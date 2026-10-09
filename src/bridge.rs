//! Per-function translation: CLIF `Function` -> waffle `FunctionBody`.
//!
//! Strategy: two passes, no placeholders. Pass 1 creates every waffle block and
//! blockparam (CLIF blockparams map 1:1, except i128 which becomes a (lo, hi) pair of
//! I64 params). Pass 2 walks blocks in reverse post-order — CLIF is legal SSA, so on
//! the reducible CFGs we accept, every def is translated before any use and a plain
//! value map suffices.
//!
//! Shadow stack: wasm locals have no address, so functions with sized stack slots get
//! a synthesized frame — `sp_new = __stack_pointer - frame_size` in the prologue,
//! `__stack_pointer = sp_old` before every return. `stack_addr` lowers to
//! `sp_new + slot_offset` (the standard LLVM-wasm approach; plan §8).

use std::collections::HashMap;

use crate::error::{Context, Result};
use crate::{bail, ensure};
use cranelift_codegen::dominator_tree::DominatorTree;
use cranelift_codegen::flowgraph::ControlFlowGraph;
use cranelift_codegen::ir::{self, InstructionData, types};
use waffle::entity::EntityRef;
use waffle::{BlockTarget, FunctionBody, Operator, Terminator, Type};

use crate::{map_type, ops};

/// A CLIF value's Waffle representation.
#[derive(Clone, Debug)]
pub enum WVal {
    One(waffle::Value),
    Pair(waffle::Value, waffle::Value),
    Vector(Vec<waffle::Value>),
}

/// Module-level context every function translation needs.
pub struct ModCtx<'a> {
    /// waffle Func index for each input function, by ordinal (call resolution).
    pub callees: &'a [waffle::Func],
    /// Fixture-style `ExternalName::TestCase` callees, by function name.
    pub testcase_callees: &'a HashMap<String, (u32, waffle::Func)>,
    /// The module's single linear memory.
    pub mem0: waffle::Memory,
    pub shared_memory: bool,
    /// The imported `__stack_pointer` mutable global.
    pub sp_global: waffle::Global,
    /// The single funcref table (index 0 is null).
    pub table: waffle::Table,
    /// Synthesized runtime helpers for `ExternalName::LibCall` callees.
    pub libcalls: &'a HashMap<crate::RuntimeFn, waffle::Func>,
    /// Symbol references lower to `global.get <marker>`; the splicer rewrites each
    /// marker site into a padded `i32.const` + relocation resolved by the linker.
    pub object_markers: &'a ObjectMarkers,
}

/// Marker globals for symbol references (see `relocatable.rs`).
#[derive(Default)]
pub struct ObjectMarkers {
    /// (data ordinal, byte offset) -> marker global.
    pub data: HashMap<(u32, i64), waffle::Global>,
    /// function ordinal (address-taken) -> marker global.
    pub funcs: HashMap<u32, waffle::Global>,
    /// Address below which the shadow stack must not grow, when checked.
    pub stack_limit: Option<waffle::Global>,
}

/// Synthesized shadow-stack frame for a function with sized stack slots.
pub struct Frame {
    /// Frame base (`__stack_pointer` after the prologue decrement).
    pub sp_new: waffle::Value,
    /// Caller's stack pointer, restored before every return.
    pub sp_old: waffle::Value,
    /// Byte offset of each CLIF stack slot from `sp_new`.
    pub slots: HashMap<ir::StackSlot, u32>,
}

/// Per-function translation context shared with the operator lowering table.
pub struct FnCx<'a> {
    pub clif: &'a ir::Function,
    pub m: &'a ModCtx<'a>,
    /// CLIF SigRef -> interned waffle signature (for call_indirect).
    pub sig_map: &'a HashMap<ir::SigRef, waffle::Signature>,
    pub frame: Option<Frame>,
    map: HashMap<ir::Value, WVal>,
}

impl FnCx<'_> {
    fn get(&self, v: ir::Value) -> Result<WVal> {
        let r = self.clif.dfg.resolve_aliases(v);
        self.map.get(&r).cloned().with_context(|| {
            format!("no waffle value for CLIF value {r} (use before def — irreducible or unsupported input?)")
        })
    }

    /// CLIF value (alias-resolved) -> single waffle value. Errors on i128 pairs.
    pub fn one(&self, v: ir::Value) -> Result<waffle::Value> {
        match self.get(v)? {
            WVal::One(w) => Ok(w),
            WVal::Pair(..) => bail!("i128 value used where a single wasm value is required"),
            WVal::Vector(..) => bail!("CLIF vector used where a scalar wasm value is required"),
        }
    }

    /// CLIF i128 value -> its (lo, hi) pair.
    pub fn pair(&self, v: ir::Value) -> Result<(waffle::Value, waffle::Value)> {
        match self.get(v)? {
            WVal::Pair(lo, hi) => Ok((lo, hi)),
            WVal::One(_) => bail!("non-i128 value used where an i128 pair is required"),
            WVal::Vector(_) => bail!("CLIF vector used where an i128 pair is required"),
        }
    }

    pub fn vector(&self, v: ir::Value) -> Result<Vec<waffle::Value>> {
        match self.get(v)? {
            WVal::Vector(values) => Ok(values),
            WVal::One(_) | WVal::Pair(..) => bail!("non-vector value used as a CLIF vector"),
        }
    }

    /// Flatten a CLIF value for ABI positions (branch args, returns, call args).
    pub fn expand_use(&self, v: ir::Value) -> Result<Vec<waffle::Value>> {
        Ok(match self.get(v)? {
            WVal::One(w) => vec![w],
            WVal::Pair(lo, hi) => vec![lo, hi],
            WVal::Vector(values) => values,
        })
    }

    pub fn bind1(&mut self, clif_v: ir::Value, wv: waffle::Value) {
        self.map
            .insert(self.clif.dfg.resolve_aliases(clif_v), WVal::One(wv));
    }

    pub fn bind2(&mut self, clif_v: ir::Value, lo: waffle::Value, hi: waffle::Value) {
        self.map
            .insert(self.clif.dfg.resolve_aliases(clif_v), WVal::Pair(lo, hi));
    }

    pub fn bind_vector(&mut self, clif_v: ir::Value, values: Vec<waffle::Value>) {
        self.map
            .insert(self.clif.dfg.resolve_aliases(clif_v), WVal::Vector(values));
    }

    /// CLIF type of an alias-resolved value.
    pub fn vty(&self, v: ir::Value) -> ir::Type {
        self.clif.dfg.value_type(self.clif.dfg.resolve_aliases(v))
    }

    /// Frame-relative address of a stack slot (+ static offset), as a wasm i32.
    pub fn slot_addr(
        &self,
        body: &mut FunctionBody,
        wb: waffle::Block,
        slot: ir::StackSlot,
        offset: i32,
    ) -> Result<waffle::Value> {
        let frame = self
            .frame
            .as_ref()
            .context("stack op in a function with no frame")?;
        let base = *frame
            .slots
            .get(&slot)
            .with_context(|| format!("unknown stack slot {slot}"))?;
        ensure!(offset >= 0, "negative stack-slot offset {offset}");
        let total = base + offset as u32;
        let c = body.add_op(wb, Operator::I32Const { value: total }, &[], &[Type::I32]);
        Ok(body.add_op(wb, Operator::I32Add, &[frame.sp_new, c], &[Type::I32]))
    }
}

pub fn translate_function(
    clif: &ir::Function,
    module: &waffle::Module,
    sig: waffle::Signature,
    m: &ModCtx,
    sig_map: &HashMap<ir::SigRef, waffle::Signature>,
) -> Result<FunctionBody> {
    let mut body = FunctionBody::new(module, sig);
    let mut cx = FnCx {
        clif,
        m,
        sig_map,
        frame: None,
        map: HashMap::new(),
    };

    let entry = clif
        .layout
        .entry_block()
        .context("function has no entry block")?;

    // Pass 1: blocks and blockparams. The CLIF entry block maps onto the entry block
    // FunctionBody::new pre-created (with params matching the *expanded* signature) —
    // bind CLIF entry params onto them (consuming two per i128) rather than adding new.
    let mut bmap: HashMap<ir::Block, waffle::Block> = HashMap::new();
    {
        let wparams: Vec<waffle::Value> = body.blocks[body.entry]
            .params
            .iter()
            .map(|&(_, v)| v)
            .collect();
        let entry_wb = body.entry;
        let mut wi = 0;
        for &p in clif.dfg.block_params(entry) {
            let ty = clif.dfg.value_type(p);
            if ty == ir::types::I128 {
                ensure!(
                    wi + 1 < wparams.len(),
                    "entry params shorter than expanded signature"
                );
                cx.bind2(p, wparams[wi], wparams[wi + 1]);
                wi += 2;
            } else if ty.is_vector() {
                let n = crate::expand_type(ty)?.len();
                ensure!(
                    wi + n <= wparams.len(),
                    "entry params shorter than expanded signature"
                );
                let values = wparams[wi..wi + n].to_vec();
                let values = ops::normalize_vector(&mut body, entry_wb, ty, values)?;
                cx.bind_vector(p, values);
                wi += n;
            } else {
                ensure!(
                    wi < wparams.len(),
                    "entry params shorter than expanded signature"
                );
                let value = wparams[wi];
                let value = if matches!(ty, ir::types::I8 | ir::types::I16) {
                    ops::mask_narrow(&mut body, entry_wb, value, ty)
                } else {
                    value
                };
                cx.bind1(p, value);
                wi += 1;
            }
        }
        ensure!(
            wi == wparams.len(),
            "entry block params ({}) do not cover expanded signature params ({})",
            wi,
            wparams.len()
        );
    }
    bmap.insert(entry, body.entry);
    for block in clif.layout.blocks() {
        if block == entry {
            continue;
        }
        let wb = body.add_block();
        bmap.insert(block, wb);
        for &p in clif.dfg.block_params(block) {
            let ty = clif.dfg.value_type(p);
            if ty == ir::types::I128 {
                let lo = body.add_blockparam(wb, Type::I64);
                let hi = body.add_blockparam(wb, Type::I64);
                cx.bind2(p, lo, hi);
            } else if ty.is_vector() {
                let types = crate::expand_type(ty)?;
                let mut values = Vec::with_capacity(types.len());
                for wty in types {
                    values.push(body.add_blockparam(wb, wty));
                }
                let values = ops::normalize_vector(&mut body, wb, ty, values)?;
                cx.bind_vector(p, values);
            } else {
                let param = body.add_blockparam(wb, map_type(ty)?);
                let wv = if matches!(ty, ir::types::I8 | ir::types::I16) {
                    ops::mask_narrow(&mut body, wb, param, ty)
                } else {
                    param
                };
                cx.bind1(p, wv);
            }
        }
    }

    // Shadow-stack prologue (entry block, before any translated instruction).
    let frame_size = layout_frame(clif, &mut cx)?;
    if frame_size > 0 {
        let wb = body.entry;
        let spg = m.sp_global;
        let sp_old = body.add_op(
            wb,
            Operator::GlobalGet { global_index: spg },
            &[],
            &[Type::I32],
        );
        let c = body.add_op(
            wb,
            Operator::I32Const { value: frame_size },
            &[],
            &[Type::I32],
        );
        let sp_new = body.add_op(wb, Operator::I32Sub, &[sp_old, c], &[Type::I32]);
        let continuation = if let Some(limit) = m.object_markers.stack_limit {
            ensure!(frame_size < 1 << 30, "shadow stack frame too large");
            let limit = body.add_op(
                wb,
                Operator::GlobalGet {
                    global_index: limit,
                },
                &[],
                &[Type::I32],
            );
            let frame = body.add_op(
                wb,
                Operator::I32Const { value: frame_size },
                &[],
                &[Type::I32],
            );
            let minimum = body.add_op(wb, Operator::I32Add, &[limit, frame], &[Type::I32]);
            let overflow = body.add_op(wb, Operator::I32LtU, &[sp_old, minimum], &[Type::I32]);
            let trap = body.add_block();
            let resume = body.add_block();
            body.set_terminator(trap, Terminator::Unreachable);
            body.set_terminator(
                wb,
                Terminator::CondBr {
                    cond: overflow,
                    if_true: BlockTarget {
                        block: trap,
                        args: vec![],
                    },
                    if_false: BlockTarget {
                        block: resume,
                        args: vec![],
                    },
                },
            );
            bmap.insert(entry, resume);
            resume
        } else {
            wb
        };
        body.add_op(
            continuation,
            Operator::GlobalSet { global_index: spg },
            &[sp_new],
            &[],
        );
        if let Some(frame) = cx.frame.as_mut() {
            frame.sp_new = sp_new;
            frame.sp_old = sp_old;
        }
    }

    // Pass 2: instructions, in RPO over reachable blocks (cranelift's own analysis).
    let cfg = ControlFlowGraph::with_function(clif);
    let domtree = DominatorTree::with_function(clif, &cfg);
    for &block in domtree.cfg_rpo() {
        let wb = bmap[&block];
        for inst in clif.layout.block_insts(block) {
            match &clif.dfg.insts[inst] {
                InstructionData::Jump { destination, .. } => {
                    let target = block_target(&cx, &bmap, destination)?;
                    body.set_terminator(wb, Terminator::Br { target });
                }
                InstructionData::Brif { arg, blocks, .. } => {
                    let cond = ops::coerce_cond(&cx, &mut body, wb, *arg)?;
                    let if_true = block_target(&cx, &bmap, &blocks[0])?;
                    let if_false = block_target(&cx, &bmap, &blocks[1])?;
                    body.set_terminator(
                        wb,
                        Terminator::CondBr {
                            cond,
                            if_true,
                            if_false,
                        },
                    );
                }
                InstructionData::BranchTable { arg, table, .. } => {
                    // wasm br_table (waffle Terminator::Select) has CLIF br_table's
                    // exact semantics: index into targets, out-of-range -> default.
                    let jt = &clif.dfg.jump_tables[*table];
                    let default = block_target(&cx, &bmap, &jt.default_block())?;
                    let targets = jt
                        .as_slice()
                        .iter()
                        .map(|bc| block_target(&cx, &bmap, bc))
                        .collect::<Result<Vec<_>>>()?;
                    let raw = cx.one(*arg)?;
                    let value = match crate::map_type(cx.vty(*arg))? {
                        Type::I32 => raw,
                        Type::I64 => body.add_op(wb, Operator::I32WrapI64, &[raw], &[Type::I32]),
                        other => bail!("br_table index has non-integer type {other}"),
                    };
                    body.set_terminator(
                        wb,
                        Terminator::Select {
                            value,
                            targets,
                            default,
                        },
                    );
                }
                InstructionData::MultiAry {
                    opcode: ir::Opcode::Return,
                    args,
                } => {
                    let mut values = Vec::new();
                    for &v in args.as_slice(&clif.dfg.value_lists) {
                        values.extend(cx.expand_use(v)?);
                    }
                    restore_stack_pointer(&cx, &mut body, wb, m);
                    body.set_terminator(wb, Terminator::Return { values });
                }
                InstructionData::Call {
                    opcode: ir::Opcode::ReturnCall,
                    args,
                    func_ref,
                } => {
                    let (Some(_), func) = ops::resolve_callee(&cx, *func_ref)? else {
                        return Err(crate::error::Error::unsupported("tail libcall unsupported")
                            .at_instruction(
                                &clif.name.to_string(),
                                &clif.dfg.display_inst(inst).to_string(),
                            ));
                    };
                    let mut values = Vec::new();
                    for &v in args.as_slice(&clif.dfg.value_lists) {
                        values.extend(cx.expand_use(v)?);
                    }
                    restore_stack_pointer(&cx, &mut body, wb, m);
                    body.set_terminator(wb, Terminator::ReturnCall { func, args: values });
                }
                InstructionData::CallIndirect {
                    opcode: ir::Opcode::ReturnCallIndirect,
                    args,
                    sig_ref,
                } => {
                    let sig = *sig_map.get(sig_ref).context("tail signature missing")?;
                    let all = args.as_slice(&clif.dfg.value_lists);
                    let mut values = Vec::new();
                    for &v in &all[1..] {
                        values.extend(cx.expand_use(v)?);
                    }
                    let table_index = match cx.vty(all[0]) {
                        types::I32 => cx.one(all[0])?,
                        types::I64 => {
                            let address = cx.one(all[0])?;
                            body.add_op(wb, Operator::I32WrapI64, &[address], &[Type::I32])
                        }
                        other => {
                            bail!("tail call callee pointer must be i32 or i64, got {other}")
                        }
                    };
                    values.push(table_index);
                    restore_stack_pointer(&cx, &mut body, wb, m);
                    body.set_terminator(
                        wb,
                        Terminator::ReturnCallIndirect {
                            sig,
                            table: m.table,
                            args: values,
                        },
                    );
                }
                InstructionData::Trap { .. } => {
                    body.set_terminator(wb, Terminator::Unreachable);
                }
                _ => {
                    let instruction = clif.dfg.display_inst(inst).to_string();
                    let function = clif.name.to_string();
                    ops::lower_inst(&mut cx, &mut body, wb, inst)
                        .with_context(|| format!("lowering `{instruction}`"))
                        .map_err(|error| error.at_instruction(&function, &instruction))?;
                }
            }
        }
    }

    for block in clif.layout.blocks() {
        let wb = bmap[&block];
        if matches!(&body.blocks[wb].terminator, Terminator::None) {
            body.set_terminator(wb, Terminator::Unreachable);
        }
    }

    Ok(body)
}

/// Assign frame offsets to every sized stack slot; returns the (16-aligned) frame size
/// in bytes, 0 if the function has no slots. Prologue values are patched in after.
fn layout_frame(clif: &ir::Function, cx: &mut FnCx) -> Result<u32> {
    if clif.sized_stack_slots.is_empty() {
        return Ok(0);
    }
    let mut slots = HashMap::new();
    let mut cur: u32 = 0;
    for (slot, data) in clif.sized_stack_slots.iter() {
        let align: u32 = 1 << data.align_shift;
        cur = (cur + align - 1) & !(align - 1);
        slots.insert(slot, cur);
        cur += data.size;
    }
    let frame_size = (cur + 15) & !15;
    // sp_new/sp_old are patched in by the prologue right after this returns; use
    // placeholders that would fail loudly if ever read unpatched.
    cx.frame = Some(Frame {
        sp_new: waffle::Value::invalid(),
        sp_old: waffle::Value::invalid(),
        slots,
    });
    Ok(frame_size)
}

fn block_target(
    cx: &FnCx,
    bmap: &HashMap<ir::Block, waffle::Block>,
    bc: &ir::BlockCall,
) -> Result<BlockTarget> {
    let pool = &cx.clif.dfg.value_lists;
    let block = *bmap
        .get(&bc.block(pool))
        .context("branch to block missing from layout")?;
    let mut args = Vec::new();
    for a in bc.args(pool) {
        match a {
            ir::BlockArg::Value(v) => args.extend(cx.expand_use(v)?),
            other => bail!("unsupported block argument {other:?} (try_call is out of scope)"),
        }
    }
    Ok(BlockTarget { block, args })
}

fn restore_stack_pointer(cx: &FnCx, body: &mut FunctionBody, wb: waffle::Block, m: &ModCtx) {
    if let Some(frame) = cx.frame.as_ref() {
        body.add_op(
            wb,
            Operator::GlobalSet {
                global_index: m.sp_global,
            },
            &[frame.sp_old],
            &[],
        );
    }
}
