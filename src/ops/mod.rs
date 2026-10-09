//! CLIF opcode -> waffle `Operator` lowering table.
//!
//! waffle's Operator enum is 1:1 with wasm opcodes, so this is instruction selection,
//! not renaming: some CLIF ops expand to short multi-op sequences (condition
//! normalization, shift-amount width fixups, i128 pair legalization). Anything not in
//! the starter set fails with a clear "unimplemented opcode" error — the gap list is a
//! prototype deliverable.

use crate::error::Result;
use crate::{bail, ensure, unsupported};
use cranelift_codegen::ir::{self, InstructionData, Opcode, types};
use waffle::{FunctionBody, Operator, Type};

use crate::bridge::FnCx;
use crate::i128_lower;
use crate::map_type;

mod atomic;
mod call;
mod cmp;
mod i128;
mod int;
mod mem;
mod overflow;
mod select;
mod vector;
use atomic::*;
use call::*;
pub(crate) use call::{lower_try_call, resolve_callee};
use cmp::*;
use i128::*;
pub(crate) use int::mask_narrow;
use int::*;
use mem::*;
pub(crate) use overflow::lower_add_trap_value;
use overflow::*;
use select::*;
pub(crate) use vector::normalize_vector;
use vector::*;

/// Normalize a CLIF condition value (i8 icmp result, or any int used as a truth
/// value) to a wasm i32. i8/i16/i32 map straight through; i64 gets eqz/eqz; i128 is
/// nonzero iff (lo | hi) is nonzero.
pub fn coerce_cond(
    cx: &FnCx,
    body: &mut FunctionBody,
    wb: waffle::Block,
    cond: ir::Value,
) -> Result<waffle::Value> {
    if cx.vty(cond) == types::I128 {
        let (lo, hi) = cx.pair(cond)?;
        let or = body.add_op(wb, Operator::I64Or, &[lo, hi], &[Type::I64]);
        let z = body.add_op(wb, Operator::I64Eqz, &[or], &[Type::I32]);
        return Ok(body.add_op(wb, Operator::I32Eqz, &[z], &[Type::I32]));
    }
    let wv = cx.one(cond)?;
    match map_type(cx.vty(cond))? {
        Type::I32 => Ok(wv),
        Type::I64 => {
            let z = body.add_op(wb, Operator::I64Eqz, &[wv], &[Type::I32]);
            Ok(body.add_op(wb, Operator::I32Eqz, &[z], &[Type::I32]))
        }
        other => bail!("branch/select condition has non-integer type {other}"),
    }
}

pub fn lower_inst(
    cx: &mut FnCx,
    body: &mut FunctionBody,
    wb: waffle::Block,
    inst: ir::Inst,
) -> Result<()> {
    let dfg = &cx.clif.dfg;
    match dfg.insts[inst] {
        InstructionData::DynamicStackAddr {
            opcode: Opcode::DynamicStackAddr,
            dynamic_stack_slot,
        } => unsupported!(
            "dynamic_stack_addr for {dynamic_stack_slot} is unsupported: the wasm runtime has no dynamic stack allocation or lifetime tracking"
        ),

        // --- Constants ---
        InstructionData::UnaryConst {
            opcode: Opcode::Vconst,
            constant_handle,
        } => {
            let result = dfg.first_result(inst);
            let ty = dfg.value_type(result);
            ensure!(
                ty.is_vector(),
                "vconst result must be a fixed vector, got {ty}"
            );
            let data = dfg.constants.get(constant_handle).as_slice();
            ensure!(
                data.len() * 8 == ty.bits() as usize,
                "vconst data size does not match {ty}"
            );
            let mut values = Vec::new();
            for chunk in data.chunks(16) {
                let mut bytes = [0; 16];
                bytes[..chunk.len()].copy_from_slice(chunk);
                values.push(body.add_op(
                    wb,
                    Operator::V128Const {
                        value: u128::from_le_bytes(bytes),
                    },
                    &[],
                    &[Type::V128],
                ));
            }
            cx.bind_vector(result, normalize_vector(body, wb, ty, values)?);
        }
        InstructionData::UnaryImm {
            opcode: Opcode::Iconst,
            imm,
        } => {
            let rty = dfg.value_type(dfg.first_result(inst));
            let bits = imm.bits();
            let (op, wty) = match rty {
                types::I8 => (
                    Operator::I32Const {
                        value: bits as u32 & 0xFF,
                    },
                    Type::I32,
                ),
                types::I16 => (
                    Operator::I32Const {
                        value: bits as u32 & 0xFFFF,
                    },
                    Type::I32,
                ),
                types::I32 => (Operator::I32Const { value: bits as u32 }, Type::I32),
                types::I64 => (Operator::I64Const { value: bits as u64 }, Type::I64),
                other => unsupported!("iconst of unsupported type {other}"),
            };
            let wv = body.add_op(wb, op, &[], &[wty]);
            cx.bind1(dfg.first_result(inst), wv);
        }
        InstructionData::UnaryIeee32 {
            opcode: Opcode::F32const,
            imm,
        } => {
            let wv = body.add_op(
                wb,
                Operator::F32Const { value: imm.bits() },
                &[],
                &[Type::F32],
            );
            cx.bind1(dfg.first_result(inst), wv);
        }
        InstructionData::UnaryIeee64 {
            opcode: Opcode::F64const,
            imm,
        } => {
            let wv = body.add_op(
                wb,
                Operator::F64Const { value: imm.bits() },
                &[],
                &[Type::F64],
            );
            cx.bind1(dfg.first_result(inst), wv);
        }

        // --- Unary int conversions (and isplit) ---
        InstructionData::Unary {
            opcode: Opcode::SetPinnedReg,
            ..
        } => unsupported!(
            "pinned registers are unsupported: wasm has no reserved register and the relocatable form has no slot for a pinned-register global"
        ),
        InstructionData::Unary {
            opcode: Opcode::X86Cvtt2dq,
            ..
        } => lower_x86_cvtt2dq(cx, body, wb, inst)?,
        InstructionData::Unary { opcode, arg } => {
            lower_unary(cx, body, wb, inst, opcode, arg)?;
        }

        InstructionData::Shuffle {
            opcode: Opcode::Shuffle,
            args,
            imm,
        } => {
            let result = dfg.first_result(inst);
            let ty = dfg.value_type(result);
            ensure!(
                ty == types::I8X16,
                "shuffle currently requires i8x16, got {ty}"
            );
            let data = dfg.immediates[imm].as_slice();
            ensure!(data.len() == 16, "shuffle mask must contain 16 bytes");
            let lanes: [u8; 16] = data.try_into().unwrap();
            let a = cx.vector(args[0])?;
            let b = cx.vector(args[1])?;
            let value = body.add_op(
                wb,
                Operator::I8x16Shuffle { lanes },
                &[a[0], b[0]],
                &[Type::V128],
            );
            cx.bind_vector(result, vec![value]);
        }

        InstructionData::Binary {
            opcode: Opcode::X86Pmaddubsw,
            ..
        } => lower_x86_pmaddubsw(cx, body, wb, inst)?,

        InstructionData::Binary {
            opcode: opcode @ (Opcode::Swizzle | Opcode::X86Pshufb),
            args,
        } => {
            let result = dfg.first_result(inst);
            let ty = dfg.value_type(result);
            ensure!(
                ty == types::I8X16,
                "swizzle currently requires i8x16, got {ty}"
            );
            let x = cx.vector(args[0])?;
            let mask = cx.vector(args[1])?;
            let value = body.add_op(wb, Operator::I8x16Swizzle, &[x[0], mask[0]], &[Type::V128]);
            let value = if opcode == Opcode::X86Pshufb {
                let zero = body.add_op(wb, Operator::V128Const { value: 0 }, &[], &[Type::V128]);
                let negative = body.add_op(wb, Operator::I8x16LtS, &[mask[0], zero], &[Type::V128]);
                body.add_op(wb, Operator::V128AndNot, &[value, negative], &[Type::V128])
            } else {
                value
            };
            cx.bind_vector(result, vec![value]);
        }

        InstructionData::BinaryImm8 {
            opcode: Opcode::Extractlane,
            arg,
            imm,
        } => {
            let result = dfg.first_result(inst);
            let vector_ty = cx.vty(arg);
            let lane_ty = vector_ty.lane_type();
            let lane_bits = lane_ty.bits();
            let lane_index = imm as usize;
            ensure!(
                lane_index < vector_ty.lane_count() as usize,
                "extractlane index {lane_index} out of range for {vector_ty}"
            );
            let chunk_index = lane_index * lane_bits as usize / 128;
            let chunk_lane = lane_index % (128 / lane_bits as usize);
            let vector = cx.vector(arg)?;
            let op = extract_lane_op(lane_ty, chunk_lane as u8)?;
            let value = body.add_op(wb, op, &[vector[chunk_index]], &[map_type(lane_ty)?]);
            cx.bind1(result, value);
        }

        InstructionData::TernaryImm8 {
            opcode: Opcode::Insertlane,
            args,
            imm,
        } => {
            let result = dfg.first_result(inst);
            let ty = dfg.value_type(result);
            let lane_ty = ty.lane_type();
            let lane_bits = lane_ty.bits();
            let lane_index = imm as usize;
            ensure!(
                lane_index < ty.lane_count() as usize,
                "insertlane index {lane_index} out of range for {ty}"
            );
            let chunk_index = lane_index * lane_bits as usize / 128;
            let chunk_lane = lane_index % (128 / lane_bits as usize);
            let mut vector = cx.vector(args[0])?;
            let scalar = cx.one(args[1])?;
            let op = replace_lane_op(lane_ty, chunk_lane as u8)?;
            vector[chunk_index] =
                body.add_op(wb, op, &[vector[chunk_index], scalar], &[Type::V128]);
            cx.bind_vector(result, normalize_vector(body, wb, ty, vector)?);
        }

        // cg_clif sprinkles `nop`s as MIR-comment anchors; they carry nothing.
        InstructionData::NullAry {
            opcode: Opcode::Nop,
        } => {}

        // bitcast (LoadNoOffset format): same-size reinterpretation.
        InstructionData::LoadNoOffset {
            opcode: Opcode::Bitcast,
            arg,
            ..
        } => {
            let result = dfg.first_result(inst);
            let (src, dst) = (cx.vty(arg), dfg.value_type(result));
            if src.is_vector() && dst.is_vector() {
                ensure!(
                    src.bits() == dst.bits(),
                    "bitcast {src} -> {dst} changes vector size"
                );
                cx.bind_vector(result, cx.vector(arg)?);
                return Ok(());
            }
            let v = cx.one(arg)?;
            let wv = match (src, dst) {
                (types::F32, types::I32) => {
                    body.add_op(wb, Operator::I32ReinterpretF32, &[v], &[Type::I32])
                }
                (types::I32, types::F32) => {
                    body.add_op(wb, Operator::F32ReinterpretI32, &[v], &[Type::F32])
                }
                (types::F64, types::I64) => {
                    body.add_op(wb, Operator::I64ReinterpretF64, &[v], &[Type::I64])
                }
                (types::I64, types::F64) => {
                    body.add_op(wb, Operator::F64ReinterpretI64, &[v], &[Type::F64])
                }
                (s, d) if s == d => v,
                (s, d) => unsupported!("bitcast {s} -> {d} unimplemented"),
            };
            cx.bind1(result, wv);
        }

        // --- Statics: symbol_value / global_value -> linear-memory address ---
        InstructionData::UnaryGlobalValue {
            opcode: Opcode::SymbolValue,
            ..
        } => lower_symbol_value(cx, body, wb, inst)?,
        InstructionData::UnaryGlobalValue {
            opcode: Opcode::TlsValue,
            ..
        } => lower_tls_value(cx, inst)?,

        // --- Integer & float binary arithmetic / bitwise ---
        //
        // Narrow ints (i8/i16) live in I32 with a canonical zero-extended representation.
        InstructionData::Binary { .. } => lower_binary(cx, body, wb, inst)?,

        // --- Comparisons ---
        InstructionData::IntCompare { .. } => lower_icmp(cx, body, wb, inst)?,
        InstructionData::FloatCompare { .. } => lower_fcmp(cx, body, wb, inst)?,

        InstructionData::Ternary {
            opcode: Opcode::StackSwitch,
            ..
        } => {
            unsupported!(
                "stack_switch is unsupported: wasm stack switching requires a stack-context ABI and runtime support, neither of which this module provides"
            );
        }

        InstructionData::Ternary { opcode, args } if is_overflow_opcode(opcode) => {
            if dfg.value_type(dfg.first_result(inst)) == types::I128 {
                lower_i128_carry(cx, body, wb, inst, opcode, args)?;
            } else {
                lower_scalar_overflow(cx, body, wb, inst)?;
            }
        }

        InstructionData::Ternary {
            opcode: Opcode::Fma,
            args,
        } => lower_fma(cx, body, wb, inst, args)?,

        // --- Select ---
        InstructionData::Ternary {
            opcode: Opcode::Select | Opcode::SelectSpectreGuard,
            ..
        } => lower_select(cx, body, wb, inst)?,

        InstructionData::Ternary {
            opcode: Opcode::Bitselect,
            ..
        } => lower_bitselect(cx, body, wb, inst)?,

        InstructionData::Ternary {
            opcode: Opcode::Blendv,
            ..
        } => lower_blendv(cx, body, wb, inst)?,

        // --- Memory ---
        InstructionData::Load { .. } => lower_load(cx, body, wb, inst)?,
        InstructionData::Store { .. } => lower_store(cx, body, wb, inst)?,

        // --- Shadow stack ---
        InstructionData::StackAddr {
            opcode: Opcode::StackAddr,
            stack_slot,
            offset,
        } => {
            let result = dfg.first_result(inst);
            ensure!(
                dfg.value_type(result) == types::I32,
                "stack_addr result must be i32"
            );
            let addr = cx.slot_addr(body, wb, stack_slot, offset.into())?;
            cx.bind1(result, addr);
        }

        InstructionData::LoadNoOffset {
            opcode: Opcode::AtomicLoad,
            ..
        } => lower_atomic_load(cx, body, wb, inst)?,
        InstructionData::StoreNoOffset {
            opcode: Opcode::AtomicStore,
            ..
        } => lower_atomic_store(cx, body, wb, inst)?,
        InstructionData::AtomicRmw { .. } => lower_atomic_rmw(cx, body, wb, inst)?,
        InstructionData::AtomicCas { .. } => lower_atomic_cas(cx, body, wb, inst)?,
        InstructionData::NullAry {
            opcode: Opcode::Fence,
        } => lower_fence(cx, body, wb, inst)?,

        // --- Function pointers ---
        InstructionData::FuncAddr { .. } => lower_func_addr(cx, body, wb, inst)?,

        // --- Direct calls ---
        InstructionData::Call { .. } => lower_call(cx, body, wb, inst)?,

        // --- Indirect calls ---
        InstructionData::CallIndirect { .. } => lower_call_indirect(cx, body, wb, inst)?,

        InstructionData::NullAry {
            opcode: Opcode::Debugtrap,
        } => {}
        InstructionData::NullAry {
            opcode: Opcode::GetStackPointer,
        } => {
            let result = cx.clif.dfg.first_result(inst);
            ensure!(
                cx.vty(result) == types::I32,
                "get_stack_pointer must produce a 32-bit pointer, got {}",
                cx.vty(result)
            );
            let sp = body.add_op(
                wb,
                Operator::GlobalGet {
                    global_index: cx.m.sp_global,
                },
                &[],
                &[Type::I32],
            );
            cx.bind1(result, sp);
        }
        InstructionData::NullAry {
            opcode: Opcode::GetPinnedReg,
        } => unsupported!(
            "pinned registers are unsupported: wasm has no reserved register and the relocatable form has no slot for a pinned-register global"
        ),
        InstructionData::NullAry {
            opcode: Opcode::GetFramePointer,
        } => unsupported!(
            "get_frame_pointer is unsupported: the shadow-stack frame has no frame-pointer chain"
        ),
        InstructionData::NullAry {
            opcode: Opcode::GetReturnAddress,
        } => unsupported!(
            "get_return_address is unsupported: wasm return addresses are not observable"
        ),
        InstructionData::ExceptionHandlerAddress { .. } => unsupported!(
            "get_exception_handler_address is unsupported: handler addresses are not observable in wasm"
        ),

        ref other => unsupported!("unimplemented opcode {}", other.opcode()),
    }
    Ok(())
}
