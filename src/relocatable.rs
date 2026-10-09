//! Translation of CLIF into a structured relocatable form.
//!
//! Every output mode (linkable object, whole module, incremental session) starts here:
//! `translate` compiles each function body to wasm bytes whose symbol references
//! (functions, data addresses, table slots, the stack pointer, the stack limit) are
//! 5-byte padded LEB immediates with a relocation record. `object.rs` serializes the
//! result as a wasm-ld object; `link.rs` resolves it in-process into a complete module.
//!
//! Symbol index space (shared by relocs, the object symbol table and the linker):
//! input functions by ordinal, then libcall imports, then data objects by ordinal,
//! then `__stack_pointer` and `__indirect_function_table`.
//!
//! Waffle entities are allocated so their indices equal the object's index space —
//! memory 0, global 0 = stack pointer, table 0, function imports first — because
//! compiled bodies carry raw entity indices as immediates.

use std::collections::HashMap;

use crate::bridge::{self, ModCtx};
use crate::error::{Context, Result};
use crate::module::{intern_sig, signature_data};
use crate::{DataRelocEntry, bail, ensure};
use cranelift_codegen::ir;
use waffle::backend::WasmFuncBackend;
use waffle::{
    FuncDecl, FunctionBody, GlobalData, MemoryData, SignatureData, TableData, Terminator, Type,
};

/// Symbol binding for the object's symbol table.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum ObjBinding {
    Global,
    Weak,
    Local,
}

/// A function definition: translated CLIF, or a synthesized runtime body
/// (i128 helpers via CLIF synthesis, memory.grow/size directly in waffle IR).
pub enum ObjDef<'a> {
    Clif(&'a ir::Function),
    Runtime(crate::RuntimeFn),
}

/// One function slot, in FuncId order. `def: None` = undefined: it becomes a
/// function import from `env` plus an undefined symbol for the linker to resolve.
pub struct ObjFunc<'a> {
    pub name: &'a str,
    pub binding: ObjBinding,
    pub hidden: bool,
    pub def: Option<ObjDef<'a>>,
    /// Authoritative signature (the declaration's; for defined functions this must
    /// match `def.signature`).
    pub sig: ir::Signature,
}

pub struct ObjDataDef {
    pub bytes: Vec<u8>,
    /// Linear alignment (power of two); emitted as log2 in SEGMENT_INFO.
    pub align: u32,
    pub relocs: Vec<DataRelocEntry>,
}

/// One data slot, in DataId order. `def: None` = undefined data symbol.
pub struct ObjData<'a> {
    pub name: &'a str,
    pub binding: ObjBinding,
    pub hidden: bool,
    pub def: Option<ObjDataDef>,
}

// --- relocation types ---
pub(crate) const R_WASM_FUNCTION_INDEX_LEB: u8 = 0;
pub(crate) const R_WASM_TABLE_INDEX_SLEB: u8 = 1;
pub(crate) const R_WASM_TABLE_INDEX_I32: u8 = 2;
pub(crate) const R_WASM_MEMORY_ADDR_SLEB: u8 = 4;
pub(crate) const R_WASM_MEMORY_ADDR_I32: u8 = 5;
pub(crate) const R_WASM_TYPE_INDEX_LEB: u8 = 6;
pub(crate) const R_WASM_GLOBAL_INDEX_LEB: u8 = 7;
pub(crate) const R_WASM_TABLE_NUMBER_LEB: u8 = 20;

/// One relocation record. `index` is a symbol index for every type we emit except
/// TYPE_INDEX_LEB, where it is the type index itself. `addend` is emitted only for
/// the MEMORY_ADDR_* / FUNCTION_OFFSET_* families.
#[derive(Debug)]
pub(crate) struct Reloc {
    pub ty: u8,
    pub offset: u32,
    pub index: u32,
    pub addend: Option<i64>,
}

// --- byte-stream helpers ---
pub(crate) fn uleb(out: &mut Vec<u8>, mut v: u64) {
    loop {
        let b = (v & 0x7f) as u8;
        v >>= 7;
        if v == 0 {
            out.push(b);
            break;
        }
        out.push(b | 0x80);
    }
}

pub(crate) fn sleb(out: &mut Vec<u8>, mut v: i64) {
    loop {
        let b = (v & 0x7f) as u8;
        v >>= 7;
        let sign = b & 0x40 != 0;
        if (v == 0 && !sign) || (v == -1 && sign) {
            out.push(b);
            break;
        }
        out.push(b | 0x80);
    }
}

/// Exactly-5-byte ULEB — reloc sites must be padded so the linker can patch any
/// u32 in place.
pub(crate) fn uleb_padded5(out: &mut Vec<u8>, v: u32) {
    out.push((v & 0x7f) as u8 | 0x80);
    out.push(((v >> 7) & 0x7f) as u8 | 0x80);
    out.push(((v >> 14) & 0x7f) as u8 | 0x80);
    out.push(((v >> 21) & 0x7f) as u8 | 0x80);
    out.push(((v >> 28) & 0x0f) as u8);
}

/// Exactly-5-byte SLEB (i32 range) for SLEB-typed reloc sites.
pub(crate) fn sleb_padded5(out: &mut Vec<u8>, v: i32) {
    out.push((v & 0x7f) as u8 | 0x80);
    out.push(((v >> 7) & 0x7f) as u8 | 0x80);
    out.push(((v >> 14) & 0x7f) as u8 | 0x80);
    out.push(((v >> 21) & 0x7f) as u8 | 0x80);
    out.push(((v >> 28) & 0x7f) as u8); // arithmetic shift keeps the sign bits
}

/// Pseudo relocation (never written to an object): the linker substitutes the
/// shadow-stack limit address. Present only when `TranslateOptions::stack_limit`.
pub(crate) const R_CLIF2WASM_STACK_LIMIT: u8 = 0xF0;

#[derive(Clone, Copy, Default)]
pub(crate) struct TranslateOptions {
    pub shared_memory: bool,
    /// Stub untranslatable signatures/bodies with traps and report a gap line.
    pub lenient: bool,
    /// Emit a shadow-stack overflow check in prologues.
    pub stack_limit: bool,
}

pub(crate) struct Libcall {
    pub kind: crate::RuntimeFn,
    pub name: &'static str,
    pub sig: u32,
}

/// One compiled function body (locals + instructions, no size prefix). Reloc
/// offsets are relative to `bytes`; every reloc site is a 5-byte padded LEB.
pub(crate) struct Body {
    pub ord: usize,
    pub bytes: Vec<u8>,
    pub relocs: Vec<Reloc>,
}

pub(crate) struct Relocatable<'a> {
    pub funcs: &'a [ObjFunc<'a>],
    pub data: &'a [ObjData<'a>],
    pub signatures: Vec<SignatureData>,
    pub func_sigs: Vec<u32>,
    pub libcalls: Vec<Libcall>,
    /// Defined functions, in input order.
    pub bodies: Vec<Body>,
    pub uses_tail_call: bool,
}

impl Relocatable<'_> {
    pub fn data_sym_base(&self) -> u32 {
        (self.funcs.len() + self.libcalls.len()) as u32
    }
}

fn first_line(s: &str) -> &str {
    s.lines().next().unwrap_or(s)
}

fn unreachable_stub(module: &waffle::Module, sig: waffle::Signature) -> FunctionBody {
    let mut stub = FunctionBody::new(module, sig);
    let entry = stub.entry;
    stub.set_terminator(entry, Terminator::Unreachable);
    stub
}

/// Ordinal of the input function a callee name refers to, if it is one.
fn callee_ordinal(
    clif: &ir::Function,
    name: &ir::ExternalName,
    testcase_callees: &HashMap<String, (u32, waffle::Func)>,
) -> Option<u32> {
    match name {
        ir::ExternalName::User(r) => {
            let user = clif.params.user_named_funcs().get(*r)?;
            (user.namespace == 0).then_some(user.index)
        }
        ir::ExternalName::TestCase(name) => {
            testcase_callees.get(&name.to_string()).map(|(ord, _)| *ord)
        }
        _ => None,
    }
}

fn libcall_kind(lc: ir::LibCall) -> Result<crate::RuntimeFn> {
    Ok(match lc {
        ir::LibCall::Memcpy => crate::RuntimeFn::Memcpy,
        ir::LibCall::Memmove => crate::RuntimeFn::Memmove,
        ir::LibCall::Memset => crate::RuntimeFn::Memset,
        ir::LibCall::Memcmp => crate::RuntimeFn::Memcmp,
        other => crate::unsupported!(
            "unimplemented libcall {other} (float libcalls should not arise: wasm has direct ops)"
        ),
    })
}

fn translate_body(
    f: &ObjFunc,
    k: usize,
    module: &mut waffle::Module,
    sig_cache: &mut HashMap<SignatureData, waffle::Signature>,
    sigs: &[waffle::Signature],
    mctx: &ModCtx,
    lenient: bool,
) -> Result<FunctionBody> {
    let body = match f.def.as_ref().unwrap() {
        ObjDef::Clif(clif) => {
            let mut sig_map: HashMap<ir::SigRef, waffle::Signature> = HashMap::new();
            for (sig_ref, sig) in clif.dfg.signatures.iter() {
                let sd = match signature_data(sig) {
                    Ok(sd) => sd,
                    Err(_) if lenient => continue,
                    Err(e) => {
                        return Err(e)
                            .with_context(|| format!("SigRef {sig_ref} in function `{}`", f.name));
                    }
                };
                sig_map.insert(sig_ref, intern_sig(module, sig_cache, sd));
            }
            bridge::translate_function(clif, module, sigs[k], mctx, &sig_map)
                .with_context(|| format!("translating function `{}`", f.name))?
        }
        &ObjDef::Runtime(kind) => {
            if let Some(clif_fn) = crate::runtime_i128::build(kind) {
                bridge::translate_function(&clif_fn, module, sigs[k], mctx, &HashMap::new())
                    .with_context(|| format!("translating runtime `{}`", f.name))?
            } else {
                crate::module::synth_runtime_body(kind, module, sigs[k], mctx.mem0)
                    .with_context(|| format!("synthesizing runtime `{}`", f.name))?
            }
        }
    };
    body.validate().map_err(|e| {
        crate::error::Error::general(format!("waffle validate() rejected `{}`:\n{e}", f.name))
    })?;
    Ok(body)
}

/// Translate CLIF functions + data into the relocatable form.
pub(crate) fn translate<'a>(
    funcs: &'a [ObjFunc<'a>],
    data: &'a [ObjData<'a>],
    opts: TranslateOptions,
) -> Result<Relocatable<'a>> {
    let mut module = waffle::Module::empty();

    let mem0 = module.memories.push(MemoryData {
        initial_pages: 1,
        maximum_pages: None,
        segments: vec![],
        memory64: false,
        shared: opts.shared_memory,
        page_size_log2: None,
    });
    let sp_global = module.globals.push(GlobalData {
        ty: Type::I32,
        value: None,
        mutable: true,
    });
    let table = module.tables.push(TableData {
        ty: Type::Heap(waffle::WithNullable {
            value: waffle::HeapType::FuncRef,
            nullable: true,
        }),
        initial: 0,
        max: None,
        func_elements: None,
        table64: false,
    });

    // Signatures (interned with dedup — type indices are shared by bodies'
    // call_indirect immediates and the emitted type section).
    let mut sig_cache: HashMap<SignatureData, waffle::Signature> = HashMap::new();
    let mut sigs = Vec::with_capacity(funcs.len());
    let mut force_stub: std::collections::HashSet<usize> = Default::default();
    for (k, f) in funcs.iter().enumerate() {
        let sd = match signature_data(&f.sig) {
            Ok(sd) => sd,
            // f16/f128 signatures: callers reaching for such a slot are themselves
            // f16/f128 paths that lenient-stub on their own call lowering.
            Err(e) if opts.lenient => {
                eprintln!(
                    "clif2wasm-gap: signature stubbed: {} ({})",
                    f.name,
                    first_line(&format!("{e:#}"))
                );
                force_stub.insert(k);
                SignatureData::Func {
                    params: vec![],
                    returns: vec![],
                    shared: false,
                }
            }
            Err(e) => {
                return Err(e).with_context(|| format!("signature of function `{}`", f.name));
            }
        };
        sigs.push(intern_sig(&mut module, &mut sig_cache, sd));
    }

    // Libcall callees (`ExternalName::LibCall`) become undefined imports under their
    // real C names; memmove stays distinct from memcpy because libc memcpy is not
    // overlap-safe. A linker that synthesizes them may merge the bodies.
    let mut libcall_sigs: HashMap<crate::RuntimeFn, waffle::Signature> = HashMap::new();
    for f in funcs {
        let Some(ObjDef::Clif(clif)) = &f.def else {
            continue;
        };
        for ext in clif.dfg.ext_funcs.values() {
            let ir::ExternalName::LibCall(lc) = ext.name else {
                continue;
            };
            let kind = match libcall_kind(lc) {
                Ok(kind) => kind,
                Err(e) if opts.lenient => {
                    eprintln!("clif2wasm-gap: libcall {lc} in `{}` ({e:#})", f.name);
                    continue;
                }
                Err(e) => return Err(e),
            };
            if libcall_sigs.contains_key(&kind) {
                continue;
            }
            let sd = signature_data(&clif.dfg.signatures[ext.signature])
                .with_context(|| format!("libcall {lc} signature in `{}`", f.name))?;
            libcall_sigs.insert(kind, intern_sig(&mut module, &mut sig_cache, sd));
        }
    }

    // Function entities: imports (undefined + libcalls) FIRST so entity index ==
    // wasm function index, then placeholders for defined functions.
    use waffle::entity::EntityRef as _;
    let mut wfuncs = vec![waffle::Func::invalid(); funcs.len()];
    for (k, f) in funcs.iter().enumerate() {
        if f.def.is_none() {
            wfuncs[k] = module
                .funcs
                .push(FuncDecl::Import(sigs[k], f.name.to_string()));
        }
    }
    let mut libcalls: Vec<Libcall> = Vec::new();
    let mut libcall_map: HashMap<crate::RuntimeFn, waffle::Func> = HashMap::new();
    let mut libcall_funcs: Vec<waffle::Func> = Vec::new();
    for (kind, name) in [
        (crate::RuntimeFn::Memcpy, "memcpy"),
        (crate::RuntimeFn::Memmove, "memmove"),
        (crate::RuntimeFn::Memset, "memset"),
        (crate::RuntimeFn::Memcmp, "memcmp"),
    ] {
        let Some(&sig) = libcall_sigs.get(&kind) else {
            continue;
        };
        let wf = module.funcs.push(FuncDecl::Import(sig, name.to_string()));
        libcall_map.insert(kind, wf);
        libcall_funcs.push(wf);
        libcalls.push(Libcall {
            kind,
            name,
            sig: sig.index() as u32,
        });
    }
    let mut defined_fn_ords: Vec<usize> = Vec::new();
    for (k, f) in funcs.iter().enumerate() {
        if f.def.is_some() {
            wfuncs[k] = module.funcs.push(FuncDecl::None);
            defined_fn_ords.push(k);
        }
    }

    let mut testcase_callees: HashMap<String, (u32, waffle::Func)> = HashMap::new();
    for (k, f) in funcs.iter().enumerate() {
        let callee = (k as u32, wfuncs[k]);
        testcase_callees.insert(f.name.to_string(), callee);
        if let Some(ObjDef::Clif(clif)) = &f.def {
            testcase_callees.insert(clif.name.to_string(), callee);
        }
    }

    // Pre-scan defined bodies for symbol references and allocate MARKER globals: one
    // per unique (data ordinal, offset) for `symbol_value`, one per address-taken
    // function for `func_addr`, one for the stack limit. Bodies emit `global.get
    // <marker>`; the splicer rewrites each site into a padded i32.const + reloc.
    // Marker globals are entities only.
    let mut markers = bridge::ObjectMarkers::default();
    for f in funcs {
        let Some(ObjDef::Clif(clif)) = &f.def else {
            continue;
        };
        for (_gv, gvd) in clif.global_values.iter() {
            let ir::GlobalValueData::Symbol {
                name,
                offset,
                tls: false,
                ..
            } = gvd
            else {
                continue;
            };
            let ir::ExternalName::User(r) = name else {
                continue;
            };
            let Some(user) = clif.params.user_named_funcs().get(*r) else {
                continue;
            };
            if user.namespace != 1 {
                continue;
            }
            let ord = user.index;
            ensure!(
                (ord as usize) < data.len(),
                "function `{}` references data ordinal {ord} out of range",
                f.name
            );
            let off: i64 = (*offset).into();
            markers.data.entry((ord, off)).or_insert_with(|| {
                module.globals.push(GlobalData {
                    ty: Type::I32,
                    value: Some(0),
                    mutable: false,
                })
            });
        }
        for block in clif.layout.blocks() {
            for inst in clif.layout.block_insts(block) {
                let ir::InstructionData::FuncAddr { func_ref, .. } = clif.dfg.insts[inst] else {
                    continue;
                };
                let ext = &clif.dfg.ext_funcs[func_ref];
                let Some(ord) = callee_ordinal(clif, &ext.name, &testcase_callees) else {
                    continue;
                };
                ensure!(
                    (ord as usize) < funcs.len(),
                    "function `{}` takes the address of ordinal {ord} out of range",
                    f.name
                );
                markers.funcs.entry(ord).or_insert_with(|| {
                    module.globals.push(GlobalData {
                        ty: Type::I32,
                        value: Some(0),
                        mutable: false,
                    })
                });
            }
        }
    }
    markers.stack_limit = opts.stack_limit.then(|| {
        module.globals.push(GlobalData {
            ty: Type::I32,
            value: Some(0),
            mutable: false,
        })
    });

    // Symbol numbering and the wasm-index -> symbol map the splicer needs.
    let data_sym_base = (funcs.len() + libcalls.len()) as u32;
    let sp_sym = data_sym_base + data.len() as u32;
    let table_sym = sp_sym + 1;
    let mut fn_sym_of_wasm_index = vec![u32::MAX; funcs.len() + libcalls.len()];
    for (k, wf) in wfuncs.iter().enumerate() {
        fn_sym_of_wasm_index[wf.index()] = k as u32;
    }
    for (j, wf) in libcall_funcs.iter().enumerate() {
        fn_sym_of_wasm_index[wf.index()] = (funcs.len() + j) as u32;
    }
    // marker global entity index -> (reloc type, symbol index, addend).
    let mut marker_relocs: HashMap<u32, (u8, u32, Option<i64>)> = HashMap::new();
    for (&(ord, off), g) in &markers.data {
        marker_relocs.insert(
            g.index() as u32,
            (R_WASM_MEMORY_ADDR_SLEB, data_sym_base + ord, Some(off)),
        );
    }
    for (&ord, g) in &markers.funcs {
        marker_relocs.insert(g.index() as u32, (R_WASM_TABLE_INDEX_SLEB, ord, None));
    }
    if let Some(g) = markers.stack_limit {
        marker_relocs.insert(g.index() as u32, (R_CLIF2WASM_STACK_LIMIT, u32::MAX, None));
    }

    let mctx = ModCtx {
        callees: &wfuncs,
        testcase_callees: &testcase_callees,
        mem0,
        shared_memory: opts.shared_memory,
        sp_global,
        table,
        libcalls: &libcall_map,
        object_markers: &markers,
    };
    let mut bodies = Vec::with_capacity(defined_fn_ords.len());
    let mut uses_tail_call = false;
    for &k in &defined_fn_ords {
        let f = &funcs[k];
        let body = if force_stub.contains(&k) {
            unreachable_stub(&module, sigs[k])
        } else {
            match translate_body(
                f,
                k,
                &mut module,
                &mut sig_cache,
                &sigs,
                &mctx,
                opts.lenient,
            ) {
                Ok(body) => body,
                // Lenient (sysroot) mode: an untranslatable BODY becomes a trap stub
                // with a reported gap line; stubbed bodies only matter if called.
                Err(e) if opts.lenient => {
                    eprintln!(
                        "clif2wasm-gap: body stubbed: {} ({})",
                        f.name,
                        first_line(&format!("{e:#}"))
                    );
                    unreachable_stub(&module, sigs[k])
                }
                Err(e) => return Err(e),
            }
        };
        let compiled = WasmFuncBackend::compile(&body).map_err(|e| {
            crate::error::Error::general(format!("waffle backend compile of `{}`: {e}", f.name))
        })?;
        let (bytes, relocs) = splice_body(
            &compiled.into_raw_body(),
            &fn_sym_of_wasm_index,
            sp_sym,
            table_sym,
            &marker_relocs,
            &mut uses_tail_call,
        )
        .with_context(|| format!("splicing function `{}`", f.name))?;
        bodies.push(Body {
            ord: k,
            bytes,
            relocs,
        });
    }

    Ok(Relocatable {
        funcs,
        data,
        signatures: module
            .signatures
            .entries()
            .map(|(_, sd)| sd.clone())
            .collect(),
        func_sigs: sigs.iter().map(|s| s.index() as u32).collect(),
        libcalls,
        bodies,
        uses_tail_call,
    })
}

/// Splice one compiled body: copy bytes verbatim, except at reloc-bearing
/// instructions, which are re-emitted with 5-byte padded LEB immediates and
/// recorded as relocations (offsets relative to the START OF THIS BODY's bytes).
///
/// Reloc-bearing sites: `call`/`return_call` (FUNCTION_INDEX_LEB via the function's
/// symbol), `call_indirect`/`return_call_indirect` (TYPE_INDEX_LEB on the type +
/// TABLE_NUMBER_LEB on the table),
/// `global.get/set` of the stack pointer (GLOBAL_INDEX_LEB). Any other global
/// index or a `ref.func` is a bug at this stage — B1.c introduces marker globals.
pub(crate) fn splice_body(
    body: &[u8],
    fn_sym_of_wasm_index: &[u32],
    sp_sym: u32,
    table_sym: u32,
    marker_relocs: &HashMap<u32, (u8, u32, Option<i64>)>,
    uses_tail_call: &mut bool,
) -> Result<(Vec<u8>, Vec<Reloc>)> {
    use wasmparser::Operator as Op;
    let mut out = Vec::with_capacity(body.len() + 32);
    let mut relocs = Vec::new();
    let fb = wasmparser::FunctionBody::new(wasmparser::BinaryReader::new(body, 0));
    let mut reader = fb
        .get_operators_reader()
        .context("reading Wasm operators")?;
    let mut copied_to = 0usize; // source offset up to which bytes are flushed
    while !reader.eof() {
        let op_start = usize::try_from(reader.original_position())
            .context("instruction offset exceeds address space")?;
        let op = reader.read().context("reading Wasm operator")?;
        let op_end = usize::try_from(reader.original_position())
            .context("instruction end exceeds address space")?;
        match op {
            Op::Call { function_index } | Op::ReturnCall { function_index } => {
                let tail = matches!(op, Op::ReturnCall { .. });
                *uses_tail_call |= tail;
                out.extend_from_slice(&body[copied_to..op_start]);
                out.push(if tail { 0x12 } else { 0x10 });
                let sym = *fn_sym_of_wasm_index
                    .get(function_index as usize)
                    .ok_or_else(|| {
                        crate::error::Error::general(format!(
                            "call to unknown function index {function_index}"
                        ))
                    })?;
                relocs.push(Reloc {
                    ty: R_WASM_FUNCTION_INDEX_LEB,
                    offset: out.len() as u32,
                    index: sym,
                    addend: None,
                });
                uleb_padded5(&mut out, function_index);
                copied_to = op_end;
            }
            Op::CallIndirect {
                type_index,
                table_index,
            }
            | Op::ReturnCallIndirect {
                type_index,
                table_index,
            } => {
                let tail = matches!(op, Op::ReturnCallIndirect { .. });
                *uses_tail_call |= tail;
                out.extend_from_slice(&body[copied_to..op_start]);
                out.push(if tail { 0x13 } else { 0x11 });
                relocs.push(Reloc {
                    ty: R_WASM_TYPE_INDEX_LEB,
                    offset: out.len() as u32,
                    index: type_index, // type index, not a symbol
                    addend: None,
                });
                uleb_padded5(&mut out, type_index);
                ensure!(
                    table_index == 0,
                    "call_indirect through table {table_index}"
                );
                relocs.push(Reloc {
                    ty: R_WASM_TABLE_NUMBER_LEB,
                    offset: out.len() as u32,
                    index: table_sym,
                    addend: None,
                });
                uleb_padded5(&mut out, table_index);
                copied_to = op_end;
            }
            Op::GlobalGet { global_index } => {
                out.extend_from_slice(&body[copied_to..op_start]);
                if global_index == 0 {
                    out.push(0x23);
                    relocs.push(Reloc {
                        ty: R_WASM_GLOBAL_INDEX_LEB,
                        offset: out.len() as u32,
                        index: sp_sym,
                        addend: None,
                    });
                    uleb_padded5(&mut out, 0);
                } else if let Some(&(ty, sym, addend)) = marker_relocs.get(&global_index) {
                    // Marker site: becomes a padded i32.const carrying a
                    // MEMORY_ADDR_SLEB / TABLE_INDEX_SLEB relocation.
                    out.push(0x41);
                    relocs.push(Reloc {
                        ty,
                        offset: out.len() as u32,
                        index: sym,
                        addend,
                    });
                    sleb_padded5(&mut out, 0);
                } else {
                    bail!("global.get {global_index} is neither the stack pointer nor a marker");
                }
                copied_to = op_end;
            }
            Op::GlobalSet { global_index } => {
                ensure!(
                    global_index == 0,
                    "global.set {global_index} in relocatable translation"
                );
                out.extend_from_slice(&body[copied_to..op_start]);
                out.push(0x24);
                relocs.push(Reloc {
                    ty: R_WASM_GLOBAL_INDEX_LEB,
                    offset: out.len() as u32,
                    index: sp_sym,
                    addend: None,
                });
                uleb_padded5(&mut out, 0);
                copied_to = op_end;
            }
            Op::RefFunc { .. } => {
                bail!(
                    "ref.func is unsupported in relocatable translation (unexpected from our lowering)"
                )
            }
            _ => {}
        }
    }
    out.extend_from_slice(&body[copied_to..]);
    Ok((out, relocs))
}
