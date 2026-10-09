//! Relocatable wasm object emission — the LLVM tool-conventions format:
//! <https://github.com/WebAssembly/tool-conventions/blob/main/Linking.md>.
//!
//! This is one of two consumers of `relocatable::translate` (the other is the
//! in-process linker in `link.rs`): undefined symbols stay undefined (function imports
//! from `env`), data becomes named segments placed by the linker, and a `linking`
//! custom section carries the symbol table. We own every byte, so reloc offsets fall
//! out of the byte stream.

use std::collections::HashMap;

use crate::error::Result;
use crate::relocatable::{
    R_WASM_MEMORY_ADDR_I32, R_WASM_TABLE_INDEX_I32, Reloc, Relocatable, TranslateOptions, sleb,
    uleb,
};
use crate::{bail, ensure};
use waffle::{SignatureData, Type};

pub use crate::relocatable::{ObjBinding, ObjData, ObjDataDef, ObjDef, ObjFunc};

// --- linking-section constants (tool-conventions Linking.md) ---
const WASM_SYMBOL_TABLE: u8 = 8;
const WASM_SEGMENT_INFO: u8 = 5;
const SYMTAB_FUNCTION: u8 = 0;
const SYMTAB_DATA: u8 = 1;
const SYMTAB_GLOBAL: u8 = 2;
const SYMTAB_TABLE: u8 = 5;
const WASM_SYM_BINDING_WEAK: u32 = 0x01;
const WASM_SYM_BINDING_LOCAL: u32 = 0x02;
const WASM_SYM_VISIBILITY_HIDDEN: u32 = 0x04;
const WASM_SYM_UNDEFINED: u32 = 0x10;

fn emit_reloc_section(w: &mut ObjWriter, name: &str, target_section: u32, relocs: &[Reloc]) {
    let mut p = Vec::new();
    uleb(&mut p, target_section as u64);
    uleb(&mut p, relocs.len() as u64);
    for r in relocs {
        p.push(r.ty);
        uleb(&mut p, r.offset as u64);
        uleb(&mut p, r.index as u64);
        if let Some(a) = r.addend {
            sleb(&mut p, a);
        }
    }
    w.custom(name, &p);
}

/// The target_features `+` set, matching what rustc's LLVM backend stamps on
/// wasm32-wasip1 objects (feature-union checked by wasm-ld).
const TARGET_FEATURES: &[&str] = &[
    "bulk-memory",
    "bulk-memory-opt",
    "call-indirect-overlong",
    "multivalue",
    "mutable-globals",
    "nontrapping-fptoint",
    "reference-types",
    "sign-ext",
];

fn write_name(out: &mut Vec<u8>, s: &str) {
    uleb(out, s.len() as u64);
    out.extend_from_slice(s.as_bytes());
}

fn valtype_byte(t: Type) -> Result<u8> {
    Ok(match t {
        Type::I32 => 0x7f,
        Type::I64 => 0x7e,
        Type::F32 => 0x7d,
        Type::F64 => 0x7c,
        Type::V128 => 0x7b,
        other => bail!("unsupported value type {other} in object emission"),
    })
}

/// Tracks emitted sections so reloc sections can name their target by ordinal
/// (0-based, counting every section entry in order of appearance).
struct ObjWriter {
    out: Vec<u8>,
    next_section: u32,
}

impl ObjWriter {
    fn new() -> Self {
        ObjWriter {
            out: b"\0asm\x01\0\0\0".to_vec(),
            next_section: 0,
        }
    }

    /// Emit one section; returns its ordinal.
    fn section(&mut self, id: u8, payload: &[u8]) -> u32 {
        self.out.push(id);
        uleb(&mut self.out, payload.len() as u64);
        self.out.extend_from_slice(payload);
        let ord = self.next_section;
        self.next_section += 1;
        ord
    }

    fn custom(&mut self, name: &str, payload: &[u8]) -> u32 {
        let mut p = Vec::with_capacity(name.len() + 1 + payload.len());
        write_name(&mut p, name);
        p.extend_from_slice(payload);
        self.section(0, &p)
    }
}

/// A symbol-table entry, in final symbol-index order (functions, then data, then
/// the synthetic global/table symbols).
enum Sym {
    Func {
        flags: u32,
        index: u32,
        name: Option<String>,
    },
    Data {
        flags: u32,
        name: String,
        def: Option<(u32, u32, u32)>,
    }, // (segment, offset, size)
    Global {
        flags: u32,
        index: u32,
    },
    Table {
        flags: u32,
        index: u32,
    },
}

fn binding_flags(binding: ObjBinding, hidden: bool) -> u32 {
    let mut f = match binding {
        ObjBinding::Global => 0,
        ObjBinding::Weak => WASM_SYM_BINDING_WEAK,
        ObjBinding::Local => WASM_SYM_BINDING_LOCAL,
    };
    if hidden {
        f |= WASM_SYM_VISIBILITY_HIDDEN;
    }
    f
}

/// Translate CLIF functions + data into a relocatable wasm object.
pub fn translate_object(funcs: &[ObjFunc], data: &[ObjData]) -> Result<Vec<u8>> {
    write_object(&crate::relocatable::translate(
        funcs,
        data,
        TranslateOptions::default(),
    )?)
}

fn write_object(rel: &Relocatable) -> Result<Vec<u8>> {
    let funcs = rel.funcs;
    let data = rel.data;
    let mut w = ObjWriter::new();

    // Object function index space: undefined functions, then libcall imports, then
    // defined functions — the order relocatable::translate allocated entities in.
    let import_fn_ords: Vec<usize> = (0..funcs.len())
        .filter(|&k| funcs[k].def.is_none())
        .collect();
    let mut fn_wasm_index = vec![0u32; funcs.len()];
    let mut next = 0u32;
    for &k in &import_fn_ords {
        fn_wasm_index[k] = next;
        next += 1;
    }
    let libcall_index_base = next;
    next += rel.libcalls.len() as u32;
    for body in &rel.bodies {
        fn_wasm_index[body.ord] = next;
        next += 1;
    }

    // type section: waffle signatures in entity order.
    let mut p = Vec::new();
    uleb(&mut p, rel.signatures.len() as u64);
    for sd in &rel.signatures {
        let SignatureData { params, returns } = sd;
        p.push(0x60);
        uleb(&mut p, params.len() as u64);
        for &t in params {
            p.push(valtype_byte(t)?);
        }
        uleb(&mut p, returns.len() as u64);
        for &t in returns {
            p.push(valtype_byte(t)?);
        }
    }
    w.section(1, &p);

    // import section: memory, stack-pointer global, funcref table, undefined fns,
    // libcalls — function order MUST match entity allocation above.
    let mut p = Vec::new();
    uleb(
        &mut p,
        (3 + import_fn_ords.len() + rel.libcalls.len()) as u64,
    );
    write_name(&mut p, "env");
    write_name(&mut p, "__linear_memory");
    p.extend_from_slice(&[0x02, 0x00, 0x01]); // memory, limits: min 1, no max
    write_name(&mut p, "env");
    write_name(&mut p, "__stack_pointer");
    p.extend_from_slice(&[0x03, 0x7f, 0x01]); // global, i32, mutable
    write_name(&mut p, "env");
    write_name(&mut p, "__indirect_function_table");
    p.extend_from_slice(&[0x01, 0x70, 0x00, 0x00]); // table, funcref, limits: min 0
    for &k in &import_fn_ords {
        write_name(&mut p, "env");
        write_name(&mut p, funcs[k].name);
        p.push(0x00); // func
        uleb(&mut p, rel.func_sigs[k] as u64);
    }
    for lc in &rel.libcalls {
        write_name(&mut p, "env");
        write_name(&mut p, lc.name);
        p.push(0x00); // func
        uleb(&mut p, lc.sig as u64);
    }
    w.section(2, &p);

    // function section: defined functions' signature indices, in entity order.
    let mut p = Vec::new();
    uleb(&mut p, rel.bodies.len() as u64);
    for body in &rel.bodies {
        uleb(&mut p, rel.func_sigs[body.ord] as u64);
    }
    w.section(3, &p);

    // data segments: every DEFINED data object, in input order.
    let segments: Vec<(usize, &ObjDataDef)> = data
        .iter()
        .enumerate()
        .filter_map(|(i, d)| d.def.as_ref().map(|def| (i, def)))
        .collect();

    if !segments.is_empty() {
        let mut p = Vec::new();
        uleb(&mut p, segments.len() as u64);
        w.section(12, &p); // DataCount
    }
    // Symbol index layout (must match the symbol table below): function symbols in
    // input order, then libcall symbols, then data symbols in input order, then
    // __stack_pointer, __indirect_function_table.
    let data_sym_base = rel.data_sym_base();

    // code section: bodies already carry padded reloc-site immediates; lay out the
    // section, rebasing reloc offsets onto the payload.
    let mut code_relocs: Vec<Reloc> = Vec::new();
    let mut p = Vec::new();
    uleb(&mut p, rel.bodies.len() as u64);
    for body in &rel.bodies {
        uleb(&mut p, body.bytes.len() as u64);
        let body_base = p.len() as u32;
        for r in &body.relocs {
            ensure!(
                r.ty != crate::relocatable::R_CLIF2WASM_STACK_LIMIT,
                "stack-limit relocation cannot be written to an object"
            );
            code_relocs.push(Reloc {
                ty: r.ty,
                offset: r.offset + body_base,
                index: r.index,
                addend: r.addend,
            });
        }
        p.extend_from_slice(&body.bytes);
    }
    let code_ord = w.section(10, &p);

    // data section: active segments with placeholder offsets (placement is the
    // linker's job, guided by SEGMENT_INFO); pointer slots become reloc.DATA
    // entries against the target's symbol, slots left as-is for the linker.
    let mut data_relocs: Vec<Reloc> = Vec::new();
    let mut data_ord = None;
    if !segments.is_empty() {
        let mut p = Vec::new();
        uleb(&mut p, segments.len() as u64);
        for (di, def) in &segments {
            p.push(0x00); // active, memory 0
            p.extend_from_slice(&[0x41, 0x00, 0x0b]); // i32.const 0; end
            uleb(&mut p, def.bytes.len() as u64);
            let seg_base = p.len() as u32;
            for r in &def.relocs {
                ensure!(
                    (r.offset as usize) + 4 <= def.bytes.len(),
                    "data `{}` reloc at {} overruns object of {} bytes",
                    data[*di].name,
                    r.offset,
                    def.bytes.len()
                );
                match r.target {
                    crate::DataRelocTarget::Data(ord) => {
                        ensure!(
                            (ord as usize) < data.len(),
                            "data reloc ordinal {ord} out of range"
                        );
                        data_relocs.push(Reloc {
                            ty: R_WASM_MEMORY_ADDR_I32,
                            offset: seg_base + r.offset,
                            index: data_sym_base + ord,
                            addend: Some(r.addend),
                        });
                    }
                    crate::DataRelocTarget::Func(ord) => {
                        ensure!(
                            (ord as usize) < funcs.len(),
                            "func reloc ordinal {ord} out of range"
                        );
                        ensure!(
                            r.addend == 0,
                            "function-address reloc with addend {}",
                            r.addend
                        );
                        data_relocs.push(Reloc {
                            ty: R_WASM_TABLE_INDEX_I32,
                            offset: seg_base + r.offset,
                            index: ord,
                            addend: None,
                        });
                    }
                }
            }
            p.extend_from_slice(&def.bytes);
        }
        data_ord = Some(w.section(11, &p));
    }

    // ---- symbol table ----
    let mut syms: Vec<Sym> = Vec::new();
    for (k, f) in funcs.iter().enumerate() {
        let mut flags = binding_flags(f.binding, f.hidden);
        let name = if f.def.is_some() {
            Some(f.name.to_string())
        } else {
            flags |= WASM_SYM_UNDEFINED;
            None // name comes from the import entry
        };
        syms.push(Sym::Func {
            flags,
            index: fn_wasm_index[k],
            name,
        });
    }
    for j in 0..rel.libcalls.len() {
        // Undefined; name comes from the import entry.
        syms.push(Sym::Func {
            flags: WASM_SYM_UNDEFINED,
            index: libcall_index_base + j as u32,
            name: None,
        });
    }
    // data-input ordinal -> segment index, for defined data.
    let mut seg_index: HashMap<usize, u32> = HashMap::new();
    for (si, (i, _)) in segments.iter().enumerate() {
        seg_index.insert(*i, si as u32);
    }
    for (i, d) in data.iter().enumerate() {
        let mut flags = binding_flags(d.binding, d.hidden);
        let def = match &d.def {
            Some(def) => Some((seg_index[&i], 0u32, def.bytes.len() as u32)),
            None => {
                flags |= WASM_SYM_UNDEFINED;
                None
            }
        };
        syms.push(Sym::Data {
            flags,
            name: d.name.to_string(),
            def,
        });
    }
    // Synthetic linker-provided references (always imported by this writer).
    syms.push(Sym::Global {
        flags: WASM_SYM_UNDEFINED,
        index: 0,
    });
    syms.push(Sym::Table {
        flags: WASM_SYM_UNDEFINED,
        index: 0,
    });

    // linking section: version 2, SYMBOL_TABLE + SEGMENT_INFO subsections.
    let mut link = Vec::new();
    uleb(&mut link, 2); // version

    let mut st = Vec::new();
    uleb(&mut st, syms.len() as u64);
    for s in &syms {
        match s {
            Sym::Func { flags, index, name } => {
                st.push(SYMTAB_FUNCTION);
                uleb(&mut st, *flags as u64);
                uleb(&mut st, *index as u64);
                if let Some(n) = name {
                    write_name(&mut st, n);
                }
            }
            Sym::Data { flags, name, def } => {
                st.push(SYMTAB_DATA);
                uleb(&mut st, *flags as u64);
                write_name(&mut st, name);
                if let Some((seg, off, size)) = def {
                    uleb(&mut st, *seg as u64);
                    uleb(&mut st, *off as u64);
                    uleb(&mut st, *size as u64);
                }
            }
            Sym::Global { flags, index } => {
                st.push(SYMTAB_GLOBAL);
                uleb(&mut st, *flags as u64);
                uleb(&mut st, *index as u64);
            }
            Sym::Table { flags, index } => {
                st.push(SYMTAB_TABLE);
                uleb(&mut st, *flags as u64);
                uleb(&mut st, *index as u64);
            }
        }
    }
    link.push(WASM_SYMBOL_TABLE);
    uleb(&mut link, st.len() as u64);
    link.extend_from_slice(&st);

    if !segments.is_empty() {
        let mut si = Vec::new();
        uleb(&mut si, segments.len() as u64);
        for (i, def) in &segments {
            ensure!(
                def.align.is_power_of_two(),
                "data `{}` align {} not a power of two",
                data[*i].name,
                def.align
            );
            write_name(&mut si, data[*i].name);
            uleb(&mut si, def.align.trailing_zeros() as u64); // log2
            uleb(&mut si, 0); // flags
        }
        link.push(WASM_SEGMENT_INFO);
        uleb(&mut link, si.len() as u64);
        link.extend_from_slice(&si);
    }
    w.custom("linking", &link);

    if !code_relocs.is_empty() {
        emit_reloc_section(&mut w, "reloc.CODE", code_ord, &code_relocs);
    }
    if !data_relocs.is_empty() {
        emit_reloc_section(
            &mut w,
            "reloc.DATA",
            data_ord.expect("data section exists"),
            &data_relocs,
        );
    }

    let mut features = TARGET_FEATURES.to_vec();
    if rel.uses_tail_call {
        features.push("tail-call");
    }
    let mut tf = Vec::new();
    uleb(&mut tf, features.len() as u64);
    for f in features {
        tf.push(b'+');
        write_name(&mut tf, f);
    }
    w.custom("target_features", &tf);

    Ok(w.out)
}
