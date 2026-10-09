//! In-process linker: turns the relocatable form into a complete wasm module.
//!
//! Whole-module output and incremental sessions are the same translation as a linkable
//! object; they differ only in the choices made here — where data lives, which table
//! slot a function gets (ordinal + 1, slot 0 stays null), whether memory, table and the
//! stack pointer are defined or imported, and which libcalls get synthesized bodies.

use std::borrow::Cow;

use waffle::wasm_encoder::{
    ConstExpr, DataSection, ElementSection, Elements, EntityType, ExportKind, ExportSection,
    FunctionSection, GlobalSection, GlobalType, ImportSection, MemorySection, MemoryType, NameMap,
    NameSection, RawSection, RefType, TableSection, TableType, TypeSection, ValType,
};

use crate::error::{Context, Result};
use crate::relocatable::{
    Body, R_CLIF2WASM_STACK_LIMIT, R_WASM_FUNCTION_INDEX_LEB, R_WASM_GLOBAL_INDEX_LEB,
    R_WASM_MEMORY_ADDR_SLEB, R_WASM_TABLE_INDEX_SLEB, R_WASM_TABLE_NUMBER_LEB,
    R_WASM_TYPE_INDEX_LEB, Relocatable, sleb, uleb,
};
use crate::{DataRelocTarget, bail, ensure};
use waffle::backend::WasmFuncBackend;
use waffle::{SignatureData, Type};

/// One 64KiB wasm page; the shadow stack starts at its top and grows down.
const STACK_TOP: u64 = 0x1_0000;
/// Statics are bump-allocated upward from here (0x0–0xFFF stays as a null guard);
/// they live below the shadow stack, which grows down from STACK_TOP.
const DATA_BASE: u32 = 0x1000;
/// Lowest address a session's shadow stack may reach (keeps the null page free).
const SESSION_STACK_LIMIT: u32 = 4096;

/// Incremental emission: the host owns memory, table and stack pointer; data
/// addresses were allocated up front and the first `initialized_data` objects were
/// already written by an earlier session.
pub(crate) struct SessionLayout<'a> {
    pub data_addresses: &'a [u32],
    pub initialized_data: usize,
}

pub(crate) struct LinkOptions<'a> {
    pub shared_memory_max_pages: Option<usize>,
    pub session: Option<SessionLayout<'a>>,
    /// (function ordinal, export name)
    pub exports: &'a [(usize, &'a str)],
}

fn val_type(t: Type) -> Result<ValType> {
    Ok(match t {
        Type::I32 => ValType::I32,
        Type::I64 => ValType::I64,
        Type::F32 => ValType::F32,
        Type::F64 => ValType::F64,
        Type::V128 => ValType::V128,
        other => bail!("unsupported value type {other} in linked module"),
    })
}

/// Rewrite a body's padded reloc sites with their resolved values, re-encoding each as
/// a minimal LEB.
fn apply_relocs(
    rel: &Relocatable,
    body: &Body,
    final_index: &[u32],
    data_addrs: &[u32],
    stack_limit: u32,
) -> Result<Vec<u8>> {
    let mut out = Vec::with_capacity(body.bytes.len());
    let mut copied_to = 0;
    for r in &body.relocs {
        let at = r.offset as usize;
        out.extend_from_slice(&body.bytes[copied_to..at]);
        match r.ty {
            R_WASM_FUNCTION_INDEX_LEB => uleb(&mut out, final_index[r.index as usize] as u64),
            R_WASM_TYPE_INDEX_LEB => uleb(&mut out, r.index as u64),
            R_WASM_TABLE_NUMBER_LEB | R_WASM_GLOBAL_INDEX_LEB => uleb(&mut out, 0),
            R_WASM_MEMORY_ADDR_SLEB => {
                let address = data_addrs[(r.index - rel.data_sym_base()) as usize] as i64
                    + r.addend.unwrap_or(0);
                sleb(&mut out, address as i32 as i64);
            }
            R_WASM_TABLE_INDEX_SLEB => sleb(&mut out, r.index as i64 + 1),
            R_CLIF2WASM_STACK_LIMIT => sleb(&mut out, stack_limit as i32 as i64),
            other => bail!("unexpected relocation type {other} while linking"),
        }
        copied_to = at + 5;
    }
    out.extend_from_slice(&body.bytes[copied_to..]);
    Ok(out)
}

pub(crate) fn link(rel: &Relocatable, opts: &LinkOptions) -> Result<Vec<u8>> {
    let funcs = &rel.funcs[..];
    let session = opts.session.as_ref();
    ensure!(
        session.is_none_or(|l| l.data_addresses.len() == rel.data.len()),
        "session data layout mismatch"
    );

    // Lay out static data objects: bump-allocate from DATA_BASE honoring per-object
    // alignment, or take the session's addresses.
    let mut data_addrs = Vec::with_capacity(rel.data.len());
    let mut cur = DATA_BASE;
    for (i, d) in rel.data.iter().enumerate() {
        let def = d
            .def
            .as_ref()
            .with_context(|| format!("data `{}` is declared but never defined", d.name))?;
        ensure!(
            def.align.is_power_of_two(),
            "data `{}` align {} not a power of two",
            d.name,
            def.align
        );
        cur = session.map_or((cur + def.align - 1) & !(def.align - 1), |l| {
            l.data_addresses[i]
        });
        data_addrs.push(cur);
        cur += def.bytes.len() as u32;
    }
    // Shadow stack lives ABOVE the statics: 64 KiB, 16-aligned base; memory sized to
    // fit (one page minimum — small modules keep the historical 0x10000 stack top).
    let statics_end = ((cur + 15) & !15) as u64;
    let stack_top = core::cmp::max(STACK_TOP, statics_end + 0x1_0000);
    let pages = stack_top.div_ceil(0x1_0000);
    let shared_memory = opts.shared_memory_max_pages.is_some();
    if let Some(max_pages) = opts.shared_memory_max_pages {
        ensure!(
            max_pages >= pages as usize,
            "shared memory maximum {max_pages} pages is below the module requirement of {pages} pages"
        );
    }
    let stack_limit = if session.is_some() {
        SESSION_STACK_LIMIT
    } else {
        statics_end as u32
    };

    // Apply data relocations now that every address is known: pointer slots get the
    // target's linear-memory address (data) or funcref-table index (function).
    let first_new_data = session.map_or(0, |l| l.initialized_data);
    let mut segments: Vec<(u32, Vec<u8>)> = Vec::new();
    for (i, d) in rel.data.iter().enumerate().skip(first_new_data) {
        let def = d.def.as_ref().unwrap();
        let mut bytes = def.bytes.clone();
        for r in &def.relocs {
            let value = match r.target {
                DataRelocTarget::Data(ord) => *data_addrs.get(ord as usize).with_context(|| {
                    format!("data `{}` reloc: data ordinal {ord} out of range", d.name)
                })? as i64,
                // Table slot 0 is null; function k lives at k+1.
                DataRelocTarget::Func(ord) => {
                    ensure!(
                        (ord as usize) < funcs.len(),
                        "data `{}` reloc: function ordinal {ord} out of range",
                        d.name
                    );
                    ord as i64 + 1
                }
            };
            let off = r.offset as usize;
            ensure!(
                off + 4 <= bytes.len(),
                "data `{}` reloc at {off} overruns object of {} bytes",
                d.name,
                bytes.len()
            );
            bytes[off..off + 4].copy_from_slice(&((value + r.addend) as u32).to_le_bytes());
        }
        segments.push((data_addrs[i], bytes));
    }

    // Function index space: imports first (input order), then defined functions
    // (input order), then synthesized libcall helpers.
    let mut final_index = vec![0u32; funcs.len() + rel.libcalls.len()];
    let mut next = 0u32;
    for (k, f) in funcs.iter().enumerate() {
        if f.def.is_none() {
            final_index[k] = next;
            next += 1;
        }
    }
    for body in &rel.bodies {
        final_index[body.ord] = next;
        next += 1;
    }
    for j in 0..rel.libcalls.len() {
        final_index[funcs.len() + j] = next;
        next += 1;
    }

    let mut module = waffle::wasm_encoder::Module::new();

    let mut types = TypeSection::new();
    for sd in &rel.signatures {
        let SignatureData { params, returns } = sd;
        types.ty().function(
            params
                .iter()
                .map(|&t| val_type(t))
                .collect::<Result<Vec<_>>>()?,
            returns
                .iter()
                .map(|&t| val_type(t))
                .collect::<Result<Vec<_>>>()?,
        );
    }
    module.section(&types);

    let memory_type = MemoryType {
        minimum: if session.is_some() { 0 } else { pages },
        maximum: opts.shared_memory_max_pages.map(|p| p as u64),
        memory64: false,
        shared: shared_memory,
        page_size_log2: None,
    };
    let mut imports = ImportSection::new();
    if session.is_some() {
        imports.import("env", "memory", EntityType::Memory(memory_type));
        imports.import(
            "env",
            "table",
            EntityType::Table(TableType {
                element_type: RefType::FUNCREF,
                minimum: 0,
                maximum: None,
                table64: false,
                shared: false,
            }),
        );
        imports.import(
            "env",
            "stack_pointer",
            EntityType::Global(GlobalType {
                val_type: ValType::I32,
                mutable: true,
                shared: false,
            }),
        );
    }
    for (k, f) in funcs.iter().enumerate() {
        if f.def.is_none() {
            imports.import("env", f.name, EntityType::Function(rel.func_sigs[k]));
        }
    }
    module.section(&imports);

    let mut function_section = FunctionSection::new();
    for body in &rel.bodies {
        function_section.function(rel.func_sigs[body.ord]);
    }
    for lc in &rel.libcalls {
        function_section.function(lc.sig);
    }
    module.section(&function_section);

    if session.is_none() {
        let slots = funcs.len() as u64 + 1;
        let mut tables = TableSection::new();
        tables.table(TableType {
            element_type: RefType::FUNCREF,
            minimum: slots,
            maximum: Some(slots),
            table64: false,
            shared: false,
        });
        module.section(&tables);

        let mut memories = MemorySection::new();
        memories.memory(memory_type);
        module.section(&memories);

        let mut globals = GlobalSection::new();
        globals.global(
            GlobalType {
                val_type: ValType::I32,
                mutable: true,
                shared: false,
            },
            &ConstExpr::i32_const(stack_top as i32),
        );
        module.section(&globals);
    }

    let mut exports = ExportSection::new();
    for &(ord, name) in opts.exports {
        exports.export(name, ExportKind::Func, final_index[ord]);
    }
    if shared_memory {
        ensure!(
            !opts.exports.iter().any(|&(_, name)| name == "memory"),
            "shared memory export name `memory` conflicts with a function export"
        );
        exports.export("memory", ExportKind::Memory, 0);
    }
    module.section(&exports);

    if session.is_none() {
        let mut elements = ElementSection::new();
        elements.active(
            Some(0),
            &ConstExpr::i32_const(1),
            Elements::Functions(Cow::Owned(final_index[..funcs.len()].to_vec())),
        );
        module.section(&elements);
    }

    let mut code = Vec::new();
    uleb(&mut code, (rel.bodies.len() + rel.libcalls.len()) as u64);
    for body in &rel.bodies {
        let bytes = apply_relocs(rel, body, &final_index, &data_addrs, stack_limit)
            .with_context(|| format!("linking function `{}`", funcs[body.ord].name))?;
        uleb(&mut code, bytes.len() as u64);
        code.extend_from_slice(&bytes);
    }
    if !rel.libcalls.is_empty() {
        let mut scratch = waffle::Module::empty();
        let mem0 = scratch.memories.push(waffle::MemoryData {
            initial_pages: 1,
            maximum_pages: None,
            segments: vec![],
            shared: shared_memory,
        });
        for lc in &rel.libcalls {
            let sig = scratch
                .signatures
                .push(rel.signatures[lc.sig as usize].clone());
            let body = crate::module::synth_runtime_body(lc.kind, &scratch, sig, mem0)?;
            let compiled = WasmFuncBackend::compile(&body)
                .map_err(|e| {
                    crate::error::Error::general(format!(
                        "waffle backend compile of `{}`: {e}",
                        lc.name
                    ))
                })?
                .into_raw_body();
            uleb(&mut code, compiled.len() as u64);
            code.extend_from_slice(&compiled);
        }
    }
    module.section(&RawSection {
        id: 10,
        data: &code,
    });

    if !segments.is_empty() {
        let mut data_section = DataSection::new();
        for (address, bytes) in &segments {
            data_section.active(
                0,
                &ConstExpr::i32_const(*address as i32),
                bytes.iter().copied(),
            );
        }
        module.section(&data_section);
    }

    let mut names: Vec<(u32, String)> = Vec::with_capacity(final_index.len());
    for (k, f) in funcs.iter().enumerate() {
        names.push((final_index[k], f.name.to_string()));
    }
    for (j, lc) in rel.libcalls.iter().enumerate() {
        names.push((
            final_index[funcs.len() + j],
            format!("__clif2wasm_{:?}", lc.kind),
        ));
    }
    names.sort_by_key(|&(index, _)| index);
    let mut function_names = NameMap::new();
    for (index, name) in &names {
        function_names.append(*index, name);
    }
    let mut name_section = NameSection::new();
    name_section.functions(&function_names);
    module.section(&name_section);

    Ok(module.finish())
}
