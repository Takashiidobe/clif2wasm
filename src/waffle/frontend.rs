//! Frontend: convert Wasm to IR.

#![allow(dead_code)]

use crate::waffle::entity::EntityRef;
use crate::waffle::errors::FrontendError;
use crate::waffle::ir::*;
use crate::waffle::op_traits::{op_inputs, op_outputs};
use crate::waffle::ops::Operator;
#[cfg(feature = "dwarf")]
use addr2line::gimli;
use anyhow::{bail, Result};
use fxhash::{FxHashMap, FxHashSet};
use log::trace;
use std::convert::TryFrom;
use wasmparser_248::{BlockType, DataKind, ExternalKind, KnownCustom, Name, Parser, Payload, TypeRef};

/// Options to control the Wasm-to-bytecode translation process.
#[derive(Clone, Copy, Debug, Default)]
pub struct FrontendOptions {
    /// Preserve DWARF debug-info. Otherwise, it is discarded if
    /// present.
    pub debug: bool,
}

/// Convert the given bytecode to a `Module`.
pub(crate) fn wasm_to_ir<'a>(bytes: &'a [u8], options: &FrontendOptions) -> Result<Module<'a>> {
    let mut module = Module::with_orig_bytes(bytes);
    let parser = Parser::new(0);
    let mut next_func = 0;
    #[cfg(feature = "dwarf")]
    let mut dwarf = gimli::Dwarf::default();
    let mut extra_sections = ExtraSections::default();
    for payload in parser.parse_all(bytes) {
        let payload = payload?;
        handle_payload(
            &mut module,
            payload,
            &mut next_func,
            #[cfg(feature = "dwarf")]
            &mut dwarf,
            &mut extra_sections,
        )?;
    }
    #[cfg(feature = "dwarf")]
    {
        dwarf.locations =
            gimli::LocationLists::new(extra_sections.debug_loc, extra_sections.debug_loclists);
        dwarf.ranges =
            gimli::RangeLists::new(extra_sections.debug_ranges, extra_sections.debug_rnglists);

        if options.debug {
            let debug_map =
                DebugMap::from_dwarf(dwarf, &mut module.debug, extra_sections.code_offset)?;
            module.debug_map = debug_map;
        }
    }
    #[cfg(not(feature = "dwarf"))]
    {
        let _ = options.debug;
    }

    Ok(module)
}

fn parse_init_expr<'a>(init_expr: &wasmparser_248::ConstExpr<'a>) -> Result<Option<u64>> {
    let operators = init_expr
        .get_operators_reader()
        .into_iter()
        .collect::<Result<Vec<wasmparser_248::Operator>, _>>()?;
    if operators.len() == 1 && matches!(&operators[0], &wasmparser_248::Operator::End) {
        return Ok(None);
    }
    if operators.len() != 2 || !matches!(&operators[1], &wasmparser_248::Operator::End) {
        bail!(FrontendError::UnsupportedFeature(format!(
            "Unsupported operator seq in base-address expr: {:?}",
            operators
        )));
    }
    Ok(match &operators[0] {
        &wasmparser_248::Operator::I32Const { value } => Some(value as u64),
        &wasmparser_248::Operator::I64Const { value } => Some(value as u64),
        &wasmparser_248::Operator::F32Const { value } => Some(value.bits() as u64),
        &wasmparser_248::Operator::F64Const { value } => Some(value.bits()),
        op => anyhow::bail!(FrontendError::UnsupportedFeature(format!(
            "Unsupported data segment base-address operator: {:?}",
            op
        ))),
    })
}

#[derive(Default)]
struct ExtraSections<'a> {
    #[cfg(feature = "dwarf")]
    debug_loc: gimli::DebugLoc<gimli::EndianSlice<'a, gimli::LittleEndian>>,
    #[cfg(feature = "dwarf")]
    debug_loclists: gimli::DebugLocLists<gimli::EndianSlice<'a, gimli::LittleEndian>>,
    #[cfg(feature = "dwarf")]
    debug_ranges: gimli::DebugRanges<gimli::EndianSlice<'a, gimli::LittleEndian>>,
    #[cfg(feature = "dwarf")]
    debug_rnglists: gimli::DebugRngLists<gimli::EndianSlice<'a, gimli::LittleEndian>>,
    code_offset: u32,
    #[cfg(not(feature = "dwarf"))]
    _phantom: std::marker::PhantomData<&'a ()>,
}

fn handle_payload<'a>(
    module: &mut Module<'a>,
    payload: Payload<'a>,
    next_func: &mut usize,
    #[cfg(feature = "dwarf")] dwarf: &mut gimli::Dwarf<gimli::EndianSlice<'a, gimli::LittleEndian>>,
    extra_sections: &mut ExtraSections<'a>,
) -> Result<()> {
    trace!("Wasm parser item: {:?}", payload);
    match payload {
        Payload::TypeSection(reader) => {
            for rec_group in reader {
                for ty in rec_group?.into_types() {
                    match &ty.composite_type.inner {
                        wasmparser_248::CompositeInnerType::Func(fty) => {
                            module.signatures.push(fty.into());
                        }
                        _ => bail!(FrontendError::UnsupportedFeature(
                            "non-function type in type section".into()
                        )),
                    }
                }
            }
        }
        Payload::ImportSection(reader) => {
            for imports in reader {
                let imports = imports?;
                let mut handle = |module_name: &str, name: &str, ty: TypeRef| -> Result<()> {
                    let module_name = module_name.to_owned();
                    let name = name.to_owned();
                    let kind = match ty {
                        TypeRef::Func(sig_idx) | TypeRef::FuncExact(sig_idx) => {
                            let func = module
                                .funcs
                                .push(FuncDecl::Import(Signature::from(sig_idx), "".to_owned()));
                            *next_func += 1;
                            ImportKind::Func(func)
                        }
                        TypeRef::Global(ty) => {
                            let mutable = ty.mutable;
                            let ty = ty.content_type.into();
                            let global = module.globals.push(GlobalData {
                                ty,
                                value: None,
                                mutable,
                            });
                            ImportKind::Global(global)
                        }
                        TypeRef::Table(ty) => {
                            let table = module.tables.push(TableData {
                                ty: ty.element_type.into(),
                                initial: ty.initial,
                                max: ty.maximum,
                                func_elements: Some(vec![]),
                            });
                            ImportKind::Table(table)
                        }
                        TypeRef::Memory(mem) => {
                            let mem = module.memories.push(MemoryData {
                                initial_pages: mem.initial as usize,
                                maximum_pages: mem.maximum.map(|max| max as usize),
                                segments: vec![],
                                shared: mem.shared,
                            });
                            ImportKind::Memory(mem)
                        }
                        t => {
                            bail!(FrontendError::UnsupportedFeature(format!(
                                "Unknown import type: {:?}",
                                t
                            )));
                        }
                    };
                    module.imports.push(Import {
                        module: module_name,
                        name,
                        kind,
                    });
                    Ok(())
                };
                match imports {
                    wasmparser_248::Imports::Single(_, import) => {
                        handle(import.module, import.name, import.ty)?;
                    }
                    wasmparser_248::Imports::Compact1 { module: m, items } => {
                        for item in items {
                            let item = item?;
                            handle(m, item.name, item.ty)?;
                        }
                    }
                    wasmparser_248::Imports::Compact2 {
                        module: m,
                        ty,
                        names,
                    } => {
                        for name in names {
                            let name = name?;
                            handle(m, name, ty)?;
                        }
                    }
                }
            }
        }
        Payload::GlobalSection(reader) => {
            for global in reader {
                let global = global?;
                let mutable = global.ty.mutable;
                let ty = global.ty.content_type.into();
                let init_expr = parse_init_expr(&global.init_expr)?;
                module.globals.push(GlobalData {
                    ty,
                    value: init_expr,
                    mutable,
                });
            }
        }
        Payload::TableSection(reader) => {
            for table in reader {
                let table = table?;
                module.tables.push(TableData {
                    ty: table.ty.element_type.into(),
                    initial: table.ty.initial,
                    max: table.ty.maximum,
                    func_elements: Some(vec![]),
                });
            }
        }
        Payload::FunctionSection(reader) => {
            for sig_idx in reader {
                let sig_idx = Signature::from(sig_idx?);
                module.funcs.push(FuncDecl::Body(
                    sig_idx,
                    "".to_owned(),
                    FunctionBody::default(),
                ));
            }
        }
        Payload::CodeSectionStart { range, .. } => {
            extra_sections.code_offset = range.start as u32;
        }
        Payload::CodeSectionEntry(body) => {
            let func_idx = Func::new(*next_func);
            *next_func += 1;

            let sig = module.funcs[func_idx].sig();
            let name = module.funcs[func_idx].name().to_owned();
            module.funcs[func_idx] = FuncDecl::Lazy(sig, name, body);
        }
        Payload::ExportSection(reader) => {
            for export in reader {
                let export = export?;
                let name = export.name.to_owned();
                let kind = match export.kind {
                    ExternalKind::Func => Some(ExportKind::Func(Func::from(export.index))),
                    ExternalKind::Table => Some(ExportKind::Table(Table::from(export.index))),
                    ExternalKind::Global => Some(ExportKind::Global(Global::from(export.index))),
                    ExternalKind::Memory => Some(ExportKind::Memory(Memory::from(export.index))),
                    _ => None,
                };
                if let Some(kind) = kind {
                    module.exports.push(Export { name, kind });
                }
            }
        }
        Payload::MemorySection(reader) => {
            for memory in reader {
                let memory = memory?;
                module.memories.push(MemoryData {
                    initial_pages: memory.initial as usize,
                    maximum_pages: memory.maximum.map(|max| max as usize),
                    segments: vec![],
                    shared: memory.shared,
                });
            }
        }
        Payload::DataSection(reader) => {
            for segment in reader {
                let segment = segment?;
                match &segment.kind {
                    DataKind::Passive => {}
                    DataKind::Active {
                        memory_index,
                        offset_expr,
                    } => {
                        let data = segment.data.to_vec();
                        let memory = Memory::from(*memory_index);
                        let offset = parse_init_expr(offset_expr)?.unwrap_or(0) as usize;
                        module.memories[memory]
                            .segments
                            .push(MemorySegment { offset, data });
                    }
                }
            }
        }
        Payload::CustomSection(reader) => {
            let handled = match reader.as_known() {
                KnownCustom::Name(name_reader) => {
                    for subsection in name_reader {
                        let subsection = subsection?;
                        match subsection {
                            Name::Function(names) => {
                                for name in names {
                                    let name = name?;
                                    module.funcs[Func::new(name.index as usize)]
                                        .set_name(name.name);
                                }
                            }
                            _ => {}
                        }
                    }
                    true
                }
                KnownCustom::Unknown => {
                    #[cfg(feature = "dwarf")]
                    {
                        if reader.name() == ".debug_info" {
                            dwarf.debug_info =
                                gimli::DebugInfo::new(reader.data(), gimli::LittleEndian);
                            true
                        } else if reader.name() == ".debug_abbrev" {
                            dwarf.debug_abbrev =
                                gimli::DebugAbbrev::new(reader.data(), gimli::LittleEndian);
                            true
                        } else if reader.name() == ".debug_addr" {
                            dwarf.debug_addr = gimli::DebugAddr::from(gimli::EndianSlice::new(
                                reader.data(),
                                gimli::LittleEndian,
                            ));
                            true
                        } else if reader.name() == ".debug_aranges" {
                            dwarf.debug_aranges =
                                gimli::DebugAranges::new(reader.data(), gimli::LittleEndian);
                            true
                        } else if reader.name() == ".debug_line" {
                            dwarf.debug_line =
                                gimli::DebugLine::new(reader.data(), gimli::LittleEndian);
                            true
                        } else if reader.name() == ".debug_line_str" {
                            dwarf.debug_line_str =
                                gimli::DebugLineStr::new(reader.data(), gimli::LittleEndian);
                            true
                        } else if reader.name() == ".debug_str" {
                            dwarf.debug_str =
                                gimli::DebugStr::new(reader.data(), gimli::LittleEndian);
                            true
                        } else if reader.name() == ".debug_str_offsets" {
                            dwarf.debug_str_offsets = gimli::DebugStrOffsets::from(
                                gimli::EndianSlice::new(reader.data(), gimli::LittleEndian),
                            );
                            true
                        } else if reader.name() == ".debug_types" {
                            dwarf.debug_types =
                                gimli::DebugTypes::new(reader.data(), gimli::LittleEndian);
                            true
                        } else if reader.name() == ".debug_loc" {
                            extra_sections.debug_loc =
                                gimli::DebugLoc::new(reader.data(), gimli::LittleEndian);
                            true
                        } else if reader.name() == ".debug_loclists" {
                            extra_sections.debug_loclists =
                                gimli::DebugLocLists::new(reader.data(), gimli::LittleEndian);
                            true
                        } else if reader.name() == ".debug_ranges" {
                            extra_sections.debug_ranges =
                                gimli::DebugRanges::new(reader.data(), gimli::LittleEndian);
                            true
                        } else if reader.name() == ".debug_rnglists" {
                            extra_sections.debug_rnglists =
                                gimli::DebugRngLists::new(reader.data(), gimli::LittleEndian);
                            true
                        } else {
                            false
                        }
                    }
                    #[cfg(not(feature = "dwarf"))]
                    {
                        false
                    }
                }
                _ => false,
            };

            if !handled {
                module
                    .custom_sections
                    .insert(reader.name().to_owned(), reader.data());
            }
        }
        Payload::Version { .. } => {}
        Payload::ElementSection(reader) => {
            for element in reader {
                let element = element?;
                match &element.kind {
                    wasmparser_248::ElementKind::Passive => {}
                    wasmparser_248::ElementKind::Declared => {}
                    wasmparser_248::ElementKind::Active {
                        table_index,
                        offset_expr,
                    } => {
                        let table = Table::from(table_index.unwrap_or(0));
                        let offset = parse_init_expr(&offset_expr)?.unwrap_or(0) as usize;
                        let funcs = match element.items {
                            wasmparser_248::ElementItems::Functions(items) => {
                                let mut funcs = vec![];
                                for item in items {
                                    let item = item?;
                                    let func = Func::from(item);
                                    funcs.push(func);
                                }
                                funcs
                            }
                            wasmparser_248::ElementItems::Expressions(_, const_exprs) => {
                                let mut funcs = vec![];
                                for const_expr in const_exprs {
                                    let const_expr = const_expr?;
                                    let mut func = None;
                                    for op in const_expr.get_operators_reader() {
                                        let op = op?;
                                        match op {
                                            wasmparser_248::Operator::End => {}
                                            wasmparser_248::Operator::RefFunc { function_index } => {
                                                func = Some(Func::from(function_index));
                                            }
                                            wasmparser_248::Operator::RefNull { .. } => {
                                                func = Some(Func::invalid());
                                            }
                                            _ => panic!("Unsupported table-init op: {:?}", op),
                                        }
                                    }
                                    funcs.push(func.unwrap_or(Func::invalid()));
                                }
                                funcs
                            }
                        };

                        let table_items = module.tables[table].func_elements.as_mut().unwrap();
                        let new_size = offset.checked_add(funcs.len()).ok_or_else(|| {
                            FrontendError::TooLarge(format!(
                                "Overflowing element offset + length: {} + {}",
                                offset,
                                funcs.len()
                            ))
                        })?;
                        if new_size > table_items.len() {
                            static MAX_TABLE: usize = 100_000;
                            if new_size > MAX_TABLE {
                                bail!(FrontendError::TooLarge(format!(
                                    "Too many table elements: {:?}",
                                    new_size
                                )));
                            }
                            table_items.resize(new_size, Func::invalid());
                        }
                        table_items[offset..new_size].copy_from_slice(&funcs[..]);
                    }
                }
            }
        }
        Payload::End(_) => {}
        Payload::StartSection { func, .. } => {
            module.start_func = Some(Func::from(func));
        }
        payload => {
            log::warn!("Skipping section: {:?}", payload);
        }
    }

    Ok(())
}

struct DebugLocReader<'a> {
    code_offset: u32,
    locs: &'a [(u32, u32, SourceLoc)],
}

impl<'a> DebugLocReader<'a> {
    fn new(module: &'a Module, func_offset_in_file: u32) -> Self {
        let code_offset = module.debug_map.code_offset;
        let func_address = func_offset_in_file - code_offset;
        let start = match module
            .debug_map
            .tuples
            .binary_search_by(|&(start, len, _)| {
                use std::cmp::Ordering::*;
                if start > func_address {
                    Greater
                } else if (start + len) <= func_address {
                    Less
                } else {
                    Equal
                }
            }) {
            Ok(idx) => idx,
            Err(idx) => idx,
        };
        DebugLocReader {
            code_offset,
            locs: &module.debug_map.tuples[start..],
        }
    }

    fn get_loc(&mut self, offset: usize) -> SourceLoc {
        let address = u32::try_from(offset).unwrap() - self.code_offset;
        while self.locs.len() > 0 {
            let (start, len, loc) = self.locs[0];
            if address < start {
                break;
            }
            if address < start + len {
                return loc;
            }
            self.locs = &self.locs[1..];
        }
        SourceLoc::invalid()
    }
}

pub(crate) fn parse_body<'a>(
    module: &'a Module,
    my_sig: Signature,
    body: &mut wasmparser_248::FunctionBody,
) -> Result<FunctionBody> {
    let mut ret: FunctionBody = FunctionBody::default();

    let mut debug_locs = DebugLocReader::new(module, body.range().start as u32);

    for &param in &module.signatures[my_sig].params[..] {
        ret.locals.push(param.into());
    }
    ret.n_params = module.signatures[my_sig].params.len();
    for &r in &module.signatures[my_sig].returns[..] {
        ret.rets.push(r.into());
    }

    let mut locals = body.get_locals_reader()?;
    for _ in 0..locals.get_count() {
        let (count, ty) = locals.read()?;
        for _ in 0..count {
            ret.locals.push(ty.into());
        }
    }
    let locals = ret.locals.clone();

    trace!(
        "Parsing function body: locals = {:?} sig = {:?}",
        ret.locals,
        module.signatures[my_sig]
    );

    let mut builder = FunctionBodyBuilder::new(module, my_sig, &mut ret);
    let entry = Block::new(0);
    builder.body.entry = entry;
    builder.locals.seal_block_preds(entry, &mut builder.body);
    builder.locals.start_block(entry);

    for (arg_idx, &arg_ty) in module.signatures[my_sig].params.iter().enumerate() {
        let local_idx = Local::new(arg_idx);
        builder.body.add_blockparam(entry, arg_ty);
        let value = builder.body.blocks[entry].params.last().unwrap().1;
        trace!("defining local {} to value {}", local_idx, value);
        builder.locals.declare(local_idx, arg_ty);
        builder.locals.set(local_idx, value);
    }

    let n_args = module.signatures[my_sig].params.len();
    for (offset, local_ty) in locals.values().enumerate() {
        let local_idx = Local::new(n_args + offset);
        builder.locals.declare(local_idx, *local_ty);
    }

    let ops = body.get_operators_reader()?;
    for item in ops.into_iter_with_offsets() {
        let (op, offset) = item?;
        let loc = debug_locs.get_loc(offset);
        if builder.reachable {
            builder.handle_op(op, loc)?;
        } else {
            builder.handle_op_unreachable(op)?;
        }
    }

    if builder.reachable {
        builder.handle_op(wasmparser_248::Operator::Return, SourceLoc::invalid())?;
    }

    for block in builder.body.blocks.iter() {
        log::trace!("checking if block is sealed: {}", block);
        debug_assert!(builder.locals.is_sealed(block));
    }
    for value in builder.body.values.values() {
        debug_assert!(!matches!(value, &ValueDef::Placeholder(_)));
    }

    trace!("Final function body:{:?}", ret);

    Ok(ret)
}

/// State used to construct SSA from Wasm locals.
#[derive(Debug, Clone, Default)]
struct LocalTracker {
    /// Types of locals, as declared.
    types: FxHashMap<Local, Type>,
    /// The current block.
    cur_block: Block,
    /// In some block?
    in_block: bool,
    /// Is the given block sealed?
    block_sealed: FxHashSet<Block>,
    /// The local-to-value mapping at the start of a block.
    block_start: FxHashMap<Block, FxHashMap<Local, Value>>,
    /// The local-to-value mapping at the end of a block.
    block_end: FxHashMap<Block, FxHashMap<Local, Value>>,
    /// Mapping from locals to SSA values within the current block.
    in_cur_block: FxHashMap<Local, Value>,
    /// Blockparams (phis) that are still `Placeholder`.
    incomplete_phis: FxHashMap<Block, Vec<(Local, Value)>>,
}

impl LocalTracker {
    pub fn declare(&mut self, local: Local, ty: Type) {
        let was_present = self.types.insert(local, ty).is_some();
        assert!(!was_present);
    }

    pub fn start_block(&mut self, block: Block) {
        log::trace!("start_block: block {}", block);
        assert!(!self.in_block);
        self.in_block = true;
        self.cur_block = block;
    }

    pub fn finish_block(&mut self, reachable: bool) {
        if !self.in_block {
            assert!(!reachable);
            return;
        }
        log::trace!("finish_block: block {}", self.cur_block);
        if reachable {
            let mapping = std::mem::take(&mut self.in_cur_block);
            log::trace!(" -> mapping: {:?}", mapping);
            let old_mapping = self.block_end.insert(self.cur_block, mapping);
            assert!(
                old_mapping.is_none(),
                "Mapping already present for {}: {:?}",
                self.cur_block,
                old_mapping
            );
        } else {
            self.in_cur_block.clear();
            self.block_end.insert(self.cur_block, FxHashMap::default());
        }
        self.in_block = false;
    }

    pub fn seal_block_preds(&mut self, block: Block, body: &mut FunctionBody) {
        log::trace!("seal_block_preds: block {}", block);
        let not_sealed = self.block_sealed.insert(block);
        assert!(not_sealed);
        for (local, phi_value) in self
            .incomplete_phis
            .remove(&block)
            .unwrap_or_else(|| vec![])
        {
            self.compute_blockparam(body, block, local, phi_value);
        }
    }

    fn is_sealed(&self, block: Block) -> bool {
        self.block_sealed.contains(&block)
    }

    pub fn set(&mut self, local: Local, value: Value) {
        log::trace!("set: local {} value {:?}", local, value);
        self.in_cur_block.insert(local, value);
    }

    fn get_in_block(&mut self, body: &mut FunctionBody, at_block: Block, local: Local) -> Value {
        log::trace!(
            "get_in_block: at_block {} local {} cur_block {}",
            at_block,
            local,
            self.cur_block
        );
        let ty = body.locals[local];

        if self.cur_block == at_block {
            if let Some(&value) = self.in_cur_block.get(&local) {
                log::trace!(" -> {:?}", value);
                return value;
            }
        }

        if self.is_sealed(at_block) {
            if let Some(end_mapping) = self.block_end.get(&at_block) {
                if let Some(&value) = end_mapping.get(&local) {
                    log::trace!(" -> from end_mapping: {:?}", value);
                    return value;
                }
            }

            if body.blocks[at_block].preds.is_empty() {
                let value = self.create_default_value(body, ty, at_block);
                log::trace!(" -> created default: {:?}", value);
                return value;
            }

            let placeholder = body.add_placeholder(ty);
            body.mark_value_as_local(placeholder, local);
            if at_block == self.cur_block {
                self.in_cur_block.insert(local, placeholder);
            } else {
                self.block_end
                    .get_mut(&at_block)
                    .unwrap()
                    .insert(local, placeholder);
            }
            log::trace!(" -> created placeholder: {:?}", placeholder);
            self.compute_blockparam(body, at_block, local, placeholder);
            placeholder
        } else {
            if let Some(end_mapping) = self.block_end.get(&at_block) {
                if let Some(&value) = end_mapping.get(&local) {
                    log::trace!(" -> from end_mapping: {:?}", value);
                    return value;
                }
            }

            let placeholder = body.add_placeholder(ty);
            body.mark_value_as_local(placeholder, local);
            if at_block == self.cur_block {
                self.in_cur_block.insert(local, placeholder);
            } else {
                self.block_end
                    .get_mut(&at_block)
                    .unwrap()
                    .insert(local, placeholder);
            }
            log::trace!(
                " -> created placeholder and added as incomplete phi: {:?}",
                placeholder
            );
            self.incomplete_phis
                .entry(at_block)
                .or_insert_with(|| vec![])
                .push((local, placeholder));

            placeholder
        }
    }

    pub fn get(&mut self, body: &mut FunctionBody, local: Local) -> Value {
        self.get_in_block(body, self.cur_block, local)
    }

    fn create_default_value(
        &mut self,
        body: &mut FunctionBody,
        ty: Type,
        at_block: Block,
    ) -> Value {
        let val = match ty {
            Type::I32 => body.add_op(at_block, Operator::I32Const { value: 0 }, &[], &[ty]),
            Type::I64 => body.add_op(at_block, Operator::I64Const { value: 0 }, &[], &[ty]),
            Type::F32 => body.add_op(at_block, Operator::F32Const { value: 0 }, &[], &[ty]),
            Type::F64 => body.add_op(at_block, Operator::F64Const { value: 0 }, &[], &[ty]),
            Type::V128 => body.add_op(at_block, Operator::V128Const { value: 0 }, &[], &[ty]),
            _ => todo!("unsupported type: {:?}", ty),
        };
        log::trace!(
            "created default value {} of type {} at block {}",
            val,
            ty,
            at_block
        );
        val
    }

    fn compute_blockparam(
        &mut self,
        body: &mut FunctionBody,
        block: Block,
        local: Local,
        value: Value,
    ) {
        log::trace!(
            "compute_blockparam: block {} local {} value {:?}",
            block,
            local,
            value
        );
        let mut results: Vec<Value> = vec![];
        let preds = body.blocks[block].preds.clone();
        for pred in preds {
            let pred_value = self.get_in_block(body, pred, local);
            log::trace!(
                "compute_blockparam: block {} local {} value {:?}: pred {} -> {:?}",
                block,
                local,
                value,
                pred,
                pred_value
            );
            results.push(pred_value);
        }

        let mut non_self = results.iter().filter(|&&v| v != value);
        let trivial_alias = match non_self.next() {
            None => None,
            Some(&first) if non_self.all(|&v| v == first) && body.resolve_alias(first) != value => {
                Some(first)
            }
            Some(_) => None,
        };

        if let Some(v) = trivial_alias {
            log::trace!(
                "compute_blockparam: block {} local {} value {:?}: alias to {:?}",
                block,
                local,
                value,
                v
            );
            body.set_alias(value, v);
        } else {
            log::trace!(
                "compute_blockparam: block {} local {} value {:?}: making blockparam",
                block,
                local,
                value,
            );
            body.replace_placeholder_with_blockparam(block, value);
            for (i, (&pred, result)) in body.blocks[block]
                .preds
                .clone()
                .iter()
                .zip(results.into_iter())
                .enumerate()
            {
                let index = body.blocks[block].pos_in_pred_succ[i];
                body.blocks[pred].terminator.update_target(index, |target| {
                    log::trace!(
                        "compute_blockparam: block {} local {} value {:?}: in pred {}, adding branch arg {:?}",
                        block,
                        local,
                        value,
                        pred,
                        result,
                    );
                    target.args.push(result);
                });
            }
        }
    }
}

/// State used to build an SSA CFG from Wasm structured control flow
/// with locals.
#[derive(Debug)]
struct FunctionBodyBuilder<'a, 'b> {
    module: &'b Module<'a>,
    my_sig: Signature,
    body: &'b mut FunctionBody,
    locals: LocalTracker,
    cur_block: Block,
    reachable: bool,
    ctrl_stack: Vec<Frame>,
    op_stack: Vec<(Type, Value)>,
}

/// A frame in the Wasm control stack, mapping to IR entities for
/// associated label targets and block-parameter values.
#[derive(Clone, Debug)]
enum Frame {
    Block {
        start_depth: usize,
        out: Block,
        params: Vec<Type>,
        results: Vec<Type>,
        out_reachable: bool,
    },
    Loop {
        start_depth: usize,
        header: Block,
        out: Block,
        params: Vec<Type>,
        results: Vec<Type>,
    },
    If {
        start_depth: usize,
        out: Block,
        el: Block,
        param_values: Vec<(Type, Value)>,
        params: Vec<Type>,
        results: Vec<Type>,
        head_reachable: bool,
        merge_reachable: bool,
    },
    Else {
        start_depth: usize,
        out: Block,
        params: Vec<Type>,
        results: Vec<Type>,
        merge_reachable: bool,
    },
}

impl Frame {
    fn start_depth(&self) -> usize {
        match self {
            Frame::Block { start_depth, .. }
            | Frame::Loop { start_depth, .. }
            | Frame::If { start_depth, .. }
            | Frame::Else { start_depth, .. } => *start_depth,
        }
    }

    fn br_args(&self) -> &[Type] {
        match self {
            Frame::Block { results, .. }
            | Frame::If { results, .. }
            | Frame::Else { results, .. } => &results[..],
            Frame::Loop { params, .. } => &params[..],
        }
    }

    fn br_target(&self) -> Block {
        match self {
            Frame::Block { out, .. } => *out,
            Frame::Loop { header, .. } => *header,
            Frame::If { out, .. } | Frame::Else { out, .. } => *out,
        }
    }

    fn out(&self) -> Block {
        match self {
            Frame::Block { out, .. }
            | Frame::Loop { out, .. }
            | Frame::If { out, .. }
            | Frame::Else { out, .. } => *out,
        }
    }

    fn params(&self) -> &[Type] {
        match self {
            Frame::Block { params, .. }
            | Frame::Loop { params, .. }
            | Frame::If { params, .. }
            | Frame::Else { params, .. } => &params[..],
        }
    }

    fn results(&self) -> &[Type] {
        match self {
            Frame::Block { results, .. }
            | Frame::Loop { results, .. }
            | Frame::If { results, .. }
            | Frame::Else { results, .. } => &results[..],
        }
    }

    fn set_reachable(&mut self) {
        match self {
            Frame::Block { out_reachable, .. } => *out_reachable = true,
            Frame::If {
                merge_reachable, ..
            }
            | Frame::Else {
                merge_reachable, ..
            } => *merge_reachable = true,
            _ => {}
        }
    }
}

impl<'a, 'b> FunctionBodyBuilder<'a, 'b> {
    fn new(module: &'b Module<'a>, my_sig: Signature, body: &'b mut FunctionBody) -> Self {
        body.blocks.push(BlockDef::default());
        let mut ret = Self {
            module,
            my_sig,
            body,
            ctrl_stack: vec![],
            op_stack: vec![],
            cur_block: Block::new(0),
            reachable: true,
            locals: LocalTracker::default(),
        };

        // Push initial implicit Block.
        let results = module.signatures[my_sig].returns.to_vec();
        let out = ret.body.add_block();
        ret.add_block_params(out, &results[..]);
        ret.ctrl_stack.push(Frame::Block {
            start_depth: 0,
            out,
            params: vec![],
            results,
            out_reachable: false,
        });
        ret
    }

    fn pop_n(&mut self, n: usize) -> Vec<Value> {
        assert!(self.reachable);
        let new_top = self.op_stack.len() - n;
        let ret = self.op_stack[new_top..]
            .iter()
            .map(|(_ty, value)| *value)
            .collect::<Vec<_>>();
        self.op_stack.truncate(new_top);
        ret
    }

    fn pop_1(&mut self) -> Value {
        assert!(self.reachable);
        self.op_stack.pop().unwrap().1
    }

    fn block_results(&mut self, tys: &[Type], start_depth: usize, at_block: Block) -> Vec<Value> {
        if self.op_stack.len() < start_depth + tys.len() {
            tys.iter()
                .map(|&ty| {
                    self.locals
                        .create_default_value(&mut self.body, ty, at_block)
                })
                .collect()
        } else {
            self.pop_n(tys.len())
        }
    }

    fn handle_op(&mut self, op: wasmparser_248::Operator<'a>, loc: SourceLoc) -> Result<()> {
        trace!("handle_op: {:?}", op);
        trace!("op_stack = {:?}", self.op_stack);
        trace!("ctrl_stack = {:?}", self.ctrl_stack);
        trace!("locals = {:?}", self.locals);

        debug_assert!(self.reachable);

        if self.handle_ctrl_op(op.clone())? {
            return Ok(());
        }

        match &op {
            wasmparser_248::Operator::Unreachable => {
                self.emit_unreachable();
            }

            wasmparser_248::Operator::LocalGet { local_index } => {
                let local_index = Local::from(*local_index);
                let ty = self.body.locals[local_index];
                let value = self.locals.get(&mut self.body, local_index);
                self.op_stack.push((ty, value));
            }

            wasmparser_248::Operator::LocalSet { local_index } => {
                let local_index = Local::from(*local_index);
                let (_, value) = self.op_stack.pop().unwrap();
                self.locals.set(local_index, value);
            }

            wasmparser_248::Operator::LocalTee { local_index } => {
                let local_index = Local::from(*local_index);
                let (_ty, value) = *self.op_stack.last().unwrap();
                self.locals.set(local_index, value);
            }

            wasmparser_248::Operator::Call { .. }
            | wasmparser_248::Operator::CallIndirect { .. }
            | wasmparser_248::Operator::Select
            | wasmparser_248::Operator::TypedSelect { .. }
            | wasmparser_248::Operator::GlobalGet { .. }
            | wasmparser_248::Operator::GlobalSet { .. }
            | wasmparser_248::Operator::I32Load { .. }
            | wasmparser_248::Operator::I64Load { .. }
            | wasmparser_248::Operator::F32Load { .. }
            | wasmparser_248::Operator::F64Load { .. }
            | wasmparser_248::Operator::I32Load8S { .. }
            | wasmparser_248::Operator::I32Load8U { .. }
            | wasmparser_248::Operator::I32Load16S { .. }
            | wasmparser_248::Operator::I32Load16U { .. }
            | wasmparser_248::Operator::I64Load8S { .. }
            | wasmparser_248::Operator::I64Load8U { .. }
            | wasmparser_248::Operator::I64Load16S { .. }
            | wasmparser_248::Operator::I64Load16U { .. }
            | wasmparser_248::Operator::I64Load32S { .. }
            | wasmparser_248::Operator::I64Load32U { .. }
            | wasmparser_248::Operator::I32Store { .. }
            | wasmparser_248::Operator::I64Store { .. }
            | wasmparser_248::Operator::F32Store { .. }
            | wasmparser_248::Operator::F64Store { .. }
            | wasmparser_248::Operator::I32Store8 { .. }
            | wasmparser_248::Operator::I32Store16 { .. }
            | wasmparser_248::Operator::I64Store8 { .. }
            | wasmparser_248::Operator::I64Store16 { .. }
            | wasmparser_248::Operator::I64Store32 { .. }
            | wasmparser_248::Operator::MemoryAtomicNotify { .. }
            | wasmparser_248::Operator::MemoryAtomicWait32 { .. }
            | wasmparser_248::Operator::MemoryAtomicWait64 { .. }
            | wasmparser_248::Operator::AtomicFence
            | wasmparser_248::Operator::I32AtomicLoad { .. }
            | wasmparser_248::Operator::I64AtomicLoad { .. }
            | wasmparser_248::Operator::I32AtomicLoad8U { .. }
            | wasmparser_248::Operator::I32AtomicLoad16U { .. }
            | wasmparser_248::Operator::I64AtomicLoad8U { .. }
            | wasmparser_248::Operator::I64AtomicLoad16U { .. }
            | wasmparser_248::Operator::I64AtomicLoad32U { .. }
            | wasmparser_248::Operator::I32AtomicStore { .. }
            | wasmparser_248::Operator::I64AtomicStore { .. }
            | wasmparser_248::Operator::I32AtomicStore8 { .. }
            | wasmparser_248::Operator::I32AtomicStore16 { .. }
            | wasmparser_248::Operator::I64AtomicStore8 { .. }
            | wasmparser_248::Operator::I64AtomicStore16 { .. }
            | wasmparser_248::Operator::I64AtomicStore32 { .. }
            | wasmparser_248::Operator::I32AtomicRmwAdd { .. }
            | wasmparser_248::Operator::I64AtomicRmwAdd { .. }
            | wasmparser_248::Operator::I32AtomicRmw8AddU { .. }
            | wasmparser_248::Operator::I32AtomicRmw16AddU { .. }
            | wasmparser_248::Operator::I64AtomicRmw8AddU { .. }
            | wasmparser_248::Operator::I64AtomicRmw16AddU { .. }
            | wasmparser_248::Operator::I64AtomicRmw32AddU { .. }
            | wasmparser_248::Operator::I32AtomicRmwSub { .. }
            | wasmparser_248::Operator::I64AtomicRmwSub { .. }
            | wasmparser_248::Operator::I32AtomicRmw8SubU { .. }
            | wasmparser_248::Operator::I32AtomicRmw16SubU { .. }
            | wasmparser_248::Operator::I64AtomicRmw8SubU { .. }
            | wasmparser_248::Operator::I64AtomicRmw16SubU { .. }
            | wasmparser_248::Operator::I64AtomicRmw32SubU { .. }
            | wasmparser_248::Operator::I32AtomicRmwAnd { .. }
            | wasmparser_248::Operator::I64AtomicRmwAnd { .. }
            | wasmparser_248::Operator::I32AtomicRmw8AndU { .. }
            | wasmparser_248::Operator::I32AtomicRmw16AndU { .. }
            | wasmparser_248::Operator::I64AtomicRmw8AndU { .. }
            | wasmparser_248::Operator::I64AtomicRmw16AndU { .. }
            | wasmparser_248::Operator::I64AtomicRmw32AndU { .. }
            | wasmparser_248::Operator::I32AtomicRmwOr { .. }
            | wasmparser_248::Operator::I64AtomicRmwOr { .. }
            | wasmparser_248::Operator::I32AtomicRmw8OrU { .. }
            | wasmparser_248::Operator::I32AtomicRmw16OrU { .. }
            | wasmparser_248::Operator::I64AtomicRmw8OrU { .. }
            | wasmparser_248::Operator::I64AtomicRmw16OrU { .. }
            | wasmparser_248::Operator::I64AtomicRmw32OrU { .. }
            | wasmparser_248::Operator::I32AtomicRmwXor { .. }
            | wasmparser_248::Operator::I64AtomicRmwXor { .. }
            | wasmparser_248::Operator::I32AtomicRmw8XorU { .. }
            | wasmparser_248::Operator::I32AtomicRmw16XorU { .. }
            | wasmparser_248::Operator::I64AtomicRmw8XorU { .. }
            | wasmparser_248::Operator::I64AtomicRmw16XorU { .. }
            | wasmparser_248::Operator::I64AtomicRmw32XorU { .. }
            | wasmparser_248::Operator::I32AtomicRmwXchg { .. }
            | wasmparser_248::Operator::I64AtomicRmwXchg { .. }
            | wasmparser_248::Operator::I32AtomicRmw8XchgU { .. }
            | wasmparser_248::Operator::I32AtomicRmw16XchgU { .. }
            | wasmparser_248::Operator::I64AtomicRmw8XchgU { .. }
            | wasmparser_248::Operator::I64AtomicRmw16XchgU { .. }
            | wasmparser_248::Operator::I64AtomicRmw32XchgU { .. }
            | wasmparser_248::Operator::I32AtomicRmwCmpxchg { .. }
            | wasmparser_248::Operator::I64AtomicRmwCmpxchg { .. }
            | wasmparser_248::Operator::I32AtomicRmw8CmpxchgU { .. }
            | wasmparser_248::Operator::I32AtomicRmw16CmpxchgU { .. }
            | wasmparser_248::Operator::I64AtomicRmw8CmpxchgU { .. }
            | wasmparser_248::Operator::I64AtomicRmw16CmpxchgU { .. }
            | wasmparser_248::Operator::I64AtomicRmw32CmpxchgU { .. }
            | wasmparser_248::Operator::MemorySize { .. }
            | wasmparser_248::Operator::MemoryGrow { .. }
            | wasmparser_248::Operator::I32Const { .. }
            | wasmparser_248::Operator::I64Const { .. }
            | wasmparser_248::Operator::F32Const { .. }
            | wasmparser_248::Operator::F64Const { .. }
            | wasmparser_248::Operator::I32Eqz
            | wasmparser_248::Operator::I32Eq
            | wasmparser_248::Operator::I32Ne
            | wasmparser_248::Operator::I32LtS
            | wasmparser_248::Operator::I32LtU
            | wasmparser_248::Operator::I32GtS
            | wasmparser_248::Operator::I32GtU
            | wasmparser_248::Operator::I32LeS
            | wasmparser_248::Operator::I32LeU
            | wasmparser_248::Operator::I32GeS
            | wasmparser_248::Operator::I32GeU
            | wasmparser_248::Operator::I64Eqz
            | wasmparser_248::Operator::I64Eq
            | wasmparser_248::Operator::I64Ne
            | wasmparser_248::Operator::I64LtS
            | wasmparser_248::Operator::I64LtU
            | wasmparser_248::Operator::I64GtU
            | wasmparser_248::Operator::I64GtS
            | wasmparser_248::Operator::I64LeS
            | wasmparser_248::Operator::I64LeU
            | wasmparser_248::Operator::I64GeS
            | wasmparser_248::Operator::I64GeU
            | wasmparser_248::Operator::F32Eq
            | wasmparser_248::Operator::F32Ne
            | wasmparser_248::Operator::F32Lt
            | wasmparser_248::Operator::F32Gt
            | wasmparser_248::Operator::F32Le
            | wasmparser_248::Operator::F32Ge
            | wasmparser_248::Operator::F64Eq
            | wasmparser_248::Operator::F64Ne
            | wasmparser_248::Operator::F64Lt
            | wasmparser_248::Operator::F64Gt
            | wasmparser_248::Operator::F64Le
            | wasmparser_248::Operator::F64Ge
            | wasmparser_248::Operator::I32Clz
            | wasmparser_248::Operator::I32Ctz
            | wasmparser_248::Operator::I32Popcnt
            | wasmparser_248::Operator::I32Add
            | wasmparser_248::Operator::I32Sub
            | wasmparser_248::Operator::I32Mul
            | wasmparser_248::Operator::I32DivS
            | wasmparser_248::Operator::I32DivU
            | wasmparser_248::Operator::I32RemS
            | wasmparser_248::Operator::I32RemU
            | wasmparser_248::Operator::I32And
            | wasmparser_248::Operator::I32Or
            | wasmparser_248::Operator::I32Xor
            | wasmparser_248::Operator::I32Shl
            | wasmparser_248::Operator::I32ShrS
            | wasmparser_248::Operator::I32ShrU
            | wasmparser_248::Operator::I32Rotl
            | wasmparser_248::Operator::I32Rotr
            | wasmparser_248::Operator::I64Clz
            | wasmparser_248::Operator::I64Ctz
            | wasmparser_248::Operator::I64Popcnt
            | wasmparser_248::Operator::I64Add
            | wasmparser_248::Operator::I64Sub
            | wasmparser_248::Operator::I64Mul
            | wasmparser_248::Operator::I64DivS
            | wasmparser_248::Operator::I64DivU
            | wasmparser_248::Operator::I64RemS
            | wasmparser_248::Operator::I64RemU
            | wasmparser_248::Operator::I64And
            | wasmparser_248::Operator::I64Or
            | wasmparser_248::Operator::I64Xor
            | wasmparser_248::Operator::I64Shl
            | wasmparser_248::Operator::I64ShrS
            | wasmparser_248::Operator::I64ShrU
            | wasmparser_248::Operator::I64Rotl
            | wasmparser_248::Operator::I64Rotr
            | wasmparser_248::Operator::F32Abs
            | wasmparser_248::Operator::F32Neg
            | wasmparser_248::Operator::F32Ceil
            | wasmparser_248::Operator::F32Floor
            | wasmparser_248::Operator::F32Trunc
            | wasmparser_248::Operator::F32Nearest
            | wasmparser_248::Operator::F32Sqrt
            | wasmparser_248::Operator::F32Add
            | wasmparser_248::Operator::F32Sub
            | wasmparser_248::Operator::F32Mul
            | wasmparser_248::Operator::F32Div
            | wasmparser_248::Operator::F32Min
            | wasmparser_248::Operator::F32Max
            | wasmparser_248::Operator::F32Copysign
            | wasmparser_248::Operator::F64Abs
            | wasmparser_248::Operator::F64Neg
            | wasmparser_248::Operator::F64Ceil
            | wasmparser_248::Operator::F64Floor
            | wasmparser_248::Operator::F64Trunc
            | wasmparser_248::Operator::F64Nearest
            | wasmparser_248::Operator::F64Sqrt
            | wasmparser_248::Operator::F64Add
            | wasmparser_248::Operator::F64Sub
            | wasmparser_248::Operator::F64Mul
            | wasmparser_248::Operator::F64Div
            | wasmparser_248::Operator::F64Min
            | wasmparser_248::Operator::F64Max
            | wasmparser_248::Operator::F64Copysign
            | wasmparser_248::Operator::I32WrapI64
            | wasmparser_248::Operator::I32TruncF32S
            | wasmparser_248::Operator::I32TruncF32U
            | wasmparser_248::Operator::I32TruncF64S
            | wasmparser_248::Operator::I32TruncF64U
            | wasmparser_248::Operator::I64ExtendI32S
            | wasmparser_248::Operator::I64ExtendI32U
            | wasmparser_248::Operator::I64TruncF32S
            | wasmparser_248::Operator::I64TruncF32U
            | wasmparser_248::Operator::I64TruncF64S
            | wasmparser_248::Operator::I64TruncF64U
            | wasmparser_248::Operator::F32ConvertI32S
            | wasmparser_248::Operator::F32ConvertI32U
            | wasmparser_248::Operator::F32ConvertI64S
            | wasmparser_248::Operator::F32ConvertI64U
            | wasmparser_248::Operator::F32DemoteF64
            | wasmparser_248::Operator::F64ConvertI32S
            | wasmparser_248::Operator::F64ConvertI32U
            | wasmparser_248::Operator::F64ConvertI64S
            | wasmparser_248::Operator::F64ConvertI64U
            | wasmparser_248::Operator::F64PromoteF32
            | wasmparser_248::Operator::I32Extend8S
            | wasmparser_248::Operator::I32Extend16S
            | wasmparser_248::Operator::I64Extend8S
            | wasmparser_248::Operator::I64Extend16S
            | wasmparser_248::Operator::I64Extend32S
            | wasmparser_248::Operator::I32TruncSatF32S
            | wasmparser_248::Operator::I32TruncSatF32U
            | wasmparser_248::Operator::I32TruncSatF64S
            | wasmparser_248::Operator::I32TruncSatF64U
            | wasmparser_248::Operator::I64TruncSatF32S
            | wasmparser_248::Operator::I64TruncSatF32U
            | wasmparser_248::Operator::I64TruncSatF64S
            | wasmparser_248::Operator::I64TruncSatF64U
            | wasmparser_248::Operator::F32ReinterpretI32
            | wasmparser_248::Operator::F64ReinterpretI64
            | wasmparser_248::Operator::I32ReinterpretF32
            | wasmparser_248::Operator::I64ReinterpretF64
            | wasmparser_248::Operator::TableGet { .. }
            | wasmparser_248::Operator::TableSet { .. }
            | wasmparser_248::Operator::TableGrow { .. }
            | wasmparser_248::Operator::TableSize { .. }
            | wasmparser_248::Operator::V128Load { .. }
            | wasmparser_248::Operator::V128Load8x8S { .. }
            | wasmparser_248::Operator::V128Load8x8U { .. }
            | wasmparser_248::Operator::V128Load16x4S { .. }
            | wasmparser_248::Operator::V128Load16x4U { .. }
            | wasmparser_248::Operator::V128Load32x2S { .. }
            | wasmparser_248::Operator::V128Load32x2U { .. }
            | wasmparser_248::Operator::V128Load8Splat { .. }
            | wasmparser_248::Operator::V128Load16Splat { .. }
            | wasmparser_248::Operator::V128Load32Splat { .. }
            | wasmparser_248::Operator::V128Load64Splat { .. }
            | wasmparser_248::Operator::V128Load32Zero { .. }
            | wasmparser_248::Operator::V128Load64Zero { .. }
            | wasmparser_248::Operator::V128Store { .. }
            | wasmparser_248::Operator::V128Load8Lane { .. }
            | wasmparser_248::Operator::V128Load16Lane { .. }
            | wasmparser_248::Operator::V128Load32Lane { .. }
            | wasmparser_248::Operator::V128Load64Lane { .. }
            | wasmparser_248::Operator::V128Store8Lane { .. }
            | wasmparser_248::Operator::V128Store16Lane { .. }
            | wasmparser_248::Operator::V128Store32Lane { .. }
            | wasmparser_248::Operator::V128Store64Lane { .. }
            | wasmparser_248::Operator::V128Const { .. }
            | wasmparser_248::Operator::I8x16Shuffle { .. }
            | wasmparser_248::Operator::I8x16ExtractLaneS { .. }
            | wasmparser_248::Operator::I8x16ExtractLaneU { .. }
            | wasmparser_248::Operator::I8x16ReplaceLane { .. }
            | wasmparser_248::Operator::I16x8ExtractLaneS { .. }
            | wasmparser_248::Operator::I16x8ExtractLaneU { .. }
            | wasmparser_248::Operator::I16x8ReplaceLane { .. }
            | wasmparser_248::Operator::I32x4ExtractLane { .. }
            | wasmparser_248::Operator::I32x4ReplaceLane { .. }
            | wasmparser_248::Operator::I64x2ExtractLane { .. }
            | wasmparser_248::Operator::I64x2ReplaceLane { .. }
            | wasmparser_248::Operator::F32x4ExtractLane { .. }
            | wasmparser_248::Operator::F32x4ReplaceLane { .. }
            | wasmparser_248::Operator::F64x2ExtractLane { .. }
            | wasmparser_248::Operator::F64x2ReplaceLane { .. }
            | wasmparser_248::Operator::I8x16Swizzle
            | wasmparser_248::Operator::I8x16Splat
            | wasmparser_248::Operator::I16x8Splat
            | wasmparser_248::Operator::I32x4Splat
            | wasmparser_248::Operator::I64x2Splat
            | wasmparser_248::Operator::F32x4Splat
            | wasmparser_248::Operator::F64x2Splat
            | wasmparser_248::Operator::I8x16Eq
            | wasmparser_248::Operator::I8x16Ne
            | wasmparser_248::Operator::I8x16LtS
            | wasmparser_248::Operator::I8x16LtU
            | wasmparser_248::Operator::I8x16GtS
            | wasmparser_248::Operator::I8x16GtU
            | wasmparser_248::Operator::I8x16LeS
            | wasmparser_248::Operator::I8x16LeU
            | wasmparser_248::Operator::I8x16GeS
            | wasmparser_248::Operator::I8x16GeU
            | wasmparser_248::Operator::I16x8Eq
            | wasmparser_248::Operator::I16x8Ne
            | wasmparser_248::Operator::I16x8LtS
            | wasmparser_248::Operator::I16x8LtU
            | wasmparser_248::Operator::I16x8GtS
            | wasmparser_248::Operator::I16x8GtU
            | wasmparser_248::Operator::I16x8LeS
            | wasmparser_248::Operator::I16x8LeU
            | wasmparser_248::Operator::I16x8GeS
            | wasmparser_248::Operator::I16x8GeU
            | wasmparser_248::Operator::I32x4Eq
            | wasmparser_248::Operator::I32x4Ne
            | wasmparser_248::Operator::I32x4LtS
            | wasmparser_248::Operator::I32x4LtU
            | wasmparser_248::Operator::I32x4GtS
            | wasmparser_248::Operator::I32x4GtU
            | wasmparser_248::Operator::I32x4LeS
            | wasmparser_248::Operator::I32x4LeU
            | wasmparser_248::Operator::I32x4GeS
            | wasmparser_248::Operator::I32x4GeU
            | wasmparser_248::Operator::I64x2Eq
            | wasmparser_248::Operator::I64x2Ne
            | wasmparser_248::Operator::I64x2LtS
            | wasmparser_248::Operator::I64x2GtS
            | wasmparser_248::Operator::I64x2LeS
            | wasmparser_248::Operator::I64x2GeS
            | wasmparser_248::Operator::F32x4Eq
            | wasmparser_248::Operator::F32x4Ne
            | wasmparser_248::Operator::F32x4Lt
            | wasmparser_248::Operator::F32x4Gt
            | wasmparser_248::Operator::F32x4Le
            | wasmparser_248::Operator::F32x4Ge
            | wasmparser_248::Operator::F64x2Eq
            | wasmparser_248::Operator::F64x2Ne
            | wasmparser_248::Operator::F64x2Lt
            | wasmparser_248::Operator::F64x2Gt
            | wasmparser_248::Operator::F64x2Le
            | wasmparser_248::Operator::F64x2Ge
            | wasmparser_248::Operator::V128Not
            | wasmparser_248::Operator::V128And
            | wasmparser_248::Operator::V128AndNot
            | wasmparser_248::Operator::V128Or
            | wasmparser_248::Operator::V128Xor
            | wasmparser_248::Operator::V128Bitselect
            | wasmparser_248::Operator::V128AnyTrue
            | wasmparser_248::Operator::I8x16Abs
            | wasmparser_248::Operator::I8x16Neg
            | wasmparser_248::Operator::I8x16Popcnt
            | wasmparser_248::Operator::I8x16AllTrue
            | wasmparser_248::Operator::I8x16Bitmask
            | wasmparser_248::Operator::I8x16NarrowI16x8S
            | wasmparser_248::Operator::I8x16NarrowI16x8U
            | wasmparser_248::Operator::I8x16Shl
            | wasmparser_248::Operator::I8x16ShrS
            | wasmparser_248::Operator::I8x16ShrU
            | wasmparser_248::Operator::I8x16Add
            | wasmparser_248::Operator::I8x16AddSatS
            | wasmparser_248::Operator::I8x16AddSatU
            | wasmparser_248::Operator::I8x16Sub
            | wasmparser_248::Operator::I8x16SubSatS
            | wasmparser_248::Operator::I8x16SubSatU
            | wasmparser_248::Operator::I8x16MinS
            | wasmparser_248::Operator::I8x16MinU
            | wasmparser_248::Operator::I8x16MaxS
            | wasmparser_248::Operator::I8x16MaxU
            | wasmparser_248::Operator::I8x16AvgrU
            | wasmparser_248::Operator::I16x8ExtAddPairwiseI8x16S
            | wasmparser_248::Operator::I16x8ExtAddPairwiseI8x16U
            | wasmparser_248::Operator::I16x8Abs
            | wasmparser_248::Operator::I16x8Neg
            | wasmparser_248::Operator::I16x8Q15MulrSatS
            | wasmparser_248::Operator::I16x8AllTrue
            | wasmparser_248::Operator::I16x8Bitmask
            | wasmparser_248::Operator::I16x8NarrowI32x4S
            | wasmparser_248::Operator::I16x8NarrowI32x4U
            | wasmparser_248::Operator::I16x8ExtendLowI8x16S
            | wasmparser_248::Operator::I16x8ExtendHighI8x16S
            | wasmparser_248::Operator::I16x8ExtendLowI8x16U
            | wasmparser_248::Operator::I16x8ExtendHighI8x16U
            | wasmparser_248::Operator::I16x8Shl
            | wasmparser_248::Operator::I16x8ShrS
            | wasmparser_248::Operator::I16x8ShrU
            | wasmparser_248::Operator::I16x8Add
            | wasmparser_248::Operator::I16x8AddSatS
            | wasmparser_248::Operator::I16x8AddSatU
            | wasmparser_248::Operator::I16x8Sub
            | wasmparser_248::Operator::I16x8SubSatS
            | wasmparser_248::Operator::I16x8SubSatU
            | wasmparser_248::Operator::I16x8Mul
            | wasmparser_248::Operator::I16x8MinS
            | wasmparser_248::Operator::I16x8MinU
            | wasmparser_248::Operator::I16x8MaxS
            | wasmparser_248::Operator::I16x8MaxU
            | wasmparser_248::Operator::I16x8AvgrU
            | wasmparser_248::Operator::I16x8ExtMulLowI8x16S
            | wasmparser_248::Operator::I16x8ExtMulHighI8x16S
            | wasmparser_248::Operator::I16x8ExtMulLowI8x16U
            | wasmparser_248::Operator::I16x8ExtMulHighI8x16U
            | wasmparser_248::Operator::I32x4ExtAddPairwiseI16x8S
            | wasmparser_248::Operator::I32x4ExtAddPairwiseI16x8U
            | wasmparser_248::Operator::I32x4Abs
            | wasmparser_248::Operator::I32x4Neg
            | wasmparser_248::Operator::I32x4AllTrue
            | wasmparser_248::Operator::I32x4Bitmask
            | wasmparser_248::Operator::I32x4ExtendLowI16x8S
            | wasmparser_248::Operator::I32x4ExtendHighI16x8S
            | wasmparser_248::Operator::I32x4ExtendLowI16x8U
            | wasmparser_248::Operator::I32x4ExtendHighI16x8U
            | wasmparser_248::Operator::I32x4Shl
            | wasmparser_248::Operator::I32x4ShrS
            | wasmparser_248::Operator::I32x4ShrU
            | wasmparser_248::Operator::I32x4Add
            | wasmparser_248::Operator::I32x4Sub
            | wasmparser_248::Operator::I32x4Mul
            | wasmparser_248::Operator::I32x4MinS
            | wasmparser_248::Operator::I32x4MinU
            | wasmparser_248::Operator::I32x4MaxS
            | wasmparser_248::Operator::I32x4MaxU
            | wasmparser_248::Operator::I32x4DotI16x8S
            | wasmparser_248::Operator::I32x4ExtMulLowI16x8S
            | wasmparser_248::Operator::I32x4ExtMulHighI16x8S
            | wasmparser_248::Operator::I32x4ExtMulLowI16x8U
            | wasmparser_248::Operator::I32x4ExtMulHighI16x8U
            | wasmparser_248::Operator::I64x2Abs
            | wasmparser_248::Operator::I64x2Neg
            | wasmparser_248::Operator::I64x2AllTrue
            | wasmparser_248::Operator::I64x2Bitmask
            | wasmparser_248::Operator::I64x2ExtendLowI32x4S
            | wasmparser_248::Operator::I64x2ExtendHighI32x4S
            | wasmparser_248::Operator::I64x2ExtendLowI32x4U
            | wasmparser_248::Operator::I64x2ExtendHighI32x4U
            | wasmparser_248::Operator::I64x2Shl
            | wasmparser_248::Operator::I64x2ShrS
            | wasmparser_248::Operator::I64x2ShrU
            | wasmparser_248::Operator::I64x2Add
            | wasmparser_248::Operator::I64x2Sub
            | wasmparser_248::Operator::I64x2Mul
            | wasmparser_248::Operator::I64x2ExtMulLowI32x4S
            | wasmparser_248::Operator::I64x2ExtMulHighI32x4S
            | wasmparser_248::Operator::I64x2ExtMulLowI32x4U
            | wasmparser_248::Operator::I64x2ExtMulHighI32x4U
            | wasmparser_248::Operator::F32x4Ceil
            | wasmparser_248::Operator::F32x4Floor
            | wasmparser_248::Operator::F32x4Trunc
            | wasmparser_248::Operator::F32x4Nearest
            | wasmparser_248::Operator::F32x4Abs
            | wasmparser_248::Operator::F32x4Neg
            | wasmparser_248::Operator::F32x4Sqrt
            | wasmparser_248::Operator::F32x4Add
            | wasmparser_248::Operator::F32x4Sub
            | wasmparser_248::Operator::F32x4Mul
            | wasmparser_248::Operator::F32x4Div
            | wasmparser_248::Operator::F32x4Min
            | wasmparser_248::Operator::F32x4Max
            | wasmparser_248::Operator::F32x4PMin
            | wasmparser_248::Operator::F32x4PMax
            | wasmparser_248::Operator::F64x2Ceil
            | wasmparser_248::Operator::F64x2Floor
            | wasmparser_248::Operator::F64x2Trunc
            | wasmparser_248::Operator::F64x2Nearest
            | wasmparser_248::Operator::F64x2Abs
            | wasmparser_248::Operator::F64x2Neg
            | wasmparser_248::Operator::F64x2Sqrt
            | wasmparser_248::Operator::F64x2Add
            | wasmparser_248::Operator::F64x2Sub
            | wasmparser_248::Operator::F64x2Mul
            | wasmparser_248::Operator::F64x2Div
            | wasmparser_248::Operator::F64x2Min
            | wasmparser_248::Operator::F64x2Max
            | wasmparser_248::Operator::F64x2PMin
            | wasmparser_248::Operator::F64x2PMax
            | wasmparser_248::Operator::I32x4TruncSatF32x4S
            | wasmparser_248::Operator::I32x4TruncSatF32x4U
            | wasmparser_248::Operator::F32x4ConvertI32x4S
            | wasmparser_248::Operator::F32x4ConvertI32x4U
            | wasmparser_248::Operator::I32x4TruncSatF64x2SZero
            | wasmparser_248::Operator::I32x4TruncSatF64x2UZero
            | wasmparser_248::Operator::F64x2ConvertLowI32x4S
            | wasmparser_248::Operator::F64x2ConvertLowI32x4U
            | wasmparser_248::Operator::F32x4DemoteF64x2Zero
            | wasmparser_248::Operator::F64x2PromoteLowF32x4
            | wasmparser_248::Operator::CallRef { .. }
            | wasmparser_248::Operator::RefIsNull
            | wasmparser_248::Operator::RefNull { .. }
            | wasmparser_248::Operator::RefFunc { .. }
            | wasmparser_248::Operator::MemoryFill { .. }
            | wasmparser_248::Operator::MemoryCopy { .. } => {
                self.emit(Operator::try_from(&op).unwrap(), loc)?
            }

            wasmparser_248::Operator::Nop => {}

            wasmparser_248::Operator::Drop => {
                let _ = self.pop_1();
            }

            wasmparser_248::Operator::Br { relative_depth }
            | wasmparser_248::Operator::BrIf { relative_depth } => {
                let cond = match &op {
                    wasmparser_248::Operator::Br { .. } => None,
                    wasmparser_248::Operator::BrIf { .. } => Some(self.pop_1()),
                    _ => unreachable!(),
                };
                // Get the frame we're branching to.
                let frame = self.relative_frame(*relative_depth);
                frame.set_reachable();
                let frame = frame.clone();
                log::trace!("Br/BrIf: dest frame {:?}", frame);
                // Finally, generate the branch itself.
                match cond {
                    None => {
                        // Get the args off the stack unconditionally.
                        let args = self.pop_n(frame.br_args().len());
                        self.emit_branch(frame.br_target(), &args[..]);
                        self.locals.finish_block(self.reachable);
                        self.reachable = false;
                    }
                    Some(cond) => {
                        let cont = self.body.add_block();
                        // Get the args off the stack but leave for the fallthrough.
                        let args = self.op_stack[self.op_stack.len() - frame.br_args().len()..]
                            .iter()
                            .map(|(_ty, value)| *value)
                            .collect::<Vec<_>>();
                        self.emit_cond_branch(cond, frame.br_target(), &args[..], cont, &[]);
                        self.locals.seal_block_preds(cont, &mut self.body);
                        self.cur_block = cont;
                        self.locals.finish_block(self.reachable);
                        self.locals.start_block(cont);
                    }
                }
            }

            wasmparser_248::Operator::BrTable { targets } => {
                // Get the selector index.
                let index = self.pop_1();
                // Get the signature of the default frame; this tells
                // us the signature of all frames (since wasmparser
                // validates the input for us). Pop that many args.
                let default_frame = self.relative_frame(targets.default());
                default_frame.set_reachable();
                let default_term_target = default_frame.br_target();
                let arg_len = default_frame.br_args().len();
                let args = self.pop_n(arg_len);
                // Generate a branch terminator with the same args for
                // every branch target.
                let mut term_targets = vec![];
                for target in targets.targets() {
                    let target = target?;
                    let frame = self.relative_frame(target);
                    frame.set_reachable();
                    assert_eq!(frame.br_args().len(), args.len());
                    let block = frame.br_target();
                    term_targets.push(block);
                }
                self.emit_br_table(index, default_term_target, &term_targets[..], &args[..]);
                self.locals.finish_block(self.reachable);
                self.reachable = false;
            }

            wasmparser_248::Operator::Return => {
                let retvals = self.pop_n(self.module.signatures[self.my_sig].returns.len());
                self.emit_ret(&retvals[..]);
                self.reachable = false;
            }

            wasmparser_248::Operator::ReturnCall { function_index } => {
                let func = Func::new(*function_index as usize);
                let n = self.module.signatures[self.module.funcs[func].sig()]
                    .params
                    .len();
                let args = self.pop_n(n);
                self.emit_term(Terminator::ReturnCall { func, args });
            }

            wasmparser_248::Operator::ReturnCallIndirect {
                type_index,
                table_index,
            } => {
                let sig = Signature::new(*type_index as usize);
                // the table index operand is on top of the stack, after the arguments
                let args = self.pop_n(self.module.signatures[sig].params.len() + 1);
                self.emit_term(Terminator::ReturnCallIndirect {
                    sig,
                    table: Table::new(*table_index as usize),
                    args,
                });
            }

            _ => bail!(FrontendError::UnsupportedFeature(format!(
                "Unsupported operator: {:?}",
                op
            ))),
        }

        Ok(())
    }

    fn handle_op_unreachable(&mut self, op: wasmparser_248::Operator<'a>) -> Result<()> {
        trace!("handle_op_unreachable: {:?}", op);
        trace!("op_stack = {:?}", self.op_stack);
        trace!("ctrl_stack = {:?}", self.ctrl_stack);

        debug_assert!(!self.reachable);

        self.handle_ctrl_op(op)?;

        Ok(())
    }

    fn handle_ctrl_op(&mut self, op: wasmparser_248::Operator<'a>) -> Result<bool> {
        log::trace!(
            "handle_ctrl_op: op {:?} reachable {} cur_block {}",
            op,
            self.reachable,
            self.cur_block
        );
        log::trace!("ctrl stack: {:?}", self.ctrl_stack);
        match &op {
            wasmparser_248::Operator::End => {
                let frame = self.ctrl_stack.pop();
                match &frame {
                    None => {
                        if self.reachable {
                            let retvals =
                                self.pop_n(self.module.signatures[self.my_sig].returns.len());
                            self.emit_ret(&retvals[..]);
                        } else {
                            self.emit_unreachable();
                        }
                    }
                    Some(Frame::Block {
                        start_depth,
                        out,
                        results,
                        ..
                    })
                    | Some(Frame::Loop {
                        start_depth,
                        out,
                        results,
                        ..
                    }) => {
                        // Generate a branch to the out-block with
                        // blockparams for the results.
                        let was_reachable = self.reachable;
                        if self.reachable {
                            let result_values =
                                self.block_results(&results[..], *start_depth, self.cur_block);
                            self.emit_branch(*out, &result_values[..]);
                        }
                        self.op_stack.truncate(*start_depth);
                        // Seal the out-block: no more edges will be
                        // added to it. Also, if we're ending a loop,
                        // seal thea header: no more back-edges will
                        // be added to it.
                        self.locals.seal_block_preds(*out, &mut self.body);
                        if let Some(Frame::Loop { header, .. }) = &frame {
                            self.locals.seal_block_preds(*header, &mut self.body);
                        }
                        // Set `cur_block` only if currently set (otherwise, unreachable!)
                        self.cur_block = *out;
                        self.locals.finish_block(self.reachable);
                        self.locals.start_block(*out);
                        self.reachable = was_reachable
                            || match &frame {
                                Some(Frame::Block { out_reachable, .. }) => *out_reachable,
                                _ => false,
                            };
                        self.push_block_params(results.len());
                    }
                    Some(Frame::If {
                        start_depth,
                        out,
                        el,
                        param_values,
                        results,
                        head_reachable,
                        merge_reachable,
                        ..
                    }) => {
                        // Generate a branch to the out-block with
                        // blockparams for the results.
                        let was_reachable = self.reachable;
                        if self.reachable {
                            let result_values =
                                self.block_results(&results[..], *start_depth, self.cur_block);
                            self.emit_branch(*out, &result_values[..]);
                        }
                        assert!(self.op_stack.len() >= *start_depth);
                        self.op_stack.truncate(*start_depth);
                        if *head_reachable {
                            // No `else`, so we need to generate a trivial
                            // branch in the else-block. If the if-block-type
                            // has results, they must be exactly the params.
                            let else_result_values = param_values;
                            assert_eq!(else_result_values.len(), results.len());
                            let else_result_values = else_result_values
                                .iter()
                                .map(|(_ty, value)| *value)
                                .collect::<Vec<_>>();
                            self.locals.finish_block(self.reachable);
                            self.locals.start_block(*el);
                            self.cur_block = *el;
                            self.reachable = *head_reachable;
                            self.emit_branch(*out, &else_result_values[..]);
                            assert_eq!(self.op_stack.len(), *start_depth);
                        }
                        self.cur_block = *out;
                        let else_reachable = self.reachable;
                        self.reachable = *head_reachable || was_reachable || *merge_reachable;
                        self.locals.seal_block_preds(*out, &mut self.body);
                        self.locals.finish_block(else_reachable);
                        self.locals.start_block(*out);
                        self.push_block_params(results.len());
                    }
                    Some(Frame::Else {
                        out,
                        results,
                        start_depth,
                        merge_reachable,
                        ..
                    }) => {
                        // Generate a branch to the out-block with
                        // blockparams for the results.
                        let was_reachable = self.reachable;
                        if self.reachable {
                            let result_values =
                                self.block_results(&results[..], *start_depth, self.cur_block);
                            self.emit_branch(*out, &result_values[..]);
                        }
                        self.op_stack.truncate(*start_depth);
                        self.cur_block = *out;
                        self.reachable = *merge_reachable || self.reachable;
                        self.locals.seal_block_preds(*out, &mut self.body);
                        self.locals.finish_block(was_reachable);
                        self.locals.start_block(*out);
                        self.push_block_params(results.len());
                    }
                }
            }

            wasmparser_248::Operator::Block { blockty } => {
                let (params, results) = self.block_params_and_results(*blockty);
                let out = self.body.add_block();
                self.add_block_params(out, &results[..]);
                let start_depth = if self.reachable {
                    self.op_stack.len() - params.len()
                } else {
                    self.op_stack.len()
                };
                self.ctrl_stack.push(Frame::Block {
                    start_depth,
                    out,
                    params,
                    results,
                    out_reachable: false,
                });
            }

            wasmparser_248::Operator::Loop { blockty } => {
                let (params, results) = self.block_params_and_results(*blockty);
                let header = self.body.add_block();
                self.add_block_params(header, &params[..]);
                let initial_args = if self.reachable {
                    self.pop_n(params.len())
                } else {
                    vec![Value::invalid(); params.len()]
                };
                let start_depth = self.op_stack.len();
                self.emit_branch(header, &initial_args[..]);
                self.cur_block = header;
                self.locals.finish_block(self.reachable);
                self.locals.start_block(header);
                self.push_block_params(params.len());
                let out = self.body.add_block();
                self.add_block_params(out, &results[..]);
                self.ctrl_stack.push(Frame::Loop {
                    start_depth,
                    header,
                    out,
                    params,
                    results,
                });
            }

            wasmparser_248::Operator::If { blockty } => {
                let (params, results) = self.block_params_and_results(*blockty);
                let if_true = self.body.add_block();
                let if_false = self.body.add_block();
                let join = self.body.add_block();
                self.add_block_params(join, &results[..]);
                let (cond, param_values) = if self.reachable {
                    let cond = self.pop_1();
                    let param_values = self.op_stack[self.op_stack.len() - params.len()..].to_vec();
                    (cond, param_values)
                } else {
                    (
                        Value::invalid(),
                        params.iter().map(|&ty| (ty, Value::invalid())).collect(),
                    )
                };
                let start_depth = if self.reachable {
                    self.op_stack.len() - params.len()
                } else {
                    self.op_stack.len()
                };
                self.ctrl_stack.push(Frame::If {
                    start_depth,
                    out: join,
                    el: if_false,
                    param_values,
                    params,
                    results,
                    head_reachable: self.reachable,
                    merge_reachable: false,
                });
                self.emit_cond_branch(cond, if_true, &[], if_false, &[]);
                self.locals.seal_block_preds(if_true, &mut self.body);
                self.locals.seal_block_preds(if_false, &mut self.body);
                self.cur_block = if_true;
                self.locals.finish_block(self.reachable);
                self.locals.start_block(if_true);
            }

            wasmparser_248::Operator::Else => {
                if let Frame::If {
                    start_depth,
                    out,
                    el,
                    param_values,
                    params,
                    results,
                    head_reachable,
                    merge_reachable,
                } = self.ctrl_stack.pop().unwrap()
                {
                    if self.reachable {
                        let if_results =
                            self.block_results(&results[..], start_depth, self.cur_block);
                        self.emit_branch(out, &if_results[..]);
                    }
                    self.op_stack.truncate(start_depth);
                    self.op_stack.extend(param_values);
                    self.ctrl_stack.push(Frame::Else {
                        start_depth,
                        out,
                        params,
                        results,
                        merge_reachable: merge_reachable || self.reachable,
                    });
                    self.cur_block = el;
                    self.locals.finish_block(self.reachable);
                    self.locals.start_block(el);
                    self.reachable = head_reachable;
                } else {
                    bail!(FrontendError::Internal(format!(
                        "Else without If on top of frame stack"
                    )));
                }
            }

            _ => return Ok(false),
        }

        Ok(true)
    }

    fn add_block_params(&mut self, block: Block, tys: &[Type]) {
        log::trace!("add_block_params: block {} tys {:?}", block, tys);
        for &ty in tys {
            self.body.add_blockparam(block, ty);
        }
    }

    fn block_params_and_results(&self, ty: BlockType) -> (Vec<Type>, Vec<Type>) {
        match ty {
            BlockType::Empty => (vec![], vec![]),
            BlockType::Type(ret_ty) => (vec![], vec![ret_ty.into()]),
            BlockType::FuncType(sig_idx) => {
                let sig = &self.module.signatures[Signature::from(sig_idx)];
                (
                    Vec::from(sig.params.clone()),
                    Vec::from(sig.returns.clone()),
                )
            }
        }
    }

    fn relative_frame(&mut self, relative_depth: u32) -> &mut Frame {
        let index = self.ctrl_stack.len() - 1 - relative_depth as usize;
        &mut self.ctrl_stack[index]
    }

    fn emit_branch(&mut self, target: Block, args: &[Value]) {
        log::trace!(
            "emit_branch: cur_block {:?} target {} args {:?}",
            self.cur_block,
            target,
            args
        );
        if self.reachable {
            let args = args.to_vec();
            let target = BlockTarget {
                block: target,
                args,
            };
            self.body
                .set_terminator(self.cur_block, Terminator::Br { target });
        }
    }

    fn emit_cond_branch(
        &mut self,
        cond: Value,
        if_true: Block,
        if_true_args: &[Value],
        if_false: Block,
        if_false_args: &[Value],
    ) {
        log::trace!(
            "emit_cond_branch: cur_block {:?} if_true {} args {:?} if_false {} args {:?}",
            self.cur_block,
            if_true,
            if_true_args,
            if_false,
            if_false_args
        );
        if self.reachable {
            let if_true_args = if_true_args.to_vec();
            let if_false_args = if_false_args.to_vec();
            self.body.set_terminator(
                self.cur_block,
                Terminator::CondBr {
                    cond,
                    if_true: BlockTarget {
                        block: if_true,
                        args: if_true_args,
                    },
                    if_false: BlockTarget {
                        block: if_false,
                        args: if_false_args,
                    },
                },
            );
        }
    }

    fn emit_br_table(
        &mut self,
        index: Value,
        default_target: Block,
        indexed_targets: &[Block],
        args: &[Value],
    ) {
        log::trace!(
            "emit_br_table: cur_block {:?} index {:?} default {} indexed {:?} args {:?}",
            self.cur_block,
            index,
            default_target,
            indexed_targets,
            args,
        );
        if self.reachable {
            let args = args.to_vec();
            let targets = indexed_targets
                .iter()
                .map(|&block| {
                    let args = args.clone();
                    BlockTarget { block, args }
                })
                .collect();

            let default_args = args;
            let default = BlockTarget {
                block: default_target,
                args: default_args,
            };

            self.body.set_terminator(
                self.cur_block,
                Terminator::Select {
                    value: index,
                    targets,
                    default,
                },
            );
        }
    }

    fn emit_ret(&mut self, values: &[Value]) {
        log::trace!(
            "emit_ret: cur_block {} reachable {} values {:?}",
            self.cur_block,
            self.reachable,
            values
        );
        if self.reachable {
            let values = values.to_vec();
            self.body
                .set_terminator(self.cur_block, Terminator::Return { values });
            self.reachable = false;
        }
    }

    fn emit_term(&mut self, terminator: Terminator) {
        if self.reachable {
            self.body.set_terminator(self.cur_block, terminator);
            self.reachable = false;
        }
    }

    fn emit_unreachable(&mut self) {
        log::trace!(
            "emit_unreachable: cur_block {} reachable {}",
            self.cur_block,
            self.reachable
        );
        if self.reachable {
            self.body
                .set_terminator(self.cur_block, Terminator::Unreachable);
            self.reachable = false;
        }
    }

    fn push_block_params(&mut self, num_params: usize) {
        log::trace!(
            "push_block_params: cur_block {:?}, {} params",
            self.cur_block,
            num_params
        );
        for i in 0..num_params {
            let (ty, value) = self.body.blocks[self.cur_block].params[i];
            log::trace!(" -> push {:?} ty {:?}", value, ty);
            self.op_stack.push((ty, value));
        }
    }

    fn emit(&mut self, op: Operator, loc: SourceLoc) -> Result<()> {
        let inputs = op_inputs(self.module, &self.op_stack[..], &op)?;
        let outputs = op_outputs(self.module, &self.op_stack[..], &op)?;

        log::trace!(
            "emit into block {:?}: op {:?} inputs {:?}",
            self.cur_block,
            op,
            inputs
        );

        let n_outputs = outputs.len();

        let input_operands = self.body.arg_pool.allocate(inputs.len(), Value::invalid());
        let args = &mut self.body.arg_pool[input_operands];
        for (i, &input) in inputs.into_iter().enumerate().rev() {
            let (stack_top_ty, stack_top) = self.op_stack.pop().unwrap();
            assert_eq!(stack_top_ty, input);
            args[i] = stack_top;
        }
        log::trace!(" -> operands: {:?}", input_operands);
        log::trace!(" -> ty {:?}", outputs);

        let outputs_list = if n_outputs == 1 {
            self.body.single_type_list(outputs[0])
        } else {
            self.body.type_pool.from_iter(outputs.iter().cloned())
        };

        let value = self
            .body
            .add_value(ValueDef::Operator(op, input_operands, outputs_list));
        log::trace!(" -> value: {:?}", value);

        if self.reachable {
            self.body.append_to_block(self.cur_block, value);
        }
        self.body.source_locs[value] = loc;

        if n_outputs == 1 {
            let output_ty = outputs[0];
            self.op_stack.push((output_ty, value));
        } else {
            for (i, &output_ty) in outputs.into_iter().enumerate() {
                let pick = self
                    .body
                    .add_value(ValueDef::PickOutput(value, i as u32, output_ty));
                if self.reachable {
                    self.body.append_to_block(self.cur_block, pick);
                }
                self.op_stack.push((output_ty, pick));
                log::trace!(" -> pick {}: {:?} ty {:?}", i, pick, output_ty);
            }
        }

        Ok(())
    }
}
