use alloc::collections::BTreeMap;
use alloc::string::String;
use core::default;
use core::iter::{empty, once};
use impl_trait_for_tuples::impl_for_tuples;

use super::{
    ControlTag, Func, FuncDecl, Global, HeapType, Memory, ModuleDisplay, Signature, StorageType,
    Table, Type, WithMutablility,
};
use crate::entity::{EntityRef, EntityVec};
use crate::ir::{Debug, DebugMap, FunctionBody};
use crate::{backend, frontend};
use alloc::vec;
use alloc::vec::Vec;
use anyhow::Result;
use either::Either;
use indexmap::IndexMap;

pub use crate::frontend::FrontendOptions;

#[derive(Clone, Debug)]
pub struct Module<'a> {
    /// The original Wasm module this module was parsed from, if
    /// any. Used only for "lazy function bodies", which retain a
    /// range that can refer into this slice.
    pub orig_bytes: Option<&'a [u8]>,
    /// The functions in this module: imports, un-expanded ("lazily
    /// parsed") functions, functions as IR, or IR compiled into new
    /// bytecode.
    pub funcs: EntityVec<Func, FuncDecl<'a>>,
    /// Type signatures, referred to by `funcs`, `imports` and
    /// `exports`.
    pub signatures: EntityVec<Signature, SignatureData>,
    /// Global variables in this module.
    pub globals: EntityVec<Global, GlobalData>,
    /// Tables in this module.
    pub tables: EntityVec<Table, TableData>,
    /// Imports into this module. Function imports must also have an
    /// entry at the appropriate function index in `funcs`.
    pub imports: Vec<Import>,
    /// Exports from this module.
    pub exports: Vec<Export>,
    /// Memories/heapds that this module contains.
    pub memories: EntityVec<Memory, MemoryData>,
    /// Control tags that this module contains
    pub control_tags: EntityVec<ControlTag, ControlTagData>,
    /// The "start function" invoked at instantiation, if any.
    pub start_func: Option<Func>,
    /// Debug-info associated with function bodies: interning pools
    /// for source file names and locations in those files.
    pub debug: Debug,
    /// Maps from original Wasm bytecode offsets to source locations.
    pub debug_map: DebugMap,
    pub custom_sections: BTreeMap<String, Vec<u8>>,
}
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ControlTagData {
    ///The signature used when invoking this tag
    pub sig: Signature,
}
#[non_exhaustive]
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub enum SignatureData {
    Func {
        /// Parameters: a Wasm function may have zero or more primitive
        /// types as parameters.
        params: Vec<Type>,
        /// Returns: a Wasm function (when using the multivalue extension,
        /// which we assume to be present) may have zero or more primitive
        /// types as return values.
        returns: Vec<Type>,
        ///Is this signature shared
        shared: bool,
    },
    Struct {
        ///The fields of the struct
        fields: Vec<WithMutablility<StorageType>>,
        ///Is this signature shared
        shared: bool,
    },
    Array {
        ///The element type
        ty: WithMutablility<StorageType>,
        ///Is this signature shared
        shared: bool,
    },
    Import {
        like: HeapType,
        shared: bool,
    },
    #[default]
    None,
}

impl SignatureData {
    pub fn shared(&self) -> bool {
        match self {
            SignatureData::Func {
                params,
                returns,
                shared,
            } => *shared,
            SignatureData::Struct { fields, shared } => *shared,
            SignatureData::Array { ty, shared } => *shared,
            SignatureData::Import { like, shared } => *shared,
            SignatureData::None => todo!(),
        }
    }
}

/// The size of a single Wasm page, used in memory definitions.
pub const WASM_PAGE: usize = 0x1_0000; // 64KiB

/// A memory definition.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MemoryData {
    /// How many Wasm pages (64KiB size) in the initial memory size?
    pub initial_pages: usize,
    /// How many Wasm pages (64KiB size) in the maximum memory size?
    pub maximum_pages: Option<usize>,
    /// Initialization data (initial image) for this memory.
    pub segments: Vec<MemorySegment>,
    pub memory64: bool,
    pub shared: bool,
    pub page_size_log2: Option<u32>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MemorySegment {
    /// The offset of this data.
    pub offset: usize,
    /// The data, overlaid on previously-existing data at this offset.
    pub data: Vec<u8>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TableData {
    /// The type of element in this table.
    pub ty: Type,
    pub initial: u64,
    /// The maximum size (in elements), if any, of this table.
    pub max: Option<u64>,
    /// If this is a table of function references, the initial
    /// contents of the table. `null` funcrefs are represented by
    /// `Func::invalid()`.
    pub func_elements: Option<Vec<Func>>,
    pub table64: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct GlobalData {
    /// The type of this global variable.
    pub ty: Type,
    /// The initial value of this global variable, as a bundle of 64
    /// bits (all primitive types, `i32`/`i64`/`f32`/`f64`, can be
    /// represented in this way).
    pub value: Option<u64>,
    /// Whether this global variable is mutable.
    pub mutable: bool,
}

impl From<&wasmparser::SubType> for SignatureData {
    fn from(fty: &wasmparser::SubType) -> Self {
        match &fty.composite_type.inner {
            wasmparser::CompositeInnerType::Func(func_type) => Self::Func {
                params: func_type
                    .params()
                    .iter()
                    .map(|&ty| ty.into())
                    .collect::<Vec<Type>>(),
                returns: func_type
                    .results()
                    .iter()
                    .map(|&ty| ty.into())
                    .collect::<Vec<Type>>(),
                shared: fty.composite_type.shared,
            },
            wasmparser::CompositeInnerType::Array(array_type) => Self::Array {
                ty: array_type.0.clone().into(),
                shared: fty.composite_type.shared,
            },
            wasmparser::CompositeInnerType::Struct(struct_type) => Self::Struct {
                fields: struct_type.fields.iter().map(|&ty| ty.into()).collect(),
                shared: fty.composite_type.shared,
            },
            _ => todo!(),
        }
    }
}
impl From<wasmparser::SubType> for SignatureData {
    fn from(fty: wasmparser::SubType) -> Self {
        (&fty).into()
    }
}

impl From<&SignatureData> for wasm_encoder::SubType {
    fn from(value: &SignatureData) -> Self {
        match value {
            SignatureData::Func {
                params,
                returns,
                shared,
            } => wasm_encoder::SubType {
                is_final: true,
                supertype_idx: None,
                composite_type: wasm_encoder::CompositeType {
                    inner: wasm_encoder::CompositeInnerType::Func(wasm_encoder::FuncType::new(
                        params.iter().cloned().map(|a| a.into()),
                        returns.iter().cloned().map(|a| a.into()),
                    )),
                    shared: *shared,
                },
            },
            SignatureData::None => todo!(),
            SignatureData::Struct { fields, shared } => wasm_encoder::SubType {
                is_final: true,
                supertype_idx: None,
                composite_type: wasm_encoder::CompositeType {
                    inner: wasm_encoder::CompositeInnerType::Struct(wasm_encoder::StructType {
                        fields: fields.iter().cloned().map(|a| a.into()).collect(),
                    }),
                    shared: *shared,
                },
            },
            SignatureData::Array { ty, shared } => wasm_encoder::SubType {
                is_final: true,
                supertype_idx: None,
                composite_type: wasm_encoder::CompositeType {
                    inner: wasm_encoder::CompositeInnerType::Array(wasm_encoder::ArrayType(
                        ty.clone().into(),
                    )),
                    shared: *shared,
                },
            },
            SignatureData::Import { like, shared } => todo!(),
        }
    }
}

impl Signature {
    pub fn is_backref(&self, module: &Module) -> bool {
        return match &module.signatures[*self] {
            SignatureData::Func {
                params, returns, ..
            } => params
                .iter()
                .chain(returns.iter())
                .flat_map(|a| a.sigs())
                .any(|sig| sig.index() >= self.index()),
            _ => false,
        };
    }
}

impl Type {
    pub fn sigs<'a>(&'a self) -> impl Iterator<Item = Signature> + 'a {
        match self {
            Type::Heap(h) => match &h.value {
                HeapType::Sig { sig_index } => Either::Right(once(*sig_index)),
                _ => Either::Left(empty()),
            },
            _ => Either::Left(empty()),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Import {
    /// The name of the module the import comes from.
    pub module: String,
    /// The name of the export within that module that this import
    /// comes from.
    pub name: String,
    /// The kind of import and its specific entity index.
    pub kind: ImportKind,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub enum ImportKind {
    /// An import of a table.
    Table(Table),
    /// An import of a function.
    Func(Func),
    /// An import of a global.
    Global(Global),
    /// An import of a memory.
    Memory(Memory),
    /// An import of a control tag
    ControlTag(ControlTag),
    /// An import of a type
    Type(Signature),
}

impl core::fmt::Display for ImportKind {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        match self {
            ImportKind::Table(table) => write!(f, "{}", table)?,
            ImportKind::Func(func) => write!(f, "{}", func)?,
            ImportKind::Global(global) => write!(f, "{}", global)?,
            ImportKind::Memory(mem) => write!(f, "{}", mem)?,
            ImportKind::ControlTag(control_tag) => write!(f, "{}", control_tag)?,
            ImportKind::Type(t) => write!(f, "{}", t)?,
        }
        Ok(())
    }
}

#[derive(Clone, Debug)]
pub struct Export {
    /// The name of this export.
    pub name: String,
    /// The kind of export and its specific entity index.
    pub kind: ExportKind,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub enum ExportKind {
    /// An export of a table.
    Table(Table),
    /// An export of a function.
    Func(Func),
    /// An export of a global.
    Global(Global),
    /// An export of a memory.
    Memory(Memory),
    /// An export of a control tag
    ControlTag(ControlTag),
    ///An export of a type
    Type(Signature),
}

pub fn x2i(x: ExportKind) -> ImportKind {
    match x {
        ExportKind::Table(a) => ImportKind::Table(a),
        ExportKind::Func(a) => ImportKind::Func(a),
        ExportKind::Global(a) => ImportKind::Global(a),
        ExportKind::Memory(a) => ImportKind::Memory(a),
        ExportKind::ControlTag(control_tag) => ImportKind::ControlTag(control_tag),
        ExportKind::Type(t) => ImportKind::Type(t),
    }
}
pub fn i2x(x: ImportKind) -> ExportKind {
    match x {
        ImportKind::Table(a) => ExportKind::Table(a),
        ImportKind::Func(a) => ExportKind::Func(a),
        ImportKind::Global(a) => ExportKind::Global(a),
        ImportKind::Memory(a) => ExportKind::Memory(a),
        ImportKind::ControlTag(control_tag) => ExportKind::ControlTag(control_tag),
        ImportKind::Type(t) => ExportKind::Type(t),
    }
}

impl core::fmt::Display for ExportKind {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        match self {
            ExportKind::Table(table) => write!(f, "{}", table)?,
            ExportKind::Func(func) => write!(f, "{}", func)?,
            ExportKind::Global(global) => write!(f, "{}", global)?,
            ExportKind::Memory(memory) => write!(f, "{}", memory)?,
            ExportKind::ControlTag(control_tag) => write!(f, "{}", control_tag)?,
            ExportKind::Type(t) => write!(f, "{}", t)?,
        }
        Ok(())
    }
}

impl<'a> Module<'a> {
    // pub(crate) fn with_orig_bytes(orig_bytes: &'a [u8]) -> Module<'a> {
    //     Module {
    //         orig_bytes,
    //         funcs: EntityVec::default(),
    //         signatures: EntityVec::default(),
    //         globals: EntityVec::default(),
    //         tables: EntityVec::default(),
    //         imports: vec![],
    //         exports: vec![],
    //         memories: EntityVec::default(),
    //         start_func: None,
    //         debug: Debug::default(),
    //         debug_map: DebugMap::default(),
    //         custom_sections: BTreeMap::default(),
    //     }
    // }

    pub fn empty() -> Module<'static> {
        Module {
            orig_bytes: None,
            funcs: EntityVec::default(),
            signatures: EntityVec::default(),
            globals: EntityVec::default(),
            tables: EntityVec::default(),
            imports: vec![],
            exports: vec![],
            memories: EntityVec::default(),
            start_func: None,
            debug: Debug::default(),
            debug_map: DebugMap::default(),
            custom_sections: Default::default(),
            control_tags: Default::default(),
        }
    }

    /// Parse a WebAssembly module, as a slice of bytes in memory,
    /// into a waffle Module ready to be manipulated and recompile.
    pub fn from_wasm_bytes(bytes: &'a [u8], options: &FrontendOptions) -> Result<Self> {
        frontend::wasm_to_ir(bytes, options)
    }

    /// Take this module and strip its reference to the original
    /// bytes, producing a module with the same logical contents.
    ///
    /// Note that this has a few side-effects:
    /// - Any (non-debug) custom sections are lost; i.e., they will
    ///   not be roundtripped from the original Wasm module.
    /// - All function bodies are expanded to IR so they can be
    ///   recompiled into new bytecode. The bytecode should be
    ///   equivalent, but will not literally be the same bytecode as the
    ///   original module.
    pub fn without_orig_bytes(self) -> Module<'static> {
        Module {
            orig_bytes: None,
            funcs: EntityVec::from(
                self.funcs
                    .into_vec()
                    .into_iter()
                    .map(|decl| decl.without_orig_bytes())
                    .collect::<Vec<_>>(),
            ),
            signatures: self.signatures,
            globals: self.globals,
            tables: self.tables,
            imports: self.imports,
            exports: self.exports,
            memories: self.memories,
            start_func: self.start_func,
            debug: self.debug,
            debug_map: self.debug_map,
            custom_sections: self.custom_sections,
            control_tags: self.control_tags,
        }
    }
}

impl<'a> Module<'a> {
    // pub(crate) fn frontend_add_table(&mut self, ty: Type, initial: u64, max: Option<u64>) -> Table {
    //     let func_elements = Some(vec![]);
    //     self.tables.push(TableData {
    //         ty,
    //         func_elements,
    //         initial,
    //         max,
    //     })
    // }

    // pub fn from_wasm_bytes(bytes: &'a [u8], options: &FrontendOptions) -> Result<Self> {
    //     frontend::wasm_to_ir(bytes, options)
    // }

    pub fn to_wasm_bytes(&self) -> Result<Vec<u8>> {
        backend::compile(self).map(|a| a.finish())
    }
    pub fn to_encoded_module(&self) -> Result<wasm_encoder::Module> {
        backend::compile(self)
    }

    pub fn per_func_body<F: Fn(&mut FunctionBody)>(&mut self, f: F) {
        for func_decl in self.funcs.values_mut() {
            if let Some(body) = func_decl.body_mut() {
                f(body);
            }
        }
    }

    pub fn take_per_func_body<F: FnMut(&mut Self, &mut FunctionBody)>(&mut self, mut f: F) {
        for func_decl in self.funcs.iter().collect::<Vec<_>>() {
            let mut x = core::mem::take(&mut self.funcs[func_decl]);
            if let Some(body) = x.body_mut() {
                f(self, body);
            }
            self.funcs[func_decl] = x;
        }
    }

    pub fn try_per_func_body<F: FnMut(&mut FunctionBody) -> Result<(), E>, E>(
        &mut self,
        mut f: F,
    ) -> Result<(), E> {
        for func_decl in self.funcs.values_mut() {
            if let Some(body) = func_decl.body_mut() {
                f(body)?;
            }
        }
        Ok(())
    }

    pub fn try_take_per_func_body<F: FnMut(&mut Self, &mut FunctionBody) -> Result<(), E>, E>(
        &mut self,
        mut f: F,
    ) -> Result<(), E> {
        for func_decl in self.funcs.iter().collect::<Vec<_>>() {
            let mut x = core::mem::take(&mut self.funcs[func_decl]);
            let mut y = None;
            if let Some(body) = x.body_mut() {
                y = Some(f(self, body));
            }
            self.funcs[func_decl] = x;
            if let Some(z) = y {
                z?;
            }
        }
        Ok(())
    }

    /// Expand a function body, parsing its lazy reference to original
    /// bytecode into IR if needed.
    pub fn expand_func<'b>(&'b mut self, id: Func) -> Result<&'b mut FuncDecl<'a>> {
        if let FuncDecl::Lazy(..) = self.funcs[id] {
            // End the borrow. This is cheap (a slice copy).
            let mut func = self.funcs[id].clone();
            func.parse(self)?;
            self.funcs[id] = func;
        }
        Ok(&mut self.funcs[id])
    }

    /// Clone a function body *without* expanding it, and return a
    /// *new* function body with IR expanded. Useful when a tool
    /// appends new functions that are processed versions of an
    /// original function (which itself must remain as well).
    pub fn clone_and_expand_body(&self, id: Func) -> Result<FunctionBody> {
        let mut body = self.funcs[id].clone();
        body.parse(self)?;
        Ok(match body {
            FuncDecl::Body(_, _, body) => body,
            _ => unreachable!(),
        })
    }

    /// For all functions that are lazy references to initial
    /// bytecode, expand them into IR.
    pub fn expand_all_funcs(&mut self) -> Result<()> {
        for id in 0..self.funcs.len() {
            let id = Func::new(id);
            self.expand_func(id)?;
        }
        Ok(())
    }

    /// Return a wrapper that implements Display on this module,
    /// pretty-printing it as textual IR.
    pub fn display<'b>(&'b self) -> ModuleDisplay<'b>
    where
        'b: 'a,
    {
        ModuleDisplay { module: self }
    }

    /// Internal (used during parsing): create an empty module, with
    /// the given slice of original Wasm bytecode. Used during parsing
    /// and meant to be filled in as the Wasm bytecode is processed.
    pub(crate) fn with_orig_bytes(orig_bytes: &'a [u8]) -> Module<'a> {
        Module {
            orig_bytes: Some(orig_bytes),
            funcs: EntityVec::default(),
            signatures: EntityVec::default(),
            globals: EntityVec::default(),
            tables: EntityVec::default(),
            imports: vec![],
            exports: vec![],
            memories: EntityVec::default(),
            start_func: None,
            debug: Debug::default(),
            debug_map: DebugMap::default(),
            custom_sections: BTreeMap::default(),
            control_tags: EntityVec::default(),
        }
    }
}
#[impl_for_tuples(12)]
pub trait FuncCollector {
    fn collect_func(&mut self, f: Func);
}
impl<'a, T: FuncCollector> FuncCollector for &'a mut T {
    fn collect_func(&mut self, f: Func) {
        FuncCollector::collect_func(&mut **self, f);
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn empty_module_valid() {
        let module = Module::empty();
        let _ = module.to_wasm_bytes().unwrap();
    }
}
