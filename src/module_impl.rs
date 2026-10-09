//! S4: the `cranelift_module::Module` implementation — the exact seam cg_clif drives.
//!
//! `WasmModule` sits where `ObjectModule` sits: cg_clif calls `declare_function` /
//! `declare_data` / `define_function` / `define_data` through `&mut dyn Module`, and an
//! inherent `finish()` (finalization is NOT part of the trait — the reason the plan
//! needs a thin cg_clif driver fork) turns the collected CLIF + data into a wasm module
//! via the existing translator.
//!
//! `isa()` returns a **Pulley32** TargetIsa — the only 32-bit-pointer ISA in cranelift
//! 0.133 — so `pointer_type() == I32` and cg_clif's `pointer_ty(tcx) == isa.pointer_type`
//! assertion holds for a wasm32 rustc target with no cg_clif core changes. Nothing ever
//! calls `ctx.compile()`; the ISA is a pointer-width oracle only.

use std::collections::BTreeMap;

use cranelift_codegen::control::ControlPlane;
use cranelift_codegen::ir;
use cranelift_codegen::isa::{self, OwnedTargetIsa, TargetIsa};
use cranelift_codegen::settings::{self, Configurable};
use cranelift_module::{
    DataDescription, DataId, FuncId, Init, Linkage, Module, ModuleDeclarations, ModuleError,
    ModuleReloc, ModuleResult,
};
use target_lexicon::Triple;

use crate::error::{Context, Error, Result};
use crate::object::{ObjBinding, ObjData, ObjDataDef, ObjDef, ObjFunc};
use crate::{bail, unsupported};

pub struct WasmModule {
    isa: OwnedTargetIsa,
    data_addresses: Vec<u32>,
    initialized_data: usize,
    declarations: ModuleDeclarations,
    funcs: BTreeMap<FuncId, ir::Function>,
    data: BTreeMap<DataId, DataDescription>,
    translation_options: crate::TranslationOptions,
    runtime_overrides: BTreeMap<FuncId, crate::RuntimeFn>,
    /// Undefined symbols allowed to become REAL `env` wasm imports (host-provided at
    /// instantiation — the playground's print path). From CLIF2WASM_IMPORTS
    /// (comma-separated) or `allow_import`.
    import_symbols: BTreeMap<String, String>,
}

impl Clone for WasmModule {
    fn clone(&self) -> Self {
        let mut declarations = ModuleDeclarations::default();
        for (id, decl) in self.declarations.get_functions() {
            let copied = match &decl.name {
                Some(name) => {
                    declarations
                        .declare_function(name, decl.linkage, &decl.signature)
                        .expect("valid function declaration")
                        .0
                }
                None => declarations
                    .declare_anonymous_function(&decl.signature)
                    .expect("valid anonymous function"),
            };
            assert_eq!(copied, id);
        }
        for (id, decl) in self.declarations.get_data_objects() {
            let copied = match &decl.name {
                Some(name) => {
                    declarations
                        .declare_data(name, decl.linkage, decl.writable, decl.tls)
                        .expect("valid data declaration")
                        .0
                }
                None => declarations
                    .declare_anonymous_data(decl.writable, decl.tls)
                    .expect("valid anonymous data"),
            };
            assert_eq!(copied, id);
        }
        Self {
            isa: self.isa.clone(),
            declarations,
            data_addresses: self.data_addresses.clone(),
            initialized_data: self.initialized_data,
            funcs: self.funcs.clone(),
            data: self.data.clone(),
            translation_options: self.translation_options,
            runtime_overrides: self.runtime_overrides.clone(),
            import_symbols: self.import_symbols.clone(),
        }
    }
}

impl WasmModule {
    pub fn new() -> Result<Self> {
        let mut fb = settings::builder();
        fb.set("opt_level", "none")
            .map_err(|e| Error::general(e.to_string()))?;
        let flags = settings::Flags::new(fb);
        let triple: Triple = "pulley32-unknown-unknown"
            .parse::<Triple>()
            .map_err(|e| Error::general(e.to_string()))?;
        let isa = isa::lookup(triple)
            .context("looking up Pulley32 ISA")?
            .finish(flags)
            .context("finishing Pulley32 ISA")?;
        let import_symbols = std::env::var("CLIF2WASM_IMPORTS")
            .map(|v| {
                v.split(',')
                    .map(|s| s.trim().to_string())
                    .filter(|s| !s.is_empty())
                    .map(|name| (name.clone(), name))
                    .collect()
            })
            .unwrap_or_default();
        Ok(WasmModule {
            isa,
            data_addresses: vec![],
            initialized_data: 0,
            declarations: ModuleDeclarations::default(),
            funcs: BTreeMap::new(),
            data: BTreeMap::new(),
            translation_options: crate::TranslationOptions::default(),
            runtime_overrides: BTreeMap::new(),
            import_symbols,
        })
    }

    /// Allow an undefined symbol to become a real `env` wasm import.
    pub fn allow_import(&mut self, name: &str) {
        self.allow_import_as(name, name);
    }

    pub fn allow_import_as(&mut self, symbol: &str, import_name: &str) {
        self.import_symbols
            .insert(symbol.to_string(), import_name.to_string());
    }

    pub fn set_translation_options(&mut self, options: crate::TranslationOptions) {
        self.translation_options = options;
    }

    pub fn override_runtime(&mut self, function: FuncId, runtime: crate::RuntimeFn) {
        self.runtime_overrides.insert(function, runtime);
    }

    /// Finalize: translate every collected function and data object into one wasm
    /// module, exporting every `Linkage::Export` function under its declared name.
    ///
    /// Mirrors `ObjectModule::finish()` in shape (inherent, consumes self) — this is
    /// the method the cg_clif driver fork will call where it now calls
    /// `ObjectProduct` emission.
    pub fn finish(self) -> Result<Vec<u8>> {
        self.emit(None)
    }

    pub fn data_address(&self, id: DataId) -> Option<u32> {
        self.data_addresses.get(id.as_u32() as usize).copied()
    }

    pub fn function_names(&self) -> Vec<String> {
        self.declarations
            .get_functions()
            .map(|(id, decl)| {
                decl.name
                    .clone()
                    .unwrap_or_else(|| format!("fn{}", id.as_u32()))
            })
            .collect()
    }

    pub fn emit_incremental(
        &mut self,
        mut allocate: impl FnMut(usize, u32) -> Result<u32>,
    ) -> Result<Vec<u8>> {
        for (id, _) in self
            .declarations
            .get_data_objects()
            .skip(self.data_addresses.len())
        {
            let data = self
                .data
                .get(&id)
                .ok_or_else(|| Error::general(format!("undefined data {id}")))?;
            let size = match &data.init {
                Init::Bytes { contents } => contents.len(),
                Init::Zeros { size } => *size,
                Init::Uninitialized => bail!("uninitialized data {id}"),
            };
            self.data_addresses
                .push(allocate(size, data.align.unwrap_or(8) as u32)?);
        }
        let bytes = self.emit(Some(crate::link::SessionLayout {
            data_addresses: &self.data_addresses,
            initialized_data: self.initialized_data,
        }))?;
        self.initialized_data = self.data_addresses.len();
        for id in self.funcs.keys() {
            let name = self
                .declarations
                .get_function_decl(*id)
                .name
                .clone()
                .unwrap_or_else(|| format!("fn{}", id.as_u32()));
            self.import_symbols.insert(name.clone(), name);
        }
        self.funcs.clear();
        Ok(bytes)
    }

    fn emit(&self, layout: Option<crate::link::SessionLayout<'_>>) -> Result<Vec<u8>> {
        // Data objects, in DataId order (= namespace-1 index order).
        let mut data_objs: Vec<ObjData> = Vec::new();
        let mut data_names: Vec<String> = Vec::new();
        for (id, decl) in self.declarations.get_data_objects() {
            data_names.push(
                decl.name
                    .clone()
                    .unwrap_or_else(|| format!("data{}", id.as_u32())),
            );
        }
        for (i, (id, decl)) in self.declarations.get_data_objects().enumerate() {
            let desc = self.data.get(&id);
            let (bytes, relocs) = match desc {
                Some(d) => {
                    let bytes = match &d.init {
                        Init::Bytes { contents } => contents.to_vec(),
                        Init::Zeros { size } => vec![0; *size],
                        Init::Uninitialized => {
                            bail!("data `{}` is uninitialized", data_names[i])
                        }
                    };
                    // Pointer slots inside the object: resolve each reloc's target to
                    // the module-level ordinal; the translator patches actual values
                    // after layout.
                    let lenient = std::env::var_os("CLIF2WASM_LENIENT").is_some_and(|v| v == "1");
                    let mut relocs = Vec::new();
                    for &(offset, fref) in &d.function_relocs {
                        match reloc_target_ordinal(&d.function_decls[fref], 0) {
                            Ok(target) => relocs.push(crate::DataRelocEntry {
                                offset,
                                target: crate::DataRelocTarget::Func(target),
                                addend: 0,
                            }),
                            Err(e) if lenient => eprintln!(
                                "clif2wasm-gap: data reloc skipped in `{}`: {e:#}",
                                data_names[i]
                            ),
                            Err(e) => {
                                return Err(Error::general(format!(
                                    "data `{}`: {e}",
                                    data_names[i]
                                )));
                            }
                        }
                    }
                    for &(offset, gv, addend) in &d.data_relocs {
                        match reloc_target_ordinal(&d.data_decls[gv], 1) {
                            Ok(target) => relocs.push(crate::DataRelocEntry {
                                offset,
                                target: crate::DataRelocTarget::Data(target),
                                addend,
                            }),
                            Err(e) if lenient => eprintln!(
                                "clif2wasm-gap: data reloc skipped in `{}`: {e:#}",
                                data_names[i]
                            ),
                            Err(e) => {
                                return Err(Error::general(format!(
                                    "data `{}`: {e}",
                                    data_names[i]
                                )));
                            }
                        }
                    }
                    (bytes, relocs)
                }
                None if std::env::var_os("CLIF2WASM_LENIENT").is_some_and(|v| v == "1") => {
                    // Sysroot tier: cross-crate data import (e.g. core statics seen
                    // from compiler_builtins). Zero placeholder; reads through it are
                    // wrong-but-unreachable rlib-object code, and it's gap-reported.
                    eprintln!(
                        "clif2wasm-gap: data import zero-stubbed: {} ({:?})",
                        data_names[i], decl.linkage
                    );
                    (vec![0u8; 64], Vec::new())
                }
                None => bail!(
                    "data `{}` declared ({:?}) but never defined — imports of data are a fork-scope gap",
                    data_names[i],
                    decl.linkage
                ),
            };
            let align = desc.and_then(|d| d.align).unwrap_or(8) as u32;
            data_objs.push(ObjData {
                name: &data_names[i],
                binding: ObjBinding::Global,
                hidden: false,
                def: Some(ObjDataDef {
                    bytes,
                    align,
                    relocs,
                }),
            });
        }

        // Functions, in FuncId order (= namespace-0 index order = slice ordinal).
        // Declared-but-undefined functions become `unreachable` stubs (the S3 panic
        // policy applied at the seam; real imports are Milestone-B linker scope).
        let mut fn_names: Vec<String> = Vec::new();
        for (id, decl) in self.declarations.get_functions() {
            fn_names.push(
                decl.name
                    .clone()
                    .unwrap_or_else(|| format!("fn{}", id.as_u32())),
            );
        }
        // Undefined-function policy:
        //   1. well-known runtime symbols (memcpy/memcmp/...) -> synthesized real bodies;
        //   2. panic-family symbols -> `unreachable` trap stubs (correct semantics for
        //      -Cpanic=abort without unwinding);
        //   3. anything else -> hard error naming every symbol — unless
        //      CLIF2WASM_LENIENT=1 (sysroot builds), which stubs them and prints a
        //      `clif2wasm-gap:` line per symbol for the gap ratchet.
        let lenient = std::env::var_os("CLIF2WASM_LENIENT").is_some_and(|v| v == "1");
        let mut stub_storage: Vec<ir::Function> = Vec::new();
        let mut which: Vec<Option<usize>> = Vec::new(); // index into stub_storage for stubs
        let mut runtime_overrides: std::collections::HashMap<usize, crate::RuntimeFn> =
            Default::default();
        let mut import_map: std::collections::HashMap<usize, String> = Default::default();
        let mut missing: Vec<String> = Vec::new();
        for (i, (id, decl)) in self.declarations.get_functions().enumerate() {
            if self.funcs.contains_key(&id) {
                which.push(None);
                continue;
            }
            let name = &fn_names[i];
            let mut f = ir::Function::with_name_signature(
                ir::UserFuncName::user(0, id.as_u32()),
                decl.signature.clone(),
            );
            build_trap_body(&mut f);
            if let Some(import_name) = self.import_symbols.get(name) {
                import_map.insert(i, import_name.clone());
            } else if let Some(kind) = crate::RuntimeFn::from_symbol(name) {
                runtime_overrides.insert(i, kind);
            } else if name.contains("panic") || name.ends_with("_fail") || name.ends_with("_failed")
            {
                // trap stub (diverging error/fail handlers are panic-family)
            } else if lenient {
                eprintln!("clif2wasm-gap: undefined symbol stubbed: {name}");
            } else {
                missing.push(name.clone());
            }
            which.push(Some(stub_storage.len()));
            stub_storage.push(f);
        }
        for (i, (id, _)) in self.declarations.get_functions().enumerate() {
            if let Some(runtime) = self.runtime_overrides.get(&id) {
                runtime_overrides.insert(i, *runtime);
            }
        }
        if !missing.is_empty() {
            unsupported!(
                "undefined non-panic symbols (no linker yet; CLIF2WASM_LENIENT=1 to stub for sysroot builds):\n  {}",
                missing.join("\n  ")
            );
        }
        let mut funcs: Vec<ObjFunc> = Vec::new();
        let mut exports: Vec<(usize, &str)> = Vec::new();
        for (i, (id, decl)) in self.declarations.get_functions().enumerate() {
            let func: &ir::Function = match which[i] {
                None => &self.funcs[&id],
                Some(s) => &stub_storage[s],
            };
            let (name, def) = if let Some(import_name) = import_map.get(&i) {
                (import_name.as_str(), None)
            } else if let Some(&kind) = runtime_overrides.get(&i) {
                (fn_names[i].as_str(), Some(ObjDef::Runtime(kind)))
            } else {
                (fn_names[i].as_str(), Some(ObjDef::Clif(func)))
            };
            funcs.push(ObjFunc {
                name,
                binding: ObjBinding::Global,
                hidden: false,
                def,
                sig: decl.signature.clone(),
            });
            if decl.linkage == Linkage::Export || layout.is_some() {
                exports.push((i, &fn_names[i]));
            }
        }

        let relocatable = crate::relocatable::translate(
            &funcs,
            &data_objs,
            crate::relocatable::TranslateOptions {
                shared_memory: self.translation_options.shared_memory_max_pages.is_some(),
                lenient,
                stack_limit: true,
            },
        )?;
        crate::link::link(
            &relocatable,
            &crate::link::LinkOptions {
                shared_memory_max_pages: self.translation_options.shared_memory_max_pages,
                session: layout,
                exports: &exports,
            },
        )
    }

    /// Finalize as a RELOCATABLE wasm object (Phase B): undefined symbols stay
    /// undefined, data becomes named segments, and the `linking` section carries
    /// the symbol table. No stub/import/lenient policy — resolution is the
    /// linker's job.
    pub fn finish_object(self) -> Result<Vec<u8>> {
        use crate::object::{ObjBinding, ObjData, ObjDataDef, ObjFunc, translate_object};

        fn binding_of(linkage: Linkage) -> ObjBinding {
            match linkage {
                Linkage::Local => ObjBinding::Local,
                // Preemptible is where rustc's linkonce_odr monomorphizations land:
                // duplicate copies across objects must merge, i.e. weak binding.
                Linkage::Preemptible => ObjBinding::Weak,
                _ => ObjBinding::Global,
            }
        }

        // Owned name storage (ObjFunc/ObjData borrow).
        let fn_names: Vec<String> = self
            .declarations
            .get_functions()
            .map(|(id, decl)| {
                decl.name
                    .clone()
                    .unwrap_or_else(|| format!(".L__unnamed_fn_{}", id.as_u32()))
            })
            .collect();
        let data_names: Vec<String> = self
            .declarations
            .get_data_objects()
            .map(|(id, decl)| {
                decl.name
                    .clone()
                    .unwrap_or_else(|| format!(".L__unnamed_{}", id.as_u32()))
            })
            .collect();

        // cg_clif's i128 helper family (__udivti3/__divti3/__umodti3/__modti3/
        // __rust_{u,i}128_mulo) is called with OUR i128-as-2xi64 expansion, which
        // need not match LLVM compiler_builtins' lowering of the same names. Keep
        // the namespaces fully separate: rename our references to
        // __clif2wasm_<name> and DEFINE them (synthesized CLIF) as hidden weak —
        // weak so duplicate copies across our objects merge; LLVM-compiled code
        // keeps resolving the original names to compiler_builtins.
        let mut fn_names = fn_names;
        let mut synth: BTreeMap<usize, crate::RuntimeFn> = BTreeMap::new();
        for (i, (id, _decl)) in self.declarations.get_functions().enumerate() {
            if self.funcs.contains_key(&id) {
                continue;
            }
            let Some(kind) = crate::RuntimeFn::from_symbol(&fn_names[i]) else {
                continue;
            };
            // Memory libcalls by name (memcpy/...) stay undefined: real libc.
            if matches!(
                kind,
                crate::RuntimeFn::Memcpy
                    | crate::RuntimeFn::Memmove
                    | crate::RuntimeFn::Memset
                    | crate::RuntimeFn::Memcmp
            ) {
                continue;
            }
            if !fn_names[i].starts_with("__clif2wasm_") {
                fn_names[i] = format!(
                    "__clif2wasm_{}",
                    fn_names[i]
                        .trim_start_matches("__rust_")
                        .trim_start_matches("__")
                );
            }
            synth.insert(i, kind);
        }

        let mut fns: Vec<ObjFunc> = Vec::with_capacity(fn_names.len());
        for (i, (id, decl)) in self.declarations.get_functions().enumerate() {
            use crate::object::ObjDef;
            let (def, binding, hidden) = match (self.funcs.get(&id), synth.get(&i)) {
                (Some(f), _) => (
                    Some(ObjDef::Clif(f)),
                    if decl.name.is_none() {
                        // Anonymous functions have no linkage identity outside
                        // this object.
                        ObjBinding::Local
                    } else {
                        binding_of(decl.linkage)
                    },
                    false,
                ),
                (None, Some(&kind)) => (Some(ObjDef::Runtime(kind)), ObjBinding::Weak, true),
                (None, None) => (
                    None,
                    if decl.name.is_none() {
                        ObjBinding::Local
                    } else {
                        binding_of(decl.linkage)
                    },
                    false,
                ),
            };
            fns.push(ObjFunc {
                name: &fn_names[i],
                binding,
                hidden,
                def,
                sig: decl.signature.clone(),
            });
        }

        let mut data: Vec<ObjData> = Vec::with_capacity(data_names.len());
        for (i, (id, decl)) in self.declarations.get_data_objects().enumerate() {
            let def = match self.data.get(&id) {
                Some(d) => {
                    let bytes = match &d.init {
                        Init::Bytes { contents } => contents.to_vec(),
                        Init::Zeros { size } => vec![0; *size],
                        Init::Uninitialized => {
                            bail!("data `{}` is uninitialized", data_names[i])
                        }
                    };
                    let mut relocs = Vec::new();
                    for &(offset, fref) in &d.function_relocs {
                        relocs.push(crate::DataRelocEntry {
                            offset,
                            target: crate::DataRelocTarget::Func(reloc_target_ordinal(
                                &d.function_decls[fref],
                                0,
                            )?),
                            addend: 0,
                        });
                    }
                    for &(offset, gv, addend) in &d.data_relocs {
                        relocs.push(crate::DataRelocEntry {
                            offset,
                            target: crate::DataRelocTarget::Data(reloc_target_ordinal(
                                &d.data_decls[gv],
                                1,
                            )?),
                            addend,
                        });
                    }
                    Some(ObjDataDef {
                        bytes,
                        align: d.align.unwrap_or(8) as u32,
                        relocs,
                    })
                }
                // Undefined data: a real undefined symbol now — the old
                // "fork-scope gap" bail is object mode's bread and butter.
                None => None,
            };
            data.push(ObjData {
                name: &data_names[i],
                binding: if decl.name.is_none() {
                    ObjBinding::Local
                } else {
                    binding_of(decl.linkage)
                },
                hidden: false,
                def,
            });
        }

        translate_object(&fns, &data)
    }
}

/// Resolve a data reloc's `ModuleRelocTarget` to the ordinal in the expected
/// namespace (0 = FuncId, 1 = DataId); anything else is a named fork-scope gap.
fn reloc_target_ordinal(
    target: &cranelift_module::ModuleRelocTarget,
    expected_ns: u32,
) -> Result<u32> {
    match target {
        cranelift_module::ModuleRelocTarget::User { namespace, index } => {
            if *namespace != expected_ns {
                unsupported!("reloc target namespace {namespace} (expected {expected_ns})");
            }
            Ok(*index)
        }
        other => unsupported!("unsupported reloc target {other:?} (libcall/known-symbol)"),
    }
}

/// Hand-rolled `unreachable` body (no cranelift-frontend dep in the library): one
/// block carrying the signature's params, terminated by a trap.
fn build_trap_body(f: &mut ir::Function) {
    let block = f.dfg.make_block();
    f.layout.append_block(block);
    for p in f.signature.params.clone() {
        f.dfg.append_block_param(block, p.value_type);
    }
    let inst = f.dfg.make_inst(ir::InstructionData::Trap {
        opcode: ir::Opcode::Trap,
        code: ir::TrapCode::user(1).unwrap(),
    });
    f.layout.append_inst(inst, block);
}

impl Module for WasmModule {
    fn isa(&self) -> &dyn TargetIsa {
        &*self.isa
    }

    fn declarations(&self) -> &ModuleDeclarations {
        &self.declarations
    }

    fn declare_function(
        &mut self,
        name: &str,
        linkage: Linkage,
        signature: &ir::Signature,
    ) -> ModuleResult<FuncId> {
        let (id, _linkage) = self
            .declarations
            .declare_function(name, linkage, signature)?;
        Ok(id)
    }

    fn declare_anonymous_function(&mut self, signature: &ir::Signature) -> ModuleResult<FuncId> {
        self.declarations.declare_anonymous_function(signature)
    }

    fn declare_data(
        &mut self,
        name: &str,
        linkage: Linkage,
        writable: bool,
        tls: bool,
    ) -> ModuleResult<DataId> {
        let (id, _linkage) = self
            .declarations
            .declare_data(name, linkage, writable, tls)?;
        Ok(id)
    }

    fn declare_anonymous_data(&mut self, writable: bool, tls: bool) -> ModuleResult<DataId> {
        self.declarations.declare_anonymous_data(writable, tls)
    }

    fn define_function_with_control_plane(
        &mut self,
        func: FuncId,
        ctx: &mut cranelift_codegen::Context,
        _ctrl_plane: &mut ControlPlane,
    ) -> ModuleResult<()> {
        let decl = self.declarations.get_function_decl(func);
        if !decl.linkage.is_definable() {
            return Err(ModuleError::InvalidImportDefinition(
                decl.name.clone().unwrap_or_default(),
            ));
        }
        if self.funcs.contains_key(&func) {
            return Err(ModuleError::DuplicateDefinition(
                decl.name.clone().unwrap_or_default(),
            ));
        }
        // The interception point (plan §5): grab the un-compiled, target-independent
        // CLIF. ctx.compile() is never called.
        self.funcs.insert(func, ctx.func.clone());
        Ok(())
    }

    fn define_function_bytes(
        &mut self,
        _func_id: FuncId,
        _alignment: u64,
        _bytes: &[u8],
        _relocs: &[ModuleReloc],
    ) -> ModuleResult<()> {
        Err(ModuleError::Backend(
            std::io::Error::other(
                "define_function_bytes: machine-code injection is unsupported by the wasm backend",
            )
            .into(),
        ))
    }

    fn define_data(&mut self, data_id: DataId, data: &DataDescription) -> ModuleResult<()> {
        let decl = self.declarations.get_data_decl(data_id);
        if !decl.linkage.is_definable() {
            return Err(ModuleError::InvalidImportDefinition(
                decl.name.clone().unwrap_or_default(),
            ));
        }
        if self.data.contains_key(&data_id) {
            return Err(ModuleError::DuplicateDefinition(
                decl.name.clone().unwrap_or_default(),
            ));
        }
        self.data.insert(data_id, data.clone());
        Ok(())
    }
}
