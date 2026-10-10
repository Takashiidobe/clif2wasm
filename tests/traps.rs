//! `TranslationOptions::report_traps`: the host sees the CLIF trap code before the trap.

use std::sync::{Arc, Mutex};

use clif2wasm::{TRAP_IMPORT, TranslationOptions, WasmModule};
use cranelift_codegen::Context;
use cranelift_module::{Linkage, Module as _};
use cranelift_reader::parse_functions;
use wasmi::{Engine, Linker, Module, Store, Val};

const SOURCE: &str = "
function %trap() { block0: trap user5 }
function %heap() { block0: trap heap_oob }
function %trapz(i32) { block0(v0: i32): trapz v0, user6 \n return }
function %trapnz(i32) { block0(v0: i32): trapnz v0, int_ovf \n return }
function %add_trap(i32, i32) -> i32 {
block0(v0: i32, v1: i32):
    v2 = uadd_overflow_trap v0, v1, user7
    return v2
}
function %divide(i128, i128) -> i128 {
    sig0 = (i128, i128) -> i128
    fn0 = colocated u0:0 sig0
block0(v0: i128, v1: i128):
    v2 = call fn0(v0, v1)
    return v2
}
function %leaf(i32) -> i32 { block0(v0: i32): return v0 }
";

fn module(report: bool) -> Vec<u8> {
    let mut module = WasmModule::new().unwrap();
    module.set_translation_options(TranslationOptions {
        report_traps: report,
        ..TranslationOptions::default()
    });
    let functions = parse_functions(SOURCE).unwrap();
    let mut divide =
        cranelift_codegen::ir::Signature::new(cranelift_codegen::isa::CallConv::SystemV);
    divide.params.push(cranelift_codegen::ir::AbiParam::new(
        cranelift_codegen::ir::types::I128,
    ));
    divide.params.push(cranelift_codegen::ir::AbiParam::new(
        cranelift_codegen::ir::types::I128,
    ));
    divide.returns.push(cranelift_codegen::ir::AbiParam::new(
        cranelift_codegen::ir::types::I128,
    ));
    module
        .declare_function("__udivti3", Linkage::Import, &divide)
        .unwrap();
    let mut ids = Vec::new();
    for function in &functions {
        let name = function.name.to_string();
        ids.push(
            module
                .declare_function(
                    name.trim_start_matches('%'),
                    Linkage::Export,
                    &function.signature,
                )
                .unwrap(),
        );
    }
    for (function, id) in functions.into_iter().zip(ids) {
        module
            .define_function(id, &mut Context::for_function(function))
            .unwrap();
    }
    module.finish().unwrap()
}

fn run(bytes: &[u8], name: &str, args: &[Val]) -> (bool, Vec<i32>) {
    let engine = Engine::default();
    let module = Module::new(&engine, bytes).unwrap();
    let seen = Arc::new(Mutex::new(Vec::new()));
    let mut store = Store::new(&engine, ());
    let mut linker = Linker::new(&engine);
    let sink = seen.clone();
    linker
        .func_wrap("env", TRAP_IMPORT, move |code: i32| {
            sink.lock().unwrap().push(code);
        })
        .unwrap();
    let instance = linker.instantiate_and_start(&mut store, &module).unwrap();
    let func = instance.get_func(&store, name).unwrap();
    let mut results = vec![Val::I32(0); func.ty(&store).results().len()];
    let trapped = func.call(&mut store, args, &mut results).is_err();
    let codes = seen.lock().unwrap().clone();
    (trapped, codes)
}

#[test]
fn trap_codes_reach_the_host() {
    let bytes = module(true);
    assert_eq!(run(&bytes, "trap", &[]), (true, vec![5]));
    assert_eq!(run(&bytes, "heap", &[]), (true, vec![253]));
    assert_eq!(run(&bytes, "trapz", &[Val::I32(0)]), (true, vec![6]));
    assert_eq!(run(&bytes, "trapz", &[Val::I32(1)]), (false, vec![]));
    assert_eq!(run(&bytes, "trapnz", &[Val::I32(1)]), (true, vec![252]));
    assert_eq!(run(&bytes, "trapnz", &[Val::I32(0)]), (false, vec![]));
    let add = |a, b| run(&bytes, "add_trap", &[Val::I32(a), Val::I32(b)]);
    assert_eq!(add(1, 2), (false, vec![]));
    assert_eq!(add(-1, 2), (true, vec![7]));
}

#[test]
fn runtime_helper_traps_are_reported() {
    let bytes = module(true);
    let zero = [Val::I64(1), Val::I64(0), Val::I64(0), Val::I64(0)];
    assert_eq!(run(&bytes, "divide", &zero), (true, vec![2]));
}

#[test]
fn reporting_is_off_by_default() {
    let bytes = module(false);
    let engine = Engine::default();
    let module = Module::new(&engine, &bytes[..]).unwrap();
    assert!(module.imports().all(|import| import.name() != TRAP_IMPORT));
    let mut store = Store::new(&engine, ());
    let instance = Linker::<()>::new(&engine)
        .instantiate_and_start(&mut store, &module)
        .unwrap();
    let func = instance.get_func(&store, "trap").unwrap();
    assert!(func.call(&mut store, &[], &mut []).is_err());
}

#[test]
fn object_output_leaves_the_trap_import_undefined() {
    let mut module = WasmModule::new().unwrap();
    module.set_translation_options(TranslationOptions {
        report_traps: true,
        ..TranslationOptions::default()
    });
    let function = parse_functions("function %t() { block0: trap user1 }")
        .unwrap()
        .remove(0);
    let id = module
        .declare_function("t", Linkage::Export, &function.signature)
        .unwrap();
    module
        .define_function(id, &mut Context::for_function(function))
        .unwrap();
    let object = module.finish_object().unwrap();
    assert!(
        object
            .windows(TRAP_IMPORT.len())
            .any(|w| w == TRAP_IMPORT.as_bytes())
    );
}
