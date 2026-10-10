//! Characterization tests for the module-assembly modes behind `WasmModule`:
//! static data with relocations, function pointers in data, libcalls, host imports,
//! undefined-symbol policy, and incremental ("session") emission.

use clif2wasm::WasmModule;
use cranelift_codegen::Context;
use cranelift_module::{DataDescription, DataId, FuncId, Linkage, Module as _};
use cranelift_reader::parse_functions;
use wasmi::{Engine, Linker, Module, Store};

#[test]
fn module_frontend_config_uses_wasm_pointer_width() {
    let module = WasmModule::new().unwrap();
    let config = module.target_config();
    assert_eq!(config.pointer_type(), cranelift_codegen::ir::types::I32);
    assert_eq!(
        config.default_call_conv,
        cranelift_codegen::isa::CallConv::SystemV
    );
    assert_eq!(
        module.make_context().func.signature.call_conv,
        config.default_call_conv
    );
    assert_eq!(module.make_signature().call_conv, config.default_call_conv);
}

fn declare(module: &mut WasmModule, name: &str, linkage: Linkage, source: &str) -> FuncId {
    let function = parse_functions(source).unwrap().remove(0);
    module
        .declare_function(name, linkage, &function.signature)
        .unwrap()
}

fn define(module: &mut WasmModule, id: FuncId, source: &str) {
    let function = parse_functions(source).unwrap().remove(0);
    module
        .define_function(id, &mut Context::for_function(function))
        .unwrap();
}

fn run_i32(bytes: &[u8], export: &str, arg: i32) -> i32 {
    let engine = Engine::default();
    let module = Module::new(&engine, bytes).unwrap();
    let mut store = Store::new(&engine, ());
    let mut linker = Linker::new(&engine);
    linker
        .func_wrap("env", "host_add", |a: i32, b: i32| a + b + 1000)
        .unwrap();
    let instance = linker.instantiate_and_start(&mut store, &module).unwrap();
    let func = instance.get_func(&store, export).unwrap();
    let mut results = [wasmi::Val::I32(0)];
    func.call(&mut store, &[wasmi::Val::I32(arg)], &mut results)
        .unwrap();
    let wasmi::Val::I32(value) = results[0] else {
        panic!("non-i32 result")
    };
    value
}

#[test]
fn data_relocations_and_function_pointers() {
    let mut module = WasmModule::new().unwrap();
    let add1_src = "function %add1(i32) -> i32 {\nblock0(v0: i32):\n    v2 = iconst.i32 1\n    v1 = iadd v0, v2\n    return v1\n}";
    let main_src = "function %main(i32) -> i32 {
    sig0 = (i32) -> i32
    gv0 = symbol colocated u1:0
    gv1 = symbol colocated u1:1
block0(v0: i32):
    v1 = symbol_value.i32 gv0
    v2 = load.i32 v1
    v3 = call_indirect sig0, v2(v0)
    v4 = load.i32 v1+4
    v5 = load.i32 v4
    v6 = iadd v3, v5
    v7 = symbol_value.i32 gv1
    v8 = load.i32 v7+4
    v9 = iadd v6, v8
    return v9
}";
    let add1 = declare(&mut module, "add1", Linkage::Local, add1_src);
    let main = declare(&mut module, "main", Linkage::Export, main_src);
    let table = module
        .declare_data("table", Linkage::Local, false, false)
        .unwrap();
    let value = module
        .declare_data("value", Linkage::Local, false, false)
        .unwrap();
    define(&mut module, add1, add1_src);
    define(&mut module, main, main_src);

    let mut table_desc = DataDescription::new();
    table_desc.define(vec![0u8; 8].into_boxed_slice());
    table_desc.set_align(4);
    let func_ref = module.declare_func_in_data(add1, &mut table_desc);
    table_desc.write_function_addr(0, func_ref);
    let value_gv = module.declare_data_in_data(value, &mut table_desc);
    table_desc.write_data_addr(4, value_gv, 0);
    module.define_data(table, &table_desc).unwrap();

    let mut value_desc = DataDescription::new();
    value_desc.define([5u32, 700].iter().flat_map(|v| v.to_le_bytes()).collect());
    value_desc.set_align(4);
    module.define_data(value, &value_desc).unwrap();

    let _: (DataId, DataId) = (table, value);
    let bytes = module.finish().unwrap();
    // main(10) = add1(10) + *value + value[1] = 11 + 5 + 700
    assert_eq!(run_i32(&bytes, "main", 10), 716);
}

#[test]
fn libcalls_are_synthesized() {
    let mut module = WasmModule::new().unwrap();
    let main_src = "function %main(i32) -> i32 {
    ss0 = explicit_slot 32
    sig0 = (i32, i32, i32) -> i32
    fn0 = %Memset sig0
    fn1 = %Memcpy sig0
    fn2 = %Memmove sig0
    fn3 = %Memcmp sig0
block0(v0: i32):
    v1 = stack_addr.i32 ss0
    v2 = stack_addr.i32 ss0+16
    v3 = iconst.i32 0x41
    v4 = iconst.i32 8
    v5 = call fn0(v1, v3, v4)
    v6 = call fn1(v2, v1, v4)
    v7 = call fn3(v1, v2, v4)
    v8 = iconst.i32 0x04030201
    store v8, v1
    v14 = iconst.i32 1
    v9 = iadd v1, v14
    v10 = iconst.i32 3
    v11 = call fn2(v9, v1, v10)
    v12 = load.i32 v1
    v13 = iadd v12, v7
    return v13
}";
    let main = declare(&mut module, "main", Linkage::Export, main_src);
    define(&mut module, main, main_src);
    let bytes = module.finish().unwrap();
    // memmove(a+1, a, 3) over 01 02 03 04 gives 01 01 02 03
    assert_eq!(run_i32(&bytes, "main", 0), 0x0302_0101);
}

#[test]
fn host_imports_and_panic_stubs() {
    let mut module = WasmModule::new().unwrap();
    module.allow_import("host_add");
    let host_src =
        "function %host_add(i32, i32) -> i32 {\nblock0(v0: i32, v1: i32):\n    return v0\n}";
    let panic_src = "function %core_panic() {\nblock0:\n    return\n}";
    let main_src = "function %main(i32) -> i32 {
    sig0 = (i32, i32) -> i32
    sig1 = ()
    fn0 = colocated u0:0 sig0
    fn1 = colocated u0:1 sig1
block0(v0: i32):
    v1 = iconst.i32 0
    brif v0, block1, block2
block1:
    v2 = call fn0(v0, v0)
    return v2
block2:
    call fn1()
    return v1
}";
    declare(&mut module, "host_add", Linkage::Import, host_src);
    declare(&mut module, "core_panic", Linkage::Import, panic_src);
    let main = declare(&mut module, "main", Linkage::Export, main_src);
    define(&mut module, main, main_src);
    let bytes = module.finish().unwrap();
    assert_eq!(run_i32(&bytes, "main", 7), 7 + 7 + 1000);
}

#[test]
fn undefined_non_panic_symbol_is_rejected() {
    let mut module = WasmModule::new().unwrap();
    let missing_src = "function %missing() {\nblock0:\n    return\n}";
    let main_src = "function %main() {
    sig0 = ()
    fn0 = colocated u0:0 sig0
block0:
    call fn0()
    return
}";
    declare(&mut module, "missing", Linkage::Import, missing_src);
    let main = declare(&mut module, "main", Linkage::Export, main_src);
    define(&mut module, main, main_src);
    let error = module.finish().unwrap_err();
    assert!(format!("{error:#}").contains("missing"), "{error:#}");
}

#[test]
fn lenient_option_stubs_undefined_symbols() {
    let mut module = WasmModule::new().unwrap();
    module.set_translation_options(clif2wasm::TranslationOptions {
        lenient: true,
        ..Default::default()
    });
    let missing_src = "function %missing() {\nblock0:\n    return\n}";
    let main_src = "function %main(i32) -> i32 {
    sig0 = ()
    fn0 = colocated u0:0 sig0
block0(v0: i32):
    brif v0, block1, block2
block1:
    call fn0()
    return v0
block2:
    return v0
}";
    declare(&mut module, "missing", Linkage::Import, missing_src);
    let main = declare(&mut module, "main", Linkage::Export, main_src);
    define(&mut module, main, main_src);
    let bytes = module.finish().unwrap();
    assert_eq!(run_i32(&bytes, "main", 0), 0);
}

#[test]
fn shadow_stack_overflow_check_traps_before_memory_is_exhausted() {
    let mut module = WasmModule::new().unwrap();
    // the 17th nested 4 KiB frame sits below the stack base but still in bounds, so only the limit check traps
    let main_src = "function %main(i32) -> i32 {
    ss0 = explicit_slot 4096
    sig0 = (i32) -> i32
    fn0 = colocated u0:0 sig0
block0(v0: i32):
    v1 = stack_addr.i32 ss0
    store v0, v1
    brif v0, block1, block2
block1:
    v2 = iconst.i32 1
    v3 = isub v0, v2
    v4 = call fn0(v3)
    return v4
block2:
    v5 = iconst.i32 0
    return v5
}";
    let main = declare(&mut module, "main", Linkage::Export, main_src);
    define(&mut module, main, main_src);
    let bytes = module.finish().unwrap();
    let engine = Engine::default();
    let module = Module::new(&engine, &bytes[..]).unwrap();
    let call = |depth: i32| {
        let mut store = Store::new(&engine, ());
        let instance = Linker::<()>::new(&engine)
            .instantiate_and_start(&mut store, &module)
            .unwrap();
        let func = instance.get_func(&store, "main").unwrap();
        let mut results = [wasmi::Val::I32(0)];
        func.call(&mut store, &[wasmi::Val::I32(depth)], &mut results)
    };
    assert!(call(15).is_ok());
    assert!(call(16).is_err());
}

#[test]
fn incremental_emission_links_sessions_through_the_host() {
    let mut module = WasmModule::new().unwrap();
    let first_src = "function %first(i32) -> i32 {
    gv0 = symbol colocated u1:0
block0(v0: i32):
    v1 = symbol_value.i32 gv0
    v2 = load.i32 v1
    v3 = iadd v0, v2
    return v3
}";
    let second_src = "function %second(i32) -> i32 {
    sig0 = (i32) -> i32
    fn0 = colocated u0:0 sig0
    gv0 = symbol colocated u1:1
block0(v0: i32):
    v1 = call fn0(v0)
    v2 = symbol_value.i32 gv0
    v3 = load.i32 v2
    v4 = iadd v1, v3
    return v4
}";
    let first = declare(&mut module, "first", Linkage::Export, first_src);
    let one = module
        .declare_data("one", Linkage::Local, false, false)
        .unwrap();
    define(&mut module, first, first_src);
    let mut desc = DataDescription::new();
    desc.define(30u32.to_le_bytes().to_vec().into_boxed_slice());
    desc.set_align(4);
    module.define_data(one, &desc).unwrap();

    let mut next_address = 0x2000u32;
    let mut allocate = |size: usize, align: u32| {
        next_address = (next_address + align - 1) & !(align - 1);
        let address = next_address;
        next_address += size as u32;
        Ok(address)
    };
    let first_bytes = module.emit_incremental(&mut allocate).unwrap();

    let second = declare(&mut module, "second", Linkage::Export, second_src);
    let two = module
        .declare_data("two", Linkage::Local, false, false)
        .unwrap();
    define(&mut module, second, second_src);
    let mut desc = DataDescription::new();
    desc.define(400u32.to_le_bytes().to_vec().into_boxed_slice());
    desc.set_align(4);
    module.define_data(two, &desc).unwrap();
    let second_bytes = module.emit_incremental(&mut allocate).unwrap();

    let engine = Engine::default();
    let mut store = Store::new(&engine, ());
    let memory = wasmi::Memory::new(&mut store, wasmi::MemoryType::new(1, None)).unwrap();
    let table = wasmi::Table::new(
        &mut store,
        wasmi::TableType::new(wasmi::RefType::Func, 8, None),
        wasmi::Ref::Func(wasmi::Nullable::Null),
    )
    .unwrap();
    let stack_pointer =
        wasmi::Global::new(&mut store, wasmi::Val::I32(0x1000), wasmi::Mutability::Var);
    let mut linker = Linker::new(&engine);
    linker.define("env", "memory", memory).unwrap();
    linker.define("env", "table", table).unwrap();
    linker
        .define("env", "stack_pointer", stack_pointer)
        .unwrap();

    let first_module = Module::new(&engine, &first_bytes[..]).unwrap();
    let first_instance = linker
        .instantiate_and_start(&mut store, &first_module)
        .unwrap();
    let first_func = first_instance.get_func(&store, "first").unwrap();
    linker.define("env", "first", first_func).unwrap();

    let second_module = Module::new(&engine, &second_bytes[..]).unwrap();
    let second_instance = linker
        .instantiate_and_start(&mut store, &second_module)
        .unwrap();
    let second_func = second_instance.get_func(&store, "second").unwrap();
    let mut results = [wasmi::Val::I32(0)];
    second_func
        .call(&mut store, &[wasmi::Val::I32(5)], &mut results)
        .unwrap();
    // second(5) = first(5) + 400 = (5 + 30) + 400
    assert!(matches!(results[0], wasmi::Val::I32(435)));
}

fn translate_error(source: &str) -> String {
    let mut module = WasmModule::new().unwrap();
    let id = declare(&mut module, "main", Linkage::Export, source);
    let slot = module
        .declare_data("slot", Linkage::Local, true, false)
        .unwrap();
    let mut desc = DataDescription::new();
    desc.define(vec![0; 4].into_boxed_slice());
    module.define_data(slot, &desc).unwrap();
    let function = parse_functions(source).unwrap().remove(0);
    let defined = module.define_function(id, &mut Context::for_function(function));
    match defined {
        Err(error) => error.to_string(),
        Ok(()) => module.finish().unwrap_err().to_string(),
    }
}

#[test]
fn symbol_value_applies_the_symbol_offset() {
    let mut module = WasmModule::new().unwrap();
    let main_src = "function %main(i32) -> i32 {
    gv0 = symbol colocated u1:0+4
block0(v0: i32):
    v1 = symbol_value.i32 gv0
    v2 = load.i32 v1
    return v2
}";
    let main = declare(&mut module, "main", Linkage::Export, main_src);
    let table = module
        .declare_data("table", Linkage::Local, false, false)
        .unwrap();
    define(&mut module, main, main_src);
    let mut desc = DataDescription::new();
    desc.define([1u32, 77, 3].iter().flat_map(|v| v.to_le_bytes()).collect());
    desc.set_align(4);
    module.define_data(table, &desc).unwrap();
    let bytes = module.finish().unwrap();
    assert_eq!(run_i32(&bytes, "main", 0), 77);
}

#[test]
fn tls_value_is_rejected() {
    let message = translate_error(
        "function %main() -> i32 {
    gv0 = symbol colocated tls u1:0
block0:
    v0 = tls_value.i32 gv0
    return v0
}",
    );
    assert!(message.contains("CLIF2WASM-E2000"), "{message}");
    assert!(message.contains("tls_value"), "{message}");
}

#[test]
fn symbol_value_of_a_tls_symbol_is_rejected() {
    let message = translate_error(
        "function %main() -> i32 {
    gv0 = symbol colocated tls u1:0
block0:
    v0 = symbol_value.i32 gv0
    return v0
}",
    );
    assert!(message.contains("CLIF2WASM-E2000"), "{message}");
    assert!(message.contains("TLS"), "{message}");
}

#[test]
fn non_symbol_global_values_are_rejected() {
    let message = translate_error(
        "function %main() -> i32 {
    gv0 = symbol colocated u1:0
    gv1 = iadd_imm.i32 gv0, 8
block0:
    v0 = symbol_value.i32 gv1
    return v0
}",
    );
    assert!(message.contains("CLIF2WASM-E2000"), "{message}");
    assert!(message.contains("only symbol global values"), "{message}");
}

#[test]
fn thread_local_data_declarations_are_rejected() {
    let mut module = WasmModule::new().unwrap();
    let named = module.declare_data("tls", Linkage::Local, true, true);
    assert!(named.unwrap_err().to_string().contains("thread-local"));
    let anonymous = module.declare_anonymous_data(true, true);
    assert!(anonymous.unwrap_err().to_string().contains("thread-local"));
}

#[test]
fn try_call_without_handlers_is_a_call_and_branch() {
    let mut module = WasmModule::new().unwrap();
    let inc_src = "function %inc(i32) -> i32 {
block0(v0: i32):
    v1 = iadd v0, v0
    return v1
}";
    let main_src = "function %main(i32) -> i32 {
    sig0 = (i32) -> i32
    fn0 = colocated u0:0 sig0
block0(v0: i32):
    try_call fn0(v0), sig0, block1(v0, ret0), [ context v0 ]
block1(v1: i32, v2: i32):
    v3 = iadd v1, v2
    return v3
}";
    let inc = declare(&mut module, "inc", Linkage::Local, inc_src);
    let main = declare(&mut module, "main", Linkage::Export, main_src);
    define(&mut module, inc, inc_src);
    define(&mut module, main, main_src);
    let bytes = module.finish().unwrap();
    assert_eq!(run_i32(&bytes, "main", 300), 900);
}

#[test]
fn try_call_indirect_without_handlers_is_a_call_and_branch() {
    let mut module = WasmModule::new().unwrap();
    let inc_src = "function %inc(i32) -> i32 {
block0(v0: i32):
    v1 = iadd v0, v0
    return v1
}";
    let main_src = "function %main(i32) -> i32 {
    sig0 = (i32) -> i32
    fn0 = colocated u0:0 sig0
block0(v0: i32):
    v1 = func_addr.i32 fn0
    try_call_indirect v1(v0), sig0, block1(ret0), []
block1(v2: i32):
    return v2
}";
    let inc = declare(&mut module, "inc", Linkage::Local, inc_src);
    let main = declare(&mut module, "main", Linkage::Export, main_src);
    define(&mut module, inc, inc_src);
    define(&mut module, main, main_src);
    let bytes = module.finish().unwrap();
    assert_eq!(run_i32(&bytes, "main", 300), 600);
}

#[test]
fn multi_value_call_results_keep_their_order() {
    let mut module = WasmModule::new().unwrap();
    let pair_src = "function %pair(i32) -> i32, i8 {
block0(v0: i32):
    v1 = iadd v0, v0
    v2 = ireduce.i8 v0
    return v1, v2
}";
    let direct_src = "function %direct(i32) -> i32 {
    sig0 = (i32) -> i32, i8
    fn0 = colocated u0:0 sig0
block0(v0: i32):
    v1, v2 = call fn0(v0)
    v3 = uextend.i32 v2
    v4 = iadd v1, v3
    return v4
}";
    let try_src = "function %tried(i32) -> i32 {
    sig0 = (i32) -> i32, i8
    fn0 = colocated u0:0 sig0
block0(v0: i32):
    try_call fn0(v0), sig0, block1(ret1, ret0), []
block1(v1: i8, v2: i32):
    v3 = uextend.i32 v1
    v4 = iadd v2, v3
    return v4
}";
    let pair = declare(&mut module, "pair", Linkage::Local, pair_src);
    let direct = declare(&mut module, "direct", Linkage::Export, direct_src);
    let tried = declare(&mut module, "tried", Linkage::Export, try_src);
    define(&mut module, pair, pair_src);
    define(&mut module, direct, direct_src);
    define(&mut module, tried, try_src);
    let bytes = module.finish().unwrap();
    // pair(300) = (600, 300 as i8 = 44)
    assert_eq!(run_i32(&bytes, "direct", 300), 644);
    assert_eq!(run_i32(&bytes, "tried", 300), 644);
}

#[test]
fn try_call_with_handlers_is_rejected() {
    for table in ["[ tag0: block2(exn0) ]", "[ default: block2(exn0) ]"] {
        let message = translate_error(&format!(
            "function %main(i32) -> i32 {{
    sig0 = (i32) -> i32
    fn0 = colocated u0:0 sig0
block0(v0: i32):
    try_call fn0(v0), sig0, block1(ret0), {table}
block1(v1: i32):
    return v1
block2(v2: i64):
    v3 = iconst.i32 0
    return v3
}}"
        ));
        assert!(message.contains("CLIF2WASM-E2000"), "{message}");
        assert!(message.contains("exception handlers"), "{message}");
    }
}

#[test]
fn tail_call_to_a_host_import() {
    let mut module = WasmModule::new().unwrap();
    module.allow_import("host_add");
    let host_src =
        "function %host_add(i32, i32) -> i32 {\nblock0(v0: i32, v1: i32):\n    return v0\n}";
    let main_src = "function %main(i32) -> i32 {
    sig0 = (i32, i32) -> i32
    fn0 = colocated u0:0 sig0
block0(v0: i32):
    return_call fn0(v0, v0)
}";
    declare(&mut module, "host_add", Linkage::Import, host_src);
    let main = declare(&mut module, "main", Linkage::Export, main_src);
    define(&mut module, main, main_src);
    let bytes = module.finish().unwrap();
    assert_eq!(run_i32(&bytes, "main", 7), 7 + 7 + 1000);
}

#[test]
fn tail_call_forwards_multi_value_results_and_frees_the_frame() {
    let mut module = WasmModule::new().unwrap();
    let pair_src = "function %pair(i32) -> i32, i8 tail {
block0(v0: i32):
    v1 = iadd v0, v0
    v2 = ireduce.i8 v0
    return v1, v2
}";
    let forward_src = "function %forward(i32) -> i32, i8 tail {
    ss0 = explicit_slot 64
    sig0 = (i32) -> i32, i8 tail
    fn0 = colocated u0:0 sig0
block0(v0: i32):
    v1 = stack_addr.i32 ss0
    store v0, v1
    return_call fn0(v0)
}";
    let main_src = "function %main(i32) -> i32 {
    sig0 = (i32) -> i32, i8 tail
    fn0 = colocated u0:1 sig0
block0(v0: i32):
    v1, v2 = call fn0(v0)
    v3 = uextend.i32 v2
    v4 = iadd v1, v3
    return v4
}";
    let pair = declare(&mut module, "pair", Linkage::Local, pair_src);
    let forward = declare(&mut module, "forward", Linkage::Local, forward_src);
    let main = declare(&mut module, "main", Linkage::Export, main_src);
    define(&mut module, pair, pair_src);
    define(&mut module, forward, forward_src);
    define(&mut module, main, main_src);
    let bytes = module.finish().unwrap();
    assert_eq!(run_i32(&bytes, "main", 300), 644);
}

#[test]
fn tail_call_to_a_libcall_is_rejected() {
    let message = translate_error(
        "function %main(i32, i32, i32) tail {
    sig0 = (i32, i32, i32) -> i32 tail
    fn0 = %Memcpy sig0
block0(v0: i32, v1: i32, v2: i32):
    return_call fn0(v0, v1, v2)
}",
    );
    assert!(message.contains("tail libcall unsupported"), "{message}");
}

fn run_i32_result(bytes: &[u8], export: &str, arg: i32) -> Result<i32, wasmi::Error> {
    let engine = Engine::default();
    let module = Module::new(&engine, bytes).unwrap();
    let mut store = Store::new(&engine, ());
    let instance = Linker::new(&engine)
        .instantiate_and_start(&mut store, &module)
        .unwrap();
    let func = instance.get_func(&store, export).unwrap();
    let mut results = [wasmi::Val::I32(0)];
    func.call(&mut store, &[wasmi::Val::I32(arg)], &mut results)?;
    let wasmi::Val::I32(value) = results[0] else {
        panic!("non-i32 result")
    };
    Ok(value)
}

fn conditional_trap_module(opcode: &str) -> Vec<u8> {
    let mut module = WasmModule::new().unwrap();
    let source = format!(
        "function %main(i32) -> i32 {{
block0(v0: i32):
    {opcode} v0, user1
    v1 = iconst.i32 42
    return v1
}}"
    );
    let main = declare(&mut module, "main", Linkage::Export, &source);
    define(&mut module, main, &source);
    module.finish().unwrap()
}

#[test]
fn trapz_traps_only_on_zero() {
    let bytes = conditional_trap_module("trapz");
    assert!(run_i32_result(&bytes, "main", 0).is_err());
    assert_eq!(run_i32_result(&bytes, "main", 5).unwrap(), 42);
}

#[test]
fn trapnz_traps_only_on_nonzero() {
    let bytes = conditional_trap_module("trapnz");
    assert!(run_i32_result(&bytes, "main", 5).is_err());
    assert_eq!(run_i32_result(&bytes, "main", 0).unwrap(), 42);
}

#[test]
fn debugtrap_is_a_no_op() {
    let mut module = WasmModule::new().unwrap();
    let source = "function %main(i32) -> i32 {
block0(v0: i32):
    debugtrap
    return v0
}";
    let main = declare(&mut module, "main", Linkage::Export, source);
    define(&mut module, main, source);
    let bytes = module.finish().unwrap();
    assert_eq!(run_i32(&bytes, "main", 9), 9);
}

#[test]
fn sequence_point_is_erased_and_keeps_store_order() {
    let mut module = WasmModule::new().unwrap();
    let source = "function %main(i32) -> i32 {
    ss0 = explicit_slot 4
block0(v0: i32):
    v1 = stack_addr.i32 ss0
    store v0, v1
    sequence_point
    v2 = iconst.i32 7
    store v2, v1
    sequence_point
    v3 = load.i32 v1
    return v3
}";
    let main = declare(&mut module, "main", Linkage::Export, source);
    define(&mut module, main, source);
    let bytes = module.finish().unwrap();
    assert_eq!(run_i32(&bytes, "main", 9), 7);
}

#[test]
fn get_stack_pointer_tracks_the_shadow_stack() {
    let mut module = WasmModule::new().unwrap();
    let source = "function %main(i32) -> i32 {
    ss0 = explicit_slot 32
block0(v0: i32):
    v1 = get_stack_pointer.i32
    v2 = stack_addr.i32 ss0
    v3 = icmp eq v1, v2
    v4 = uextend.i32 v3
    return v4
}";
    let main = declare(&mut module, "main", Linkage::Export, source);
    define(&mut module, main, source);
    let bytes = module.finish().unwrap();
    assert_eq!(run_i32(&bytes, "main", 0), 1);
}

#[test]
fn machine_state_intrinsics_without_a_wasm_equivalent_are_rejected() {
    for (body, expected) in [
        (
            "v1 = get_pinned_reg.i32",
            "pinned registers are unsupported",
        ),
        ("set_pinned_reg v0", "pinned registers are unsupported"),
        (
            "v1 = get_frame_pointer.i32",
            "get_frame_pointer is unsupported",
        ),
        (
            "v1 = get_return_address.i32",
            "get_return_address is unsupported",
        ),
    ] {
        let source = format!(
            "function %main(i32) {{
block0(v0: i32):
    {body}
    return
}}"
        );
        let message = translate_error(&source);
        assert!(message.contains(expected), "{body}: {message}");
    }
}
