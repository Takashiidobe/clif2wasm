use std::path::PathBuf;
use std::process::Command;

use clif2wasm::object::{ObjBinding, ObjData, ObjDataDef, ObjDef, ObjFunc, translate_object};
use cranelift_reader::parse_functions;
use wasmi::{Engine, Instance, Module, Store, Val};

fn wasm_ld() -> Option<PathBuf> {
    Command::new("wasm-ld")
        .arg("--version")
        .output()
        .ok()
        .filter(|output| output.status.success())
        .map(|_| PathBuf::from("wasm-ld"))
}

const PADDING: &str = "
function %pad0() -> i32 {
block0:
    v0 = iconst.i32 0
    return v0
}
function %pad1() -> i32 {
block0:
    v0 = iconst.i32 1
    return v0
}
function %pad2() -> i32 {
block0:
    v0 = iconst.i32 2
    return v0
}
";

fn build_object(label: &str, names: &[&'static str], source: &str, data: &[ObjData]) -> Vec<u8> {
    let functions = parse_functions(source).unwrap_or_else(|e| panic!("parsing {label}: {e}"));
    let funcs = functions
        .iter()
        .zip(names)
        .map(|(function, &name)| ObjFunc {
            name,
            binding: ObjBinding::Global,
            hidden: false,
            def: Some(ObjDef::Clif(function)),
            sig: function.signature.clone(),
        })
        .collect::<Vec<_>>();
    let object = translate_object(&funcs, data).unwrap_or_else(|e| panic!("{label}: {e:#}"));
    wasmparser::Validator::new()
        .validate_all(&object)
        .unwrap_or_else(|e| panic!("{label}: invalid object: {e}"));
    object
}

// a padding object is linked first so every function in the object under test is
// renumbered: a missing function-index relocation then shows up as a wrong call.
fn link_and_call(name: &str, source: &str, data: &[ObjData], arg: i32) -> Option<i32> {
    let linker = wasm_ld()?;
    let padding = build_object(name, &["pad0", "pad1", "pad2"], PADDING, &[]);
    let object = build_object(name, &["count", "main"], source, data);

    let dir = std::env::temp_dir().join(format!("clif2wasm-object-link-{name}"));
    std::fs::create_dir_all(&dir).unwrap();
    let (pad_input, input, output) = (dir.join("pad.o"), dir.join("in.o"), dir.join("out.wasm"));
    std::fs::write(&pad_input, &padding).unwrap();
    std::fs::write(&input, &object).unwrap();
    let status = Command::new(linker)
        .args(["--no-entry", "--no-gc-sections", "--export=main", "-o"])
        .arg(&output)
        .arg(&pad_input)
        .arg(&input)
        .output()
        .unwrap();
    assert!(
        status.status.success(),
        "{name}: wasm-ld failed: {}",
        String::from_utf8_lossy(&status.stderr)
    );

    let engine = Engine::default();
    let module = Module::new(&engine, std::fs::read(&output).unwrap()).unwrap();
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).unwrap();
    let main = instance.get_func(&store, "main").unwrap();
    let mut results = [Val::I32(0)];
    main.call(&mut store, &[Val::I32(arg)], &mut results)
        .unwrap_or_else(|e| panic!("{name}: trapped: {e}"));
    let Val::I32(value) = results[0] else {
        panic!("{name}: non-i32 result")
    };
    Some(value)
}

const MAIN: &str = "
function %main(i32) -> i32 {
    sig0 = (i32, i32) -> i32 tail
    fn0 = colocated u0:0 sig0
block0(v0: i32):
    v1 = iconst.i32 0
    v2 = call fn0(v0, v1)
    return v2
}
";

#[test]
fn direct_calls_link_and_run() {
    let source = "
function %count(i32, i32) -> i32 {
block0(v0: i32, v1: i32):
    v2 = iadd v0, v1
    return v2
}
function %main(i32) -> i32 {
    sig0 = (i32, i32) -> i32
    fn0 = colocated u0:0 sig0
block0(v0: i32):
    v1 = iconst.i32 2
    v2 = call fn0(v0, v1)
    return v2
}
";
    if let Some(value) = link_and_call("direct", source, &[], 40) {
        assert_eq!(value, 42);
    }
}

#[test]
fn direct_tail_call_loop_links_and_runs() {
    let source = format!(
        "
function %count(i32, i32) -> i32 tail {{
    ss0 = explicit_slot 16
    sig0 = (i32, i32) -> i32 tail
    fn0 = colocated u0:0 sig0
block0(v0: i32, v1: i32):
    v2 = stack_addr.i32 ss0
    store v0, v2
    v3 = iconst.i32 0
    v4 = icmp eq v0, v3
    brif v4, block1, block2
block1:
    return v1
block2:
    v5 = load.i32 v2
    v6 = iconst.i32 1
    v7 = isub v5, v6
    v8 = iadd v1, v6
    return_call fn0(v7, v8)
}}
{MAIN}"
    );
    if let Some(value) = link_and_call("direct-tail", &source, &[], 100_000) {
        assert_eq!(value, 100_000);
    }
}

#[test]
fn indirect_tail_call_loop_links_and_runs() {
    let source = format!(
        "
function %count(i32, i32) -> i32 tail {{
    sig0 = (i32, i32) -> i32 tail
    fn0 = colocated u0:0 sig0
block0(v0: i32, v1: i32):
    v3 = iconst.i32 0
    v4 = icmp eq v0, v3
    brif v4, block1, block2
block1:
    return v1
block2:
    v6 = iconst.i32 1
    v7 = isub v0, v6
    v8 = iadd v1, v6
    v9 = func_addr.i32 fn0
    return_call_indirect sig0, v9(v7, v8)
}}
{MAIN}"
    );
    if let Some(value) = link_and_call("indirect-tail", &source, &[], 100_000) {
        assert_eq!(value, 100_000);
    }
}

#[test]
fn data_symbol_links_and_runs() {
    let source = "
function %count(i32) -> i32 {
    gv0 = symbol colocated u1:0+4
block0(v0: i32):
    v1 = symbol_value.i32 gv0
    v2 = load.i32 v1
    return v2
}
function %main(i32) -> i32 {
    sig0 = (i32) -> i32
    fn0 = colocated u0:0 sig0
block0(v0: i32):
    v1 = call fn0(v0)
    return v1
}
";
    let data = [ObjData {
        name: "table",
        binding: ObjBinding::Global,
        hidden: false,
        def: Some(ObjDataDef {
            bytes: [1u32, 77, 3].iter().flat_map(|v| v.to_le_bytes()).collect(),
            align: 4,
            relocs: Vec::new(),
        }),
    }];
    if let Some(value) = link_and_call("data", source, &data, 0) {
        assert_eq!(value, 77);
    }
}
