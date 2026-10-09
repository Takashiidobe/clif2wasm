use std::fs;
use std::path::Path;

use cranelift_codegen::data_value::DataValue;
use cranelift_codegen::ir::{Function, Type, types};
use cranelift_interpreter::environment::FunctionStore;
use cranelift_interpreter::interpreter::{Interpreter, InterpreterState};
use cranelift_interpreter::step::ControlFlow;
use cranelift_reader::{RunCommand, parse_functions, parse_run_command};
use wasmi::{Engine, Instance, Module, Store, Val};

#[test]
fn fixtures_match_cranelift_interpreter() {
    let mut paths = Vec::new();
    collect_fixtures(Path::new("tests/fixtures"), &mut paths);
    paths.sort();
    assert!(!paths.is_empty(), "no .clif fixtures found");

    for path in paths {
        run_fixture(&path);
    }
}

fn collect_fixtures(directory: &Path, paths: &mut Vec<std::path::PathBuf>) {
    for entry in fs::read_dir(directory).unwrap_or_else(|e| panic!("{}: {e}", directory.display()))
    {
        let path = entry.expect("read fixture entry").path();
        if path.is_dir() {
            collect_fixtures(&path, paths);
        } else if path.extension().is_some_and(|ext| ext == "clif") {
            paths.push(path);
        }
    }
}

fn run_fixture(path: &Path) {
    let text = fs::read_to_string(path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
    let functions =
        parse_functions(&text).unwrap_or_else(|e| panic!("parsing {}: {e}", path.display()));
    assert_eq!(
        functions.len(),
        1,
        "{}: expected one function",
        path.display()
    );
    let function = &functions[0];
    let commands = text
        .lines()
        .map(|line| parse_run_command(line, &function.signature))
        .collect::<Result<Vec<_>, _>>()
        .unwrap_or_else(|e| panic!("reading run commands in {}: {e}", path.display()))
        .into_iter()
        .flatten()
        .collect::<Vec<_>>();
    assert!(
        !commands.is_empty(),
        "{}: no `; run:` commands",
        path.display()
    );

    let named = [clif2wasm::NamedClifFunc::new("test", function)];
    let wasm = clif2wasm::translate_module(&named, "test")
        .unwrap_or_else(|e| panic!("translating {}: {e:#}", path.display()));
    let engine = Engine::default();
    let module = Module::new(&engine, &wasm)
        .unwrap_or_else(|e| panic!("validating wasm from {}: {e}", path.display()));

    for (index, command) in commands.iter().enumerate() {
        let RunCommand::Run(invocation, _, _) = command else {
            panic!(
                "{}: use `run:` commands with expected results",
                path.display()
            );
        };
        let reference = interpret(function, &invocation.args, path, index);
        let actual = execute_wasm(&engine, &module, function, &invocation.args, path, index);
        assert_values_equal(&reference, &actual, path, index, "interpreter vs wasm");
        command
            .run(|_, _| Ok(reference.clone()))
            .unwrap_or_else(|e| panic!("{}: interpreter: {e}", path.display()));
        command
            .run(|_, _| Ok(actual.clone()))
            .unwrap_or_else(|e| panic!("{}: wasm: {e}", path.display()));
    }
}

fn interpret(function: &Function, args: &[DataValue], path: &Path, case: usize) -> Vec<DataValue> {
    let mut functions = FunctionStore::default();
    functions.add("test".to_owned(), function);
    let state = InterpreterState::default().with_function_store(functions);
    let mut interpreter = Interpreter::new(state).with_fuel(Some(100_000));
    match interpreter.call_by_name("test", args) {
        Ok(ControlFlow::Return(values)) => values.into_vec(),
        Ok(ControlFlow::Trap(trap)) => panic!(
            "{} case {} trapped in CLIF: {trap}",
            path.display(),
            case + 1
        ),
        Ok(other) => panic!(
            "{} case {} ended unexpectedly: {other:?}",
            path.display(),
            case + 1
        ),
        Err(error) => panic!(
            "{} case {} failed in CLIF interpreter: {error}",
            path.display(),
            case + 1
        ),
    }
}

fn execute_wasm(
    engine: &Engine,
    module: &Module,
    function: &Function,
    args: &[DataValue],
    path: &Path,
    case: usize,
) -> Vec<DataValue> {
    let mut store = Store::new(engine, ());
    let instance = Instance::new(&mut store, module, &[]).unwrap_or_else(|e| {
        panic!(
            "{} case {} instantiating wasm: {e}",
            path.display(),
            case + 1
        )
    });
    let func = instance
        .get_func(&store, "test")
        .unwrap_or_else(|| panic!("{}: wasm export `test` is missing", path.display()));
    let wasm_args = args.iter().flat_map(to_wasm_args).collect::<Vec<_>>();
    let mut results = function
        .signature
        .returns
        .iter()
        .flat_map(|ret| wasm_result_types(ret.value_type))
        .collect::<Vec<_>>();
    func.call(&mut store, &wasm_args, &mut results)
        .unwrap_or_else(|e| panic!("{} case {} trapped in wasm: {e}", path.display(), case + 1));
    let mut index = 0;
    function
        .signature
        .returns
        .iter()
        .map(|ret| {
            let (value, count) = from_wasm_result(ret.value_type, &results[index..]);
            index += count;
            value
        })
        .collect()
}

fn to_wasm_args(value: &DataValue) -> Vec<Val> {
    match value {
        DataValue::I8(value) => vec![Val::I32(*value as i32)],
        DataValue::I16(value) => vec![Val::I32(*value as i32)],
        DataValue::I32(value) => vec![Val::I32(*value)],
        DataValue::I64(value) => vec![Val::I64(*value)],
        DataValue::I128(value) => vec![
            Val::I64(*value as u64 as i64),
            Val::I64((*value >> 64) as i64),
        ],
        DataValue::F32(value) => vec![Val::from(value.as_f32())],
        DataValue::F64(value) => vec![Val::from(value.as_f64())],
        other => panic!("unsupported fixture argument {other:?}"),
    }
}

fn wasm_result_types(ty: Type) -> Vec<Val> {
    match ty {
        types::I8 | types::I16 | types::I32 => vec![Val::I32(0)],
        types::I64 => vec![Val::I64(0)],
        types::I128 => vec![Val::I64(0), Val::I64(0)],
        types::F32 => vec![Val::from(0.0f32)],
        types::F64 => vec![Val::from(0.0f64)],
        other => panic!("unsupported fixture result type {other}"),
    }
}

fn from_wasm_result(ty: Type, values: &[Val]) -> (DataValue, usize) {
    match (ty, values) {
        (types::I8, [Val::I32(value), ..]) => (DataValue::I8(*value as i8), 1),
        (types::I16, [Val::I32(value), ..]) => (DataValue::I16(*value as i16), 1),
        (types::I32, [Val::I32(value), ..]) => (DataValue::I32(*value), 1),
        (types::I64, [Val::I64(value), ..]) => (DataValue::I64(*value), 1),
        (types::I128, [Val::I64(low), Val::I64(high), ..]) => {
            let value = *low as u64 as u128 | ((*high as u64 as u128) << 64);
            (DataValue::I128(value as i128), 2)
        }
        (types::F32, [Val::F32(value), ..]) => (DataValue::F32(value.to_float().into()), 1),
        (types::F64, [Val::F64(value), ..]) => (DataValue::F64(value.to_float().into()), 1),
        _ => panic!("wasm results do not match CLIF type {ty}: {values:?}"),
    }
}

fn assert_values_equal(
    left: &[DataValue],
    right: &[DataValue],
    path: &Path,
    case: usize,
    label: &str,
) {
    assert_eq!(
        left.len(),
        right.len(),
        "{} case {}: {label}",
        path.display(),
        case + 1
    );
    for (left, right) in left.iter().zip(right) {
        assert!(
            left.bitwise_eq(right),
            "{} case {}: {label}: {left:?} != {right:?}",
            path.display(),
            case + 1
        );
    }
}
