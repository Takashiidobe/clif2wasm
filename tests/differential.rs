use std::fs;
use std::path::Path;

use cranelift_codegen::data_value::DataValue;
use cranelift_codegen::ir::{Function, Type, types};
use cranelift_interpreter::environment::FunctionStore;
use cranelift_interpreter::interpreter::{Interpreter, InterpreterState};
use cranelift_interpreter::step::ControlFlow;
use cranelift_module::{Linkage, Module as CraneliftModule};
use cranelift_reader::{Invocation, RunCommand, parse_functions, parse_run_command};
use wasmi::{Engine, Instance, Module, Store, Val};

#[path = "support/fuzz.rs"]
mod fuzz;

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
    assert!(!functions.is_empty(), "{}: no functions", path.display());
    let default_entry = functions[0].name.to_string();
    let entry_name = text
        .lines()
        .find_map(|line| line.strip_prefix("; entry:").map(str::trim))
        .unwrap_or(&default_entry);
    let (entry_index, function) = functions
        .iter()
        .enumerate()
        .find(|(_, function)| function.name.to_string() == entry_name)
        .unwrap_or_else(|| {
            panic!(
                "{}: entry function `{entry_name}` not found",
                path.display()
            )
        });
    let names = (0..functions.len())
        .map(|index| {
            if index == entry_index {
                "test".to_owned()
            } else {
                format!("fixture_{index}")
            }
        })
        .collect::<Vec<_>>();
    let expected_span = text
        .lines()
        .find_map(|line| line.strip_prefix("; error-span:").map(str::trim));
    let expected_error = text
        .lines()
        .find_map(|line| line.strip_prefix("; error:").map(str::trim))
        .or(expected_span);
    if let Some(expected) = expected_error {
        let error = translate_fixture(&functions, &names, entry_index).expect_err(
            "error fixture now translates; move it to tests/fixtures and add run expectations",
        );
        let diagnostic = format!("{error:#}");
        assert!(
            diagnostic.contains(expected),
            "{}: expected diagnostic containing `{expected}`, got: {diagnostic}",
            path.display()
        );
        if expected_span.is_some() {
            let clif2wasm::error::Error::Unsupported {
                code: clif2wasm::error::ErrorCode::UnsupportedOpcode,
                source_code: Some(_),
                span: Some(span),
                ..
            } = error
            else {
                panic!(
                    "{}: expected an Unsupported diagnostic with a source span, got {error:?}",
                    path.display()
                );
            };
            assert!(
                !span.is_empty(),
                "{}: diagnostic span is empty",
                path.display()
            );
            assert_eq!(
                miette::Diagnostic::code(&error).unwrap().to_string(),
                "CLIF2WASM-E2000",
                "{}: unstable diagnostic code",
                path.display()
            );
        }
        return;
    }
    let commands = text
        .lines()
        .filter_map(|line| {
            if let Some(trap) = line.strip_prefix("; trap:") {
                let expected = trap_command_results(function);
                let parsed =
                    parse_run_command(&format!("; run:{trap} == {expected}"), &function.signature)
                        .unwrap_or_else(|e| {
                            panic!("reading trap command in {}: {e}", path.display())
                        });
                let Some(RunCommand::Run(invocation, _, _)) = parsed else {
                    panic!("{}: invalid trap command `{line}`", path.display());
                };
                Some(FixtureCommand::Trap(invocation))
            } else if let Some(run) = line.strip_prefix("; wasm-run:") {
                let parsed = parse_run_command(&format!("; run:{run}"), &function.signature)
                    .unwrap_or_else(|e| {
                        panic!("reading wasm run command in {}: {e}", path.display())
                    });
                parsed.map(FixtureCommand::WasmRun)
            } else {
                parse_run_command(line, &function.signature)
                    .unwrap_or_else(|e| panic!("reading run command in {}: {e}", path.display()))
                    .map(FixtureCommand::Run)
            }
        })
        .collect::<Vec<_>>();
    assert!(
        !commands.is_empty(),
        "{}: no `; run:` or `; trap:` commands",
        path.display()
    );

    let wasm = translate_fixture(&functions, &names, entry_index)
        .unwrap_or_else(|e| panic!("translating {}: {e:#}", path.display()));
    let engine = Engine::default();
    let module = Module::new(&engine, &wasm)
        .unwrap_or_else(|e| panic!("validating wasm from {}: {e}", path.display()));

    for (index, command) in commands.iter().enumerate() {
        match command {
            FixtureCommand::Run(command @ RunCommand::Run(invocation, _, _)) => {
                let reference = interpret(&functions, entry_name, &invocation.args);
                let actual =
                    execute_wasm(&engine, &module, function, &invocation.args, path, index);
                let reference = returned(reference, "Cranelift interpreter", path, index);
                let actual = returned(actual, "wasm", path, index);
                assert_values_equal(&reference, &actual, path, index, "interpreter vs wasm");
                command
                    .run(|_, _| Ok(reference.clone()))
                    .unwrap_or_else(|e| panic!("{}: interpreter: {e}", path.display()));
                command
                    .run(|_, _| Ok(actual.clone()))
                    .unwrap_or_else(|e| panic!("{}: wasm: {e}", path.display()));
            }
            FixtureCommand::Run(command) => {
                panic!("{}: unsupported print command {command}", path.display());
            }
            FixtureCommand::WasmRun(command @ RunCommand::Run(invocation, _, _)) => {
                let actual =
                    execute_wasm(&engine, &module, function, &invocation.args, path, index);
                let actual = returned(actual, "wasm", path, index);
                command
                    .run(|_, _| Ok(actual.clone()))
                    .unwrap_or_else(|e| panic!("{}: wasm: {e}", path.display()));
            }
            FixtureCommand::WasmRun(command) => {
                panic!(
                    "{}: unsupported wasm print command {command}",
                    path.display()
                );
            }
            FixtureCommand::Trap(invocation) => {
                let reference = interpret(&functions, entry_name, &invocation.args);
                let actual =
                    execute_wasm(&engine, &module, function, &invocation.args, path, index);
                assert_trapped(reference, actual, path, index);
            }
        }
    }
}

fn translate_fixture(
    functions: &[Function],
    names: &[String],
    entry_index: usize,
) -> clif2wasm::error::Result<Vec<u8>> {
    translate_fixture_with_options(
        functions,
        names,
        entry_index,
        clif2wasm::TranslationOptions::default(),
    )
}

fn translate_fixture_with_options(
    functions: &[Function],
    names: &[String],
    entry_index: usize,
    options: clif2wasm::TranslationOptions,
) -> clif2wasm::error::Result<Vec<u8>> {
    let mut module = clif2wasm::WasmModule::new()?;
    module.set_translation_options(options);
    let mut ids = Vec::with_capacity(functions.len());
    for (index, (function, name)) in functions.iter().zip(names).enumerate() {
        let linkage = if index == entry_index {
            Linkage::Export
        } else {
            Linkage::Local
        };
        ids.push(
            module
                .declare_function(name, linkage, &function.signature)
                .expect("declare fixture function"),
        );
    }
    for (function, id) in functions.iter().zip(ids) {
        let mut context = cranelift_codegen::Context::for_function(function.clone());
        module
            .define_function(id, &mut context)
            .expect("define fixture function");
    }
    module.finish()
}

fn trap_command_results(function: &Function) -> String {
    let values = function
        .signature
        .returns
        .iter()
        .map(|ret| match ret.value_type {
            types::F32 | types::F64 => "0.0".to_owned(),
            types::I8 | types::I16 | types::I32 | types::I64 | types::I128 => "0".to_owned(),
            other => panic!("unsupported trap fixture return type {other}"),
        })
        .collect::<Vec<_>>();
    match values.as_slice() {
        [] => "[]".to_owned(),
        [value] => value.clone(),
        _ => format!("[{}]", values.join(", ")),
    }
}

enum FixtureCommand {
    Run(RunCommand),
    WasmRun(RunCommand),
    Trap(Invocation),
}

enum Execution {
    Returned(Vec<DataValue>),
    Trapped(String),
    Failed(String),
}

fn interpret(functions: &[Function], entry_name: &str, args: &[DataValue]) -> Execution {
    let mut function_store = FunctionStore::default();
    for function in functions {
        function_store.add(function.name.to_string(), function);
    }
    let state = InterpreterState::default().with_function_store(function_store);
    let mut interpreter = Interpreter::new(state).with_fuel(Some(100_000));
    match interpreter.call_by_name(entry_name, args) {
        Ok(ControlFlow::Return(values)) => Execution::Returned(values.into_vec()),
        Ok(ControlFlow::Trap(trap)) => Execution::Trapped(format!("CLIF trapped: {trap}")),
        Ok(other) => Execution::Failed(format!("CLIF ended unexpectedly: {other:?}")),
        Err(error) => Execution::Failed(format!("CLIF interpreter failed: {error:?}")),
    }
}

fn execute_wasm(
    engine: &Engine,
    module: &Module,
    function: &Function,
    args: &[DataValue],
    path: &Path,
    case: usize,
) -> Execution {
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
    if let Err(error) = func.call(&mut store, &wasm_args, &mut results) {
        return Execution::Trapped(format!("wasm trapped: {error}"));
    }
    let mut index = 0;
    let values = function
        .signature
        .returns
        .iter()
        .map(|ret| {
            let (value, count) = from_wasm_result(ret.value_type, &results[index..]);
            index += count;
            value
        })
        .collect::<Vec<_>>();
    Execution::Returned(values)
}

fn returned(execution: Execution, engine: &str, path: &Path, case: usize) -> Vec<DataValue> {
    match execution {
        Execution::Returned(values) => values,
        Execution::Trapped(error) | Execution::Failed(error) => {
            panic!("{} case {}: {engine}: {error}", path.display(), case + 1)
        }
    }
}

fn assert_trapped(reference: Execution, actual: Execution, path: &Path, case: usize) {
    match (reference, actual) {
        (Execution::Trapped(_), Execution::Trapped(_)) => {}
        (Execution::Returned(reference), Execution::Returned(actual)) => panic!(
            "{} case {}: expected both engines to trap, both returned; CLIF={reference:?}, wasm={actual:?}",
            path.display(),
            case + 1
        ),
        (Execution::Trapped(error), Execution::Returned(actual)) => panic!(
            "{} case {}: expected wasm to trap like the CLIF interpreter ({error}), but returned {actual:?}",
            path.display(),
            case + 1
        ),
        (Execution::Returned(reference), Execution::Trapped(error)) => panic!(
            "{} case {}: expected the CLIF interpreter to trap like wasm ({error}), but returned {reference:?}",
            path.display(),
            case + 1
        ),
        (Execution::Failed(error), _) => panic!(
            "{} case {}: CLIF interpreter failed instead of trapping: {error}",
            path.display(),
            case + 1
        ),
        (_, Execution::Failed(error)) => panic!(
            "{} case {}: wasm execution failed instead of trapping: {error}",
            path.display(),
            case + 1
        ),
    }
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
        DataValue::F16(value) => vec![Val::I32(i32::from(value.bits()))],
        DataValue::F32(value) => vec![Val::from(value.as_f32())],
        DataValue::F64(value) => vec![Val::from(value.as_f64())],
        DataValue::V128(value) => vec![Val::V128(wasmi::V128::from(u128::from_le_bytes(*value)))],
        DataValue::V64(value) => vec![Val::V128(wasmi::V128::from(
            u64::from_le_bytes(*value) as u128
        ))],
        DataValue::V32(value) => vec![Val::V128(wasmi::V128::from(
            u32::from_le_bytes(*value) as u128
        ))],
        DataValue::V16(value) => vec![Val::V128(wasmi::V128::from(
            u16::from_le_bytes(*value) as u128
        ))],
        other => panic!("unsupported fixture argument {other:?}"),
    }
}

fn wasm_result_types(ty: Type) -> Vec<Val> {
    match ty {
        types::I8 | types::I16 | types::I32 | types::F16 => vec![Val::I32(0)],
        types::I64 => vec![Val::I64(0)],
        types::I128 => vec![Val::I64(0), Val::I64(0)],
        types::F32 => vec![Val::from(0.0f32)],
        types::F64 => vec![Val::from(0.0f64)],
        ty if ty.is_vector() && ty.bits() <= 128 => vec![Val::V128(wasmi::V128::from(0_u128))],
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
        (types::F16, [Val::I32(value), ..]) => (
            DataValue::F16(cranelift_codegen::ir::immediates::Ieee16::with_bits(
                *value as u16,
            )),
            1,
        ),
        (types::F32, [Val::F32(value), ..]) => (DataValue::F32(value.to_float().into()), 1),
        (types::F64, [Val::F64(value), ..]) => (DataValue::F64(value.to_float().into()), 1),
        (ty, [Val::V128(value), ..]) if ty.is_vector() && ty.bits() <= 128 => (
            match ty.bits() {
                16 => DataValue::V16((value.as_u128() as u16).to_le_bytes()),
                32 => DataValue::V32((value.as_u128() as u32).to_le_bytes()),
                64 => DataValue::V64((value.as_u128() as u64).to_le_bytes()),
                128 => DataValue::V128(value.as_u128().to_le_bytes()),
                bits => panic!("unsupported wasm vector result width {bits}"),
            },
            1,
        ),
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
