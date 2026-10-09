use super::*;
use cranelift_codegen::ir::instructions::{
    InstructionFormat, OpcodeConstraints, ResolvedConstraint,
};
use cranelift_codegen::ir::{
    ConstantData, InstructionData, Opcode,
    immediates::{Ieee16, Ieee32, Ieee64, Imm64},
};

const OPCODES: &[&str] = &[
    "iadd", "isub", "imul", "band", "bor", "bxor", "ishl", "ushr", "sshr", "rotl", "rotr",
];

#[test]
fn supported_fixture_programs_match_cranelift_interpreter_for_generated_inputs() {
    let mut paths = Vec::new();
    collect_fixtures(Path::new("tests/fixtures"), &mut paths);
    paths.retain(|path| {
        fs::read_to_string(path)
            .is_ok_and(|text| {
                !text
                    .lines()
                    .any(|line| line.starts_with("; error:") || line == "; fuzz: skip")
            })
    });
    paths.sort();
    assert!(!paths.is_empty(), "no interpreter-backed fixtures found");

    let engine = Engine::default();
    let mut seed_rng = TestRng::new("fixture programs");
    let mut exercised = 0;
    for path in paths {
        let text = fs::read_to_string(&path).unwrap();
        let interpreter_supported = text
            .lines()
            .any(|line| line.starts_with("; run:") || line.starts_with("; trap:"));
        let functions = parse_functions(&text)
            .unwrap_or_else(|error| panic!("parsing {}: {error}", path.display()));
        let default_entry = functions[0].name.to_string();
        let entry_name = text
            .lines()
            .find_map(|line| line.strip_prefix("; entry:").map(str::trim))
            .unwrap_or(&default_entry);
        let (entry_index, _) = functions
            .iter()
            .enumerate()
            .find(|(_, function)| function.name.to_string() == entry_name)
            .unwrap_or_else(|| panic!("{}: entry `{entry_name}` not found", path.display()));
        let names = (0..functions.len())
            .map(|index| {
                if index == entry_index {
                    "test".to_owned()
                } else {
                    format!("fuzz_{index}")
                }
            })
            .collect::<Vec<_>>();

        for program_seed in 1..=8u32 {
            let seed =
                seed_rng.next() ^ program_seed ^ (exercised as u32).wrapping_mul(0x9e37_79b9);
            let mut rng = TestRng::seeded(seed);
            let mut generated_functions = functions.clone();
            for generated in &mut generated_functions {
                randomize_constants(generated, &mut rng);
            }
            let generated_function = &generated_functions[entry_index];
            let wasm = translate_fixture(&generated_functions, &names, entry_index).unwrap_or_else(
                |error| {
                    panic!(
                        "translating {} run seed 0x{:08x}, program seed 0x{seed:08x}: {error:#}",
                        path.display(),
                        seed_rng.seed
                    )
                },
            );
            let module = Module::new(&engine, &wasm).unwrap_or_else(|error| {
                panic!(
                    "validating {} run seed 0x{:08x}, program seed 0x{seed:08x}: {error}",
                    path.display(),
                    seed_rng.seed
                )
            });
            let entry_name = generated_function.name.to_string();

            for case in 0..2 {
                let args = generated_function
                    .signature
                    .params
                    .iter()
                    .map(|param| random_value(param.value_type, &mut rng))
                    .collect::<Vec<_>>();
                let case_id = (program_seed as usize - 1) * 2 + case;
                let actual =
                    execute_wasm(&engine, &module, generated_function, &args, &path, case_id);
                if interpreter_supported {
                    let reference = interpret(&generated_functions, &entry_name, &args);
                    match (reference, actual) {
                        (Execution::Returned(expected), Execution::Returned(actual)) => {
                            assert_fuzz_values_equal(
                                &expected,
                                &actual,
                                &path,
                                case_id,
                                &format!(
                                    "generated input; run seed 0x{:08x}, program seed 0x{seed:08x}",
                                    seed_rng.seed
                                ),
                            )
                        }
                        (reference, actual) => {
                            assert_fuzz_trapped(reference, actual, &path, case_id, seed_rng.seed)
                        }
                    }
                } else if let Execution::Failed(error) = actual {
                    panic!(
                        "{} run seed 0x{:08x}, program seed 0x{seed:08x}: wasm execution failed: {error}",
                        path.display(),
                        seed_rng.seed
                    );
                }
            }
        }
        exercised += 1;
    }
    assert!(exercised > 0, "no fixtures exercised");
}

#[test]
fn supported_simple_opcodes_are_generated_from_cranelift_metadata() {
    let engine = Engine::default();
    let mut generated = 0;
    let mut rng = TestRng::new("metadata opcodes");
    let mut generated_opcodes = std::collections::BTreeSet::new();
    for &opcode in Opcode::all() {
        if opcode == Opcode::ExtractVector {
            continue;
        }
        let format = opcode.format();
        if !matches!(
            format,
            InstructionFormat::Unary
                | InstructionFormat::Binary
                | InstructionFormat::Ternary
                | InstructionFormat::TernaryImm8
                | InstructionFormat::BinaryImm8
                | InstructionFormat::FloatCompare
                | InstructionFormat::IntCompare
        ) {
            continue;
        }
        let constraints = opcode.constraints();
        if !(1..=2).contains(&constraints.num_fixed_results()) {
            continue;
        }
        let Some(typeset) = constraints.ctrl_typeset() else {
            continue;
        };

        for &ctrl_type in candidate_types().iter().filter(|ty| typeset.contains(**ty)) {
            let candidate = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                let args = argument_types(constraints, ctrl_type)?;
                let results = (0..constraints.num_fixed_results())
                    .map(|index| constraints.result_type(index, ctrl_type))
                    .collect::<Vec<_>>();
                Some((args, results))
            }))
            .ok()
            .flatten();
            let Some((args, results)) = candidate else {
                continue;
            };
            if !results.iter().all(|ty| is_wasm_abi_type(*ty))
                || !args.iter().all(|ty| is_wasm_abi_type(*ty))
            {
                continue;
            }
            let source = simple_function_source(opcode, format, &args, &results, ctrl_type);
            let functions = parse_functions(&source).unwrap_or_else(|error| {
                panic!("generated invalid `{opcode}` CLIF: {error}\n{source}")
            });
            let wasm = match translate_fixture(&functions, &["test".to_owned()], 0) {
                Ok(wasm) => wasm,
                Err(
                    clif2wasm::error::Error::Unsupported { .. }
                    | clif2wasm::error::Error::Internal { .. },
                ) => continue,
                Err(error) => {
                    panic!("translating generated `{opcode}` CLIF: {error:#}\n{source}")
                }
            };
            let module = Module::new(&engine, &wasm).unwrap_or_else(|error| {
                panic!("validating generated `{opcode}` wasm: {error}\n{source}")
            });
            let function = &functions[0];
            let entry_name = function.name.to_string();
            for case in 0..4 {
                let values = args
                    .iter()
                    .map(|&ty| random_value(ty, &mut rng))
                    .collect::<Vec<_>>();
                let reference: Result<Execution, ()> = if results.iter().any(|ty| ty.is_vector())
                    || args.iter().any(|ty| ty.is_vector())
                {
                    Err(())
                } else {
                    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                        interpret(&functions, &entry_name, &values)
                    }))
                    .map_err(|_| ())
                };
                let actual = execute_wasm(
                    &engine,
                    &module,
                    function,
                    &values,
                    Path::new("generated opcode"),
                    case,
                );
                match reference {
                    Ok(Execution::Failed(_)) | Err(_) => match actual {
                        Execution::Returned(_) | Execution::Trapped(_) => {}
                        Execution::Failed(error) => {
                            panic!(
                                "generated `{opcode}` wasm execution failed with seed 0x{:08x}: {error}",
                                rng.seed
                            )
                        }
                    },
                    Ok(reference) => match (&reference, &actual) {
                        (Execution::Returned(expected), Execution::Returned(actual)) => {
                            assert_fuzz_values_equal(
                                expected,
                                actual,
                                Path::new("generated opcode"),
                                case,
                                &format!("{opcode} on {ctrl_type}; seed 0x{:08x}", rng.seed),
                            );
                        }
                        _ => assert_fuzz_trapped(
                            reference,
                            actual,
                            Path::new("generated opcode"),
                            case,
                            rng.seed,
                        ),
                    },
                }
            }
            generated += 1;
            generated_opcodes.insert(opcode.to_string());
        }
    }

    assert!(generated > 0, "no supported simple opcodes were generated");
    for opcode in OPCODES {
        assert!(
            generated_opcodes.contains(*opcode),
            "manual integer generator opcode `{opcode}` missing from metadata cases"
        );
    }
}

#[test]
fn every_opcode_format_has_a_fuzzer_route_or_unsupported_classification() {
    let mut routed = std::collections::BTreeSet::new();
    for &opcode in Opcode::all() {
        let route = if opcode == Opcode::ExtractVector {
            "unsupported"
        } else {
            match opcode.format() {
                InstructionFormat::Unary
                | InstructionFormat::Binary
                | InstructionFormat::Ternary
                | InstructionFormat::TernaryImm8
                | InstructionFormat::BinaryImm8
                | InstructionFormat::FloatCompare
                | InstructionFormat::IntCompare => "metadata",
                InstructionFormat::Load | InstructionFormat::Store => "memory",
                InstructionFormat::LoadNoOffset
                | InstructionFormat::StoreNoOffset
                | InstructionFormat::AtomicRmw
                | InstructionFormat::AtomicCas => "atomics",
                InstructionFormat::BranchTable => "branch_table",
                InstructionFormat::Brif
                | InstructionFormat::Call
                | InstructionFormat::CallIndirect
                | InstructionFormat::FuncAddr
                | InstructionFormat::Jump
                | InstructionFormat::MultiAry
                | InstructionFormat::Trap
                | InstructionFormat::Shuffle => "fixtures",
                InstructionFormat::NullAry => "nullary",
                InstructionFormat::StackAddr => "stack_address",
                InstructionFormat::UnaryConst => "vector_constants",
                InstructionFormat::UnaryGlobalValue => "symbol_value",
                InstructionFormat::UnaryIeee32
                | InstructionFormat::UnaryIeee64
                | InstructionFormat::UnaryImm => "scalar_constants",
                InstructionFormat::CondTrap
                | InstructionFormat::DynamicStackAddr
                | InstructionFormat::ExceptionHandlerAddress
                | InstructionFormat::IntAddTrap
                | InstructionFormat::TryCall
                | InstructionFormat::TryCallIndirect
                | InstructionFormat::UnaryIeee16 => "unsupported",
            }
        };
        routed.insert(route);
    }

    assert_eq!(
        routed,
        [
            "atomics",
            "branch_table",
            "fixtures",
            "memory",
            "metadata",
            "nullary",
            "scalar_constants",
            "stack_address",
            "symbol_value",
            "unsupported",
            "vector_constants",
        ]
        .into_iter()
        .collect()
    );
}

#[test]
fn supported_constant_opcodes_are_fuzzed() {
    let constants = [
        ("iconst", "i8", "0", "i8"),
        ("iconst", "i16", "0", "i16"),
        ("iconst", "i32", "0", "i32"),
        ("iconst", "i64", "0", "i64"),
        ("f32const", "", "0.0", "f32"),
        ("f64const", "", "0.0", "f64"),
    ];
    let engine = Engine::default();
    let mut rng = TestRng::new("constants");

    for (opcode, suffix, immediate, result) in constants {
        let typed_opcode = if suffix.is_empty() {
            opcode.to_owned()
        } else {
            format!("{opcode}.{suffix}")
        };
        let source = format!(
            "function %test() -> {result} {{\nblock0:\nv0 = {typed_opcode} {immediate}\nreturn v0\n}}\n"
        );
        let functions = parse_functions(&source)
            .unwrap_or_else(|error| panic!("invalid generated `{opcode}` CLIF: {error}\n{source}"));
        for seed in 1..=8 {
            let mut generated_functions = functions.clone();
            randomize_constants(&mut generated_functions[0], &mut rng);
            let wasm = translate_fixture(&generated_functions, &["test".to_owned()], 0)
                .unwrap_or_else(|error| panic!("translating generated `{opcode}`: {error:#}"));
            let module = Module::new(&engine, &wasm)
                .unwrap_or_else(|error| panic!("validating generated `{opcode}`: {error}"));
            let function = &generated_functions[0];
            let entry_name = function.name.to_string();
            let reference = interpret(&generated_functions, &entry_name, &[]);
            let actual = execute_wasm(
                &engine,
                &module,
                function,
                &[],
                Path::new("generated constant"),
                seed,
            );
            match (reference, actual) {
                (Execution::Returned(expected), Execution::Returned(actual)) => {
                    assert_fuzz_values_equal(
                        &expected,
                        &actual,
                        Path::new("generated constant"),
                        seed,
                        &format!("{opcode}; seed 0x{:08x}", rng.seed),
                    );
                }
                (reference, actual) => assert_fuzz_trapped(
                    reference,
                    actual,
                    Path::new("generated constant"),
                    seed,
                    rng.seed,
                ),
            }
        }
    }
}

#[test]
fn supported_nullary_opcode_is_fuzzed() {
    let programs = [(
        "nop",
        "function %test() -> i32 {\nblock0:\nnop\nv0 = iconst.i32 0\nreturn v0\n}\n",
    )];
    let engine = Engine::default();
    let mut rng = TestRng::new("nullary opcode");
    for (label, source) in programs {
        let functions = parse_functions(source)
            .unwrap_or_else(|error| panic!("invalid generated `{label}` CLIF: {error}\n{source}"));
        let entry_index = 0;
        let names = (0..functions.len())
            .map(|index| {
                if index == entry_index {
                    "test".to_owned()
                } else {
                    format!("callee_{index}")
                }
            })
            .collect::<Vec<_>>();
        let wasm = translate_fixture(&functions, &names, entry_index)
            .unwrap_or_else(|error| panic!("translating generated `{label}`: {error:#}"));
        let module = Module::new(&engine, &wasm)
            .unwrap_or_else(|error| panic!("validating generated `{label}`: {error}"));
        let function = &functions[entry_index];
        let entry_name = function.name.to_string();
        for case in 0..16 {
            let args = function
                .signature
                .params
                .iter()
                .map(|param| random_value(param.value_type, &mut rng))
                .collect::<Vec<_>>();
            let reference = interpret(&functions, &entry_name, &args);
            let actual = execute_wasm(
                &engine,
                &module,
                function,
                &args,
                Path::new("generated nullary opcode"),
                case,
            );
            match (reference, actual) {
                (Execution::Returned(expected), Execution::Returned(actual)) => {
                    assert_fuzz_values_equal(
                        &expected,
                        &actual,
                        Path::new("generated nullary opcode"),
                        case,
                        &format!("{label}; seed 0x{:08x}", rng.seed),
                    );
                }
                (reference, actual) => assert_fuzz_trapped(
                    reference,
                    actual,
                    Path::new("generated nullary opcode"),
                    case,
                    rng.seed,
                ),
            }
        }
    }
}

#[test]
fn supported_stack_address_opcode_is_fuzzed() {
    let engine = Engine::default();
    let mut rng = TestRng::new("stack address");

    for case in 0..32 {
        let slot_size = 4 + rng.next() % 28;
        let offset = rng.next() % (slot_size - 3);
        let value = rng.next() as i32;
        let source = format!(
            "function %test() -> i32 {{\n    ss0 = explicit_slot {slot_size}\nblock0:\n    v0 = stack_addr.i32 ss0+{offset}\n    v1 = iconst.i32 {value}\n    store.i32 v1, v0\n    v2 = load.i32 v0\n    return v2\n}}\n"
        );
        let functions = parse_functions(&source).unwrap_or_else(|error| {
            panic!("invalid generated `stack_addr` CLIF: {error}\n{source}")
        });
        let wasm = translate_fixture(&functions, &["test".to_owned()], 0)
            .unwrap_or_else(|error| panic!("translating generated `stack_addr`: {error:#}"));
        let module = Module::new(&engine, &wasm)
            .unwrap_or_else(|error| panic!("validating generated `stack_addr`: {error}"));
        let function = &functions[0];
        let entry_name = function.name.to_string();
        let reference = interpret(&functions, &entry_name, &[]);
        let actual = execute_wasm(
            &engine,
            &module,
            function,
            &[],
            Path::new("generated stack address"),
            case,
        );
        match (reference, actual) {
            (Execution::Returned(expected), Execution::Returned(actual)) => {
                assert_fuzz_values_equal(
                    &expected,
                    &actual,
                    Path::new("generated stack address"),
                    case,
                    &format!("slot {slot_size}, offset {offset}, seed 0x{:08x}", rng.seed),
                );
            }
            (reference, actual) => assert_fuzz_trapped(
                reference,
                actual,
                Path::new("generated stack address"),
                case,
                rng.seed,
            ),
        }
    }
}

#[test]
fn supported_symbol_value_opcode_is_fuzzed() {
    use clif2wasm::object::{ObjBinding, ObjData, ObjDataDef, ObjDef, ObjFunc};

    for offset in 0..16 {
        let source = format!(
            "function %test() -> i32 {{\n    gv0 = symbol u1:0+{offset}\nblock0:\n    v0 = symbol_value.i32 gv0\n    return v0\n}}\n"
        );
        let functions = parse_functions(&source).unwrap_or_else(|error| {
            panic!("invalid generated `symbol_value` CLIF: {error}\n{source}")
        });
        let function = &functions[0];
        let funcs = [ObjFunc {
            name: "test",
            binding: ObjBinding::Global,
            hidden: false,
            def: Some(ObjDef::Clif(function)),
            sig: function.signature.clone(),
            gv_symbols: Default::default(),
        }];
        let data = [ObjData {
            name: "data",
            binding: ObjBinding::Global,
            hidden: false,
            def: Some(ObjDataDef {
                bytes: vec![0; 32],
                align: 4,
                relocs: Vec::new(),
            }),
        }];
        let object = clif2wasm::object::translate_object(&funcs, &data)
            .unwrap_or_else(|error| panic!("translating generated `symbol_value`: {error:#}"));
        wasmparser::Validator::new()
            .validate_all(&object)
            .unwrap_or_else(|error| panic!("validating generated `symbol_value` object: {error}"));
    }
}

#[test]
fn supported_direct_tail_call_opcode_is_fuzzed() {
    use cranelift_codegen::ir::{
        AbiParam, ExtFuncData, ExternalName, Function, InstBuilder, Signature, UserExternalName,
        UserFuncName,
    };
    use cranelift_codegen::isa::{CallConv, TargetFrontendConfig};
    use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};

    let callee_source = "function %callee(i32) -> i32 {\nblock0(v0: i32):\nreturn v0\n}\n";
    let callee = parse_functions(callee_source)
        .unwrap_or_else(|error| panic!("invalid generated callee CLIF: {error}"))
        .remove(0);
    let mut signature = Signature::new(CallConv::SystemV);
    signature.params.push(AbiParam::new(types::I32));
    signature.returns.push(AbiParam::new(types::I32));
    let mut caller =
        Function::with_name_signature(UserFuncName::testcase("test"), signature.clone());
    let sig_ref = caller.import_signature(signature.clone());
    let name_ref = caller.declare_imported_user_function(UserExternalName::new(0, 0));
    let func_ref = caller.import_function(ExtFuncData {
        name: ExternalName::User(name_ref),
        signature: sig_ref,
        colocated: true,
        patchable: false,
    });
    let mut context = FunctionBuilderContext::new();
    let mut builder = FunctionBuilder::new(&mut caller, &mut context);
    let block = builder.create_block();
    builder.append_block_params_for_function_params(block);
    builder.switch_to_block(block);
    let arg = builder.block_params(block)[0];
    builder.ins().return_call(func_ref, &[arg]);
    builder.seal_all_blocks();
    builder.finalize(TargetFrontendConfig {
        default_call_conv: CallConv::SystemV,
        pointer_width: target_lexicon::PointerWidth::U32,
        page_size_align_log2: 12,
    });

    let functions = [callee, caller];
    let wasm = translate_fixture(&functions, &["callee".to_owned(), "test".to_owned()], 1)
        .unwrap_or_else(|error| panic!("translating generated `return_call`: {error:#}"));
    wasmparser::Validator::new()
        .validate_all(&wasm)
        .unwrap_or_else(|error| panic!("validating generated `return_call`: {error}"));
}

#[test]
fn supported_indirect_tail_call_opcode_is_fuzzed() {
    use cranelift_codegen::ir::{AbiParam, Function, InstBuilder, Signature, UserFuncName};
    use cranelift_codegen::isa::{CallConv, TargetFrontendConfig};
    use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};

    let callee_source = "function %callee(i32) -> i32 {\nblock0(v0: i32):\nreturn v0\n}\n";
    let callee = parse_functions(callee_source)
        .unwrap_or_else(|error| panic!("invalid generated callee CLIF: {error}"))
        .remove(0);
    let mut caller_signature = Signature::new(CallConv::SystemV);
    caller_signature.params.push(AbiParam::new(types::I64));
    caller_signature.params.push(AbiParam::new(types::I32));
    caller_signature.returns.push(AbiParam::new(types::I32));
    let mut caller =
        Function::with_name_signature(UserFuncName::testcase("test"), caller_signature.clone());
    let sig_ref = caller.import_signature(callee.signature.clone());
    let mut context = FunctionBuilderContext::new();
    let mut builder = FunctionBuilder::new(&mut caller, &mut context);
    let block = builder.create_block();
    builder.append_block_params_for_function_params(block);
    builder.switch_to_block(block);
    let callee_addr = builder.block_params(block)[0];
    let arg = builder.block_params(block)[1];
    builder
        .ins()
        .return_call_indirect(sig_ref, callee_addr, &[arg]);
    builder.seal_all_blocks();
    builder.finalize(TargetFrontendConfig {
        default_call_conv: CallConv::SystemV,
        pointer_width: target_lexicon::PointerWidth::U32,
        page_size_align_log2: 12,
    });

    let functions = [callee, caller];
    let wasm = translate_fixture(&functions, &["callee".to_owned(), "test".to_owned()], 1)
        .unwrap_or_else(|error| panic!("translating generated `return_call_indirect`: {error:#}"));
    wasmparser::Validator::new()
        .validate_all(&wasm)
        .unwrap_or_else(|error| panic!("validating generated `return_call_indirect`: {error}"));
}

#[test]
fn supported_branch_table_opcode_is_fuzzed() {
    let source = "function %test(i32) -> i32 {\nblock0(v0: i32):\nbr_table v0, block1, [block2, block1]\nblock1:\nv1 = iconst.i32 11\nreturn v1\nblock2:\nv2 = iconst.i32 22\nreturn v2\n}\n";
    let functions = parse_functions(source)
        .unwrap_or_else(|error| panic!("invalid generated `br_table` CLIF: {error}\n{source}"));
    let entry_name = functions[0].name.to_string();
    let engine = Engine::default();
    let mut rng = TestRng::new("branch table");
    for program_seed in 1..=8 {
        let mut generated_functions = functions.clone();
        randomize_constants(&mut generated_functions[0], &mut rng);
        let wasm = translate_fixture(&generated_functions, &["test".to_owned()], 0)
            .unwrap_or_else(|error| panic!("translating generated `br_table`: {error:#}"));
        let module = Module::new(&engine, &wasm)
            .unwrap_or_else(|error| panic!("validating generated `br_table`: {error}"));
        let function = &generated_functions[0];
        for case in 0..8 {
            let args = [DataValue::I32(rng.next() as i32)];
            let reference = interpret(&generated_functions, &entry_name, &args);
            let actual = execute_wasm(
                &engine,
                &module,
                function,
                &args,
                Path::new("generated branch table"),
                case,
            );
            match (reference, actual) {
                (Execution::Returned(expected), Execution::Returned(actual)) => {
                    assert_fuzz_values_equal(
                        &expected,
                        &actual,
                        Path::new("generated branch table"),
                        case,
                        &format!("variant {program_seed}, seed 0x{:08x}", rng.seed),
                    );
                }
                (reference, actual) => assert_fuzz_trapped(
                    reference,
                    actual,
                    Path::new("generated branch table"),
                    case,
                    rng.seed,
                ),
            }
        }
    }
}

#[test]
fn supported_memory_opcodes_are_generated_from_cranelift_metadata() {
    let engine = Engine::default();
    let mut generated = 0;
    let mut rng = TestRng::new("memory opcodes");

    for &opcode in Opcode::all() {
        let format = opcode.format();
        if !matches!(format, InstructionFormat::Load | InstructionFormat::Store) {
            continue;
        }
        let constraints = opcode.constraints();
        let Some(typeset) = constraints.ctrl_typeset() else {
            continue;
        };
        for &ctrl_type in candidate_types().iter().filter(|ty| typeset.contains(**ty)) {
            let candidate = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                let args = argument_types(constraints, ctrl_type)?;
                let result = (constraints.num_fixed_results() == 1)
                    .then(|| constraints.result_type(0, ctrl_type));
                Some((args, result))
            }))
            .ok()
            .flatten();
            let Some((args, result)) = candidate else {
                continue;
            };
            if !args.iter().all(|ty| is_wasm_abi_type(*ty))
                || result.is_some_and(|ty| !is_wasm_abi_type(ty))
            {
                continue;
            }
            let source = memory_function_source(opcode, format, &args, result, ctrl_type);
            let functions = parse_functions(&source).unwrap_or_else(|error| {
                panic!("generated invalid memory opcode `{opcode}`: {error}\n{source}")
            });
            let wasm = match translate_fixture(&functions, &["test".to_owned()], 0) {
                Ok(wasm) => wasm,
                Err(
                    clif2wasm::error::Error::Unsupported { .. }
                    | clif2wasm::error::Error::Internal { .. },
                ) => continue,
                Err(error) => {
                    panic!("translating generated memory `{opcode}`: {error:#}\n{source}")
                }
            };
            let module = Module::new(&engine, &wasm)
                .unwrap_or_else(|error| panic!("validating memory `{opcode}`: {error}"));
            let function = &functions[0];
            for case in 0..4 {
                let address_index = if format == InstructionFormat::Load {
                    0
                } else {
                    args.len() - 1
                };
                let values = args
                    .iter()
                    .enumerate()
                    .map(|(index, &ty)| {
                        if index == address_index {
                            random_value_with_value(ty, 0, &mut rng)
                        } else {
                            random_value(ty, &mut rng)
                        }
                    })
                    .collect::<Vec<_>>();
                match execute_wasm(
                    &engine,
                    &module,
                    function,
                    &values,
                    Path::new("generated memory opcode"),
                    case,
                ) {
                    Execution::Returned(_) | Execution::Trapped(_) => {}
                    Execution::Failed(error) => panic!(
                        "generated `{opcode}` wasm execution failed with seed 0x{:08x}: {error}",
                        rng.seed
                    ),
                }
            }
            generated += 1;
        }
    }

    assert!(generated > 0, "no supported memory opcodes were generated");
}

#[test]
fn supported_atomic_opcodes_are_generated_and_wasm_validated() {
    let integer_types = ["i8", "i16", "i32", "i64"];
    let mut programs = Vec::new();
    for ty in integer_types {
        programs.push((
            format!("atomic_load_{ty}"),
            format!("function %test(i32) -> {ty} {{\nblock0(v0: i32):\nv1 = atomic_load.{ty} v0\nreturn v1\n}}\n"),
        ));
        programs.push((
            format!("atomic_store_{ty}"),
            format!("function %test({ty}, i32) -> i32 {{\nblock0(v0: {ty}, v1: i32):\natomic_store v0, v1\nreturn v1\n}}\n"),
        ));
        programs.push((
            format!("atomic_cas_{ty}"),
            format!("function %test(i32, {ty}, {ty}) -> {ty} {{\nblock0(v0: i32, v1: {ty}, v2: {ty}):\nv3 = atomic_cas v0, v1, v2\nreturn v3\n}}\n"),
        ));
        for rmw in ["add", "sub", "and", "or", "xor", "xchg"] {
            programs.push((
                format!("atomic_rmw_{rmw}_{ty}"),
                format!("function %test(i32, {ty}) -> {ty} {{\nblock0(v0: i32, v1: {ty}):\nv2 = atomic_rmw.{ty} {rmw} v0, v1\nreturn v2\n}}\n"),
            ));
        }
    }
    programs.push((
        "fence".to_owned(),
        "function %test() -> i32 {\nblock0:\nfence\nv0 = iconst.i32 0\nreturn v0\n}\n".to_owned(),
    ));

    for (label, source) in programs {
        let functions = parse_functions(&source)
            .unwrap_or_else(|error| panic!("invalid generated `{label}` CLIF: {error}\n{source}"));
        let wasm = translate_fixture_with_options(
            &functions,
            &["test".to_owned()],
            0,
            clif2wasm::TranslationOptions {
                shared_memory_max_pages: Some(2),
            },
        )
        .unwrap_or_else(|error| panic!("translating generated `{label}`: {error:#}\n{source}"));
        wasmparser::Validator::new()
            .validate_all(&wasm)
            .unwrap_or_else(|error| panic!("validating generated `{label}` wasm: {error}"));
    }
}

fn memory_function_source(
    opcode: Opcode,
    format: InstructionFormat,
    args: &[Type],
    result: Option<Type>,
    ctrl_type: Type,
) -> String {
    let params = args
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join(", ");
    let block_params = args
        .iter()
        .enumerate()
        .map(|(index, ty)| format!("v{index}: {ty}"))
        .collect::<Vec<_>>()
        .join(", ");
    let typed_opcode = format!("{opcode}.{ctrl_type}");
    match (format, result) {
        (InstructionFormat::Load, Some(result)) => {
            let output = format!("v{}", args.len());
            format!(
                "function %test({params}) -> {result} {{\nblock0({block_params}):\n{output} = {typed_opcode} v0\nreturn {output}\n}}\n"
            )
        }
        (InstructionFormat::Store, None) => {
            let address = args.len() - 1;
            format!(
                "function %test({params}) -> i32 {{\nblock0({block_params}):\n{typed_opcode} {}\nreturn v{address}\n}}\n",
                operand_names(args.len())
            )
        }
        _ => unreachable!(),
    }
}

fn random_value_with_value(ty: Type, value: u32, rng: &mut TestRng) -> DataValue {
    match ty {
        types::I8 => DataValue::I8(value as i8),
        types::I16 => DataValue::I16(value as i16),
        types::I32 => DataValue::I32(value as i32),
        types::I64 => DataValue::I64(value as i64),
        other => random_value(other, rng),
    }
}

fn candidate_types() -> &'static [Type] {
    &[
        types::I8,
        types::I16,
        types::I32,
        types::I64,
        types::I128,
        types::F32,
        types::F64,
        types::I8X2,
        types::I8X4,
        types::I8X8,
        types::I8X16,
        types::I16X2,
        types::I16X4,
        types::I16X8,
        types::I32X2,
        types::I32X4,
        types::I64X2,
        types::F32X2,
        types::F32X4,
        types::F64X2,
    ]
}

fn is_wasm_abi_type(ty: Type) -> bool {
    matches!(
        ty,
        types::I8 | types::I16 | types::I32 | types::I64 | types::I128 | types::F32 | types::F64
    ) || (ty.is_vector() && ty.bits() <= 128)
}

fn argument_types(constraints: OpcodeConstraints, ctrl_type: Type) -> Option<Vec<Type>> {
    (0..constraints.num_fixed_value_arguments())
        .map(
            |index| match constraints.value_argument_constraint(index, ctrl_type) {
                ResolvedConstraint::Bound(ty) => Some(ty),
                ResolvedConstraint::Free(typeset) => candidate_types()
                    .iter()
                    .copied()
                    .find(|ty| typeset.contains(*ty)),
            },
        )
        .collect()
}

fn simple_function_source(
    opcode: Opcode,
    format: InstructionFormat,
    args: &[Type],
    results: &[Type],
    ctrl_type: Type,
) -> String {
    let params = args
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join(", ");
    let block_params = args
        .iter()
        .enumerate()
        .map(|(index, ty)| format!("v{index}: {ty}"))
        .collect::<Vec<_>>()
        .join(", ");
    let operands = operand_names(args.len());
    let typed_opcode = format!("{opcode}.{ctrl_type}");
    let expression = match format {
        InstructionFormat::FloatCompare => format!("fcmp eq {operands}"),
        InstructionFormat::IntCompare => format!("icmp eq {operands}"),
        InstructionFormat::BinaryImm8 => format!("{typed_opcode} {operands}, 0"),
        InstructionFormat::TernaryImm8 => format!("{typed_opcode} {operands}, 0"),
        _ => format!("{typed_opcode} {operands}"),
    };
    let result_names = (0..results.len())
        .map(|index| format!("v{}", args.len() + index))
        .collect::<Vec<_>>()
        .join(", ");
    let return_type = results[0].to_string();
    let returned = result_names.split(", ").next().unwrap();
    format!(
        "function %test({params}) -> {return_type} {{\nblock0({block_params}):\n{result_names} = {expression}\nreturn {returned}\n}}\n"
    )
}

fn operand_names(count: usize) -> String {
    (0..count)
        .map(|index| format!("v{index}"))
        .collect::<Vec<_>>()
        .join(", ")
}

fn assert_fuzz_values_equal(
    expected: &[DataValue],
    actual: &[DataValue],
    path: &Path,
    case: usize,
    label: &str,
) {
    assert_eq!(
        expected.len(),
        actual.len(),
        "{} case {}: {label}",
        path.display(),
        case + 1
    );
    for (expected, actual) in expected.iter().zip(actual) {
        if expected.bitwise_eq(actual) {
            continue;
        }
        let both_nan = match (expected, actual) {
            (DataValue::F32(left), DataValue::F32(right)) => {
                left.as_f32().is_nan() && right.as_f32().is_nan()
            }
            (DataValue::F64(left), DataValue::F64(right)) => {
                left.as_f64().is_nan() && right.as_f64().is_nan()
            }
            _ => false,
        };
        assert!(
            both_nan,
            "{} case {}: {label}: {expected:?} != {actual:?}",
            path.display(),
            case + 1
        );
    }
}

fn assert_fuzz_trapped(
    reference: Execution,
    actual: Execution,
    path: &Path,
    case: usize,
    seed: u32,
) {
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        assert_trapped(reference, actual, path, case)
    }));
    if let Err(payload) = result {
        let message = payload
            .downcast_ref::<String>()
            .map(String::as_str)
            .or_else(|| payload.downcast_ref::<&str>().copied())
            .unwrap_or("trap mismatch");
        panic!("{message}; fuzz seed 0x{seed:08x}");
    }
}

fn randomize_constants(function: &mut Function, rng: &mut TestRng) {
    let instructions = function
        .layout
        .blocks()
        .flat_map(|block| function.layout.block_insts(block))
        .collect::<Vec<_>>();
    for inst in instructions {
        if let InstructionData::UnaryImm {
            opcode: Opcode::Iconst,
            imm,
        } = &mut function.dfg.insts[inst]
        {
            *imm = Imm64::new(rng.next_u64() as i64);
            continue;
        }
        let lane_count = match function.dfg.insts[inst] {
            InstructionData::BinaryImm8 {
                opcode: Opcode::Extractlane,
                arg,
                ..
            } => Some(function.dfg.value_type(arg).lane_count()),
            InstructionData::TernaryImm8 {
                opcode: Opcode::Insertlane,
                ..
            } => Some(
                function
                    .dfg
                    .value_type(function.dfg.first_result(inst))
                    .lane_count(),
            ),
            _ => None,
        };
        if let Some(lane_count) = lane_count {
            match &mut function.dfg.insts[inst] {
                InstructionData::BinaryImm8 { imm, .. }
                | InstructionData::TernaryImm8 { imm, .. } => {
                    *imm = (rng.next() % lane_count) as u8;
                }
                _ => unreachable!(),
            }
            continue;
        }
        let shuffle = match function.dfg.insts[inst] {
            InstructionData::Shuffle { imm, .. } => Some(imm),
            _ => None,
        };
        if let Some(shuffle) = shuffle {
            let bytes = (0..16).map(|_| (rng.next() % 32) as u8).collect::<Vec<_>>();
            function.dfg.immediates[shuffle] = ConstantData::from(bytes);
            continue;
        }
        let constant_handle = match function.dfg.insts[inst] {
            InstructionData::UnaryConst {
                constant_handle, ..
            } => Some(constant_handle),
            _ => None,
        };
        if let Some(handle) = constant_handle {
            let length = function.dfg.constants.get(handle).len();
            let bytes = (0..length).map(|_| rng.next() as u8).collect::<Vec<_>>();
            let new_handle = function.dfg.constants.insert(ConstantData::from(bytes));
            if let InstructionData::UnaryConst {
                constant_handle, ..
            } = &mut function.dfg.insts[inst]
            {
                *constant_handle = new_handle;
            }
            continue;
        }
        match &mut function.dfg.insts[inst] {
            InstructionData::UnaryIeee16 { imm, .. } => *imm = Ieee16::with_bits(rng.next() as u16),
            InstructionData::UnaryIeee32 { imm, .. } => *imm = Ieee32::with_bits(rng.next()),
            InstructionData::UnaryIeee64 { imm, .. } => *imm = Ieee64::with_bits(rng.next_u64()),
            _ => {}
        }
    }
}

fn random_value(ty: Type, rng: &mut TestRng) -> DataValue {
    match ty {
        types::I8 => DataValue::I8(rng.next() as i8),
        types::I16 => DataValue::I16(rng.next() as i16),
        types::I32 => DataValue::I32(rng.next() as i32),
        types::I64 => DataValue::I64(rng.next_u64() as i64),
        types::I128 => DataValue::I128(rng.next_u128() as i128),
        types::F32 => DataValue::F32(Ieee32::with_bits(rng.next())),
        types::F64 => DataValue::F64(Ieee64::with_bits(rng.next_u64())),
        ty if ty.is_vector() => match ty.bits() {
            16 => DataValue::V16((rng.next() as u16).to_le_bytes()),
            32 => DataValue::V32(rng.next().to_le_bytes()),
            64 => DataValue::V64(rng.next_u64().to_le_bytes()),
            128 => DataValue::V128(rng.next_u128().to_le_bytes()),
            bits => panic!("fuzzer cannot generate {bits}-bit vector values"),
        },
        other => panic!("fuzzer cannot generate argument type {other}"),
    }
}

#[test]
fn generated_supported_integer_programs_match_cranelift_interpreter() {
    let engine = Engine::default();
    let mut seed_rng = TestRng::new("generated integer programs");

    for _ in 0..64 {
        let seed = seed_rng.next();
        let mut rng = TestRng::seeded(seed);
        let mut opcodes = OPCODES.to_vec();
        rng.shuffle(&mut opcodes);
        let mut body =
            String::from("function %test(i32, i32) -> i32 {\nblock0(v0: i32, v1: i32):\n");
        let mut result = "v0".to_owned();
        for (index, opcode) in opcodes.iter().enumerate() {
            let output = format!("v{}", index + 2);
            body.push_str(&format!("{output} = {opcode} {result}, v1\n"));
            result = output;
        }
        body.push_str(&format!("return {result}\n}}\n"));

        let functions = parse_functions(&body)
            .unwrap_or_else(|error| panic!("run seed 0x{:08x}, program seed 0x{seed:08x}: invalid generated CLIF: {error}\n{body}", seed_rng.seed));
        let function = &functions[0];
        let entry_name = function.name.to_string();
        let wasm = translate_fixture(&functions, &["test".to_owned()], 0)
            .unwrap_or_else(|error| panic!("run seed 0x{:08x}, program seed 0x{seed:08x}: translating generated CLIF: {error:#}", seed_rng.seed));
        let module = Module::new(&engine, &wasm).unwrap_or_else(|error| {
            panic!(
                "run seed 0x{:08x}, program seed 0x{seed:08x}: invalid generated wasm: {error}",
                seed_rng.seed
            )
        });

        for case in 0..16 {
            let args = [
                DataValue::I32(rng.next() as i32),
                DataValue::I32(rng.next() as i32),
            ];
            let path = Path::new("generated CLIF");
            let reference = returned(
                interpret(&functions, &entry_name, &args),
                "Cranelift interpreter",
                path,
                case,
            );
            let actual = returned(
                execute_wasm(&engine, &module, function, &args, path, case),
                "wasm",
                path,
                case,
            );
            assert_values_equal(
                &reference,
                &actual,
                path,
                case,
                &format!(
                    "run seed 0x{:08x}, program seed 0x{seed:08x}",
                    seed_rng.seed
                ),
            );
        }
    }
}

struct TestRng {
    state: u32,
    seed: u32,
}

impl TestRng {
    fn new(label: &str) -> Self {
        let mut entropy = [0; 4];
        let base_seed = match std::env::var("CLIF2WASM_FUZZ_SEED") {
            Ok(seed) => parse_fuzz_seed(&seed),
            Err(std::env::VarError::NotPresent) => {
                getrandom::fill(&mut entropy)
                    .expect("failed to obtain OS entropy for CLIF fuzz tests");
                u32::from_le_bytes(entropy)
            }
            Err(error) => panic!("reading CLIF2WASM_FUZZ_SEED: {error}"),
        };
        assert_ne!(base_seed, 0, "fuzz seed for `{label}` must not be zero");
        eprintln!("CLIF2WASM_FUZZ_SEED=0x{base_seed:08x} (suite `{label}`)");
        Self {
            state: base_seed,
            seed: base_seed,
        }
    }

    fn seeded(seed: u32) -> Self {
        let seed = if seed == 0 { 0xa341_316c } else { seed };
        Self { state: seed, seed }
    }

    fn next(&mut self) -> u32 {
        self.state ^= self.state << 13;
        self.state ^= self.state >> 17;
        self.state ^= self.state << 5;
        self.state
    }

    fn shuffle<T>(&mut self, values: &mut [T]) {
        for index in (1..values.len()).rev() {
            values.swap(index, self.next() as usize % (index + 1));
        }
    }

    fn next_u64(&mut self) -> u64 {
        (u64::from(self.next()) << 32) | u64::from(self.next())
    }

    fn next_u128(&mut self) -> u128 {
        (u128::from(self.next_u64()) << 64) | u128::from(self.next_u64())
    }
}

fn parse_fuzz_seed(seed: &str) -> u32 {
    let parsed = if let Some(hex) = seed.strip_prefix("0x") {
        u32::from_str_radix(hex, 16)
    } else {
        seed.parse()
    };
    parsed.unwrap_or_else(|error| {
        panic!(
            "invalid CLIF2WASM_FUZZ_SEED `{seed}` (expected decimal or 0x-prefixed hex): {error}"
        )
    })
}
