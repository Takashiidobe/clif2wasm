//! Signature lowering and synthesized runtime bodies shared by translation and linking.

use crate::waffle as waffle;
use std::collections::HashMap;

use crate::error::Result;
use crate::{ensure, unsupported};
use cranelift_codegen::ir;
use waffle::{FunctionBody, Operator, SignatureData, Terminator, Type};

use crate::{RuntimeFn, expand_type};

/// Build a runtime helper directly as waffle IR. The signature comes from the call
/// site / declaration (pointer-ish params are wasm i32).
pub(crate) fn synth_runtime_body(
    kind: RuntimeFn,
    module: &waffle::Module,
    sig: waffle::Signature,
    mem0: waffle::Memory,
) -> Result<FunctionBody> {
    let sigdata = &module.signatures[sig];
    let (params, returns) = signature_parts(sigdata)?;
    // The memory intrinsics shims: (mem, delta) -> prev_pages / (mem) -> pages.
    // The mem index param is carried for signature parity with the LLVM
    // intrinsic and ignored (single linear memory).
    match kind {
        RuntimeFn::MemoryGrow => {
            ensure!(
                params.len() == 2 && returns.len() == 1,
                "MemoryGrow expects (i32, i32) -> i32, got {sigdata:?}"
            );
            let mut body = FunctionBody::new(module, sig);
            let entry = body.entry;
            let delta = body.blocks[entry].params[1].1;
            let prev = body.add_op(
                entry,
                Operator::MemoryGrow { mem: mem0 },
                &[delta],
                &[Type::I32],
            );
            body.set_terminator(entry, Terminator::Return { values: vec![prev] });
            return Ok(body);
        }
        RuntimeFn::MemorySize => {
            ensure!(
                params.len() == 1 && returns.len() == 1,
                "MemorySize expects (i32) -> i32, got {sigdata:?}"
            );
            let mut body = FunctionBody::new(module, sig);
            let entry = body.entry;
            let pages = body.add_op(entry, Operator::MemorySize { mem: mem0 }, &[], &[Type::I32]);
            body.set_terminator(
                entry,
                Terminator::Return {
                    values: vec![pages],
                },
            );
            return Ok(body);
        }
        _ => {}
    }
    ensure!(
        params.len() == 3 && params.iter().all(|&t| t == Type::I32),
        "runtime {kind:?} expects (i32, i32, i32) params, got {:?}",
        params
    );
    let returns_ptr = !returns.is_empty();
    let mut body = FunctionBody::new(module, sig);
    let entry = body.entry;
    let a = body.blocks[entry].params[0].1;
    let b = body.blocks[entry].params[1].1;
    let n = body.blocks[entry].params[2].1;
    match kind {
        RuntimeFn::Memcpy | RuntimeFn::Memmove => {
            // memory.copy is overlap-safe, so one body serves both names.
            body.add_op(
                entry,
                Operator::MemoryCopy {
                    dst_mem: mem0,
                    src_mem: mem0,
                },
                &[a, b, n],
                &[],
            );
            let values = if returns_ptr { vec![a] } else { vec![] };
            body.set_terminator(entry, Terminator::Return { values });
        }
        RuntimeFn::Memset => {
            body.add_op(entry, Operator::MemoryFill { mem: mem0 }, &[a, b, n], &[]);
            let values = if returns_ptr { vec![a] } else { vec![] };
            body.set_terminator(entry, Terminator::Return { values });
        }
        // i128 and fma runtime fns are CLIF-synthesized in runtime_i128/runtime_fma and never reach here.
        RuntimeFn::Udivti3
        | RuntimeFn::Divti3
        | RuntimeFn::Umodti3
        | RuntimeFn::Modti3
        | RuntimeFn::U128Mulo
        | RuntimeFn::I128Mulo
        | RuntimeFn::FmaF32
        | RuntimeFn::FmaF64 => {
            unsupported!("{kind:?} is CLIF-synthesized, not waffle-synthesized")
        }
        // Handled by the early returns above.
        RuntimeFn::MemoryGrow | RuntimeFn::MemorySize => unreachable!(),
        RuntimeFn::Memcmp => {
            ensure!(returns_ptr, "memcmp must return i32");
            // entry(a,b,n) -> header(i); header: i==n ? ret0 : cmp;
            // cmp: load bytes, equal ? next(i+1 via header) : ret diff.
            let header = body.add_block();
            let i = body.add_blockparam(header, Type::I32);
            let cmp = body.add_block();
            let ret_eq = body.add_block();
            let ret_diff = body.add_block();

            let zero = body.add_op(entry, Operator::I32Const { value: 0 }, &[], &[Type::I32]);
            body.set_terminator(
                entry,
                Terminator::Br {
                    target: waffle::BlockTarget {
                        block: header,
                        args: vec![zero],
                    },
                },
            );

            let done = body.add_op(header, Operator::I32Eq, &[i, n], &[Type::I32]);
            body.set_terminator(
                header,
                Terminator::CondBr {
                    cond: done,
                    if_true: waffle::BlockTarget {
                        block: ret_eq,
                        args: vec![],
                    },
                    if_false: waffle::BlockTarget {
                        block: cmp,
                        args: vec![],
                    },
                },
            );

            let mem = waffle::MemoryArg {
                align: 0,
                offset: 0,
                memory: mem0,
            };
            let pa = body.add_op(cmp, Operator::I32Add, &[a, i], &[Type::I32]);
            let ba = body.add_op(
                cmp,
                Operator::I32Load8U { memory: mem },
                &[pa],
                &[Type::I32],
            );
            let pb = body.add_op(cmp, Operator::I32Add, &[b, i], &[Type::I32]);
            let bb = body.add_op(
                cmp,
                Operator::I32Load8U { memory: mem },
                &[pb],
                &[Type::I32],
            );
            let eq = body.add_op(cmp, Operator::I32Eq, &[ba, bb], &[Type::I32]);
            let one = body.add_op(cmp, Operator::I32Const { value: 1 }, &[], &[Type::I32]);
            let i2 = body.add_op(cmp, Operator::I32Add, &[i, one], &[Type::I32]);
            body.set_terminator(
                cmp,
                Terminator::CondBr {
                    cond: eq,
                    if_true: waffle::BlockTarget {
                        block: header,
                        args: vec![i2],
                    },
                    if_false: waffle::BlockTarget {
                        block: ret_diff,
                        args: vec![],
                    },
                },
            );

            // cmp dominates ret_diff, so ba/bb are usable here.
            let d = body.add_op(ret_diff, Operator::I32Sub, &[ba, bb], &[Type::I32]);
            body.set_terminator(ret_diff, Terminator::Return { values: vec![d] });

            let z = body.add_op(ret_eq, Operator::I32Const { value: 0 }, &[], &[Type::I32]);
            body.set_terminator(ret_eq, Terminator::Return { values: vec![z] });
        }
    }
    Ok(body)
}

pub(crate) fn intern_sig(
    module: &mut waffle::Module,
    cache: &mut HashMap<SignatureData, waffle::Signature>,
    data: SignatureData,
) -> waffle::Signature {
    *cache
        .entry(data.clone())
        .or_insert_with(|| module.signatures.push(data))
}

pub(crate) fn signature_parts(data: &SignatureData) -> Result<(&[Type], &[Type])> {
    Ok((&data.params, &data.returns))
}

pub(crate) fn signature_data(sig: &ir::Signature) -> Result<SignatureData> {
    let expand_abi = |p: &ir::AbiParam| -> Result<Vec<Type>> {
        match p.purpose {
            ir::ArgumentPurpose::Normal => {}
            // sret is semantically just an i32 out-pointer parameter on wasm32.
            ir::ArgumentPurpose::StructReturn => {
                ensure!(
                    p.value_type == ir::types::I32,
                    "sret param must be i32 (wasm32 pointer), got {}",
                    p.value_type
                );
            }
            other => unsupported!("unsupported ArgumentPurpose {other:?}"),
        }
        expand_type(p.value_type)
    };
    let mut params = Vec::new();
    for p in &sig.params {
        params.extend(expand_abi(p)?);
    }
    let mut returns = Vec::new();
    for r in &sig.returns {
        returns.extend(expand_abi(r)?);
    }
    Ok(SignatureData { params, returns })
}
