use crate::error::{Context, Result};
use crate::{bail, ensure, unsupported};
use cranelift_codegen::ir::{self, InstructionData, Opcode, types};
use waffle::{FunctionBody, Operator, Type, ValueDef};

use super::*;
use crate::bridge::FnCx;

/// Emit a call-shaped operator and bind its (expanded, possibly multi-value) results.
pub(super) fn bind_call_results(
    cx: &mut FnCx,
    body: &mut FunctionBody,
    wb: waffle::Block,
    inst: ir::Inst,
    op: Operator,
    wargs: &[waffle::Value],
) -> Result<()> {
    let results: Vec<ir::Value> = cx.clif.dfg.inst_results(inst).to_vec();
    // Flatten result types (i128 -> 2xI64).
    let mut tys = Vec::new();
    let mut widths = Vec::new(); // wasm values per CLIF result
    for &r in &results {
        let expanded = crate::expand_type(cx.clif.dfg.value_type(r))?;
        widths.push(expanded.len());
        tys.extend(expanded);
    }
    let call = body.add_op(wb, op, wargs, &tys);
    match tys.len() {
        0 => {}
        1 => {
            let ty = cx.clif.dfg.value_type(results[0]);
            if ty.is_vector() {
                cx.bind_vector(results[0], normalize_vector(body, wb, ty, vec![call])?);
            } else {
                let value = if matches!(ty, types::I8 | types::I16) {
                    mask_narrow(body, wb, call, ty)
                } else {
                    call
                };
                cx.bind1(results[0], value);
            }
        }
        // Multi-value: waffle models the call as one tuple-typed value; each wasm-level
        // result is a PickOutput projection (risk probe: external builders plausibly
        // never exercised this path).
        _ => {
            let mut idx = 0u32;
            for (&r, &w) in results.iter().zip(widths.iter()) {
                let mut picked = Vec::new();
                for _ in 0..w {
                    let ty = tys[idx as usize];
                    let pv = body.add_value(ValueDef::PickOutput(call, idx, ty));
                    body.append_to_block(wb, pv);
                    picked.push(pv);
                    idx += 1;
                }
                if cx.clif.dfg.value_type(r).is_vector() {
                    let ty = cx.clif.dfg.value_type(r);
                    cx.bind_vector(r, normalize_vector(body, wb, ty, picked)?);
                } else {
                    match w {
                        1 => {
                            let ty = cx.clif.dfg.value_type(r);
                            let value = if matches!(ty, types::I8 | types::I16) {
                                mask_narrow(body, wb, picked[0], ty)
                            } else {
                                picked[0]
                            };
                            cx.bind1(r, value)
                        }
                        2 => cx.bind2(r, picked[0], picked[1]),
                        _ => bail!("unexpected result width {w}"),
                    }
                }
            }
        }
    }
    Ok(())
}

/// Resolve a CLIF `FuncRef` to (ordinal, waffle `Func`): `ExternalName::User
/// { namespace: 0, index: k }` where `k` is the callee's ordinal in the input slice,
/// or an `ExternalName::LibCall` routed to a synthesized runtime helper (which has no
/// ordinal — its address cannot be taken).
pub(crate) fn resolve_callee(
    cx: &FnCx,
    func_ref: ir::FuncRef,
) -> Result<(Option<u32>, waffle::Func)> {
    let ext = &cx.clif.dfg.ext_funcs[func_ref];
    let name_ref = match ext.name {
        ir::ExternalName::User(r) => r,
        ir::ExternalName::TestCase(ref name) => {
            let (ordinal, callee) =
                cx.m.testcase_callees
                    .get(&name.to_string())
                    .with_context(|| format!("unresolved fixture function reference `{name}`"))?;
            return Ok((Some(*ordinal), *callee));
        }
        ir::ExternalName::LibCall(lc) => {
            let kind = match lc {
                ir::LibCall::Memcpy => crate::RuntimeFn::Memcpy,
                ir::LibCall::Memmove => crate::RuntimeFn::Memmove,
                ir::LibCall::Memset => crate::RuntimeFn::Memset,
                ir::LibCall::Memcmp => crate::RuntimeFn::Memcmp,
                other => unsupported!("unimplemented libcall callee {other}"),
            };
            let f =
                cx.m.libcalls
                    .get(&kind)
                    .copied()
                    .with_context(|| format!("libcall {lc} not pre-synthesized"))?;
            return Ok((None, f));
        }
        ref other => {
            unsupported!("unsupported callee name {other:?} (only ExternalName::User/LibCall)")
        }
    };
    let user = cx
        .clif
        .params
        .user_named_funcs()
        .get(name_ref)
        .context("dangling UserExternalNameRef")?;
    ensure!(
        user.namespace == 0,
        "callee namespace {} unsupported (convention: namespace 0, index = ordinal)",
        user.namespace
    );
    let f =
        cx.m.callees
            .get(user.index as usize)
            .copied()
            .with_context(|| {
                format!(
                    "callee index {} out of range ({} functions)",
                    user.index,
                    cx.m.callees.len()
                )
            })?;
    Ok((Some(user.index), f))
}

pub(super) fn lower_func_addr(
    cx: &mut FnCx,
    body: &mut FunctionBody,
    wb: waffle::Block,
    inst: ir::Inst,
) -> Result<()> {
    let dfg = &cx.clif.dfg;
    let InstructionData::FuncAddr {
        opcode: Opcode::FuncAddr,
        func_ref,
    } = dfg.insts[inst]
    else {
        unreachable!("lower_func_addr dispatched on a non-matching instruction")
    };
    let result = dfg.first_result(inst);
    let result_ty = dfg.value_type(result);
    ensure!(
        matches!(result_ty, types::I32 | types::I64),
        "func_addr result must be i32 or i64, got {result_ty}"
    );
    let (ordinal, _) = resolve_callee(cx, func_ref)?;
    let ordinal =
        ordinal.context("func_addr of a libcall helper is unsupported (no table slot)")?;
    let marker =
        cx.m.object_markers
            .funcs
            .get(&ordinal)
            .with_context(|| format!("no marker for func_addr of ordinal {ordinal}"))?;
    let marker = body.add_op(
        wb,
        Operator::GlobalGet {
            global_index: *marker,
        },
        &[],
        &[Type::I32],
    );
    let wv = if result_ty == types::I64 {
        body.add_op(wb, Operator::I64ExtendI32U, &[marker], &[Type::I64])
    } else {
        marker
    };
    cx.bind1(result, wv);
    Ok(())
}

pub(super) fn lower_call(
    cx: &mut FnCx,
    body: &mut FunctionBody,
    wb: waffle::Block,
    inst: ir::Inst,
) -> Result<()> {
    let dfg = &cx.clif.dfg;
    let InstructionData::Call {
        opcode: Opcode::Call,
        args,
        func_ref,
    } = dfg.insts[inst]
    else {
        unreachable!("lower_call dispatched on a non-matching instruction")
    };
    let (_, callee) = resolve_callee(cx, func_ref)?;
    let mut wargs = Vec::new();
    for &v in args.as_slice(&dfg.value_lists) {
        wargs.extend(cx.expand_use(v)?);
    }
    let op = Operator::Call {
        function_index: callee,
    };
    bind_call_results(cx, body, wb, inst, op, &wargs)?;
    Ok(())
}

pub(super) fn lower_call_indirect(
    cx: &mut FnCx,
    body: &mut FunctionBody,
    wb: waffle::Block,
    inst: ir::Inst,
) -> Result<()> {
    let dfg = &cx.clif.dfg;
    let InstructionData::CallIndirect {
        opcode: Opcode::CallIndirect,
        args,
        sig_ref,
    } = dfg.insts[inst]
    else {
        unreachable!("lower_call_indirect dispatched on a non-matching instruction")
    };
    let all = args.as_slice(&dfg.value_lists);
    ensure!(!all.is_empty(), "call_indirect with no callee operand");
    let callee_ptr = all[0];
    let table_index = match cx.vty(callee_ptr) {
        types::I32 => cx.one(callee_ptr)?,
        types::I64 => {
            let address = cx.one(callee_ptr)?;
            body.add_op(wb, Operator::I32WrapI64, &[address], &[Type::I32])
        }
        other => bail!("call_indirect callee pointer must be i32 or i64, got {other}"),
    };
    let mut wargs = Vec::new();
    for &v in &all[1..] {
        wargs.extend(cx.expand_use(v)?);
    }
    // wasm call_indirect takes the table index as the LAST operand.
    wargs.push(table_index);
    let sig_index = *cx
        .sig_map
        .get(&sig_ref)
        .context("call_indirect signature not interned")?;
    let op = Operator::CallIndirect {
        sig_index,
        table_index: cx.m.table,
    };
    bind_call_results(cx, body, wb, inst, op, &wargs)?;
    Ok(())
}
