use crate::waffle as waffle;
use crate::error::{Context, Result};
use crate::{bail, ensure, unsupported};
use cranelift_codegen::ir::{self, InstructionData, Opcode, types};
use waffle::{FunctionBody, Operator, Type, ValueDef};

use super::*;
use crate::bridge::FnCx;

/// Emit a call-shaped operator; returns each CLIF result as its (expanded, normalized)
/// wasm values.
pub(crate) fn emit_call(
    body: &mut FunctionBody,
    wb: waffle::Block,
    op: Operator,
    wargs: &[waffle::Value],
    result_types: &[ir::Type],
) -> Result<Vec<Vec<waffle::Value>>> {
    let mut tys = Vec::new();
    let mut widths = Vec::new();
    for &ty in result_types {
        let expanded = crate::expand_type(ty)?;
        widths.push(expanded.len());
        tys.extend(expanded);
    }
    let call = body.add_op(wb, op, wargs, &tys);
    let flat = match tys.len() {
        0 => Vec::new(),
        1 => vec![call],
        // Multi-value: waffle models the call as one tuple-typed value; each wasm-level
        // result is a PickOutput projection (risk probe: external builders plausibly
        // never exercised this path).
        _ => tys
            .iter()
            .enumerate()
            .map(|(idx, &ty)| {
                let pv = body.add_value(ValueDef::PickOutput(call, idx as u32, ty));
                body.append_to_block(wb, pv);
                pv
            })
            .collect(),
    };
    let mut groups = Vec::new();
    let mut at = 0;
    for (&ty, &w) in result_types.iter().zip(&widths) {
        let chunk = flat[at..at + w].to_vec();
        at += w;
        groups.push(if ty.is_vector() {
            normalize_vector(body, wb, ty, chunk)?
        } else if matches!(ty, types::I8 | types::I16 | types::F16) {
            vec![mask_narrow(body, wb, chunk[0], ty)]
        } else {
            chunk
        });
    }
    Ok(groups)
}

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
    let types: Vec<ir::Type> = results.iter().map(|&r| cx.vty(r)).collect();
    let groups = emit_call(body, wb, op, wargs, &types)?;
    for ((&r, ty), values) in results.iter().zip(types).zip(groups) {
        if ty.is_vector() {
            cx.bind_vector(r, values);
        } else if values.len() == 2 {
            cx.bind2(r, values[0], values[1]);
        } else {
            cx.bind1(r, values[0]);
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

fn indirect_call_parts(
    cx: &FnCx,
    body: &mut FunctionBody,
    wb: waffle::Block,
    all: &[ir::Value],
    sig_ref: ir::SigRef,
) -> Result<(Operator, Vec<waffle::Value>)> {
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
    Ok((op, wargs))
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
    let (op, wargs) = indirect_call_parts(cx, body, wb, args.as_slice(&dfg.value_lists), sig_ref)?;
    bind_call_results(cx, body, wb, inst, op, &wargs)?;
    Ok(())
}

/// `try_call` / `try_call_indirect` are terminators. Only tables without handlers are
/// lowered: an exception can't be caught, so this is a call followed by a branch to the
/// normal-return block, with `retN` block arguments bound to the call's results.
pub(crate) fn lower_try_call(
    cx: &mut FnCx,
    body: &mut FunctionBody,
    wb: waffle::Block,
    inst: ir::Inst,
    bmap: &std::collections::HashMap<ir::Block, waffle::Block>,
) -> Result<waffle::BlockTarget> {
    let dfg = &cx.clif.dfg;
    let (exception, call) = match dfg.insts[inst] {
        InstructionData::TryCall {
            args,
            func_ref,
            exception,
            ..
        } => {
            let (_, callee) = resolve_callee(cx, func_ref)?;
            let mut wargs = Vec::new();
            for &v in args.as_slice(&dfg.value_lists) {
                wargs.extend(cx.expand_use(v)?);
            }
            (
                exception,
                (
                    Operator::Call {
                        function_index: callee,
                    },
                    wargs,
                ),
            )
        }
        InstructionData::TryCallIndirect {
            args, exception, ..
        } => {
            let sig = dfg.exception_tables[exception].signature();
            (
                exception,
                indirect_call_parts(cx, body, wb, args.as_slice(&dfg.value_lists), sig)?,
            )
        }
        _ => unreachable!("lower_try_call dispatched on a non-matching instruction"),
    };
    let table = &dfg.exception_tables[exception];
    if table.items().any(|item| {
        matches!(
            item,
            ir::ExceptionTableItem::Tag(..) | ir::ExceptionTableItem::Default(..)
        )
    }) {
        unsupported!(
            "try_call with exception handlers is unsupported: the waffle IR has no wasm exception-handling operators"
        );
    }
    let sig = &dfg.signatures[table.signature()];
    let return_types: Vec<ir::Type> = sig.returns.iter().map(|r| r.value_type).collect();
    let rets = emit_call(body, wb, call.0, &call.1, &return_types)?;
    crate::bridge::block_target(cx, bmap, table.normal_return(), &rets)
}

pub(super) fn lower_fma(
    cx: &mut FnCx,
    body: &mut FunctionBody,
    wb: waffle::Block,
    inst: ir::Inst,
    args: [ir::Value; 3],
) -> Result<()> {
    let ty = cx.vty(cx.clif.dfg.first_result(inst));
    let kind = match ty {
        types::F32 => crate::RuntimeFn::FmaF32,
        types::F64 => crate::RuntimeFn::FmaF64,
        other => unsupported!("fma on {other} is unsupported"),
    };
    let callee =
        cx.m.helpers
            .get(&kind)
            .copied()
            .with_context(|| format!("{kind:?} helper was not synthesized for this module"))?;
    let mut wargs = Vec::with_capacity(3);
    for arg in args {
        wargs.extend(cx.expand_use(arg)?);
    }
    let op = Operator::Call {
        function_index: callee,
    };
    bind_call_results(cx, body, wb, inst, op, &wargs)
}
