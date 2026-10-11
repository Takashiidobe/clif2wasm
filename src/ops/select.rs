use crate::waffle as waffle;
use crate::error::Result;
use crate::{ensure, unsupported};
use cranelift_codegen::ir::{self, InstructionData, Opcode, types};
use waffle::{FunctionBody, Operator, Type};

use super::*;
use crate::bridge::FnCx;
use crate::map_type;

pub(super) fn lower_select(
    cx: &mut FnCx,
    body: &mut FunctionBody,
    wb: waffle::Block,
    inst: ir::Inst,
) -> Result<()> {
    let dfg = &cx.clif.dfg;
    let InstructionData::Ternary {
        opcode: Opcode::Select | Opcode::SelectSpectreGuard,
        args,
    } = dfg.insts[inst]
    else {
        unreachable!("lower_select dispatched on a non-matching instruction")
    };
    let result = dfg.first_result(inst);
    let rty = dfg.value_type(result);
    let c = coerce_cond(cx, body, wb, args[0])?;
    if rty == types::I128 {
        let (xl, xh) = cx.pair(args[1])?;
        let (yl, yh) = cx.pair(args[2])?;
        let lo = body.add_op(wb, Operator::Select, &[xl, yl, c], &[Type::I64]);
        let hi = body.add_op(wb, Operator::Select, &[xh, yh, c], &[Type::I64]);
        cx.bind2(result, lo, hi);
        return Ok(());
    }
    if rty.is_vector() {
        let yes = cx.vector(args[1])?;
        let no = cx.vector(args[2])?;
        ensure!(yes.len() == no.len(), "vector select chunk count mismatch");
        let values = yes
            .into_iter()
            .zip(no)
            .map(|(yes, no)| body.add_op(wb, Operator::Select, &[yes, no, c], &[Type::V128]))
            .collect();
        cx.bind_vector(result, normalize_vector(body, wb, rty, values)?);
        return Ok(());
    }
    let wty = map_type(rty)?;
    let x = cx.one(args[1])?;
    let y = cx.one(args[2])?;
    // wasm select returns the FIRST operand when cond != 0 — same as CLIF.
    let wv = body.add_op(wb, Operator::Select, &[x, y, c], &[wty]);
    cx.bind1(result, wv);
    Ok(())
}

pub(super) fn lower_bitselect(
    cx: &mut FnCx,
    body: &mut FunctionBody,
    wb: waffle::Block,
    inst: ir::Inst,
) -> Result<()> {
    let dfg = &cx.clif.dfg;
    let InstructionData::Ternary {
        opcode: Opcode::Bitselect,
        args,
    } = dfg.insts[inst]
    else {
        unreachable!("lower_bitselect dispatched on a non-matching instruction")
    };
    let result = dfg.first_result(inst);
    let ty = dfg.value_type(result);
    ensure!(ty.is_vector(), "bitselect requires a vector, got {ty}");
    let mask = cx.vector(args[0])?;
    let yes = cx.vector(args[1])?;
    let no = cx.vector(args[2])?;
    ensure!(
        mask.len() == yes.len() && yes.len() == no.len(),
        "bitselect chunk count mismatch"
    );
    let values = mask
        .into_iter()
        .zip(yes)
        .zip(no)
        .map(|((mask, yes), no)| {
            body.add_op(wb, Operator::V128Bitselect, &[yes, no, mask], &[Type::V128])
        })
        .collect();
    cx.bind_vector(result, normalize_vector(body, wb, ty, values)?);
    Ok(())
}

pub(super) fn lower_blendv(
    cx: &mut FnCx,
    body: &mut FunctionBody,
    wb: waffle::Block,
    inst: ir::Inst,
) -> Result<()> {
    let dfg = &cx.clif.dfg;
    let InstructionData::Ternary {
        opcode: Opcode::Blendv,
        args,
    } = dfg.insts[inst]
    else {
        unreachable!("lower_blendv dispatched on a non-matching instruction")
    };
    let result = dfg.first_result(inst);
    let ty = dfg.value_type(result);
    ensure!(ty.is_vector(), "blendv requires a vector, got {ty}");
    let lane_ty = ty.lane_type();
    let mask_op = match lane_ty.bits() {
        8 => Operator::I8x16LtS,
        16 => Operator::I16x8LtS,
        32 => Operator::I32x4LtS,
        64 => Operator::I64x2LtS,
        _ => unsupported!("blendv lane type {lane_ty} is unsupported"),
    };
    let mask = cx.vector(args[0])?;
    let yes = cx.vector(args[1])?;
    let no = cx.vector(args[2])?;
    ensure!(
        mask.len() == yes.len() && yes.len() == no.len(),
        "blendv chunk count mismatch"
    );
    let zero = body.add_op(wb, Operator::V128Const { value: 0 }, &[], &[Type::V128]);
    let values = mask
        .into_iter()
        .zip(yes)
        .zip(no)
        .map(|((mask, yes), no)| {
            let sign_mask = body.add_op(wb, mask_op, &[mask, zero], &[Type::V128]);
            body.add_op(
                wb,
                Operator::V128Bitselect,
                &[yes, no, sign_mask],
                &[Type::V128],
            )
        })
        .collect();
    cx.bind_vector(result, normalize_vector(body, wb, ty, values)?);
    Ok(())
}
