use crate::error::Result;
use crate::{ensure, unsupported};
use cranelift_codegen::ir::{self, Opcode, condcodes::FloatCC, condcodes::IntCC, types};
use waffle::{FunctionBody, Operator, Type};

use super::*;
use crate::bridge::FnCx;
use crate::i128_lower::{self};
use crate::map_type;

pub(crate) fn normalize_vector(
    body: &mut FunctionBody,
    wb: waffle::Block,
    ty: ir::Type,
    mut values: Vec<waffle::Value>,
) -> Result<Vec<waffle::Value>> {
    ensure!(ty.is_vector(), "expected CLIF vector type, got {ty}");
    ensure!(
        values.len() == ty.bits().div_ceil(128) as usize,
        "wrong number of Waffle chunks for CLIF vector {ty}"
    );
    let rem = ty.bits() % 128;
    if rem != 0 {
        let mask = u128::MAX >> (128 - rem);
        let mask = body.add_op(wb, Operator::V128Const { value: mask }, &[], &[Type::V128]);
        let last = values.len() - 1;
        values[last] = body.add_op(wb, Operator::V128And, &[values[last], mask], &[Type::V128]);
    }
    Ok(values)
}

pub(super) fn splat_op(lane: ir::Type) -> Result<Operator> {
    Ok(match lane {
        types::I8 => Operator::I8x16Splat,
        types::I16 => Operator::I16x8Splat,
        types::I32 => Operator::I32x4Splat,
        types::I64 => Operator::I64x2Splat,
        types::F32 => Operator::F32x4Splat,
        types::F64 => Operator::F64x2Splat,
        other => unsupported!("SIMD splat lane type {other} is unsupported"),
    })
}

pub(super) fn replace_lane_op(lane: ir::Type, index: u8) -> Result<Operator> {
    Ok(match lane {
        types::I8 => Operator::I8x16ReplaceLane { lane: index },
        types::I16 => Operator::I16x8ReplaceLane { lane: index },
        types::I32 => Operator::I32x4ReplaceLane { lane: index },
        types::I64 => Operator::I64x2ReplaceLane { lane: index },
        types::F32 => Operator::F32x4ReplaceLane { lane: index },
        types::F64 => Operator::F64x2ReplaceLane { lane: index },
        other => unsupported!("SIMD lane insertion type {other} is unsupported"),
    })
}

pub(super) fn extract_lane_op(lane: ir::Type, index: u8) -> Result<Operator> {
    Ok(match lane {
        types::I8 => Operator::I8x16ExtractLaneU { lane: index },
        types::I16 => Operator::I16x8ExtractLaneU { lane: index },
        types::I32 => Operator::I32x4ExtractLane { lane: index },
        types::I64 => Operator::I64x2ExtractLane { lane: index },
        types::F32 => Operator::F32x4ExtractLane { lane: index },
        types::F64 => Operator::F64x2ExtractLane { lane: index },
        other => unsupported!("SIMD lane extraction type {other} is unsupported"),
    })
}

pub(super) fn vector_binary_operator(opcode: Opcode, lane: ir::Type) -> Result<Operator> {
    let op = match (opcode, lane) {
        (Opcode::Band, _) => Operator::V128And,
        (Opcode::Bor, _) => Operator::V128Or,
        (Opcode::Bxor, _) => Operator::V128Xor,
        (Opcode::Iadd, types::I8) => Operator::I8x16Add,
        (Opcode::Isub, types::I8) => Operator::I8x16Sub,
        (Opcode::SaddSat, types::I8) => Operator::I8x16AddSatS,
        (Opcode::UaddSat, types::I8) => Operator::I8x16AddSatU,
        (Opcode::SsubSat, types::I8) => Operator::I8x16SubSatS,
        (Opcode::UsubSat, types::I8) => Operator::I8x16SubSatU,
        (Opcode::Smin, types::I8) => Operator::I8x16MinS,
        (Opcode::Umin, types::I8) => Operator::I8x16MinU,
        (Opcode::Smax, types::I8) => Operator::I8x16MaxS,
        (Opcode::Umax, types::I8) => Operator::I8x16MaxU,
        (Opcode::AvgRound, types::I8) => Operator::I8x16AvgrU,
        (Opcode::Iadd, types::I16) => Operator::I16x8Add,
        (Opcode::Isub, types::I16) => Operator::I16x8Sub,
        (Opcode::Imul, types::I16) => Operator::I16x8Mul,
        (Opcode::SaddSat, types::I16) => Operator::I16x8AddSatS,
        (Opcode::UaddSat, types::I16) => Operator::I16x8AddSatU,
        (Opcode::SsubSat, types::I16) => Operator::I16x8SubSatS,
        (Opcode::UsubSat, types::I16) => Operator::I16x8SubSatU,
        (Opcode::Smin, types::I16) => Operator::I16x8MinS,
        (Opcode::Umin, types::I16) => Operator::I16x8MinU,
        (Opcode::Smax, types::I16) => Operator::I16x8MaxS,
        (Opcode::Umax, types::I16) => Operator::I16x8MaxU,
        (Opcode::AvgRound, types::I16) => Operator::I16x8AvgrU,
        (Opcode::Iadd, types::I32) => Operator::I32x4Add,
        (Opcode::Isub, types::I32) => Operator::I32x4Sub,
        (Opcode::Imul, types::I32) => Operator::I32x4Mul,
        (Opcode::Smin, types::I32) => Operator::I32x4MinS,
        (Opcode::Umin, types::I32) => Operator::I32x4MinU,
        (Opcode::Smax, types::I32) => Operator::I32x4MaxS,
        (Opcode::Umax, types::I32) => Operator::I32x4MaxU,
        (Opcode::Iadd, types::I64) => Operator::I64x2Add,
        (Opcode::Isub, types::I64) => Operator::I64x2Sub,
        (Opcode::Imul, types::I64) => Operator::I64x2Mul,
        (Opcode::Fadd, types::F32) => Operator::F32x4Add,
        (Opcode::Fsub, types::F32) => Operator::F32x4Sub,
        (Opcode::Fmul, types::F32) => Operator::F32x4Mul,
        (Opcode::Fdiv, types::F32) => Operator::F32x4Div,
        (Opcode::Fmin, types::F32) => Operator::F32x4Min,
        (Opcode::Fmax, types::F32) => Operator::F32x4Max,
        (Opcode::Fadd, types::F64) => Operator::F64x2Add,
        (Opcode::Fsub, types::F64) => Operator::F64x2Sub,
        (Opcode::Fmul, types::F64) => Operator::F64x2Mul,
        (Opcode::Fdiv, types::F64) => Operator::F64x2Div,
        (Opcode::Fmin, types::F64) => Operator::F64x2Min,
        (Opcode::Fmax, types::F64) => Operator::F64x2Max,
        _ => unsupported!("vector opcode {opcode} on lane type {lane} is unsupported"),
    };
    Ok(op)
}

pub(super) fn lower_vector_binary(
    cx: &mut FnCx,
    body: &mut FunctionBody,
    wb: waffle::Block,
    result: ir::Value,
    opcode: Opcode,
    args: [ir::Value; 2],
) -> Result<()> {
    let ty = cx.vty(result);
    ensure!(
        ty.is_vector(),
        "vector operation result is not a vector: {ty}"
    );
    if opcode == Opcode::IaddPairwise {
        return lower_iadd_pairwise(cx, body, wb, result, ty, args);
    }
    if matches!(opcode, Opcode::SqmulRoundSat | Opcode::X86Pmulhrsw) {
        return lower_vector_sqmul_round_sat(cx, body, wb, result, ty, opcode, args);
    }
    if matches!(opcode, Opcode::Smulhi | Opcode::Umulhi) {
        return lower_vector_mulhi(cx, body, wb, result, ty, opcode, args);
    }
    if matches!(
        opcode,
        Opcode::Ishl | Opcode::Ushr | Opcode::Sshr | Opcode::Rotl | Opcode::Rotr
    ) {
        return lower_vector_shift(cx, body, wb, result, ty, opcode, args);
    }
    if opcode == Opcode::Fcopysign {
        return lower_vector_copysign(cx, body, wb, result, ty, args);
    }
    let lhs = cx.vector(args[0])?;
    let rhs = cx.vector(args[1])?;
    ensure!(
        lhs.len() == rhs.len(),
        "vector operation chunk count mismatch"
    );
    let op = vector_binary_operator(opcode, ty.lane_type())?;
    let values = lhs
        .into_iter()
        .zip(rhs)
        .map(|(a, b)| body.add_op(wb, op, &[a, b], &[Type::V128]))
        .collect();
    cx.bind_vector(result, normalize_vector(body, wb, ty, values)?);
    Ok(())
}

pub(super) fn lower_vector_sqmul_round_sat(
    cx: &mut FnCx,
    body: &mut FunctionBody,
    wb: waffle::Block,
    result: ir::Value,
    ty: ir::Type,
    opcode: Opcode,
    args: [ir::Value; 2],
) -> Result<()> {
    let lane_ty = ty.lane_type();
    ensure!(
        matches!(lane_ty, types::I16 | types::I32),
        "{opcode} lane type {lane_ty} is unsupported"
    );
    let lhs = cx.vector(args[0])?;
    let rhs = cx.vector(args[1])?;
    let lanes = ty.lane_count() as usize;
    let per_chunk = (128 / lane_ty.bits()) as usize;
    let mut output = (0..ty.bits().div_ceil(128) as usize)
        .map(|_| body.add_op(wb, Operator::V128Const { value: 0 }, &[], &[Type::V128]))
        .collect::<Vec<_>>();
    for lane in 0..lanes {
        let chunk = lane / per_chunk;
        let index = (lane % per_chunk) as u8;
        let extract = extract_lane_op(lane_ty, index)?;
        let mut a = body.add_op(wb, extract, &[lhs[chunk]], &[Type::I32]);
        let mut b = body.add_op(wb, extract, &[rhs[chunk]], &[Type::I32]);
        if lane_ty == types::I16 {
            a = sign_extend_narrow(body, wb, a, lane_ty);
            b = sign_extend_narrow(body, wb, b, lane_ty);
        }
        let (orig_a, orig_b) = (a, b);
        let a = body.add_op(wb, Operator::I64ExtendI32S, &[a], &[Type::I64]);
        let b = body.add_op(wb, Operator::I64ExtendI32S, &[b], &[Type::I64]);
        let product = body.add_op(wb, Operator::I64Mul, &[a, b], &[Type::I64]);
        let bias = body.add_op(
            wb,
            Operator::I64Const {
                value: 1u64 << (lane_ty.bits() - 2),
            },
            &[],
            &[Type::I64],
        );
        let rounded = body.add_op(wb, Operator::I64Add, &[product, bias], &[Type::I64]);
        let shift = body.add_op(
            wb,
            Operator::I64Const {
                value: lane_ty.bits() as u64 - 1,
            },
            &[],
            &[Type::I64],
        );
        let value = body.add_op(wb, Operator::I64ShrS, &[rounded, shift], &[Type::I64]);
        let min = body.add_op(
            wb,
            Operator::I64Const {
                value: (-(1i64 << (lane_ty.bits() - 1))) as u64,
            },
            &[],
            &[Type::I64],
        );
        let max = body.add_op(
            wb,
            Operator::I64Const {
                value: ((1i64 << (lane_ty.bits() - 1)) - 1) as u64,
            },
            &[],
            &[Type::I64],
        );
        let under = body.add_op(wb, Operator::I64LtS, &[value, min], &[Type::I32]);
        let clamped_low = body.add_op(wb, Operator::Select, &[min, value, under], &[Type::I64]);
        let over = body.add_op(wb, Operator::I64GtS, &[clamped_low, max], &[Type::I32]);
        let clamped = body.add_op(
            wb,
            Operator::Select,
            &[max, clamped_low, over],
            &[Type::I64],
        );
        let mut lane_value = body.add_op(wb, Operator::I32WrapI64, &[clamped], &[Type::I32]);
        if opcode == Opcode::X86Pmulhrsw && lane_ty == types::I16 {
            let min16 = body.add_op(
                wb,
                Operator::I32Const { value: 0xffff_8000 },
                &[],
                &[Type::I32],
            );
            let special_a = body.add_op(wb, Operator::I32Eq, &[orig_a, min16], &[Type::I32]);
            let special_b = body.add_op(wb, Operator::I32Eq, &[orig_b, min16], &[Type::I32]);
            let special = body.add_op(wb, Operator::I32And, &[special_a, special_b], &[Type::I32]);
            lane_value = body.add_op(
                wb,
                Operator::Select,
                &[min16, lane_value, special],
                &[Type::I32],
            );
        }
        if lane_ty == types::I16 {
            lane_value = mask_narrow(body, wb, lane_value, lane_ty);
        }
        let dst_chunk = lane / per_chunk;
        output[dst_chunk] = body.add_op(
            wb,
            replace_lane_op(lane_ty, (lane % per_chunk) as u8)?,
            &[output[dst_chunk], lane_value],
            &[Type::V128],
        );
    }
    cx.bind_vector(result, normalize_vector(body, wb, ty, output)?);
    Ok(())
}

pub(super) fn lower_vector_copysign(
    cx: &mut FnCx,
    body: &mut FunctionBody,
    wb: waffle::Block,
    result: ir::Value,
    ty: ir::Type,
    args: [ir::Value; 2],
) -> Result<()> {
    let lane_ty = ty.lane_type();
    let (scalar_ty, op) = match lane_ty {
        types::F32 => (Type::F32, Operator::F32Copysign),
        types::F64 => (Type::F64, Operator::F64Copysign),
        _ => unsupported!("fcopysign lane type {lane_ty} is unsupported"),
    };
    let lhs = cx.vector(args[0])?;
    let rhs = cx.vector(args[1])?;
    let lane_count = ty.lane_count() as usize;
    let lanes_per_chunk = 128 / lane_ty.bits() as usize;
    let chunks = ty.bits().div_ceil(128) as usize;
    let mut output = (0..chunks)
        .map(|_| body.add_op(wb, Operator::V128Const { value: 0 }, &[], &[Type::V128]))
        .collect::<Vec<_>>();
    for lane in 0..lane_count {
        let chunk = lane / lanes_per_chunk;
        let index = (lane % lanes_per_chunk) as u8;
        let extract = extract_lane_op(lane_ty, index)?;
        let a = body.add_op(wb, extract, &[lhs[chunk]], &[scalar_ty]);
        let b = body.add_op(wb, extract, &[rhs[chunk]], &[scalar_ty]);
        let value = body.add_op(wb, op, &[a, b], &[scalar_ty]);
        let dst_chunk = lane / lanes_per_chunk;
        let dst_lane = (lane % lanes_per_chunk) as u8;
        output[dst_chunk] = body.add_op(
            wb,
            replace_lane_op(lane_ty, dst_lane)?,
            &[output[dst_chunk], value],
            &[Type::V128],
        );
    }
    cx.bind_vector(result, normalize_vector(body, wb, ty, output)?);
    Ok(())
}

pub(super) fn lower_vector_mulhi(
    cx: &mut FnCx,
    body: &mut FunctionBody,
    wb: waffle::Block,
    result: ir::Value,
    ty: ir::Type,
    opcode: Opcode,
    args: [ir::Value; 2],
) -> Result<()> {
    let lane_ty = ty.lane_type();
    ensure!(
        matches!(lane_ty, types::I8 | types::I16 | types::I32 | types::I64),
        "{opcode} lane type {lane_ty} is unsupported"
    );
    let lhs = cx.vector(args[0])?;
    let rhs = cx.vector(args[1])?;
    let lane_count = ty.lane_count() as usize;
    let lanes_per_chunk = 128 / lane_ty.bits() as usize;
    let chunks = ty.bits().div_ceil(128) as usize;
    let signed = opcode == Opcode::Smulhi;
    let mut output = (0..chunks)
        .map(|_| body.add_op(wb, Operator::V128Const { value: 0 }, &[], &[Type::V128]))
        .collect::<Vec<_>>();
    for lane in 0..lane_count {
        let chunk = lane / lanes_per_chunk;
        let index = (lane % lanes_per_chunk) as u8;
        let extract = extract_lane_op(lane_ty, index)?;
        let mut a = body.add_op(wb, extract, &[lhs[chunk]], &[map_type(lane_ty)?]);
        let mut b = body.add_op(wb, extract, &[rhs[chunk]], &[map_type(lane_ty)?]);
        let high = match lane_ty {
            types::I8 | types::I16 => {
                if signed {
                    a = sign_extend_narrow(body, wb, a, lane_ty);
                    b = sign_extend_narrow(body, wb, b, lane_ty);
                }
                let product = body.add_op(wb, Operator::I32Mul, &[a, b], &[Type::I32]);
                let shift = body.add_op(
                    wb,
                    Operator::I32Const {
                        value: lane_ty.bits(),
                    },
                    &[],
                    &[Type::I32],
                );
                let shift_op = if signed {
                    Operator::I32ShrS
                } else {
                    Operator::I32ShrU
                };
                let high = body.add_op(wb, shift_op, &[product, shift], &[Type::I32]);
                mask_narrow(body, wb, high, lane_ty)
            }
            types::I32 => {
                let extend = if signed {
                    Operator::I64ExtendI32S
                } else {
                    Operator::I64ExtendI32U
                };
                let a = body.add_op(wb, extend, &[a], &[Type::I64]);
                let b = body.add_op(wb, extend, &[b], &[Type::I64]);
                let product = body.add_op(wb, Operator::I64Mul, &[a, b], &[Type::I64]);
                let shift = body.add_op(wb, Operator::I64Const { value: 32 }, &[], &[Type::I64]);
                let shift_op = if signed {
                    Operator::I64ShrS
                } else {
                    Operator::I64ShrU
                };
                let high = body.add_op(wb, shift_op, &[product, shift], &[Type::I64]);
                body.add_op(wb, Operator::I32WrapI64, &[high], &[Type::I32])
            }
            types::I64 => {
                let zero = body.add_op(wb, Operator::I64Const { value: 0 }, &[], &[Type::I64]);
                let (a_hi, b_hi) = if signed {
                    let shift =
                        body.add_op(wb, Operator::I64Const { value: 63 }, &[], &[Type::I64]);
                    (
                        body.add_op(wb, Operator::I64ShrS, &[a, shift], &[Type::I64]),
                        body.add_op(wb, Operator::I64ShrS, &[b, shift], &[Type::I64]),
                    )
                } else {
                    (zero, zero)
                };
                i128_lower::mul(body, wb, (a, a_hi), (b, b_hi)).1
            }
            _ => unreachable!(),
        };
        let dst_chunk = lane / lanes_per_chunk;
        let dst_lane = (lane % lanes_per_chunk) as u8;
        output[dst_chunk] = body.add_op(
            wb,
            replace_lane_op(lane_ty, dst_lane)?,
            &[output[dst_chunk], high],
            &[Type::V128],
        );
    }
    cx.bind_vector(result, normalize_vector(body, wb, ty, output)?);
    Ok(())
}

pub(super) fn lower_vector_shift(
    cx: &mut FnCx,
    body: &mut FunctionBody,
    wb: waffle::Block,
    result: ir::Value,
    ty: ir::Type,
    opcode: Opcode,
    args: [ir::Value; 2],
) -> Result<()> {
    let lane_ty = ty.lane_type();
    ensure!(
        matches!(lane_ty, types::I8 | types::I16 | types::I32 | types::I64),
        "{opcode} lane type {lane_ty} is unsupported"
    );
    let values = cx.vector(args[0])?;
    let amounts = cx.vector(args[1])?;
    ensure!(
        values.len() == amounts.len(),
        "vector shift chunk count mismatch"
    );
    let lane_count = ty.lane_count() as usize;
    let lanes_per_chunk = 128 / lane_ty.bits() as usize;
    let chunks = ty.bits().div_ceil(128) as usize;
    let scalar_ty = map_type(lane_ty)?;
    let width = lane_ty.bits();
    let mut output = (0..chunks)
        .map(|_| body.add_op(wb, Operator::V128Const { value: 0 }, &[], &[Type::V128]))
        .collect::<Vec<_>>();
    for lane in 0..lane_count {
        let chunk = lane / lanes_per_chunk;
        let index = (lane % lanes_per_chunk) as u8;
        let extract = extract_lane_op(lane_ty, index)?;
        let raw = body.add_op(wb, extract, &[values[chunk]], &[scalar_ty]);
        let amount = body.add_op(wb, extract, &[amounts[chunk]], &[scalar_ty]);
        let shift = if scalar_ty == Type::I64 {
            amount
        } else {
            let mask = body.add_op(
                wb,
                Operator::I32Const { value: width - 1 },
                &[],
                &[Type::I32],
            );
            body.add_op(wb, Operator::I32And, &[amount, mask], &[Type::I32])
        };
        let value = if opcode == Opcode::Sshr && matches!(lane_ty, types::I8 | types::I16) {
            sign_extend_narrow(body, wb, raw, lane_ty)
        } else {
            raw
        };
        let shifted = if matches!(opcode, Opcode::Rotl | Opcode::Rotr)
            && matches!(lane_ty, types::I8 | types::I16)
        {
            let width_value =
                body.add_op(wb, Operator::I32Const { value: width }, &[], &[Type::I32]);
            let inverse = body.add_op(wb, Operator::I32Sub, &[width_value, shift], &[Type::I32]);
            let (left_op, right_op) = if opcode == Opcode::Rotl {
                (Operator::I32Shl, Operator::I32ShrU)
            } else {
                (Operator::I32ShrU, Operator::I32Shl)
            };
            let left = body.add_op(wb, left_op, &[value, shift], &[Type::I32]);
            let right = body.add_op(wb, right_op, &[value, inverse], &[Type::I32]);
            let combined = body.add_op(wb, Operator::I32Or, &[left, right], &[Type::I32]);
            mask_narrow(body, wb, combined, lane_ty)
        } else {
            let op = match (opcode, scalar_ty) {
                (Opcode::Ishl, Type::I32) => Operator::I32Shl,
                (Opcode::Ishl, Type::I64) => Operator::I64Shl,
                (Opcode::Ushr, Type::I32) => Operator::I32ShrU,
                (Opcode::Ushr, Type::I64) => Operator::I64ShrU,
                (Opcode::Sshr, Type::I32) => Operator::I32ShrS,
                (Opcode::Sshr, Type::I64) => Operator::I64ShrS,
                (Opcode::Rotl, Type::I32) => Operator::I32Rotl,
                (Opcode::Rotl, Type::I64) => Operator::I64Rotl,
                (Opcode::Rotr, Type::I32) => Operator::I32Rotr,
                (Opcode::Rotr, Type::I64) => Operator::I64Rotr,
                _ => unsupported!("vector shift {opcode} on {scalar_ty} is unsupported"),
            };
            let shifted = body.add_op(wb, op, &[value, shift], &[scalar_ty]);
            if matches!(lane_ty, types::I8 | types::I16) {
                mask_narrow(body, wb, shifted, lane_ty)
            } else {
                shifted
            }
        };
        let dst_chunk = lane / lanes_per_chunk;
        let dst_lane = (lane % lanes_per_chunk) as u8;
        output[dst_chunk] = body.add_op(
            wb,
            replace_lane_op(lane_ty, dst_lane)?,
            &[output[dst_chunk], shifted],
            &[Type::V128],
        );
    }
    cx.bind_vector(result, normalize_vector(body, wb, ty, output)?);
    Ok(())
}

pub(super) fn lower_iadd_pairwise(
    cx: &mut FnCx,
    body: &mut FunctionBody,
    wb: waffle::Block,
    result: ir::Value,
    ty: ir::Type,
    args: [ir::Value; 2],
) -> Result<()> {
    let lane_ty = ty.lane_type();
    ensure!(
        matches!(lane_ty, types::I8 | types::I16 | types::I32 | types::I64),
        "iadd_pairwise lane type {lane_ty} is unsupported"
    );
    let lhs = cx.vector(args[0])?;
    let rhs = cx.vector(args[1])?;
    let lane_count = ty.lane_count() as usize;
    ensure!(
        lane_count.is_multiple_of(2),
        "iadd_pairwise requires an even lane count"
    );
    let lanes_per_chunk = 128 / lane_ty.bits() as usize;
    let scalar_ty = map_type(lane_ty)?;
    let chunks = (ty.bits().div_ceil(128)) as usize;
    let mut output = (0..chunks)
        .map(|_| body.add_op(wb, Operator::V128Const { value: 0 }, &[], &[Type::V128]))
        .collect::<Vec<_>>();
    for lane in 0..lane_count {
        let source = if lane < lane_count / 2 { &lhs } else { &rhs };
        let pair = (lane % (lane_count / 2)) * 2;
        let chunk = pair / lanes_per_chunk;
        let first_lane = (pair % lanes_per_chunk) as u8;
        let second_lane = first_lane + 1;
        let extract0 = extract_lane_op(lane_ty, first_lane)?;
        let extract1 = extract_lane_op(lane_ty, second_lane)?;
        let first = body.add_op(wb, extract0, &[source[chunk]], &[scalar_ty]);
        let second = body.add_op(wb, extract1, &[source[chunk]], &[scalar_ty]);
        let add = if scalar_ty == Type::I64 {
            Operator::I64Add
        } else {
            Operator::I32Add
        };
        let sum = body.add_op(wb, add, &[first, second], &[scalar_ty]);
        let dst_chunk = lane / lanes_per_chunk;
        let dst_lane = (lane % lanes_per_chunk) as u8;
        output[dst_chunk] = body.add_op(
            wb,
            replace_lane_op(lane_ty, dst_lane)?,
            &[output[dst_chunk], sum],
            &[Type::V128],
        );
    }
    cx.bind_vector(result, normalize_vector(body, wb, ty, output)?);
    Ok(())
}

pub(super) fn vector_int_compare(cond: IntCC, lane: ir::Type) -> Result<Operator> {
    use IntCC::*;
    Ok(match (lane, cond) {
        (types::I8, Equal) => Operator::I8x16Eq,
        (types::I8, NotEqual) => Operator::I8x16Ne,
        (types::I8, SignedLessThan) => Operator::I8x16LtS,
        (types::I8, UnsignedLessThan) => Operator::I8x16LtU,
        (types::I8, SignedLessThanOrEqual) => Operator::I8x16LeS,
        (types::I8, UnsignedLessThanOrEqual) => Operator::I8x16LeU,
        (types::I8, SignedGreaterThan) => Operator::I8x16GtS,
        (types::I8, UnsignedGreaterThan) => Operator::I8x16GtU,
        (types::I8, SignedGreaterThanOrEqual) => Operator::I8x16GeS,
        (types::I8, UnsignedGreaterThanOrEqual) => Operator::I8x16GeU,
        (types::I16, Equal) => Operator::I16x8Eq,
        (types::I16, NotEqual) => Operator::I16x8Ne,
        (types::I16, SignedLessThan) => Operator::I16x8LtS,
        (types::I16, UnsignedLessThan) => Operator::I16x8LtU,
        (types::I16, SignedLessThanOrEqual) => Operator::I16x8LeS,
        (types::I16, UnsignedLessThanOrEqual) => Operator::I16x8LeU,
        (types::I16, SignedGreaterThan) => Operator::I16x8GtS,
        (types::I16, UnsignedGreaterThan) => Operator::I16x8GtU,
        (types::I16, SignedGreaterThanOrEqual) => Operator::I16x8GeS,
        (types::I16, UnsignedGreaterThanOrEqual) => Operator::I16x8GeU,
        (types::I32, Equal) => Operator::I32x4Eq,
        (types::I32, NotEqual) => Operator::I32x4Ne,
        (types::I32, SignedLessThan) => Operator::I32x4LtS,
        (types::I32, UnsignedLessThan) => Operator::I32x4LtU,
        (types::I32, SignedLessThanOrEqual) => Operator::I32x4LeS,
        (types::I32, UnsignedLessThanOrEqual) => Operator::I32x4LeU,
        (types::I32, SignedGreaterThan) => Operator::I32x4GtS,
        (types::I32, UnsignedGreaterThan) => Operator::I32x4GtU,
        (types::I32, SignedGreaterThanOrEqual) => Operator::I32x4GeS,
        (types::I32, UnsignedGreaterThanOrEqual) => Operator::I32x4GeU,
        (types::I64, Equal) => Operator::I64x2Eq,
        (types::I64, NotEqual) => Operator::I64x2Ne,
        (types::I64, SignedLessThan) => Operator::I64x2LtS,
        (types::I64, SignedLessThanOrEqual) => Operator::I64x2LeS,
        (types::I64, SignedGreaterThan) => Operator::I64x2GtS,
        (types::I64, SignedGreaterThanOrEqual) => Operator::I64x2GeS,
        _ => unsupported!("vector icmp {cond} on lane type {lane} is unsupported"),
    })
}

pub(super) fn vector_float_compare(cond: FloatCC, lane: ir::Type) -> Result<Operator> {
    Ok(match (lane, cond) {
        (types::F32, FloatCC::Equal) => Operator::F32x4Eq,
        (types::F32, FloatCC::NotEqual) => Operator::F32x4Ne,
        (types::F32, FloatCC::LessThan) => Operator::F32x4Lt,
        (types::F32, FloatCC::LessThanOrEqual) => Operator::F32x4Le,
        (types::F32, FloatCC::GreaterThan) => Operator::F32x4Gt,
        (types::F32, FloatCC::GreaterThanOrEqual) => Operator::F32x4Ge,
        (types::F64, FloatCC::Equal) => Operator::F64x2Eq,
        (types::F64, FloatCC::NotEqual) => Operator::F64x2Ne,
        (types::F64, FloatCC::LessThan) => Operator::F64x2Lt,
        (types::F64, FloatCC::LessThanOrEqual) => Operator::F64x2Le,
        (types::F64, FloatCC::GreaterThan) => Operator::F64x2Gt,
        (types::F64, FloatCC::GreaterThanOrEqual) => Operator::F64x2Ge,
        _ => unsupported!("vector fcmp {cond} on lane type {lane} is unsupported"),
    })
}

pub(super) fn vector_float_compare_value(
    body: &mut FunctionBody,
    wb: waffle::Block,
    cond: FloatCC,
    lane: ir::Type,
    lhs: waffle::Value,
    rhs: waffle::Value,
) -> Result<waffle::Value> {
    let direct = |condition| vector_float_compare(condition, lane);
    let compare = |body: &mut FunctionBody, condition| -> Result<waffle::Value> {
        let op = direct(condition)?;
        Ok(body.add_op(wb, op, &[lhs, rhs], &[Type::V128]))
    };
    Ok(match cond {
        FloatCC::Equal
        | FloatCC::NotEqual
        | FloatCC::LessThan
        | FloatCC::LessThanOrEqual
        | FloatCC::GreaterThan
        | FloatCC::GreaterThanOrEqual => compare(body, cond)?,
        FloatCC::Ordered => {
            let op = direct(FloatCC::Equal)?;
            let lhs_ordered = body.add_op(wb, op, &[lhs, lhs], &[Type::V128]);
            let rhs_ordered = body.add_op(wb, op, &[rhs, rhs], &[Type::V128]);
            body.add_op(
                wb,
                Operator::V128And,
                &[lhs_ordered, rhs_ordered],
                &[Type::V128],
            )
        }
        FloatCC::Unordered => vector_unordered_mask(body, wb, lane, lhs, rhs)?,
        FloatCC::OrderedNotEqual => {
            let lt = compare(body, FloatCC::LessThan)?;
            let gt = compare(body, FloatCC::GreaterThan)?;
            body.add_op(wb, Operator::V128Or, &[lt, gt], &[Type::V128])
        }
        FloatCC::UnorderedOrEqual => {
            let lt = compare(body, FloatCC::LessThan)?;
            let gt = compare(body, FloatCC::GreaterThan)?;
            let ordered_ne = body.add_op(wb, Operator::V128Or, &[lt, gt], &[Type::V128]);
            body.add_op(wb, Operator::V128Not, &[ordered_ne], &[Type::V128])
        }
        FloatCC::UnorderedOrLessThan
        | FloatCC::UnorderedOrLessThanOrEqual
        | FloatCC::UnorderedOrGreaterThan
        | FloatCC::UnorderedOrGreaterThanOrEqual => {
            let relation = match cond {
                FloatCC::UnorderedOrLessThan => FloatCC::LessThan,
                FloatCC::UnorderedOrLessThanOrEqual => FloatCC::LessThanOrEqual,
                FloatCC::UnorderedOrGreaterThan => FloatCC::GreaterThan,
                FloatCC::UnorderedOrGreaterThanOrEqual => FloatCC::GreaterThanOrEqual,
                _ => unreachable!(),
            };
            let ordered = compare(body, relation)?;
            let nan = vector_unordered_mask(body, wb, lane, lhs, rhs)?;
            body.add_op(wb, Operator::V128Or, &[ordered, nan], &[Type::V128])
        }
    })
}

pub(super) fn vector_unordered_mask(
    body: &mut FunctionBody,
    wb: waffle::Block,
    lane: ir::Type,
    lhs: waffle::Value,
    rhs: waffle::Value,
) -> Result<waffle::Value> {
    let ne = vector_float_compare(FloatCC::NotEqual, lane)?;
    let lhs_nan = body.add_op(wb, ne, &[lhs, lhs], &[Type::V128]);
    let rhs_nan = body.add_op(wb, ne, &[rhs, rhs], &[Type::V128]);
    Ok(body.add_op(wb, Operator::V128Or, &[lhs_nan, rhs_nan], &[Type::V128]))
}

pub(super) fn vector_float_unary_operator(opcode: Opcode, lane: ir::Type) -> Result<Operator> {
    Ok(match (opcode, lane) {
        (Opcode::Fneg, types::F32) => Operator::F32x4Neg,
        (Opcode::Fabs, types::F32) => Operator::F32x4Abs,
        (Opcode::Sqrt, types::F32) => Operator::F32x4Sqrt,
        (Opcode::Ceil, types::F32) => Operator::F32x4Ceil,
        (Opcode::Floor, types::F32) => Operator::F32x4Floor,
        (Opcode::Trunc, types::F32) => Operator::F32x4Trunc,
        (Opcode::Nearest, types::F32) => Operator::F32x4Nearest,
        (Opcode::Fneg, types::F64) => Operator::F64x2Neg,
        (Opcode::Fabs, types::F64) => Operator::F64x2Abs,
        (Opcode::Sqrt, types::F64) => Operator::F64x2Sqrt,
        (Opcode::Ceil, types::F64) => Operator::F64x2Ceil,
        (Opcode::Floor, types::F64) => Operator::F64x2Floor,
        (Opcode::Trunc, types::F64) => Operator::F64x2Trunc,
        (Opcode::Nearest, types::F64) => Operator::F64x2Nearest,
        _ => unsupported!("vector float unary {opcode} on lane type {lane} is unsupported"),
    })
}
