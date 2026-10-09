use crate::error::Result;
use crate::{ensure, unsupported};
use cranelift_codegen::ir::{
    self, InstructionData, Opcode, condcodes::FloatCC, condcodes::IntCC, types,
};
use waffle::{FunctionBody, Operator, Type};

use super::*;
use crate::bridge::FnCx;
use crate::map_type;

pub(super) fn lower_icmp(
    cx: &mut FnCx,
    body: &mut FunctionBody,
    wb: waffle::Block,
    inst: ir::Inst,
) -> Result<()> {
    let dfg = &cx.clif.dfg;
    let InstructionData::IntCompare {
        opcode: Opcode::Icmp,
        args,
        cond,
    } = dfg.insts[inst]
    else {
        unreachable!("lower_icmp dispatched on a non-matching instruction")
    };
    let operand_clif_ty = cx.vty(args[0]);
    if operand_clif_ty.is_vector() {
        let result = dfg.first_result(inst);
        let result_ty = dfg.value_type(result);
        let lane_ty = operand_clif_ty.lane_type();
        let (lhs, rhs, compare_cond) = if lane_ty == types::I64
            && matches!(
                cond,
                IntCC::UnsignedLessThan
                    | IntCC::UnsignedLessThanOrEqual
                    | IntCC::UnsignedGreaterThan
                    | IntCC::UnsignedGreaterThanOrEqual
            ) {
            let signed_cond = match cond {
                IntCC::UnsignedLessThan => IntCC::SignedLessThan,
                IntCC::UnsignedLessThanOrEqual => IntCC::SignedLessThanOrEqual,
                IntCC::UnsignedGreaterThan => IntCC::SignedGreaterThan,
                IntCC::UnsignedGreaterThanOrEqual => IntCC::SignedGreaterThanOrEqual,
                _ => unreachable!(),
            };
            let sign = body.add_op(
                wb,
                Operator::V128Const {
                    value: (1u128 << 63) | (1u128 << 127),
                },
                &[],
                &[Type::V128],
            );
            let lhs = cx
                .vector(args[0])?
                .into_iter()
                .map(|value| body.add_op(wb, Operator::V128Xor, &[value, sign], &[Type::V128]))
                .collect();
            let rhs = cx
                .vector(args[1])?
                .into_iter()
                .map(|value| body.add_op(wb, Operator::V128Xor, &[value, sign], &[Type::V128]))
                .collect();
            (lhs, rhs, signed_cond)
        } else {
            (cx.vector(args[0])?, cx.vector(args[1])?, cond)
        };
        let op = vector_int_compare(compare_cond, lane_ty)?;
        ensure!(
            lhs.len() == rhs.len(),
            "vector compare chunk count mismatch"
        );
        let values = lhs
            .into_iter()
            .zip(rhs)
            .map(|(a, b)| body.add_op(wb, op, &[a, b], &[Type::V128]))
            .collect();
        cx.bind_vector(result, normalize_vector(body, wb, result_ty, values)?);
        return Ok(());
    }
    if operand_clif_ty == types::I128 {
        let a = cx.pair(args[0])?;
        let b = cx.pair(args[1])?;
        let wv = i128_lower::icmp(body, wb, cond, a, b)?;
        cx.bind1(dfg.first_result(inst), wv);
        return Ok(());
    }
    let operand_ty = map_type(operand_clif_ty)?;
    ensure!(
        matches!(operand_ty, Type::I32 | Type::I64),
        "icmp on unsupported operand type {operand_ty}"
    );
    let is64 = operand_ty == Type::I64;
    // Narrow operands: canonical form is zero-extended, so eq/ne/unsigned
    // compares are direct; signed compares sign-extend both sides first.
    let narrow = matches!(operand_clif_ty, types::I8 | types::I16);
    let signed_cc = matches!(
        cond,
        IntCC::SignedLessThan
            | IntCC::SignedLessThanOrEqual
            | IntCC::SignedGreaterThan
            | IntCC::SignedGreaterThanOrEqual
    );
    let (a0, b0) = (cx.one(args[0])?, cx.one(args[1])?);
    let (a0, b0) = if narrow {
        let a0 = mask_narrow(body, wb, a0, operand_clif_ty);
        let b0 = mask_narrow(body, wb, b0, operand_clif_ty);
        if signed_cc {
            (
                sign_extend_narrow(body, wb, a0, operand_clif_ty),
                sign_extend_narrow(body, wb, b0, operand_clif_ty),
            )
        } else {
            (a0, b0)
        }
    } else {
        (a0, b0)
    };
    let op = match cond {
        IntCC::Equal => {
            if is64 {
                Operator::I64Eq
            } else {
                Operator::I32Eq
            }
        }
        IntCC::NotEqual => {
            if is64 {
                Operator::I64Ne
            } else {
                Operator::I32Ne
            }
        }
        IntCC::SignedLessThan => {
            if is64 {
                Operator::I64LtS
            } else {
                Operator::I32LtS
            }
        }
        IntCC::UnsignedLessThan => {
            if is64 {
                Operator::I64LtU
            } else {
                Operator::I32LtU
            }
        }
        IntCC::SignedLessThanOrEqual => {
            if is64 {
                Operator::I64LeS
            } else {
                Operator::I32LeS
            }
        }
        IntCC::UnsignedLessThanOrEqual => {
            if is64 {
                Operator::I64LeU
            } else {
                Operator::I32LeU
            }
        }
        IntCC::SignedGreaterThan => {
            if is64 {
                Operator::I64GtS
            } else {
                Operator::I32GtS
            }
        }
        IntCC::UnsignedGreaterThan => {
            if is64 {
                Operator::I64GtU
            } else {
                Operator::I32GtU
            }
        }
        IntCC::SignedGreaterThanOrEqual => {
            if is64 {
                Operator::I64GeS
            } else {
                Operator::I32GeS
            }
        }
        IntCC::UnsignedGreaterThanOrEqual => {
            if is64 {
                Operator::I64GeU
            } else {
                Operator::I32GeU
            }
        }
    };
    // wasm comparisons produce i32; CLIF's i8 result folds to I32 in map_type.
    let wv = body.add_op(wb, op, &[a0, b0], &[Type::I32]);
    cx.bind1(dfg.first_result(inst), wv);
    Ok(())
}

pub(super) fn lower_fcmp(
    cx: &mut FnCx,
    body: &mut FunctionBody,
    wb: waffle::Block,
    inst: ir::Inst,
) -> Result<()> {
    let dfg = &cx.clif.dfg;
    let InstructionData::FloatCompare {
        opcode: Opcode::Fcmp,
        args,
        cond,
    } = dfg.insts[inst]
    else {
        unreachable!("lower_fcmp dispatched on a non-matching instruction")
    };
    let operand_ty = cx.vty(args[0]);
    if operand_ty.is_vector() {
        let result = dfg.first_result(inst);
        let result_ty = dfg.value_type(result);
        let lane_ty = operand_ty.lane_type();
        let lhs = cx.vector(args[0])?;
        let rhs = cx.vector(args[1])?;
        ensure!(
            lhs.len() == rhs.len(),
            "vector compare chunk count mismatch"
        );
        let values = lhs
            .into_iter()
            .zip(rhs)
            .map(|(a, b)| vector_float_compare_value(body, wb, cond, lane_ty, a, b))
            .collect::<Result<Vec<_>>>()?;
        cx.bind_vector(result, normalize_vector(body, wb, result_ty, values)?);
        return Ok(());
    }
    let is64 = map_type(cx.vty(args[0]))? == Type::F64;
    let a = cx.one(args[0])?;
    let b = cx.one(args[1])?;
    // Direct wasm comparisons (all "ordered": false on NaN except Ne).
    let direct = |c: FloatCC| -> Option<Operator> {
        Some(match (c, is64) {
            (FloatCC::Equal, true) => Operator::F64Eq,
            (FloatCC::Equal, false) => Operator::F32Eq,
            (FloatCC::NotEqual, true) => Operator::F64Ne, // unordered-or-ne == CLIF NotEqual
            (FloatCC::NotEqual, false) => Operator::F32Ne,
            (FloatCC::LessThan, true) => Operator::F64Lt,
            (FloatCC::LessThan, false) => Operator::F32Lt,
            (FloatCC::LessThanOrEqual, true) => Operator::F64Le,
            (FloatCC::LessThanOrEqual, false) => Operator::F32Le,
            (FloatCC::GreaterThan, true) => Operator::F64Gt,
            (FloatCC::GreaterThan, false) => Operator::F32Gt,
            (FloatCC::GreaterThanOrEqual, true) => Operator::F64Ge,
            (FloatCC::GreaterThanOrEqual, false) => Operator::F32Ge,
            _ => return None,
        })
    };
    let wv = if let Some(op) = direct(cond) {
        body.add_op(wb, op, &[a, b], &[Type::I32])
    } else {
        // Unordered family: derive from the negation of the ordered dual
        // (wasm ordered compares are false on NaN, so !ge == unordered|lt).
        let negated_dual = |c: FloatCC| -> Result<FloatCC> {
            Ok(match c {
                FloatCC::UnorderedOrLessThan => FloatCC::GreaterThanOrEqual,
                FloatCC::UnorderedOrLessThanOrEqual => FloatCC::GreaterThan,
                FloatCC::UnorderedOrGreaterThan => FloatCC::LessThanOrEqual,
                FloatCC::UnorderedOrGreaterThanOrEqual => FloatCC::LessThan,
                other => unsupported!("unimplemented fcmp condition {other}"),
            })
        };
        match cond {
            FloatCC::Ordered => {
                // a==a && b==b
                let eq_op = if is64 {
                    Operator::F64Eq
                } else {
                    Operator::F32Eq
                };
                let aa = body.add_op(wb, eq_op, &[a, a], &[Type::I32]);
                let bb = body.add_op(wb, eq_op, &[b, b], &[Type::I32]);
                body.add_op(wb, Operator::I32And, &[aa, bb], &[Type::I32])
            }
            FloatCC::Unordered => {
                let ne_op = if is64 {
                    Operator::F64Ne
                } else {
                    Operator::F32Ne
                };
                let aa = body.add_op(wb, ne_op, &[a, a], &[Type::I32]);
                let bb = body.add_op(wb, ne_op, &[b, b], &[Type::I32]);
                body.add_op(wb, Operator::I32Or, &[aa, bb], &[Type::I32])
            }
            FloatCC::OrderedNotEqual => {
                // lt | gt (ordered, excludes NaN and equality)
                let lt = body.add_op(
                    wb,
                    if is64 {
                        Operator::F64Lt
                    } else {
                        Operator::F32Lt
                    },
                    &[a, b],
                    &[Type::I32],
                );
                let gt = body.add_op(
                    wb,
                    if is64 {
                        Operator::F64Gt
                    } else {
                        Operator::F32Gt
                    },
                    &[a, b],
                    &[Type::I32],
                );
                body.add_op(wb, Operator::I32Or, &[lt, gt], &[Type::I32])
            }
            FloatCC::UnorderedOrEqual => {
                // !(lt | gt)
                let lt = body.add_op(
                    wb,
                    if is64 {
                        Operator::F64Lt
                    } else {
                        Operator::F32Lt
                    },
                    &[a, b],
                    &[Type::I32],
                );
                let gt = body.add_op(
                    wb,
                    if is64 {
                        Operator::F64Gt
                    } else {
                        Operator::F32Gt
                    },
                    &[a, b],
                    &[Type::I32],
                );
                let or = body.add_op(wb, Operator::I32Or, &[lt, gt], &[Type::I32]);
                body.add_op(wb, Operator::I32Eqz, &[or], &[Type::I32])
            }
            other => {
                let dual = direct(negated_dual(other)?)
                    .expect("negated dual is always a direct comparison");
                let d = body.add_op(wb, dual, &[a, b], &[Type::I32]);
                body.add_op(wb, Operator::I32Eqz, &[d], &[Type::I32])
            }
        }
    };
    cx.bind1(dfg.first_result(inst), wv);
    Ok(())
}
