use crate::waffle as waffle;
use crate::error::Result;
use crate::unsupported;
use cranelift_codegen::ir::{self, Opcode, condcodes::IntCC, types};
use waffle::{FunctionBody, Operator, Type};

use super::*;
use crate::bridge::FnCx;
use crate::i128_lower::{self, ShiftKind};
use crate::map_type;

pub(super) fn lower_float_to_i128(
    body: &mut FunctionBody,
    wb: waffle::Block,
    value: waffle::Value,
    from_f32: bool,
    signed: bool,
) -> Result<(waffle::Value, waffle::Value)> {
    let value = if from_f32 {
        body.add_op(wb, Operator::F64PromoteF32, &[value], &[Type::F64])
    } else {
        value
    };
    let zero_f = body.add_op(
        wb,
        Operator::F64Const {
            value: 0.0f64.to_bits(),
        },
        &[],
        &[Type::F64],
    );
    let nan = body.add_op(wb, Operator::F64Ne, &[value, value], &[Type::I32]);
    let lower_bound = body.add_op(
        wb,
        Operator::F64Const {
            value: (-2f64.powi(127)).to_bits(),
        },
        &[],
        &[Type::F64],
    );
    let upper_bound = body.add_op(
        wb,
        Operator::F64Const {
            value: (2f64.powi(if signed { 127 } else { 128 })).to_bits(),
        },
        &[],
        &[Type::F64],
    );
    let below = if signed {
        body.add_op(wb, Operator::F64Lt, &[value, lower_bound], &[Type::I32])
    } else {
        body.add_op(wb, Operator::F64Le, &[value, zero_f], &[Type::I32])
    };
    let above = body.add_op(wb, Operator::F64Ge, &[value, upper_bound], &[Type::I32]);
    let negative = body.add_op(wb, Operator::F64Lt, &[value, zero_f], &[Type::I32]);
    let abs = body.add_op(wb, Operator::F64Abs, &[value], &[Type::F64]);
    let magnitude = if signed {
        body.add_op(wb, Operator::Select, &[abs, value, negative], &[Type::F64])
    } else {
        value
    };
    let inv_scale = body.add_op(
        wb,
        Operator::F64Const {
            value: (2f64.powi(-64)).to_bits(),
        },
        &[],
        &[Type::F64],
    );
    let high_float = body.add_op(wb, Operator::F64Mul, &[magnitude, inv_scale], &[Type::F64]);
    let high_float = body.add_op(wb, Operator::F64Trunc, &[high_float], &[Type::F64]);
    let high = body.add_op(wb, Operator::I64TruncSatF64U, &[high_float], &[Type::I64]);
    let high_back = body.add_op(wb, Operator::F64ConvertI64U, &[high], &[Type::F64]);
    let scale = body.add_op(
        wb,
        Operator::F64Const {
            value: (2f64.powi(64)).to_bits(),
        },
        &[],
        &[Type::F64],
    );
    let high_scaled = body.add_op(wb, Operator::F64Mul, &[high_back, scale], &[Type::F64]);
    let low_float = body.add_op(
        wb,
        Operator::F64Sub,
        &[magnitude, high_scaled],
        &[Type::F64],
    );
    let low_float = body.add_op(wb, Operator::F64Trunc, &[low_float], &[Type::F64]);
    let low = body.add_op(wb, Operator::I64TruncSatF64U, &[low_float], &[Type::I64]);
    let mut result = (low, high);
    if signed {
        let zero = body.add_op(wb, Operator::I64Const { value: 0 }, &[], &[Type::I64]);
        let negated = i128_lower::sub(body, wb, (zero, zero), result);
        result = (
            body.add_op(
                wb,
                Operator::Select,
                &[negated.0, result.0, negative],
                &[Type::I64],
            ),
            body.add_op(
                wb,
                Operator::Select,
                &[negated.1, result.1, negative],
                &[Type::I64],
            ),
        );
    }
    let zero = body.add_op(wb, Operator::I64Const { value: 0 }, &[], &[Type::I64]);
    let max = (
        body.add_op(
            wb,
            Operator::I64Const { value: u64::MAX },
            &[],
            &[Type::I64],
        ),
        body.add_op(
            wb,
            Operator::I64Const {
                value: i64::MAX as u64,
            },
            &[],
            &[Type::I64],
        ),
    );
    let min = (
        zero,
        body.add_op(
            wb,
            Operator::I64Const {
                value: i64::MIN as u64,
            },
            &[],
            &[Type::I64],
        ),
    );
    let all_ones = (
        body.add_op(
            wb,
            Operator::I64Const { value: u64::MAX },
            &[],
            &[Type::I64],
        ),
        body.add_op(
            wb,
            Operator::I64Const { value: u64::MAX },
            &[],
            &[Type::I64],
        ),
    );
    let high_clamped = if signed { max } else { all_ones };
    result = (
        body.add_op(
            wb,
            Operator::Select,
            &[high_clamped.0, result.0, above],
            &[Type::I64],
        ),
        body.add_op(
            wb,
            Operator::Select,
            &[high_clamped.1, result.1, above],
            &[Type::I64],
        ),
    );
    if signed {
        result = (
            body.add_op(
                wb,
                Operator::Select,
                &[min.0, result.0, below],
                &[Type::I64],
            ),
            body.add_op(
                wb,
                Operator::Select,
                &[min.1, result.1, below],
                &[Type::I64],
            ),
        );
    }
    let clear = body.add_op(wb, Operator::I32Or, &[below, nan], &[Type::I32]);
    let clear = if signed {
        nan
    } else {
        body.add_op(wb, Operator::I32Or, &[clear, negative], &[Type::I32])
    };
    result = (
        body.add_op(wb, Operator::Select, &[zero, result.0, clear], &[Type::I64]),
        body.add_op(wb, Operator::Select, &[zero, result.1, clear], &[Type::I64]),
    );
    Ok(result)
}

pub(super) fn lower_i128_to_float(
    body: &mut FunctionBody,
    wb: waffle::Block,
    value: (waffle::Value, waffle::Value),
    signed: bool,
    to_f32: bool,
) -> Result<waffle::Value> {
    let zero = body.add_op(wb, Operator::I64Const { value: 0 }, &[], &[Type::I64]);
    let zero32 = body.add_op(wb, Operator::I32Const { value: 0 }, &[], &[Type::I32]);
    let one = body.add_op(wb, Operator::I64Const { value: 1 }, &[], &[Type::I64]);
    let negative = if signed {
        body.add_op(wb, Operator::I64LtS, &[value.1, zero], &[Type::I32])
    } else {
        body.add_op(wb, Operator::I32Const { value: 0 }, &[], &[Type::I32])
    };
    let magnitude = if signed {
        let negated = i128_lower::sub(body, wb, (zero, zero), value);
        (
            body.add_op(
                wb,
                Operator::Select,
                &[negated.0, value.0, negative],
                &[Type::I64],
            ),
            body.add_op(
                wb,
                Operator::Select,
                &[negated.1, value.1, negative],
                &[Type::I64],
            ),
        )
    } else {
        value
    };
    let precision = if to_f32 { 24u32 } else { 53 };
    let mantissa_bits = precision - 1;
    let clz_hi = body.add_op(wb, Operator::I64Clz, &[magnitude.1], &[Type::I64]);
    let clz_lo = body.add_op(wb, Operator::I64Clz, &[magnitude.0], &[Type::I64]);
    let c127 = body.add_op(wb, Operator::I64Const { value: 127 }, &[], &[Type::I64]);
    let c63 = body.add_op(wb, Operator::I64Const { value: 63 }, &[], &[Type::I64]);
    let high_exp = body.add_op(wb, Operator::I64Sub, &[c127, clz_hi], &[Type::I64]);
    let low_exp = body.add_op(wb, Operator::I64Sub, &[c63, clz_lo], &[Type::I64]);
    let hi_zero = body.add_op(wb, Operator::I64Eqz, &[magnitude.1], &[Type::I32]);
    let exponent = body.add_op(
        wb,
        Operator::Select,
        &[low_exp, high_exp, hi_zero],
        &[Type::I64],
    );
    let precision_minus_one = body.add_op(
        wb,
        Operator::I64Const {
            value: mantissa_bits as u64,
        },
        &[],
        &[Type::I64],
    );
    let shift_raw = body.add_op(
        wb,
        Operator::I64Sub,
        &[exponent, precision_minus_one],
        &[Type::I64],
    );
    let needs_shift = body.add_op(
        wb,
        Operator::I64GeS,
        &[exponent, precision_minus_one],
        &[Type::I32],
    );
    let shift = body.add_op(
        wb,
        Operator::Select,
        &[shift_raw, zero, needs_shift],
        &[Type::I64],
    );
    let shifted = i128_lower::shift(body, wb, ShiftKind::UShr, magnitude, shift)?;
    let sig = shifted.0;
    let shift_zero = body.add_op(wb, Operator::I64Eqz, &[shift], &[Type::I32]);
    let guard_raw = body.add_op(wb, Operator::I64Sub, &[shift, one], &[Type::I64]);
    let guard_shift = body.add_op(
        wb,
        Operator::Select,
        &[zero, guard_raw, shift_zero],
        &[Type::I64],
    );
    let guard_pair = i128_lower::shift(body, wb, ShiftKind::UShr, magnitude, guard_shift)?;
    let guard_bit = body.add_op(wb, Operator::I64And, &[guard_pair.0, one], &[Type::I64]);
    let guard = body.add_op(wb, Operator::I32WrapI64, &[guard_bit], &[Type::I32]);
    let guard = body.add_op(
        wb,
        Operator::Select,
        &[zero32, guard, shift_zero],
        &[Type::I32],
    );
    let one_pair = (one, zero);
    let half_bit = i128_lower::shift(body, wb, ShiftKind::Shl, one_pair, guard_shift)?;
    let mask = i128_lower::sub(body, wb, half_bit, one_pair);
    let discarded = i128_lower::logic(body, wb, Operator::I64And, magnitude, mask);
    let discarded_any = body.add_op(
        wb,
        Operator::I64Or,
        &[discarded.0, discarded.1],
        &[Type::I64],
    );
    let sticky = body.add_op(wb, Operator::I64Ne, &[discarded_any, zero], &[Type::I32]);
    let odd_bits = body.add_op(wb, Operator::I64And, &[sig, one], &[Type::I64]);
    let odd = body.add_op(wb, Operator::I64Ne, &[odd_bits, zero], &[Type::I32]);
    let sticky_or_odd = body.add_op(wb, Operator::I32Or, &[sticky, odd], &[Type::I32]);
    let round_up = body.add_op(wb, Operator::I32And, &[guard, sticky_or_odd], &[Type::I32]);
    let round64 = body.add_op(wb, Operator::I64ExtendI32U, &[round_up], &[Type::I64]);
    let rounded_sig = body.add_op(wb, Operator::I64Add, &[sig, round64], &[Type::I64]);
    let limit = body.add_op(
        wb,
        Operator::I64Const {
            value: 1u64 << precision,
        },
        &[],
        &[Type::I64],
    );
    let rollover = body.add_op(wb, Operator::I64GeU, &[rounded_sig, limit], &[Type::I32]);
    let one_shift = body.add_op(wb, Operator::I64ShrU, &[rounded_sig, one], &[Type::I64]);
    let significand = body.add_op(
        wb,
        Operator::Select,
        &[one_shift, rounded_sig, rollover],
        &[Type::I64],
    );
    let exponent_inc = body.add_op(wb, Operator::I64Add, &[exponent, one], &[Type::I64]);
    let exponent = body.add_op(
        wb,
        Operator::Select,
        &[exponent_inc, exponent, rollover],
        &[Type::I64],
    );
    let normalized = body.add_op(
        wb,
        Operator::I64GeS,
        &[exponent, precision_minus_one],
        &[Type::I32],
    );
    let base = body.add_op(
        wb,
        Operator::I64Const {
            value: 1u64 << mantissa_bits,
        },
        &[],
        &[Type::I64],
    );
    let norm_fraction = body.add_op(wb, Operator::I64Sub, &[significand, base], &[Type::I64]);
    let sig_clz = body.add_op(wb, Operator::I64Clz, &[significand], &[Type::I64]);
    let sig_exp = body.add_op(wb, Operator::I64Sub, &[c63, sig_clz], &[Type::I64]);
    let small_base = body.add_op(wb, Operator::I64Shl, &[one, sig_exp], &[Type::I64]);
    let small_fraction = body.add_op(
        wb,
        Operator::I64Sub,
        &[significand, small_base],
        &[Type::I64],
    );
    let mantissa_width = body.add_op(
        wb,
        Operator::I64Const {
            value: (if to_f32 { 23 } else { 52 }) as u64,
        },
        &[],
        &[Type::I64],
    );
    let small_shift = body.add_op(
        wb,
        Operator::I64Sub,
        &[mantissa_width, sig_exp],
        &[Type::I64],
    );
    let small_fraction = body.add_op(
        wb,
        Operator::I64Shl,
        &[small_fraction, small_shift],
        &[Type::I64],
    );
    let fraction = body.add_op(
        wb,
        Operator::Select,
        &[norm_fraction, small_fraction, normalized],
        &[Type::I64],
    );
    let output_exp = body.add_op(
        wb,
        Operator::Select,
        &[exponent, sig_exp, normalized],
        &[Type::I64],
    );
    let bias = body.add_op(
        wb,
        Operator::I64Const {
            value: (if to_f32 { 127 } else { 1023 }) as u64,
        },
        &[],
        &[Type::I64],
    );
    let biased = body.add_op(wb, Operator::I64Add, &[output_exp, bias], &[Type::I64]);
    let exp_shift = body.add_op(
        wb,
        Operator::I64Const {
            value: (if to_f32 { 23 } else { 52 }) as u64,
        },
        &[],
        &[Type::I64],
    );
    let exp_bits = body.add_op(wb, Operator::I64Shl, &[biased, exp_shift], &[Type::I64]);
    let bits = body.add_op(wb, Operator::I64Or, &[exp_bits, fraction], &[Type::I64]);
    let sign_bit = body.add_op(
        wb,
        Operator::I64Const {
            value: if to_f32 { 1u64 << 31 } else { 1u64 << 63 },
        },
        &[],
        &[Type::I64],
    );
    let sign = body.add_op(
        wb,
        Operator::Select,
        &[sign_bit, zero, negative],
        &[Type::I64],
    );
    let bits = body.add_op(wb, Operator::I64Or, &[bits, sign], &[Type::I64]);
    let mag_or = body.add_op(
        wb,
        Operator::I64Or,
        &[magnitude.0, magnitude.1],
        &[Type::I64],
    );
    let is_zero = body.add_op(wb, Operator::I64Eqz, &[mag_or], &[Type::I32]);
    let bits = body.add_op(wb, Operator::Select, &[zero, bits, is_zero], &[Type::I64]);
    if to_f32 {
        let bits = body.add_op(wb, Operator::I32WrapI64, &[bits], &[Type::I32]);
        Ok(body.add_op(wb, Operator::F32ReinterpretI32, &[bits], &[Type::F32]))
    } else {
        Ok(body.add_op(wb, Operator::F64ReinterpretI64, &[bits], &[Type::F64]))
    }
}

pub(super) fn lower_binary_i128(
    cx: &mut FnCx,
    body: &mut FunctionBody,
    wb: waffle::Block,
    result: ir::Value,
    opcode: Opcode,
    args: [ir::Value; 2],
) -> Result<()> {
    match opcode {
        // iconcat lo, hi -> i128 (first operand is the LOW half).
        Opcode::Iconcat => {
            let lo = cx.one(args[0])?;
            let hi = cx.one(args[1])?;
            cx.bind2(result, lo, hi);
        }
        Opcode::Iadd => {
            let (a, b) = (cx.pair(args[0])?, cx.pair(args[1])?);
            let (lo, hi) = i128_lower::add(body, wb, a, b);
            cx.bind2(result, lo, hi);
        }
        Opcode::Isub => {
            let (a, b) = (cx.pair(args[0])?, cx.pair(args[1])?);
            let (lo, hi) = i128_lower::sub(body, wb, a, b);
            cx.bind2(result, lo, hi);
        }
        Opcode::Imul => {
            let (a, b) = (cx.pair(args[0])?, cx.pair(args[1])?);
            let (lo, hi) = i128_lower::mul(body, wb, a, b);
            cx.bind2(result, lo, hi);
        }
        Opcode::Smulhi | Opcode::Umulhi => {
            let (a, b) = (cx.pair(args[0])?, cx.pair(args[1])?);
            let value = i128_lower::mulhi(body, wb, a, b, opcode == Opcode::Smulhi);
            cx.bind2(result, value.0, value.1);
        }
        Opcode::Udiv | Opcode::Urem => {
            let (a, b) = (cx.pair(args[0])?, cx.pair(args[1])?);
            let (q, r) = i128_lower::divrem_u(body, wb, a, b);
            let value = if opcode == Opcode::Udiv { q } else { r };
            cx.bind2(result, value.0, value.1);
        }
        Opcode::Sdiv | Opcode::Srem => {
            let (a, b) = (cx.pair(args[0])?, cx.pair(args[1])?);
            let (q, r) = i128_lower::divrem_s(body, wb, a, b)?;
            let value = if opcode == Opcode::Sdiv { q } else { r };
            cx.bind2(result, value.0, value.1);
        }
        Opcode::Smin | Opcode::Umin | Opcode::Smax | Opcode::Umax => {
            let (a, b) = (cx.pair(args[0])?, cx.pair(args[1])?);
            let cond = match opcode {
                Opcode::Smin => IntCC::SignedLessThan,
                Opcode::Umin => IntCC::UnsignedLessThan,
                Opcode::Smax => IntCC::SignedGreaterThan,
                Opcode::Umax => IntCC::UnsignedGreaterThan,
                _ => unreachable!(),
            };
            let choose_a = i128_lower::icmp(body, wb, cond, a, b)?;
            let lo = body.add_op(wb, Operator::Select, &[a.0, b.0, choose_a], &[Type::I64]);
            let hi = body.add_op(wb, Operator::Select, &[a.1, b.1, choose_a], &[Type::I64]);
            cx.bind2(result, lo, hi);
        }
        Opcode::Band | Opcode::Bor | Opcode::Bxor => {
            let op = match opcode {
                Opcode::Band => Operator::I64And,
                Opcode::Bor => Operator::I64Or,
                _ => Operator::I64Xor,
            };
            let (a, b) = (cx.pair(args[0])?, cx.pair(args[1])?);
            let (lo, hi) = i128_lower::logic(body, wb, op, a, b);
            cx.bind2(result, lo, hi);
        }
        Opcode::Ishl | Opcode::Ushr | Opcode::Sshr | Opcode::Rotl | Opcode::Rotr => {
            let v = cx.pair(args[0])?;
            // Coerce the shift amount to i64 (CLIF allows any int width; i128 uses lo).
            let amt_ty = cx.vty(args[1]);
            let amt = if amt_ty == types::I128 {
                cx.pair(args[1])?.0
            } else {
                let raw = cx.one(args[1])?;
                if map_type(amt_ty)? == Type::I32 {
                    body.add_op(wb, Operator::I64ExtendI32U, &[raw], &[Type::I64])
                } else {
                    raw
                }
            };
            if matches!(opcode, Opcode::Rotl | Opcode::Rotr) {
                // rot(v, s) = shl(v, s') | ushr(v, 128 - s') with mod-128 masking on
                // both shifts (s'=0 makes both sides the identity: v | v = v).
                let c128 = body.add_op(wb, Operator::I64Const { value: 128 }, &[], &[Type::I64]);
                let inv = body.add_op(wb, Operator::I64Sub, &[c128, amt], &[Type::I64]);
                let (l_amt, r_amt) = if opcode == Opcode::Rotl {
                    (amt, inv)
                } else {
                    (inv, amt)
                };
                let (llo, lhi) = i128_lower::shift(body, wb, ShiftKind::Shl, v, l_amt)?;
                let (rlo, rhi) = i128_lower::shift(body, wb, ShiftKind::UShr, v, r_amt)?;
                let (lo, hi) = i128_lower::logic(body, wb, Operator::I64Or, (llo, lhi), (rlo, rhi));
                cx.bind2(result, lo, hi);
                return Ok(());
            }
            let kind = ShiftKind::from_opcode(opcode)?;
            let (lo, hi) = i128_lower::shift(body, wb, kind, v, amt)?;
            cx.bind2(result, lo, hi);
        }
        other => {
            unsupported!("i128 binary opcode {other} is unsupported")
        }
    }
    Ok(())
}

pub(super) fn lower_i128_overflow(
    cx: &mut FnCx,
    body: &mut FunctionBody,
    wb: waffle::Block,
    inst: ir::Inst,
    opcode: Opcode,
    args: [ir::Value; 2],
) -> Result<()> {
    let (a, b) = (cx.pair(args[0])?, cx.pair(args[1])?);
    let (value, overflow) = match opcode {
        Opcode::UaddOverflow | Opcode::SaddOverflow => {
            let (lo, hi) = i128_lower::add(body, wb, a, b);
            let flag = if opcode == Opcode::UaddOverflow {
                let hi0 = body.add_op(wb, Operator::I64Add, &[a.1, b.1], &[Type::I64]);
                let hi_wrap = body.add_op(wb, Operator::I64LtU, &[hi0, a.1], &[Type::I32]);
                let carry = body.add_op(wb, Operator::I64LtU, &[lo, a.0], &[Type::I32]);
                let carry64 = body.add_op(wb, Operator::I64ExtendI32U, &[carry], &[Type::I64]);
                let high = body.add_op(wb, Operator::I64Add, &[hi0, carry64], &[Type::I64]);
                let carry_wrap = body.add_op(wb, Operator::I64LtU, &[high, hi0], &[Type::I32]);
                body.add_op(wb, Operator::I32Or, &[hi_wrap, carry_wrap], &[Type::I32])
            } else {
                let zero = body.add_op(wb, Operator::I64Const { value: 0 }, &[], &[Type::I64]);
                let sa = body.add_op(wb, Operator::I64LtS, &[a.1, zero], &[Type::I32]);
                let sb = body.add_op(wb, Operator::I64LtS, &[b.1, zero], &[Type::I32]);
                let sr = body.add_op(wb, Operator::I64LtS, &[hi, zero], &[Type::I32]);
                let different = body.add_op(wb, Operator::I32Xor, &[sa, sb], &[Type::I32]);
                let changed = body.add_op(wb, Operator::I32Xor, &[sa, sr], &[Type::I32]);
                let same_inputs = body.add_op(wb, Operator::I32Eqz, &[different], &[Type::I32]);
                body.add_op(wb, Operator::I32And, &[same_inputs, changed], &[Type::I32])
            };
            ((lo, hi), flag)
        }
        Opcode::UsubOverflow | Opcode::SsubOverflow => {
            let (lo, hi) = i128_lower::sub(body, wb, a, b);
            let flag = if opcode == Opcode::UsubOverflow {
                i128_lower::icmp(body, wb, IntCC::UnsignedLessThan, a, b)?
            } else {
                let zero = body.add_op(wb, Operator::I64Const { value: 0 }, &[], &[Type::I64]);
                let sa = body.add_op(wb, Operator::I64LtS, &[a.1, zero], &[Type::I32]);
                let sb = body.add_op(wb, Operator::I64LtS, &[b.1, zero], &[Type::I32]);
                let sr = body.add_op(wb, Operator::I64LtS, &[hi, zero], &[Type::I32]);
                let different = body.add_op(wb, Operator::I32Xor, &[sa, sb], &[Type::I32]);
                let changed = body.add_op(wb, Operator::I32Xor, &[sa, sr], &[Type::I32]);
                body.add_op(wb, Operator::I32And, &[different, changed], &[Type::I32])
            };
            ((lo, hi), flag)
        }
        _ => unreachable!(),
    };
    let results = cx.clif.dfg.inst_results(inst).to_vec();
    cx.bind2(results[0], value.0, value.1);
    cx.bind1(results[1], overflow);
    Ok(())
}

pub(super) fn lower_i128_carry(
    cx: &mut FnCx,
    body: &mut FunctionBody,
    wb: waffle::Block,
    inst: ir::Inst,
    opcode: Opcode,
    args: [ir::Value; 3],
) -> Result<()> {
    let a = cx.pair(args[0])?;
    let b = cx.pair(args[1])?;
    let input = coerce_cond(cx, body, wb, args[2])?;
    let is_zero = body.add_op(wb, Operator::I32Eqz, &[input], &[Type::I32]);
    let carry = body.add_op(wb, Operator::I32Eqz, &[is_zero], &[Type::I32]);
    let zero64 = body.add_op(wb, Operator::I64Const { value: 0 }, &[], &[Type::I64]);
    let carry64 = body.add_op(wb, Operator::I64ExtendI32U, &[carry], &[Type::I64]);
    let unit = (carry64, zero64);
    let is_add = matches!(opcode, Opcode::UaddOverflowCin | Opcode::SaddOverflowCin);
    let signed = matches!(opcode, Opcode::SaddOverflowCin | Opcode::SsubOverflowBin);
    let first = if is_add {
        i128_lower::add(body, wb, a, b)
    } else {
        i128_lower::sub(body, wb, a, b)
    };
    let value = if is_add {
        i128_lower::add(body, wb, first, unit)
    } else {
        i128_lower::sub(body, wb, first, unit)
    };
    let of1 = if signed {
        signed_overflow_flag(body, wb, a, b, first, is_add)
    } else if is_add {
        unsigned_add_overflow_flag(body, wb, a, b, first)
    } else {
        i128_lower::icmp(body, wb, IntCC::UnsignedLessThan, a, b)?
    };
    let of2 = if signed {
        signed_overflow_flag(body, wb, first, unit, value, is_add)
    } else if is_add {
        unsigned_add_overflow_flag(body, wb, first, unit, value)
    } else {
        i128_lower::icmp(body, wb, IntCC::UnsignedLessThan, first, unit)?
    };
    let overflow = body.add_op(wb, Operator::I32Or, &[of1, of2], &[Type::I32]);
    let results = cx.clif.dfg.inst_results(inst).to_vec();
    cx.bind2(results[0], value.0, value.1);
    cx.bind1(results[1], overflow);
    Ok(())
}

pub(super) fn signed_overflow_flag(
    body: &mut FunctionBody,
    wb: waffle::Block,
    a: (waffle::Value, waffle::Value),
    b: (waffle::Value, waffle::Value),
    result: (waffle::Value, waffle::Value),
    add: bool,
) -> waffle::Value {
    let zero = body.add_op(wb, Operator::I64Const { value: 0 }, &[], &[Type::I64]);
    let sa = body.add_op(wb, Operator::I64LtS, &[a.1, zero], &[Type::I32]);
    let sb = body.add_op(wb, Operator::I64LtS, &[b.1, zero], &[Type::I32]);
    let sr = body.add_op(wb, Operator::I64LtS, &[result.1, zero], &[Type::I32]);
    let signs_ab = body.add_op(wb, Operator::I32Xor, &[sa, sb], &[Type::I32]);
    let signs_ar = body.add_op(wb, Operator::I32Xor, &[sa, sr], &[Type::I32]);
    if add {
        let same = body.add_op(wb, Operator::I32Eqz, &[signs_ab], &[Type::I32]);
        body.add_op(wb, Operator::I32And, &[same, signs_ar], &[Type::I32])
    } else {
        body.add_op(wb, Operator::I32And, &[signs_ab, signs_ar], &[Type::I32])
    }
}

pub(super) fn unsigned_add_overflow_flag(
    body: &mut FunctionBody,
    wb: waffle::Block,
    a: (waffle::Value, waffle::Value),
    b: (waffle::Value, waffle::Value),
    result: (waffle::Value, waffle::Value),
) -> waffle::Value {
    let hi0 = body.add_op(wb, Operator::I64Add, &[a.1, b.1], &[Type::I64]);
    let hi_wrap = body.add_op(wb, Operator::I64LtU, &[hi0, a.1], &[Type::I32]);
    let carry_lo = body.add_op(wb, Operator::I64LtU, &[result.0, a.0], &[Type::I32]);
    let carry_lo64 = body.add_op(wb, Operator::I64ExtendI32U, &[carry_lo], &[Type::I64]);
    let hi = body.add_op(wb, Operator::I64Add, &[hi0, carry_lo64], &[Type::I64]);
    let carry_hi = body.add_op(wb, Operator::I64LtU, &[hi, hi0], &[Type::I32]);
    let wraps = body.add_op(wb, Operator::I32Or, &[hi_wrap, carry_hi], &[Type::I32]);
    let _ = result;
    wraps
}
