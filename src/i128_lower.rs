//! i128 legalization: CLIF i128 ops lowered to (lo, hi) pairs of wasm i64 ops.
//!
//! CLIF i128 operations are lowered to pairs of wasm i64 values. Arithmetic that
//! spans both halves is synthesized with carry, borrow, or quotient-bit logic.

use crate::waffle as waffle;
use cranelift_codegen::ir::condcodes::IntCC;
use waffle::{FunctionBody, Operator, Type, Value};

use crate::error::{Error, Result};

type Pair = (Value, Value); // (lo, hi)

fn op1(
    body: &mut FunctionBody,
    wb: waffle::Block,
    op: Operator,
    args: &[Value],
    ty: Type,
) -> Value {
    body.add_op(wb, op, args, &[ty])
}

fn c64(body: &mut FunctionBody, wb: waffle::Block, v: u64) -> Value {
    op1(body, wb, Operator::I64Const { value: v }, &[], Type::I64)
}

/// wasm select: returns `a` when `cond != 0`, else `b`.
fn sel64(body: &mut FunctionBody, wb: waffle::Block, cond: Value, a: Value, b: Value) -> Value {
    op1(body, wb, Operator::Select, &[a, b, cond], Type::I64)
}

pub fn add(body: &mut FunctionBody, wb: waffle::Block, a: Pair, b: Pair) -> Pair {
    let lo = op1(body, wb, Operator::I64Add, &[a.0, b.0], Type::I64);
    let carry_i32 = op1(body, wb, Operator::I64LtU, &[lo, a.0], Type::I32);
    let carry = op1(body, wb, Operator::I64ExtendI32U, &[carry_i32], Type::I64);
    let hi0 = op1(body, wb, Operator::I64Add, &[a.1, b.1], Type::I64);
    let hi = op1(body, wb, Operator::I64Add, &[hi0, carry], Type::I64);
    (lo, hi)
}

pub fn sub(body: &mut FunctionBody, wb: waffle::Block, a: Pair, b: Pair) -> Pair {
    let lo = op1(body, wb, Operator::I64Sub, &[a.0, b.0], Type::I64);
    let borrow_i32 = op1(body, wb, Operator::I64LtU, &[a.0, b.0], Type::I32);
    let borrow = op1(body, wb, Operator::I64ExtendI32U, &[borrow_i32], Type::I64);
    let hi0 = op1(body, wb, Operator::I64Sub, &[a.1, b.1], Type::I64);
    let hi = op1(body, wb, Operator::I64Sub, &[hi0, borrow], Type::I64);
    (lo, hi)
}

/// Full 128-bit multiply from 64-bit halves: lo = lo(a.0*b.0);
/// hi = a.1*b.0 + a.0*b.1 + umulhi64(a.0, b.0), with umulhi64 built from 32-bit
/// partial products.
pub fn mul(body: &mut FunctionBody, wb: waffle::Block, a: Pair, b: Pair) -> Pair {
    use Operator::*;
    let mask32 = c64(body, wb, 0xFFFF_FFFF);
    let c32 = c64(body, wb, 32);
    let lo32 = |body: &mut FunctionBody, v: Value| op1(body, wb, I64And, &[v, mask32], Type::I64);
    let hi32 = |body: &mut FunctionBody, v: Value| op1(body, wb, I64ShrU, &[v, c32], Type::I64);

    let al = lo32(body, a.0);
    let ah = hi32(body, a.0);
    let bl = lo32(body, b.0);
    let bh = hi32(body, b.0);

    // umulhi64(a.0, b.0) with carry-correct 32-bit partials.
    let lo_lo = op1(body, wb, I64Mul, &[al, bl], Type::I64);
    let t1 = op1(body, wb, I64Mul, &[ah, bl], Type::I64);
    let mid1 = {
        let h = hi32(body, lo_lo);
        op1(body, wb, I64Add, &[t1, h], Type::I64)
    };
    let t2 = op1(body, wb, I64Mul, &[al, bh], Type::I64);
    let mid2 = {
        let l = lo32(body, mid1);
        op1(body, wb, I64Add, &[t2, l], Type::I64)
    };
    let t3 = op1(body, wb, I64Mul, &[ah, bh], Type::I64);
    let hi_of_lo = {
        let h1 = hi32(body, mid1);
        let h2 = hi32(body, mid2);
        let s = op1(body, wb, I64Add, &[t3, h1], Type::I64);
        op1(body, wb, I64Add, &[s, h2], Type::I64)
    };

    let lo = op1(body, wb, I64Mul, &[a.0, b.0], Type::I64);
    let cross1 = op1(body, wb, I64Mul, &[a.1, b.0], Type::I64);
    let cross2 = op1(body, wb, I64Mul, &[a.0, b.1], Type::I64);
    let hi = {
        let s = op1(body, wb, I64Add, &[cross1, cross2], Type::I64);
        op1(body, wb, I64Add, &[s, hi_of_lo], Type::I64)
    };
    (lo, hi)
}

pub fn divrem_u(
    body: &mut FunctionBody,
    wb: waffle::Block,
    dividend: Pair,
    divisor: Pair,
) -> (Pair, Pair) {
    use Operator::*;
    let zero = c64(body, wb, 0);
    let one = c64(body, wb, 1);
    let d_or = op1(body, wb, I64Or, &[divisor.0, divisor.1], Type::I64);
    let is_zero = op1(body, wb, I64Eqz, &[d_or], Type::I32);
    let trap_den = op1(body, wb, Select, &[zero, one, is_zero], Type::I64);
    let _ = op1(body, wb, I64DivU, &[one, trap_den], Type::I64);

    let mut rem = (zero, zero);
    let mut quotient = (zero, zero);
    let (mut src_lo, mut src_hi) = dividend;
    let c1 = c64(body, wb, 1);
    let c63 = c64(body, wb, 63);
    for _ in 0..128 {
        let bit = op1(body, wb, I64ShrU, &[src_hi, c63], Type::I64);
        let src_hi_shift = op1(body, wb, I64Shl, &[src_hi, c1], Type::I64);
        let src_lo_carry = op1(body, wb, I64ShrU, &[src_lo, c63], Type::I64);
        let src_lo_shift = op1(body, wb, I64Shl, &[src_lo, c1], Type::I64);
        src_hi = op1(body, wb, I64Or, &[src_hi_shift, src_lo_carry], Type::I64);
        src_lo = src_lo_shift;

        let carry = op1(body, wb, I64ShrU, &[rem.1, c63], Type::I64);
        let rem_hi_shift = op1(body, wb, I64Shl, &[rem.1, c1], Type::I64);
        let rem_lo_carry = op1(body, wb, I64ShrU, &[rem.0, c63], Type::I64);
        let rem_lo_shift = op1(body, wb, I64Shl, &[rem.0, c1], Type::I64);
        let shifted_hi = op1(body, wb, I64Or, &[rem_hi_shift, rem_lo_carry], Type::I64);
        let shifted_lo = op1(body, wb, I64Or, &[rem_lo_shift, bit], Type::I64);
        let hi_gt = op1(body, wb, I64GtU, &[shifted_hi, divisor.1], Type::I32);
        let hi_eq = op1(body, wb, I64Eq, &[shifted_hi, divisor.1], Type::I32);
        let lo_ge = op1(body, wb, I64GeU, &[shifted_lo, divisor.0], Type::I32);
        let hi_eq_and_lo_ge = op1(body, wb, I32And, &[hi_eq, lo_ge], Type::I32);
        let ge = op1(body, wb, I32Or, &[hi_gt, hi_eq_and_lo_ge], Type::I32);
        let carry_nonzero = op1(body, wb, I64Ne, &[carry, zero], Type::I32);
        let take = op1(body, wb, I32Or, &[carry_nonzero, ge], Type::I32);
        let diff = sub(body, wb, (shifted_lo, shifted_hi), divisor);
        rem = (
            sel64(body, wb, take, diff.0, shifted_lo),
            sel64(body, wb, take, diff.1, shifted_hi),
        );

        let q_hi_carry = op1(body, wb, I64ShrU, &[quotient.0, c63], Type::I64);
        let q_hi_shift = op1(body, wb, I64Shl, &[quotient.1, c1], Type::I64);
        let q_lo_shift = op1(body, wb, I64Shl, &[quotient.0, c1], Type::I64);
        let q_hi = op1(body, wb, I64Or, &[q_hi_shift, q_hi_carry], Type::I64);
        let q_bit = op1(body, wb, I64ExtendI32U, &[take], Type::I64);
        let q_lo = op1(body, wb, I64Or, &[q_lo_shift, q_bit], Type::I64);
        quotient = (q_lo, q_hi);
    }
    (quotient, rem)
}

pub fn divrem_s(
    body: &mut FunctionBody,
    wb: waffle::Block,
    dividend: Pair,
    divisor: Pair,
) -> Result<(Pair, Pair)> {
    use Operator::*;
    let zero = c64(body, wb, 0);
    let one = c64(body, wb, 1);
    let c63 = c64(body, wb, 63);
    let min = (zero, c64(body, wb, 1u64 << 63));
    let minus_one = (c64(body, wb, u64::MAX), c64(body, wb, u64::MAX));
    let is_min = icmp(body, wb, IntCC::Equal, dividend, min)?;
    let is_minus_one = icmp(body, wb, IntCC::Equal, divisor, minus_one)?;
    let overflow = op1(body, wb, I32And, &[is_min, is_minus_one], Type::I32);
    let trap_den = op1(body, wb, Select, &[zero, one, overflow], Type::I64);
    let _ = op1(body, wb, I64DivS, &[one, trap_den], Type::I64);

    let neg_a = op1(body, wb, I64ShrS, &[dividend.1, c63], Type::I64);
    let neg_b = op1(body, wb, I64ShrS, &[divisor.1, c63], Type::I64);
    let abs_a = {
        let negated = sub(body, wb, (zero, zero), dividend);
        let negative = op1(body, wb, I64Ne, &[neg_a, zero], Type::I32);
        (
            sel64(body, wb, negative, negated.0, dividend.0),
            sel64(body, wb, negative, negated.1, dividend.1),
        )
    };
    let abs_b = {
        let negated = sub(body, wb, (zero, zero), divisor);
        let negative = op1(body, wb, I64Ne, &[neg_b, zero], Type::I32);
        (
            sel64(body, wb, negative, negated.0, divisor.0),
            sel64(body, wb, negative, negated.1, divisor.1),
        )
    };
    let (mut quotient, mut rem) = divrem_u(body, wb, abs_a, abs_b);
    let q_negative = op1(body, wb, I64Xor, &[neg_a, neg_b], Type::I64);
    let q_negative = op1(body, wb, I64Ne, &[q_negative, zero], Type::I32);
    let neg_q = sub(body, wb, (zero, zero), quotient);
    quotient = (
        sel64(body, wb, q_negative, neg_q.0, quotient.0),
        sel64(body, wb, q_negative, neg_q.1, quotient.1),
    );
    let neg_r = sub(body, wb, (zero, zero), rem);
    let a_negative = op1(body, wb, I64Ne, &[neg_a, zero], Type::I32);
    rem = (
        sel64(body, wb, a_negative, neg_r.0, rem.0),
        sel64(body, wb, a_negative, neg_r.1, rem.1),
    );
    Ok((quotient, rem))
}

pub fn mulhi(body: &mut FunctionBody, wb: waffle::Block, a: Pair, b: Pair, signed: bool) -> Pair {
    use Operator::*;
    let zero = c64(body, wb, 0);
    let one = c64(body, wb, 1);
    let c63 = c64(body, wb, 63);
    let mut product = [zero; 4];
    let mut multiplicand = [a.0, a.1, zero, zero];
    let mut multiplier = b;
    for _ in 0..128 {
        let bit = op1(body, wb, I64And, &[multiplier.0, one], Type::I64);
        let bit32 = op1(body, wb, I32WrapI64, &[bit], Type::I32);
        let m = multiplicand.map(|limb| sel64(body, wb, bit32, limb, zero));
        let mut carry = zero;
        for index in 0..4 {
            let first = op1(body, wb, I64Add, &[product[index], m[index]], Type::I64);
            let c1 = op1(body, wb, I64LtU, &[first, product[index]], Type::I32);
            let second = op1(body, wb, I64Add, &[first, carry], Type::I64);
            let c2 = op1(body, wb, I64LtU, &[second, first], Type::I32);
            let c = op1(body, wb, I32Or, &[c1, c2], Type::I32);
            carry = op1(body, wb, I64ExtendI32U, &[c], Type::I64);
            product[index] = second;
        }
        let m0 = op1(body, wb, I64Shl, &[multiplicand[0], one], Type::I64);
        let m1s = op1(body, wb, I64Shl, &[multiplicand[1], one], Type::I64);
        let m1c = op1(body, wb, I64ShrU, &[multiplicand[0], c63], Type::I64);
        let m2s = op1(body, wb, I64Shl, &[multiplicand[2], one], Type::I64);
        let m2c = op1(body, wb, I64ShrU, &[multiplicand[1], c63], Type::I64);
        let m3s = op1(body, wb, I64Shl, &[multiplicand[3], one], Type::I64);
        let m3c = op1(body, wb, I64ShrU, &[multiplicand[2], c63], Type::I64);
        multiplicand = [
            m0,
            op1(body, wb, I64Or, &[m1s, m1c], Type::I64),
            op1(body, wb, I64Or, &[m2s, m2c], Type::I64),
            op1(body, wb, I64Or, &[m3s, m3c], Type::I64),
        ];
        let old_hi = multiplier.1;
        let lo_shift = op1(body, wb, I64ShrU, &[multiplier.0, one], Type::I64);
        let hi_shift = op1(body, wb, I64ShrU, &[old_hi, one], Type::I64);
        let b_to_lo = op1(body, wb, I64Shl, &[old_hi, c63], Type::I64);
        multiplier = (
            op1(body, wb, I64Or, &[lo_shift, b_to_lo], Type::I64),
            hi_shift,
        );
    }
    let mut high = (product[2], product[3]);
    if signed {
        let zero = c64(body, wb, 0);
        let sign = c64(body, wb, 63);
        let a_negative = op1(body, wb, I64ShrS, &[a.1, sign], Type::I64);
        let b_negative = op1(body, wb, I64ShrS, &[b.1, sign], Type::I64);
        let a_negative = op1(body, wb, I64Ne, &[a_negative, zero], Type::I32);
        let b_negative = op1(body, wb, I64Ne, &[b_negative, zero], Type::I32);
        let correction_a = (
            sel64(body, wb, a_negative, b.0, zero),
            sel64(body, wb, a_negative, b.1, zero),
        );
        let correction_b = (
            sel64(body, wb, b_negative, a.0, zero),
            sel64(body, wb, b_negative, a.1, zero),
        );
        high = sub(body, wb, high, correction_a);
        high = sub(body, wb, high, correction_b);
    }
    high
}

pub fn logic(
    body: &mut FunctionBody,
    wb: waffle::Block,
    op: Operator, // an I64 pairwise op: I64And / I64Or / I64Xor
    a: Pair,
    b: Pair,
) -> Pair {
    let lo = op1(body, wb, op, &[a.0, b.0], Type::I64);
    let hi = op1(body, wb, op, &[a.1, b.1], Type::I64);
    (lo, hi)
}

/// i128 comparison -> wasm i32 (0/1). Ordering compares are `strict_hi | (eq_hi & lo_u)`.
pub fn icmp(
    body: &mut FunctionBody,
    wb: waffle::Block,
    cond: IntCC,
    a: Pair,
    b: Pair,
) -> Result<Value> {
    use Operator::*;
    let ordered = |body: &mut FunctionBody, strict_hi_op: Operator, lo_op: Operator| {
        let strict_hi = op1(body, wb, strict_hi_op, &[a.1, b.1], Type::I32);
        let eq_hi = op1(body, wb, I64Eq, &[a.1, b.1], Type::I32);
        let lo_cmp = op1(body, wb, lo_op, &[a.0, b.0], Type::I32);
        let both = op1(body, wb, I32And, &[eq_hi, lo_cmp], Type::I32);
        op1(body, wb, I32Or, &[strict_hi, both], Type::I32)
    };
    Ok(match cond {
        IntCC::Equal => {
            let lo = op1(body, wb, I64Eq, &[a.0, b.0], Type::I32);
            let hi = op1(body, wb, I64Eq, &[a.1, b.1], Type::I32);
            op1(body, wb, I32And, &[lo, hi], Type::I32)
        }
        IntCC::NotEqual => {
            let lo = op1(body, wb, I64Ne, &[a.0, b.0], Type::I32);
            let hi = op1(body, wb, I64Ne, &[a.1, b.1], Type::I32);
            op1(body, wb, I32Or, &[lo, hi], Type::I32)
        }
        IntCC::SignedLessThan => ordered(body, I64LtS, I64LtU),
        IntCC::UnsignedLessThan => ordered(body, I64LtU, I64LtU),
        IntCC::SignedLessThanOrEqual => ordered(body, I64LtS, I64LeU),
        IntCC::UnsignedLessThanOrEqual => ordered(body, I64LtU, I64LeU),
        IntCC::SignedGreaterThan => ordered(body, I64GtS, I64GtU),
        IntCC::UnsignedGreaterThan => ordered(body, I64GtU, I64GtU),
        IntCC::SignedGreaterThanOrEqual => ordered(body, I64GtS, I64GeU),
        IntCC::UnsignedGreaterThanOrEqual => ordered(body, I64GtU, I64GeU),
    })
}

/// Branchless dynamic shifts. `amt` is an i64, taken mod 128 (CLIF semantics).
/// The `s1 == 0` special case exists because `x >> (64 - 0)` re-masks to `x >> 0`
/// in wasm, which would leak the whole word into the spill term.
pub fn shift(
    body: &mut FunctionBody,
    wb: waffle::Block,
    kind: ShiftKind,
    v: Pair,
    amt: Value,
) -> Result<Pair> {
    use Operator::*;
    let c127 = c64(body, wb, 127);
    let s = op1(body, wb, I64And, &[amt, c127], Type::I64);
    let c63 = c64(body, wb, 63);
    let s1 = op1(body, wb, I64And, &[s, c63], Type::I64);
    let c64v = c64(body, wb, 64);
    let big = op1(body, wb, I64GeU, &[s, c64v], Type::I32); // s >= 64
    let inv = op1(body, wb, I64Sub, &[c64v, s1], Type::I64); // 64 - s1 (64 when s1==0)
    let s1_is0 = op1(body, wb, I64Eqz, &[s1], Type::I32);
    let zero = c64(body, wb, 0);

    Ok(match kind {
        ShiftKind::Shl => {
            let spill_raw = op1(body, wb, I64ShrU, &[v.0, inv], Type::I64);
            let spill = sel64(body, wb, s1_is0, zero, spill_raw);
            let hi_shift = op1(body, wb, I64Shl, &[v.1, s1], Type::I64);
            let hi_small = op1(body, wb, I64Or, &[hi_shift, spill], Type::I64);
            let lo_small = op1(body, wb, I64Shl, &[v.0, s1], Type::I64);
            let hi_big = op1(body, wb, I64Shl, &[v.0, s1], Type::I64);
            let hi = sel64(body, wb, big, hi_big, hi_small);
            let lo = sel64(body, wb, big, zero, lo_small);
            (lo, hi)
        }
        ShiftKind::UShr => {
            let spill_raw = op1(body, wb, I64Shl, &[v.1, inv], Type::I64);
            let spill = sel64(body, wb, s1_is0, zero, spill_raw);
            let lo_shift = op1(body, wb, I64ShrU, &[v.0, s1], Type::I64);
            let lo_small = op1(body, wb, I64Or, &[lo_shift, spill], Type::I64);
            let hi_small = op1(body, wb, I64ShrU, &[v.1, s1], Type::I64);
            let lo_big = op1(body, wb, I64ShrU, &[v.1, s1], Type::I64);
            let lo = sel64(body, wb, big, lo_big, lo_small);
            let hi = sel64(body, wb, big, zero, hi_small);
            (lo, hi)
        }
        ShiftKind::SShr => {
            let spill_raw = op1(body, wb, I64Shl, &[v.1, inv], Type::I64);
            let spill = sel64(body, wb, s1_is0, zero, spill_raw);
            let lo_shift = op1(body, wb, I64ShrU, &[v.0, s1], Type::I64);
            let lo_small = op1(body, wb, I64Or, &[lo_shift, spill], Type::I64);
            let hi_small = op1(body, wb, I64ShrS, &[v.1, s1], Type::I64);
            let c63b = c64(body, wb, 63);
            let sign = op1(body, wb, I64ShrS, &[v.1, c63b], Type::I64);
            let lo_big = op1(body, wb, I64ShrS, &[v.1, s1], Type::I64);
            let lo = sel64(body, wb, big, lo_big, lo_small);
            let hi = sel64(body, wb, big, sign, hi_small);
            (lo, hi)
        }
    })
}

#[derive(Copy, Clone)]
pub enum ShiftKind {
    Shl,
    UShr,
    SShr,
}

impl ShiftKind {
    pub fn from_opcode(op: cranelift_codegen::ir::Opcode) -> Result<Self> {
        use cranelift_codegen::ir::Opcode;
        Ok(match op {
            Opcode::Ishl => ShiftKind::Shl,
            Opcode::Ushr => ShiftKind::UShr,
            Opcode::Sshr => ShiftKind::SShr,
            other => return Err(Error::internal(format!("not a shift opcode: {other}"))),
        })
    }
}
