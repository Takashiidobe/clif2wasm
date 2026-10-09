use crate::ensure;
use crate::error::Result;
use cranelift_codegen::ir::{self, InstructionData, Opcode, types};
use waffle::{FunctionBody, Operator, Type};

use super::*;
use crate::bridge::FnCx;
use crate::i128_lower;

#[derive(Clone, Copy, PartialEq)]
enum Kind {
    Add,
    Sub,
    Mul,
}

pub(super) fn is_overflow_opcode(opcode: Opcode) -> bool {
    matches!(
        opcode,
        Opcode::UaddOverflow
            | Opcode::SaddOverflow
            | Opcode::UsubOverflow
            | Opcode::SsubOverflow
            | Opcode::UmulOverflow
            | Opcode::SmulOverflow
            | Opcode::UaddOverflowCin
            | Opcode::SaddOverflowCin
            | Opcode::UsubOverflowBin
            | Opcode::SsubOverflowBin
    )
}

fn classify(opcode: Opcode) -> (Kind, bool) {
    match opcode {
        Opcode::UaddOverflow | Opcode::UaddOverflowCin | Opcode::UaddOverflowTrap => {
            (Kind::Add, false)
        }
        Opcode::SaddOverflow | Opcode::SaddOverflowCin => (Kind::Add, true),
        Opcode::UsubOverflow | Opcode::UsubOverflowBin => (Kind::Sub, false),
        Opcode::SsubOverflow | Opcode::SsubOverflowBin => (Kind::Sub, true),
        Opcode::UmulOverflow => (Kind::Mul, false),
        Opcode::SmulOverflow => (Kind::Mul, true),
        other => unreachable!("{other} is not an overflow opcode"),
    }
}

fn wide_const(body: &mut FunctionBody, wb: waffle::Block, value: u64) -> waffle::Value {
    body.add_op(wb, Operator::I64Const { value }, &[], &[Type::I64])
}

fn widen(
    body: &mut FunctionBody,
    wb: waffle::Block,
    v: waffle::Value,
    ty: ir::Type,
    signed: bool,
) -> waffle::Value {
    if signed {
        let v = if matches!(ty, types::I8 | types::I16) {
            sign_extend_narrow(body, wb, v, ty)
        } else {
            v
        };
        body.add_op(wb, Operator::I64ExtendI32S, &[v], &[Type::I64])
    } else {
        body.add_op(wb, Operator::I64ExtendI32U, &[v], &[Type::I64])
    }
}

fn wrap_in_i64(
    body: &mut FunctionBody,
    wb: waffle::Block,
    r: waffle::Value,
    ty: ir::Type,
    signed: bool,
) -> waffle::Value {
    if signed {
        let op = match ty {
            types::I8 => Operator::I64Extend8S,
            types::I16 => Operator::I64Extend16S,
            _ => Operator::I64Extend32S,
        };
        body.add_op(wb, op, &[r], &[Type::I64])
    } else {
        let mask = match ty {
            types::I8 => 0xFF,
            types::I16 => 0xFFFF,
            _ => 0xFFFF_FFFF,
        };
        let mask = wide_const(body, wb, mask);
        body.add_op(wb, Operator::I64And, &[r, mask], &[Type::I64])
    }
}

fn out_of_range(
    body: &mut FunctionBody,
    wb: waffle::Block,
    r: waffle::Value,
    ty: ir::Type,
    signed: bool,
) -> waffle::Value {
    let wrapped = wrap_in_i64(body, wb, r, ty, signed);
    body.add_op(wb, Operator::I64Ne, &[r, wrapped], &[Type::I32])
}

fn wide_op(
    body: &mut FunctionBody,
    wb: waffle::Block,
    kind: Kind,
    a: waffle::Value,
    b: waffle::Value,
) -> waffle::Value {
    let op = match kind {
        Kind::Add => Operator::I64Add,
        Kind::Sub => Operator::I64Sub,
        Kind::Mul => Operator::I64Mul,
    };
    body.add_op(wb, op, &[a, b], &[Type::I64])
}

fn pair_op(
    body: &mut FunctionBody,
    wb: waffle::Block,
    kind: Kind,
    a: (waffle::Value, waffle::Value),
    b: (waffle::Value, waffle::Value),
) -> (waffle::Value, waffle::Value) {
    match kind {
        Kind::Add => i128_lower::add(body, wb, a, b),
        Kind::Sub => i128_lower::sub(body, wb, a, b),
        Kind::Mul => i128_lower::mul(body, wb, a, b),
    }
}

fn pair_widen(
    body: &mut FunctionBody,
    wb: waffle::Block,
    v: waffle::Value,
    signed: bool,
) -> (waffle::Value, waffle::Value) {
    if signed {
        let shift = wide_const(body, wb, 63);
        let hi = body.add_op(wb, Operator::I64ShrS, &[v, shift], &[Type::I64]);
        (v, hi)
    } else {
        (v, wide_const(body, wb, 0))
    }
}

fn pair_out_of_range(
    body: &mut FunctionBody,
    wb: waffle::Block,
    r: (waffle::Value, waffle::Value),
    signed: bool,
) -> waffle::Value {
    let expected = if signed {
        let shift = wide_const(body, wb, 63);
        body.add_op(wb, Operator::I64ShrS, &[r.0, shift], &[Type::I64])
    } else {
        wide_const(body, wb, 0)
    };
    body.add_op(wb, Operator::I64Ne, &[r.1, expected], &[Type::I32])
}

fn carry_bit(
    cx: &FnCx,
    body: &mut FunctionBody,
    wb: waffle::Block,
    carry: ir::Value,
) -> Result<waffle::Value> {
    let truthy = coerce_cond(cx, body, wb, carry)?;
    let zero = body.add_op(wb, Operator::I32Eqz, &[truthy], &[Type::I32]);
    Ok(body.add_op(wb, Operator::I32Eqz, &[zero], &[Type::I32]))
}

/// Lowers the value and overflow flag for 8/16/32/64-bit operands; `carry` is the
/// optional carry/borrow-in. Returns the wasm result value and an i32 flag.
fn overflow_parts(
    cx: &FnCx,
    body: &mut FunctionBody,
    wb: waffle::Block,
    ty: ir::Type,
    kind: Kind,
    signed: bool,
    operands: (ir::Value, ir::Value),
    carry: Option<ir::Value>,
) -> Result<(waffle::Value, waffle::Value)> {
    ensure!(
        matches!(ty, types::I8 | types::I16 | types::I32 | types::I64),
        "overflow operations on {ty} are unsupported"
    );
    let a = cx.one(operands.0)?;
    let b = cx.one(operands.1)?;
    let carry_in = carry.map(|c| carry_bit(cx, body, wb, c)).transpose()?;
    if ty == types::I64 {
        let (pa, pb) = (
            pair_widen(body, wb, a, signed),
            pair_widen(body, wb, b, signed),
        );
        let first = pair_op(body, wb, kind, pa, pb);
        let mut flag = pair_out_of_range(body, wb, first, signed);
        let mut result = first;
        if let Some(bit) = carry_in {
            let bit = body.add_op(wb, Operator::I64ExtendI32U, &[bit], &[Type::I64]);
            let base = pair_widen(body, wb, first.0, signed);
            let zero = wide_const(body, wb, 0);
            result = pair_op(body, wb, kind, base, (bit, zero));
            let second = pair_out_of_range(body, wb, result, signed);
            flag = body.add_op(wb, Operator::I32Or, &[flag, second], &[Type::I32]);
        }
        return Ok((result.0, flag));
    }
    let (ea, eb) = (
        widen(body, wb, a, ty, signed),
        widen(body, wb, b, ty, signed),
    );
    let first = wide_op(body, wb, kind, ea, eb);
    let mut flag = out_of_range(body, wb, first, ty, signed);
    let mut result = first;
    if let Some(bit) = carry_in {
        let bit = body.add_op(wb, Operator::I64ExtendI32U, &[bit], &[Type::I64]);
        let base = wrap_in_i64(body, wb, first, ty, signed);
        result = wide_op(body, wb, kind, base, bit);
        let second = out_of_range(body, wb, result, ty, signed);
        flag = body.add_op(wb, Operator::I32Or, &[flag, second], &[Type::I32]);
    }
    let mut value = body.add_op(wb, Operator::I32WrapI64, &[result], &[Type::I32]);
    if matches!(ty, types::I8 | types::I16) {
        value = mask_narrow(body, wb, value, ty);
    }
    Ok((value, flag))
}

pub(super) fn lower_scalar_overflow(
    cx: &mut FnCx,
    body: &mut FunctionBody,
    wb: waffle::Block,
    inst: ir::Inst,
) -> Result<()> {
    let dfg = &cx.clif.dfg;
    let (opcode, operands, carry) = match dfg.insts[inst] {
        InstructionData::Binary { opcode, args } => (opcode, (args[0], args[1]), None),
        InstructionData::Ternary { opcode, args } => (opcode, (args[0], args[1]), Some(args[2])),
        _ => unreachable!("lower_scalar_overflow dispatched on a non-matching instruction"),
    };
    let results = dfg.inst_results(inst).to_vec();
    let ty = dfg.value_type(results[0]);
    let (kind, signed) = classify(opcode);
    let (value, flag) = overflow_parts(cx, body, wb, ty, kind, signed, operands, carry)?;
    cx.bind1(results[0], value);
    cx.bind1(results[1], flag);
    Ok(())
}

/// Binds the sum of `uadd_overflow_trap` and returns the i32 overflow flag the caller
/// must turn into a trap.
pub(crate) fn lower_add_trap_value(
    cx: &mut FnCx,
    body: &mut FunctionBody,
    wb: waffle::Block,
    inst: ir::Inst,
) -> Result<waffle::Value> {
    let dfg = &cx.clif.dfg;
    let InstructionData::IntAddTrap { args, .. } = dfg.insts[inst] else {
        unreachable!("lower_add_trap_value dispatched on a non-matching instruction")
    };
    let result = dfg.first_result(inst);
    let ty = dfg.value_type(result);
    if ty == types::I128 {
        let (a, b) = (cx.pair(args[0])?, cx.pair(args[1])?);
        let sum = i128_lower::add(body, wb, a, b);
        let flag = super::i128::unsigned_add_overflow_flag(body, wb, a, b, sum);
        cx.bind2(result, sum.0, sum.1);
        return Ok(flag);
    }
    let (value, flag) =
        overflow_parts(cx, body, wb, ty, Kind::Add, false, (args[0], args[1]), None)?;
    cx.bind1(result, value);
    Ok(flag)
}

pub(super) fn lower_i128_mul_overflow(
    cx: &mut FnCx,
    body: &mut FunctionBody,
    wb: waffle::Block,
    inst: ir::Inst,
    opcode: Opcode,
    args: [ir::Value; 2],
) -> Result<()> {
    let signed = opcode == Opcode::SmulOverflow;
    let (a, b) = (cx.pair(args[0])?, cx.pair(args[1])?);
    let low = i128_lower::mul(body, wb, a, b);
    let high = i128_lower::mulhi(body, wb, a, b, signed);
    let expected = if signed {
        let shift = wide_const(body, wb, 63);
        let sign = body.add_op(wb, Operator::I64ShrS, &[low.1, shift], &[Type::I64]);
        (sign, sign)
    } else {
        let zero = wide_const(body, wb, 0);
        (zero, zero)
    };
    let lo_differs = body.add_op(wb, Operator::I64Ne, &[high.0, expected.0], &[Type::I32]);
    let hi_differs = body.add_op(wb, Operator::I64Ne, &[high.1, expected.1], &[Type::I32]);
    let flag = body.add_op(wb, Operator::I32Or, &[lo_differs, hi_differs], &[Type::I32]);
    let results = cx.clif.dfg.inst_results(inst).to_vec();
    cx.bind2(results[0], low.0, low.1);
    cx.bind1(results[1], flag);
    Ok(())
}
