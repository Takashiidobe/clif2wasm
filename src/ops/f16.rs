use crate::error::Result;
use crate::unsupported;
use cranelift_codegen::ir::{self, Opcode};
use waffle::{FunctionBody, Operator, Type, Value};

use crate::bridge::FnCx;

fn i32c(body: &mut FunctionBody, wb: waffle::Block, value: u32) -> Value {
    body.add_op(wb, Operator::I32Const { value }, &[], &[Type::I32])
}

fn i32op(body: &mut FunctionBody, wb: waffle::Block, op: Operator, a: Value, b: Value) -> Value {
    body.add_op(wb, op, &[a, b], &[Type::I32])
}

fn select(body: &mut FunctionBody, wb: waffle::Block, yes: Value, no: Value, c: Value) -> Value {
    body.add_op(wb, Operator::Select, &[yes, no, c], &[Type::I32])
}

pub(super) fn to_f32(body: &mut FunctionBody, wb: waffle::Block, half: Value) -> Value {
    let magnitude_mask = i32c(body, wb, 0x7fff);
    let c13 = i32c(body, wb, 13);
    let magnitude = i32op(body, wb, Operator::I32And, half, magnitude_mask);
    let shifted = i32op(body, wb, Operator::I32Shl, magnitude, c13);
    let as_float = body.add_op(wb, Operator::F32ReinterpretI32, &[shifted], &[Type::F32]);
    let rebias = body.add_op(
        wb,
        Operator::F32Const { value: 0x7780_0000 },
        &[],
        &[Type::F32],
    );
    let scaled = body.add_op(wb, Operator::F32Mul, &[as_float, rebias], &[Type::F32]);
    let scaled_bits = body.add_op(wb, Operator::I32ReinterpretF32, &[scaled], &[Type::I32]);

    let exp_mask = i32c(body, wb, 0x7c00);
    let exp = i32op(body, wb, Operator::I32And, half, exp_mask);
    let special = i32op(body, wb, Operator::I32Eq, exp, exp_mask);
    let inf_exp = i32c(body, wb, 0x7f80_0000);
    let special_bits = i32op(body, wb, Operator::I32Or, shifted, inf_exp);
    let bits = select(body, wb, special_bits, scaled_bits, special);

    let sign_mask = i32c(body, wb, 0x8000);
    let c16 = i32c(body, wb, 16);
    let sign = i32op(body, wb, Operator::I32And, half, sign_mask);
    let sign = i32op(body, wb, Operator::I32Shl, sign, c16);
    let bits = i32op(body, wb, Operator::I32Or, bits, sign);
    body.add_op(wb, Operator::F32ReinterpretI32, &[bits], &[Type::F32])
}

pub(super) fn from_f32(body: &mut FunctionBody, wb: waffle::Block, x: Value) -> Value {
    let bits = body.add_op(wb, Operator::I32ReinterpretF32, &[x], &[Type::I32]);
    let sign_mask = i32c(body, wb, 0x8000_0000);
    let sign = i32op(body, wb, Operator::I32And, bits, sign_mask);
    let abs = i32op(body, wb, Operator::I32Xor, bits, sign);
    let c13 = i32c(body, wb, 13);

    let overflow_at = i32c(body, wb, 143 << 23);
    let overflows = i32op(body, wb, Operator::I32GeU, abs, overflow_at);
    let inf_bits = i32c(body, wb, 255 << 23);
    let is_nan = i32op(body, wb, Operator::I32GtU, abs, inf_bits);
    let payload_mask = i32c(body, wb, 0x3ff);
    let payload = i32op(body, wb, Operator::I32ShrU, abs, c13);
    let payload = i32op(body, wb, Operator::I32And, payload, payload_mask);
    let quiet_nan_base = i32c(body, wb, 0x7e00);
    let nan = i32op(body, wb, Operator::I32Or, quiet_nan_base, payload);
    let inf = i32c(body, wb, 0x7c00);
    let big = select(body, wb, nan, inf, is_nan);

    let subnormal_at = i32c(body, wb, 113 << 23);
    let subnormal = i32op(body, wb, Operator::I32LtU, abs, subnormal_at);
    let abs_float = body.add_op(wb, Operator::F32ReinterpretI32, &[abs], &[Type::F32]);
    let magic = body.add_op(
        wb,
        Operator::F32Const { value: 0x3f00_0000 },
        &[],
        &[Type::F32],
    );
    let sum = body.add_op(wb, Operator::F32Add, &[abs_float, magic], &[Type::F32]);
    let sum_bits = body.add_op(wb, Operator::I32ReinterpretF32, &[sum], &[Type::I32]);
    let magic_bits = i32c(body, wb, 0x3f00_0000);
    let small = i32op(body, wb, Operator::I32Sub, sum_bits, magic_bits);

    let one = i32c(body, wb, 1);
    let odd = i32op(body, wb, Operator::I32ShrU, abs, c13);
    let odd = i32op(body, wb, Operator::I32And, odd, one);
    let rebias = i32c(
        body,
        wb,
        (0xfff_u32).wrapping_add((15u32.wrapping_sub(127)) << 23),
    );
    let rounded = i32op(body, wb, Operator::I32Add, abs, rebias);
    let rounded = i32op(body, wb, Operator::I32Add, rounded, odd);
    let normal = i32op(body, wb, Operator::I32ShrU, rounded, c13);

    let finite = select(body, wb, small, normal, subnormal);
    let magnitude = select(body, wb, big, finite, overflows);
    let c16 = i32c(body, wb, 16);
    let sign = i32op(body, wb, Operator::I32ShrU, sign, c16);
    i32op(body, wb, Operator::I32Or, magnitude, sign)
}

pub(super) fn from_f64(body: &mut FunctionBody, wb: waffle::Block, x: Value) -> Value {
    let narrow = body.add_op(wb, Operator::F32DemoteF64, &[x], &[Type::F32]);
    let back = body.add_op(wb, Operator::F64PromoteF32, &[narrow], &[Type::F64]);
    let differs = body.add_op(wb, Operator::F64Ne, &[back, x], &[Type::I32]);
    let ordered = body.add_op(wb, Operator::F64Eq, &[x, x], &[Type::I32]);
    let inexact = i32op(body, wb, Operator::I32And, differs, ordered);
    let bits = body.add_op(wb, Operator::I32ReinterpretF32, &[narrow], &[Type::I32]);
    let one = i32c(body, wb, 1);
    let even = i32op(body, wb, Operator::I32And, bits, one);
    let even = body.add_op(wb, Operator::I32Eqz, &[even], &[Type::I32]);
    let adjust = i32op(body, wb, Operator::I32And, inexact, even);
    let back_abs = body.add_op(wb, Operator::F64Abs, &[back], &[Type::F64]);
    let x_abs = body.add_op(wb, Operator::F64Abs, &[x], &[Type::F64]);
    let too_big = body.add_op(wb, Operator::F64Gt, &[back_abs, x_abs], &[Type::I32]);
    let down = i32c(body, wb, u32::MAX);
    let step = select(body, wb, down, one, too_big);
    let nudged = i32op(body, wb, Operator::I32Add, bits, step);
    let odd_bits = select(body, wb, nudged, bits, adjust);
    let odd = body.add_op(wb, Operator::F32ReinterpretI32, &[odd_bits], &[Type::F32]);
    from_f32(body, wb, odd)
}

pub(super) fn lower_binary(
    cx: &mut FnCx,
    body: &mut FunctionBody,
    wb: waffle::Block,
    result: ir::Value,
    opcode: Opcode,
    args: [ir::Value; 2],
) -> Result<()> {
    let a = cx.one(args[0])?;
    let b = cx.one(args[1])?;
    if opcode == Opcode::Fcopysign {
        let magnitude_mask = i32c(body, wb, 0x7fff);
        let sign_mask = i32c(body, wb, 0x8000);
        let magnitude = i32op(body, wb, Operator::I32And, a, magnitude_mask);
        let sign = i32op(body, wb, Operator::I32And, b, sign_mask);
        let value = i32op(body, wb, Operator::I32Or, magnitude, sign);
        cx.bind1(result, value);
        return Ok(());
    }
    let op = match opcode {
        Opcode::Fadd => Operator::F32Add,
        Opcode::Fsub => Operator::F32Sub,
        Opcode::Fmul => Operator::F32Mul,
        Opcode::Fdiv => Operator::F32Div,
        Opcode::Fmin => Operator::F32Min,
        Opcode::Fmax => Operator::F32Max,
        other => unsupported!("{other} on f16 is unsupported"),
    };
    let a = to_f32(body, wb, a);
    let b = to_f32(body, wb, b);
    let wide = body.add_op(wb, op, &[a, b], &[Type::F32]);
    let value = from_f32(body, wb, wide);
    cx.bind1(result, value);
    Ok(())
}

pub(super) fn lower_unary(
    cx: &mut FnCx,
    body: &mut FunctionBody,
    wb: waffle::Block,
    result: ir::Value,
    opcode: Opcode,
    arg: ir::Value,
) -> Result<()> {
    let v = cx.one(arg)?;
    let value = match opcode {
        Opcode::Fneg => {
            let sign_mask = i32c(body, wb, 0x8000);
            i32op(body, wb, Operator::I32Xor, v, sign_mask)
        }
        Opcode::Fabs => {
            let magnitude_mask = i32c(body, wb, 0x7fff);
            i32op(body, wb, Operator::I32And, v, magnitude_mask)
        }
        _ => {
            let op = match opcode {
                Opcode::Sqrt => Operator::F32Sqrt,
                Opcode::Ceil => Operator::F32Ceil,
                Opcode::Floor => Operator::F32Floor,
                Opcode::Trunc => Operator::F32Trunc,
                Opcode::Nearest => Operator::F32Nearest,
                other => unsupported!("{other} on f16 is unsupported"),
            };
            let wide = to_f32(body, wb, v);
            let wide = body.add_op(wb, op, &[wide], &[Type::F32]);
            from_f32(body, wb, wide)
        }
    };
    cx.bind1(result, value);
    Ok(())
}
