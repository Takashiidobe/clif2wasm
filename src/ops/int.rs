use crate::error::Result;
use crate::{ensure, unsupported};
use cranelift_codegen::ir::{self, InstructionData, Opcode, types};
use waffle::{FunctionBody, Operator, Type};

use super::*;
use crate::bridge::FnCx;
use crate::i128_lower::{self};
use crate::map_type;

pub(super) fn lower_scalar_integer_special(
    cx: &mut FnCx,
    body: &mut FunctionBody,
    wb: waffle::Block,
    result: ir::Value,
    opcode: Opcode,
    args: [ir::Value; 2],
) -> Result<()> {
    let ty = cx.vty(result);
    ensure!(
        matches!(ty, types::I8 | types::I16 | types::I32 | types::I64),
        "{opcode} scalar type {ty} is unsupported"
    );
    let wty = map_type(ty)?;
    let narrow = matches!(ty, types::I8 | types::I16);
    let bits = ty.bits();
    let mut a = cx.one(args[0])?;
    let mut b = cx.one(args[1])?;
    if narrow {
        a = mask_narrow(body, wb, a, ty);
        b = mask_narrow(body, wb, b, ty);
    }
    let signed = matches!(
        opcode,
        Opcode::Smin | Opcode::Smax | Opcode::SaddSat | Opcode::SsubSat | Opcode::Smulhi
    );
    if narrow && signed && !matches!(opcode, Opcode::Smulhi) {
        a = sign_extend_narrow(body, wb, a, ty);
        b = sign_extend_narrow(body, wb, b, ty);
    }
    let wv = match opcode {
        Opcode::Smin | Opcode::Umin | Opcode::Smax | Opcode::Umax => {
            let lt = matches!(opcode, Opcode::Smin | Opcode::Umin);
            let cmp = match (wty, signed) {
                (Type::I32, true) => {
                    if lt {
                        Operator::I32LtS
                    } else {
                        Operator::I32GtS
                    }
                }
                (Type::I32, false) => {
                    if lt {
                        Operator::I32LtU
                    } else {
                        Operator::I32GtU
                    }
                }
                (Type::I64, true) => {
                    if lt {
                        Operator::I64LtS
                    } else {
                        Operator::I64GtS
                    }
                }
                (Type::I64, false) => {
                    if lt {
                        Operator::I64LtU
                    } else {
                        Operator::I64GtU
                    }
                }
                _ => unreachable!(),
            };
            let c = body.add_op(wb, cmp, &[a, b], &[Type::I32]);
            body.add_op(wb, Operator::Select, &[a, b, c], &[wty])
        }
        Opcode::Smulhi | Opcode::Umulhi if ty != types::I64 => {
            let (wide_ty, mul, ext_a, ext_b, shift, shr) = match ty {
                types::I8 | types::I16 => (
                    Type::I32,
                    Operator::I32Mul,
                    if ty == types::I8 {
                        Operator::I32Extend8S
                    } else {
                        Operator::I32Extend16S
                    },
                    if ty == types::I8 {
                        Operator::I32Extend8S
                    } else {
                        Operator::I32Extend16S
                    },
                    bits,
                    if signed {
                        Operator::I32ShrS
                    } else {
                        Operator::I32ShrU
                    },
                ),
                types::I32 => (
                    Type::I64,
                    Operator::I64Mul,
                    if signed {
                        Operator::I64ExtendI32S
                    } else {
                        Operator::I64ExtendI32U
                    },
                    if signed {
                        Operator::I64ExtendI32S
                    } else {
                        Operator::I64ExtendI32U
                    },
                    32,
                    if signed {
                        Operator::I64ShrS
                    } else {
                        Operator::I64ShrU
                    },
                ),
                _ => unreachable!(),
            };
            if matches!(ty, types::I8 | types::I16) && !signed {
                a = mask_narrow(body, wb, a, ty);
                b = mask_narrow(body, wb, b, ty);
            }
            let x = if matches!(ty, types::I8 | types::I16) && !signed {
                a
            } else {
                body.add_op(wb, ext_a, &[a], &[wide_ty])
            };
            let y = if matches!(ty, types::I8 | types::I16) && !signed {
                b
            } else {
                body.add_op(wb, ext_b, &[b], &[wide_ty])
            };
            let product = body.add_op(wb, mul, &[x, y], &[wide_ty]);
            let sh = match wide_ty {
                Type::I32 => body.add_op(wb, Operator::I32Const { value: shift }, &[], &[wide_ty]),
                _ => body.add_op(
                    wb,
                    Operator::I64Const {
                        value: shift as u64,
                    },
                    &[],
                    &[wide_ty],
                ),
            };
            let high = body.add_op(wb, shr, &[product, sh], &[wide_ty]);
            if wide_ty == Type::I64 {
                body.add_op(wb, Operator::I32WrapI64, &[high], &[Type::I32])
            } else {
                high
            }
        }
        Opcode::Smulhi | Opcode::Umulhi => {
            let signed = opcode == Opcode::Smulhi;
            let zero = body.add_op(wb, Operator::I64Const { value: 0 }, &[], &[Type::I64]);
            let sign = body.add_op(wb, Operator::I64Const { value: 63 }, &[], &[Type::I64]);
            let ah = if signed {
                body.add_op(wb, Operator::I64ShrS, &[a, sign], &[Type::I64])
            } else {
                zero
            };
            let bh = if signed {
                body.add_op(wb, Operator::I64ShrS, &[b, sign], &[Type::I64])
            } else {
                zero
            };
            i128_lower::mul(body, wb, (a, ah), (b, bh)).1
        }
        _ => unsupported!("scalar opcode {opcode} on {ty} is unsupported"),
    };
    let wv = if narrow {
        mask_narrow(body, wb, wv, ty)
    } else {
        wv
    };
    cx.bind1(result, wv);
    Ok(())
}

pub(super) fn lower_unary(
    cx: &mut FnCx,
    body: &mut FunctionBody,
    wb: waffle::Block,
    inst: ir::Inst,
    opcode: Opcode,
    arg: ir::Value,
) -> Result<()> {
    let dfg = &cx.clif.dfg;
    let src_ty = cx.vty(arg);
    match opcode {
        Opcode::VanyTrue | Opcode::VallTrue | Opcode::VhighBits => {
            let result = dfg.first_result(inst);
            let dst_ty = dfg.value_type(result);
            ensure!(
                src_ty.is_vector(),
                "{opcode} requires a fixed vector, got {src_ty}"
            );
            let values = cx.vector(arg)?;
            let lane_ty = src_ty.lane_type();
            let lane_count = src_ty.lane_count() as usize;
            let lanes_per_chunk = 128 / lane_ty.bits() as usize;
            let result_ty = if opcode == Opcode::VhighBits {
                map_type(dst_ty)?
            } else {
                Type::I32
            };
            if opcode == Opcode::VallTrue {
                let scalar_ty = map_type(lane_ty)?;
                let chunks = cx.vector(arg)?;
                let mut all = body.add_op(wb, Operator::I32Const { value: 1 }, &[], &[Type::I32]);
                for lane in 0..lane_count {
                    let chunk = lane / lanes_per_chunk;
                    let index = lane % lanes_per_chunk;
                    let extract = extract_lane_op(lane_ty, index as u8)?;
                    let value = body.add_op(wb, extract, &[chunks[chunk]], &[scalar_ty]);
                    let zero = match scalar_ty {
                        Type::I32 => {
                            body.add_op(wb, Operator::I32Const { value: 0 }, &[], &[Type::I32])
                        }
                        Type::I64 => {
                            body.add_op(wb, Operator::I64Const { value: 0 }, &[], &[Type::I64])
                        }
                        _ => unsupported!("vall_true lane type {lane_ty} is unsupported"),
                    };
                    let nonzero = match scalar_ty {
                        Type::I32 => body.add_op(wb, Operator::I32Ne, &[value, zero], &[Type::I32]),
                        Type::I64 => body.add_op(wb, Operator::I64Ne, &[value, zero], &[Type::I32]),
                        _ => unsupported!("vall_true lane type {lane_ty} is unsupported"),
                    };
                    all = body.add_op(wb, Operator::I32And, &[all, nonzero], &[Type::I32]);
                }
                cx.bind1(result, all);
                return Ok(());
            }
            let mut accumulated = None;
            for (chunk_index, value) in values.into_iter().enumerate() {
                let op = match (opcode, lane_ty) {
                    (Opcode::VanyTrue, _) => Operator::V128AnyTrue,
                    (Opcode::VhighBits, types::I8) => Operator::I8x16Bitmask,
                    (Opcode::VhighBits, types::I16) => Operator::I16x8Bitmask,
                    (Opcode::VhighBits, types::I32) => Operator::I32x4Bitmask,
                    (Opcode::VhighBits, types::I64) => Operator::I64x2Bitmask,
                    _ => unsupported!("{opcode} is unsupported for vector lane type {lane_ty}"),
                };
                let raw = body.add_op(wb, op, &[value], &[Type::I32]);
                let partial = if result_ty == Type::I64 {
                    body.add_op(wb, Operator::I64ExtendI32U, &[raw], &[Type::I64])
                } else {
                    raw
                };
                let result = if opcode == Opcode::VhighBits {
                    let shift = chunk_index * lanes_per_chunk;
                    if shift == 0 {
                        partial
                    } else {
                        let shift_ty = result_ty;
                        let shift_value = match shift_ty {
                            Type::I32 => body.add_op(
                                wb,
                                Operator::I32Const {
                                    value: shift as u32,
                                },
                                &[],
                                &[Type::I32],
                            ),
                            Type::I64 => body.add_op(
                                wb,
                                Operator::I64Const {
                                    value: shift as u64,
                                },
                                &[],
                                &[Type::I64],
                            ),
                            _ => unreachable!(),
                        };
                        let shift_op = if shift_ty == Type::I64 {
                            Operator::I64Shl
                        } else {
                            Operator::I32Shl
                        };
                        body.add_op(wb, shift_op, &[partial, shift_value], &[shift_ty])
                    }
                } else {
                    partial
                };
                accumulated = Some(match accumulated {
                    None => result,
                    Some(previous) if result_ty == Type::I64 => {
                        body.add_op(wb, Operator::I64Or, &[previous, result], &[Type::I64])
                    }
                    Some(previous) => {
                        body.add_op(wb, Operator::I32Or, &[previous, result], &[Type::I32])
                    }
                });
            }
            let mut result = accumulated.unwrap_or_else(|| match result_ty {
                Type::I64 => body.add_op(wb, Operator::I64Const { value: 0 }, &[], &[Type::I64]),
                _ => body.add_op(wb, Operator::I32Const { value: 0 }, &[], &[Type::I32]),
            });
            if result_ty == Type::I32 && matches!(dst_ty, types::I8 | types::I16) {
                result = mask_narrow(body, wb, result, dst_ty);
            }
            cx.bind1(dfg.first_result(inst), result);
        }
        Opcode::Iabs => {
            let result = dfg.first_result(inst);
            let ty = dfg.value_type(result);
            ensure!(ty.is_vector(), "iabs requires a vector, got {ty}");
            let op = match ty.lane_type() {
                types::I8 => Operator::I8x16Abs,
                types::I16 => Operator::I16x8Abs,
                types::I32 => Operator::I32x4Abs,
                types::I64 => Operator::I64x2Abs,
                other => unsupported!("iabs lane type {other} is unsupported"),
            };
            let values = cx
                .vector(arg)?
                .into_iter()
                .map(|value| body.add_op(wb, op, &[value], &[Type::V128]))
                .collect();
            cx.bind_vector(result, normalize_vector(body, wb, ty, values)?);
        }
        Opcode::Splat | Opcode::ScalarToVector => {
            let result = dfg.first_result(inst);
            let ty = dfg.value_type(result);
            ensure!(
                ty.is_vector(),
                "{opcode} result must be a fixed vector, got {ty}"
            );
            let lane_ty = ty.lane_type();
            let scalar = cx.one(arg)?;
            let chunks = crate::expand_type(ty)?.len();
            let mut values = Vec::with_capacity(chunks);
            if opcode == Opcode::Splat {
                let op = splat_op(lane_ty)?;
                for _ in 0..chunks {
                    values.push(body.add_op(wb, op, &[scalar], &[Type::V128]));
                }
            } else {
                let replace = replace_lane_op(lane_ty, 0)?;
                for i in 0..chunks {
                    let zero =
                        body.add_op(wb, Operator::V128Const { value: 0 }, &[], &[Type::V128]);
                    values.push(if i == 0 {
                        body.add_op(wb, replace, &[zero, scalar], &[Type::V128])
                    } else {
                        zero
                    });
                }
            }
            cx.bind_vector(result, normalize_vector(body, wb, ty, values)?);
        }
        // isplit: i128 -> (lo, hi) as two i64 results.
        Opcode::Isplit => {
            ensure!(src_ty == types::I128, "isplit of non-i128 {src_ty}");
            let (lo, hi) = cx.pair(arg)?;
            let results: Vec<ir::Value> = dfg.inst_results(inst).to_vec();
            ensure!(results.len() == 2, "isplit must have 2 results");
            cx.bind1(results[0], lo);
            cx.bind1(results[1], hi);
        }
        Opcode::Uextend | Opcode::Sextend => {
            let result = dfg.first_result(inst);
            let dst_ty = dfg.value_type(result);
            let signed = opcode == Opcode::Sextend;
            let v = cx.one(arg)?;
            // Normalize narrow sources within I32 first: canonical form is already
            // zero-extended, so uextend is a no-op; sextend re-signs in place.
            let (v, src_ty) = match src_ty {
                types::I8 | types::I16 => {
                    let n = if signed {
                        sign_extend_narrow(body, wb, v, src_ty)
                    } else {
                        mask_narrow(body, wb, v, src_ty)
                    };
                    if dst_ty == types::I32 {
                        cx.bind1(result, n);
                        return Ok(());
                    }
                    (n, types::I32)
                }
                types::I32 | types::I64 => (v, src_ty),
                other => unsupported!("extend from {other} unimplemented"),
            };
            // Widen to i64 if needed.
            let v64 = if src_ty == types::I32 {
                let op = if signed {
                    Operator::I64ExtendI32S
                } else {
                    Operator::I64ExtendI32U
                };
                body.add_op(wb, op, &[v], &[Type::I64])
            } else {
                v
            };
            match dst_ty {
                types::I64 => cx.bind1(result, v64),
                types::I128 => {
                    let hi = if signed {
                        let c63 =
                            body.add_op(wb, Operator::I64Const { value: 63 }, &[], &[Type::I64]);
                        body.add_op(wb, Operator::I64ShrS, &[v64, c63], &[Type::I64])
                    } else {
                        body.add_op(wb, Operator::I64Const { value: 0 }, &[], &[Type::I64])
                    };
                    cx.bind2(result, v64, hi);
                }
                other => unsupported!("extend to {other} unimplemented"),
            }
        }
        // ineg: wasm has no neg — emit 0 - v.
        Opcode::Ineg => {
            let result = dfg.first_result(inst);
            let rty = dfg.value_type(result);
            if rty.is_vector() {
                let op = match rty.lane_type() {
                    types::I8 => Operator::I8x16Neg,
                    types::I16 => Operator::I16x8Neg,
                    types::I32 => Operator::I32x4Neg,
                    types::I64 => Operator::I64x2Neg,
                    other => unsupported!("ineg vector lane type {other} is unsupported"),
                };
                let values = cx
                    .vector(arg)?
                    .into_iter()
                    .map(|value| body.add_op(wb, op, &[value], &[Type::V128]))
                    .collect();
                cx.bind_vector(result, normalize_vector(body, wb, rty, values)?);
                return Ok(());
            }
            if rty == types::I128 {
                let zero = body.add_op(wb, Operator::I64Const { value: 0 }, &[], &[Type::I64]);
                let v = cx.pair(arg)?;
                let (lo, hi) = crate::i128_lower::sub(body, wb, (zero, zero), v);
                cx.bind2(result, lo, hi);
                return Ok(());
            }
            let wty = map_type(rty)?;
            let v = cx.one(arg)?;
            let (zero_op, sub_op) = match wty {
                Type::I32 => (Operator::I32Const { value: 0 }, Operator::I32Sub),
                Type::I64 => (Operator::I64Const { value: 0 }, Operator::I64Sub),
                other => unsupported!("ineg of unsupported type {other}"),
            };
            let zero = body.add_op(wb, zero_op, &[], &[wty]);
            let mut wv = body.add_op(wb, sub_op, &[zero, v], &[wty]);
            if matches!(rty, types::I8 | types::I16) {
                wv = mask_narrow(body, wb, wv, rty);
            }
            cx.bind1(result, wv);
        }
        // bnot: wasm has no not — emit v ^ -1.
        Opcode::Bnot => {
            let result = dfg.first_result(inst);
            let rty = dfg.value_type(result);
            if rty.is_vector() {
                let values = cx
                    .vector(arg)?
                    .into_iter()
                    .map(|value| body.add_op(wb, Operator::V128Not, &[value], &[Type::V128]))
                    .collect();
                cx.bind_vector(result, normalize_vector(body, wb, rty, values)?);
                return Ok(());
            }
            if rty == types::I128 {
                let ones = body.add_op(
                    wb,
                    Operator::I64Const { value: u64::MAX },
                    &[],
                    &[Type::I64],
                );
                let v = cx.pair(arg)?;
                let (lo, hi) =
                    crate::i128_lower::logic(body, wb, Operator::I64Xor, v, (ones, ones));
                cx.bind2(result, lo, hi);
                return Ok(());
            }
            let wty = map_type(rty)?;
            let v = cx.one(arg)?;
            let (ones_op, xor_op) = match wty {
                Type::I32 => (Operator::I32Const { value: u32::MAX }, Operator::I32Xor),
                Type::I64 => (Operator::I64Const { value: u64::MAX }, Operator::I64Xor),
                other => unsupported!("bnot of unsupported type {other}"),
            };
            let ones = body.add_op(wb, ones_op, &[], &[wty]);
            let mut wv = body.add_op(wb, xor_op, &[v, ones], &[wty]);
            if matches!(rty, types::I8 | types::I16) {
                wv = mask_narrow(body, wb, wv, rty);
            }
            cx.bind1(result, wv);
        }
        Opcode::Ireduce => {
            let result = dfg.first_result(inst);
            let dst_ty = dfg.value_type(result);
            let low64 = if src_ty == types::I128 {
                cx.pair(arg)?.0
            } else {
                cx.one(arg)?
            };
            let wv = match (src_ty, dst_ty) {
                (types::I128, types::I64) => low64,
                (types::I128, types::I32) | (types::I64, types::I32) => {
                    body.add_op(wb, Operator::I32WrapI64, &[low64], &[Type::I32])
                }
                // Narrow destinations MUST re-canonicalize (mask): the source's high
                // bits are live data, not representation slack. (The battery's
                // cast_chain miscompile is what happens otherwise.)
                (types::I64, types::I8 | types::I16) => {
                    let w = body.add_op(wb, Operator::I32WrapI64, &[low64], &[Type::I32]);
                    mask_narrow(body, wb, w, dst_ty)
                }
                (types::I32, types::I8 | types::I16) => mask_narrow(body, wb, low64, dst_ty),
                (s, d) => unsupported!("ireduce {s} -> {d} unimplemented"),
            };
            cx.bind1(result, wv);
        }
        // --- Bit-counting ---
        Opcode::Clz | Opcode::Ctz | Opcode::Popcnt => {
            let result = dfg.first_result(inst);
            let rty = dfg.value_type(result);
            if rty == types::I128 {
                let (lo, hi) = cx.pair(arg)?;
                let (lo_r, hi_r) = match opcode {
                    // clz128 = hi==0 ? 64+clz(lo) : clz(hi); ctz mirrors on lo.
                    Opcode::Clz | Opcode::Ctz => {
                        let (primary, secondary, prim_op) = if opcode == Opcode::Clz {
                            (hi, lo, Operator::I64Clz)
                        } else {
                            (lo, hi, Operator::I64Ctz)
                        };
                        let p = body.add_op(wb, prim_op, &[primary], &[Type::I64]);
                        let s = body.add_op(wb, prim_op, &[secondary], &[Type::I64]);
                        let c64 =
                            body.add_op(wb, Operator::I64Const { value: 64 }, &[], &[Type::I64]);
                        let s64 = body.add_op(wb, Operator::I64Add, &[s, c64], &[Type::I64]);
                        let z = body.add_op(wb, Operator::I64Eqz, &[primary], &[Type::I32]);
                        let r = body.add_op(wb, Operator::Select, &[s64, p, z], &[Type::I64]);
                        let zero =
                            body.add_op(wb, Operator::I64Const { value: 0 }, &[], &[Type::I64]);
                        (r, zero)
                    }
                    _ => {
                        let a = body.add_op(wb, Operator::I64Popcnt, &[lo], &[Type::I64]);
                        let b = body.add_op(wb, Operator::I64Popcnt, &[hi], &[Type::I64]);
                        let r = body.add_op(wb, Operator::I64Add, &[a, b], &[Type::I64]);
                        let zero =
                            body.add_op(wb, Operator::I64Const { value: 0 }, &[], &[Type::I64]);
                        (r, zero)
                    }
                };
                cx.bind2(result, lo_r, hi_r);
                return Ok(());
            }
            let wty = map_type(rty)?;
            let v = cx.one(arg)?;
            let op = match (opcode, wty) {
                (Opcode::Clz, Type::I32) => Operator::I32Clz,
                (Opcode::Clz, Type::I64) => Operator::I64Clz,
                (Opcode::Ctz, Type::I32) => Operator::I32Ctz,
                (Opcode::Ctz, Type::I64) => Operator::I64Ctz,
                (Opcode::Popcnt, Type::I32) => Operator::I32Popcnt,
                (Opcode::Popcnt, Type::I64) => Operator::I64Popcnt,
                (o, t) => unsupported!("{o} on {t} unreachable"),
            };
            let mut wv = body.add_op(wb, op, &[v], &[wty]);
            // Narrow adjustments under canonical zext: clz counts 32-width bits
            // (subtract the pad); ctz of 0 must be the narrow width (OR in the
            // implicit top bit at position `width`); popcnt is already correct.
            if matches!(rty, types::I8 | types::I16) {
                let width = if rty == types::I8 { 8u32 } else { 16 };
                match opcode {
                    Opcode::Clz => {
                        let pad = body.add_op(
                            wb,
                            Operator::I32Const { value: 32 - width },
                            &[],
                            &[Type::I32],
                        );
                        wv = body.add_op(wb, Operator::I32Sub, &[wv, pad], &[Type::I32]);
                    }
                    Opcode::Ctz => {
                        let top = body.add_op(
                            wb,
                            Operator::I32Const { value: 1 << width },
                            &[],
                            &[Type::I32],
                        );
                        let v2 = body.add_op(wb, Operator::I32Or, &[v, top], &[Type::I32]);
                        wv = body.add_op(wb, Operator::I32Ctz, &[v2], &[Type::I32]);
                    }
                    _ => {}
                }
            }
            cx.bind1(result, wv);
        }
        // bitrev: classic mask-and-shift bit reversal (no wasm op).
        Opcode::Bitrev => {
            let result = dfg.first_result(inst);
            let rty = dfg.value_type(result);
            let v_in = cx.one(arg)?;
            let wv = match rty {
                types::I8 | types::I16 | types::I32 => {
                    let r = bitrev32(body, wb, v_in);
                    // Narrow: the reversed bits sit in the TOP of the 32-bit word.
                    match rty {
                        types::I8 => {
                            let c = body.add_op(
                                wb,
                                Operator::I32Const { value: 24 },
                                &[],
                                &[Type::I32],
                            );
                            body.add_op(wb, Operator::I32ShrU, &[r, c], &[Type::I32])
                        }
                        types::I16 => {
                            let c = body.add_op(
                                wb,
                                Operator::I32Const { value: 16 },
                                &[],
                                &[Type::I32],
                            );
                            body.add_op(wb, Operator::I32ShrU, &[r, c], &[Type::I32])
                        }
                        _ => r,
                    }
                }
                types::I64 => {
                    // reverse each half with bitrev32, then swap halves.
                    let c32 = body.add_op(wb, Operator::I64Const { value: 32 }, &[], &[Type::I64]);
                    let lo32 = body.add_op(wb, Operator::I32WrapI64, &[v_in], &[Type::I32]);
                    let hi64 = body.add_op(wb, Operator::I64ShrU, &[v_in, c32], &[Type::I64]);
                    let hi32 = body.add_op(wb, Operator::I32WrapI64, &[hi64], &[Type::I32]);
                    let rlo = bitrev32(body, wb, lo32);
                    let rhi = bitrev32(body, wb, hi32);
                    let rlo64 = body.add_op(wb, Operator::I64ExtendI32U, &[rlo], &[Type::I64]);
                    let rhi64 = body.add_op(wb, Operator::I64ExtendI32U, &[rhi], &[Type::I64]);
                    let top = body.add_op(wb, Operator::I64Shl, &[rlo64, c32], &[Type::I64]);
                    body.add_op(wb, Operator::I64Or, &[top, rhi64], &[Type::I64])
                }
                other => unsupported!("bitrev of {other} unimplemented"),
            };
            cx.bind1(result, wv);
        }

        // bswap: no wasm op — shift/mask expansion.
        Opcode::Bswap => {
            let result = dfg.first_result(inst);
            let rty = dfg.value_type(result);
            let v_in = cx.one(arg)?;
            let wv = match rty {
                types::I16 => {
                    // canonical zext: ((v >> 8) | (v << 8)) & 0xFFFF
                    let c8 = body.add_op(wb, Operator::I32Const { value: 8 }, &[], &[Type::I32]);
                    let hi = body.add_op(wb, Operator::I32ShrU, &[v_in, c8], &[Type::I32]);
                    let lo = body.add_op(wb, Operator::I32Shl, &[v_in, c8], &[Type::I32]);
                    let or = body.add_op(wb, Operator::I32Or, &[hi, lo], &[Type::I32]);
                    mask_narrow(body, wb, or, types::I16)
                }
                types::I32 => bswap32(body, wb, v_in),
                types::I64 => bswap64(body, wb, v_in),
                other => unsupported!("bswap of {other} unimplemented"),
            };
            cx.bind1(result, wv);
        }

        // --- Float unary ---
        Opcode::Fneg
        | Opcode::Fabs
        | Opcode::Sqrt
        | Opcode::Ceil
        | Opcode::Floor
        | Opcode::Trunc
        | Opcode::Nearest => {
            let result = dfg.first_result(inst);
            let result_ty = dfg.value_type(result);
            if result_ty.is_vector() {
                let op = vector_float_unary_operator(opcode, result_ty.lane_type())?;
                let values = cx
                    .vector(arg)?
                    .into_iter()
                    .map(|value| body.add_op(wb, op, &[value], &[Type::V128]))
                    .collect();
                cx.bind_vector(result, normalize_vector(body, wb, result_ty, values)?);
                return Ok(());
            }
            let wty = map_type(result_ty)?;
            let v = cx.one(arg)?;
            let op = match (opcode, wty) {
                (Opcode::Fneg, Type::F32) => Operator::F32Neg,
                (Opcode::Fneg, Type::F64) => Operator::F64Neg,
                (Opcode::Fabs, Type::F32) => Operator::F32Abs,
                (Opcode::Fabs, Type::F64) => Operator::F64Abs,
                (Opcode::Sqrt, Type::F32) => Operator::F32Sqrt,
                (Opcode::Sqrt, Type::F64) => Operator::F64Sqrt,
                (Opcode::Ceil, Type::F32) => Operator::F32Ceil,
                (Opcode::Ceil, Type::F64) => Operator::F64Ceil,
                (Opcode::Floor, Type::F32) => Operator::F32Floor,
                (Opcode::Floor, Type::F64) => Operator::F64Floor,
                (Opcode::Trunc, Type::F32) => Operator::F32Trunc,
                (Opcode::Trunc, Type::F64) => Operator::F64Trunc,
                (Opcode::Nearest, Type::F32) => Operator::F32Nearest,
                (Opcode::Nearest, Type::F64) => Operator::F64Nearest,
                (o, t) => unsupported!("float unary {o} on {t} unimplemented"),
            };
            let wv = body.add_op(wb, op, &[v], &[wty]);
            cx.bind1(result, wv);
        }

        // --- Float <-> int conversions ---
        Opcode::FcvtToSintSat | Opcode::FcvtToUintSat => {
            let result = dfg.first_result(inst);
            let dst = dfg.value_type(result);
            let signed = opcode == Opcode::FcvtToSintSat;
            let src_ty = cx.vty(arg);
            if src_ty.is_vector() {
                ensure!(
                    dst.is_vector(),
                    "vector saturating conversion requires a vector result"
                );
                let op = match (src_ty, dst, signed) {
                    (types::F32X4, types::I32X4, true) => Operator::I32x4TruncSatF32x4S,
                    (types::F32X4, types::I32X4, false) => Operator::I32x4TruncSatF32x4U,
                    (types::F64X2, types::I32X4, true) => Operator::I32x4TruncSatF64x2SZero,
                    (types::F64X2, types::I32X4, false) => Operator::I32x4TruncSatF64x2UZero,
                    _ => unsupported!(
                        "saturating vector conversion {src_ty} -> {dst} is unsupported"
                    ),
                };
                let value = cx.vector(arg)?[0];
                let converted = body.add_op(wb, op, &[value], &[Type::V128]);
                cx.bind_vector(result, normalize_vector(body, wb, dst, vec![converted])?);
                return Ok(());
            }
            if dst.is_vector() {
                unsupported!("scalar saturating conversion to vector type {dst} is unsupported");
            }
            let f64src = cx.vty(arg) == types::F64;
            let v = cx.one(arg)?;
            if dst == types::I128 {
                let value = lower_float_to_i128(body, wb, v, !f64src, signed)?;
                cx.bind2(result, value.0, value.1);
                return Ok(());
            }
            // Wide saturating truncation first (nontrapping-fptoint).
            let wide_dst = if dst == types::I64 {
                Type::I64
            } else {
                Type::I32
            };
            let op = match (wide_dst, f64src, signed) {
                (Type::I32, false, true) => Operator::I32TruncSatF32S,
                (Type::I32, false, false) => Operator::I32TruncSatF32U,
                (Type::I32, true, true) => Operator::I32TruncSatF64S,
                (Type::I32, true, false) => Operator::I32TruncSatF64U,
                (Type::I64, false, true) => Operator::I64TruncSatF32S,
                (Type::I64, false, false) => Operator::I64TruncSatF32U,
                (Type::I64, true, true) => Operator::I64TruncSatF64S,
                (Type::I64, true, false) => Operator::I64TruncSatF64U,
                _ => unreachable!(),
            };
            let mut wv = body.add_op(wb, op, &[v], &[wide_dst]);
            // Narrow destinations saturate at the NARROW range: clamp (with the
            // matching signedness — the unsigned wide result can exceed i32::MAX),
            // then re-canonicalize.
            if matches!(dst, types::I8 | types::I16) {
                if signed {
                    let (lo, hi) = if dst == types::I8 {
                        (-128, 127)
                    } else {
                        (-32768, 32767)
                    };
                    wv = clamp_i32(body, wb, wv, lo, hi);
                } else {
                    let hi = if dst == types::I8 { 255u32 } else { 65535 };
                    let hi_c = body.add_op(wb, Operator::I32Const { value: hi }, &[], &[Type::I32]);
                    let too_hi = body.add_op(wb, Operator::I32GtU, &[wv, hi_c], &[Type::I32]);
                    wv = body.add_op(wb, Operator::Select, &[hi_c, wv, too_hi], &[Type::I32]);
                }
                wv = mask_narrow(body, wb, wv, dst);
            } else if dst == types::I128 {
                unsupported!("fcvt to i128 is unsupported");
            }
            cx.bind1(result, wv);
        }
        Opcode::FcvtToSint | Opcode::FcvtToUint => {
            // Trapping form: wasm trunc traps on NaN/overflow exactly where CLIF does
            // (i32/i64 destinations only; Rust `as` uses the saturating form anyway).
            let result = dfg.first_result(inst);
            let dst = dfg.value_type(result);
            if dst == types::I128 {
                unsupported!("trapping fcvt to i128 is unsupported");
            }
            ensure!(
                matches!(dst, types::I32 | types::I64),
                "trapping fcvt to {dst} unimplemented"
            );
            let signed = opcode == Opcode::FcvtToSint;
            let f64src = cx.vty(arg) == types::F64;
            let v = cx.one(arg)?;
            let (op, wty) = match (dst, f64src, signed) {
                (types::I32, false, true) => (Operator::I32TruncF32S, Type::I32),
                (types::I32, false, false) => (Operator::I32TruncF32U, Type::I32),
                (types::I32, true, true) => (Operator::I32TruncF64S, Type::I32),
                (types::I32, true, false) => (Operator::I32TruncF64U, Type::I32),
                (types::I64, false, true) => (Operator::I64TruncF32S, Type::I64),
                (types::I64, false, false) => (Operator::I64TruncF32U, Type::I64),
                (types::I64, true, true) => (Operator::I64TruncF64S, Type::I64),
                (types::I64, true, false) => (Operator::I64TruncF64U, Type::I64),
                _ => unreachable!(),
            };
            let wv = body.add_op(wb, op, &[v], &[wty]);
            cx.bind1(result, wv);
        }
        Opcode::FcvtFromSint | Opcode::FcvtFromUint => {
            let result = dfg.first_result(inst);
            let dst_ty = dfg.value_type(result);
            let signed = opcode == Opcode::FcvtFromSint;
            let src_ty = cx.vty(arg);
            if src_ty.is_vector() {
                let op = match (src_ty, dst_ty, signed) {
                    (types::I32X4, types::F32X4, true) => Operator::F32x4ConvertI32x4S,
                    (types::I32X4, types::F32X4, false) => Operator::F32x4ConvertI32x4U,
                    (types::I32X4, types::F64X2, true) => Operator::F64x2ConvertLowI32x4S,
                    (types::I32X4, types::F64X2, false) => Operator::F64x2ConvertLowI32x4U,
                    _ => unsupported!("vector conversion {src_ty} -> {dst_ty} is unsupported"),
                };
                let value = cx.vector(arg)?[0];
                let converted = body.add_op(wb, op, &[value], &[Type::V128]);
                cx.bind_vector(result, normalize_vector(body, wb, dst_ty, vec![converted])?);
                return Ok(());
            }
            if dst_ty.is_vector() {
                unsupported!("scalar conversion to vector type {dst_ty} is unsupported");
            }
            if src_ty == types::I128 {
                ensure!(
                    matches!(dst_ty, types::F32 | types::F64),
                    "fcvt from i128 to {dst_ty} is unsupported"
                );
                let value =
                    lower_i128_to_float(body, wb, cx.pair(arg)?, signed, dst_ty == types::F32)?;
                cx.bind1(result, value);
                return Ok(());
            }
            let mut v = cx.one(arg)?;
            // Narrow sources: canonical zext is exact for unsigned; sign-extend first
            // for signed.
            let src_wide = match src_ty {
                types::I8 | types::I16 => {
                    if signed {
                        v = sign_extend_narrow(body, wb, v, src_ty);
                    }
                    Type::I32
                }
                other => map_type(other)?,
            };
            let dst_f64 = dst_ty == types::F64;
            let (op, wty) = match (dst_f64, src_wide, signed) {
                (false, Type::I32, true) => (Operator::F32ConvertI32S, Type::F32),
                (false, Type::I32, false) => (Operator::F32ConvertI32U, Type::F32),
                (false, Type::I64, true) => (Operator::F32ConvertI64S, Type::F32),
                (false, Type::I64, false) => (Operator::F32ConvertI64U, Type::F32),
                (true, Type::I32, true) => (Operator::F64ConvertI32S, Type::F64),
                (true, Type::I32, false) => (Operator::F64ConvertI32U, Type::F64),
                (true, Type::I64, true) => (Operator::F64ConvertI64S, Type::F64),
                (true, Type::I64, false) => (Operator::F64ConvertI64U, Type::F64),
                (_, t, _) => unsupported!("fcvt from {t} unimplemented"),
            };
            let wv = body.add_op(wb, op, &[v], &[wty]);
            cx.bind1(result, wv);
        }
        Opcode::Fpromote => {
            let result = dfg.first_result(inst);
            let dst_ty = dfg.value_type(result);
            if dst_ty.is_vector() {
                ensure!(
                    cx.vty(arg) == types::F32X4 && dst_ty == types::F64X2,
                    "unsupported vector fpromote {} -> {dst_ty}",
                    cx.vty(arg)
                );
                let value = body.add_op(
                    wb,
                    Operator::F64x2PromoteLowF32x4,
                    &cx.vector(arg)?,
                    &[Type::V128],
                );
                cx.bind_vector(result, vec![value]);
                return Ok(());
            }
            let v = cx.one(arg)?;
            let wv = body.add_op(wb, Operator::F64PromoteF32, &[v], &[Type::F64]);
            cx.bind1(result, wv);
        }
        Opcode::Fdemote => {
            let result = dfg.first_result(inst);
            let dst_ty = dfg.value_type(result);
            if dst_ty.is_vector() {
                ensure!(
                    cx.vty(arg) == types::F64X2 && dst_ty == types::F32X4,
                    "unsupported vector fdemote {} -> {dst_ty}",
                    cx.vty(arg)
                );
                let value = body.add_op(
                    wb,
                    Operator::F32x4DemoteF64x2Zero,
                    &cx.vector(arg)?,
                    &[Type::V128],
                );
                cx.bind_vector(result, vec![value]);
                return Ok(());
            }
            let v = cx.one(arg)?;
            let wv = body.add_op(wb, Operator::F32DemoteF64, &[v], &[Type::F32]);
            cx.bind1(result, wv);
        }

        other => unsupported!("unimplemented unary opcode {other}"),
    }
    Ok(())
}

/// 32-bit bit reversal: swap adjacent bits, pairs, nibbles, then bswap.
pub(super) fn bitrev32(
    body: &mut FunctionBody,
    wb: waffle::Block,
    v: waffle::Value,
) -> waffle::Value {
    let mut x = v;
    for (mask, sh) in [(0x5555_5555u32, 1u32), (0x3333_3333, 2), (0x0F0F_0F0F, 4)] {
        let m = body.add_op(wb, Operator::I32Const { value: mask }, &[], &[Type::I32]);
        let s = body.add_op(wb, Operator::I32Const { value: sh }, &[], &[Type::I32]);
        let lo = body.add_op(wb, Operator::I32And, &[x, m], &[Type::I32]);
        let lo_sh = body.add_op(wb, Operator::I32Shl, &[lo, s], &[Type::I32]);
        let hi_shr = body.add_op(wb, Operator::I32ShrU, &[x, s], &[Type::I32]);
        let hi = body.add_op(wb, Operator::I32And, &[hi_shr, m], &[Type::I32]);
        x = body.add_op(wb, Operator::I32Or, &[lo_sh, hi], &[Type::I32]);
    }
    bswap32(body, wb, x)
}

pub(super) fn bswap32(
    body: &mut FunctionBody,
    wb: waffle::Block,
    v: waffle::Value,
) -> waffle::Value {
    let c = |body: &mut FunctionBody, k: u32| {
        body.add_op(wb, Operator::I32Const { value: k }, &[], &[Type::I32])
    };
    let c24 = c(body, 24);
    let c8 = c(body, 8);
    let m1 = c(body, 0x0000_FF00);
    let m2 = c(body, 0x00FF_0000);
    let b0 = body.add_op(wb, Operator::I32Shl, &[v, c24], &[Type::I32]);
    let t1 = body.add_op(wb, Operator::I32Shl, &[v, c8], &[Type::I32]);
    let b1 = body.add_op(wb, Operator::I32And, &[t1, m2], &[Type::I32]);
    let t2 = body.add_op(wb, Operator::I32ShrU, &[v, c8], &[Type::I32]);
    let b2 = body.add_op(wb, Operator::I32And, &[t2, m1], &[Type::I32]);
    let b3 = body.add_op(wb, Operator::I32ShrU, &[v, c24], &[Type::I32]);
    let o1 = body.add_op(wb, Operator::I32Or, &[b0, b1], &[Type::I32]);
    let o2 = body.add_op(wb, Operator::I32Or, &[o1, b2], &[Type::I32]);
    body.add_op(wb, Operator::I32Or, &[o2, b3], &[Type::I32])
}

pub(super) fn bswap64(
    body: &mut FunctionBody,
    wb: waffle::Block,
    v: waffle::Value,
) -> waffle::Value {
    // Swap halves, then bswap32 each half in i64 form:
    // r = (bswap32(lo) << 32) | bswap32(hi)
    let c32 = body.add_op(wb, Operator::I64Const { value: 32 }, &[], &[Type::I64]);
    let lo32 = body.add_op(wb, Operator::I32WrapI64, &[v], &[Type::I32]);
    let hi64 = body.add_op(wb, Operator::I64ShrU, &[v, c32], &[Type::I64]);
    let hi32 = body.add_op(wb, Operator::I32WrapI64, &[hi64], &[Type::I32]);
    let slo = bswap32(body, wb, lo32);
    let shi = bswap32(body, wb, hi32);
    let slo64 = body.add_op(wb, Operator::I64ExtendI32U, &[slo], &[Type::I64]);
    let shi64 = body.add_op(wb, Operator::I64ExtendI32U, &[shi], &[Type::I64]);
    let hi_part = body.add_op(wb, Operator::I64Shl, &[slo64, c32], &[Type::I64]);
    body.add_op(wb, Operator::I64Or, &[hi_part, shi64], &[Type::I64])
}

/// Clamp an i32 value into [lo, hi] via two selects.
pub(super) fn clamp_i32(
    body: &mut FunctionBody,
    wb: waffle::Block,
    v: waffle::Value,
    lo: i32,
    hi: i32,
) -> waffle::Value {
    let lo_c = body.add_op(
        wb,
        Operator::I32Const { value: lo as u32 },
        &[],
        &[Type::I32],
    );
    let hi_c = body.add_op(
        wb,
        Operator::I32Const { value: hi as u32 },
        &[],
        &[Type::I32],
    );
    let too_lo = body.add_op(wb, Operator::I32LtS, &[v, lo_c], &[Type::I32]);
    let v1 = body.add_op(wb, Operator::Select, &[lo_c, v, too_lo], &[Type::I32]);
    let too_hi = body.add_op(wb, Operator::I32GtS, &[v1, hi_c], &[Type::I32]);
    body.add_op(wb, Operator::Select, &[hi_c, v1, too_hi], &[Type::I32])
}

/// Re-canonicalize a narrow (i8/i16) value to zero-extended form after an op that
/// can dirty its high bits.
pub(crate) fn mask_narrow(
    body: &mut FunctionBody,
    wb: waffle::Block,
    v: waffle::Value,
    ty: ir::Type,
) -> waffle::Value {
    let mask = if ty == types::I8 { 0xFF } else { 0xFFFF };
    let m = body.add_op(wb, Operator::I32Const { value: mask }, &[], &[Type::I32]);
    body.add_op(wb, Operator::I32And, &[v, m], &[Type::I32])
}

/// Sign-extend a canonical narrow value in place (i8/i16 within I32) via the wasm
/// sign-extension ops.
pub(super) fn sign_extend_narrow(
    body: &mut FunctionBody,
    wb: waffle::Block,
    v: waffle::Value,
    ty: ir::Type,
) -> waffle::Value {
    let op = if ty == types::I8 {
        Operator::I32Extend8S
    } else {
        Operator::I32Extend16S
    };
    body.add_op(wb, op, &[v], &[Type::I32])
}

pub(super) fn lower_binary(
    cx: &mut FnCx,
    body: &mut FunctionBody,
    wb: waffle::Block,
    inst: ir::Inst,
) -> Result<()> {
    let dfg = &cx.clif.dfg;
    let InstructionData::Binary { opcode, args } = dfg.insts[inst] else {
        unreachable!("lower_binary dispatched on a non-matching instruction")
    };
    let result = dfg.first_result(inst);
    let rty = dfg.value_type(result);

    if rty.is_vector() {
        lower_vector_binary(cx, body, wb, result, opcode, args)?;
        return Ok(());
    }

    // i128: pair legalization.
    if rty == types::I128 {
        if matches!(
            opcode,
            Opcode::UaddOverflow
                | Opcode::SaddOverflow
                | Opcode::UsubOverflow
                | Opcode::SsubOverflow
        ) {
            lower_i128_overflow(cx, body, wb, inst, opcode, args)?;
            return Ok(());
        }
        lower_binary_i128(cx, body, wb, result, opcode, args)?;
        return Ok(());
    }

    if matches!(
        opcode,
        Opcode::Smin
            | Opcode::Umin
            | Opcode::Smax
            | Opcode::Umax
            | Opcode::SaddSat
            | Opcode::UaddSat
            | Opcode::SsubSat
            | Opcode::UsubSat
            | Opcode::AvgRound
            | Opcode::Smulhi
            | Opcode::Umulhi
    ) {
        lower_scalar_integer_special(cx, body, wb, result, opcode, args)?;
        return Ok(());
    }

    let wty = map_type(rty)?;
    let mut a = cx.one(args[0])?;
    let mut b = cx.one(args[1])?;
    let narrow = matches!(rty, types::I8 | types::I16);
    let width = if rty == types::I8 { 8 } else { 16 };
    if narrow {
        a = mask_narrow(body, wb, a, rty);
        if !matches!(opcode, Opcode::Ishl | Opcode::Ushr | Opcode::Sshr) {
            b = mask_narrow(body, wb, b, rty);
        }
        if matches!(opcode, Opcode::Sdiv | Opcode::Srem | Opcode::Sshr) {
            a = sign_extend_narrow(body, wb, a, rty);
        }
        if matches!(opcode, Opcode::Sdiv | Opcode::Srem) {
            b = sign_extend_narrow(body, wb, b, rty);
        }
    }

    // Shifts: wasm requires amount type == operand type; CLIF allows a
    // mismatch. Both agree the amount is taken mod bit-width, so a plain
    // wrap/extend preserves semantics. (Rotates share the fixup.)
    let is_shift = matches!(
        opcode,
        Opcode::Ishl | Opcode::Ushr | Opcode::Sshr | Opcode::Rotl | Opcode::Rotr
    );
    // wasm rotates work at 32/64-bit width; a narrow rotate is NOT the i32 op.
    ensure!(
        !(matches!(opcode, Opcode::Rotl | Opcode::Rotr) && matches!(rty, types::I8 | types::I16)),
        "narrow-int rotate ({rty}) unimplemented"
    );
    let mut b = if is_shift {
        let amt_ty = map_type(cx.vty(args[1]))?;
        match (wty, amt_ty) {
            (Type::I32, Type::I64) => body.add_op(wb, Operator::I32WrapI64, &[b], &[Type::I32]),
            (Type::I64, Type::I32) => body.add_op(wb, Operator::I64ExtendI32U, &[b], &[Type::I64]),
            _ => b,
        }
    } else {
        b
    };
    if narrow && is_shift {
        let mask = body.add_op(
            wb,
            Operator::I32Const { value: width - 1 },
            &[],
            &[Type::I32],
        );
        b = body.add_op(wb, Operator::I32And, &[b, mask], &[Type::I32]);
    }

    let op = match (opcode, wty) {
        (Opcode::Iadd, Type::I32) => Operator::I32Add,
        (Opcode::Iadd, Type::I64) => Operator::I64Add,
        (Opcode::Isub, Type::I32) => Operator::I32Sub,
        (Opcode::Isub, Type::I64) => Operator::I64Sub,
        (Opcode::Imul, Type::I32) => Operator::I32Mul,
        (Opcode::Imul, Type::I64) => Operator::I64Mul,
        // wasm div/rem trap on zero (and INT_MIN/-1 for signed) exactly like CLIF.
        (Opcode::Udiv, Type::I32) => Operator::I32DivU,
        (Opcode::Udiv, Type::I64) => Operator::I64DivU,
        (Opcode::Sdiv, Type::I32) => Operator::I32DivS,
        (Opcode::Sdiv, Type::I64) => Operator::I64DivS,
        (Opcode::Urem, Type::I32) => Operator::I32RemU,
        (Opcode::Urem, Type::I64) => Operator::I64RemU,
        (Opcode::Srem, Type::I32) => Operator::I32RemS,
        (Opcode::Srem, Type::I64) => Operator::I64RemS,
        (Opcode::Band, Type::I32) => Operator::I32And,
        (Opcode::Band, Type::I64) => Operator::I64And,
        (Opcode::Bor, Type::I32) => Operator::I32Or,
        (Opcode::Bor, Type::I64) => Operator::I64Or,
        (Opcode::Bxor, Type::I32) => Operator::I32Xor,
        (Opcode::Bxor, Type::I64) => Operator::I64Xor,
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
        (Opcode::Fmin, Type::F32) => Operator::F32Min,
        (Opcode::Fmin, Type::F64) => Operator::F64Min,
        (Opcode::Fmax, Type::F32) => Operator::F32Max,
        (Opcode::Fmax, Type::F64) => Operator::F64Max,
        (Opcode::Fcopysign, Type::F32) => Operator::F32Copysign,
        (Opcode::Fcopysign, Type::F64) => Operator::F64Copysign,
        (Opcode::Fadd, Type::F32) => Operator::F32Add,
        (Opcode::Fadd, Type::F64) => Operator::F64Add,
        (Opcode::Fsub, Type::F32) => Operator::F32Sub,
        (Opcode::Fsub, Type::F64) => Operator::F64Sub,
        (Opcode::Fmul, Type::F32) => Operator::F32Mul,
        (Opcode::Fmul, Type::F64) => Operator::F64Mul,
        (Opcode::Fdiv, Type::F32) => Operator::F32Div,
        (Opcode::Fdiv, Type::F64) => Operator::F64Div,
        (op, ty) => unsupported!("unimplemented binary opcode {op} on {ty}"),
    };
    let mut wv = body.add_op(wb, op, &[a, b], &[wty]);
    // Re-canonicalize narrow results whose op can dirty high bits.
    if narrow {
        wv = mask_narrow(body, wb, wv, rty);
    }
    cx.bind1(result, wv);
    Ok(())
}
