use crate::waffle as waffle;
use crate::error::{Context, Result};
use crate::{ensure, unsupported};
use cranelift_codegen::ir::{self, InstructionData, Opcode, types};
use waffle::{FunctionBody, MemoryArg, Operator, Type};

use super::*;
use crate::bridge::FnCx;
use crate::map_type;

/// The pointer-width tripwire: addresses must be CLIF i32. CLIF captured from a
/// 64-bit target carries i64 addresses; it must fail loudly here, never truncate
/// (see docs/plans/cranelift-wasm-backend.md §8 on silent 32-bit miscompiles).
pub(super) fn lower_addr(cx: &FnCx, addr: ir::Value) -> Result<waffle::Value> {
    let ty = cx.vty(addr);
    ensure!(
        ty == types::I32,
        "address has CLIF type {ty}, expected i32 — was this CLIF built for a 64-bit pointer target?"
    );
    cx.one(addr)
}

pub(super) fn mem_arg(cx: &FnCx, offset: ir::immediates::Offset32) -> Result<MemoryArg> {
    let off: i32 = offset.into();
    mem_arg_at(cx, off)
}

pub(super) fn mem_arg_at(cx: &FnCx, off: i32) -> Result<MemoryArg> {
    ensure!(
        off >= 0,
        "negative load/store offset {off} is unsupported (wasm offsets are unsigned)"
    );
    Ok(MemoryArg {
        // Byte-alignment hint: always correct, never a trap; tuning comes later.
        align: 0,
        offset: off as u32,
        memory: cx.m.mem0,
    })
}

pub(super) fn ensure_shared_memory(cx: &FnCx, operation: &str) -> Result<()> {
    ensure!(
        cx.m.shared_memory,
        "atomic operation {operation} requires translation with shared_memory_max_pages enabled"
    );
    Ok(())
}

pub(super) fn atomic_mem_arg(cx: &FnCx, ty: types::Type) -> Result<MemoryArg> {
    let align = match ty {
        types::I8 => 0,
        types::I16 => 1,
        types::I32 => 2,
        types::I64 => 3,
        other => unsupported!("atomic access of {other} is unsupported"),
    };
    Ok(MemoryArg {
        align,
        offset: 0,
        memory: cx.m.mem0,
    })
}

pub(super) fn lower_symbol_value(
    cx: &mut FnCx,
    body: &mut FunctionBody,
    wb: waffle::Block,
    inst: ir::Inst,
) -> Result<()> {
    let dfg = &cx.clif.dfg;
    let InstructionData::UnaryGlobalValue {
        opcode: Opcode::SymbolValue,
        global_value,
    } = dfg.insts[inst]
    else {
        unreachable!("lower_symbol_value dispatched on a non-matching instruction")
    };
    use cranelift_codegen::ir::GlobalValueData;
    let result = dfg.first_result(inst);
    ensure!(
        dfg.value_type(result) == types::I32,
        "symbol_value result must be i32 (wasm32 pointer), got {} — 64-bit-target CLIF?",
        dfg.value_type(result)
    );
    let gvd = &cx.clif.global_values[global_value];
    let GlobalValueData::Symbol {
        name, offset, tls, ..
    } = gvd
    else {
        unsupported!(
            "symbol_value of {global_value} is unsupported: only symbol global values are lowered, not {gvd:?}"
        );
    };
    if *tls {
        unsupported!(
            "symbol_value of TLS symbol {global_value} is unsupported: wasm has no thread-local storage model"
        );
    }
    let ir::ExternalName::User(r) = name else {
        unsupported!("unsupported data symbol name {name:?}");
    };
    let user = cx
        .clif
        .params
        .user_named_funcs()
        .get(*r)
        .context("dangling userextname on data symbol")?;
    ensure!(
        user.namespace == 1,
        "data symbol has namespace {} (expected 1)",
        user.namespace
    );
    let off: i64 = (*offset).into();
    let marker =
        cx.m.object_markers
            .data
            .get(&(user.index, off))
            .with_context(|| format!("no marker for data ordinal {} offset {off}", user.index))?;
    let wv = body.add_op(
        wb,
        Operator::GlobalGet {
            global_index: *marker,
        },
        &[],
        &[Type::I32],
    );
    cx.bind1(result, wv);
    Ok(())
}

pub(super) fn lower_tls_value(cx: &FnCx, inst: ir::Inst) -> Result<()> {
    let InstructionData::UnaryGlobalValue {
        opcode: Opcode::TlsValue,
        global_value,
    } = cx.clif.dfg.insts[inst]
    else {
        unreachable!("lower_tls_value dispatched on a non-matching instruction")
    };
    unsupported!(
        "tls_value of {global_value} is unsupported: wasm has no thread-local storage model, and lowering it to ordinary data would silently share one value between threads"
    )
}

pub(super) fn lower_load(
    cx: &mut FnCx,
    body: &mut FunctionBody,
    wb: waffle::Block,
    inst: ir::Inst,
) -> Result<()> {
    let dfg = &cx.clif.dfg;
    let InstructionData::Load {
        opcode,
        arg,
        flags,
        offset,
    } = dfg.insts[inst]
    else {
        unreachable!("lower_load dispatched on a non-matching instruction")
    };
    let big_endian = cx.clif.dfg.mem_flags[flags].explicit_endianness() == Some(ir::Endianness::Big);
    let addr = lower_addr(cx, arg)?;
    let result = dfg.first_result(inst);
    let rty = dfg.value_type(result);
    ensure!(!big_endian || !rty.is_vector(), "big-endian vector load is unsupported");
    if rty.is_vector() && opcode == Opcode::Load {
        ensure!(!big_endian, "big-endian vector load is unsupported");
        let bits = rty.bits();
        let values = if bits < 128 {
            let scalar_ty = if bits <= 32 { Type::I32 } else { Type::I64 };
            let op = match bits {
                16 => Operator::I32Load16U {
                    memory: mem_arg(cx, offset)?,
                },
                32 => Operator::I32Load {
                    memory: mem_arg(cx, offset)?,
                },
                64 => Operator::I64Load {
                    memory: mem_arg(cx, offset)?,
                },
                _ => unsupported!("vector load width {bits} is unsupported"),
            };
            let scalar = body.add_op(wb, op, &[addr], &[scalar_ty]);
            let zero = body.add_op(wb, Operator::V128Const { value: 0 }, &[], &[Type::V128]);
            let insert = replace_lane_op(
                if bits == 16 {
                    types::I16
                } else if bits == 32 {
                    types::I32
                } else {
                    types::I64
                },
                0,
            )?;
            vec![body.add_op(wb, insert, &[zero, scalar], &[Type::V128])]
        } else {
            let chunks = crate::expand_type(rty)?.len();
            let base_offset: i32 = offset.into();
            let mut values = Vec::with_capacity(chunks);
            for i in 0..chunks {
                let lane_offset = base_offset
                    .checked_add(
                        (i as i32)
                            .checked_mul(16)
                            .context("vector load offset overflow")?,
                    )
                    .context("vector load offset overflow")?;
                let memory = mem_arg_at(cx, lane_offset)?;
                values.push(body.add_op(wb, Operator::V128Load { memory }, &[addr], &[Type::V128]));
            }
            values
        };
        cx.bind_vector(result, normalize_vector(body, wb, rty, values)?);
        return Ok(());
    }
    if rty == types::I128 && opcode == Opcode::Load {
        let off: i32 = offset.into();
        ensure!(off >= 0, "negative i128 load offset");
        let m0 = mem_arg(cx, offset)?;
        let m8 = mem_arg_at(cx, off.checked_add(8).context("i128 load offset overflow")?)?;
        let lo = body.add_op(wb, Operator::I64Load { memory: m0 }, &[addr], &[Type::I64]);
        let hi = body.add_op(wb, Operator::I64Load { memory: m8 }, &[addr], &[Type::I64]);
        if big_endian {
            cx.bind2(result, crate::ops::int::bswap64(body, wb, hi), crate::ops::int::bswap64(body, wb, lo));
        } else {
            cx.bind2(result, lo, hi);
        }
        return Ok(());
    }
    let wty = if rty.is_vector() {
        Type::V128
    } else {
        map_type(rty)?
    };
    let memory = mem_arg(cx, offset)?;
    let op = match (opcode, rty) {
        (Opcode::Uload8x8, types::I16X8) => Operator::V128Load8x8U { memory },
        (Opcode::Sload8x8, types::I16X8) => Operator::V128Load8x8S { memory },
        (Opcode::Uload16x4, types::I32X4) => Operator::V128Load16x4U { memory },
        (Opcode::Sload16x4, types::I32X4) => Operator::V128Load16x4S { memory },
        (Opcode::Uload32x2, types::I64X2) => Operator::V128Load32x2U { memory },
        (Opcode::Sload32x2, types::I64X2) => Operator::V128Load32x2S { memory },
        // Narrow plain loads produce the canonical zero-extended form.
        (Opcode::Load, types::I8) => Operator::I32Load8U { memory },
        (Opcode::Load, types::I16 | types::F16) => Operator::I32Load16U { memory },
        (Opcode::Load, types::I32) => Operator::I32Load { memory },
        (Opcode::Load, types::I64) => Operator::I64Load { memory },
        (Opcode::Load, types::F32) => Operator::F32Load { memory },
        (Opcode::Load, types::F64) => Operator::F64Load { memory },
        // Explicit widening loads.
        (Opcode::Uload8, types::I32) => Operator::I32Load8U { memory },
        (Opcode::Sload8, types::I32) if big_endian => Operator::I32Load8U { memory },
        (Opcode::Sload8, types::I32) => Operator::I32Load8S { memory },
        (Opcode::Uload16, types::I32) => Operator::I32Load16U { memory },
        (Opcode::Sload16, types::I32) if big_endian => Operator::I32Load16U { memory },
        (Opcode::Sload16, types::I32) => Operator::I32Load16S { memory },
        (Opcode::Uload8, types::I64) => Operator::I64Load8U { memory },
        (Opcode::Sload8, types::I64) if big_endian => Operator::I64Load8U { memory },
        (Opcode::Sload8, types::I64) => Operator::I64Load8S { memory },
        (Opcode::Uload16, types::I64) => Operator::I64Load16U { memory },
        (Opcode::Sload16, types::I64) if big_endian => Operator::I64Load16U { memory },
        (Opcode::Sload16, types::I64) => Operator::I64Load16S { memory },
        (Opcode::Uload32, types::I64) => Operator::I64Load32U { memory },
        (Opcode::Sload32, types::I64) if big_endian => Operator::I64Load32U { memory },
        (Opcode::Sload32, types::I64) => Operator::I64Load32S { memory },
        (op, ty) => unsupported!("unimplemented load `{op}` of type {ty}"),
    };
    ensure!(!big_endian || !rty.is_vector(), "big-endian vector load is unsupported");
    let wv = body.add_op(wb, op, &[addr], &[wty]);
    let wv = if big_endian {
        match (opcode, rty) {
            (Opcode::Load, types::I16 | types::F16) | (Opcode::Uload16, types::I32 | types::I64) | (Opcode::Sload16, types::I32 | types::I64) => {
                let swapped = crate::ops::int::bswap32(body, wb, wv);
                let shift = body.add_op(wb, Operator::I32Const { value: 16 }, &[], &[Type::I32]);
                let narrow = body.add_op(wb, Operator::I32ShrU, &[swapped, shift], &[Type::I32]);
                let narrow = if opcode == Opcode::Sload16 {
                    let shift = body.add_op(wb, Operator::I32Const { value: 16 }, &[], &[Type::I32]);
                    let left = body.add_op(wb, Operator::I32Shl, &[narrow, shift], &[Type::I32]);
                    let shift = body.add_op(wb, Operator::I32Const { value: 16 }, &[], &[Type::I32]);
                    body.add_op(wb, Operator::I32ShrS, &[left, shift], &[Type::I32])
                } else { narrow };
                if rty == types::I64 {
                    body.add_op(wb, if opcode == Opcode::Sload16 { Operator::I64ExtendI32S } else { Operator::I64ExtendI32U }, &[narrow], &[Type::I64])
                } else { narrow }
            }
            (Opcode::Load, types::I32) => crate::ops::int::bswap32(body, wb, wv),
            (Opcode::Uload8, types::I64) => wv,
            (Opcode::Sload8, types::I64) => {
                let low = body.add_op(wb, Operator::I32WrapI64, &[wv], &[Type::I32]);
                let shift = body.add_op(wb, Operator::I32Const { value: 24 }, &[], &[Type::I32]);
                let left = body.add_op(wb, Operator::I32Shl, &[low, shift], &[Type::I32]);
                let shift = body.add_op(wb, Operator::I32Const { value: 24 }, &[], &[Type::I32]);
                let signed = body.add_op(wb, Operator::I32ShrS, &[left, shift], &[Type::I32]);
                body.add_op(wb, Operator::I64ExtendI32S, &[signed], &[Type::I64])
            }
            (Opcode::Load, types::I64)
            => crate::ops::int::bswap64(body, wb, wv),
            (Opcode::Uload32, types::I64) | (Opcode::Sload32, types::I64) => {
                let low = body.add_op(wb, Operator::I32WrapI64, &[wv], &[Type::I32]);
                let swapped = crate::ops::int::bswap32(body, wb, low);
                body.add_op(wb, if opcode == Opcode::Sload32 { Operator::I64ExtendI32S } else { Operator::I64ExtendI32U }, &[swapped], &[Type::I64])
            }
            (Opcode::Load, types::I8) | (Opcode::Uload8, types::I32) => wv,
            (Opcode::Sload8, types::I32) => {
                let shift = body.add_op(wb, Operator::I32Const { value: 24 }, &[], &[Type::I32]);
                let left = body.add_op(wb, Operator::I32Shl, &[wv, shift], &[Type::I32]);
                let shift = body.add_op(wb, Operator::I32Const { value: 24 }, &[], &[Type::I32]);
                body.add_op(wb, Operator::I32ShrS, &[left, shift], &[Type::I32])
            }
            (Opcode::Load, types::F32) => {
                let bits = body.add_op(wb, Operator::I32ReinterpretF32, &[wv], &[Type::I32]);
                let bits = crate::ops::int::bswap32(body, wb, bits);
                body.add_op(wb, Operator::F32ReinterpretI32, &[bits], &[Type::F32])
            }
            (Opcode::Load, types::F64) => {
                let bits = body.add_op(wb, Operator::I64ReinterpretF64, &[wv], &[Type::I64]);
                let bits = crate::ops::int::bswap64(body, wb, bits);
                body.add_op(wb, Operator::F64ReinterpretI64, &[bits], &[Type::F64])
            }
            _ => unsupported!("big-endian load `{opcode}` of type {rty} is unsupported"),
        }
    } else { wv };
    if rty.is_vector() {
        cx.bind_vector(result, vec![wv]);
    } else {
        cx.bind1(result, wv);
    }
    Ok(())
}

pub(super) fn lower_store(
    cx: &mut FnCx,
    body: &mut FunctionBody,
    wb: waffle::Block,
    inst: ir::Inst,
) -> Result<()> {
    let dfg = &cx.clif.dfg;
    let InstructionData::Store {
        opcode,
        args,
        flags,
        offset,
    } = dfg.insts[inst]
    else {
        unreachable!("lower_store dispatched on a non-matching instruction")
    };
    let big_endian = cx.clif.dfg.mem_flags[flags].explicit_endianness() == Some(ir::Endianness::Big);
    ensure!(!big_endian || !cx.vty(args[0]).is_vector(), "big-endian vector store is unsupported");
    if cx.vty(args[0]).is_vector() && opcode == Opcode::Store {
        ensure!(!big_endian, "big-endian vector store is unsupported");
        let ty = cx.vty(args[0]);
        let addr = lower_addr(cx, args[1])?;
        let vector = cx.vector(args[0])?;
        let bits = ty.bits();
        if bits < 128 {
            let extract = extract_lane_op(
                if bits == 16 {
                    types::I16
                } else if bits == 32 {
                    types::I32
                } else {
                    types::I64
                },
                0,
            )?;
            let scalar_ty = if bits <= 32 { Type::I32 } else { Type::I64 };
            let scalar = body.add_op(wb, extract, &[vector[0]], &[scalar_ty]);
            let memory = mem_arg(cx, offset)?;
            let op = match bits {
                16 => Operator::I32Store16 { memory },
                32 => Operator::I32Store { memory },
                64 => Operator::I64Store { memory },
                _ => unsupported!("vector store width {bits} is unsupported"),
            };
            body.add_op(wb, op, &[addr, scalar], &[]);
        } else {
            let base_offset: i32 = offset.into();
            for (i, &value) in vector.iter().enumerate() {
                let lane_offset = base_offset
                    .checked_add(
                        (i as i32)
                            .checked_mul(16)
                            .context("vector store offset overflow")?,
                    )
                    .context("vector store offset overflow")?;
                let memory = mem_arg_at(cx, lane_offset)?;
                body.add_op(wb, Operator::V128Store { memory }, &[addr, value], &[]);
            }
        }
        return Ok(());
    }
    // CLIF: store v, p, offset — args are [value, addr]; wasm order is [addr, value].
    if cx.vty(args[0]) == types::I128 && opcode == Opcode::Store {
        let (lo, hi) = cx.pair(args[0])?;
        let addr = lower_addr(cx, args[1])?;
        let off: i32 = offset.into();
        ensure!(off >= 0, "negative i128 store offset");
        let m0 = mem_arg(cx, offset)?;
        let m8 = mem_arg_at(
            cx,
            off.checked_add(8).context("i128 store offset overflow")?,
        )?;
        if big_endian {
            let lo_swapped = crate::ops::int::bswap64(body, wb, lo);
            let hi_swapped = crate::ops::int::bswap64(body, wb, hi);
            body.add_op(wb, Operator::I64Store { memory: m0 }, &[addr, hi_swapped], &[]);
            body.add_op(wb, Operator::I64Store { memory: m8 }, &[addr, lo_swapped], &[]);
        } else {
            body.add_op(wb, Operator::I64Store { memory: m0 }, &[addr, lo], &[]);
            body.add_op(wb, Operator::I64Store { memory: m8 }, &[addr, hi], &[]);
        }
        return Ok(());
    }
    let value = cx.one(args[0])?;
    let addr = lower_addr(cx, args[1])?;
    let memory = mem_arg(cx, offset)?;
    let vty = cx.vty(args[0]);
    let value = if big_endian { match (opcode, vty) {
        (Opcode::Store, types::I8) | (Opcode::Istore8, types::I32 | types::I64) => value,
        (Opcode::Store, types::I16 | types::F16) | (Opcode::Istore16, types::I32 | types::I64) => {
            let bits = if vty == types::I64 { body.add_op(wb, Operator::I32WrapI64, &[value], &[Type::I32]) } else { value };
            let swapped = crate::ops::int::bswap32(body, wb, bits);
            let shift = body.add_op(wb, Operator::I32Const { value: 16 }, &[], &[Type::I32]);
            let swapped = body.add_op(wb, Operator::I32ShrU, &[swapped, shift], &[Type::I32]);
            if vty == types::I64 { body.add_op(wb, Operator::I64ExtendI32U, &[swapped], &[Type::I64]) } else { swapped }
        }
        (Opcode::Istore32, types::I64) => {
            let bits = body.add_op(wb, Operator::I32WrapI64, &[value], &[Type::I32]);
            let swapped = crate::ops::int::bswap32(body, wb, bits);
            body.add_op(wb, Operator::I64ExtendI32U, &[swapped], &[Type::I64])
        }
        (_, types::I32) => crate::ops::int::bswap32(body, wb, value),
        (_, types::I64) => crate::ops::int::bswap64(body, wb, value),
        (Opcode::Store, types::F32) => { let bits = body.add_op(wb, Operator::I32ReinterpretF32, &[value], &[Type::I32]); let bits = crate::ops::int::bswap32(body, wb, bits); body.add_op(wb, Operator::F32ReinterpretI32, &[bits], &[Type::F32]) },
        (Opcode::Store, types::F64) => { let bits = body.add_op(wb, Operator::I64ReinterpretF64, &[value], &[Type::I64]); let bits = crate::ops::int::bswap64(body, wb, bits); body.add_op(wb, Operator::F64ReinterpretI64, &[bits], &[Type::F64]) },
        _ => value,
    }} else { value };
    let op = match (opcode, vty) {
        (Opcode::Store, types::I8) => Operator::I32Store8 { memory },
        (Opcode::Store, types::I16 | types::F16) => Operator::I32Store16 { memory },
        (Opcode::Store, types::I32) => Operator::I32Store { memory },
        (Opcode::Store, types::I64) => Operator::I64Store { memory },
        (Opcode::Store, types::F32) => Operator::F32Store { memory },
        (Opcode::Store, types::F64) => Operator::F64Store { memory },
        // Truncating stores of wider values.
        (Opcode::Istore8, types::I32) => Operator::I32Store8 { memory },
        (Opcode::Istore16, types::I32) => Operator::I32Store16 { memory },
        (Opcode::Istore8, types::I64) => Operator::I64Store8 { memory },
        (Opcode::Istore16, types::I64) => Operator::I64Store16 { memory },
        (Opcode::Istore32, types::I64) => Operator::I64Store32 { memory },
        (op, ty) => unsupported!("unimplemented store `{op}` of type {ty}"),
    };
    body.add_op(wb, op, &[addr, value], &[]);
    Ok(())
}
