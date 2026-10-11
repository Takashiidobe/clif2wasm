use crate::waffle as waffle;
use crate::error::Result;
use crate::unsupported;
use cranelift_codegen::ir::{self, InstructionData, Opcode, types};
use waffle::{FunctionBody, Operator};

use super::*;
use crate::bridge::FnCx;
use crate::map_type;

pub(super) fn lower_atomic_load(
    cx: &mut FnCx,
    body: &mut FunctionBody,
    wb: waffle::Block,
    inst: ir::Inst,
) -> Result<()> {
    let dfg = &cx.clif.dfg;
    let InstructionData::LoadNoOffset {
        opcode: Opcode::AtomicLoad,
        arg,
        ..
    } = dfg.insts[inst]
    else {
        unreachable!("lower_atomic_load dispatched on a non-matching instruction")
    };
    ensure_shared_memory(cx, "atomic_load")?;
    let result = dfg.first_result(inst);
    let ty = dfg.value_type(result);
    let memory = atomic_mem_arg(cx, ty)?;
    let op = match ty {
        types::I8 => Operator::I32AtomicLoad8U { memory },
        types::I16 => Operator::I32AtomicLoad16U { memory },
        types::I32 => Operator::I32AtomicLoad { memory },
        types::I64 => Operator::I64AtomicLoad { memory },
        other => unsupported!("atomic_load of {other} is unsupported"),
    };
    let addr = lower_addr(cx, arg)?;
    let value = body.add_op(wb, op, &[addr], &[map_type(ty)?]);
    cx.bind1(result, value);
    Ok(())
}

pub(super) fn lower_atomic_store(
    cx: &mut FnCx,
    body: &mut FunctionBody,
    wb: waffle::Block,
    inst: ir::Inst,
) -> Result<()> {
    let dfg = &cx.clif.dfg;
    let InstructionData::StoreNoOffset {
        opcode: Opcode::AtomicStore,
        args,
        ..
    } = dfg.insts[inst]
    else {
        unreachable!("lower_atomic_store dispatched on a non-matching instruction")
    };
    ensure_shared_memory(cx, "atomic_store")?;
    let value_ty = cx.vty(args[0]);
    let memory = atomic_mem_arg(cx, value_ty)?;
    let op = match value_ty {
        types::I8 => Operator::I32AtomicStore8 { memory },
        types::I16 => Operator::I32AtomicStore16 { memory },
        types::I32 => Operator::I32AtomicStore { memory },
        types::I64 => Operator::I64AtomicStore { memory },
        other => unsupported!("atomic_store of {other} is unsupported"),
    };
    let value = cx.one(args[0])?;
    let addr = lower_addr(cx, args[1])?;
    body.add_op(wb, op, &[addr, value], &[]);
    Ok(())
}

pub(super) fn lower_atomic_rmw(
    cx: &mut FnCx,
    body: &mut FunctionBody,
    wb: waffle::Block,
    inst: ir::Inst,
) -> Result<()> {
    let dfg = &cx.clif.dfg;
    let InstructionData::AtomicRmw {
        opcode: Opcode::AtomicRmw,
        args,
        op: rmw_op,
        ..
    } = dfg.insts[inst]
    else {
        unreachable!("lower_atomic_rmw dispatched on a non-matching instruction")
    };
    use cranelift_codegen::ir::AtomicRmwOp;
    ensure_shared_memory(cx, "atomic_rmw")?;
    let result = dfg.first_result(inst);
    let ty = dfg.value_type(result);
    let memory = atomic_mem_arg(cx, ty)?;
    let narrow = matches!(ty, types::I8 | types::I16);
    let op = match (ty, rmw_op) {
        (types::I8, AtomicRmwOp::Add) => Operator::I32AtomicRmw8AddU { memory },
        (types::I8, AtomicRmwOp::Sub) => Operator::I32AtomicRmw8SubU { memory },
        (types::I8, AtomicRmwOp::And) => Operator::I32AtomicRmw8AndU { memory },
        (types::I8, AtomicRmwOp::Or) => Operator::I32AtomicRmw8OrU { memory },
        (types::I8, AtomicRmwOp::Xor) => Operator::I32AtomicRmw8XorU { memory },
        (types::I8, AtomicRmwOp::Xchg) => Operator::I32AtomicRmw8XchgU { memory },
        (types::I16, AtomicRmwOp::Add) => Operator::I32AtomicRmw16AddU { memory },
        (types::I16, AtomicRmwOp::Sub) => Operator::I32AtomicRmw16SubU { memory },
        (types::I16, AtomicRmwOp::And) => Operator::I32AtomicRmw16AndU { memory },
        (types::I16, AtomicRmwOp::Or) => Operator::I32AtomicRmw16OrU { memory },
        (types::I16, AtomicRmwOp::Xor) => Operator::I32AtomicRmw16XorU { memory },
        (types::I16, AtomicRmwOp::Xchg) => Operator::I32AtomicRmw16XchgU { memory },
        (types::I32, AtomicRmwOp::Add) => Operator::I32AtomicRmwAdd { memory },
        (types::I32, AtomicRmwOp::Sub) => Operator::I32AtomicRmwSub { memory },
        (types::I32, AtomicRmwOp::And) => Operator::I32AtomicRmwAnd { memory },
        (types::I32, AtomicRmwOp::Or) => Operator::I32AtomicRmwOr { memory },
        (types::I32, AtomicRmwOp::Xor) => Operator::I32AtomicRmwXor { memory },
        (types::I32, AtomicRmwOp::Xchg) => Operator::I32AtomicRmwXchg { memory },
        (types::I64, AtomicRmwOp::Add) => Operator::I64AtomicRmwAdd { memory },
        (types::I64, AtomicRmwOp::Sub) => Operator::I64AtomicRmwSub { memory },
        (types::I64, AtomicRmwOp::And) => Operator::I64AtomicRmwAnd { memory },
        (types::I64, AtomicRmwOp::Or) => Operator::I64AtomicRmwOr { memory },
        (types::I64, AtomicRmwOp::Xor) => Operator::I64AtomicRmwXor { memory },
        (types::I64, AtomicRmwOp::Xchg) => Operator::I64AtomicRmwXchg { memory },
        (_, other) => {
            unsupported!("atomic_rmw operation {other} on {ty} has no direct wasm atomic opcode")
        }
    };
    let addr = lower_addr(cx, args[0])?;
    let operand = cx.one(args[1])?;
    let value = body.add_op(wb, op, &[addr, operand], &[map_type(ty)?]);
    let value = if narrow {
        mask_narrow(body, wb, value, ty)
    } else {
        value
    };
    cx.bind1(result, value);
    Ok(())
}

pub(super) fn lower_atomic_cas(
    cx: &mut FnCx,
    body: &mut FunctionBody,
    wb: waffle::Block,
    inst: ir::Inst,
) -> Result<()> {
    let dfg = &cx.clif.dfg;
    let InstructionData::AtomicCas {
        opcode: Opcode::AtomicCas,
        args,
        ..
    } = dfg.insts[inst]
    else {
        unreachable!("lower_atomic_cas dispatched on a non-matching instruction")
    };
    ensure_shared_memory(cx, "atomic_cas")?;
    let result = dfg.first_result(inst);
    let ty = dfg.value_type(result);
    let memory = atomic_mem_arg(cx, ty)?;
    let op = match ty {
        types::I8 => Operator::I32AtomicRmw8CmpxchgU { memory },
        types::I16 => Operator::I32AtomicRmw16CmpxchgU { memory },
        types::I32 => Operator::I32AtomicRmwCmpxchg { memory },
        types::I64 => Operator::I64AtomicRmwCmpxchg { memory },
        other => unsupported!("atomic_cas of {other} is unsupported"),
    };
    let addr = lower_addr(cx, args[0])?;
    let expected = cx.one(args[1])?;
    let replacement = cx.one(args[2])?;
    let value = body.add_op(wb, op, &[addr, expected, replacement], &[map_type(ty)?]);
    cx.bind1(result, value);
    Ok(())
}

pub(super) fn lower_fence(
    cx: &mut FnCx,
    body: &mut FunctionBody,
    wb: waffle::Block,
    inst: ir::Inst,
) -> Result<()> {
    let dfg = &cx.clif.dfg;
    let InstructionData::NullAry {
        opcode: Opcode::Fence,
    } = dfg.insts[inst]
    else {
        unreachable!("lower_fence dispatched on a non-matching instruction")
    };
    ensure_shared_memory(cx, "fence")?;
    body.add_op(wb, Operator::AtomicFence, &[], &[]);
    Ok(())
}
