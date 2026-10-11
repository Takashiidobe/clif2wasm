//! Operators.
//!
//! An operator is an entity in the IR that accepts some SSA value(s)
//! (or none) as inputs, and produces SSA value(s) (or none) as
//! outputs, when executed. The `Operator` itself contains all of its
//! arguments: for example, a constant value operator (say
//! `Operator::I32Const`) contains the constant value as a field of
//! the enum arm.
//!
//! The set of operators supported by waffle is meant to be 1-to-1
//! with Wasm: an operator represents and has the semantics of the
//! Wasm opcode of the same name. The only exceptions are around
//! features of Wasm bytecode that waffle "lifts" into its own SSA IR:
//! accesses to Wasm locals (these become the SSA dataflow itself) and
//! control flow (these become `Terminator` instructions).

use crate::waffle::{entity::EntityRef, Func, Global, Memory, Signature, Table, Type};
use std::convert::TryFrom;
pub use wasmparser_248::{Ieee32, Ieee64};

/// An argument to a memory load or store, specifying which memory,
/// alignment and an optional offset.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct MemoryArg {
    pub align: u32,
    pub offset: u32,
    pub memory: Memory,
}

impl std::fmt::Display for MemoryArg {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(
            f,
            "{}, align={}, offset={}",
            self.memory, self.align, self.offset
        )
    }
}

/// An operator in the IR, consuming arguments and producing results
/// when executed.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Operator {
    Unreachable,
    Nop,

    Call {
        function_index: Func,
    },
    CallIndirect {
        sig_index: Signature,
        table_index: Table,
    },
    Select,
    TypedSelect {
        ty: Type,
    },
    GlobalGet {
        global_index: Global,
    },
    GlobalSet {
        global_index: Global,
    },

    I32Load {
        memory: MemoryArg,
    },
    I64Load {
        memory: MemoryArg,
    },
    F32Load {
        memory: MemoryArg,
    },
    F64Load {
        memory: MemoryArg,
    },
    I32Load8S {
        memory: MemoryArg,
    },
    I32Load8U {
        memory: MemoryArg,
    },
    I32Load16S {
        memory: MemoryArg,
    },
    I32Load16U {
        memory: MemoryArg,
    },
    I64Load8S {
        memory: MemoryArg,
    },
    I64Load8U {
        memory: MemoryArg,
    },
    I64Load16S {
        memory: MemoryArg,
    },
    I64Load16U {
        memory: MemoryArg,
    },
    I64Load32S {
        memory: MemoryArg,
    },
    I64Load32U {
        memory: MemoryArg,
    },

    I32Store {
        memory: MemoryArg,
    },
    I64Store {
        memory: MemoryArg,
    },
    F32Store {
        memory: MemoryArg,
    },
    F64Store {
        memory: MemoryArg,
    },
    I32Store8 {
        memory: MemoryArg,
    },
    I32Store16 {
        memory: MemoryArg,
    },
    I64Store8 {
        memory: MemoryArg,
    },
    I64Store16 {
        memory: MemoryArg,
    },
    I64Store32 {
        memory: MemoryArg,
    },
    MemoryAtomicNotify {
        memory: MemoryArg,
    },
    MemoryAtomicWait32 {
        memory: MemoryArg,
    },
    MemoryAtomicWait64 {
        memory: MemoryArg,
    },
    AtomicFence,
    I32AtomicLoad {
        memory: MemoryArg,
    },
    I64AtomicLoad {
        memory: MemoryArg,
    },
    I32AtomicLoad8U {
        memory: MemoryArg,
    },
    I32AtomicLoad16U {
        memory: MemoryArg,
    },
    I64AtomicLoad8U {
        memory: MemoryArg,
    },
    I64AtomicLoad16U {
        memory: MemoryArg,
    },
    I64AtomicLoad32U {
        memory: MemoryArg,
    },
    I32AtomicStore {
        memory: MemoryArg,
    },
    I64AtomicStore {
        memory: MemoryArg,
    },
    I32AtomicStore8 {
        memory: MemoryArg,
    },
    I32AtomicStore16 {
        memory: MemoryArg,
    },
    I64AtomicStore8 {
        memory: MemoryArg,
    },
    I64AtomicStore16 {
        memory: MemoryArg,
    },
    I64AtomicStore32 {
        memory: MemoryArg,
    },
    I32AtomicRmwAdd {
        memory: MemoryArg,
    },
    I64AtomicRmwAdd {
        memory: MemoryArg,
    },
    I32AtomicRmw8AddU {
        memory: MemoryArg,
    },
    I32AtomicRmw16AddU {
        memory: MemoryArg,
    },
    I64AtomicRmw8AddU {
        memory: MemoryArg,
    },
    I64AtomicRmw16AddU {
        memory: MemoryArg,
    },
    I64AtomicRmw32AddU {
        memory: MemoryArg,
    },
    I32AtomicRmwSub {
        memory: MemoryArg,
    },
    I64AtomicRmwSub {
        memory: MemoryArg,
    },
    I32AtomicRmw8SubU {
        memory: MemoryArg,
    },
    I32AtomicRmw16SubU {
        memory: MemoryArg,
    },
    I64AtomicRmw8SubU {
        memory: MemoryArg,
    },
    I64AtomicRmw16SubU {
        memory: MemoryArg,
    },
    I64AtomicRmw32SubU {
        memory: MemoryArg,
    },
    I32AtomicRmwAnd {
        memory: MemoryArg,
    },
    I64AtomicRmwAnd {
        memory: MemoryArg,
    },
    I32AtomicRmw8AndU {
        memory: MemoryArg,
    },
    I32AtomicRmw16AndU {
        memory: MemoryArg,
    },
    I64AtomicRmw8AndU {
        memory: MemoryArg,
    },
    I64AtomicRmw16AndU {
        memory: MemoryArg,
    },
    I64AtomicRmw32AndU {
        memory: MemoryArg,
    },
    I32AtomicRmwOr {
        memory: MemoryArg,
    },
    I64AtomicRmwOr {
        memory: MemoryArg,
    },
    I32AtomicRmw8OrU {
        memory: MemoryArg,
    },
    I32AtomicRmw16OrU {
        memory: MemoryArg,
    },
    I64AtomicRmw8OrU {
        memory: MemoryArg,
    },
    I64AtomicRmw16OrU {
        memory: MemoryArg,
    },
    I64AtomicRmw32OrU {
        memory: MemoryArg,
    },
    I32AtomicRmwXor {
        memory: MemoryArg,
    },
    I64AtomicRmwXor {
        memory: MemoryArg,
    },
    I32AtomicRmw8XorU {
        memory: MemoryArg,
    },
    I32AtomicRmw16XorU {
        memory: MemoryArg,
    },
    I64AtomicRmw8XorU {
        memory: MemoryArg,
    },
    I64AtomicRmw16XorU {
        memory: MemoryArg,
    },
    I64AtomicRmw32XorU {
        memory: MemoryArg,
    },
    I32AtomicRmwXchg {
        memory: MemoryArg,
    },
    I64AtomicRmwXchg {
        memory: MemoryArg,
    },
    I32AtomicRmw8XchgU {
        memory: MemoryArg,
    },
    I32AtomicRmw16XchgU {
        memory: MemoryArg,
    },
    I64AtomicRmw8XchgU {
        memory: MemoryArg,
    },
    I64AtomicRmw16XchgU {
        memory: MemoryArg,
    },
    I64AtomicRmw32XchgU {
        memory: MemoryArg,
    },
    I32AtomicRmwCmpxchg {
        memory: MemoryArg,
    },
    I64AtomicRmwCmpxchg {
        memory: MemoryArg,
    },
    I32AtomicRmw8CmpxchgU {
        memory: MemoryArg,
    },
    I32AtomicRmw16CmpxchgU {
        memory: MemoryArg,
    },
    I64AtomicRmw8CmpxchgU {
        memory: MemoryArg,
    },
    I64AtomicRmw16CmpxchgU {
        memory: MemoryArg,
    },
    I64AtomicRmw32CmpxchgU {
        memory: MemoryArg,
    },

    I32Const {
        value: u32,
    },
    I64Const {
        value: u64,
    },
    F32Const {
        value: u32,
    },
    F64Const {
        value: u64,
    },

    I32Eqz,
    I32Eq,
    I32Ne,
    I32LtS,
    I32LtU,
    I32GtS,
    I32GtU,
    I32LeS,
    I32LeU,
    I32GeS,
    I32GeU,

    I64Eqz,

    I64Eq,
    I64Ne,
    I64LtS,
    I64LtU,
    I64GtU,
    I64GtS,
    I64LeS,
    I64LeU,
    I64GeS,
    I64GeU,

    F32Eq,
    F32Ne,
    F32Lt,
    F32Gt,
    F32Le,
    F32Ge,

    F64Eq,
    F64Ne,
    F64Lt,
    F64Gt,
    F64Le,
    F64Ge,

    I32Clz,
    I32Ctz,
    I32Popcnt,

    I32Add,
    I32Sub,
    I32Mul,
    I32DivS,
    I32DivU,
    I32RemS,
    I32RemU,
    I32And,
    I32Or,
    I32Xor,
    I32Shl,
    I32ShrS,
    I32ShrU,
    I32Rotl,
    I32Rotr,

    I64Clz,
    I64Ctz,
    I64Popcnt,

    I64Add,
    I64Sub,
    I64Mul,
    I64DivS,
    I64DivU,
    I64RemS,
    I64RemU,
    I64And,
    I64Or,
    I64Xor,
    I64Shl,
    I64ShrS,
    I64ShrU,
    I64Rotl,
    I64Rotr,

    F32Abs,
    F32Neg,
    F32Ceil,
    F32Floor,
    F32Trunc,
    F32Nearest,
    F32Sqrt,

    F32Add,
    F32Sub,
    F32Mul,
    F32Div,
    F32Min,
    F32Max,
    F32Copysign,

    F64Abs,
    F64Neg,
    F64Ceil,
    F64Floor,
    F64Trunc,
    F64Nearest,
    F64Sqrt,

    F64Add,
    F64Sub,
    F64Mul,
    F64Div,
    F64Min,
    F64Max,
    F64Copysign,

    I32WrapI64,
    I32TruncF32S,
    I32TruncF32U,
    I32TruncF64S,
    I32TruncF64U,
    I64ExtendI32S,
    I64ExtendI32U,
    I64TruncF32S,
    I64TruncF32U,
    I64TruncF64S,
    I64TruncF64U,
    F32ConvertI32S,
    F32ConvertI32U,
    F32ConvertI64S,
    F32ConvertI64U,
    F32DemoteF64,
    F64ConvertI32S,
    F64ConvertI32U,
    F64ConvertI64S,
    F64ConvertI64U,
    F64PromoteF32,
    I32Extend8S,
    I32Extend16S,
    I64Extend8S,
    I64Extend16S,
    I64Extend32S,
    I32TruncSatF32S,
    I32TruncSatF32U,
    I32TruncSatF64S,
    I32TruncSatF64U,
    I64TruncSatF32S,
    I64TruncSatF32U,
    I64TruncSatF64S,
    I64TruncSatF64U,
    F32ReinterpretI32,
    F64ReinterpretI64,
    I32ReinterpretF32,
    I64ReinterpretF64,
    TableGet {
        table_index: Table,
    },
    TableSet {
        table_index: Table,
    },
    TableGrow {
        table_index: Table,
    },
    TableSize {
        table_index: Table,
    },
    MemorySize {
        mem: Memory,
    },
    MemoryGrow {
        mem: Memory,
    },
    MemoryCopy {
        dst_mem: Memory,
        src_mem: Memory,
    },
    MemoryFill {
        mem: Memory,
    },

    V128Load {
        memory: MemoryArg,
    },
    V128Load8x8S {
        memory: MemoryArg,
    },
    V128Load8x8U {
        memory: MemoryArg,
    },
    V128Load16x4S {
        memory: MemoryArg,
    },
    V128Load16x4U {
        memory: MemoryArg,
    },
    V128Load32x2S {
        memory: MemoryArg,
    },
    V128Load32x2U {
        memory: MemoryArg,
    },
    V128Load8Splat {
        memory: MemoryArg,
    },
    V128Load16Splat {
        memory: MemoryArg,
    },
    V128Load32Splat {
        memory: MemoryArg,
    },
    V128Load64Splat {
        memory: MemoryArg,
    },
    V128Load32Zero {
        memory: MemoryArg,
    },
    V128Load64Zero {
        memory: MemoryArg,
    },
    V128Store {
        memory: MemoryArg,
    },
    V128Load8Lane {
        memory: MemoryArg,
        lane: u8,
    },
    V128Load16Lane {
        memory: MemoryArg,
        lane: u8,
    },
    V128Load32Lane {
        memory: MemoryArg,
        lane: u8,
    },
    V128Load64Lane {
        memory: MemoryArg,
        lane: u8,
    },
    V128Store8Lane {
        memory: MemoryArg,
        lane: u8,
    },
    V128Store16Lane {
        memory: MemoryArg,
        lane: u8,
    },
    V128Store32Lane {
        memory: MemoryArg,
        lane: u8,
    },
    V128Store64Lane {
        memory: MemoryArg,
        lane: u8,
    },

    V128Const {
        value: u128,
    },

    I8x16Shuffle {
        lanes: [u8; 16],
    },

    I8x16ExtractLaneS {
        lane: u8,
    },
    I8x16ExtractLaneU {
        lane: u8,
    },
    I8x16ReplaceLane {
        lane: u8,
    },
    I16x8ExtractLaneS {
        lane: u8,
    },
    I16x8ExtractLaneU {
        lane: u8,
    },
    I16x8ReplaceLane {
        lane: u8,
    },
    I32x4ExtractLane {
        lane: u8,
    },
    I32x4ReplaceLane {
        lane: u8,
    },
    I64x2ExtractLane {
        lane: u8,
    },
    I64x2ReplaceLane {
        lane: u8,
    },
    F32x4ExtractLane {
        lane: u8,
    },
    F32x4ReplaceLane {
        lane: u8,
    },
    F64x2ExtractLane {
        lane: u8,
    },
    F64x2ReplaceLane {
        lane: u8,
    },

    I8x16Swizzle,
    I8x16Splat,
    I16x8Splat,
    I32x4Splat,
    I64x2Splat,
    F32x4Splat,
    F64x2Splat,

    I8x16Eq,
    I8x16Ne,
    I8x16LtS,
    I8x16LtU,
    I8x16GtS,
    I8x16GtU,
    I8x16LeS,
    I8x16LeU,
    I8x16GeS,
    I8x16GeU,

    I16x8Eq,
    I16x8Ne,
    I16x8LtS,
    I16x8LtU,
    I16x8GtS,
    I16x8GtU,
    I16x8LeS,
    I16x8LeU,
    I16x8GeS,
    I16x8GeU,

    I32x4Eq,
    I32x4Ne,
    I32x4LtS,
    I32x4LtU,
    I32x4GtS,
    I32x4GtU,
    I32x4LeS,
    I32x4LeU,
    I32x4GeS,
    I32x4GeU,

    I64x2Eq,
    I64x2Ne,
    I64x2LtS,
    I64x2GtS,
    I64x2LeS,
    I64x2GeS,

    F32x4Eq,
    F32x4Ne,
    F32x4Lt,
    F32x4Gt,
    F32x4Le,
    F32x4Ge,

    F64x2Eq,
    F64x2Ne,
    F64x2Lt,
    F64x2Gt,
    F64x2Le,
    F64x2Ge,

    V128Not,
    V128And,
    V128AndNot,
    V128Or,
    V128Xor,
    V128Bitselect,
    V128AnyTrue,

    I8x16Abs,
    I8x16Neg,
    I8x16Popcnt,
    I8x16AllTrue,
    I8x16Bitmask,
    I8x16NarrowI16x8S,
    I8x16NarrowI16x8U,
    I8x16Shl,
    I8x16ShrS,
    I8x16ShrU,
    I8x16Add,
    I8x16AddSatS,
    I8x16AddSatU,
    I8x16Sub,
    I8x16SubSatS,
    I8x16SubSatU,
    I8x16MinS,
    I8x16MinU,
    I8x16MaxS,
    I8x16MaxU,
    I8x16AvgrU,

    I16x8ExtAddPairwiseI8x16S,
    I16x8ExtAddPairwiseI8x16U,
    I16x8Abs,
    I16x8Neg,
    I16x8Q15MulrSatS,
    I16x8AllTrue,
    I16x8Bitmask,
    I16x8NarrowI32x4S,
    I16x8NarrowI32x4U,
    I16x8ExtendLowI8x16S,
    I16x8ExtendHighI8x16S,
    I16x8ExtendLowI8x16U,
    I16x8ExtendHighI8x16U,
    I16x8Shl,
    I16x8ShrS,
    I16x8ShrU,
    I16x8Add,
    I16x8AddSatS,
    I16x8AddSatU,
    I16x8Sub,
    I16x8SubSatS,
    I16x8SubSatU,
    I16x8Mul,
    I16x8MinS,
    I16x8MinU,
    I16x8MaxS,
    I16x8MaxU,
    I16x8AvgrU,
    I16x8ExtMulLowI8x16S,
    I16x8ExtMulHighI8x16S,
    I16x8ExtMulLowI8x16U,
    I16x8ExtMulHighI8x16U,
    I32x4ExtAddPairwiseI16x8S,
    I32x4ExtAddPairwiseI16x8U,

    I32x4Abs,
    I32x4Neg,
    I32x4AllTrue,
    I32x4Bitmask,
    I32x4ExtendLowI16x8S,
    I32x4ExtendHighI16x8S,
    I32x4ExtendLowI16x8U,
    I32x4ExtendHighI16x8U,
    I32x4Shl,
    I32x4ShrS,
    I32x4ShrU,
    I32x4Add,
    I32x4Sub,
    I32x4Mul,
    I32x4MinS,
    I32x4MinU,
    I32x4MaxS,
    I32x4MaxU,
    I32x4DotI16x8S,
    I32x4ExtMulLowI16x8S,
    I32x4ExtMulHighI16x8S,
    I32x4ExtMulLowI16x8U,
    I32x4ExtMulHighI16x8U,
    I64x2Abs,
    I64x2Neg,
    I64x2AllTrue,
    I64x2Bitmask,
    I64x2ExtendLowI32x4S,
    I64x2ExtendHighI32x4S,
    I64x2ExtendLowI32x4U,
    I64x2ExtendHighI32x4U,
    I64x2Shl,
    I64x2ShrS,
    I64x2ShrU,
    I64x2Add,
    I64x2Sub,
    I64x2Mul,
    I64x2ExtMulLowI32x4S,
    I64x2ExtMulHighI32x4S,
    I64x2ExtMulLowI32x4U,
    I64x2ExtMulHighI32x4U,
    F32x4Ceil,
    F32x4Floor,
    F32x4Trunc,
    F32x4Nearest,
    F32x4Abs,
    F32x4Neg,
    F32x4Sqrt,
    F32x4Add,
    F32x4Sub,
    F32x4Mul,
    F32x4Div,
    F32x4Min,
    F32x4Max,
    F32x4PMin,
    F32x4PMax,
    F64x2Ceil,
    F64x2Floor,
    F64x2Trunc,
    F64x2Nearest,
    F64x2Abs,
    F64x2Neg,
    F64x2Sqrt,
    F64x2Add,
    F64x2Sub,
    F64x2Mul,
    F64x2Div,
    F64x2Min,
    F64x2Max,
    F64x2PMin,
    F64x2PMax,
    I32x4TruncSatF32x4S,
    I32x4TruncSatF32x4U,
    F32x4ConvertI32x4S,
    F32x4ConvertI32x4U,
    I32x4TruncSatF64x2SZero,
    I32x4TruncSatF64x2UZero,
    F64x2ConvertLowI32x4S,
    F64x2ConvertLowI32x4U,
    F32x4DemoteF64x2Zero,
    F64x2PromoteLowF32x4,

    CallRef {
        sig_index: Signature,
    },
    RefIsNull,
    RefNull {
        sig_index: Signature,
    },
    RefFunc {
        func_index: Func,
    },
}

#[test]
fn op_size() {
    assert_eq!(std::mem::size_of::<Operator>(), 32);
}

impl<'a, 'b> std::convert::TryFrom<&'b wasmparser_248::Operator<'a>> for Operator {
    type Error = ();

    fn try_from(op: &'b wasmparser_248::Operator<'a>) -> Result<Operator, Self::Error> {
        match op {
            &wasmparser_248::Operator::Unreachable => Ok(Operator::Unreachable),
            &wasmparser_248::Operator::Nop => Ok(Operator::Nop),
            &wasmparser_248::Operator::Call { function_index } => Ok(Operator::Call {
                function_index: Func::from(function_index),
            }),
            &wasmparser_248::Operator::CallIndirect {
                type_index,
                table_index,
                ..
            } => Ok(Operator::CallIndirect {
                sig_index: Signature::from(type_index),
                table_index: Table::from(table_index),
            }),
            &wasmparser_248::Operator::LocalSet { .. } => Err(()),
            &wasmparser_248::Operator::LocalTee { .. } => Err(()),
            &wasmparser_248::Operator::LocalGet { .. } => Err(()),
            &wasmparser_248::Operator::Select => Ok(Operator::Select),
            &wasmparser_248::Operator::TypedSelect { ty } => {
                Ok(Operator::TypedSelect { ty: ty.into() })
            }
            &wasmparser_248::Operator::GlobalGet { global_index } => Ok(Operator::GlobalGet {
                global_index: Global::from(global_index),
            }),
            &wasmparser_248::Operator::GlobalSet { global_index } => Ok(Operator::GlobalSet {
                global_index: Global::from(global_index),
            }),
            &wasmparser_248::Operator::I32Load { memarg } => Ok(Operator::I32Load {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I64Load { memarg } => Ok(Operator::I64Load {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::F32Load { memarg } => Ok(Operator::F32Load {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::F64Load { memarg } => Ok(Operator::F64Load {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I32Load8S { memarg } => Ok(Operator::I32Load8S {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I32Load8U { memarg } => Ok(Operator::I32Load8U {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I32Load16S { memarg } => Ok(Operator::I32Load16S {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I32Load16U { memarg } => Ok(Operator::I32Load16U {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I64Load8S { memarg } => Ok(Operator::I64Load8S {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I64Load8U { memarg } => Ok(Operator::I64Load8U {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I64Load16S { memarg } => Ok(Operator::I64Load16S {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I64Load16U { memarg } => Ok(Operator::I64Load16U {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I64Load32S { memarg } => Ok(Operator::I64Load32S {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I64Load32U { memarg } => Ok(Operator::I64Load32U {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I32Store { memarg } => Ok(Operator::I32Store {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I64Store { memarg } => Ok(Operator::I64Store {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::F32Store { memarg } => Ok(Operator::F32Store {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::F64Store { memarg } => Ok(Operator::F64Store {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I32Store8 { memarg } => Ok(Operator::I32Store8 {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I32Store16 { memarg } => Ok(Operator::I32Store16 {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I64Store8 { memarg } => Ok(Operator::I64Store8 {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I64Store16 { memarg } => Ok(Operator::I64Store16 {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I64Store32 { memarg } => Ok(Operator::I64Store32 {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::MemoryAtomicNotify { memarg } => Ok(Operator::MemoryAtomicNotify {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::MemoryAtomicWait32 { memarg } => Ok(Operator::MemoryAtomicWait32 {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::MemoryAtomicWait64 { memarg } => Ok(Operator::MemoryAtomicWait64 {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::AtomicFence => Ok(Operator::AtomicFence),
            &wasmparser_248::Operator::I32AtomicLoad { memarg } => Ok(Operator::I32AtomicLoad {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I64AtomicLoad { memarg } => Ok(Operator::I64AtomicLoad {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I32AtomicLoad8U { memarg } => Ok(Operator::I32AtomicLoad8U {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I32AtomicLoad16U { memarg } => Ok(Operator::I32AtomicLoad16U {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I64AtomicLoad8U { memarg } => Ok(Operator::I64AtomicLoad8U {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I64AtomicLoad16U { memarg } => Ok(Operator::I64AtomicLoad16U {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I64AtomicLoad32U { memarg } => Ok(Operator::I64AtomicLoad32U {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I32AtomicStore { memarg } => Ok(Operator::I32AtomicStore {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I64AtomicStore { memarg } => Ok(Operator::I64AtomicStore {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I32AtomicStore8 { memarg } => Ok(Operator::I32AtomicStore8 {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I32AtomicStore16 { memarg } => Ok(Operator::I32AtomicStore16 {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I64AtomicStore8 { memarg } => Ok(Operator::I64AtomicStore8 {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I64AtomicStore16 { memarg } => Ok(Operator::I64AtomicStore16 {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I64AtomicStore32 { memarg } => Ok(Operator::I64AtomicStore32 {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I32AtomicRmwAdd { memarg } => Ok(Operator::I32AtomicRmwAdd {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I64AtomicRmwAdd { memarg } => Ok(Operator::I64AtomicRmwAdd {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I32AtomicRmw8AddU { memarg } => Ok(Operator::I32AtomicRmw8AddU {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I32AtomicRmw16AddU { memarg } => Ok(Operator::I32AtomicRmw16AddU {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I64AtomicRmw8AddU { memarg } => Ok(Operator::I64AtomicRmw8AddU {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I64AtomicRmw16AddU { memarg } => Ok(Operator::I64AtomicRmw16AddU {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I64AtomicRmw32AddU { memarg } => Ok(Operator::I64AtomicRmw32AddU {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I32AtomicRmwSub { memarg } => Ok(Operator::I32AtomicRmwSub {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I64AtomicRmwSub { memarg } => Ok(Operator::I64AtomicRmwSub {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I32AtomicRmw8SubU { memarg } => Ok(Operator::I32AtomicRmw8SubU {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I32AtomicRmw16SubU { memarg } => Ok(Operator::I32AtomicRmw16SubU {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I64AtomicRmw8SubU { memarg } => Ok(Operator::I64AtomicRmw8SubU {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I64AtomicRmw16SubU { memarg } => Ok(Operator::I64AtomicRmw16SubU {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I64AtomicRmw32SubU { memarg } => Ok(Operator::I64AtomicRmw32SubU {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I32AtomicRmwAnd { memarg } => Ok(Operator::I32AtomicRmwAnd {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I64AtomicRmwAnd { memarg } => Ok(Operator::I64AtomicRmwAnd {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I32AtomicRmw8AndU { memarg } => Ok(Operator::I32AtomicRmw8AndU {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I32AtomicRmw16AndU { memarg } => Ok(Operator::I32AtomicRmw16AndU {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I64AtomicRmw8AndU { memarg } => Ok(Operator::I64AtomicRmw8AndU {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I64AtomicRmw16AndU { memarg } => Ok(Operator::I64AtomicRmw16AndU {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I64AtomicRmw32AndU { memarg } => Ok(Operator::I64AtomicRmw32AndU {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I32AtomicRmwOr { memarg } => Ok(Operator::I32AtomicRmwOr {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I64AtomicRmwOr { memarg } => Ok(Operator::I64AtomicRmwOr {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I32AtomicRmw8OrU { memarg } => Ok(Operator::I32AtomicRmw8OrU {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I32AtomicRmw16OrU { memarg } => Ok(Operator::I32AtomicRmw16OrU {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I64AtomicRmw8OrU { memarg } => Ok(Operator::I64AtomicRmw8OrU {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I64AtomicRmw16OrU { memarg } => Ok(Operator::I64AtomicRmw16OrU {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I64AtomicRmw32OrU { memarg } => Ok(Operator::I64AtomicRmw32OrU {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I32AtomicRmwXor { memarg } => Ok(Operator::I32AtomicRmwXor {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I64AtomicRmwXor { memarg } => Ok(Operator::I64AtomicRmwXor {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I32AtomicRmw8XorU { memarg } => Ok(Operator::I32AtomicRmw8XorU {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I32AtomicRmw16XorU { memarg } => Ok(Operator::I32AtomicRmw16XorU {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I64AtomicRmw8XorU { memarg } => Ok(Operator::I64AtomicRmw8XorU {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I64AtomicRmw16XorU { memarg } => Ok(Operator::I64AtomicRmw16XorU {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I64AtomicRmw32XorU { memarg } => Ok(Operator::I64AtomicRmw32XorU {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I32AtomicRmwXchg { memarg } => Ok(Operator::I32AtomicRmwXchg {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I64AtomicRmwXchg { memarg } => Ok(Operator::I64AtomicRmwXchg {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I32AtomicRmw8XchgU { memarg } => Ok(Operator::I32AtomicRmw8XchgU {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I32AtomicRmw16XchgU { memarg } => Ok(Operator::I32AtomicRmw16XchgU {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I64AtomicRmw8XchgU { memarg } => Ok(Operator::I64AtomicRmw8XchgU {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I64AtomicRmw16XchgU { memarg } => Ok(Operator::I64AtomicRmw16XchgU {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I64AtomicRmw32XchgU { memarg } => Ok(Operator::I64AtomicRmw32XchgU {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I32AtomicRmwCmpxchg { memarg } => Ok(Operator::I32AtomicRmwCmpxchg {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I64AtomicRmwCmpxchg { memarg } => Ok(Operator::I64AtomicRmwCmpxchg {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I32AtomicRmw8CmpxchgU { memarg } => Ok(Operator::I32AtomicRmw8CmpxchgU {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I32AtomicRmw16CmpxchgU { memarg } => Ok(Operator::I32AtomicRmw16CmpxchgU {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I64AtomicRmw8CmpxchgU { memarg } => Ok(Operator::I64AtomicRmw8CmpxchgU {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I64AtomicRmw16CmpxchgU { memarg } => Ok(Operator::I64AtomicRmw16CmpxchgU {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I64AtomicRmw32CmpxchgU { memarg } => Ok(Operator::I64AtomicRmw32CmpxchgU {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::I32Const { value } => Ok(Operator::I32Const {
                value: value as u32,
            }),
            &wasmparser_248::Operator::I64Const { value } => Ok(Operator::I64Const {
                value: value as u64,
            }),
            &wasmparser_248::Operator::F32Const { value } => Ok(Operator::F32Const {
                value: value.bits(),
            }),
            &wasmparser_248::Operator::F64Const { value } => Ok(Operator::F64Const {
                value: value.bits(),
            }),
            &wasmparser_248::Operator::I32Eqz => Ok(Operator::I32Eqz),
            &wasmparser_248::Operator::I32Eq => Ok(Operator::I32Eq),
            &wasmparser_248::Operator::I32Ne => Ok(Operator::I32Ne),
            &wasmparser_248::Operator::I32LtS => Ok(Operator::I32LtS),
            &wasmparser_248::Operator::I32LtU => Ok(Operator::I32LtU),
            &wasmparser_248::Operator::I32GtS => Ok(Operator::I32GtS),
            &wasmparser_248::Operator::I32GtU => Ok(Operator::I32GtU),
            &wasmparser_248::Operator::I32LeS => Ok(Operator::I32LeS),
            &wasmparser_248::Operator::I32LeU => Ok(Operator::I32LeU),
            &wasmparser_248::Operator::I32GeS => Ok(Operator::I32GeS),
            &wasmparser_248::Operator::I32GeU => Ok(Operator::I32GeU),
            &wasmparser_248::Operator::I64Eqz => Ok(Operator::I64Eqz),
            &wasmparser_248::Operator::I64Eq => Ok(Operator::I64Eq),
            &wasmparser_248::Operator::I64Ne => Ok(Operator::I64Ne),
            &wasmparser_248::Operator::I64LtS => Ok(Operator::I64LtS),
            &wasmparser_248::Operator::I64LtU => Ok(Operator::I64LtU),
            &wasmparser_248::Operator::I64GtU => Ok(Operator::I64GtU),
            &wasmparser_248::Operator::I64GtS => Ok(Operator::I64GtS),
            &wasmparser_248::Operator::I64LeS => Ok(Operator::I64LeS),
            &wasmparser_248::Operator::I64LeU => Ok(Operator::I64LeU),
            &wasmparser_248::Operator::I64GeS => Ok(Operator::I64GeS),
            &wasmparser_248::Operator::I64GeU => Ok(Operator::I64GeU),
            &wasmparser_248::Operator::F32Eq => Ok(Operator::F32Eq),
            &wasmparser_248::Operator::F32Ne => Ok(Operator::F32Ne),
            &wasmparser_248::Operator::F32Lt => Ok(Operator::F32Lt),
            &wasmparser_248::Operator::F32Gt => Ok(Operator::F32Gt),
            &wasmparser_248::Operator::F32Le => Ok(Operator::F32Le),
            &wasmparser_248::Operator::F32Ge => Ok(Operator::F32Ge),
            &wasmparser_248::Operator::F64Eq => Ok(Operator::F64Eq),
            &wasmparser_248::Operator::F64Ne => Ok(Operator::F64Ne),
            &wasmparser_248::Operator::F64Lt => Ok(Operator::F64Lt),
            &wasmparser_248::Operator::F64Gt => Ok(Operator::F64Gt),
            &wasmparser_248::Operator::F64Le => Ok(Operator::F64Le),
            &wasmparser_248::Operator::F64Ge => Ok(Operator::F64Ge),
            &wasmparser_248::Operator::I32Clz => Ok(Operator::I32Clz),
            &wasmparser_248::Operator::I32Ctz => Ok(Operator::I32Ctz),
            &wasmparser_248::Operator::I32Popcnt => Ok(Operator::I32Popcnt),
            &wasmparser_248::Operator::I32Add => Ok(Operator::I32Add),
            &wasmparser_248::Operator::I32Sub => Ok(Operator::I32Sub),
            &wasmparser_248::Operator::I32Mul => Ok(Operator::I32Mul),
            &wasmparser_248::Operator::I32DivS => Ok(Operator::I32DivS),
            &wasmparser_248::Operator::I32DivU => Ok(Operator::I32DivU),
            &wasmparser_248::Operator::I32RemS => Ok(Operator::I32RemS),
            &wasmparser_248::Operator::I32RemU => Ok(Operator::I32RemU),
            &wasmparser_248::Operator::I32And => Ok(Operator::I32And),
            &wasmparser_248::Operator::I32Or => Ok(Operator::I32Or),
            &wasmparser_248::Operator::I32Xor => Ok(Operator::I32Xor),
            &wasmparser_248::Operator::I32Shl => Ok(Operator::I32Shl),
            &wasmparser_248::Operator::I32ShrS => Ok(Operator::I32ShrS),
            &wasmparser_248::Operator::I32ShrU => Ok(Operator::I32ShrU),
            &wasmparser_248::Operator::I32Rotl => Ok(Operator::I32Rotl),
            &wasmparser_248::Operator::I32Rotr => Ok(Operator::I32Rotr),
            &wasmparser_248::Operator::I64Clz => Ok(Operator::I64Clz),
            &wasmparser_248::Operator::I64Ctz => Ok(Operator::I64Ctz),
            &wasmparser_248::Operator::I64Popcnt => Ok(Operator::I64Popcnt),
            &wasmparser_248::Operator::I64Add => Ok(Operator::I64Add),
            &wasmparser_248::Operator::I64Sub => Ok(Operator::I64Sub),
            &wasmparser_248::Operator::I64Mul => Ok(Operator::I64Mul),
            &wasmparser_248::Operator::I64DivS => Ok(Operator::I64DivS),
            &wasmparser_248::Operator::I64DivU => Ok(Operator::I64DivU),
            &wasmparser_248::Operator::I64RemS => Ok(Operator::I64RemS),
            &wasmparser_248::Operator::I64RemU => Ok(Operator::I64RemU),
            &wasmparser_248::Operator::I64And => Ok(Operator::I64And),
            &wasmparser_248::Operator::I64Or => Ok(Operator::I64Or),
            &wasmparser_248::Operator::I64Xor => Ok(Operator::I64Xor),
            &wasmparser_248::Operator::I64Shl => Ok(Operator::I64Shl),
            &wasmparser_248::Operator::I64ShrS => Ok(Operator::I64ShrS),
            &wasmparser_248::Operator::I64ShrU => Ok(Operator::I64ShrU),
            &wasmparser_248::Operator::I64Rotl => Ok(Operator::I64Rotl),
            &wasmparser_248::Operator::I64Rotr => Ok(Operator::I64Rotr),
            &wasmparser_248::Operator::F32Abs => Ok(Operator::F32Abs),
            &wasmparser_248::Operator::F32Neg => Ok(Operator::F32Neg),
            &wasmparser_248::Operator::F32Ceil => Ok(Operator::F32Ceil),
            &wasmparser_248::Operator::F32Floor => Ok(Operator::F32Floor),
            &wasmparser_248::Operator::F32Trunc => Ok(Operator::F32Trunc),
            &wasmparser_248::Operator::F32Nearest => Ok(Operator::F32Nearest),
            &wasmparser_248::Operator::F32Sqrt => Ok(Operator::F32Sqrt),
            &wasmparser_248::Operator::F32Add => Ok(Operator::F32Add),
            &wasmparser_248::Operator::F32Sub => Ok(Operator::F32Sub),
            &wasmparser_248::Operator::F32Mul => Ok(Operator::F32Mul),
            &wasmparser_248::Operator::F32Div => Ok(Operator::F32Div),
            &wasmparser_248::Operator::F32Min => Ok(Operator::F32Min),
            &wasmparser_248::Operator::F32Max => Ok(Operator::F32Max),
            &wasmparser_248::Operator::F32Copysign => Ok(Operator::F32Copysign),
            &wasmparser_248::Operator::F64Abs => Ok(Operator::F64Abs),
            &wasmparser_248::Operator::F64Neg => Ok(Operator::F64Neg),
            &wasmparser_248::Operator::F64Ceil => Ok(Operator::F64Ceil),
            &wasmparser_248::Operator::F64Floor => Ok(Operator::F64Floor),
            &wasmparser_248::Operator::F64Trunc => Ok(Operator::F64Trunc),
            &wasmparser_248::Operator::F64Nearest => Ok(Operator::F64Nearest),
            &wasmparser_248::Operator::F64Sqrt => Ok(Operator::F64Sqrt),
            &wasmparser_248::Operator::F64Add => Ok(Operator::F64Add),
            &wasmparser_248::Operator::F64Sub => Ok(Operator::F64Sub),
            &wasmparser_248::Operator::F64Mul => Ok(Operator::F64Mul),
            &wasmparser_248::Operator::F64Div => Ok(Operator::F64Div),
            &wasmparser_248::Operator::F64Min => Ok(Operator::F64Min),
            &wasmparser_248::Operator::F64Max => Ok(Operator::F64Max),
            &wasmparser_248::Operator::F64Copysign => Ok(Operator::F64Copysign),
            &wasmparser_248::Operator::I32WrapI64 => Ok(Operator::I32WrapI64),
            &wasmparser_248::Operator::I32TruncF32S => Ok(Operator::I32TruncF32S),
            &wasmparser_248::Operator::I32TruncF32U => Ok(Operator::I32TruncF32U),
            &wasmparser_248::Operator::I32TruncF64S => Ok(Operator::I32TruncF64S),
            &wasmparser_248::Operator::I32TruncF64U => Ok(Operator::I32TruncF64U),
            &wasmparser_248::Operator::I64ExtendI32S => Ok(Operator::I64ExtendI32S),
            &wasmparser_248::Operator::I64ExtendI32U => Ok(Operator::I64ExtendI32U),
            &wasmparser_248::Operator::I64TruncF32S => Ok(Operator::I64TruncF32S),
            &wasmparser_248::Operator::I64TruncF32U => Ok(Operator::I64TruncF32U),
            &wasmparser_248::Operator::I64TruncF64S => Ok(Operator::I64TruncF64S),
            &wasmparser_248::Operator::I64TruncF64U => Ok(Operator::I64TruncF64U),
            &wasmparser_248::Operator::F32ConvertI32S => Ok(Operator::F32ConvertI32S),
            &wasmparser_248::Operator::F32ConvertI32U => Ok(Operator::F32ConvertI32U),
            &wasmparser_248::Operator::F32ConvertI64S => Ok(Operator::F32ConvertI64S),
            &wasmparser_248::Operator::F32ConvertI64U => Ok(Operator::F32ConvertI64U),
            &wasmparser_248::Operator::F32DemoteF64 => Ok(Operator::F32DemoteF64),
            &wasmparser_248::Operator::F64ConvertI32S => Ok(Operator::F64ConvertI32S),
            &wasmparser_248::Operator::F64ConvertI32U => Ok(Operator::F64ConvertI32U),
            &wasmparser_248::Operator::F64ConvertI64S => Ok(Operator::F64ConvertI64S),
            &wasmparser_248::Operator::F64ConvertI64U => Ok(Operator::F64ConvertI64U),
            &wasmparser_248::Operator::F64PromoteF32 => Ok(Operator::F64PromoteF32),
            &wasmparser_248::Operator::I32Extend8S => Ok(Operator::I32Extend8S),
            &wasmparser_248::Operator::I32Extend16S => Ok(Operator::I32Extend16S),
            &wasmparser_248::Operator::I64Extend8S => Ok(Operator::I64Extend8S),
            &wasmparser_248::Operator::I64Extend16S => Ok(Operator::I64Extend16S),
            &wasmparser_248::Operator::I64Extend32S => Ok(Operator::I64Extend32S),
            &wasmparser_248::Operator::I32TruncSatF32S => Ok(Operator::I32TruncSatF32S),
            &wasmparser_248::Operator::I32TruncSatF32U => Ok(Operator::I32TruncSatF32U),
            &wasmparser_248::Operator::I32TruncSatF64S => Ok(Operator::I32TruncSatF64S),
            &wasmparser_248::Operator::I32TruncSatF64U => Ok(Operator::I32TruncSatF64U),
            &wasmparser_248::Operator::I64TruncSatF32S => Ok(Operator::I64TruncSatF32S),
            &wasmparser_248::Operator::I64TruncSatF32U => Ok(Operator::I64TruncSatF32U),
            &wasmparser_248::Operator::I64TruncSatF64S => Ok(Operator::I64TruncSatF64S),
            &wasmparser_248::Operator::I64TruncSatF64U => Ok(Operator::I64TruncSatF64U),
            &wasmparser_248::Operator::F32ReinterpretI32 => Ok(Operator::F32ReinterpretI32),
            &wasmparser_248::Operator::F64ReinterpretI64 => Ok(Operator::F64ReinterpretI64),
            &wasmparser_248::Operator::I32ReinterpretF32 => Ok(Operator::I32ReinterpretF32),
            &wasmparser_248::Operator::I64ReinterpretF64 => Ok(Operator::I64ReinterpretF64),
            &wasmparser_248::Operator::TableGet { table } => Ok(Operator::TableGet {
                table_index: Table::from(table),
            }),
            &wasmparser_248::Operator::TableSet { table } => Ok(Operator::TableSet {
                table_index: Table::from(table),
            }),
            &wasmparser_248::Operator::TableGrow { table } => Ok(Operator::TableGrow {
                table_index: Table::from(table),
            }),
            &wasmparser_248::Operator::TableSize { table } => Ok(Operator::TableSize {
                table_index: Table::from(table),
            }),
            &wasmparser_248::Operator::MemorySize { mem, .. } => Ok(Operator::MemorySize {
                mem: Memory::from(mem),
            }),
            &wasmparser_248::Operator::MemoryGrow { mem, .. } => Ok(Operator::MemoryGrow {
                mem: Memory::from(mem),
            }),
            &wasmparser_248::Operator::MemoryCopy { dst_mem, src_mem } => Ok(Operator::MemoryCopy {
                dst_mem: Memory::from(dst_mem),
                src_mem: Memory::from(src_mem),
            }),
            &wasmparser_248::Operator::MemoryFill { mem } => Ok(Operator::MemoryFill {
                mem: Memory::from(mem),
            }),

            &wasmparser_248::Operator::V128Load { memarg } => Ok(Operator::V128Load {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::V128Load8x8S { memarg } => Ok(Operator::V128Load8x8S {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::V128Load8x8U { memarg } => Ok(Operator::V128Load8x8U {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::V128Load16x4S { memarg } => Ok(Operator::V128Load16x4S {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::V128Load16x4U { memarg } => Ok(Operator::V128Load16x4U {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::V128Load32x2S { memarg } => Ok(Operator::V128Load32x2S {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::V128Load32x2U { memarg } => Ok(Operator::V128Load32x2U {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::V128Load8Splat { memarg } => Ok(Operator::V128Load8Splat {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::V128Load16Splat { memarg } => Ok(Operator::V128Load16Splat {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::V128Load32Splat { memarg } => Ok(Operator::V128Load32Splat {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::V128Load64Splat { memarg } => Ok(Operator::V128Load64Splat {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::V128Load32Zero { memarg } => Ok(Operator::V128Load32Zero {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::V128Load64Zero { memarg } => Ok(Operator::V128Load64Zero {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::V128Store { memarg } => Ok(Operator::V128Store {
                memory: memarg.into(),
            }),
            &wasmparser_248::Operator::V128Load8Lane { memarg, lane } => Ok(Operator::V128Load8Lane {
                memory: memarg.into(),
                lane,
            }),
            &wasmparser_248::Operator::V128Load16Lane { memarg, lane } => {
                Ok(Operator::V128Load16Lane {
                    memory: memarg.into(),
                    lane,
                })
            }
            &wasmparser_248::Operator::V128Load32Lane { memarg, lane } => {
                Ok(Operator::V128Load32Lane {
                    memory: memarg.into(),
                    lane,
                })
            }
            &wasmparser_248::Operator::V128Load64Lane { memarg, lane } => {
                Ok(Operator::V128Load64Lane {
                    memory: memarg.into(),
                    lane,
                })
            }
            &wasmparser_248::Operator::V128Store8Lane { memarg, lane } => {
                Ok(Operator::V128Store8Lane {
                    memory: memarg.into(),
                    lane,
                })
            }
            &wasmparser_248::Operator::V128Store16Lane { memarg, lane } => {
                Ok(Operator::V128Store16Lane {
                    memory: memarg.into(),
                    lane,
                })
            }
            &wasmparser_248::Operator::V128Store32Lane { memarg, lane } => {
                Ok(Operator::V128Store32Lane {
                    memory: memarg.into(),
                    lane,
                })
            }
            &wasmparser_248::Operator::V128Store64Lane { memarg, lane } => {
                Ok(Operator::V128Store64Lane {
                    memory: memarg.into(),
                    lane,
                })
            }

            &wasmparser_248::Operator::V128Const { value } => Ok(Operator::V128Const {
                value: value.i128() as u128,
            }),

            &wasmparser_248::Operator::I8x16Shuffle { lanes } => Ok(Operator::I8x16Shuffle { lanes }),

            &wasmparser_248::Operator::I8x16ExtractLaneS { lane } => {
                Ok(Operator::I8x16ExtractLaneS { lane })
            }
            &wasmparser_248::Operator::I8x16ExtractLaneU { lane } => {
                Ok(Operator::I8x16ExtractLaneU { lane })
            }
            &wasmparser_248::Operator::I8x16ReplaceLane { lane } => {
                Ok(Operator::I8x16ReplaceLane { lane })
            }
            &wasmparser_248::Operator::I16x8ExtractLaneS { lane } => {
                Ok(Operator::I16x8ExtractLaneS { lane })
            }
            &wasmparser_248::Operator::I16x8ExtractLaneU { lane } => {
                Ok(Operator::I16x8ExtractLaneU { lane })
            }
            &wasmparser_248::Operator::I16x8ReplaceLane { lane } => {
                Ok(Operator::I16x8ReplaceLane { lane })
            }
            &wasmparser_248::Operator::I32x4ExtractLane { lane } => {
                Ok(Operator::I32x4ExtractLane { lane })
            }
            &wasmparser_248::Operator::I32x4ReplaceLane { lane } => {
                Ok(Operator::I32x4ReplaceLane { lane })
            }
            &wasmparser_248::Operator::I64x2ExtractLane { lane } => {
                Ok(Operator::I64x2ExtractLane { lane })
            }
            &wasmparser_248::Operator::I64x2ReplaceLane { lane } => {
                Ok(Operator::I64x2ReplaceLane { lane })
            }
            &wasmparser_248::Operator::F32x4ExtractLane { lane } => {
                Ok(Operator::F32x4ExtractLane { lane })
            }
            &wasmparser_248::Operator::F32x4ReplaceLane { lane } => {
                Ok(Operator::F32x4ReplaceLane { lane })
            }
            &wasmparser_248::Operator::F64x2ExtractLane { lane } => {
                Ok(Operator::F64x2ExtractLane { lane })
            }
            &wasmparser_248::Operator::F64x2ReplaceLane { lane } => {
                Ok(Operator::F64x2ReplaceLane { lane })
            }

            &wasmparser_248::Operator::I8x16Swizzle => Ok(Operator::I8x16Swizzle),
            &wasmparser_248::Operator::I8x16Splat => Ok(Operator::I8x16Splat),
            &wasmparser_248::Operator::I16x8Splat => Ok(Operator::I16x8Splat),
            &wasmparser_248::Operator::I32x4Splat => Ok(Operator::I32x4Splat),
            &wasmparser_248::Operator::I64x2Splat => Ok(Operator::I64x2Splat),
            &wasmparser_248::Operator::F32x4Splat => Ok(Operator::F32x4Splat),
            &wasmparser_248::Operator::F64x2Splat => Ok(Operator::F64x2Splat),

            &wasmparser_248::Operator::I8x16Eq => Ok(Operator::I8x16Eq),
            &wasmparser_248::Operator::I8x16Ne => Ok(Operator::I8x16Ne),
            &wasmparser_248::Operator::I8x16LtS => Ok(Operator::I8x16LtS),
            &wasmparser_248::Operator::I8x16LtU => Ok(Operator::I8x16LtU),
            &wasmparser_248::Operator::I8x16GtS => Ok(Operator::I8x16GtS),
            &wasmparser_248::Operator::I8x16GtU => Ok(Operator::I8x16GtU),
            &wasmparser_248::Operator::I8x16LeS => Ok(Operator::I8x16LeS),
            &wasmparser_248::Operator::I8x16LeU => Ok(Operator::I8x16LeU),
            &wasmparser_248::Operator::I8x16GeS => Ok(Operator::I8x16GeS),
            &wasmparser_248::Operator::I8x16GeU => Ok(Operator::I8x16GeU),

            &wasmparser_248::Operator::I16x8Eq => Ok(Operator::I16x8Eq),
            &wasmparser_248::Operator::I16x8Ne => Ok(Operator::I16x8Ne),
            &wasmparser_248::Operator::I16x8LtS => Ok(Operator::I16x8LtS),
            &wasmparser_248::Operator::I16x8LtU => Ok(Operator::I16x8LtU),
            &wasmparser_248::Operator::I16x8GtS => Ok(Operator::I16x8GtS),
            &wasmparser_248::Operator::I16x8GtU => Ok(Operator::I16x8GtU),
            &wasmparser_248::Operator::I16x8LeS => Ok(Operator::I16x8LeS),
            &wasmparser_248::Operator::I16x8LeU => Ok(Operator::I16x8LeU),
            &wasmparser_248::Operator::I16x8GeS => Ok(Operator::I16x8GeS),
            &wasmparser_248::Operator::I16x8GeU => Ok(Operator::I16x8GeU),

            &wasmparser_248::Operator::I32x4Eq => Ok(Operator::I32x4Eq),
            &wasmparser_248::Operator::I32x4Ne => Ok(Operator::I32x4Ne),
            &wasmparser_248::Operator::I32x4LtS => Ok(Operator::I32x4LtS),
            &wasmparser_248::Operator::I32x4LtU => Ok(Operator::I32x4LtU),
            &wasmparser_248::Operator::I32x4GtS => Ok(Operator::I32x4GtS),
            &wasmparser_248::Operator::I32x4GtU => Ok(Operator::I32x4GtU),
            &wasmparser_248::Operator::I32x4LeS => Ok(Operator::I32x4LeS),
            &wasmparser_248::Operator::I32x4LeU => Ok(Operator::I32x4LeU),
            &wasmparser_248::Operator::I32x4GeS => Ok(Operator::I32x4GeS),
            &wasmparser_248::Operator::I32x4GeU => Ok(Operator::I32x4GeU),

            &wasmparser_248::Operator::I64x2Eq => Ok(Operator::I64x2Eq),
            &wasmparser_248::Operator::I64x2Ne => Ok(Operator::I64x2Ne),
            &wasmparser_248::Operator::I64x2LtS => Ok(Operator::I64x2LtS),
            &wasmparser_248::Operator::I64x2GtS => Ok(Operator::I64x2GtS),
            &wasmparser_248::Operator::I64x2LeS => Ok(Operator::I64x2LeS),
            &wasmparser_248::Operator::I64x2GeS => Ok(Operator::I64x2GeS),

            &wasmparser_248::Operator::F32x4Eq => Ok(Operator::F32x4Eq),
            &wasmparser_248::Operator::F32x4Ne => Ok(Operator::F32x4Ne),
            &wasmparser_248::Operator::F32x4Lt => Ok(Operator::F32x4Lt),
            &wasmparser_248::Operator::F32x4Gt => Ok(Operator::F32x4Gt),
            &wasmparser_248::Operator::F32x4Le => Ok(Operator::F32x4Le),
            &wasmparser_248::Operator::F32x4Ge => Ok(Operator::F32x4Ge),

            &wasmparser_248::Operator::F64x2Eq => Ok(Operator::F64x2Eq),
            &wasmparser_248::Operator::F64x2Ne => Ok(Operator::F64x2Ne),
            &wasmparser_248::Operator::F64x2Lt => Ok(Operator::F64x2Lt),
            &wasmparser_248::Operator::F64x2Gt => Ok(Operator::F64x2Gt),
            &wasmparser_248::Operator::F64x2Le => Ok(Operator::F64x2Le),
            &wasmparser_248::Operator::F64x2Ge => Ok(Operator::F64x2Ge),

            &wasmparser_248::Operator::V128Not => Ok(Operator::V128Not),
            &wasmparser_248::Operator::V128And => Ok(Operator::V128And),
            &wasmparser_248::Operator::V128AndNot => Ok(Operator::V128AndNot),
            &wasmparser_248::Operator::V128Or => Ok(Operator::V128Or),
            &wasmparser_248::Operator::V128Xor => Ok(Operator::V128Xor),
            &wasmparser_248::Operator::V128Bitselect => Ok(Operator::V128Bitselect),
            &wasmparser_248::Operator::V128AnyTrue => Ok(Operator::V128AnyTrue),

            &wasmparser_248::Operator::I8x16Abs => Ok(Operator::I8x16Abs),
            &wasmparser_248::Operator::I8x16Neg => Ok(Operator::I8x16Neg),
            &wasmparser_248::Operator::I8x16Popcnt => Ok(Operator::I8x16Popcnt),
            &wasmparser_248::Operator::I8x16AllTrue => Ok(Operator::I8x16AllTrue),
            &wasmparser_248::Operator::I8x16Bitmask => Ok(Operator::I8x16Bitmask),
            &wasmparser_248::Operator::I8x16NarrowI16x8S => Ok(Operator::I8x16NarrowI16x8S),
            &wasmparser_248::Operator::I8x16NarrowI16x8U => Ok(Operator::I8x16NarrowI16x8U),
            &wasmparser_248::Operator::I8x16Shl => Ok(Operator::I8x16Shl),
            &wasmparser_248::Operator::I8x16ShrS => Ok(Operator::I8x16ShrS),
            &wasmparser_248::Operator::I8x16ShrU => Ok(Operator::I8x16ShrU),
            &wasmparser_248::Operator::I8x16Add => Ok(Operator::I8x16Add),
            &wasmparser_248::Operator::I8x16AddSatS => Ok(Operator::I8x16AddSatS),
            &wasmparser_248::Operator::I8x16AddSatU => Ok(Operator::I8x16AddSatU),
            &wasmparser_248::Operator::I8x16Sub => Ok(Operator::I8x16Sub),
            &wasmparser_248::Operator::I8x16SubSatS => Ok(Operator::I8x16SubSatS),
            &wasmparser_248::Operator::I8x16SubSatU => Ok(Operator::I8x16SubSatU),
            &wasmparser_248::Operator::I8x16MinS => Ok(Operator::I8x16MinS),
            &wasmparser_248::Operator::I8x16MinU => Ok(Operator::I8x16MinU),
            &wasmparser_248::Operator::I8x16MaxS => Ok(Operator::I8x16MaxS),
            &wasmparser_248::Operator::I8x16MaxU => Ok(Operator::I8x16MaxU),
            &wasmparser_248::Operator::I8x16AvgrU => Ok(Operator::I8x16AvgrU),

            &wasmparser_248::Operator::I16x8ExtAddPairwiseI8x16S => {
                Ok(Operator::I16x8ExtAddPairwiseI8x16S)
            }
            &wasmparser_248::Operator::I16x8ExtAddPairwiseI8x16U => {
                Ok(Operator::I16x8ExtAddPairwiseI8x16U)
            }
            &wasmparser_248::Operator::I16x8Abs => Ok(Operator::I16x8Abs),
            &wasmparser_248::Operator::I16x8Neg => Ok(Operator::I16x8Neg),
            &wasmparser_248::Operator::I16x8Q15MulrSatS => Ok(Operator::I16x8Q15MulrSatS),
            &wasmparser_248::Operator::I16x8AllTrue => Ok(Operator::I16x8AllTrue),
            &wasmparser_248::Operator::I16x8Bitmask => Ok(Operator::I16x8Bitmask),
            &wasmparser_248::Operator::I16x8NarrowI32x4S => Ok(Operator::I16x8NarrowI32x4S),
            &wasmparser_248::Operator::I16x8NarrowI32x4U => Ok(Operator::I16x8NarrowI32x4U),
            &wasmparser_248::Operator::I16x8ExtendLowI8x16S => Ok(Operator::I16x8ExtendLowI8x16S),
            &wasmparser_248::Operator::I16x8ExtendHighI8x16S => Ok(Operator::I16x8ExtendHighI8x16S),
            &wasmparser_248::Operator::I16x8ExtendLowI8x16U => Ok(Operator::I16x8ExtendLowI8x16U),
            &wasmparser_248::Operator::I16x8ExtendHighI8x16U => Ok(Operator::I16x8ExtendHighI8x16U),
            &wasmparser_248::Operator::I16x8Shl => Ok(Operator::I16x8Shl),
            &wasmparser_248::Operator::I16x8ShrS => Ok(Operator::I16x8ShrS),
            &wasmparser_248::Operator::I16x8ShrU => Ok(Operator::I16x8ShrU),
            &wasmparser_248::Operator::I16x8Add => Ok(Operator::I16x8Add),
            &wasmparser_248::Operator::I16x8AddSatS => Ok(Operator::I16x8AddSatS),
            &wasmparser_248::Operator::I16x8AddSatU => Ok(Operator::I16x8AddSatU),
            &wasmparser_248::Operator::I16x8Sub => Ok(Operator::I16x8Sub),
            &wasmparser_248::Operator::I16x8SubSatS => Ok(Operator::I16x8SubSatS),
            &wasmparser_248::Operator::I16x8SubSatU => Ok(Operator::I16x8SubSatU),
            &wasmparser_248::Operator::I16x8Mul => Ok(Operator::I16x8Mul),
            &wasmparser_248::Operator::I16x8MinS => Ok(Operator::I16x8MinS),
            &wasmparser_248::Operator::I16x8MinU => Ok(Operator::I16x8MinU),
            &wasmparser_248::Operator::I16x8MaxS => Ok(Operator::I16x8MaxS),
            &wasmparser_248::Operator::I16x8MaxU => Ok(Operator::I16x8MaxU),
            &wasmparser_248::Operator::I16x8AvgrU => Ok(Operator::I16x8AvgrU),
            &wasmparser_248::Operator::I16x8ExtMulLowI8x16S => Ok(Operator::I16x8ExtMulLowI8x16S),
            &wasmparser_248::Operator::I16x8ExtMulHighI8x16S => Ok(Operator::I16x8ExtMulHighI8x16S),
            &wasmparser_248::Operator::I16x8ExtMulLowI8x16U => Ok(Operator::I16x8ExtMulLowI8x16U),
            &wasmparser_248::Operator::I16x8ExtMulHighI8x16U => Ok(Operator::I16x8ExtMulHighI8x16U),
            &wasmparser_248::Operator::I32x4ExtAddPairwiseI16x8S => {
                Ok(Operator::I32x4ExtAddPairwiseI16x8S)
            }
            &wasmparser_248::Operator::I32x4ExtAddPairwiseI16x8U => {
                Ok(Operator::I32x4ExtAddPairwiseI16x8U)
            }

            &wasmparser_248::Operator::I32x4Abs => Ok(Operator::I32x4Abs),
            &wasmparser_248::Operator::I32x4Neg => Ok(Operator::I32x4Neg),
            &wasmparser_248::Operator::I32x4AllTrue => Ok(Operator::I32x4AllTrue),
            &wasmparser_248::Operator::I32x4Bitmask => Ok(Operator::I32x4Bitmask),
            &wasmparser_248::Operator::I32x4ExtendLowI16x8S => Ok(Operator::I32x4ExtendLowI16x8S),
            &wasmparser_248::Operator::I32x4ExtendHighI16x8S => Ok(Operator::I32x4ExtendHighI16x8S),
            &wasmparser_248::Operator::I32x4ExtendLowI16x8U => Ok(Operator::I32x4ExtendLowI16x8U),
            &wasmparser_248::Operator::I32x4ExtendHighI16x8U => Ok(Operator::I32x4ExtendHighI16x8U),
            &wasmparser_248::Operator::I32x4Shl => Ok(Operator::I32x4Shl),
            &wasmparser_248::Operator::I32x4ShrS => Ok(Operator::I32x4ShrS),
            &wasmparser_248::Operator::I32x4ShrU => Ok(Operator::I32x4ShrU),
            &wasmparser_248::Operator::I32x4Add => Ok(Operator::I32x4Add),
            &wasmparser_248::Operator::I32x4Sub => Ok(Operator::I32x4Sub),
            &wasmparser_248::Operator::I32x4Mul => Ok(Operator::I32x4Mul),
            &wasmparser_248::Operator::I32x4MinS => Ok(Operator::I32x4MinS),
            &wasmparser_248::Operator::I32x4MinU => Ok(Operator::I32x4MinU),
            &wasmparser_248::Operator::I32x4MaxS => Ok(Operator::I32x4MaxS),
            &wasmparser_248::Operator::I32x4MaxU => Ok(Operator::I32x4MaxU),
            &wasmparser_248::Operator::I32x4DotI16x8S => Ok(Operator::I32x4DotI16x8S),
            &wasmparser_248::Operator::I32x4ExtMulLowI16x8S => Ok(Operator::I32x4ExtMulLowI16x8S),
            &wasmparser_248::Operator::I32x4ExtMulHighI16x8S => Ok(Operator::I32x4ExtMulHighI16x8S),
            &wasmparser_248::Operator::I32x4ExtMulLowI16x8U => Ok(Operator::I32x4ExtMulLowI16x8U),
            &wasmparser_248::Operator::I32x4ExtMulHighI16x8U => Ok(Operator::I32x4ExtMulHighI16x8U),
            &wasmparser_248::Operator::I64x2Abs => Ok(Operator::I64x2Abs),
            &wasmparser_248::Operator::I64x2Neg => Ok(Operator::I64x2Neg),
            &wasmparser_248::Operator::I64x2AllTrue => Ok(Operator::I64x2AllTrue),
            &wasmparser_248::Operator::I64x2Bitmask => Ok(Operator::I64x2Bitmask),
            &wasmparser_248::Operator::I64x2ExtendLowI32x4S => Ok(Operator::I64x2ExtendLowI32x4S),
            &wasmparser_248::Operator::I64x2ExtendHighI32x4S => Ok(Operator::I64x2ExtendHighI32x4S),
            &wasmparser_248::Operator::I64x2ExtendLowI32x4U => Ok(Operator::I64x2ExtendLowI32x4U),
            &wasmparser_248::Operator::I64x2ExtendHighI32x4U => Ok(Operator::I64x2ExtendHighI32x4U),
            &wasmparser_248::Operator::I64x2Shl => Ok(Operator::I64x2Shl),
            &wasmparser_248::Operator::I64x2ShrS => Ok(Operator::I64x2ShrS),
            &wasmparser_248::Operator::I64x2ShrU => Ok(Operator::I64x2ShrU),
            &wasmparser_248::Operator::I64x2Add => Ok(Operator::I64x2Add),
            &wasmparser_248::Operator::I64x2Sub => Ok(Operator::I64x2Sub),
            &wasmparser_248::Operator::I64x2Mul => Ok(Operator::I64x2Mul),
            &wasmparser_248::Operator::I64x2ExtMulLowI32x4S => Ok(Operator::I64x2ExtMulLowI32x4S),
            &wasmparser_248::Operator::I64x2ExtMulHighI32x4S => Ok(Operator::I64x2ExtMulHighI32x4S),
            &wasmparser_248::Operator::I64x2ExtMulLowI32x4U => Ok(Operator::I64x2ExtMulLowI32x4U),
            &wasmparser_248::Operator::I64x2ExtMulHighI32x4U => Ok(Operator::I64x2ExtMulHighI32x4U),
            &wasmparser_248::Operator::F32x4Ceil => Ok(Operator::F32x4Ceil),
            &wasmparser_248::Operator::F32x4Floor => Ok(Operator::F32x4Floor),
            &wasmparser_248::Operator::F32x4Trunc => Ok(Operator::F32x4Trunc),
            &wasmparser_248::Operator::F32x4Nearest => Ok(Operator::F32x4Nearest),
            &wasmparser_248::Operator::F32x4Abs => Ok(Operator::F32x4Abs),
            &wasmparser_248::Operator::F32x4Neg => Ok(Operator::F32x4Neg),
            &wasmparser_248::Operator::F32x4Sqrt => Ok(Operator::F32x4Sqrt),
            &wasmparser_248::Operator::F32x4Add => Ok(Operator::F32x4Add),
            &wasmparser_248::Operator::F32x4Sub => Ok(Operator::F32x4Sub),
            &wasmparser_248::Operator::F32x4Mul => Ok(Operator::F32x4Mul),
            &wasmparser_248::Operator::F32x4Div => Ok(Operator::F32x4Div),
            &wasmparser_248::Operator::F32x4Min => Ok(Operator::F32x4Min),
            &wasmparser_248::Operator::F32x4Max => Ok(Operator::F32x4Max),
            &wasmparser_248::Operator::F32x4PMin => Ok(Operator::F32x4PMin),
            &wasmparser_248::Operator::F32x4PMax => Ok(Operator::F32x4PMax),
            &wasmparser_248::Operator::F64x2Ceil => Ok(Operator::F64x2Ceil),
            &wasmparser_248::Operator::F64x2Floor => Ok(Operator::F64x2Floor),
            &wasmparser_248::Operator::F64x2Trunc => Ok(Operator::F64x2Trunc),
            &wasmparser_248::Operator::F64x2Nearest => Ok(Operator::F64x2Nearest),
            &wasmparser_248::Operator::F64x2Abs => Ok(Operator::F64x2Abs),
            &wasmparser_248::Operator::F64x2Neg => Ok(Operator::F64x2Neg),
            &wasmparser_248::Operator::F64x2Sqrt => Ok(Operator::F64x2Sqrt),
            &wasmparser_248::Operator::F64x2Add => Ok(Operator::F64x2Add),
            &wasmparser_248::Operator::F64x2Sub => Ok(Operator::F64x2Sub),
            &wasmparser_248::Operator::F64x2Mul => Ok(Operator::F64x2Mul),
            &wasmparser_248::Operator::F64x2Div => Ok(Operator::F64x2Div),
            &wasmparser_248::Operator::F64x2Min => Ok(Operator::F64x2Min),
            &wasmparser_248::Operator::F64x2Max => Ok(Operator::F64x2Max),
            &wasmparser_248::Operator::F64x2PMin => Ok(Operator::F64x2PMin),
            &wasmparser_248::Operator::F64x2PMax => Ok(Operator::F64x2PMax),
            &wasmparser_248::Operator::I32x4TruncSatF32x4S => Ok(Operator::I32x4TruncSatF32x4S),
            &wasmparser_248::Operator::I32x4TruncSatF32x4U => Ok(Operator::I32x4TruncSatF32x4U),
            &wasmparser_248::Operator::F32x4ConvertI32x4S => Ok(Operator::F32x4ConvertI32x4S),
            &wasmparser_248::Operator::F32x4ConvertI32x4U => Ok(Operator::F32x4ConvertI32x4U),
            &wasmparser_248::Operator::I32x4TruncSatF64x2SZero => Ok(Operator::I32x4TruncSatF64x2SZero),
            &wasmparser_248::Operator::I32x4TruncSatF64x2UZero => Ok(Operator::I32x4TruncSatF64x2UZero),
            &wasmparser_248::Operator::F64x2ConvertLowI32x4S => Ok(Operator::F64x2ConvertLowI32x4S),
            &wasmparser_248::Operator::F64x2ConvertLowI32x4U => Ok(Operator::F64x2ConvertLowI32x4U),
            &wasmparser_248::Operator::F32x4DemoteF64x2Zero => Ok(Operator::F32x4DemoteF64x2Zero),
            &wasmparser_248::Operator::F64x2PromoteLowF32x4 => Ok(Operator::F64x2PromoteLowF32x4),

            &wasmparser_248::Operator::CallRef { type_index } => Ok(Operator::CallRef {
                sig_index: Signature::from(type_index),
            }),
            &wasmparser_248::Operator::RefIsNull => Ok(Operator::RefIsNull),
            &wasmparser_248::Operator::RefNull {
                hty: wasmparser_248::HeapType::Concrete(wasmparser_248::UnpackedIndex::Module(sig)),
            } => Ok(Operator::RefNull {
                sig_index: Signature::from(sig),
            }),
            &wasmparser_248::Operator::RefFunc { function_index } => Ok(Operator::RefFunc {
                func_index: Func::from(function_index),
            }),

            _ => Err(()),
        }
    }
}

impl std::convert::From<wasmparser_248::MemArg> for MemoryArg {
    fn from(value: wasmparser_248::MemArg) -> MemoryArg {
        MemoryArg {
            align: value.align as u32,
            offset: u32::try_from(value.offset).expect("offset too large"),
            memory: Memory::from(value.memory),
        }
    }
}

impl std::convert::From<MemoryArg> for wasm_encoder::MemArg {
    fn from(value: MemoryArg) -> wasm_encoder::MemArg {
        wasm_encoder::MemArg {
            offset: value.offset as u64,
            align: value.align,
            memory_index: value.memory.index() as u32,
        }
    }
}
