//! CLIF opcode -> waffle `Operator` lowering table.
//!
//! waffle's Operator enum is 1:1 with wasm opcodes, so this is instruction selection,
//! not renaming: some CLIF ops expand to short multi-op sequences (condition
//! normalization, shift-amount width fixups, i128 pair legalization). Anything not in
//! the starter set fails with a clear "unimplemented opcode" error — the gap list is a
//! prototype deliverable.

use crate::error::{Context, Result};
use crate::{bail, ensure, unsupported};
use cranelift_codegen::ir::{
    self, InstructionData, Opcode, condcodes::FloatCC, condcodes::IntCC, types,
};
use waffle::{FunctionBody, MemoryArg, Operator, Type, ValueDef};

use crate::bridge::FnCx;
use crate::i128_lower::{self, ShiftKind};
use crate::map_type;

/// Normalize a CLIF condition value (i8 icmp result, or any int used as a truth
/// value) to a wasm i32. i8/i16/i32 map straight through; i64 gets eqz/eqz; i128 is
/// nonzero iff (lo | hi) is nonzero.
pub fn coerce_cond(
    cx: &FnCx,
    body: &mut FunctionBody,
    wb: waffle::Block,
    cond: ir::Value,
) -> Result<waffle::Value> {
    if cx.vty(cond) == types::I128 {
        let (lo, hi) = cx.pair(cond)?;
        let or = body.add_op(wb, Operator::I64Or, &[lo, hi], &[Type::I64]);
        let z = body.add_op(wb, Operator::I64Eqz, &[or], &[Type::I32]);
        return Ok(body.add_op(wb, Operator::I32Eqz, &[z], &[Type::I32]));
    }
    let wv = cx.one(cond)?;
    match map_type(cx.vty(cond))? {
        Type::I32 => Ok(wv),
        Type::I64 => {
            let z = body.add_op(wb, Operator::I64Eqz, &[wv], &[Type::I32]);
            Ok(body.add_op(wb, Operator::I32Eqz, &[z], &[Type::I32]))
        }
        other => bail!("branch/select condition has non-integer type {other}"),
    }
}

pub fn lower_inst(
    cx: &mut FnCx,
    body: &mut FunctionBody,
    wb: waffle::Block,
    inst: ir::Inst,
) -> Result<()> {
    let dfg = &cx.clif.dfg;
    match dfg.insts[inst] {
        // --- Constants ---
        InstructionData::UnaryConst {
            opcode: Opcode::Vconst,
            constant_handle,
        } => {
            let result = dfg.first_result(inst);
            let ty = dfg.value_type(result);
            ensure!(
                ty.is_vector(),
                "vconst result must be a fixed vector, got {ty}"
            );
            let data = dfg.constants.get(constant_handle).as_slice();
            ensure!(
                data.len() * 8 == ty.bits() as usize,
                "vconst data size does not match {ty}"
            );
            let mut values = Vec::new();
            for chunk in data.chunks(16) {
                let mut bytes = [0; 16];
                bytes[..chunk.len()].copy_from_slice(chunk);
                values.push(body.add_op(
                    wb,
                    Operator::V128Const {
                        value: u128::from_le_bytes(bytes),
                    },
                    &[],
                    &[Type::V128],
                ));
            }
            cx.bind_vector(result, normalize_vector(body, wb, ty, values)?);
        }
        InstructionData::UnaryImm {
            opcode: Opcode::Iconst,
            imm,
        } => {
            let rty = dfg.value_type(dfg.first_result(inst));
            let bits = imm.bits();
            let (op, wty) = match rty {
                types::I8 => (
                    Operator::I32Const {
                        value: bits as u32 & 0xFF,
                    },
                    Type::I32,
                ),
                types::I16 => (
                    Operator::I32Const {
                        value: bits as u32 & 0xFFFF,
                    },
                    Type::I32,
                ),
                types::I32 => (Operator::I32Const { value: bits as u32 }, Type::I32),
                types::I64 => (Operator::I64Const { value: bits as u64 }, Type::I64),
                other => unsupported!("iconst of unsupported type {other}"),
            };
            let wv = body.add_op(wb, op, &[], &[wty]);
            cx.bind1(dfg.first_result(inst), wv);
        }
        InstructionData::UnaryIeee32 {
            opcode: Opcode::F32const,
            imm,
        } => {
            let wv = body.add_op(
                wb,
                Operator::F32Const { value: imm.bits() },
                &[],
                &[Type::F32],
            );
            cx.bind1(dfg.first_result(inst), wv);
        }
        InstructionData::UnaryIeee64 {
            opcode: Opcode::F64const,
            imm,
        } => {
            let wv = body.add_op(
                wb,
                Operator::F64Const { value: imm.bits() },
                &[],
                &[Type::F64],
            );
            cx.bind1(dfg.first_result(inst), wv);
        }

        // --- Unary int conversions (and isplit) ---
        InstructionData::Unary { opcode, arg } => {
            lower_unary(cx, body, wb, inst, opcode, arg)?;
        }

        InstructionData::Shuffle {
            opcode: Opcode::Shuffle,
            args,
            imm,
        } => {
            let result = dfg.first_result(inst);
            let ty = dfg.value_type(result);
            ensure!(
                ty == types::I8X16,
                "shuffle currently requires i8x16, got {ty}"
            );
            let data = dfg.immediates[imm].as_slice();
            ensure!(data.len() == 16, "shuffle mask must contain 16 bytes");
            let lanes: [u8; 16] = data.try_into().unwrap();
            let a = cx.vector(args[0])?;
            let b = cx.vector(args[1])?;
            let value = body.add_op(
                wb,
                Operator::I8x16Shuffle { lanes },
                &[a[0], b[0]],
                &[Type::V128],
            );
            cx.bind_vector(result, vec![value]);
        }

        InstructionData::Binary {
            opcode: opcode @ (Opcode::Swizzle | Opcode::X86Pshufb),
            args,
        } => {
            let result = dfg.first_result(inst);
            let ty = dfg.value_type(result);
            ensure!(
                ty == types::I8X16,
                "swizzle currently requires i8x16, got {ty}"
            );
            let x = cx.vector(args[0])?;
            let mask = cx.vector(args[1])?;
            let value = body.add_op(wb, Operator::I8x16Swizzle, &[x[0], mask[0]], &[Type::V128]);
            let value = if opcode == Opcode::X86Pshufb {
                let zero = body.add_op(wb, Operator::V128Const { value: 0 }, &[], &[Type::V128]);
                let negative = body.add_op(wb, Operator::I8x16LtS, &[mask[0], zero], &[Type::V128]);
                body.add_op(wb, Operator::V128AndNot, &[value, negative], &[Type::V128])
            } else {
                value
            };
            cx.bind_vector(result, vec![value]);
        }

        InstructionData::BinaryImm8 {
            opcode: Opcode::Extractlane,
            arg,
            imm,
        } => {
            let result = dfg.first_result(inst);
            let vector_ty = cx.vty(arg);
            let lane_ty = vector_ty.lane_type();
            let lane_bits = lane_ty.bits();
            let lane_index = imm as usize;
            ensure!(
                lane_index < vector_ty.lane_count() as usize,
                "extractlane index {lane_index} out of range for {vector_ty}"
            );
            let chunk_index = lane_index * lane_bits as usize / 128;
            let chunk_lane = lane_index % (128 / lane_bits as usize);
            let vector = cx.vector(arg)?;
            let op = extract_lane_op(lane_ty, chunk_lane as u8)?;
            let value = body.add_op(wb, op, &[vector[chunk_index]], &[map_type(lane_ty)?]);
            cx.bind1(result, value);
        }

        InstructionData::TernaryImm8 {
            opcode: Opcode::Insertlane,
            args,
            imm,
        } => {
            let result = dfg.first_result(inst);
            let ty = dfg.value_type(result);
            let lane_ty = ty.lane_type();
            let lane_bits = lane_ty.bits();
            let lane_index = imm as usize;
            ensure!(
                lane_index < ty.lane_count() as usize,
                "insertlane index {lane_index} out of range for {ty}"
            );
            let chunk_index = lane_index * lane_bits as usize / 128;
            let chunk_lane = lane_index % (128 / lane_bits as usize);
            let mut vector = cx.vector(args[0])?;
            let scalar = cx.one(args[1])?;
            let op = replace_lane_op(lane_ty, chunk_lane as u8)?;
            vector[chunk_index] =
                body.add_op(wb, op, &[vector[chunk_index], scalar], &[Type::V128]);
            cx.bind_vector(result, normalize_vector(body, wb, ty, vector)?);
        }

        // cg_clif sprinkles `nop`s as MIR-comment anchors; they carry nothing.
        InstructionData::NullAry {
            opcode: Opcode::Nop,
        } => {}

        // bitcast (LoadNoOffset format): same-size reinterpretation.
        InstructionData::LoadNoOffset {
            opcode: Opcode::Bitcast,
            arg,
            ..
        } => {
            let result = dfg.first_result(inst);
            let (src, dst) = (cx.vty(arg), dfg.value_type(result));
            if src.is_vector() && dst.is_vector() {
                ensure!(
                    src.bits() == dst.bits(),
                    "bitcast {src} -> {dst} changes vector size"
                );
                cx.bind_vector(result, cx.vector(arg)?);
                return Ok(());
            }
            let v = cx.one(arg)?;
            let wv = match (src, dst) {
                (types::F32, types::I32) => {
                    body.add_op(wb, Operator::I32ReinterpretF32, &[v], &[Type::I32])
                }
                (types::I32, types::F32) => {
                    body.add_op(wb, Operator::F32ReinterpretI32, &[v], &[Type::F32])
                }
                (types::F64, types::I64) => {
                    body.add_op(wb, Operator::I64ReinterpretF64, &[v], &[Type::I64])
                }
                (types::I64, types::F64) => {
                    body.add_op(wb, Operator::F64ReinterpretI64, &[v], &[Type::F64])
                }
                (s, d) if s == d => v,
                (s, d) => unsupported!("bitcast {s} -> {d} unimplemented"),
            };
            cx.bind1(result, wv);
        }

        // --- Statics: symbol_value / global_value -> linear-memory address ---
        InstructionData::UnaryGlobalValue {
            opcode: Opcode::SymbolValue,
            global_value,
        } => {
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
                unsupported!("unimplemented global value form {gvd:?} (only Symbol)");
            };
            ensure!(!tls, "TLS symbols are out of scope");
            // Object mode: the address is the linker's to assign — emit a marker
            // global.get; the object writer splices it into i32.const + reloc.
            if let Some(mk) = cx.m.object_markers {
                let ir::ExternalName::User(r) = name else {
                    unsupported!("unsupported data symbol name {name:?} in object mode");
                };
                let user = cx
                    .clif
                    .params
                    .user_named_funcs()
                    .get(*r)
                    .context("dangling userextname in object mode")?;
                ensure!(
                    user.namespace == 1,
                    "data symbol has namespace {} (expected 1)",
                    user.namespace
                );
                let off: i64 = (*offset).into();
                let g = mk.data.get(&(user.index, off)).with_context(|| {
                    format!("no marker for data ordinal {} offset {off}", user.index)
                })?;
                let wv = body.add_op(
                    wb,
                    Operator::GlobalGet { global_index: *g },
                    &[],
                    &[Type::I32],
                );
                cx.bind1(result, wv);
                return Ok(());
            }
            let base = match name {
                ir::ExternalName::User(r) => {
                    // Side table FIRST: in reader-parsed dumps the `userextnameN` ref
                    // indexes cg_clif's original table, which the text doesn't carry —
                    // cranelift-reader rebuilds its own table from `u0:M` callee tokens,
                    // so the ref can FALSELY resolve to a callee entry. The comment-borne
                    // side table is the only trustworthy identity for parsed input.
                    if let Some(sym) = cx.gv_symbols.get(&global_value.as_u32()) {
                        cx.m.data_addr_for_symbol(sym)?
                    } else if let Some(user) = cx.clif.params.user_named_funcs().get(*r) {
                        // Hand-built path: cg_clif convention, namespace 1 = DataId.
                        ensure!(
                            user.namespace == 1,
                            "data symbol has namespace {} (expected 1)",
                            user.namespace
                        );
                        *cx.m.data_addrs.get(user.index as usize).with_context(|| {
                            format!(
                                "data index {} out of range ({} objects)",
                                user.index,
                                cx.m.data_addrs.len()
                            )
                        })?
                    } else {
                        bail!(
                            "gv{}: dangling userextname and no side-table entry",
                            global_value.as_u32()
                        )
                    }
                }
                other => unsupported!("unsupported data symbol name {other:?}"),
            };
            let off: i64 = (*offset).into();
            let addr = (base as i64 + off) as u32;
            let wv = body.add_op(wb, Operator::I32Const { value: addr }, &[], &[Type::I32]);
            cx.bind1(result, wv);
        }

        // --- Integer & float binary arithmetic / bitwise ---
        //
        // Narrow ints (i8/i16) live in I32 with a canonical zero-extended representation.
        InstructionData::Binary { opcode, args } => {
            let result = dfg.first_result(inst);
            let rty = dfg.value_type(result);

            if rty.is_vector() {
                lower_vector_binary(cx, body, wb, result, opcode, args)?;
                return Ok(());
            }

            // i128: pair legalization.
            if rty == types::I128 {
                lower_binary_i128(cx, body, wb, result, opcode, args)?;
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
                !(matches!(opcode, Opcode::Rotl | Opcode::Rotr)
                    && matches!(rty, types::I8 | types::I16)),
                "narrow-int rotate ({rty}) unimplemented"
            );
            let mut b = if is_shift {
                let amt_ty = map_type(cx.vty(args[1]))?;
                match (wty, amt_ty) {
                    (Type::I32, Type::I64) => {
                        body.add_op(wb, Operator::I32WrapI64, &[b], &[Type::I32])
                    }
                    (Type::I64, Type::I32) => {
                        body.add_op(wb, Operator::I64ExtendI32U, &[b], &[Type::I64])
                    }
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
        }

        // --- Comparisons ---
        InstructionData::IntCompare {
            opcode: Opcode::Icmp,
            args,
            cond,
        } => {
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
                        .map(|value| {
                            body.add_op(wb, Operator::V128Xor, &[value, sign], &[Type::V128])
                        })
                        .collect();
                    let rhs = cx
                        .vector(args[1])?
                        .into_iter()
                        .map(|value| {
                            body.add_op(wb, Operator::V128Xor, &[value, sign], &[Type::V128])
                        })
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
        }
        InstructionData::FloatCompare {
            opcode: Opcode::Fcmp,
            args,
            cond,
        } => {
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
        }

        // --- Select ---
        InstructionData::Ternary {
            opcode: Opcode::Select,
            args,
        } => {
            let result = dfg.first_result(inst);
            let rty = dfg.value_type(result);
            let c = coerce_cond(cx, body, wb, args[0])?;
            if rty == types::I128 {
                let (xl, xh) = cx.pair(args[1])?;
                let (yl, yh) = cx.pair(args[2])?;
                let lo = body.add_op(wb, Operator::Select, &[xl, yl, c], &[Type::I64]);
                let hi = body.add_op(wb, Operator::Select, &[xh, yh, c], &[Type::I64]);
                cx.bind2(result, lo, hi);
                return Ok(());
            }
            if rty.is_vector() {
                let yes = cx.vector(args[1])?;
                let no = cx.vector(args[2])?;
                ensure!(yes.len() == no.len(), "vector select chunk count mismatch");
                let values = yes
                    .into_iter()
                    .zip(no)
                    .map(|(yes, no)| {
                        body.add_op(wb, Operator::Select, &[yes, no, c], &[Type::V128])
                    })
                    .collect();
                cx.bind_vector(result, normalize_vector(body, wb, rty, values)?);
                return Ok(());
            }
            let wty = map_type(rty)?;
            let x = cx.one(args[1])?;
            let y = cx.one(args[2])?;
            // wasm select returns the FIRST operand when cond != 0 — same as CLIF.
            let wv = body.add_op(wb, Operator::Select, &[x, y, c], &[wty]);
            cx.bind1(result, wv);
        }

        InstructionData::Ternary {
            opcode: Opcode::Bitselect,
            args,
        } => {
            let result = dfg.first_result(inst);
            let ty = dfg.value_type(result);
            ensure!(ty.is_vector(), "bitselect requires a vector, got {ty}");
            let mask = cx.vector(args[0])?;
            let yes = cx.vector(args[1])?;
            let no = cx.vector(args[2])?;
            ensure!(
                mask.len() == yes.len() && yes.len() == no.len(),
                "bitselect chunk count mismatch"
            );
            let values = mask
                .into_iter()
                .zip(yes)
                .zip(no)
                .map(|((mask, yes), no)| {
                    body.add_op(wb, Operator::V128Bitselect, &[yes, no, mask], &[Type::V128])
                })
                .collect();
            cx.bind_vector(result, normalize_vector(body, wb, ty, values)?);
        }

        InstructionData::Ternary {
            opcode: Opcode::Blendv,
            args,
        } => {
            let result = dfg.first_result(inst);
            let ty = dfg.value_type(result);
            ensure!(ty.is_vector(), "blendv requires a vector, got {ty}");
            let lane_ty = ty.lane_type();
            let mask_op = match lane_ty.bits() {
                8 => Operator::I8x16LtS,
                16 => Operator::I16x8LtS,
                32 => Operator::I32x4LtS,
                64 => Operator::I64x2LtS,
                _ => unsupported!("blendv lane type {lane_ty} is unsupported"),
            };
            let mask = cx.vector(args[0])?;
            let yes = cx.vector(args[1])?;
            let no = cx.vector(args[2])?;
            ensure!(
                mask.len() == yes.len() && yes.len() == no.len(),
                "blendv chunk count mismatch"
            );
            let zero = body.add_op(wb, Operator::V128Const { value: 0 }, &[], &[Type::V128]);
            let values = mask
                .into_iter()
                .zip(yes)
                .zip(no)
                .map(|((mask, yes), no)| {
                    let sign_mask = body.add_op(wb, mask_op, &[mask, zero], &[Type::V128]);
                    body.add_op(
                        wb,
                        Operator::V128Bitselect,
                        &[yes, no, sign_mask],
                        &[Type::V128],
                    )
                })
                .collect();
            cx.bind_vector(result, normalize_vector(body, wb, ty, values)?);
        }

        // --- Memory ---
        InstructionData::Load {
            opcode,
            arg,
            flags: _,
            offset,
        } => {
            let addr = lower_addr(cx, arg)?;
            let result = dfg.first_result(inst);
            let rty = dfg.value_type(result);
            if rty.is_vector() && opcode == Opcode::Load {
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
                    let zero =
                        body.add_op(wb, Operator::V128Const { value: 0 }, &[], &[Type::V128]);
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
                        let memory = mem_arg_at(cx, base_offset + i as i32 * 16)?;
                        values.push(body.add_op(
                            wb,
                            Operator::V128Load { memory },
                            &[addr],
                            &[Type::V128],
                        ));
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
                let m8 = mem_arg(cx, (off + 8).into())?;
                let lo = body.add_op(wb, Operator::I64Load { memory: m0 }, &[addr], &[Type::I64]);
                let hi = body.add_op(wb, Operator::I64Load { memory: m8 }, &[addr], &[Type::I64]);
                cx.bind2(result, lo, hi);
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
                (Opcode::Load, types::I16) => Operator::I32Load16U { memory },
                (Opcode::Load, types::I32) => Operator::I32Load { memory },
                (Opcode::Load, types::I64) => Operator::I64Load { memory },
                (Opcode::Load, types::F32) => Operator::F32Load { memory },
                (Opcode::Load, types::F64) => Operator::F64Load { memory },
                // Explicit widening loads.
                (Opcode::Uload8, types::I32) => Operator::I32Load8U { memory },
                (Opcode::Sload8, types::I32) => Operator::I32Load8S { memory },
                (Opcode::Uload16, types::I32) => Operator::I32Load16U { memory },
                (Opcode::Sload16, types::I32) => Operator::I32Load16S { memory },
                (Opcode::Uload8, types::I64) => Operator::I64Load8U { memory },
                (Opcode::Sload8, types::I64) => Operator::I64Load8S { memory },
                (Opcode::Uload16, types::I64) => Operator::I64Load16U { memory },
                (Opcode::Sload16, types::I64) => Operator::I64Load16S { memory },
                (Opcode::Uload32, types::I64) => Operator::I64Load32U { memory },
                (Opcode::Sload32, types::I64) => Operator::I64Load32S { memory },
                (op, ty) => unsupported!("unimplemented load `{op}` of type {ty}"),
            };
            let wv = body.add_op(wb, op, &[addr], &[wty]);
            if rty.is_vector() {
                cx.bind_vector(result, vec![wv]);
            } else {
                cx.bind1(result, wv);
            }
        }
        InstructionData::Store {
            opcode,
            args,
            flags: _,
            offset,
        } => {
            if cx.vty(args[0]).is_vector() && opcode == Opcode::Store {
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
                        let memory = mem_arg_at(cx, base_offset + i as i32 * 16)?;
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
                let m8 = mem_arg(cx, (off + 8).into())?;
                body.add_op(wb, Operator::I64Store { memory: m0 }, &[addr, lo], &[]);
                body.add_op(wb, Operator::I64Store { memory: m8 }, &[addr, hi], &[]);
                return Ok(());
            }
            let value = cx.one(args[0])?;
            let addr = lower_addr(cx, args[1])?;
            let memory = mem_arg(cx, offset)?;
            let vty = cx.vty(args[0]);
            let op = match (opcode, vty) {
                (Opcode::Store, types::I8) => Operator::I32Store8 { memory },
                (Opcode::Store, types::I16) => Operator::I32Store16 { memory },
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
        }

        // --- Shadow stack ---
        InstructionData::StackAddr {
            opcode: Opcode::StackAddr,
            stack_slot,
            offset,
        } => {
            let result = dfg.first_result(inst);
            ensure!(
                dfg.value_type(result) == types::I32,
                "stack_addr result must be i32"
            );
            let addr = cx.slot_addr(body, wb, stack_slot, offset.into())?;
            cx.bind1(result, addr);
        }

        InstructionData::LoadNoOffset {
            opcode: Opcode::AtomicLoad,
            arg,
            ..
        } => {
            ensure_shared_memory(cx, "atomic_load")?;
            let result = dfg.first_result(inst);
            let ty = dfg.value_type(result);
            let memory = atomic_mem_arg(cx, ty)?;
            let op = match ty {
                types::I8 => Operator::I32AtomicLoad8U { memarg: memory },
                types::I16 => Operator::I32AtomicLoad16U { memarg: memory },
                types::I32 => Operator::I32AtomicLoad { memarg: memory },
                types::I64 => Operator::I64AtomicLoad { memarg: memory },
                other => unsupported!("atomic_load of {other} is unsupported"),
            };
            let addr = lower_addr(cx, arg)?;
            let value = body.add_op(wb, op, &[addr], &[map_type(ty)?]);
            cx.bind1(result, value);
        }
        InstructionData::StoreNoOffset {
            opcode: Opcode::AtomicStore,
            args,
            ..
        } => {
            ensure_shared_memory(cx, "atomic_store")?;
            let value_ty = cx.vty(args[0]);
            let memory = atomic_mem_arg(cx, value_ty)?;
            let op = match value_ty {
                types::I8 => Operator::I32AtomicStore8 { memarg: memory },
                types::I16 => Operator::I32AtomicStore16 { memarg: memory },
                types::I32 => Operator::I32AtomicStore { memarg: memory },
                types::I64 => Operator::I64AtomicStore { memarg: memory },
                other => unsupported!("atomic_store of {other} is unsupported"),
            };
            let value = cx.one(args[0])?;
            let addr = lower_addr(cx, args[1])?;
            body.add_op(wb, op, &[addr, value], &[]);
        }
        InstructionData::AtomicRmw {
            opcode: Opcode::AtomicRmw,
            args,
            op: rmw_op,
            ..
        } => {
            use cranelift_codegen::ir::AtomicRmwOp;
            ensure_shared_memory(cx, "atomic_rmw")?;
            let result = dfg.first_result(inst);
            let ty = dfg.value_type(result);
            let memory = atomic_mem_arg(cx, ty)?;
            let narrow = matches!(ty, types::I8 | types::I16);
            let op = match (ty, rmw_op) {
                (types::I8, AtomicRmwOp::Add) => Operator::I32AtomicRmw8AddU { memarg: memory },
                (types::I8, AtomicRmwOp::Sub) => Operator::I32AtomicRmw8SubU { memarg: memory },
                (types::I8, AtomicRmwOp::And) => Operator::I32AtomicRmw8AndU { memarg: memory },
                (types::I8, AtomicRmwOp::Or) => Operator::I32AtomicRmw8OrU { memarg: memory },
                (types::I8, AtomicRmwOp::Xor) => Operator::I32AtomicRmw8XorU { memarg: memory },
                (types::I8, AtomicRmwOp::Xchg) => Operator::I32AtomicRmw8XchgU { memarg: memory },
                (types::I16, AtomicRmwOp::Add) => Operator::I32AtomicRmw16AddU { memarg: memory },
                (types::I16, AtomicRmwOp::Sub) => Operator::I32AtomicRmw16SubU { memarg: memory },
                (types::I16, AtomicRmwOp::And) => Operator::I32AtomicRmw16AndU { memarg: memory },
                (types::I16, AtomicRmwOp::Or) => Operator::I32AtomicRmw16OrU { memarg: memory },
                (types::I16, AtomicRmwOp::Xor) => Operator::I32AtomicRmw16XorU { memarg: memory },
                (types::I16, AtomicRmwOp::Xchg) => Operator::I32AtomicRmw16XchgU { memarg: memory },
                (types::I32, AtomicRmwOp::Add) => Operator::I32AtomicRmwAdd { memarg: memory },
                (types::I32, AtomicRmwOp::Sub) => Operator::I32AtomicRmwSub { memarg: memory },
                (types::I32, AtomicRmwOp::And) => Operator::I32AtomicRmwAnd { memarg: memory },
                (types::I32, AtomicRmwOp::Or) => Operator::I32AtomicRmwOr { memarg: memory },
                (types::I32, AtomicRmwOp::Xor) => Operator::I32AtomicRmwXor { memarg: memory },
                (types::I32, AtomicRmwOp::Xchg) => Operator::I32AtomicRmwXchg { memarg: memory },
                (types::I64, AtomicRmwOp::Add) => Operator::I64AtomicRmwAdd { memarg: memory },
                (types::I64, AtomicRmwOp::Sub) => Operator::I64AtomicRmwSub { memarg: memory },
                (types::I64, AtomicRmwOp::And) => Operator::I64AtomicRmwAnd { memarg: memory },
                (types::I64, AtomicRmwOp::Or) => Operator::I64AtomicRmwOr { memarg: memory },
                (types::I64, AtomicRmwOp::Xor) => Operator::I64AtomicRmwXor { memarg: memory },
                (types::I64, AtomicRmwOp::Xchg) => Operator::I64AtomicRmwXchg { memarg: memory },
                (_, other) => {
                    unsupported!(
                        "atomic_rmw operation {other} on {ty} has no direct wasm atomic opcode"
                    )
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
        }
        InstructionData::AtomicCas {
            opcode: Opcode::AtomicCas,
            args,
            ..
        } => {
            ensure_shared_memory(cx, "atomic_cas")?;
            let result = dfg.first_result(inst);
            let ty = dfg.value_type(result);
            let memory = atomic_mem_arg(cx, ty)?;
            let op = match ty {
                types::I8 => Operator::I32AtomicRmw8CmpxchgU { memarg: memory },
                types::I16 => Operator::I32AtomicRmw16CmpxchgU { memarg: memory },
                types::I32 => Operator::I32AtomicRmwCmpxchg { memarg: memory },
                types::I64 => Operator::I64AtomicRmwCmpxchg { memarg: memory },
                other => unsupported!("atomic_cas of {other} is unsupported"),
            };
            let addr = lower_addr(cx, args[0])?;
            let expected = cx.one(args[1])?;
            let replacement = cx.one(args[2])?;
            let value = body.add_op(wb, op, &[addr, expected, replacement], &[map_type(ty)?]);
            cx.bind1(result, value);
        }
        InstructionData::NullAry {
            opcode: Opcode::Fence,
        } => {
            ensure_shared_memory(cx, "fence")?;
            body.add_op(wb, Operator::AtomicFence, &[], &[]);
        }

        // --- Function pointers ---
        InstructionData::FuncAddr {
            opcode: Opcode::FuncAddr,
            func_ref,
        } => {
            let result = dfg.first_result(inst);
            let result_ty = dfg.value_type(result);
            ensure!(
                matches!(result_ty, types::I32 | types::I64),
                "func_addr result must be i32 or i64, got {result_ty}"
            );
            let (ordinal, _) = resolve_callee(cx, func_ref)?;
            let ordinal =
                ordinal.context("func_addr of a libcall helper is unsupported (no table slot)")?;
            // Object mode: the table slot is the linker's to assign — marker global.
            if let Some(mk) = cx.m.object_markers {
                let g = mk
                    .funcs
                    .get(&ordinal)
                    .with_context(|| format!("no marker for func_addr of ordinal {ordinal}"))?;
                let marker = body.add_op(
                    wb,
                    Operator::GlobalGet { global_index: *g },
                    &[],
                    &[Type::I32],
                );
                let wv = if result_ty == types::I64 {
                    body.add_op(wb, Operator::I64ExtendI32U, &[marker], &[Type::I64])
                } else {
                    marker
                };
                cx.bind1(result, wv);
                return Ok(());
            }
            // Table slot 0 is null; function k lives at k+1.
            let wv = match result_ty {
                types::I32 => body.add_op(
                    wb,
                    Operator::I32Const { value: ordinal + 1 },
                    &[],
                    &[Type::I32],
                ),
                types::I64 => body.add_op(
                    wb,
                    Operator::I64Const {
                        value: (ordinal + 1) as u64,
                    },
                    &[],
                    &[Type::I64],
                ),
                _ => unreachable!(),
            };
            cx.bind1(result, wv);
        }

        // --- Direct calls ---
        InstructionData::Call {
            opcode: Opcode::Call,
            args,
            func_ref,
        } => {
            let (_, callee) = resolve_callee(cx, func_ref)?;
            let mut wargs = Vec::new();
            for &v in args.as_slice(&dfg.value_lists) {
                wargs.extend(cx.expand_use(v)?);
            }
            let op = Operator::Call {
                function_index: callee,
            };
            bind_call_results(cx, body, wb, inst, op, &wargs)?;
        }

        // --- Indirect calls ---
        InstructionData::CallIndirect {
            opcode: Opcode::CallIndirect,
            args,
            sig_ref,
        } => {
            let all = args.as_slice(&dfg.value_lists);
            ensure!(!all.is_empty(), "call_indirect with no callee operand");
            let callee_ptr = all[0];
            let table_index = match cx.vty(callee_ptr) {
                types::I32 => cx.one(callee_ptr)?,
                types::I64 => {
                    let address = cx.one(callee_ptr)?;
                    body.add_op(wb, Operator::I32WrapI64, &[address], &[Type::I32])
                }
                other => bail!("call_indirect callee pointer must be i32 or i64, got {other}"),
            };
            let mut wargs = Vec::new();
            for &v in &all[1..] {
                wargs.extend(cx.expand_use(v)?);
            }
            // wasm call_indirect takes the table index as the LAST operand.
            wargs.push(table_index);
            let sig_index = *cx
                .sig_map
                .get(&sig_ref)
                .context("call_indirect signature not interned")?;
            let op = Operator::CallIndirect {
                sig_index,
                table_index: cx.m.table,
            };
            bind_call_results(cx, body, wb, inst, op, &wargs)?;
        }

        ref other => unsupported!("unimplemented opcode {}", other.opcode()),
    }
    Ok(())
}

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

fn splat_op(lane: ir::Type) -> Result<Operator> {
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

fn replace_lane_op(lane: ir::Type, index: u8) -> Result<Operator> {
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

fn extract_lane_op(lane: ir::Type, index: u8) -> Result<Operator> {
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

fn vector_binary_operator(opcode: Opcode, lane: ir::Type) -> Result<Operator> {
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

fn lower_vector_binary(
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

fn lower_vector_copysign(
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

fn lower_vector_mulhi(
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
                        value: lane_ty.bits() as u32,
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

fn lower_vector_shift(
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
    let width = lane_ty.bits() as u32;
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

fn lower_iadd_pairwise(
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
        lane_count % 2 == 0,
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

fn vector_int_compare(cond: IntCC, lane: ir::Type) -> Result<Operator> {
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

fn vector_float_compare(cond: FloatCC, lane: ir::Type) -> Result<Operator> {
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

fn vector_float_compare_value(
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

fn vector_unordered_mask(
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

fn vector_float_unary_operator(opcode: Opcode, lane: ir::Type) -> Result<Operator> {
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

fn lower_unary(
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
            let f64src = cx.vty(arg) == types::F64;
            let v = cx.one(arg)?;
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
                unsupported!("fcvt to i128 unimplemented");
            }
            cx.bind1(result, wv);
        }
        Opcode::FcvtToSint | Opcode::FcvtToUint => {
            // Trapping form: wasm trunc traps on NaN/overflow exactly where CLIF does
            // (i32/i64 destinations only; Rust `as` uses the saturating form anyway).
            let result = dfg.first_result(inst);
            let dst = dfg.value_type(result);
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
            ensure!(src_ty != types::I128, "fcvt from i128 unimplemented");
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
fn bitrev32(body: &mut FunctionBody, wb: waffle::Block, v: waffle::Value) -> waffle::Value {
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

fn bswap32(body: &mut FunctionBody, wb: waffle::Block, v: waffle::Value) -> waffle::Value {
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

fn bswap64(body: &mut FunctionBody, wb: waffle::Block, v: waffle::Value) -> waffle::Value {
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
fn clamp_i32(
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

fn lower_binary_i128(
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
            unsupported!("unimplemented i128 binary opcode {other} (imul.i128 is a known gap)")
        }
    }
    Ok(())
}

/// Emit a call-shaped operator and bind its (expanded, possibly multi-value) results.
fn bind_call_results(
    cx: &mut FnCx,
    body: &mut FunctionBody,
    wb: waffle::Block,
    inst: ir::Inst,
    op: Operator,
    wargs: &[waffle::Value],
) -> Result<()> {
    let results: Vec<ir::Value> = cx.clif.dfg.inst_results(inst).to_vec();
    // Flatten result types (i128 -> 2xI64).
    let mut tys = Vec::new();
    let mut widths = Vec::new(); // wasm values per CLIF result
    for &r in &results {
        let expanded = crate::expand_type(cx.clif.dfg.value_type(r))?;
        widths.push(expanded.len());
        tys.extend(expanded);
    }
    let call = body.add_op(wb, op, wargs, &tys);
    match tys.len() {
        0 => {}
        1 => {
            let ty = cx.clif.dfg.value_type(results[0]);
            if ty.is_vector() {
                cx.bind_vector(results[0], normalize_vector(body, wb, ty, vec![call])?);
            } else {
                let value = if matches!(ty, types::I8 | types::I16) {
                    mask_narrow(body, wb, call, ty)
                } else {
                    call
                };
                cx.bind1(results[0], value);
            }
        }
        // Multi-value: waffle models the call as one tuple-typed value; each wasm-level
        // result is a PickOutput projection (risk probe: external builders plausibly
        // never exercised this path).
        _ => {
            let mut idx = 0u32;
            for (&r, &w) in results.iter().zip(widths.iter()) {
                let mut picked = Vec::new();
                for _ in 0..w {
                    let ty = tys[idx as usize];
                    let pv = body.add_value(ValueDef::PickOutput(call, idx, ty));
                    body.append_to_block(wb, pv);
                    picked.push(pv);
                    idx += 1;
                }
                if cx.clif.dfg.value_type(r).is_vector() {
                    let ty = cx.clif.dfg.value_type(r);
                    cx.bind_vector(r, normalize_vector(body, wb, ty, picked)?);
                } else {
                    match w {
                        1 => {
                            let ty = cx.clif.dfg.value_type(r);
                            let value = if matches!(ty, types::I8 | types::I16) {
                                mask_narrow(body, wb, picked[0], ty)
                            } else {
                                picked[0]
                            };
                            cx.bind1(r, value)
                        }
                        2 => cx.bind2(r, picked[0], picked[1]),
                        _ => bail!("unexpected result width {w}"),
                    }
                }
            }
        }
    }
    Ok(())
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
fn sign_extend_narrow(
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

/// The pointer-width tripwire: addresses must be CLIF i32. CLIF captured from a
/// 64-bit target carries i64 addresses; it must fail loudly here, never truncate
/// (see docs/plans/cranelift-wasm-backend.md §8 on silent 32-bit miscompiles).
fn lower_addr(cx: &FnCx, addr: ir::Value) -> Result<waffle::Value> {
    let ty = cx.vty(addr);
    ensure!(
        ty == types::I32,
        "address has CLIF type {ty}, expected i32 — was this CLIF built for a 64-bit pointer target?"
    );
    Ok(cx.one(addr)?)
}

fn mem_arg(cx: &FnCx, offset: ir::immediates::Offset32) -> Result<MemoryArg> {
    let off: i32 = offset.into();
    mem_arg_at(cx, off)
}

fn mem_arg_at(cx: &FnCx, off: i32) -> Result<MemoryArg> {
    ensure!(
        off >= 0,
        "negative load/store offset {off} is unsupported (wasm offsets are unsigned)"
    );
    Ok(MemoryArg {
        // Byte-alignment hint: always correct, never a trap; tuning comes later.
        align: 0,
        offset: off as u64,
        memory: cx.m.mem0,
    })
}

fn ensure_shared_memory(cx: &FnCx, operation: &str) -> Result<()> {
    ensure!(
        cx.m.shared_memory,
        "atomic operation {operation} requires translation with shared_memory_max_pages enabled"
    );
    Ok(())
}

fn atomic_mem_arg(cx: &FnCx, ty: types::Type) -> Result<MemoryArg> {
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

/// Resolve a CLIF `FuncRef` to (ordinal, waffle `Func`): `ExternalName::User
/// { namespace: 0, index: k }` where `k` is the callee's ordinal in the input slice,
/// or an `ExternalName::LibCall` routed to a synthesized runtime helper (which has no
/// ordinal — its address cannot be taken).
fn resolve_callee(cx: &FnCx, func_ref: ir::FuncRef) -> Result<(Option<u32>, waffle::Func)> {
    let ext = &cx.clif.dfg.ext_funcs[func_ref];
    let name_ref = match ext.name {
        ir::ExternalName::User(r) => r,
        ir::ExternalName::TestCase(ref name) => {
            let (ordinal, callee) =
                cx.m.testcase_callees
                    .get(&name.to_string())
                    .with_context(|| format!("unresolved fixture function reference `{name}`"))?;
            return Ok((Some(*ordinal), *callee));
        }
        ir::ExternalName::LibCall(lc) => {
            let object_mode = cx.m.object_markers.is_some();
            let kind = match lc {
                ir::LibCall::Memcpy => crate::RuntimeFn::Memcpy,
                // Whole-module mode merges memmove into the overlap-safe
                // memory.copy helper; object mode must keep the real name.
                ir::LibCall::Memmove if object_mode => crate::RuntimeFn::Memmove,
                ir::LibCall::Memmove => crate::RuntimeFn::Memcpy,
                ir::LibCall::Memset => crate::RuntimeFn::Memset,
                ir::LibCall::Memcmp => crate::RuntimeFn::Memcmp,
                other => unsupported!("unimplemented libcall callee {other}"),
            };
            let f =
                cx.m.libcalls
                    .get(&kind)
                    .copied()
                    .with_context(|| format!("libcall {lc} not pre-synthesized"))?;
            return Ok((None, f));
        }
        ref other => {
            unsupported!("unsupported callee name {other:?} (only ExternalName::User/LibCall)")
        }
    };
    let user = cx
        .clif
        .params
        .user_named_funcs()
        .get(name_ref)
        .context("dangling UserExternalNameRef")?;
    ensure!(
        user.namespace == 0,
        "callee namespace {} unsupported (convention: namespace 0, index = ordinal)",
        user.namespace
    );
    let f =
        cx.m.callees
            .get(user.index as usize)
            .copied()
            .with_context(|| {
                format!(
                    "callee index {} out of range ({} functions)",
                    user.index,
                    cx.m.callees.len()
                )
            })?;
    Ok((Some(user.index), f))
}
