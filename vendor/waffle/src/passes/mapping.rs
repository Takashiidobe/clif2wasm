use alloc::{borrow::ToOwned, collections::BTreeMap};
use core::mem;

use crate::{
    copying::fcopy::{obf_mod, DontObf, Obfuscate},
    util::new_sig,
    Block, BlockTarget, Func, FunctionBody, Memory, MemoryArg, Module, Operator, SignatureData,
    Type,
};
use anyhow::Context;

// use crate_ast::{
//     add_op,
//     fcopy::{obf_mod, DontObf, Obfuscate},
//     Builder, Expr,
// };

#[derive(Default, Clone, Copy)]
pub struct Reload<T, F> {
    pub wrapped: T,
    pub predicate: F,
}
impl<T: Obfuscate, F: FnMut(Memory) -> bool> Reload<T, F> {
    fn store(
        &mut self,
        o: usize,
        memory: &MemoryArg,
        f: &mut crate::FunctionBody,
        b: crate::Block,
        args: &[crate::Value],
        types: &[crate::Type],
        module: &mut Module,
    ) -> anyhow::Result<(crate::Value, crate::Block)> {
        let r = f.values[args[0]].ty(&f.type_pool).unwrap();
        let r2 = f.values[args[1]].ty(&f.type_pool).unwrap();
        if o == 1 {
            return self.obf(
                match r2 {
                    Type::I32 => Operator::I32Store8 {
                        memory: memory.clone(),
                    },
                    Type::I64 => Operator::I64Store8 {
                        memory: memory.clone(),
                    },
                    _ => anyhow::bail!("nop!"),
                },
                f,
                b,
                args,
                types,
                module,
            );
        }
        let (a, b) = self.obf(
            match r2 {
                Type::I32 => Operator::I32Const { value: 0xff },
                Type::I64 => Operator::I64Const { value: 0xff },
                _ => anyhow::bail!("nop!"),
            },
            f,
            b,
            &[],
            &[r2],
            module,
        )?;
        let (a, b) = self.obf(
            match r2 {
                Type::I32 => Operator::I32And,
                Type::I64 => Operator::I64And,
                _ => anyhow::bail!("nop!"),
            },
            f,
            b,
            &[args[1], a],
            &[r2],
            module,
        )?;
        let (_, b) = self.obf(
            match r2 {
                Type::I32 => Operator::I32Store8 {
                    memory: memory.clone(),
                },
                Type::I64 => Operator::I64Store8 {
                    memory: memory.clone(),
                },
                _ => anyhow::bail!("nop!"),
            },
            f,
            b,
            &[args[0], a],
            types,
            module,
        )?;
        let (a, b) = self.obf(
            match r2 {
                Type::I32 => Operator::I32Const { value: 8 },
                Type::I64 => Operator::I64Const { value: 8 },
                _ => anyhow::bail!("nop!"),
            },
            f,
            b,
            &[],
            &[r2],
            module,
        )?;
        let (c, b) = self.obf(
            match r2 {
                Type::I32 => Operator::I32ShrU,
                Type::I64 => Operator::I64ShrU,
                _ => anyhow::bail!("nop!"),
            },
            f,
            b,
            &[args[1], a],
            &[r2],
            module,
        )?;
        let (a, b) = self.obf(
            match r {
                Type::I32 => Operator::I32Const { value: 1 },
                Type::I64 => Operator::I64Const { value: 1 },
                _ => anyhow::bail!("nop!"),
            },
            f,
            b,
            &[],
            &[r],
            module,
        )?;
        let (a, b) = self.obf(
            match r {
                Type::I32 => Operator::I32Add,
                Type::I64 => Operator::I64Add,
                _ => anyhow::bail!("nop!"),
            },
            f,
            b,
            &[args[0], a],
            &[r],
            module,
        )?;
        return self.store(o - 1, memory, f, b, &[a, c], types, module);
    }
    fn load(
        &mut self,
        o: usize,
        memory: &MemoryArg,
        f: &mut crate::FunctionBody,
        b: crate::Block,
        args: &[crate::Value],
        types: &[crate::Type],
        module: &mut Module,
    ) -> anyhow::Result<(crate::Value, crate::Block)> {
        let r = f.values[args[0]].ty(&f.type_pool).unwrap();
        if o == 0 {
            return self.obf(
                match types[0] {
                    Type::I32 => Operator::I32Const { value: 0 },
                    Type::I64 => Operator::I64Const { value: 0 },
                    _ => anyhow::bail!("nop!"),
                },
                f,
                b,
                args,
                types,
                module,
            );
        }
        if o == 1 {
            return self.obf(
                match types[0] {
                    Type::I32 => Operator::I32Load8U {
                        memory: memory.clone(),
                    },
                    Type::I64 => Operator::I64Load8U {
                        memory: memory.clone(),
                    },
                    _ => anyhow::bail!("nop!"),
                },
                f,
                b,
                args,
                types,
                module,
            );
        }
        let (first, b) = self.obf(
            match types[0] {
                Type::I32 => Operator::I32Load8U {
                    memory: memory.clone(),
                },
                Type::I64 => Operator::I64Load8U {
                    memory: memory.clone(),
                },
                _ => anyhow::bail!("nop!"),
            },
            f,
            b,
            args,
            types,
            module,
        )?;
        let (n, b) = self.obf(
            match r {
                Type::I32 => Operator::I32Const { value: 1 },
                Type::I64 => Operator::I64Const { value: 1 },
                _ => anyhow::bail!("nop!"),
            },
            f,
            b,
            &[],
            &[r],
            module,
        )?;
        let (n, b) = self.obf(
            match types[0] {
                Type::I32 => Operator::I32Add,
                Type::I64 => Operator::I64Add,
                _ => anyhow::bail!("nop!"),
            },
            f,
            b,
            &[args[0], n],
            &[r],
            module,
        )?;
        let (second, b) = self.load(o - 1, memory, f, b, &[n], types, module)?;
        let (n, b) = self.obf(
            Operator::I32Const { value: 8 },
            f,
            b,
            &[],
            &[Type::I32],
            module,
        )?;
        let (m, b) = self.obf(
            match types[0] {
                Type::I32 => Operator::I32Shl,
                Type::I64 => Operator::I64Shl,
                _ => anyhow::bail!("nop!"),
            },
            f,
            b,
            &[second, n],
            types,
            module,
        )?;
        return self.obf(
            match types[0] {
                Type::I32 => Operator::I32Add,
                Type::I64 => Operator::I64Add,
                _ => anyhow::bail!("nop!"),
            },
            f,
            b,
            &[m, first],
            types,
            module,
        );
    }
}
impl<T: Obfuscate, F: FnMut(Memory) -> bool> Obfuscate for Reload<T, F> {
    fn boot(
        &mut self,
        b: crate::Block,
        f: &mut crate::FunctionBody,
        m: &mut Module,
    ) -> anyhow::Result<crate::Block> {
        return self.wrapped.boot(b, f, m);
    }
    fn obf_term(
        &mut self,
        t: crate::Terminator,
        b: crate::Block,
        f: &mut crate::FunctionBody,
        m: &mut Module,
    ) -> anyhow::Result<()> {
        return self.wrapped.obf_term(t, b, f, m);
    }
    fn sig(
        &mut self,
        a: crate::SignatureData,
        m: &mut Module,
    ) -> anyhow::Result<crate::SignatureData> {
        return self.wrapped.sig(a, m);
    }
    fn obf(
        &mut self,
        o: crate::Operator,
        f: &mut crate::FunctionBody,
        b: crate::Block,
        args: &[crate::Value],
        types: &[crate::Type],
        module: &mut Module,
    ) -> anyhow::Result<(crate::Value, crate::Block)> {
        if let Some(m) = crate::op_traits::memory_arg(&o) {
            if !(self.predicate)(m.memory) {
                return self.wrapped.obf(o, f, b, args, types, module);
            }
        }
        match &o {
            //Signed operations
            Operator::I32Load8S { memory } => {
                let (unsigned, b) = self.obf(
                    Operator::I32Load8U {
                        memory: memory.clone(),
                    },
                    f,
                    b,
                    args,
                    types,
                    module,
                )?;
                let (signed, b) =
                    self.obf(Operator::I32Extend8S, f, b, &[unsigned], types, module)?;
                return Ok((signed, b));
            }
            Operator::I64Load8S { memory } => {
                let (unsigned, b) = self.obf(
                    Operator::I64Load8U {
                        memory: memory.clone(),
                    },
                    f,
                    b,
                    args,
                    types,
                    module,
                )?;
                let (signed, b) =
                    self.obf(Operator::I64Extend8S, f, b, &[unsigned], types, module)?;
                return Ok((signed, b));
            }
            Operator::I32Load16S { memory } => {
                let (unsigned, b) = self.obf(
                    Operator::I32Load16U {
                        memory: memory.clone(),
                    },
                    f,
                    b,
                    args,
                    types,
                    module,
                )?;
                let (signed, b) =
                    self.obf(Operator::I32Extend16S, f, b, &[unsigned], types, module)?;
                return Ok((signed, b));
            }
            Operator::I64Load16S { memory } => {
                let (unsigned, b) = self.obf(
                    Operator::I64Load16U {
                        memory: memory.clone(),
                    },
                    f,
                    b,
                    args,
                    types,
                    module,
                )?;
                let (signed, b) =
                    self.obf(Operator::I64Extend16S, f, b, &[unsigned], types, module)?;
                return Ok((signed, b));
            }
            Operator::I64Load32S { memory } => {
                let (unsigned, b) = self.obf(
                    Operator::I64Load32U {
                        memory: memory.clone(),
                    },
                    f,
                    b,
                    args,
                    types,
                    module,
                )?;
                let (signed, b) =
                    self.obf(Operator::I64Extend32S, f, b, &[unsigned], types, module)?;
                return Ok((signed, b));
            }
            //Unsigned loads
            Operator::I32Load16U { memory } => {
                return self.load(2, memory, f, b, args, types, module);
            }
            Operator::I64Load16U { memory } => {
                return self.load(2, memory, f, b, args, types, module);
            }
            Operator::I32Load { memory } => {
                return self.load(4, memory, f, b, args, types, module);
            }
            Operator::I64Load32U { memory } => {
                return self.load(4, memory, f, b, args, types, module);
            }
            Operator::I64Load { memory } => {
                return self.load(8, memory, f, b, args, types, module);
            }
            //Unsigned stores
            Operator::I32Store16 { memory } => {
                return self.store(2, memory, f, b, args, types, module);
            }
            Operator::I64Store16 { memory } => {
                return self.store(2, memory, f, b, args, types, module);
            }
            Operator::I32Store { memory } => {
                return self.store(4, memory, f, b, args, types, module);
            }
            Operator::I64Store32 { memory } => {
                return self.store(4, memory, f, b, args, types, module);
            }
            Operator::I64Store { memory } => {
                return self.store(8, memory, f, b, args, types, module);
            }
            //Float loads
            Operator::F32Load { memory } => {
                let (a, b) = self.load(4, memory, f, b, args, &[Type::I32], module)?;
                return self.obf(Operator::F32ReinterpretI32, f, b, &[a], types, module);
            }
            Operator::F64Load { memory } => {
                let (a, b) = self.load(8, memory, f, b, args, &[Type::I64], module)?;
                return self.obf(Operator::F64ReinterpretI64, f, b, &[a], types, module);
            }
            //Float stores
            Operator::F32Store { memory } => {
                let (a, b) = self.obf(
                    Operator::I32ReinterpretF32,
                    f,
                    b,
                    args,
                    &[Type::I32],
                    module,
                )?;
                return self.store(4, memory, f, b, &[a], types, module);
            }
            Operator::F64Store { memory } => {
                let (a, b) = self.obf(
                    Operator::I64ReinterpretF64,
                    f,
                    b,
                    args,
                    &[Type::I64],
                    module,
                )?;
                return self.store(8, memory, f, b, &[a], types, module);
            }
            //64 Bit Ops
            Operator::I64Load8U { memory } => {
                let (a, b) = self.obf(
                    Operator::I32Load8U {
                        memory: memory.clone(),
                    },
                    f,
                    b,
                    args,
                    &[Type::I32],
                    module,
                )?;
                return self.obf(Operator::I64ExtendI32U, f, b, &[a], types, module);
            }
            Operator::I64Store8 { memory } => {
                let (a, b) =
                    self.obf(Operator::I32WrapI64, f, b, &[args[1]], &[Type::I32], module)?;
                return self.obf(
                    Operator::I32Store8 {
                        memory: memory.clone(),
                    },
                    f,
                    b,
                    &[args[0], a],
                    types,
                    module,
                );
            }
            //Offset ops
            Operator::I32Load8U { memory } if memory.offset != 0 => {
                let a = f.add_op(
                    b,
                    Operator::I64Const {
                        value: memory.offset,
                    },
                    &[],
                    &[Type::I64],
                );
                let a = if module.memories[memory.memory].memory64 {
                    a
                } else {
                    f.add_op(b, Operator::I32WrapI64, &[a], &[Type::I32])
                };
                let mut memory = memory.clone();
                let mut args = args.to_owned();
                memory.offset = 0;
                args[0] = f.add_op(
                    b,
                    if module.memories[memory.memory].memory64 {
                        Operator::I64Add
                    } else {
                        Operator::I32Add
                    },
                    &[a, args[0]],
                    &[if module.memories[memory.memory].memory64 {
                        Type::I64
                    } else {
                        Type::I32
                    }],
                );
                return self.obf(Operator::I32Load8U { memory }, f, b, &args, types, module);
            }
            Operator::I32Store8 { memory } if memory.offset != 0 => {
                let a = f.add_op(
                    b,
                    Operator::I64Const {
                        value: memory.offset,
                    },
                    &[],
                    &[Type::I64],
                );
                let a = if module.memories[memory.memory].memory64 {
                    a
                } else {
                    f.add_op(b, Operator::I32WrapI64, &[a], &[Type::I32])
                };
                let mut memory = memory.clone();
                let mut args = args.to_owned();
                memory.offset = 0;
                args[0] = f.add_op(
                    b,
                    if module.memories[memory.memory].memory64 {
                        Operator::I64Add
                    } else {
                        Operator::I32Add
                    },
                    &[a, args[0]],
                    &[if module.memories[memory.memory].memory64 {
                        Type::I64
                    } else {
                        Type::I32
                    }],
                );
                return self.obf(Operator::I32Store8 { memory }, f, b, &args, types, module);
            }
            _ => {
                return self.wrapped.obf(o, f, b, args, types, module);
            }
        }
    }
}
pub struct LowerBulkMemory<F> {
    pub predicate: F,
}
impl<F: FnMut(Memory) -> bool> Obfuscate for LowerBulkMemory<F> {
    fn obf(
        &mut self,
        o: Operator,
        f: &mut crate::FunctionBody,
        b: crate::Block,
        args: &[crate::Value],
        types: &[Type],
        mo: &mut Module,
    ) -> anyhow::Result<(crate::Value, crate::Block)> {
        match o {
            Operator::MemoryFill { mem } if (self.predicate)(mem) => {
                let n = f.add_block();
                let dstt = f.values[args[0]].ty(&f.type_pool).unwrap();
                let mut dst = f.add_blockparam(n, dstt);
                let srct = f.values[args[1]].ty(&f.type_pool).unwrap();
                let mut src = f.add_blockparam(n, srct);
                let countt = f.values[args[2]].ty(&f.type_pool).unwrap();
                let mut count = f.add_blockparam(n, countt);
                f.set_terminator(
                    b,
                    crate::Terminator::Br {
                        target: BlockTarget {
                            block: n,
                            args: args.to_owned(),
                        },
                    },
                );
                let b = n;
                // let mut e = Expr::Bind(
                //     Operator::I32Store8 {
                //         memory: MemoryArg {
                //             align: 0,
                //             offset: 0,
                //             memory: mem,
                //         },
                //     },
                //     vec![Expr::Leaf(dst), Expr::Leaf(src)],
                // );
                // let (_, b) = e.build(mo, f, b)?;
                f.add_op(
                    b,
                    Operator::I32Store8 {
                        memory: MemoryArg {
                            align: 0,
                            offset: 0,
                            memory: mem,
                        },
                    },
                    &[dst, src],
                    &[],
                );
                let oc = count;
                for (r, sub) in vec![(&mut dst, false), (&mut count, true)] {
                    let t = f.values[*r].ty(&f.type_pool).unwrap();
                    let s = f.add_op(
                        b,
                        match t {
                            Type::I32 => Operator::I32Const { value: 1 },
                            Type::I64 => Operator::I64Const { value: 1 },
                            _ => anyhow::bail!("wrong type"),
                        },
                        &[],
                        &[t],
                    );
                    // f.append_to_block(b, s);
                    let s = f.add_op(
                        b,
                        match t {
                            Type::I32 => {
                                if sub {
                                    Operator::I32Sub
                                } else {
                                    Operator::I32Add
                                }
                            }
                            Type::I64 => {
                                if sub {
                                    Operator::I64Sub
                                } else {
                                    Operator::I64Add
                                }
                            }
                            _ => anyhow::bail!("wrong type"),
                        },
                        &[*r, s],
                        &[t],
                    );
                    // f.append_to_block(b, s);
                    *r = s;
                }
                let oc = f.add_op(
                    b,
                    match countt {
                        Type::I32 => Operator::I32Eqz,
                        Type::I64 => Operator::I64Eqz,
                        _ => anyhow::bail!("wrong type"),
                    },
                    &[oc],
                    &[countt],
                );
                // f.append_to_block(b, oc);
                let m = f.add_block();
                f.set_terminator(
                    b,
                    crate::Terminator::CondBr {
                        cond: oc,
                        if_true: BlockTarget {
                            block: m,
                            args: vec![],
                        },
                        if_false: BlockTarget {
                            block: n,
                            args: vec![src, dst, count],
                        },
                    },
                );
                // let o = add_op(f, &[], &[], Operator::Nop);
                // f.append_to_block(m, o);
                let o = f.add_op(m, Operator::Nop, &[], &[]);
                return Ok((o, m));
            }
            Operator::MemoryCopy { dst_mem, src_mem }
                if (self.predicate)(dst_mem) || (self.predicate)(src_mem) =>
            {
                let n = f.add_block();
                let dstt = f.values[args[0]].ty(&f.type_pool).unwrap();
                let mut dst = f.add_blockparam(n, dstt);
                let srct = f.values[args[1]].ty(&f.type_pool).unwrap();
                let mut src = f.add_blockparam(n, srct);
                let countt = f.values[args[2]].ty(&f.type_pool).unwrap();
                let mut count = f.add_blockparam(n, countt);
                f.set_terminator(
                    b,
                    crate::Terminator::Br {
                        target: BlockTarget {
                            block: n,
                            args: args.to_owned(),
                        },
                    },
                );
                let b = n;
                let x = f.add_op(
                    b,
                    Operator::I32Load8U {
                        memory: MemoryArg {
                            align: 0,
                            offset: 0,
                            memory: src_mem,
                        },
                    },
                    &[src],
                    &[Type::I32],
                );
                // let mut e = Expr::Bind(
                //   ,
                //     vec![
                //         Expr::Leaf(dst),
                //         Expr::Bind(
                //             Operator::I32Load8U {
                //                 memory: MemoryArg {
                //                     align: 0,
                //                     offset: 0,
                //                     memory: src_mem,
                //                 },
                //             },
                //             vec![Expr::Leaf(src)],
                //         ),
                //     ],
                // );
                // let (_, b) = e.build(mo, f, b)?;
                let oc = count;
                f.add_op(
                    b,
                    Operator::I32Store8 {
                        memory: MemoryArg {
                            align: 0,
                            offset: 0,
                            memory: dst_mem,
                        },
                    },
                    &[dst, x],
                    &[],
                );
                for (r, sub) in vec![(&mut dst, false), (&mut src, false), (&mut count, true)] {
                    let t = f.values[*r].ty(&f.type_pool).unwrap();
                    let s = f.add_op(
                        b,
                        match t {
                            Type::I32 => Operator::I32Const { value: 1 },
                            Type::I64 => Operator::I64Const { value: 1 },
                            _ => anyhow::bail!("wrong type"),
                        },
                        &[],
                        &[t],
                    );
                    // f.append_to_block(b, s);
                    let s = f.add_op(
                        b,
                        match t {
                            Type::I32 => {
                                if sub {
                                    Operator::I32Sub
                                } else {
                                    Operator::I32Add
                                }
                            }
                            Type::I64 => {
                                if sub {
                                    Operator::I64Sub
                                } else {
                                    Operator::I64Add
                                }
                            }
                            _ => anyhow::bail!("wrong type"),
                        },
                        &[*r, s],
                        &[t],
                    );
                    // f.append_to_block(b, s);
                    *r = s;
                }
                let oc = f.add_op(
                    b,
                    match countt {
                        Type::I32 => Operator::I32Eqz,
                        Type::I64 => Operator::I64Eqz,
                        _ => anyhow::bail!("wrong type"),
                    },
                    &[oc],
                    &[countt],
                );
                // f.append_to_block(b, oc);
                let m = f.add_block();
                f.set_terminator(
                    b,
                    crate::Terminator::CondBr {
                        cond: oc,
                        if_true: BlockTarget {
                            block: m,
                            args: vec![],
                        },
                        if_false: BlockTarget {
                            block: n,
                            args: vec![src, dst, count],
                        },
                    },
                );
                let o = f.add_op(m, Operator::Nop, &[], &[]);
                return Ok((o, m));
            }
            _ => {
                let v = f.add_op(b, o, args, types);
                // f.append_to_block(b, v);
                return Ok((v, b));
            }
        }
    }
}
pub fn lower(m: &mut Module, mut f: impl FnMut(Memory) -> bool) -> anyhow::Result<()> {
    obf_mod(m, &mut LowerBulkMemory { predicate: &mut f })?;
    obf_mod(
        m,
        &mut Reload {
            predicate: f,
            wrapped: DontObf {},
        },
    )?;
    return Ok(());
}
pub struct Ream<F> {
    pub resolver: F,
}
impl<F: FnMut(Memory) -> Option<(Func, Func)>> Obfuscate for Ream<F> {
    fn obf(
        &mut self,
        o: Operator,
        f: &mut FunctionBody,
        b: Block,
        args: &[crate::Value],
        types: &[Type],
        module: &mut Module,
    ) -> anyhow::Result<(crate::Value, Block)> {
        let (f2, m) = match o {
            Operator::I32Load8U { memory } => match (self.resolver)(memory.memory) {
                None => {
                    return DontObf {}.obf(o, f, b, args, types, module);
                }
                Some(a) => (a.0, memory.memory),
            },
            Operator::I32Store8 { memory } => match (self.resolver)(memory.memory) {
                None => {
                    return DontObf {}.obf(o, f, b, args, types, module);
                }
                Some(a) => (a.1, memory.memory),
            },
            o => {
                return DontObf {}.obf(o, f, b, args, types, module);
            }
        };
        let idxtype = if module.memories[m].memory64 {
            Type::I64
        } else {
            Type::I32
        };
        let narg0 = f.add_op(
            b,
            if module.memories[m].memory64 {
                Operator::I64Const { value: 0 }
            } else {
                Operator::I32Const { value: 0 }
            },
            &[],
            &[idxtype],
        );
        let narg0 = f.add_op(
            b,
            if module.memories[m].memory64 {
                Operator::I64Sub
            } else {
                Operator::I32Sub
            },
            &[narg0, args[0]],
            &[idxtype],
        );
        let c = f.add_op(
            b,
            if module.memories[m].memory64 {
                Operator::I64GtU
            } else {
                Operator::I32GtU
            },
            &[args[0], narg0],
            &[Type::I32],
        );
        let res = f.add_block();
        let fb = f.add_block();
        let ob = f.add_block();
        f.set_terminator(
            b,
            crate::Terminator::CondBr {
                cond: c,
                if_true: BlockTarget {
                    block: fb,
                    args: vec![],
                },
                if_false: BlockTarget {
                    block: ob,
                    args: vec![],
                },
            },
        );
        let (v, ob) = DontObf {}.obf(o, f, ob, args, types, module)?;
        let v = if types.len() == 0 { c } else { v };
        f.set_terminator(
            ob,
            crate::Terminator::Br {
                target: BlockTarget {
                    block: res,
                    args: vec![v],
                },
            },
        );
        let (v, fb) = DontObf {}.obf(
            Operator::Call { function_index: f2 },
            f,
            fb,
            args,
            types,
            module,
        )?;
        let v = if types.len() == 0 { c } else { v };
        f.set_terminator(
            fb,
            crate::Terminator::Br {
                target: BlockTarget {
                    block: res,
                    args: vec![v],
                },
            },
        );
        Ok((f.add_blockparam(res, Type::I32), res))
    }
}
