use alloc::collections::BTreeMap;
use core::default;

use alloc::borrow::ToOwned;
use alloc::vec;
use alloc::vec::Vec;
use anyhow::Context;
use arena_traits::IndexAlloc;

use crate::{
    cfg::CFGInfo, passes::basic_opt::value_is_pure, Block, BlockTarget, Func, FunctionBody,
    HeapType, Operator, Type, ValueDef, WithNullable,
};
#[derive(Default)]
pub struct Frint {
    pub blocks: BTreeMap<(Block, Vec<Option<Func>>), Block>,
}
impl Frint {
    pub fn translate_base(
        &mut self,
        dst: &mut FunctionBody,
        src: &FunctionBody,
        k: Block,
    ) -> anyhow::Result<Block> {
        let params = src.blocks[k]
            .params
            .iter()
            .filter_map(|a| match &a.0 {
                Type::Heap(WithNullable {
                    value: HeapType::FuncRef | HeapType::Sig { .. },
                    ..
                }) => Some(None),
                _ => None,
            })
            .collect();
        return self.translate(dst, src, k, params);
    }
    pub fn translate(
        &mut self,
        dst: &mut FunctionBody,
        src: &FunctionBody,
        k: Block,
        params: Vec<Option<Func>>,
    ) -> anyhow::Result<Block> {
        loop {
            if let Some(l) = self.blocks.get(&(k, params.clone())) {
                return Ok(*l);
            }
            let new = dst.add_block();
            let mut p = params.iter();
            let mut state = src.blocks[k]
                .params
                .iter()
                .filter_map(|(k, v)| match k {
                    Type::Heap(WithNullable {
                        value: HeapType::FuncRef | HeapType::Sig { .. },
                        ..
                    }) => match p.next()? {
                        Some(f) => Some((
                            *v,
                            dst.add_op(
                                new,
                                Operator::RefFunc { func_index: *f },
                                &[],
                                &[k.clone()],
                            ),
                        )),
                        None => Some((*v, dst.add_blockparam(new, *k))),
                    },
                    _ => Some((*v, dst.add_blockparam(new, *k))),
                })
                .collect::<BTreeMap<_, _>>();
            self.blocks.insert((k, params.clone()), new);
            'a: for i in src.blocks[k].insts.iter().cloned() {
                let i = i.value;
                if value_is_pure(i, src) {
                    let mut unused = true;
                    for j in src.blocks[k].insts.iter().cloned() {
                        src.values[j.value].visit_uses(&src.arg_pool, |u| {
                            if u == i {
                                unused = false;
                            }
                        });
                    }
                    src.blocks[k].terminator.visit_uses(|u| {
                        if u == i {
                            unused = false;
                        }
                    });
                    if unused {
                        continue 'a;
                    }
                }
                let v = match &src.values[i] {
                    crate::ValueDef::BlockParam(block, _, _) => todo!(),
                    crate::ValueDef::Operator(operator, list_ref, list_ref1) => {
                        let args = src.arg_pool[*list_ref]
                            .iter()
                            .filter_map(|a| state.get(a))
                            .cloned()
                            .collect::<Vec<_>>();
                        let tys = &src.type_pool[*list_ref1];
                        dst.add_op(new, operator.clone(), &args, tys)
                    }
                    crate::ValueDef::PickOutput(value, a, b) => {
                        let value = state
                            .get(value)
                            .cloned()
                            .context("in getting the referenced value")?;
                        let new_value = dst.values.alloc(ValueDef::PickOutput(value, *a, *b));
                        dst.append_to_block(new, new_value);
                        new_value
                    }
                    crate::ValueDef::Alias(value) => state
                        .get(value)
                        .cloned()
                        .context("in getting the referenced value")?,
                    crate::ValueDef::Placeholder(_) => todo!(),
                    crate::ValueDef::None => dst.add_op(new, Operator::Nop, &[], &[]),
                };
                state.insert(i, v);
            }
            let mut target_ = |k: &BlockTarget| {
                let mut funcs = vec![];
                let args = k
                    .args
                    .iter()
                    .filter_map(|b| state.get(b))
                    .filter_map(|b| {
                        if let Some(Type::Heap(WithNullable {
                            value: HeapType::FuncRef | HeapType::Sig { .. },
                            ..
                        })) = dst.values[*b].ty(&dst.type_pool)
                        {
                            match &dst.values[*b] {
                                ValueDef::Operator(Operator::RefFunc { func_index }, _, _) => {
                                    funcs.push(Some(*func_index));
                                    return None;
                                }
                                _ => {
                                    funcs.push(None);
                                    return Some(b);
                                }
                            }
                        }
                        return Some(b);
                    })
                    .cloned()
                    .collect();
                anyhow::Ok(BlockTarget {
                    args: args,
                    block: self.translate(dst, src, k.block, funcs)?,
                })
            };
            let t = match &src.blocks[k].terminator {
                crate::Terminator::Br { target } => crate::Terminator::Br {
                    target: target_(target)?,
                },
                crate::Terminator::CondBr {
                    cond,
                    if_true,
                    if_false,
                } => {
                    let if_true = target_(if_true)?;
                    let if_false = target_(if_false)?;
                    let cond = state
                        .get(cond)
                        .cloned()
                        .context("in getting the referenced value")?;
                    crate::Terminator::CondBr {
                        cond,
                        if_true,
                        if_false,
                    }
                }
                crate::Terminator::Select {
                    value,
                    targets,
                    default,
                } => {
                    let value = state
                        .get(value)
                        .cloned()
                        .context("in getting the referenced value")?;
                    let default = target_(default)?;
                    let targets = targets
                        .iter()
                        .map(target_)
                        .collect::<anyhow::Result<Vec<_>>>()?;
                    crate::Terminator::Select {
                        value,
                        targets,
                        default,
                    }
                }
                crate::Terminator::Return { values } => crate::Terminator::Return {
                    values: values
                        .iter()
                        .filter_map(|b| state.get(b))
                        .cloned()
                        .collect(),
                },
                crate::Terminator::ReturnCall { func, args } => crate::Terminator::ReturnCall {
                    func: *func,
                    args: args.iter().filter_map(|b| state.get(b)).cloned().collect(),
                },
                crate::Terminator::ReturnCallIndirect { sig, table, args } => {
                    crate::Terminator::ReturnCallIndirect {
                        sig: *sig,
                        table: *table,
                        args: args.iter().filter_map(|b| state.get(b)).cloned().collect(),
                    }
                }
                crate::Terminator::ReturnCallRef { sig, args } => {
                    crate::Terminator::ReturnCallRef {
                        sig: *sig,
                        args: args.iter().filter_map(|b| state.get(b)).cloned().collect(),
                    }
                }
                crate::Terminator::Unreachable => crate::Terminator::Unreachable,
                crate::Terminator::None => crate::Terminator::None,
                &crate::Terminator::UB => crate::Terminator::UB,
            };
            dst.set_terminator(new, t);
        }
    }
}
