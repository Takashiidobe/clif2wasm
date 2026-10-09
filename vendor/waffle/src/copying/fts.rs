use alloc::collections::{BTreeMap, BTreeSet};
use core::{default, iter::once};

use anyhow::Context;
use arena_traits::IndexAlloc;
// use rayon::iter::{once, ParallelIterator};

use crate::{
    cfg::CFGInfo, passes::basic_opt::value_is_pure, util::new_sig, Block, BlockTarget, Func,
    FuncDecl, FunctionBody, Module, Operator, SignatureData, ValueDef,
};
use alloc::string::ToString;
use alloc::vec;
use alloc::vec::Vec;
#[derive(Default)]
pub struct Fts {
    pub blocks: BTreeMap<Block, Func>,
}
impl Fts {
    pub fn fueled_translate(
        &mut self,
        f: &mut BTreeMap<Block, Block>,
        module: &mut Module,
        dst: &mut FunctionBody,
        src: &FunctionBody,
        k: Block,
        stack: &BTreeSet<Block>,
    ) -> anyhow::Result<Block> {
        loop {
            if let Some(k) = f.get(&k) {
                return Ok(*k);
            }
            if stack.contains(&k) {
                let f = self.translate(module, src, k)?;
                let shim = dst.add_block();
                let args = src.blocks[k]
                    .params
                    .iter()
                    .map(|(a, b)| dst.add_blockparam(shim, *a))
                    .collect::<Vec<_>>();
                dst.set_terminator(
                    shim,
                    crate::Terminator::ReturnCall {
                        func: f,
                        args: args,
                    },
                );
                return Ok(shim);
            };
            let mut stack = stack.clone();
            stack.insert(k);
            let new = dst.add_block();
            let mut state = src.blocks[k]
                .params
                .iter()
                .map(|(k, v)| (*v, dst.add_blockparam(new, *k)))
                .collect::<BTreeMap<_, _>>();
            f.insert(k, new);
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
                anyhow::Ok(BlockTarget {
                    args: k
                        .args
                        .iter()
                        .filter_map(|b| state.get(b))
                        .cloned()
                        .collect(),
                    block: self.fueled_translate(f, module, dst, src, k.block, &stack)?,
                })
            };
            let t = match &src.blocks[k].terminator {
                crate::Terminator::UB => crate::Terminator::UB,
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
            };
            dst.set_terminator(new, t);
        }
    }
    pub fn translate(
        &mut self,
        module: &mut Module,
        src: &FunctionBody,
        k: Block,
    ) -> anyhow::Result<Func> {
        // return stacker::maybe_grow(32 * 1024, 1024 * 1024, move || loop {
        loop {
            if let Some(l) = self.blocks.get(&k) {
                return Ok(*l);
            }
            let s = new_sig(
                module,
                SignatureData::Func {
                    params: src.blocks[k].params.iter().map(|a| a.0).collect(),
                    returns: src.rets.clone(),
                    shared: src.shared,
                },
            );
            let new_f = module.funcs.alloc(FuncDecl::None);
            let mut dst = FunctionBody::new(module, s);
            let new = dst.entry;
            let mut state = src.blocks[k]
                .params
                .iter()
                .zip(dst.blocks[new].params.iter())
                .map(|((k, v), (dk, dv))| (*v, *dv))
                .collect::<BTreeMap<_, _>>();
            self.blocks.insert(k, new_f);
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
            let mut f = BTreeMap::new();
            let mut target_ = |k2: &BlockTarget| {
                Ok(BlockTarget {
                    block: self.fueled_translate(
                        &mut f,
                        module,
                        &mut dst,
                        src,
                        k2.block,
                        &once(k).collect(),
                    )?,
                    args: k2
                        .args
                        .iter()
                        .filter_map(|b| state.get(b))
                        .cloned()
                        .collect(),
                })
            };
            let t = match &src.blocks[k].terminator {
                crate::Terminator::UB => crate::Terminator::UB,
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
            };
            dst.set_terminator(new, t);
            module.funcs[new_f] = FuncDecl::Body(s, k.to_string(), dst);
        }
    }
}
pub fn run_once(f: &mut FunctionBody, module: &mut Module) -> anyhow::Result<()> {
    f.convert_to_max_ssa(None);
    let k = Fts {
        blocks: Default::default(),
        // fuel,
    }
    .translate(module, &f, f.entry)?;
    let e2 = f.add_block();
    let params = f.blocks[f.entry]
        .params
        .iter()
        .map(|a| a.0)
        .collect::<Vec<_>>();
    let params = params
        .into_iter()
        .map(|x| f.add_blockparam(e2, x))
        .collect::<Vec<_>>();
    f.entry = e2;
    f.set_terminator(
        e2,
        crate::Terminator::ReturnCall {
            func: k,
            args: params,
        },
    );
    return Ok(());
}
pub fn go(module: &mut Module) -> anyhow::Result<()> {
    return module.try_take_per_func_body(|module, f| run_once(f, module));
}
// pub fn go(module: &mut Module) -> anyhow::Result<()> {
//     return go2(module, 0);
// }
