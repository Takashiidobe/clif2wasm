use alloc::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
    vec,
    vec::Vec,
};
use core::{default, mem::take, usize};

use anyhow::Context;
// use arena_traits::IndexAlloc;

use crate::{
    cfg::CFGInfo, const_eval, entity::EntityRef, passes::basic_opt::value_is_pure, util::new_sig,
    util::results_ref_2, Block, BlockTarget, ConstVal, Func, FuncCollector, FuncDecl, FunctionBody,
    ImportKind, Module, Operator, SignatureData, Terminator, Type, Value, ValueDef,
};

// use crate::FuncCollector;
#[derive(Clone)]
pub struct InlineCfg {
    pub funcs: BTreeSet<Func>,
}
impl FuncCollector for InlineCfg {
    fn collect_func(&mut self, f: Func) {
        self.funcs.insert(f);
    }
}
// impl FuncCollector for InlineCfg {
//     fn add_func(&mut self, f: Func) {
//         self.funcs.insert(f);
//     }
// }
pub struct Inline {
    blocks: BTreeMap<Block, Block>,
    return_to: Option<Block>,
    inline_funcs: Arc<InlineCfg>,
    stack: BTreeMap<Func, Block>,
}
pub fn inline_mod(m: &mut Module, mut cfg: InlineCfg) -> anyhow::Result<()> {
    crate::td::ix(m, &mut cfg);
    for f in m.funcs.iter().collect::<BTreeSet<_>>() {
        let mut g = take(&mut m.funcs[f]);
        if let FuncDecl::Body(s, _, b) = &mut g {
            b.convert_to_max_ssa(None);
            let s = *s;
            let mut new = FunctionBody::new(&m, s);
            new.entry = match (Inline::new(cfg.clone())).translate(
                m, &mut new, &*b,
                b.entry,
                // b.blocks[b.entry].params.iter().map(|_| None).collect(),
            ) {
                Ok(a) => a,
                Err(e) => {
                    m.funcs[f] = g;
                    return Err(e);
                }
            };
            new.recompute_edges();
            new.optimize(&Default::default());
            *b = new;
        }
        m.funcs[f] = g;
    }
    Ok(())
}
impl Inline {
    pub fn new(a: InlineCfg) -> Self {
        Self {
            blocks: BTreeMap::new(),
            return_to: None,
            inline_funcs: Arc::new(a),
            stack: Default::default(),
        }
    }
    pub fn translate(
        &mut self,
        module: &Module,
        dst: &mut FunctionBody,
        src: &FunctionBody,
        k: Block,
    ) -> anyhow::Result<Block> {
        loop {
            if let Some(l) = self.blocks.get(&k) {
                return Ok(*l);
            }
            let mut new = dst.add_block();
            for a in self.blocks.iter_mut() {
                if a.1.is_invalid() {
                    *a.1 = new
                }
            }
            let mut state = src.blocks[k]
                .params
                .iter()
                .map(|(k, v)| (*v, vec![dst.add_blockparam(new, *k)]))
                .collect::<BTreeMap<_, _>>();
            self.blocks.insert(k, new);
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
                    crate::ValueDef::Operator(operator, list_ref, list_ref1) => match operator {
                        Operator::Call { function_index }
                            if self.inline_funcs.funcs.contains(function_index)
                                && !self.stack.contains_key(function_index)
                                && module.funcs[*function_index].body().is_some() =>
                        {
                            let Some(b) = module.funcs[*function_index].body() else {
                                unreachable!()
                            };
                            let k2 = dst.add_block();
                            let tys = &src.type_pool[*list_ref1];
                            let args = src.arg_pool[*list_ref]
                                .iter()
                                .filter_map(|a| state.get(a))
                                .flatten()
                                .cloned()
                                .collect::<Vec<_>>();
                            let ke = Inline {
                                blocks: Default::default(),
                                return_to: Some(k2),
                                inline_funcs: self.inline_funcs.clone(),
                                stack: match self.stack.clone() {
                                    mut a => {
                                        a.insert(*function_index, Block::invalid());
                                        a
                                    }
                                },
                            }
                            .translate(module, dst, b, b.entry)?;
                            dst.set_terminator(
                                new,
                                crate::Terminator::Br {
                                    target: BlockTarget {
                                        block: ke,
                                        args: args,
                                    },
                                },
                            );
                            new = k2;
                            tys.iter()
                                .cloned()
                                .map(|a| dst.add_blockparam(new, a))
                                .collect()
                        }
                        operator => {
                            let args = src.arg_pool[*list_ref]
                                .iter()
                                .filter_map(|a| state.get(a))
                                .flatten()
                                .cloned()
                                .collect::<Vec<_>>();
                            let tys = &src.type_pool[*list_ref1];
                            let v = dst.add_op(new, operator.clone(), &args, tys);
                            results_ref_2(dst, v)
                        }
                    },
                    crate::ValueDef::PickOutput(value, a, b) => {
                        let value = state
                            .get(value)
                            .cloned()
                            .context("in getting the referenced value")?;
                        let new_value = value[*a as usize];
                        dst.append_to_block(new, new_value);
                        vec![new_value]
                    }
                    crate::ValueDef::Alias(value) => state
                        .get(value)
                        .cloned()
                        .context("in getting the referenced value")?,
                    crate::ValueDef::Placeholder(_) => todo!(),
                    crate::ValueDef::None => vec![],
                };
                state.insert(i, v);
            }
            let mut target_ = |k: &BlockTarget| {
                anyhow::Ok(BlockTarget {
                    args: k
                        .args
                        .iter()
                        .filter_map(|b| state.get(b))
                        .flatten()
                        .cloned()
                        .collect(),
                    block: self.translate(module, dst, src, k.block)?,
                })
            };
            let t = match &src.blocks[k].terminator {
                &crate::Terminator::UB => crate::Terminator::UB,
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
                        cond: cond[0],
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
                        value: value[0],
                        targets,
                        default,
                    }
                }
                crate::Terminator::Return { values } => match self.return_to {
                    None => crate::Terminator::Return {
                        values: values
                            .iter()
                            .filter_map(|b| state.get(b))
                            .flatten()
                            .cloned()
                            .collect(),
                    },
                    Some(k) => crate::Terminator::Br {
                        target: BlockTarget {
                            block: k,
                            args: values
                                .iter()
                                .filter_map(|b| state.get(b))
                                .flatten()
                                .cloned()
                                .collect(),
                        },
                    },
                },
                crate::Terminator::ReturnCall { func, args } => match self.return_to {
                    None => crate::Terminator::ReturnCall {
                        func: *func,
                        args: args
                            .iter()
                            .filter_map(|b| state.get(b))
                            .flatten()
                            .cloned()
                            .collect(),
                    },
                    Some(k) => {
                        if self.inline_funcs.funcs.contains(func)
                            && module.funcs[*func].body().is_some()
                        {
                            match self.stack.get(func) {
                                None => {
                                    let Some(b) = module.funcs[*func].body() else {
                                        unreachable!()
                                    };
                                    // let k2 = dst.add_block();
                                    let tys = match &module.signatures[module.funcs[*func].sig()] {
                                        SignatureData::Func {
                                            params, returns, ..
                                        } => returns,
                                        _ => todo!(),
                                    };
                                    let args = args
                                        .iter()
                                        .filter_map(|a| state.get(a))
                                        .flatten()
                                        .cloned()
                                        .collect::<Vec<_>>();
                                    let ke = Inline {
                                        blocks: Default::default(),
                                        return_to: Some(k),
                                        inline_funcs: self.inline_funcs.clone(),
                                        stack: match self.stack.clone() {
                                            mut a => {
                                                a.insert(*func, Block::invalid());
                                                a
                                            }
                                        },
                                    }
                                    .translate(module, dst, b, b.entry)?;
                                    Terminator::Br {
                                        target: BlockTarget {
                                            block: ke,
                                            args: args,
                                        },
                                    }
                                }
                                Some(k2) => {
                                    let k2 = *k2;
                                    let args = args
                                        .iter()
                                        .filter_map(|a| state.get(a))
                                        .flatten()
                                        .cloned()
                                        .collect::<Vec<_>>();
                                    Terminator::Br {
                                        target: BlockTarget { block: k2, args },
                                    }
                                }
                            }
                        } else {
                            let tys = match &module.signatures[module.funcs[*func].sig()] {
                                SignatureData::Func {
                                    params, returns, ..
                                } => returns,
                                _ => todo!(),
                            };
                            let values = dst.add_op(
                                new,
                                Operator::Call {
                                    function_index: *func,
                                },
                                &args,
                                &tys,
                            );
                            let values = results_ref_2(dst, values);
                            crate::Terminator::Br {
                                target: BlockTarget {
                                    block: k,
                                    args: values
                                        .iter()
                                        .filter_map(|b| state.get(b))
                                        .flatten()
                                        .cloned()
                                        .collect(),
                                },
                            }
                        }
                    }
                },
                crate::Terminator::ReturnCallIndirect { sig, table, args } => {
                    match self.return_to {
                        None => crate::Terminator::ReturnCallIndirect {
                            sig: *sig,
                            table: *table,
                            args: args
                                .iter()
                                .filter_map(|b| state.get(b))
                                .flatten()
                                .cloned()
                                .collect(),
                        },
                        Some(k) => {
                            let tys = match &module.signatures[*sig] {
                                SignatureData::Func {
                                    params, returns, ..
                                } => returns,
                                _ => todo!(),
                            };
                            let values = dst.add_op(
                                new,
                                Operator::CallIndirect {
                                    sig_index: *sig,
                                    table_index: *table,
                                },
                                &args,
                                &tys,
                            );
                            let values = results_ref_2(dst, values);
                            crate::Terminator::Br {
                                target: BlockTarget {
                                    block: k,
                                    args: values
                                        .iter()
                                        .filter_map(|b| state.get(b))
                                        .flatten()
                                        .cloned()
                                        .collect(),
                                },
                            }
                        }
                    }
                }
                crate::Terminator::ReturnCallRef { sig, args } => match self.return_to {
                    None => crate::Terminator::ReturnCallRef {
                        sig: *sig,
                        args: args
                            .iter()
                            .filter_map(|b| state.get(b))
                            .flatten()
                            .cloned()
                            .collect(),
                    },
                    Some(k) => {
                        let tys = match &module.signatures[*sig] {
                            SignatureData::Func {
                                params, returns, ..
                            } => returns,
                            _ => todo!(),
                        };
                        let values =
                            dst.add_op(new, Operator::CallRef { sig_index: *sig }, &args, &tys);
                        let values = results_ref_2(dst, values);
                        crate::Terminator::Br {
                            target: BlockTarget {
                                block: k,
                                args: values
                                    .iter()
                                    .filter_map(|b| state.get(b))
                                    .flatten()
                                    .cloned()
                                    .collect(),
                            },
                        }
                    }
                },
                crate::Terminator::Unreachable => crate::Terminator::Unreachable,
                _ => crate::Terminator::None,
            };
            dst.set_terminator(new, t);
        }
    }
}
