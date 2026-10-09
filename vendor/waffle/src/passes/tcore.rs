use alloc::borrow::ToOwned;
use alloc::collections::{BTreeMap, BTreeSet};
use alloc::vec;
use alloc::vec::Vec;
use core::mem::take;

use anyhow::{Context, Ok};
// use fcopy::obf_mod;
// use waffle_ast::{
//     bulk_memory_lowering::{Reload, Warp},
//     fcopy::obf_mod,
// };
// use goatf2::JustNormalCFF;
// use crate::more::Flix;
use crate::{
    copying::{kts::Kts, module::tree_shake},
    entity::{EntityRef, PerEntity},
    passes, BlockTarget, ExportKind, Func, FuncDecl, FunctionBody, Import, ImportKind, Module,
    Operator, Signature, Table, Terminator, Type, ValueDef,
};
use crate::{SignatureData, Value};

// use crate::fcopy::DontObf;
// pub use waffle_ast::fcopy;
// use waffle_ast::fcopy::DontObf;
// pub mod fcopy;
// pub mod unswitch;
pub use crate::util::results_ref_2;
// pub fn tcore_bytes(a: &[u8], do_fuse: bool) -> anyhow::Result<Vec<u8>> {
//     let mut m = Module::from_wasm_bytes(a, &Default::default())?;
//     m.expand_all_funcs()?;
//     tcore(&mut m, do_fuse)?;
//     return Ok(m.to_wasm_bytes()?);
// }
pub fn un_tcore(m: &mut Module) -> anyhow::Result<()> {
    let mut b = BTreeMap::new();
    for (f, d) in m.funcs.entries() {
        if let Some(d) = d.body() {
            let d = d.clone();
            b.insert(f, d);
        }
    }
    let c = b.clone();
    for (k, v) in b.iter_mut() {
        untcore_pass(m, *k, v)?;
    }
    for (k, v) in b {
        *m.funcs[k].body_mut().unwrap() = v;
    }
    return Ok(());
}
pub fn tcore(m: &mut Module, do_fuse: bool) -> anyhow::Result<()> {
    // let mut m = Module::from_wasm_bytes(a, &Default::default())?;
    m.expand_all_funcs()?;
    let mut b = BTreeMap::new();
    for (f, d) in m.funcs.entries() {
        if let Some(d) = d.body() {
            let d = d.clone();
            b.insert(f, d);
        }
    }
    let c = b.clone();
    for (k, v) in b.iter_mut() {
        tcore_tco_pass(m, *k, v)?;
    }
    if do_fuse {
        let c = b.clone();
        for (k, v) in b.iter_mut() {
            tcore_pass(&c, *k, v)?;
        }
    }
    for (k, v) in b {
        *m.funcs[k].body_mut().unwrap() = v;
    }
    return Ok(());
}
pub fn tcore2(m: &mut Module, mut filter: impl FnMut(Func) -> bool) -> anyhow::Result<()> {
    // let mut m = Module::from_wasm_bytes(a, &Default::default())?;
    m.expand_all_funcs()?;
    let mut b = BTreeMap::new();
    for (f, d) in m.funcs.entries() {
        if !filter(f) {
            continue;
        }
        if let Some(d) = d.body() {
            let d = d.clone();
            b.insert(f, d);
        }
    }
    // let c = b.clone();
    for (k, v) in b.iter_mut() {
        tcore_tco_pass(m, *k, v)?;
    }
    // if do_fuse {
    //     let c = b.clone();
    //     for (k, v) in b.iter_mut() {
    //         tcore_pass(&c, *k, v)?;
    //     }
    // }
    for (k, v) in b {
        *m.funcs[k].body_mut().unwrap() = v;
    }
    return Ok(());
}
pub type TCache = BTreeMap<(Table, SignatureData), Func>;
pub fn trampoline_module(m: &mut Module, seal: bool) -> anyhow::Result<()> {
    let mut b = BTreeMap::new();
    for (f, d) in m.funcs.entries() {
        if let Some(d) = d.body() {
            let d = d.clone();
            b.insert(f, d);
        }
    }
    // let mut all
    // let c = b.clone();
    let mut c = TCache::new();
    for (k, v) in b.iter_mut() {
        gen_trampolines(v, m, &mut c, seal)?;
    }
    for (k, v) in b {
        *m.funcs[k].body_mut().unwrap() = v;
    }
    return Ok(());
}
// pub fn slice_module(m: &mut Module) -> anyhow::Result<()> {
//     trampoline_module(m, true)?;
//     obf_mod(
//         m,
//         &mut Reload {
//             wrapped: Warp {
//                 all: Default::default(),
//             },
//         },
//     )?;
//     for mut i in take(&mut m.imports) {
//         if i.module == "$$eal/mem_base" {
//             if let Some(ExportKind::Memory(memory)) = m.exports.iter().find_map(|x| {
//                 if x.name == i.name {
//                     Some(x.kind.clone())
//                 } else {
//                     None
//                 }
//             }) {
//                 let mut total = vec![];
//                 for n in &m.memories[memory].segments {
//                     total.resize(n.offset + n.data.len(), 0u8);
//                     total[n.offset..][..n.data.len()].copy_from_slice(&n.data);
//                 }
//                 if let ImportKind::Func(f) = i.kind {
//                     let s = m.funcs[f].sig();
//                     // let o = replace(f, p);
//                     let mut b = FunctionBody::new(&m, s);
//                     let mut k = b.entry;
//                     let (o, y) = match &b.rets[0] {
//                         Type::I32 => (
//                             Operator::I32Const {
//                                 value: total.len() as u32,
//                             },
//                             Type::I32,
//                         ),
//                         Type::I64 => (
//                             Operator::I64Const {
//                                 value: total.len() as u64,
//                             },
//                             Type::I64,
//                         ),
//                         _ => anyhow::bail!("invalid type"),
//                     };
//                     let v = b.add_op(k, o, &[], &[y]);
//                     b.set_terminator(k, Terminator::Return { values: vec![v] });
//                     m.funcs[f] = FuncDecl::Body(s, format!("_seal"), b);
//                     continue;
//                 }
//             }
//         }
//         m.imports.push(i);
//     }
//     for (mem, data) in m.memories.entries_mut() {
//         data.segments = vec![];
//         m.imports.push(Import {
//             module: format!("shim"),
//             name: format!("{mem}"),
//             kind: waffle::ImportKind::Memory(mem),
//         });
//     }
//     tree_shake(m)?;
//     return Ok(());
// }
pub fn trampoline_bytes(a: &[u8], seal: bool) -> anyhow::Result<Vec<u8>> {
    let mut m = Module::from_wasm_bytes(a, &Default::default())?;
    m.expand_all_funcs()?;
    trampoline_module(&mut m, seal)?;
    return Ok(m.to_wasm_bytes()?);
}
pub fn gen_trampoline(
    m: &mut Module,
    sig: Signature,
    table_index: Table,
    c: &mut TCache,
    seal: bool,
) -> anyhow::Result<Func> {
    let mut n = m.signatures[sig].clone();
    let cache_key = (table_index, n.clone());
    if let Some(d) = c.get(&cache_key) {
        return Ok(*d);
    }
    {
        let SignatureData::Func {
            params, returns, ..
        } = &mut n
        else {
            anyhow::bail!("invalid signature")
        };
        params.push(Type::I32);
    }
    let nd = m.signatures.push(n.clone());
    let mut b = FunctionBody::new(&m, nd);
    // let sw = b.add_blockparam(b.entry, Type::I32);
    let mut args = b.blocks[b.entry]
        .params
        .iter()
        .map(|(a, b)| *b)
        .collect::<Vec<_>>();
    // for p in n.params.iter() {
    //     args.push(b.add_blockparam(b.entry, *p));
    // }
    let idx = args.len() - 1;
    let sw = args[idx];
    let mut targets = vec![];
    let nb = b.add_block();
    b.set_terminator(nb, Terminator::Unreachable);
    for e in m.tables[table_index]
        .func_elements
        .clone()
        .context("no funcs for a called table")?
    {
        if e.is_valid() && m.funcs.get(e).map(|f| f.sig()) == Some(sig) {
            let t = b.add_block();
            // eprintln!("valid: {e}");
            // let vs = b.arg_pool.from_iter(args[..idx].iter().map(|a| *a));
            // let ts = b.type_pool.from_iter(n.clone().returns.iter().map(|a| *a));
            // let v = b.add_value(ValueDef::Operator(
            //     Operator::Call { function_index: e },
            //     vs,
            //     ts,
            // ));
            // b.append_to_block(t, v);
            // let r = more_crate::results_ref(m, &mut b, v).context("supposed to ba a call")?;
            b.set_terminator(
                t,
                Terminator::ReturnCall {
                    func: e,
                    args: args[..idx].iter().map(|a| *a).collect(),
                },
            );
            targets.push(BlockTarget {
                block: t,
                args: vec![],
            })
        } else {
            targets.push(BlockTarget {
                block: nb,
                args: vec![],
            })
        }
    }
    let cb = b.add_block();
    if seal {
        b.set_terminator(cb, Terminator::Unreachable);
    } else {
        b.set_terminator(
            cb,
            Terminator::ReturnCallIndirect {
                sig: sig,
                table: table_index,
                args: args,
            },
        );
    }
    b.set_terminator(
        b.entry,
        Terminator::Select {
            value: sw,
            targets: targets,
            default: BlockTarget {
                block: cb,
                args: vec![],
            },
        },
    );
    // b.value_locals = PerEntity::default();
    let n = m.funcs.push(FuncDecl::Body(nd, format!("$"), b));
    c.insert(cache_key, n);
    return Ok(n);
}
pub fn gen_trampolines(
    b: &mut FunctionBody,
    m: &mut Module,
    t: &mut TCache,
    seal: bool,
) -> anyhow::Result<()> {
    // b.value_locals = PerEntity::default();
    for (_, v) in b.values.entries_mut() {
        if let ValueDef::Operator(o, _1, _2) = v {
            if let Operator::CallIndirect {
                sig_index,
                table_index,
            } = o.clone()
            {
                *o = Operator::Call {
                    function_index: gen_trampoline(m, sig_index, table_index, t, seal)?,
                }
            }
        }
    }
    for (_, k) in b.blocks.entries_mut() {
        if let Terminator::ReturnCallIndirect { sig, table, args } = k.terminator.clone() {
            k.terminator = Terminator::ReturnCall {
                func: gen_trampoline(m, sig, table, t, seal)?,
                args: args,
            }
        }
    }
    return Ok(());
}
pub fn tcore_tco_pass(
    // mo: &BTreeMap<Func, FunctionBody>,
    mo2: &mut Module,
    f: Func,
    b: &mut FunctionBody,
) -> anyhow::Result<()> {
    passes::resolve_aliases::run(b);
    let mut m = BTreeMap::new();
    m.insert(f, b.entry);
    loop {
        let mut e = b.blocks.entries();
        let (block, fun, args) = 'gather: loop {
            let Some((bl, d)) = e.next() else {
                drop(e);
                // if cff{
                // goatf2::cff(b,&mut JustNormalCFF{});
                // }
                return Ok(());
            };
            // let mut d = d.clone();
            let Terminator::ReturnCall { func, args } = d.terminator.clone() else {
                continue 'gather;
            };
            let Some(_) = mo2.funcs[func].body() else {
                continue 'gather;
            };
            break 'gather (bl, func, args);
        };
        drop(e);
        let k = match m.get(&fun) {
            Some(b) => *b,
            None => {
                // eprintln!("fun_name={};func={}",mo.funcs[fun].name(),mo.funcs[fun].body().unwrap().display("", Some(mo)));
                // b.convert_to_max_ssa(None);
                let mut v = mo2.funcs[fun].body_mut().unwrap();
                v.convert_to_max_ssa(None);
                let e = Kts {
                    blocks: Default::default(),
                }
                .translate(b, &v, v.entry)?;
                m.insert(fun, e);
                e
            }
        };
        b.blocks[block].terminator = Terminator::None;
        b.set_terminator(
            block,
            Terminator::Br {
                target: BlockTarget { block: k, args },
            },
        );
        b.recompute_edges();
    }
}
pub fn untcore_pass(
    m: &mut Module,
    f: Func,
    b: &mut FunctionBody,
    // cff: bool,
) -> anyhow::Result<()> {
    passes::resolve_aliases::run(b);
    loop {
        let mut e = b.blocks.entries();
        let (block, fun, args) = 'gather: loop {
            let Some((bl, d)) = e.next() else {
                drop(e);
                // if cff{
                // goatf2::cff(b,&mut JustNormalCFF{});
                // }
                return Ok(());
            };
            // let mut d = d.clone();
            let (Terminator::ReturnCall { func: _, args }
            | Terminator::ReturnCallIndirect {
                sig: _,
                table: _,
                args,
            }) = d.terminator.clone()
            else {
                continue 'gather;
            };
            break 'gather (bl, d.terminator.clone(), args);
        };
        drop(e);
        let c = match fun {
            Terminator::ReturnCall { func, args } => Operator::Call {
                function_index: func,
            },
            Terminator::ReturnCallIndirect { sig, table, args } => Operator::CallIndirect {
                sig_index: sig,
                table_index: table,
            },
            _ => anyhow::bail!("invalid fun"),
        };
        let vs = b.arg_pool.from_iter(args.iter().map(|a| *a));
        let ts = b.type_pool.from_iter(b.rets.iter().map(|a| *a));
        let c = b.values.push(ValueDef::Operator(c, vs, ts));
        b.append_to_block(block, c);
        let c = results_ref_2(b, c);
        b.blocks[block].terminator = Terminator::None;
        b.set_terminator(block, Terminator::Return { values: c });
        b.recompute_edges();
    }
}
pub fn tcore_pass(
    mo: &BTreeMap<Func, FunctionBody>,
    f: Func,
    b: &mut FunctionBody,
    // cff: bool,
) -> anyhow::Result<()> {
    passes::resolve_aliases::run(b);
    let mut m = BTreeMap::new();
    m.insert(f, b.entry);
    loop {
        let mut e = b.blocks.entries();
        let (block, fun, args) = 'gather: loop {
            let Some((bl, d)) = e.next() else {
                drop(e);
                // if cff {
                //     // goatf2::cff(b, &mut JustNormalCFF {});
                // }
                return Ok(());
            };
            let mut d = d.clone();
            let Terminator::Return { mut values } = d.terminator.clone() else {
                continue 'gather;
            };
            if values.len() == 0 {
                let Some(v) = d.insts.last() else {
                    continue 'gather;
                };
                let df = b.values[v.value].clone();
                let ValueDef::Operator(o, vs, t) = df else {
                    continue 'gather;
                };
                let (Operator::Call { .. } | Operator::CallIndirect { .. }) = o else {
                    continue 'gather;
                };
                b.values[v.value] = ValueDef::None;
                // let Some(_) = mo.get(&function_index) else {
                //     continue 'gather;
                // };
                break 'gather (bl, o, b.arg_pool[vs].to_owned());
            };
            let mut o = None;
            let mut taint = BTreeSet::new();
            for (j, v) in values.into_iter().enumerate() {
                taint.insert(v);
                let mut w = b.values[v].clone();
                loop {
                    match w {
                        ValueDef::BlockParam(_, _, _) => continue 'gather,
                        ValueDef::Operator(_, _, _) => o = Some(v),
                        ValueDef::PickOutput(w, i, _) => {
                            if i as usize == j {
                                taint.insert(w);
                                match o.take() {
                                    Some(x) => {
                                        if x == w {
                                            o = Some(w)
                                        } else {
                                            continue 'gather;
                                        }
                                    }
                                    None => o = Some(w),
                                }
                            } else {
                                continue 'gather;
                            }
                        }
                        ValueDef::Alias(l) => {
                            taint.insert(l);
                            w = b.values[l].clone();
                            continue;
                        }
                        ValueDef::Placeholder(_) => todo!(),
                        // ValueDef::Trace(_, _) => todo!(),
                        ValueDef::None => continue 'gather,
                    }
                    break;
                }
            }
            let o = o.unwrap();
            let df = b.values[o].clone();
            let ValueDef::Operator(o, vs, t) = df else {
                continue 'gather;
            };
            let (Operator::Call { .. } | Operator::CallIndirect { .. }) = o else {
                continue 'gather;
            };
            // let Some(_) = mo.get(&function_index) else {
            //     continue 'gather;
            // };
            let t2 = taint.clone();
            while !taint.is_empty() {
                let Some(l) = d.insts.last() else {
                    continue 'gather;
                };
                if let ValueDef::None = b.values[l.value] {
                    d.insts.pop();
                    continue;
                }
                if taint.contains(&l.value) {
                    taint.remove(&l.value);
                    d.insts.pop();
                    continue;
                }
                continue 'gather;
            }
            for t in t2 {
                b.values[t] = ValueDef::None;
            }
            break 'gather (bl, o, b.arg_pool[vs].to_owned());
        };
        drop(e);
        b.blocks[block].terminator = Terminator::None;
        b.set_terminator(
            block,
            match fun {
                Operator::Call { function_index } => Terminator::ReturnCall {
                    func: function_index,
                    args: args,
                },
                Operator::CallIndirect {
                    sig_index,
                    table_index,
                } => Terminator::ReturnCallIndirect {
                    sig: sig_index,
                    table: table_index,
                    args: args,
                },
                _ => anyhow::bail!("invalid fun"),
            },
        );
        b.recompute_edges();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
}
