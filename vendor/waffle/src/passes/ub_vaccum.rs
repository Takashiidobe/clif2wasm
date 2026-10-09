use core::mem::take;

use alloc::collections::btree_set::BTreeSet;

use crate::{FunctionBody, Module, Terminator};

use super::inline::{inline_mod, InlineCfg};

pub fn vaccum(f: &mut FunctionBody) {
    let mut work = true;
    while work {
        work = false;
        for k in f.blocks.iter().collect::<BTreeSet<_>>() {
            let mut t = take(&mut f.blocks[k].terminator);
            if let Terminator::Br { target } = &t {
                if let Terminator::UB = f.blocks[target.block].terminator {
                    t = Terminator::UB;
                    work = true;
                }
            }
            if let Terminator::CondBr {
                cond,
                if_true,
                if_false,
            } = &t
            {
                if let Terminator::UB = f.blocks[if_true.block].terminator {
                    t = Terminator::Br {
                        target: if_false.clone(),
                    };
                    f.set_terminator(k, t);
                    work = true;
                    continue;
                }
                if let Terminator::UB = f.blocks[if_false.block].terminator {
                    t = Terminator::Br {
                        target: if_true.clone(),
                    };
                    f.set_terminator(k, t);
                    work = true;
                    continue;
                }
            }
            f.set_terminator(k, t);
        }
    }
}
pub fn gvc(m: &mut Module) -> anyhow::Result<()> {
    let mut work = true;
    let mut save = BTreeSet::new();
    while work {
        work = false;
        for f in m.funcs.iter().collect::<BTreeSet<_>>() {
            let mut b = take(&mut m.funcs[f]);
            'a: {
                if let Some(b) = b.body_mut() {
                    if let Terminator::UB = b.blocks[b.entry].terminator {
                        break 'a;
                    }
                    vaccum(b);
                    b.optimize(&Default::default());
                    if let Terminator::UB = b.blocks[b.entry].terminator {
                        save.insert(f);
                        // if !save.insert(f){
                        work = true
                        // }
                    }
                }
            }
            m.funcs[f] = b;
        }
        inline_mod(
            m,
            InlineCfg {
                funcs: save.clone(),
            },
        )?;
    }
    Ok(())
}
