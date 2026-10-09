use crate::{
    entity::EntityRef, ExportKind, Func, FuncDecl, FunctionBody, ImportKind, Memory, Module,
    Operator, Terminator, ValueDef,
};
use alloc::borrow::ToOwned;
use alloc::collections::BTreeMap;
use alloc::vec;
use alloc::vec::Vec;
use core::convert::Infallible;

use crate::op_traits::rewrite_mem;

pub fn reorder_funcs_in_body(b: &mut FunctionBody, f: &BTreeMap<Func, Func>) {
    for v in b.values.values_mut() {
        if let ValueDef::Operator(a, _, _) = v {
            if let Operator::Call { function_index } = a {
                *function_index = *f.get(&*function_index).unwrap();
            }
        }
    }
    for k in b.blocks.values_mut() {
        if let Terminator::ReturnCall { func, args } = &mut k.terminator {
            *func = *f.get(&*func).unwrap();
        }
    }
}
pub fn reorder_funcs(m: &mut Module, fs: &BTreeMap<Func, Func>) {
    let mut n = m.funcs.clone();
    for (f, b) in m.funcs.entries() {
        let mut b = b.clone();
        if let Some(b) = b.body_mut() {
            reorder_funcs_in_body(b, fs);
        }
        n[*fs.get(&f).unwrap()] = b;
    }
    m.funcs = n;
    for t in m.tables.values_mut() {
        if let Some(e) = t.func_elements.as_mut() {
            for e in e.iter_mut() {
                let Some(f) = fs.get(&*e) else {
                    let f = *e;
                    panic!("invalid func: {f}; {}", m.funcs[f].name())
                };
                *e = *f;
            }
        }
    }
    for i in m.imports.iter_mut() {
        if let ImportKind::Func(f) = &mut i.kind {
            *f = *fs.get(&*f).unwrap();
        }
    }
    for i in m.exports.iter_mut() {
        if let ExportKind::Func(f) = &mut i.kind {
            *f = *fs.get(&*f).unwrap();
        }
    }
}
pub fn fixup_orders(m: &mut Module) {
    let mut fs = BTreeMap::new();
    let mut a = vec![];
    let mut b = vec![];
    for (f, d) in m.funcs.entries() {
        if let FuncDecl::Import(_, _) = d {
            a.push(f)
        } else {
            b.push(f)
        }
    }
    let mut i = 0;
    for v in a {
        fs.insert(v, Func::new(i));
        i += 1;
    }
    for v in b {
        fs.insert(v, Func::new(i));
        i += 1;
    }
    assert_eq!(fs.len(), m.funcs.len());
    fs.insert(Func::invalid(), Func::invalid());
    reorder_funcs(m, &fs);
    return;
}
pub fn fixup_mem_orders(m: &mut Module) {
    let mut fs = BTreeMap::new();
    let mut a = vec![];
    let mut b = vec![];
    for (f, d) in m.memories.entries() {
        let mut c = false;
        for i in m.imports.iter() {
            if i.kind == ImportKind::Memory(f) {
                c = true
            }
        }
        if c {
            a.push(f)
        } else {
            b.push(f)
        }
    }
    let mut i = 0;
    for v in a {
        fs.insert(v, Memory::new(i));
        i += 1;
    }
    for v in b {
        fs.insert(v, Memory::new(i));
        i += 1;
    }
    reorder_mems(m, &fs);
}
pub fn reorder_mems(m: &mut Module, fs: &BTreeMap<Memory, Memory>) {
    for f in m.funcs.values_mut() {
        if let Some(b) = f.body_mut() {
            for v in b.values.values_mut() {
                if let ValueDef::Operator(a, _, _) = v {
                    let mut w = [(); 4];
                    rewrite_mem(a, &mut w, |m, _| {
                        *m = fs.get(m).copied().unwrap();
                        Ok::<(), Infallible>(())
                    })
                    .unwrap()
                }
            }
        }
    }
    let mes = m.memories.clone();
    for (f, g) in fs.iter() {
        m.memories[*g] = mes[*f].clone();
    }
}
