use crate::util::{add_start, new_sig};
use crate::{
    Block, ExportKind, Func, FuncDecl, FunctionBody, Import, ImportKind, Memory, MemoryArg,
    MemoryData, Module, Operator, Signature, SignatureData, Table, Type, Value, ValueDef,
};
use alloc::borrow::ToOwned;
use alloc::collections::BTreeMap;
use alloc::vec;
use alloc::vec::Vec;
use core::iter::empty;

// use super::reload::{ImportedCfg, ImportedMemoriesToFunc};

pub fn fuse_iter(m: &mut Module, x: impl Iterator<Item = (usize, u8)>, mem: Memory) {
    let null = new_sig(
        m,
        SignatureData::Func {
            params: vec![],
            returns: vec![],
            shared: true,
        },
    );
    let mut b = FunctionBody::new(m, null);
    let vz = b.arg_pool.from_iter(empty());
    let tz = b.type_pool.from_iter(empty());
    let ti = b.type_pool.from_iter(vec![Type::I32].into_iter());
    let ia = b.add_value(ValueDef::Operator(Operator::I32Const { value: 0 }, vz, ti));
    b.append_to_block(b.entry, ia);
    for (a, c) in x {
        // let ia = b.add_value(ValueDef::Operator(Operator::I32Const { value: a as u32 }, vz, ti));
        // b.append_to_block(b.entry, ia);
        let ic = b.add_value(ValueDef::Operator(
            Operator::I32Const { value: c as u32 },
            vz,
            ti,
        ));
        b.append_to_block(b.entry, ic);
        let ia = b.add_value(ValueDef::Operator(
            Operator::I32Const { value: a as u32 },
            vz,
            ti,
        ));
        b.append_to_block(b.entry, ia);
        let vs = b.arg_pool.from_iter(vec![ia, ic].into_iter());
        let j = b.add_value(ValueDef::Operator(
            Operator::I32Store8 {
                memory: MemoryArg {
                    align: 0,
                    offset: 0,
                    memory: mem,
                },
            },
            vs,
            tz,
        ));
        b.append_to_block(b.entry, j);
    }
    b.set_terminator(b.entry, crate::Terminator::Return { values: vec![] });
    let f = m.funcs.push(FuncDecl::Body(null, format!("z"), b));
    add_start(m, f);
}
pub fn metafuse_iter(m: &mut Module, x: &[(usize, u8)], mem: Memory) {
    for w in x.chunks(4096) {
        fuse_iter(m, w.iter().map(|a| *a), mem);
    }
}
pub fn metafuse(m: &mut Module, mem: Memory, dat: MemoryData) {
    let null = new_sig(
        m,
        SignatureData::Func {
            params: vec![],
            returns: vec![],
            shared: true,
        },
    );
    let mut v = vec![];
    for s in dat.segments.iter() {
        v.extend(s.data.iter().enumerate().map(|(a, b)| (a + s.offset, *b)));
    }
    metafuse_iter(m, &v, mem);
    let mut b = FunctionBody::new(m, null);
    let vz = b.arg_pool.from_iter(empty());
    let tz = b.type_pool.from_iter(empty());
    let ti = b.type_pool.from_iter(vec![Type::I32].into_iter());
    let ia = b.add_value(ValueDef::Operator(
        Operator::I32Const {
            value: dat.initial_pages as u32,
        },
        vz,
        ti,
    ));
    b.append_to_block(b.entry, ia);
    let vs = b.arg_pool.from_iter(vec![ia].into_iter());
    let ib = b.add_value(ValueDef::Operator(
        Operator::MemoryGrow { mem: mem },
        vs,
        tz,
    ));
    b.append_to_block(b.entry, ib);
    b.set_terminator(b.entry, crate::Terminator::Return { values: vec![] });
    let f = m.funcs.push(FuncDecl::Body(null, format!("z"), b));
    add_start(m, f);
}
pub fn metafuse_all(m: &mut Module, cfg: &mut impl Cfg) {
    let mut b = BTreeMap::new();
    for mem in m
        .memories
        .entries_mut()
        .collect::<Vec<_>>()
        .into_iter()
        .rev()
    {
        let memory64 = mem.1.memory64;
        let shared = mem.1.shared;
        let page_size_log2 = mem.1.page_size_log2;
        b.insert(
            mem.0,
            core::mem::replace(
                mem.1,
                MemoryData {
                    initial_pages: 0,
                    maximum_pages: None,
                    segments: vec![],
                    memory64,
                    shared,
                    page_size_log2,
                },
            ),
        );
    }
    for mem in m.memories.iter().collect::<Vec<_>>() {
        if !cfg.unmemmable(m, mem) {
            m.memories[mem] = b.remove(&mem).unwrap();
        }
    }
    for (c, d) in b.into_iter() {
        metafuse(m, c, d);
    }
}
pub trait Cfg {
    fn unmemmable(&mut self, module: &mut Module, mem: Memory) -> bool;
}
pub struct All {}
impl Cfg for All {
    fn unmemmable(&mut self, module: &mut Module, mem: Memory) -> bool {
        true
    }
}

pub struct ImportsOnly {}
impl Cfg for ImportsOnly {
    fn unmemmable(&mut self, module: &mut Module, mem: Memory) -> bool {
        for i in module.imports.iter().map(|a| a.clone()).collect::<Vec<_>>() {
            // if self.cfg.do_lower(&i.module, &i.name) {
            if i.kind == ImportKind::Memory(mem) {
                return true;
            }
            // }
        }
        false
    }
}
