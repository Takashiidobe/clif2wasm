use crate::op_traits::rewrite_mem;
use crate::util::{add_start, new_sig};
use crate::{HeapType, StorageType, WithNullable};
use alloc::boxed::Box;
use alloc::collections::{BTreeMap, BTreeSet};
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;
use anyhow::Context;
use arena_traits::IndexAlloc;
use core::mem::{replace, take};
use core::{
    hash::Hash,
    iter::empty,
    ops::{Deref, DerefMut},
};
use hashbrown::HashMap;
use paste::paste;

use crate::{
    entity::EntityRef, i2x, x2i, ControlTag, ExportKind, Func, FuncDecl, FunctionBody, Global,
    ImportKind, Memory, Module, Operator, Signature, SignatureData, Table, TableData, Type,
    ValueDef,
};

use super::fcopy::{clone_fn, DontObf};
use super::kts::Kts;
#[derive(Eq, PartialEq, Clone, Hash)]
pub struct IKW(pub ImportKind);

pub struct State<I, G = bool> {
    cache: HashMap<IKW, ImportKind>,
    fun_cache: BTreeMap<Func, Func>,
    table_cache: BTreeMap<Table, Table>,
    sig_cache: BTreeMap<Signature, Signature>,
    ub_cache: BTreeMap<Signature, Func>,
    pub importmap: I,
    pub tables: BTreeSet<Table>,
    pub invasive: G,
    // pub(crate) tm: crate::td::TM,
}

impl<I, G> State<I, G> {
    pub fn new(importmap: I, tables: BTreeSet<Table>, invasive: G) -> Self {
        return Self {
            importmap,
            cache: Default::default(),
            fun_cache: Default::default(),
            table_cache: Default::default(),
            tables,
            invasive,
            // tm: Default::default(),
            sig_cache: Default::default(),
            ub_cache: Default::default(),
        };
    }
}
pub struct Copier<A, B, S> {
    pub src: A,
    pub dest: B,
    pub state: S,
}
impl<A, B: Deref, S> Deref for Copier<A, B, S> {
    type Target = B::Target;

    fn deref(&self) -> &Self::Target {
        &*self.dest
    }
}
impl<A, B: DerefMut, S> DerefMut for Copier<A, B, S> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut *self.dest
    }
}
macro_rules! translator {
    ($a:tt) => {
        paste! {
            pub fn [<translate_ $a>](&mut self, m: $a) -> anyhow::Result<$a>{
                let ImportKind::$a(n) = self.translate_import(ImportKind::$a(m))? else{
                    anyhow::bail!("not the right item")
                };
                return Ok(n);
            }
        }
    };
}
pub fn tree_shake(m: &mut Module) -> anyhow::Result<()> {
    return tree_shake_via(
        m,
        import_fn(|_, _, m, n| Ok(Some(ImportBehavior::Passthrough(m, n)))),
    );
}
pub fn tree_shake_via(m: &mut Module, i: impl Imports) -> anyhow::Result<()> {
    let mut n = replace(m, Module::empty());
    let exports = n.exports.clone();
    let mut s = Copier::new(
        &mut n,
        m,
        Box::new(State::new(Box::new(i), BTreeSet::new(), true)),
    );
    s.render_imports()?;
    for x in exports.iter() {
        let i = x2i(x.kind.clone());
        let i = s.translate_import(i)?;
        let mut x = x.clone();
        x.kind = i2x(i);
        s.dest.exports.push(x);
    }
    Ok(())
}
pub trait Imports {
    fn get_import(
        &mut self,
        a: &mut Module<'_>,
        d: &Module<'_>,
        m: String,
        n: String,
    ) -> anyhow::Result<Option<ImportBehavior>>;
}
#[repr(transparent)]
#[derive(Clone, Debug, Copy)]
pub struct ImportFn<F>(pub F);

pub fn import_fn(
    a: impl FnMut(
        &mut Module<'_>,
        &Module<'_>,
        String,
        String,
    ) -> anyhow::Result<Option<ImportBehavior>>,
) -> impl Imports {
    ImportFn(a)
}

impl<
        F: FnMut(
            &mut Module<'_>,
            &Module<'_>,
            String,
            String,
        ) -> anyhow::Result<Option<ImportBehavior>>,
    > Imports for ImportFn<F>
{
    fn get_import(
        &mut self,
        a: &mut Module<'_>,
        d: &Module<'_>,
        m: String,
        n: String,
    ) -> anyhow::Result<Option<ImportBehavior>> {
        return (self.0)(a, d, m, n);
    }
}
#[non_exhaustive]
pub enum ImportBehavior {
    Bind(ImportKind),
    BindRerun(ImportKind),
    Passthrough(String, String),
    UB,
}
pub trait GetGuard<'a, A> {
    fn get(&self, a: &mut A, f: Func) -> FuncDecl<'a>;
}
impl<'a, A: DerefMut<Target = crate::Module<'a>>> GetGuard<'a, A> for bool {
    fn get(&self, a: &mut A, f: Func) -> FuncDecl<'a> {
        if *self {
            take(&mut a.funcs[f])
        } else {
            a.funcs[f].clone()
        }
    }
}
impl<'a, A: Deref<Target = crate::Module<'a>>> GetGuard<'a, A> for () {
    fn get(&self, a: &mut A, f: Func) -> FuncDecl<'a> {
        // if *self{
        //     take(&mut a.funcs[f])
        // }else{
        a.funcs[f].clone()
        // }
    }
}
impl<
        'a: 'b,
        'b,
        A: Deref<Target = crate::Module<'a>>,
        B: Deref<Target = crate::Module<'b>> + DerefMut,
        S: Deref<Target = State<I, G>> + DerefMut,
        I: Deref<Target = J> + DerefMut,
        J: Imports + ?Sized,
        G: GetGuard<'a, A>,
    > Copier<A, B, S>
{
    // pub fn collect(&mut self) -> anyhow::Result<BTreeMap<String, ExportKind>> {
    //     let e = get_exports(&self.src);
    //     // let mut m = HashMap::new();
    //     let mut m = BTreeMap::new();
    //     for (s, e) in e {
    //         let e = x2i(e);
    //         let r = self.translate_import(e.clone())?;
    //         m.insert(s, i2x(r));
    //     }
    //     return Ok(m);
    // }
    pub fn new(
        src: A,
        dest: B,
        // importmap: BTreeMap<(String, String), ImportKind>,
        cache: S,
    ) -> Self {
        return Self {
            src,
            dest,
            // importmap,
            state: cache,
        };
    }
    pub fn render_imports(&mut self) -> anyhow::Result<()> {
        for i in self.src.imports.clone() {
            let ImportKind::Func(_) = &i.kind else{
                continue;
            };
            self.translate_import(i.kind.clone())?;
        }
        for i in self.src.imports.clone() {
            self.translate_import(i.kind.clone())?;
        }
        Ok(())
    }
    pub fn resolve_import(&mut self, a: &ImportKind) -> anyhow::Result<Option<ImportBehavior>> {
        for i in self.src.imports.iter() {
            if i.kind == *a {
                return self.state.importmap.get_import(
                    &mut self.dest,
                    &self.src,
                    i.module.clone(),
                    i.name.clone(),
                );
            }
        }
        return Ok(None);
    }
    pub fn internal_translate_mem(&mut self, a: crate::Memory) -> anyhow::Result<crate::Memory> {
        let d = self.src.memories[a].clone();
        return Ok(self.dest.memories.push(d));
    }
    pub fn internal_translate_global(&mut self, a: crate::Global) -> anyhow::Result<crate::Global> {
        let mut d = self.src.globals[a].clone();
        self.translate_type(&mut d.ty)?;
        return Ok(self.dest.globals.push(d));
    }
    pub fn internal_translate_control_tag(
        &mut self,
        a: crate::ControlTag,
    ) -> anyhow::Result<crate::ControlTag> {
        let d = self.src.control_tags[a].sig;
        let d = self.translate_sig(d)?;
        return Ok(self
            .dest
            .control_tags
            .push(crate::ControlTagData { sig: d }));
    }
    pub fn translate_import(&mut self, a: ImportKind) -> anyhow::Result<ImportKind> {
        let i = match self.resolve_import(&a)? {
            None => None,
            Some(ImportBehavior::Bind(b)) => return Ok(b),
            Some(ImportBehavior::BindRerun(b)) => return self.translate_import(b),
            Some(ImportBehavior::Passthrough(a, b)) => Some((a, b)),
            Some(ImportBehavior::UB) => match a {
                ImportKind::Func(f) => {
                    let s = self.translate_sig(self.src.funcs[f].sig())?;
                    loop {
                        if let Some(f) = self.state.ub_cache.get(&s) {
                            return Ok(ImportKind::Func(*f));
                        }
                        let mut b = FunctionBody::new(&self.dest, s);
                        b.set_terminator(b.entry, crate::Terminator::UB);
                        let f = self.dest.funcs.push(FuncDecl::Body(s, format!("ub"), b));
                        self.state.ub_cache.insert(s, f);
                    }
                }
                _ => anyhow::bail!("ub type invalid"),
            },
        };
        if let Some(j) = i.clone() {
            for m in self.dest.imports.iter() {
                if m.module == j.0 && m.name == j.1 {
                    return Ok(m.kind.clone());
                }
            }
        }
        if let Some(b) = self.state.cache.get(&IKW(a.clone())) {
            return Ok(b.clone());
        }
        let mut c = match a {
            ImportKind::Table(t) => ImportKind::Table(self.internal_translate_table(t)?),
            ImportKind::Func(f) => ImportKind::Func(self.internal_translate_func(f)?),
            ImportKind::Global(g) => ImportKind::Global(self.internal_translate_global(g)?),
            ImportKind::Memory(m) => ImportKind::Memory(self.internal_translate_mem(m)?),
            ImportKind::ControlTag(control_tag) => {
                ImportKind::ControlTag(self.internal_translate_control_tag(control_tag)?)
            }
            ImportKind::Type(t) => ImportKind::Type(self.translate_sig(t)?),
        };
        // if let Some((j, k)) = i.as_ref() {
        //     crate::td::tm(
        //         // &mut self.dest,
        //         j.as_str(),
        //         k.as_str(),
        //         &mut c,
        //         &mut *self,
        //     )?;
        // };
        self.state.cache.insert(IKW(a.clone()), c.clone());
        if let Some(j) = i {
            self.dest.imports.push(crate::Import {
                module: j.0,
                name: j.1,
                kind: c.clone(),
            })
        }
        return Ok(c);
    }
    pub fn internal_translate_table(&mut self, tk: Table) -> anyhow::Result<Table> {
        // if let Some(c) = self.state.table_cache.get(&tk) {
        //     return Ok(*c);
        // }
        let mut t = self.src.tables[tk].clone();
        self.translate_type(&mut t.ty)?;
        // let nt = self.dest.tables.push(t.clone());
        // self.state.table_cache.insert(tk, nt);
        if let Some(u) = t.func_elements.as_mut() {
            for w in u.iter_mut() {
                *w = self.translate_Func(*w)?;
            }
        }
        // self.dest.tables[nt] = t;
        return Ok(self.dest.tables.push(t));
    }
    pub fn translate_type(&mut self, ty: &mut Type) -> anyhow::Result<()> {
        if let Type::Heap(WithNullable {
            value: HeapType::Sig { sig_index },
            ..
        }) = ty
        {
            *sig_index = self.translate_sig(*sig_index)?;
        };
        Ok(())
    }
    pub fn translate_sig(&mut self, s: Signature) -> anyhow::Result<Signature> {
        loop {
            if let Some(k) = self.state.sig_cache.get(&s) {
                return Ok(*k);
            }
            let k = self.dest.signatures.alloc(SignatureData::None);
            self.state.sig_cache.insert(s, k);
            let mut d = self.src.signatures[s].clone();
            match &mut d {
                SignatureData::Func {
                    params, returns, ..
                } => {
                    for x in params.iter_mut().chain(returns.iter_mut()) {
                        self.translate_type(x)?;
                    }
                }
                SignatureData::None => {}
                SignatureData::Struct { fields, .. } => {
                    for ty in fields.iter_mut() {
                        if let StorageType::Val(v) = &mut ty.value {
                            self.translate_type(v)?;
                        }
                    }
                }
                SignatureData::Array { ty, .. } => {
                    if let StorageType::Val(v) = &mut ty.value {
                        self.translate_type(v)?;
                    }
                }
                SignatureData::Import { like, shared } => {
                    if let HeapType::Sig { sig_index: like } = like {
                        *like = self.translate_sig(*like)?;
                    }
                }
            };
            self.dest.signatures[k] = d;
        }
    }
    pub fn internal_translate_func(&mut self, f: Func) -> anyhow::Result<Func> {
        {
            if f == Func::invalid() {
                return Ok(f);
            }
            if let Some(x) = self.state.fun_cache.get(&f) {
                return Ok(*x);
            }
            let a = self.dest.funcs.push(crate::FuncDecl::None);
            self.state.fun_cache.insert(f, a);
            for t in &self.state.tables {
                self.dest.tables[*t]
                    .func_elements
                    .get_or_insert(vec![])
                    .push(a);
            }
            if Some(f) == self.src.start_func {
                add_start(&mut self.dest, a);
            }
            let mut f = self.state.invasive.get(&mut self.src, f);
            // let sig = self.translate_sig(f.sig())?;
            if let Some(b) = f.body_mut() {
                // b.convert_to_max_ssa(None);
                // let mut c = FunctionBody::new(&self.dest, sig);
                // let l = Kts::default().translate(&mut c, &*b, b.entry)?;
                // c.entry = l;
                // *b = c;
                for v in b.values.iter() {
                    let mut k = b.values[v].clone();
                    if let ValueDef::BlockParam(_, _, x) = &mut k {
                        self.translate_type(x)?;
                    }
                    if let ValueDef::PickOutput(_, _, x) = &mut k {
                        self.translate_type(x)?;
                    }
                    if let ValueDef::Operator(a, vs, c) = &mut k {
                        let mut w = b.arg_pool[*vs].to_vec();
                        let mut e = None;
                        rewrite_mem(a, &mut w, |m, _| {
                            *m = self.translate_Memory(*m)?;
                            Ok::<_, anyhow::Error>(())
                        })?;
                        if let Some(e) = e {
                            return Err(e);
                        }
                        match a {
                            crate::Operator::Call { function_index } => {
                                *function_index = self.translate_Func(*function_index)?;
                            }
                            crate::Operator::RefFunc { func_index } => {
                                *func_index = self.translate_Func(*func_index)?;
                            }
                            crate::Operator::RefNull { ty } => {
                                self.translate_type(ty)?;
                            }
                            crate::Operator::TypedSelect { ty } => {
                                self.translate_type(ty)?;
                            }
                            Operator::CallRef { sig_index } => {
                                *sig_index = self.translate_sig(*sig_index)?;
                            }
                            crate::Operator::CallIndirect {
                                sig_index,
                                table_index,
                            } => {
                                *sig_index = self.translate_sig(*sig_index)?;
                                *table_index = self.translate_Table(*table_index)?;
                            }
                            crate::Operator::GlobalGet { global_index } => {
                                *global_index = self.translate_Global(*global_index)?;
                            }
                            crate::Operator::GlobalSet { global_index } => {
                                *global_index = self.translate_Global(*global_index)?;
                            }
                            crate::Operator::TableGet { table_index } => {
                                *table_index = self.translate_Table(*table_index)?;
                            }
                            crate::Operator::TableSet { table_index } => {
                                *table_index = self.translate_Table(*table_index)?;
                            }
                            crate::Operator::TableGrow { table_index } => {
                                *table_index = self.translate_Table(*table_index)?;
                            }
                            crate::Operator::TableSize { table_index } => {
                                *table_index = self.translate_Table(*table_index)?;
                            }
                            _ => {}
                        }
                        *vs = b.arg_pool.from_iter(w.into_iter());
                    }
                    b.values[v] = k;
                }
                for k in b.blocks.iter() {
                    let mut kv = b.blocks[k].clone();
                    match &mut kv.terminator {
                        crate::Terminator::ReturnCall { func, args } => {
                            *func = self.translate_Func(*func)?;
                        }
                        crate::Terminator::ReturnCallIndirect { sig, table, args } => {
                            *sig = self.translate_sig(*sig)?;
                            *table = self.translate_Table(*table)?;
                        }
                        crate::Terminator::ReturnCallRef { sig, args } => {
                            *sig = self.translate_sig(*sig)?;
                            // *table = self.translate_Table(*table)?;
                        }
                        _ => {}
                    }
                    b.blocks[k] = kv;
                }
                for x in b.type_pool.storage.iter_mut() {
                    self.translate_type(x)?;
                }
                // crate::td::fi(b, &mut self.dest)?;
                // (self.state.instrument)(&mut self.dest,b)?;
            }
            match &mut f {
                crate::FuncDecl::Import(a, _) => {
                    *a = self.translate_sig(*a)?;
                }
                crate::FuncDecl::Lazy(_, _, _) => todo!(),
                crate::FuncDecl::Body(a, _, _) => {
                    *a = self.translate_sig(*a)?;
                }
                crate::FuncDecl::Compiled(_, _, _) => todo!(),
                crate::FuncDecl::None => {}
            }
            self.dest.funcs[a] = f;
            return Ok(a);
        };
    }
    translator!(Memory);
    translator!(Table);
    translator!(Global);
    translator!(Func);
    translator!(ControlTag);
}

#[cfg(test)]
mod tests {
    use super::*;
}
