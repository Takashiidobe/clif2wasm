use core::mem::replace;

use alloc::borrow::ToOwned;

use crate::*;

pub fn with_swizz<R,T: FuncCollector + ?Sized>(
    module: &mut Module,
    f: Func,
    collector: &mut T,
    shim: impl FnOnce(
        (
            &mut Module,
            &mut FunctionBody,
            Func,
            &mut T,
        ),
    ) -> R,
) -> R {
    let sig = module.funcs[f].sig();
    let name = module.funcs[f].name().to_owned();
    let g = replace(
        &mut module.funcs[f],
        crate::FuncDecl::Import(sig, name.clone()),
    );
    let g = module.funcs.push(g);
    for i in module.imports.iter_mut() {
        if let ImportKind::Func(i) = &mut i.kind {
            if *i == f {
                *i = g;
            }
        }
    }
    let mut dst = FunctionBody::new(module, sig);
    let r = shim((module, &mut dst, g, collector));
    module.funcs[f] = FuncDecl::Body(sig, name, dst);
    collector.collect_func(f);
    return r;
}