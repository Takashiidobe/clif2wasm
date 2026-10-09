use crate::*;
use sha3::digest::*;
pub fn ix(m: &mut Module, c: &mut (dyn FuncCollector + '_)) {
    for f in m.funcs.iter().collect::<::alloc::collections::BTreeSet<_>>() {
        let n = sha3::Sha3_256::digest(m.funcs[f].name());
        let i = m
            .imports
            .iter()
            .find_map(|a| {
                if a.kind == ImportKind::Func(f) {
                    Some((
                        sha3::Sha3_256::digest(&a.module),
                        sha3::Sha3_256::digest(&a.name),
                    ))
                } else {
                    None
                }
            });
        let s = m.funcs[f].sig();
        let SignatureData::Func { params, returns, .. } = m.signatures[s].clone() else {
            continue;
        };
    }
}
