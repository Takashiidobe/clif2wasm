use alloc::{borrow::ToOwned, vec::Vec};

use crate::*;
pub fn add_start(m: &mut Module, tf: Func) {
    let s = SignatureData::Func {
        params: vec![],
        returns: vec![],
        shared: true,
    };
    let s = new_sig(m, s);
    let mut f = FunctionBody::new(&m, s);
    let vz = f.arg_pool.from_iter(core::iter::empty());
    let t = m.funcs[tf].sig();
    let SignatureData::Func {
        params, returns, ..
    } = m.signatures[t].clone()
    else {
        todo!()
    };
    let t = returns;
    let tz = f.type_pool.from_iter(t.into_iter());
    let v = f.add_value(ValueDef::Operator(
        Operator::Call { function_index: tf },
        vz,
        tz,
    ));
    f.append_to_block(f.entry, v);
    f.set_terminator(
        f.entry,
        match m.start_func {
            Some(a) => Terminator::ReturnCall {
                func: a,
                args: vec![],
            },
            None => Terminator::Return { values: vec![] },
        },
    );
    let f = m.funcs.push(FuncDecl::Body(s, format!("start"), f));
    m.start_func = Some(f);
}
pub fn new_sig(m: &mut Module, s: SignatureData) -> Signature {
    for (a, b) in m.signatures.entries() {
        if *b == s {
            return a;
        }
    }
    return m.signatures.push(s);
}

pub fn results_ref_2(f: &mut FunctionBody, c: Value) -> Vec<Value> {
    let c = f.resolve_and_update_alias(c);
    let b = f.value_blocks[c];
    let mut v = vec![];
    let s = match f.values[c] {
        ValueDef::Operator(_, _1, _2) => f.type_pool[_2].to_owned(),
        _ => return vec![c],
    };
    if s.len() == 1 {
        return vec![c];
    }
    for (s, i) in s.iter().map(|a| *a).enumerate() {
        let w = f.add_value(ValueDef::PickOutput(c, s as u32, i));
        f.append_to_block(b, w);
        v.push(w);
    }

    return v;
}
