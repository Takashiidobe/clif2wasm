//! f16 is soft-lowered: bits in an i32, arithmetic through f32, conversions inline.
//! The Cranelift interpreter cannot execute f16 arithmetic, so these tests compare
//! Wasmi against a reference built on exact f64 values and nearest-even rounding.

use clif2wasm::WasmModule;
use cranelift_codegen::Context;
use cranelift_module::{Linkage, Module as _};
use cranelift_reader::parse_functions;
use wasmi::{Engine, Instance, Module, Store, Val};

const SOURCE: &str = "
function %to_f32(f16) -> f32 { block0(v0: f16): v1 = fpromote.f32 v0 \n return v1 }
function %to_f64(f16) -> f64 { block0(v0: f16): v1 = fpromote.f64 v0 \n return v1 }
function %from_f32(f32) -> f16 { block0(v0: f32): v1 = fdemote.f16 v0 \n return v1 }
function %from_f64(f64) -> f16 { block0(v0: f64): v1 = fdemote.f16 v0 \n return v1 }
function %add(f16, f16) -> f16 { block0(v0: f16, v1: f16): v2 = fadd v0, v1 \n return v2 }
function %sub(f16, f16) -> f16 { block0(v0: f16, v1: f16): v2 = fsub v0, v1 \n return v2 }
function %mul(f16, f16) -> f16 { block0(v0: f16, v1: f16): v2 = fmul v0, v1 \n return v2 }
function %div(f16, f16) -> f16 { block0(v0: f16, v1: f16): v2 = fdiv v0, v1 \n return v2 }
function %min(f16, f16) -> f16 { block0(v0: f16, v1: f16): v2 = fmin v0, v1 \n return v2 }
function %max(f16, f16) -> f16 { block0(v0: f16, v1: f16): v2 = fmax v0, v1 \n return v2 }
function %copysign(f16, f16) -> f16 { block0(v0: f16, v1: f16): v2 = fcopysign v0, v1 \n return v2 }
function %neg(f16) -> f16 { block0(v0: f16): v1 = fneg v0 \n return v1 }
function %abs(f16) -> f16 { block0(v0: f16): v1 = fabs v0 \n return v1 }
function %sqrt(f16) -> f16 { block0(v0: f16): v1 = sqrt v0 \n return v1 }
function %ceil(f16) -> f16 { block0(v0: f16): v1 = ceil v0 \n return v1 }
function %floor(f16) -> f16 { block0(v0: f16): v1 = floor v0 \n return v1 }
function %trunc(f16) -> f16 { block0(v0: f16): v1 = trunc v0 \n return v1 }
function %nearest(f16) -> f16 { block0(v0: f16): v1 = nearest v0 \n return v1 }
function %lt(f16, f16) -> i8 { block0(v0: f16, v1: f16): v2 = fcmp lt v0, v1 \n return v2 }
function %eq(f16, f16) -> i8 { block0(v0: f16, v1: f16): v2 = fcmp eq v0, v1 \n return v2 }
function %ne(f16, f16) -> i8 { block0(v0: f16, v1: f16): v2 = fcmp ne v0, v1 \n return v2 }
function %uno(f16, f16) -> i8 { block0(v0: f16, v1: f16): v2 = fcmp uno v0, v1 \n return v2 }
function %from_i16(i16) -> f16 { block0(v0: i16): v1 = fcvt_from_sint.f16 v0 \n return v1 }
function %from_u16(i16) -> f16 { block0(v0: i16): v1 = fcvt_from_uint.f16 v0 \n return v1 }
function %from_i32(i32) -> f16 { block0(v0: i32): v1 = fcvt_from_sint.f16 v0 \n return v1 }
function %from_u32(i32) -> f16 { block0(v0: i32): v1 = fcvt_from_uint.f16 v0 \n return v1 }
function %to_i32_sat(f16) -> i32 { block0(v0: f16): v1 = fcvt_to_sint_sat.i32 v0 \n return v1 }
function %to_u32_sat(f16) -> i32 { block0(v0: f16): v1 = fcvt_to_uint_sat.i32 v0 \n return v1 }
function %to_i8_sat(f16) -> i8 { block0(v0: f16): v1 = fcvt_to_sint_sat.i8 v0 \n return v1 }
function %to_i32(f16) -> i32 { block0(v0: f16): v1 = fcvt_to_sint.i32 v0 \n return v1 }
function %const() -> f16 { block0: v0 = f16const 0x1.8p1 \n return v0 }
function %to_bits(f16) -> i16 { block0(v0: f16): v1 = bitcast.i16 little v0 \n return v1 }
function %from_bits(i16) -> f16 { block0(v0: i16): v1 = bitcast.f16 little v0 \n return v1 }
function %select(i32, f16, f16) -> f16 { block0(v0: i32, v1: f16, v2: f16): v3 = select v0, v1, v2 \n return v3 }
function %callee(f16) -> f16 { block0(v0: f16): v1 = fadd v0, v0 \n return v1 }
function %call(f16) -> f16 {
    fn0 = %callee(f16) -> f16
block0(v0: f16):
    v1 = call fn0(v0)
    return v1
}
function %store_load(f16) -> f16 {
    ss0 = explicit_slot 8
block0(v0: f16):
    v1 = stack_addr.i32 ss0
    store v0, v1+2
    v2 = load.f16 v1+2
    return v2
}
function %loop(f16, i32) -> f16 {
block0(v0: f16, v1: i32):
    jump block1(v0, v1)
block1(v2: f16, v3: i32):
    v4 = fadd v2, v2
    v7 = iconst.i32 -1
    v5 = iadd v3, v7
    brif v5, block1(v4, v5), block2(v4)
block2(v6: f16):
    return v6
}
";

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
}

struct Wasm {
    store: Store<()>,
    instance: Instance,
}

impl Wasm {
    fn new() -> Self {
        let mut module = WasmModule::new().unwrap();
        let functions = parse_functions(SOURCE).unwrap();
        let mut ids = Vec::new();
        for function in &functions {
            let name = function.name.to_string();
            let name = name.trim_start_matches('%');
            ids.push(
                module
                    .declare_function(name, Linkage::Export, &function.signature)
                    .unwrap(),
            );
        }
        for (function, id) in functions.into_iter().zip(ids) {
            module
                .define_function(id, &mut Context::for_function(function))
                .unwrap();
        }
        let bytes = module.finish().unwrap();
        let engine = Engine::default();
        let module = Module::new(&engine, &bytes[..]).unwrap();
        let mut store = Store::new(&engine, ());
        let instance = Instance::new(&mut store, &module, &[]).unwrap();
        Wasm { store, instance }
    }

    fn call(&mut self, name: &str, args: &[Val], result: Val) -> Val {
        let func = self.instance.get_func(&self.store, name).unwrap();
        let mut out = [result];
        func.call(&mut self.store, args, &mut out)
            .unwrap_or_else(|e| panic!("{name}: {e}"));
        out[0].clone()
    }

    fn h2h(&mut self, name: &str, a: u16) -> u16 {
        let Val::I32(r) = self.call(name, &[Val::I32(a as i32)], Val::I32(0)) else {
            unreachable!()
        };
        assert_eq!(r as u32 >> 16, 0, "{name}({a:#06x}) left dirty high bits");
        r as u16
    }

    fn hh2h(&mut self, name: &str, a: u16, b: u16) -> u16 {
        let Val::I32(r) = self.call(name, &[Val::I32(a as i32), Val::I32(b as i32)], Val::I32(0))
        else {
            unreachable!()
        };
        assert_eq!(
            r as u32 >> 16,
            0,
            "{name}({a:#06x},{b:#06x}) left dirty high bits"
        );
        r as u16
    }

    fn hh2b(&mut self, name: &str, a: u16, b: u16) -> bool {
        let Val::I32(r) = self.call(name, &[Val::I32(a as i32), Val::I32(b as i32)], Val::I32(0))
        else {
            unreachable!()
        };
        r & 0xff != 0
    }

    fn f32_2h(&mut self, a: f32) -> u16 {
        let Val::I32(r) = self.call("from_f32", &[Val::from(a)], Val::I32(0)) else {
            unreachable!()
        };
        r as u16
    }

    fn f64_2h(&mut self, a: f64) -> u16 {
        let Val::I32(r) = self.call("from_f64", &[Val::from(a)], Val::I32(0)) else {
            unreachable!()
        };
        r as u16
    }
}

fn is_nan(bits: u16) -> bool {
    bits & 0x7c00 == 0x7c00 && bits & 0x3ff != 0
}

fn to_f64(bits: u16) -> f64 {
    let sign = if bits & 0x8000 != 0 { -1.0 } else { 1.0 };
    let exp = ((bits >> 10) & 0x1f) as i32;
    let mant = (bits & 0x3ff) as f64;
    match exp {
        0 => sign * mant * 2f64.powi(-24),
        31 if mant == 0.0 => sign * f64::INFINITY,
        31 => f64::NAN,
        _ => sign * (1024.0 + mant) * 2f64.powi(exp - 25),
    }
}

fn from_f64(x: f64) -> u16 {
    if x.is_nan() {
        return 0x7e00;
    }
    let sign = if x.is_sign_negative() { 0x8000 } else { 0 };
    let abs = x.abs();
    if abs >= 65520.0 {
        return sign | 0x7c00;
    }
    let (mut lo, mut hi) = (0u16, 0x7bffu16);
    while lo < hi {
        let mid = (lo + hi).div_ceil(2);
        if to_f64(mid) <= abs {
            lo = mid;
        } else {
            hi = mid - 1;
        }
    }
    let next = lo + 1;
    let middle = (to_f64(lo) + to_f64(next)) / 2.0;
    let pick = if abs < middle {
        lo
    } else if abs > middle {
        next
    } else if lo % 2 == 0 {
        lo
    } else {
        next
    };
    sign | pick
}

fn same(name: &str, args: &str, got: u16, want: u16) {
    if is_nan(want) {
        assert!(is_nan(got), "{name}({args}): got {got:#06x}, want NaN");
    } else {
        assert_eq!(
            got, want,
            "{name}({args}): got {got:#06x}, want {want:#06x}"
        );
    }
}

fn samples(rng: &mut Rng, count: usize) -> Vec<u16> {
    let mut out = vec![
        0, 0x8000, 1, 0x8001, 0x03ff, 0x0400, 0x3c00, 0xbc00, 0x7bff, 0xfbff,
    ];
    out.extend([0x7c00, 0xfc00, 0x7e00]);
    out.extend((0..count).map(|_| rng.next() as u16));
    out
}

#[test]
fn promote_is_exact_for_every_bit_pattern() {
    let mut wasm = Wasm::new();
    for bits in 0..=u16::MAX {
        let Val::F32(got) = wasm.call("to_f32", &[Val::I32(bits as i32)], Val::from(0f32)) else {
            unreachable!()
        };
        let Val::F64(wide) = wasm.call("to_f64", &[Val::I32(bits as i32)], Val::from(0f64)) else {
            unreachable!()
        };
        let want = to_f64(bits);
        if want.is_nan() {
            assert!(
                got.to_float().is_nan() && wide.to_float().is_nan(),
                "{bits:#06x}"
            );
        } else {
            assert_eq!(got.to_float() as f64, want, "{bits:#06x}");
            assert_eq!(
                got.to_float().to_bits() >> 31,
                (bits >> 15) as u32,
                "{bits:#06x} sign"
            );
            assert_eq!(wide.to_float(), want, "{bits:#06x} f64");
        }
    }
}

#[test]
fn demote_rounds_to_nearest_even_without_double_rounding() {
    let mut wasm = Wasm::new();
    let mut rng = Rng(0x9e3779b97f4a7c15);
    let mut check = |x: f64| {
        let want = from_f64(x);
        same("from_f64", &format!("{x:e}"), wasm.f64_2h(x), want);
        let narrow = x as f32;
        if narrow as f64 == x {
            same(
                "from_f32",
                &format!("{narrow:e}"),
                wasm.f32_2h(narrow),
                want,
            );
        }
    };
    for bits in 0..0x7c00u16 {
        let (here, next) = (to_f64(bits), to_f64(bits + 1));
        let middle = (here + next) / 2.0;
        for x in [here, middle, next, middle.next_up(), middle.next_down()] {
            check(x);
            check(-x);
        }
        let nudge = middle * (1.0 + 2f64.powi(-40));
        check(nudge);
        check(-nudge);
        check(middle * (1.0 - 2f64.powi(-40)));
    }
    for x in [
        65504.0,
        65519.0,
        65520.0,
        65520.000001,
        1e9,
        f64::MAX,
        f64::MIN_POSITIVE,
        5e-324,
        2f64.powi(-25),
        2f64.powi(-25).next_up(),
        f64::INFINITY,
        f64::NEG_INFINITY,
    ] {
        check(x);
        check(-x);
    }
    for _ in 0..200_000 {
        let exp = (rng.next() % 50) as i32 - 30;
        let mant = 1.0 + (rng.next() >> 11) as f64 / (1u64 << 53) as f64;
        check(mant * 2f64.powi(exp));
        check(f32::from_bits(rng.next() as u32) as f64);
    }
}

#[test]
fn demote_keeps_nan_and_signed_zero() {
    let mut wasm = Wasm::new();
    assert!(is_nan(wasm.f32_2h(f32::NAN)));
    assert!(is_nan(wasm.f64_2h(f64::NAN)));
    assert_eq!(wasm.f32_2h(-0.0), 0x8000);
    assert_eq!(wasm.f64_2h(-0.0), 0x8000);
    assert_eq!(wasm.f32_2h(f32::INFINITY), 0x7c00);
    assert_eq!(wasm.f32_2h(f32::NEG_INFINITY), 0xfc00);
}

#[test]
fn binary_arithmetic_matches_reference() {
    let mut wasm = Wasm::new();
    let mut rng = Rng(0x1234_5678_9abc_def1);
    let values = samples(&mut rng, 300);
    let ops: [(&str, fn(f64, f64) -> f64); 6] = [
        ("add", |a, b| a + b),
        ("sub", |a, b| a - b),
        ("mul", |a, b| a * b),
        ("div", |a, b| a / b),
        ("min", |a, b| {
            if a.is_nan() || b.is_nan() {
                f64::NAN
            } else if a == 0.0 && b == 0.0 {
                if a.is_sign_negative() { a } else { b }
            } else {
                a.min(b)
            }
        }),
        ("max", |a, b| {
            if a.is_nan() || b.is_nan() {
                f64::NAN
            } else if a == 0.0 && b == 0.0 {
                if a.is_sign_positive() { a } else { b }
            } else {
                a.max(b)
            }
        }),
    ];
    for &a in &values {
        for &b in &values {
            for (name, reference) in ops {
                let want = from_f64(reference(to_f64(a), to_f64(b)));
                same(
                    name,
                    &format!("{a:#06x}, {b:#06x}"),
                    wasm.hh2h(name, a, b),
                    want,
                );
            }
        }
    }
}

#[test]
fn unary_arithmetic_matches_reference() {
    let mut wasm = Wasm::new();
    let unary: [(&str, fn(f64) -> f64); 7] = [
        ("sqrt", f64::sqrt),
        ("ceil", f64::ceil),
        ("floor", f64::floor),
        ("trunc", f64::trunc),
        ("nearest", f64::round_ties_even),
        ("neg", |x| -x),
        ("abs", f64::abs),
    ];
    for bits in 0..=u16::MAX {
        for (name, reference) in unary {
            let want = from_f64(reference(to_f64(bits)));
            same(name, &format!("{bits:#06x}"), wasm.h2h(name, bits), want);
        }
    }
}

#[test]
fn copysign_and_bit_moves_are_exact() {
    let mut wasm = Wasm::new();
    let mut rng = Rng(77);
    for a in samples(&mut rng, 200) {
        for b in samples(&mut rng, 20) {
            assert_eq!(wasm.hh2h("copysign", a, b), (a & 0x7fff) | (b & 0x8000));
        }
        assert_eq!(wasm.h2h("to_bits", a), a);
        assert_eq!(wasm.h2h("from_bits", a), a);
        assert_eq!(wasm.h2h("store_load", a), a);
    }
}

#[test]
fn comparisons_match_reference() {
    let mut wasm = Wasm::new();
    let mut rng = Rng(5);
    let values = samples(&mut rng, 200);
    for &a in &values {
        for &b in &values {
            let (x, y) = (to_f64(a), to_f64(b));
            assert_eq!(wasm.hh2b("lt", a, b), x < y, "lt {a:#06x} {b:#06x}");
            assert_eq!(wasm.hh2b("eq", a, b), x == y, "eq {a:#06x} {b:#06x}");
            assert_eq!(wasm.hh2b("ne", a, b), x != y, "ne {a:#06x} {b:#06x}");
            assert_eq!(wasm.hh2b("uno", a, b), x.is_nan() || y.is_nan(), "uno");
        }
    }
}

#[test]
fn integer_conversions_round_once() {
    let mut wasm = Wasm::new();
    let mut rng = Rng(99);
    let mut check_to_f16 = |name: &str, arg: Val, want: f64| {
        let Val::I32(got) = wasm.call(name, &[arg], Val::I32(0)) else {
            unreachable!()
        };
        same(name, &format!("{want}"), got as u16, from_f64(want));
    };
    for x in 0..=u16::MAX {
        check_to_f16("from_i16", Val::I32(x as i32), x as i16 as f64);
        check_to_f16("from_u16", Val::I32(x as i32), x as f64);
    }
    let mut wide = vec![
        0,
        1,
        -1,
        2047,
        2048,
        2049,
        65504,
        65519,
        65520,
        i32::MAX,
        i32::MIN,
    ];
    wide.extend((0..50_000).map(|_| (rng.next() as i32) >> (rng.next() % 32)));
    for x in wide {
        check_to_f16("from_i32", Val::I32(x), x as f64);
        check_to_f16("from_u32", Val::I32(x), x as u32 as f64);
    }
}

#[test]
fn float_to_integer_conversions_saturate_and_trap() {
    let mut wasm = Wasm::new();
    for bits in 0..=u16::MAX {
        let x = to_f64(bits);
        let Val::I32(signed) = wasm.call("to_i32_sat", &[Val::I32(bits as i32)], Val::I32(0))
        else {
            unreachable!()
        };
        let Val::I32(unsigned) = wasm.call("to_u32_sat", &[Val::I32(bits as i32)], Val::I32(0))
        else {
            unreachable!()
        };
        let Val::I32(narrow) = wasm.call("to_i8_sat", &[Val::I32(bits as i32)], Val::I32(0)) else {
            unreachable!()
        };
        assert_eq!(signed, x as i32, "to_i32_sat {bits:#06x}");
        assert_eq!(unsigned as u32, x as u32, "to_u32_sat {bits:#06x}");
        assert_eq!(narrow as i8, x as i8, "to_i8_sat {bits:#06x}");
    }
    let func = wasm.instance.get_func(&wasm.store, "to_i32").unwrap();
    let mut out = [Val::I32(0)];
    assert!(
        func.call(&mut wasm.store, &[Val::I32(0x7e00)], &mut out)
            .is_err()
    );
    func.call(&mut wasm.store, &[Val::I32(0xc200)], &mut out)
        .unwrap();
    assert!(matches!(out[0], Val::I32(-3)));
}

#[test]
fn constants_selects_calls_and_loops_carry_f16() {
    let mut wasm = Wasm::new();
    let Val::I32(constant) = wasm.call("const", &[], Val::I32(0)) else {
        unreachable!()
    };
    assert_eq!(constant as u16, from_f64(3.0));
    for (cond, want) in [(1, 0x4000), (0, 0x3c00)] {
        let Val::I32(got) = wasm.call(
            "select",
            &[Val::I32(cond), Val::I32(0x4000), Val::I32(0x3c00)],
            Val::I32(0),
        ) else {
            unreachable!()
        };
        assert_eq!(got, want);
    }
    assert_eq!(wasm.h2h("callee", 0x3c00), 0x4000);
    assert_eq!(wasm.h2h("call", 0x3c00), 0x4000);
    let Val::I32(got) = wasm.call("loop", &[Val::I32(0x3c00), Val::I32(4)], Val::I32(0)) else {
        unreachable!()
    };
    assert_eq!(got as u16, from_f64(16.0));
}

#[test]
fn dirty_high_bits_on_entry_are_ignored() {
    let mut wasm = Wasm::new();
    let Val::I32(got) = wasm.call(
        "add",
        &[Val::I32(0x7fff_3c00), Val::I32(0x1234_3c00)],
        Val::I32(0),
    ) else {
        unreachable!()
    };
    assert_eq!(got as u16, 0x4000);
}
