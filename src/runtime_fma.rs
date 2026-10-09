use cranelift_codegen::ir::{
    AbiParam, Function, InstBuilder, MemFlagsData, Signature, UserFuncName, Value,
    condcodes::IntCC, types,
};
use cranelift_codegen::isa::CallConv;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};

use crate::RuntimeFn;

pub fn build(kind: RuntimeFn) -> Option<Function> {
    Some(match kind {
        RuntimeFn::FmaF32 => build_fma(Format::F32),
        RuntimeFn::FmaF64 => build_fma(Format::F64),
        _ => return None,
    })
}

#[derive(Copy, Clone)]
struct Format {
    float: types::Type,
    int: types::Type,
    work: types::Type,
    exp_bits: i64,
    precision: i64,
}

impl Format {
    const F32: Format = Format {
        float: types::F32,
        int: types::I32,
        work: types::I64,
        exp_bits: 8,
        precision: 24,
    };
    const F64: Format = Format {
        float: types::F64,
        int: types::I64,
        work: types::I128,
        exp_bits: 11,
        precision: 53,
    };

    fn work_bits(self) -> i64 {
        self.work.bits() as i64
    }

    fn bias(self) -> i64 {
        (1 << (self.exp_bits - 1)) - 1
    }

    fn sign_shift(self) -> i64 {
        self.exp_bits + self.precision - 1
    }
}

struct Ctx<'a, 'b> {
    b: &'a mut FunctionBuilder<'b>,
    f: Format,
}

impl Ctx<'_, '_> {
    fn int(&mut self, v: i64) -> Value {
        self.b.ins().iconst(self.f.int, v)
    }

    fn i64(&mut self, v: i64) -> Value {
        self.b.ins().iconst(types::I64, v)
    }

    fn work(&mut self, v: i64) -> Value {
        if self.f.work == types::I128 {
            let lo = self.b.ins().iconst(types::I64, v);
            let hi = self.b.ins().iconst(types::I64, v >> 63);
            self.b.ins().iconcat(lo, hi)
        } else {
            self.b.ins().iconst(self.f.work, v)
        }
    }

    fn widen(&mut self, v: Value) -> Value {
        self.b.ins().uextend(self.f.work, v)
    }

    fn work_from_i64(&mut self, v: Value) -> Value {
        if self.f.work == types::I64 {
            v
        } else {
            self.b.ins().uextend(self.f.work, v)
        }
    }

    fn shl(&mut self, v: Value, amount: Value) -> Value {
        self.b.ins().ishl(v, amount)
    }

    fn shr(&mut self, v: Value, amount: Value) -> Value {
        self.b.ins().ushr(v, amount)
    }

    fn clz_work_as_i64(&mut self, v: Value) -> Value {
        let c = self.b.ins().clz(v);
        if self.f.work == types::I64 {
            c
        } else {
            self.b.ins().ireduce(types::I64, c)
        }
    }

    fn ne_zero(&mut self, v: Value) -> Value {
        let zero = self.work(0);
        self.b.ins().icmp(IntCC::NotEqual, v, zero)
    }

    fn exp_field(&mut self, bits: Value) -> Value {
        let sh = self.int(self.f.precision - 1);
        let shifted = self.b.ins().ushr(bits, sh);
        let mask = self.int((1 << self.f.exp_bits) - 1);
        self.b.ins().band(shifted, mask)
    }

    fn is_exp_max(&mut self, bits: Value) -> Value {
        let ex = self.exp_field(bits);
        let max = self.int((1 << self.f.exp_bits) - 1);
        self.b.ins().icmp(IntCC::Equal, ex, max)
    }

    fn is_zero(&mut self, bits: Value) -> Value {
        let mask = self.int(((1u64 << self.f.sign_shift()) - 1) as i64);
        let magnitude = self.b.ins().band(bits, mask);
        let zero = self.int(0);
        self.b.ins().icmp(IntCC::Equal, magnitude, zero)
    }

    fn sign_bit(&mut self, bits: Value) -> Value {
        let mask = self.int(1 << self.f.sign_shift());
        self.b.ins().band(bits, mask)
    }

    fn unpack(&mut self, bits: Value) -> (Value, Value) {
        let frac_mask = self.int((1 << (self.f.precision - 1)) - 1);
        let frac = self.b.ins().band(bits, frac_mask);
        let ex = self.exp_field(bits);
        let ex64 = self.b.ins().uextend(types::I64, ex);
        let zero = self.i64(0);
        let normal = self.b.ins().icmp(IntCC::NotEqual, ex64, zero);
        let hidden = self.int(1 << (self.f.precision - 1));
        let zero_int = self.int(0);
        let hidden = self.b.ins().select(normal, hidden, zero_int);
        let m = self.b.ins().bor(frac, hidden);
        let m = self.widen(m);
        let one = self.i64(1);
        let eff = self.b.ins().select(normal, ex64, one);
        let offset = self.i64(self.f.bias() + self.f.precision - 1);
        let e = self.b.ins().isub(eff, offset);
        let clz = self.clz_work_as_i64(m);
        let pad = self.i64(self.f.work_bits() - self.f.precision);
        let s = self.b.ins().isub(clz, pad);
        let m = self.shl(m, s);
        let e = self.b.ins().isub(e, s);
        (m, e)
    }
}

fn sig(f: Format) -> Signature {
    let mut s = Signature::new(CallConv::SystemV);
    for _ in 0..3 {
        s.params.push(AbiParam::new(f.float));
    }
    s.returns.push(AbiParam::new(f.float));
    s
}

fn build_fma(f: Format) -> Function {
    let mut func = Function::with_name_signature(UserFuncName::user(0, 0), sig(f));
    let mut fbctx = FunctionBuilderContext::new();
    {
        let mut builder = FunctionBuilder::new(&mut func, &mut fbctx);
        let entry = builder.create_block();
        let hardware_product = builder.create_block();
        let check_addend = builder.create_block();
        let addend_special = builder.create_block();
        let check_addend_zero = builder.create_block();
        let product_only = builder.create_block();
        let general = builder.create_block();
        builder.append_block_params_for_function_params(entry);

        builder.switch_to_block(entry);
        let [fa, fb, fc] = [0, 1, 2].map(|i| builder.block_params(entry)[i]);
        let mut cx = Ctx { b: &mut builder, f };
        let flags = MemFlagsData::new();
        let a = cx.b.ins().bitcast(f.int, flags, fa);
        let b = cx.b.ins().bitcast(f.int, flags, fb);
        let c = cx.b.ins().bitcast(f.int, flags, fc);

        let a_max = cx.is_exp_max(a);
        let b_max = cx.is_exp_max(b);
        let a_zero = cx.is_zero(a);
        let b_zero = cx.is_zero(b);
        let any_max = cx.b.ins().bor(a_max, b_max);
        let any_zero = cx.b.ins().bor(a_zero, b_zero);
        let simple_product = cx.b.ins().bor(any_max, any_zero);
        cx.b.ins()
            .brif(simple_product, hardware_product, &[], check_addend, &[]);

        cx.b.switch_to_block(hardware_product);
        let p = cx.b.ins().fmul(fa, fb);
        let r = cx.b.ins().fadd(p, fc);
        cx.b.ins().return_(&[r]);

        cx.b.switch_to_block(check_addend);
        let c_max = cx.is_exp_max(c);
        cx.b.ins()
            .brif(c_max, addend_special, &[], check_addend_zero, &[]);

        cx.b.switch_to_block(addend_special);
        let zero = match f.float {
            types::F32 => cx.b.ins().f32const(0.0),
            _ => cx.b.ins().f64const(0.0),
        };
        let r = cx.b.ins().fadd(fc, zero);
        cx.b.ins().return_(&[r]);

        cx.b.switch_to_block(check_addend_zero);
        let c_zero = cx.is_zero(c);
        cx.b.ins().brif(c_zero, product_only, &[], general, &[]);

        cx.b.switch_to_block(product_only);
        let r = cx.b.ins().fmul(fa, fb);
        cx.b.ins().return_(&[r]);

        cx.b.switch_to_block(general);
        let bits = general_path(&mut cx, a, b, c);
        let r = cx.b.ins().bitcast(f.float, flags, bits);
        cx.b.ins().return_(&[r]);

        builder.seal_all_blocks();
        builder.finalize(cranelift_codegen::isa::TargetFrontendConfig {
            default_call_conv: CallConv::SystemV,
            pointer_width: target_lexicon::PointerWidth::U32,
            page_size_align_log2: 16,
        });
    }
    func
}

fn general_path(cx: &mut Ctx, a: Value, b: Value, c: Value) -> Value {
    let f = cx.f;
    let w = f.work_bits();
    let p = f.precision;

    let (ma, ea) = cx.unpack(a);
    let (mb, eb) = cx.unpack(b);
    let (mc, ec) = cx.unpack(c);
    let sign_a = cx.sign_bit(a);
    let sign_b = cx.sign_bit(b);
    let sign_c = cx.sign_bit(c);
    let sign_p = cx.b.ins().bxor(sign_a, sign_b);

    let product = cx.b.ins().imul(ma, mb);
    let clz_p = cx.clz_work_as_i64(product);
    let one = cx.i64(1);
    let norm_p = cx.b.ins().isub(clz_p, one);
    let prod_n = cx.shl(product, norm_p);
    let ep_sum = cx.b.ins().iadd(ea, eb);
    let exp_p = cx.b.ins().isub(ep_sum, norm_p);

    let lift = cx.i64(w - p - 1);
    let addend_n = cx.shl(mc, lift);
    let exp_c = cx.b.ins().isub(ec, lift);

    let exp_gt = cx.b.ins().icmp(IntCC::SignedGreaterThan, exp_p, exp_c);
    let exp_eq = cx.b.ins().icmp(IntCC::Equal, exp_p, exp_c);
    let mant_ge =
        cx.b.ins()
            .icmp(IntCC::UnsignedGreaterThanOrEqual, prod_n, addend_n);
    let tie_ge = cx.b.ins().band(exp_eq, mant_ge);
    let p_big = cx.b.ins().bor(exp_gt, tie_ge);

    let big = cx.b.ins().select(p_big, prod_n, addend_n);
    let small = cx.b.ins().select(p_big, addend_n, prod_n);
    let exp_big = cx.b.ins().select(p_big, exp_p, exp_c);
    let exp_small = cx.b.ins().select(p_big, exp_c, exp_p);
    let sign_big = cx.b.ins().select(p_big, sign_p, sign_c);
    let sign_small = cx.b.ins().select(p_big, sign_c, sign_p);

    let distance = cx.b.ins().isub(exp_big, exp_small);
    let max_shift = cx.i64(w - 1);
    let shift = cx.b.ins().umin(distance, max_shift);
    let shifted = cx.shr(small, shift);
    let work_one = cx.work(1);
    let bit = cx.shl(work_one, shift);
    let low_mask = cx.b.ins().isub(bit, work_one);
    let lost = cx.b.ins().band(small, low_mask);
    let lost_any = cx.ne_zero(lost);
    let sticky = cx.b.ins().uextend(f.work, lost_any);
    let small_aligned = cx.b.ins().bor(shifted, sticky);

    let same_sign = cx.b.ins().icmp(IntCC::Equal, sign_big, sign_small);
    let sum = cx.b.ins().iadd(big, small_aligned);
    let diff = cx.b.ins().isub(big, small_aligned);
    let total = cx.b.ins().select(same_sign, sum, diff);

    let clz_t = cx.clz_work_as_i64(total);
    let total_n = cx.shl(total, clz_t);
    let top = cx.i64(w - 1);
    let exp_total = cx.b.ins().isub(exp_big, clz_t);
    let exp_top = cx.b.ins().iadd(exp_total, top);
    let bias = cx.i64(f.bias());
    let biased = cx.b.ins().iadd(exp_top, bias);

    let zero64 = cx.i64(0);
    let denormal_gap = cx.b.ins().isub(one, biased);
    let denormal_gap = cx.b.ins().smax(denormal_gap, zero64);
    let base_shift = cx.i64(w - p);
    let drop = cx.b.ins().iadd(base_shift, denormal_gap);
    let work_bits = cx.i64(w);
    let drop_c = cx.b.ins().umin(drop, work_bits);
    let flush = cx.b.ins().icmp(IntCC::UnsignedGreaterThan, drop, work_bits);

    let guard_pos = cx.b.ins().isub(drop_c, one);
    let above_guard = cx.shr(total_n, guard_pos);
    let kept = cx.shr(above_guard, one);
    let guard = cx.b.ins().band(above_guard, work_one);
    let guard_bit = cx.shl(work_one, guard_pos);
    let below_mask = cx.b.ins().isub(guard_bit, work_one);
    let below = cx.b.ins().band(total_n, below_mask);
    let below_any = cx.ne_zero(below);
    let below_one = cx.b.ins().uextend(f.work, below_any);
    let kept_odd = cx.b.ins().band(kept, work_one);
    let round_tie = cx.b.ins().bor(below_one, kept_odd);
    let round_up = cx.b.ins().band(guard, round_tie);
    let kept = cx.b.ins().iadd(kept, round_up);

    let exp_base = cx.b.ins().iadd_imm_s(biased, -1);
    let exp_base = cx.b.ins().smax(exp_base, zero64);
    let exp_base = cx.work_from_i64(exp_base);
    let mant_shift = cx.i64(p - 1);
    let exp_bits = cx.shl(exp_base, mant_shift);
    let packed = cx.b.ins().iadd(exp_bits, kept);

    let inf_bits = cx.work(((1 << f.exp_bits) - 1) << (p - 1));
    let overflow =
        cx.b.ins()
            .icmp(IntCC::UnsignedGreaterThanOrEqual, packed, inf_bits);
    let packed = cx.b.ins().select(overflow, inf_bits, packed);
    let packed = cx.b.ins().ireduce(f.int, packed);

    let zero_int = cx.int(0);
    let packed = cx.b.ins().select(flush, zero_int, packed);
    let signed = cx.b.ins().bor(packed, sign_big);
    let work_zero = cx.work(0);
    let total_zero = cx.b.ins().icmp(IntCC::Equal, total, work_zero);
    cx.b.ins().select(total_zero, zero_int, signed)
}
