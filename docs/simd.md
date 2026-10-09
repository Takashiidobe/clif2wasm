# SIMD

A fixed-width CLIF vector is a list of Waffle `v128` chunks, low bits first: one
chunk up to 128 bits, two for 256, four for 512. Unused bits in the last chunk
are zero, and every result is re-normalized. Dynamic vectors are unsupported.

Lane types are i8, i16, i32, i64, f32 and f64, wherever Wasm has the operator or
a scalar legalization exists. Shifts and rotates are legalized lane by lane
through scalar Wasm operators. `shuffle`, `swizzle` and `x86_pshufb` require
i8x16.

## Supported

- Construction and lanes: `vconst`, `scalar_to_vector`, `splat`, `insertlane`,
  `extractlane`, `shuffle`, `swizzle`, `x86_pshufb`
- Memory: vector `load`/`store`, widening loads
- `bitcast`, `select`, `select_spectre_guard` (same lowering as `select`; wasm has no speculation to guard), `blendv`, `bitselect`
- x86 ops legalized to host-independent wasm: `x86_pmulhrsw`, `x86_pmaddubsw` (i8x16 only; extend, multiply, saturating pairwise add), `x86_cvtt2dq` (f32x4 to i32x4 only; `INT_MIN` for NaN and overflow, unlike wasm's saturating truncation)
- Arithmetic: add, sub, mul (where Wasm has the lane op), signed/unsigned
  min/max, saturating add/sub, integer abs, `iadd_pairwise`, `smulhi`/`umulhi`,
  float sign-copy
- Integer and float comparisons
- `vany_true`, `vall_true`, `vhigh_bits`
- Conversions: float-to-int saturating, int-to-float, `fpromote`, `fdemote`
  (Wasm shapes only)

## Unsupported

Translation reports these as unsupported opcodes.

- Division and remainder
- i8 lane multiply
- Fused multiply-add
- Conversions with no matching Wasm operator
- Cross-chunk operations without a specific legalization

## Tests

Differential fixtures live in `tests/fixtures`. Add `; wasm-run:` when the
Cranelift interpreter lacks the instruction but Wasm execution can check the
result. Put unsupported-translation cases in `tests/fixtures/error`.
