# Scalar fma

Wasm has no fused multiply-add, so `fma.f32` and `fma.f64` call a synthesized
helper, `__clif2wasm_fma_f32` / `__clif2wasm_fma_f64`, built as CLIF in
`src/runtime_fma.rs`. Vector `fma` is unsupported.

- `relocatable::translate` adds the helper as a weak hidden function only when a
  body contains a matching `fma`, unless the input already names one. Objects get
  the same symbol, so duplicate copies merge at link time.
- The helper rounds once, to nearest even, and handles subnormal and overflowing
  results. It works in a `2p+` bit integer (i64 for f32, i128 for f64): the exact
  product and the addend are aligned with a sticky bit, summed, then rounded.
- Non-finite operands and zero products or addends go through hardware `fmul`/`fadd`,
  which already give the right infinity, NaN and signed-zero results. An overflowing
  finite product with an infinite addend returns the addend, not `inf - inf`.
- `tests/fixtures/fma_f32.clif` and `fma_f64.clif` include cases where fused and
  separate multiply/add differ. NaN results are not in the fixtures: payloads are
  bit-compared and are not specified.
