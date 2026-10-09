# SIMD support

Fixed-width CLIF vectors are represented as ordered Waffle `v128` chunks, from
low bits to high bits. Vectors up to 128 bits use one chunk; 256-bit and
512-bit vectors use two and four chunks. Unused bits in the final chunk are
zeroed. Dynamic vectors are unsupported.

The bridge lowers `vconst`, `scalar_to_vector`, `splat`, `insertlane`,
`extractlane`, `shuffle`, `swizzle`, `x86_pshufb`, vector `bitcast`, vector
`load`/`store`, widening vector loads, lane-wise add/subtract/multiply where
Wasm has the lane operation, signed/unsigned min/max, saturating add/subtract,
integer and float comparisons, integer absolute value, float sign-copy,
`select`, `blendv`, `bitselect`, `iadd_pairwise`, `smulhi`/`umulhi`,
`vany_true`, `vall_true`, and `vhigh_bits`. It also supports Wasm's vector
float-to-integer saturating conversions, integer-to-float conversions,
`fpromote`, and `fdemote` shapes. Operations run over the ordered v128 chunks,
and padding bits are normalized after each result. Vector shifts and rotates
are legalized lane by lane through scalar Wasm operators.

Lane operations cover i8, i16, i32, i64, f32, and f64 where a corresponding
Wasm SIMD operator or scalar legalization exists. `shuffle`, `swizzle`, and
`x86_pshufb` currently require i8x16. Unsupported operations include vector
division/remainder, i8 lane multiplication, fused multiply-add,
and conversions with no matching Wasm operator. Dynamic vectors remain
unsupported. Wider-vector operations that cross chunk boundaries must have a
specific legalization; otherwise translation reports the unsupported opcode.

`tests/fixtures` contains differential fixtures. Use `; wasm-run:` when the
Cranelift interpreter does not implement an instruction but Wasm execution can
still check its expected result. Use `tests/fixtures/error` for unsupported
translation cases.
