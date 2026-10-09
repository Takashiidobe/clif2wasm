# SIMD support

Waffle 0.5.5 supports WebAssembly SIMD through `v128` values and SIMD operators. The Wasm backend can emit these operators. The current CLIF bridge does not yet translate CLIF vector values; `map_type` accepts scalar integers and floats plus the separate i128 pair representation, and rejects vectors.

## Planned representation

Represent a fixed-width CLIF vector as an ordered bundle of Waffle `v128` values. Chunks run from low bits to high bits, with lane 0 in the low bits of the first chunk.

- 64-bit vectors use one `v128`; unused high bits stay zero.
- 128-bit vectors map directly to one `v128`.
- 256-bit and 512-bit vectors use two or four chunks.
- Lane-wise operations lower per chunk. Shuffles, reductions, and operations that cross chunk boundaries need dedicated legalization.
- WebAssembly SIMD lane operations directly match i8, i16, i32, i64, f32, and f64. Other CLIF lane types need separate legalization or remain unsupported.
- Dynamic/scalable vectors remain unsupported because Wasm `v128` has a fixed width.

The error fixture `tests/fixtures/error/simd_splat_i32x4.clif` records the current unsupported behavior. When vector translation is implemented, move it to the regular fixture directory and add run expectations. The differential test runtime enables Wasmi SIMD.
