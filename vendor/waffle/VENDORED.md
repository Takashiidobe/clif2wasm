# Vendored waffle

Base: bytecodealliance/waffle `c466056` (0.3.2, wasmparser/wasm-encoder 0.248).
Chosen over the portal-co fork for correctness (it has the multi-value call
result order fix); the fork's extras are re-added here only as needed.

## Local patches

1. `pub mod backend` in `src/lib.rs` (clif2wasm drives `WasmFuncBackend`).
2. Tail calls: `Terminator::ReturnCall` / `ReturnCallIndirect` in `src/ir/func.rs`,
   decoded in `src/frontend.rs`, emitted in `src/backend/mod.rs`; the interpreter
   does not support them.
3. Atomics: 67 `Operator` variants carrying `memory: MemoryArg` in `src/ops.rs`,
   wasmparser conversions, and `src/op_traits.rs` entries; frontend/backend arms.
4. `MemoryData::shared`, decoded and emitted as the shared-memory flag.

## Not ported

memory64, `page_size_log2`, table64, GC/heap types, exception handling,
`ReturnCallRef`, and the fork's extra passes. `MemoryArg.offset` is `u32`.
