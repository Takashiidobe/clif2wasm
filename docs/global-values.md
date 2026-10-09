# Global values

Cranelift 0.136 has no `global_value` instruction. A global value reaches code
only through `symbol_value` or `tls_value`, so `symbol_value` of a `symbol`
global value is the only lowered form. It becomes a marker `global.get` that the
relocatable core resolves to the data address plus the symbol's offset, in both
whole-module and object modes.

## Unsupported

All fail with `CLIF2WASM-E2000` at the instruction, naming the form.

- `symbol_value` of a `vmctx`, `load`, `iadd_imm` or `dyn_scale_target_const`
  global value: no Cranelift backend accepts these either, and `vmctx` params
  are rejected in signatures.
- `tls_value` and `symbol_value` of a `tls` symbol: wasm has no thread-local
  storage model. Lowering to ordinary data would silently share one value
  between threads.
- `declare_data` / `declare_anonymous_data` with `tls = true` fail up front for
  the same reason, so TLS data is never laid out as ordinary data.
