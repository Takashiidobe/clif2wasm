# Exceptions

`try_call` and `try_call_indirect` are terminators. A table with no `tag` or
`default` handlers can never catch, so it lowers to a call followed by a branch
to the normal-return block; `retN` block arguments are bound to the call's
results. `context` items are ignored for the same reason.

## Unsupported

A table with a `tag` or `default` handler fails with `CLIF2WASM-E2000` at the
instruction. waffle has no wasm exception-handling operators or terminators, so
there is nothing to lower a catch edge to (tracked in `clif2wasm-aaw.31`).
