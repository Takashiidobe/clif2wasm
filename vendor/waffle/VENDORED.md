# Vendored waffle

Source: <https://github.com/portal-co/waffle-> at release 0.5.5 (`ffb18b8`),
the crate published as `portal-pc-waffle`. Upstream: <https://github.com/bytecodealliance/waffle>.

Cherry-picked from upstream (`git cherry-pick -x` on top of 0.5.5, kept on a
scratch branch and re-exported into this directory):

- `0f64d1b` fix multi-value operator result order (0.5.5 binds multi-value call
  results in reverse)
- `b5a7ed4` treeify soundness: never sink effectful ops (resolved by hand for the
  fork's `.value` instruction wrapper)
- `1b8bb98` resolve_aliases: resolve every terminator use
- `f7fb3a8` backend: explicit stack instead of recursion
- `31b85ce` make `passes::empty_blocks::run` public

Local edits: `fuzz/` removed; `[lints]` in `Cargo.toml` silence warnings in this
crate. `tests/roundtrip.rs` fails on `test4.wat` with the current `wat` crate
("previous `if` had no `then`"); this is unrelated to the picks above.
