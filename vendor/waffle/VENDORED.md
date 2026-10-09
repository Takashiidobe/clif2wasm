# Vendored waffle

Source: <https://github.com/portal-co/waffle-> at release 0.5.5 (`ffb18b8`),
the crate published as `portal-pc-waffle`. Upstream: <https://github.com/bytecodealliance/waffle>.

Local changes on top of 0.5.5:

- cherry-pick of upstream `0f64d1b` (fix multi-value operator result order); the
  published 0.5.5 binds multi-value call results in reverse.
- `fuzz/` removed; `[lints]` in `Cargo.toml` silence warnings in this crate.
