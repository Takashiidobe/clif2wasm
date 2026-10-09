# Opcode coverage registry

`tests/opcode_coverage.txt` lists every member of `Opcode::all()` in the pinned
Cranelift with one status:

- `lowered`: translated, with differential fixtures or generated programs behind it.
- `erased`: translated to nothing on purpose.
- `partial`: works for some types, modes or options; the note says which.
- `unsupported`: reports an unsupported-opcode error; the note names the bead or the doc that explains why.

`tests/opcode_inventory.rs` compares the registry with `Opcode::all()` in both
directions, so a Cranelift upgrade or feature change that adds or removes an opcode
fails the test until the registry is edited. Type-level gaps (for example i8 lane
multiply) live in the per-area docs (`simd.md`, `i128.md`), not here.

## Refresh workflow

1. Bump the Cranelift version and run `cargo test --test opcode_inventory`.
2. For each reported opcode, probe it with a small CLIF function through `WasmModule`.
3. Add a line with its status. Add a note for `partial` and `unsupported`, and file a bead for unsupported opcodes wasm can express.
4. When a bead lowers an opcode, flip its line in the same commit.
