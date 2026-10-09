# Stack operations

The module imports one mutable `__stack_pointer` global and uses one linear
memory. A function with fixed-size stack slots decrements the pointer on entry
and restores it on return, and `stack_addr` is an address inside that fixed
frame.

## Unsupported

Both instructions fail with `CLIF2WASM-E2000` at the instruction, naming the
missing capability.

- `dynamic_stack_addr`: the translator doesn't track dynamic allocation or
  lifetime boundaries, and mapping it into the fixed frame would be wrong.
- `stack_switch`: the ABI has no context records or switching runtime, and
  Waffle has no stack-switching operators. Lowering it to a branch or call would
  lose suspend/resume semantics.
