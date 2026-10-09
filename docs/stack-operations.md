# Stack operation support

The generated module uses a single imported mutable `__stack_pointer` global and
one linear memory. Functions with fixed-size stack slots reserve a frame by
decrementing that pointer on entry and restore it on return. `stack_addr` is
lowered to an address within that fixed frame.

`dynamic_stack_addr` is unsupported. Correct support needs to reserve storage
whose size comes from a dynamic type, update the stack pointer at the relevant
allocation point, and restore it at the right lifetime boundary. The current
translator does not track dynamic stack allocation or lifetime boundaries, so
mapping the instruction to an address in the fixed frame would be incorrect.

`stack_switch` is unsupported. Its context memory layout is platform-dependent,
and switching requires a runtime contract for initializing, suspending, and
resuming stacks. The module ABI has neither context records nor a switching
runtime, and wasm stack switching is not represented by the current Waffle
operator set. Lowering it to an ordinary branch or call would lose its
suspend/resume semantics.

Both instructions therefore produce `CLIF2WASM-E2000` diagnostics at the
instruction. The diagnostics identify the missing runtime capability rather
than reporting an opaque unknown opcode.
