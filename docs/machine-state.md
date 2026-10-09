# Traps and machine-state intrinsics

- `trap` is `unreachable`. `trapz`/`trapnz` split the block (bridge.rs) into a trap block and a resume block on a `CondBr`; later instructions of the CLIF block continue in the resume block, so incoming branches still target the head.
- Trap codes are not reported to the host (clif2wasm-aaw.26).
- `debugtrap` is a no-op: no debugger exists to observe it.
- `sequence_point` is erased. Its debug tags have nowhere to go in the output, and the barrier it provides already holds because waffle never reorders side-effecting operations.
- `get_stack_pointer` reads the shadow-stack global, so inside a function with stack slots it equals the frame base. It must produce a 32-bit pointer.
- Unsupported, with a specific error: `get_pinned_reg`/`set_pinned_reg` (the relocatable form has no slot for another global), `get_frame_pointer` (no frame-pointer chain), `get_return_address` and `get_exception_handler_address` (not observable in wasm).
