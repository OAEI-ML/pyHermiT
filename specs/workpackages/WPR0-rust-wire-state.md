# WPR0 — Rust wire, lifecycle, and state kernel

**Goal**: establish the safe PyO3 handshake/codec and a pure-Rust state implementation
that exactly replays Python state traces.

## Read first

| What | Where |
|---|---|
| Native architecture/wire/safety | `native-backend.md` §§1–8, 12 |
| IR/backend/result/error contracts | `contracts.md` §§2–8 |
| State invariants/traces | `tableau-state.md` complete |
| Python reference deliverable | WP08 code/tests and canonical trace schema |

## Deliverables

- Pinned Rust workspace/crate config, PyO3 private module, ABI/IR handshake,
  `self_test`, typed error mapping, cancellation handle, close/busy/panic poisoning.
- Language-neutral flat IR/request/result v1 codec on both Python and Rust sides with
  golden/corrupt/fuzz/size-overflow tests; one owned copy into Rust.
- Core view lifetime/version/fingerprint metadata at session creation; no public-model
  transfer beyond the private compiled IR and at most one contiguous IR copy.
- Safe Rust node/row arenas, indexes, deltas, dependencies, trail/checkpoints, queues,
  clash/disjunction state, merge/prune mechanics, invariant checker/debug snapshots.
- GIL detach with no borrowed Python memory/callbacks and bounded event queue skeleton.
- Criterion/component benchmarks and sanitizer/Miri-compatible tests; unsafe forbidden.

## Depends on

WP01 and WP08.

## Acceptance criteria

1. Python and Rust encode/decode every golden identically and reject every malformed
   offset/count/reference/sort/enum without panic or oversized allocation.
2. Random WP08 operation traces produce identical canonical state/invariants after
   every step/backtrack, including multiple supports and slot reuse.
3. Concurrent independent mock sessions work; same-session busy/cancel/close/fork/panic
   behavior maps to stable Python errors and no panic crosses FFI.
4. Long mock native work releases the GIL and is cancellable; callbacks/events are
   drained only after reattachment.
5. Cargo fmt/Clippy/audit, native unit/property/fuzz/sanitizer/refcount/leak checks pass
   with `#![forbid(unsafe_code)]` in the kernel.
6. This package does not claim `full_reasoner`; auto remains Python and forced native
   cannot return a semantic placeholder.
7. No per-axiom FFI, OWL text/RDF intermediate, dangling core view/mmap borrow, Java/JNI/
   JPype dependency, or public native type exists.
