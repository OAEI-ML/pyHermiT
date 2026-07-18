# WPR4 native rule-engine transaction evidence

This isolated prerequisite closes the mutable-rule-state hole identified by the WPR4
session scheduler. It does not advertise `full_reasoner`, change backend selection, or
clone/store a `TableauKernel` inside `RuleEngine`.

## Ownership and snapshot boundary

`RuleEngineCheckpoint` is an opaque one-shot token containing a process-local engine
owner identity and a monotonic sequence. A checkpoint captures complete clones of every
mutable reasoning owner in `RuleEngine`:

1. `atom_ids`;
2. `atoms`;
3. `disjunction_keys`; and
4. `initialized`.

The rule program, compiled join program, source/data node maps, brancher configuration,
merging metadata, and rule limits are immutable after construction and therefore are not
copied. The full maps/vectors are captured rather than append lengths, so rollback also
restores replacement, removal, and stale-disjunction cleanup exactly.

Checkpoint creation validates the atom map/vector bijection, polls cancellation before
and after allocation, and publishes no token or registry mutation on failure. Positive
`RuleCheckpointLimits` bound both active checkpoint count and a conservative charged byte
estimate. The estimate accounts for every cloned map entry, vector element, nested atom
argument allocation, allocator allowance, and checkpoint-registry entry. Aggregate bytes
are checked and exposed for diagnostics.

## Rollback and integration contract

The public integration surface re-exported from `rules` is:

- `RuleCheckpointLimits::new(max_checkpoints, max_total_checkpoint_bytes)`;
- `RuleEngine::with_limits_and_checkpoint_limits(...)`;
- `RuleEngine::checkpoint(&CancellationState)`;
- `RuleEngine::rollback(RuleEngineCheckpoint)` for engine-only owners;
- `RuleEngine::rollback_with_kernel(&mut TableauKernel, TableauKernel,
  RuleEngineCheckpoint)` for the WPR4 operation boundary;
- `RuleEngine::release_checkpoint(RuleEngineCheckpoint)`; and
- bounded-state diagnostics (`checkpoint_count`, `checkpoint_bytes`,
  `interned_atom_count`, and `disjunction_key_count`).

The future session adapter must clone/capture its `TableauKernel` at the same boundary at
which it calls `RuleEngine::checkpoint`; `RuleEngine` deliberately does not own or clone
that kernel. On failure, the adapter passes the captured kernel value to
`rollback_with_kernel`. This method validates token ownership/liveness, checkpoint
registry accounting, the saved atom bijection, and saved kernel invariants before either
live owner changes. The subsequent engine restore and `TableauKernel` full restore are
infallible moves, so a precondition failure leaves both live owners unchanged.

Rollback consumes the selected token and invalidates every newer token because those
snapshots belong to an abandoned lineage. Release consumes only the selected token.
Foreign, released, rolled-back, and repeated tokens fail closed. Sequence numbers never
roll back, so deterministic logical identifiers are restored without token reuse.

The outer `SessionScheduler` remains responsible for fork rejection and poisoning when a
larger composite rollback fails. Its operation checkpoint should pair these two values:

```text
kernel: TableauKernel
rules:  RuleEngineCheckpoint
```

Other mutable WPR4 owners (nominals, blocking, datatypes, and service/model caches) remain
separate entries in that composite checkpoint.

## Focused verification

The focused native rule-engine suite passes 12/12 tests. Four hostile transaction tests
cover:

- byte-identical paired kernel restoration plus exact restoration of all four rule-engine
  owners after destructive, non-append mutations;
- foreign-token rejection without changing either live owner, one-shot reuse rejection,
  release rejection, and invalidation of newer checkpoints after older rollback;
- atomic cancellation, byte-budget, and count-budget failures with no partial checkpoint;
  and
- deterministic repeated disjunction interning and kernel snapshots across rollback.

Commands/results captured on Rust 1.97.1:

```text
cargo check --manifest-path native/Cargo.toml --lib
# passed before an unrelated concurrent services refactor was exported

cargo test --manifest-path native/Cargo.toml --lib rules::engine::tests
# 12 passed; 0 failed; 155 filtered out

rustfmt --edition 2021 --check native/src/rules/engine.rs native/src/rules/mod.rs
git diff --check -- native/src/rules/engine.rs native/src/rules/mod.rs
# passed
```

The integrated strict Clippy command was attempted but could not reach linting because a
concurrent uncommitted classifier tranche did not compile (`build_complete_hierarchy`
and new `known_complete` initializers were incomplete). The root integrator owns the
unified Clippy/full-suite gate after that independent tranche compiles; no services file
was modified here.

Artifact SHA-256 digests at capture time:

| artifact | SHA-256 |
|---|---|
| `native/src/rules/engine.rs` | `42a2ff455216b0618b9f10e2d92f9acda6f1e8e1b60fad2886d706439747693a` |
| `native/src/rules/mod.rs` | `5e6fc1446e1969aefee417c80a6c8b949feb6289db6456f46b4ce0949d49ebbe` |
