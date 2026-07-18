# WPR4 native session lifecycle and scheduler evidence

This isolated tranche supplies the Python-independent transaction boundary and exact
phase driver for a future complete native backend session. It intentionally does not
advertise `full_reasoner`, change `auto` selection, decode query/result wire payloads,
or introduce a Python semantic callback. The concrete WPR1-WPR3 tableau adapter remains
typed and mandatory rather than being approximated in this module.

## Exact scheduler contract

`drive_tableau` owns the complete fixed-point order shared with the Python tableau:

1. poll cancellation/resource state and account one bounded scheduler step;
2. process nominal-introduction work before any delta;
3. promote exactly one delta generation and run native rule/role consequences;
4. check dirty datatype components after every promoted delta, then revisit nominals;
5. when no delta remains, check datatypes again and continue if their state changed;
6. refresh blocking before an existential candidate, then process one existential;
7. process one deterministic ground-disjunction action;
8. resolve an installed clash through UNSAT or backtrack, invalidating derived datatype
   and blocking certificates after a successful backtrack;
9. run validated-blocking model validation and continue when it invalidates a block; and
10. return SAT only when the adapter proves no pending/unvalidated work and all component
    invariants pass.

An adapter that reports a datatype clash without installing the corresponding tableau
clash, reports consequences without a promoted delta row, or reaches the model boundary
with pending work fails with a typed invariant error. Diagnostic counters use checked
arithmetic within an operation and deterministic saturating aggregation only after the
operation commits.

## Permanent/query transaction boundary

`SessionScheduler` owns one permanent kernel behind an `Arc`, a nonblocking same-session
busy guard, a mutex-protected owned state, permanent consistency cache, deterministic
statistics, and a bounded event queue. Every uncached check has one adapter checkpoint.

- A successful permanent check atomically promotes its completed state and publishes its
  cache only after the final poll, invariant check, and adapter commit succeed.
- Every successful query restores the permanent root before its result becomes visible.
- `check_many` runs queries in input order with a distinct checkpoint/rollback per item.
  Results, cumulative statistics, and item-completion events publish only after the whole
  batch and its final cancellation poll succeed; an error never returns or records a
  prefix.
- A known-inconsistent permanent ontology answers additive query checks from the sound
  permanent UNSAT cache without tableau mutation, while still polling cancellation.
- `reset_query_state` is uninterruptible, idempotently restores the committed permanent
  root, and preserves valid permanent caches. A failed reset poisons the session.

Cancellation, timeout, resource, and malformed-query failures roll the full adapter
checkpoint back and revalidate it. An invariant error poisons the session even when
rollback succeeds. Failure to roll back, commit, or re-establish invariants returns a
stable poisoned error and permits only `close`. Rust panics are contained inside the
owned-state lock without poisoning the mutex; the session is then explicitly poisoned.

## Lifecycle, events, and resource behavior

- Closed state, creating-process identity, poison, and busy state are checked before the
  kernel is touched. Close is idempotent, rejects concurrent activity and inherited
  post-fork use, remains available for a poisoned session, and contains destructor panic.
- Independent schedulers have no shared busy state. Clones of one scheduler share the same
  lifecycle atomics and owned kernel safely; no unsafe Rust is used.
- Event version, sequence, operation ID, operation kind, completion position, query hash,
  result flag, and stable error code are immutable and deterministic. Queue overflow drops
  the oldest record deterministically and counts drops. The PyO3 adapter must attach the
  required monotonic elapsed time when draining records on the initiating Python thread;
  elapsed time is intentionally not allowed to influence native scheduling or hashes.
- Positive limits bound scheduler steps, batch item count, staged batch-result bytes, and
  event capacity. Major kernel/staging memory is observed before allocation or mutation.

## Required concrete adapter integration

The public `NativeTableau` contract is deliberately stronger than any one current native
component. Its `OperationCheckpoint` must cover, as one logical transaction:

1. `TableauKernel` state, branches, queues, operation root, and generation-checked handles;
2. mutable `RuleEngine` atom/disjunction interning and any query-overlay rule plan;
3. `NominalIntroductionManager` roots, branch contexts, and trace position;
4. `BlockingManager` assignments, projection, validation digest, rejected blocks, cache,
   invalidation frontier, and trace;
5. the public WPR3 `DatatypeScheduler` checkpoint, including dirty components and semantic
   solver certificates; and
6. all operation-local service/model caches that can affect a later answer.

`RoleRuntime` and compiled permanent IR may be shared because they are immutable. Query
installation must validate the permanent fingerprint plus symbol/predicate prefix before
adding rows or datatype constraints. The adapter must call the public WPR3 semantic solver
through `check_datatypes`; it must not duplicate datatype projection/solving or use
`AssertedOnlyDatatypes` as a fallback.

Two current components require an explicit integration decision rather than an unsafe
assumption: `RuleEngine` has no complete operation checkpoint for mutable interning, so the
adapter must add one or keep the extended query engine wholly operation-local; and the
native cancellation object must gain per-public-operation deadline/interruption/memory
reset equivalent to Python `CancellationSource.begin_operation`. The existing PyO3
`SessionControl`/`SessionOwned` must delegate to this coordinator instead of nesting a
second busy/lifecycle lock.

## Focused verification

Ten isolated Rust tests cover:

- permanent consistency caching and query/batch rollback to one committed root;
- cancellation injected at every coordinator poll, followed by healthy session reuse;
- memory rejection and scheduler-step exhaustion before partial publication;
- failed middle batch items with no returned/statistical/event prefix;
- malformed-query recovery and poisoning on invariant, commit, or rollback failure;
- same-session exclusion, close-while-busy rejection, and independent-session progress;
- creating-process mismatch, reset success/failure, panic containment, idempotent close,
  shared-clone disposal, and post-close rejection;
- byte-identical deterministic event/statistic sequences and bounded drop-oldest behavior;
- batch item/byte limits and observable empty-batch lifecycle; and
- exact hostile phase ordering through nominal, delta, datatype, blocking, existential,
  disjunction, backtrack, invalid validation, and final validated SAT, plus rejection of an
  unready SAT boundary.

An isolated no-dependency harness on Rust 1.97.1 passes all 10 tests, `rustfmt --check`,
and the crate-equivalent strict Clippy policy (`all`, `pedantic`, `nursery`,
`unwrap_used`, `expect_used`, and `panic` denied, with warnings denied). The source uses no
post-1.83 API; the repository MSRV lane remains an integrated CI gate after module export.

Artifact SHA-256 digests at capture time:

| artifact | SHA-256 |
|---|---|
| `native/src/session.rs` | `2851ecbc84d9b3a9243fdab433ac7f67b59153839df6803831785077fd857d09` |
| `native/src/session_tests.rs` | `d21cff3dce4831d5ba04e92b662c4fb9a1d77a2852806b286dcd20d77c95045d` |

## Reproduction after shared export

```text
cargo fmt --manifest-path native/Cargo.toml -- --check
cargo test --manifest-path native/Cargo.toml session_tests
cargo clippy --manifest-path native/Cargo.toml --lib --tests -- -D warnings
```
