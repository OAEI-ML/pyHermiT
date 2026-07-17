# WP08 evidence — Python tableau state

Date: 2026-07-17

## Delivered substrate

- Immutable bitset dependency sets with bounded per-session interning/compaction.
- One strict-LIFO trail and checkpoints covering node, fact/support, index, delta,
  queue, disjunction, clash, merge, prune, blocking, and existential mutations.
- Generation-safe node arena with explicit kind/sort/lifecycle, representatives,
  merge dependencies, tree metadata, named-individual guard, and stale-handle checks.
- Unique fact rows with nondominated support alternatives, total/old/new generations,
  on-demand exact indexes, canonical binding lookup, and merge rewrites.
- Deterministic duplicate-guarded queues, ground-disjunction records, one-clash
  selection, branch/backjump primitives, operation-root cancellation recovery, and
  whole-session invariant/canonical-snapshot checks.
- State mechanics for deterministic representative selection and subtree pruning. No
  hypertableau rule interpretation was added; WP09/WP10 retain semantic ownership.
- Canonical language-neutral state trace v1 and Python runner for WPR0.

## Frozen parity fixture

| Artifact | Value |
|---|---|
| Trace | `tests/data/state/trace-v1.json` |
| Operations/snapshots | 14 |
| Canonical trace SHA-256 | `501e99b619d88567fe22dfc155f9929e2f980c6ddccdb052c529f17bf479690f` |
| Newline-joined snapshot SHA-256 | `c50db3510ac32b605741731e54ef8fc7ca5a98926e47b607e29a107f21fc8196` |
| Snapshot bytes (excluding separators) | 19,373 |

The fixture includes roots/named guards, facts, delta-neutral setup, a ground-
disjunction branch, tree-node creation, branch-supported binary fact/provenance,
existential queue/mark, disjunction, clash, backtrack/alternative advance, fact-copying
merge, and invariant check.

## Verification

- CPython 3.10.11: `42 passed` in `tests/unit/tableau_state`.
- CPython 3.12.3: `42 passed` in `tests/unit/tableau_state`.
- Random persistent-reference store comparison: 24 deterministic seeds × 180
  operations = 4,320 mutation steps, with full index/dependency/delta invariants after
  every step and every rollback.
- Hypothesis dependency-set algebra and focused exact-rollback tests cover retire/slot
  reuse, stale handles, merge chains, multiple supports, index reconstruction, delta
  partitions, every session component, cancellation, and deterministic queue order.
- Ruff lint/format passes for all WP08 runtime/tests.
- Strict mypy passes for all 10 pure-Python backend source files.
- No Java, JNI, JPype, native compiler, network, or oracle is imported or invoked by
  this runtime/test layer.

The repository-wide suite was also run during implementation. Its only HermiT failures
were the pre-existing WP01 mock `OntologyView` falling behind the concurrently changing
local pyowl-core WP04 runtime protocol; WP08's isolated tests remained green. The full
cross-package suite is rerun when that dependency checkpoint is committed, before the
WP01 compatibility checkpoint is finalized.
