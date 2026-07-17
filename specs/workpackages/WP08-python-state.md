# WP08 — Pure-Python tableau state, indexes, and rollback

**Goal**: provide the readable, invariant-checked mutable substrate used by all Python
rule agents and mirrored by Rust.

## Read first

| What | Where |
|---|---|
| Nodes, rows, deltas, dependencies, trail, merge invariants | `tableau-state.md` |
| Predicate/term contracts | `contracts.md` §3; `normalization-clausification.md` §4 |
| Java behavior | pinned `Node`, `ExtensionManager/Table`, `TupleIndex/Table`, `DependencySet*`, `BranchingPoint` |
| Rust trace consumer | `native-backend.md` §§3, 8 |

## Deliverables

- Node arenas/handles/lifecycle, fact rows, unique extension tables, total/old/new delta
  views, indexed retrieval patterns, core flags, supports/dependency sets.
- Unified checkpoints/trail covering nodes, rows/supports, indexes, queues, clashes,
  disjunction records, and component extension hooks.
- Branching-point primitives, rollback/backjump substrate, operation-root reset, and
  cancellation-safe state recovery.
- Equality/representative and merge/prune **state mechanics** (semantic direction and
  assertion-copy scheduling are completed by WP10).
- Ground-disjunction/clash records and deterministic work queues.
- Expensive invariant checker, canonical debug snapshot, persistent slow reference
  model, and randomized operation-state machine tests.

## Depends on

WP01. Use contract predicate records; do not invent a second IR while WP06 proceeds.

## Acceptance criteria

1. Exact index reconstruction, delta partitions, handle generations, dependency levels,
   queue membership, and lifecycle invariants pass after every generated operation.
2. Backtracking from every mutation point restores canonical logical state exactly,
   including multiple supports where only one branch is removed.
3. Slot reuse cannot make a stale handle valid; active rows never expose retired/pruned
   nodes incorrectly.
4. Empty/deterministic dependencies, subset support replacement, branch-level union,
   and dead-set cleanup match a slow reference.
5. Serialized operation traces are stable for WPR0; no object-address/hash-order data.
6. State modules contain no logical handler that guesses an unmerged rule's semantics.

