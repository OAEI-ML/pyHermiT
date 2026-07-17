# WPR1 — Rust hyperresolution and branching

**Goal**: implement the complete native Hyp-rule, delta, clash, disjunction, dependency,
and backjump engine with exact Python transition parity.

## Read first

| What | Where |
|---|---|
| Logical rules | `hypertableau.md` §§3–5, 9 |
| Native safety/boundary | `native-backend.md` §§3–8 |
| Python source of semantics | WP09 implementation/tests/traces |
| Java hot-kernel behavior | pinned `HyperresolutionManager`, `DLClauseEvaluator`, extension/branch classes |

## Deliverables

- Rust compiled join plans/indexed semi-naive evaluation for all body predicate/guard
  forms and explicit head dispatch.
- Delta promotion, facts/supports, ground-disjunction canonicalization/order, clash
  creation, branch checkpoints, choice advancement, learning, nonchronological
  backjump/exhaustion.
- Cancellation/resource checks in joins/branch work and operation-root recovery.
- Python/Rust state-transition differential runner for every WP09 curated/generated
  trace; naive Rust/Python join comparison on bounded cases.
- Criterion benchmarks for joins, indexes, delta throughput, dependency union, branch
  rollback; profiles/counters compatible with performance spec.

## Depends on

WP09 and WPR0.

## Acceptance criteria

1. Every WP09 trace and generated clause/state case matches exact heads, supports,
   disjunctions, clashes, checkpoints, and restored snapshots.
2. No per-fact/rule callback crosses PyO3; one coarse session request runs detached.
3. Learning on/off, deterministic/empty/unit/duplicate/satisfied disjunctions, and
   multi-level backjumps return identical semantics and correct dependencies.
4. Malformed IR/state limits/cancellation produce typed errors without panic/leak/
   partial committed state.
5. Sanitizers/fuzz/property tests and benchmark baselines pass with no unsafe code.
6. Native feature manifest still remains incomplete until WPR2/WPR3/WPR4 land.

