# WP09 — Python hyperresolution, clashes, and branching

**Goal**: implement complete indexed Hyp-rule evaluation and dependency-directed
nondeterminism on the Python state.

## Read first

| What | Where |
|---|---|
| Scheduler/Hyp/disjunction/clash rules | `hypertableau.md` §§3–5, 9 |
| Store/dependency requirements | `tableau-state.md` §§3–5, 7–8 |
| Java behavior | pinned `HyperresolutionManager`, `DLClauseEvaluator`, `GroundDisjunction*`, `DisjunctionBranchingPoint`, `ClashManager` |
| Clause join metadata | `normalization-clausification.md` §4 |

## Deliverables

- Clause join-plan compiler/executor using one designated delta atom and indexed
  active/canonical tuple retrieval, sorts, repeated variables, guards, and negative
  predicates.
- Exhaustive head dispatcher for deterministic facts, roles, equality requests,
  inequalities, at-least obligations, annotated equalities, disjunctions, and clashes.
- Ground-disjunction dedup/satisfaction/order/queue and branch choice advancement.
- Dependency union, clash support, nonchronological backjump, exhausted-choice
  propagation, and disjunction learning on/off.
- Naive substitution/chronological search oracle plus targeted and generated tests.

## Depends on

WP06 and WP08.

## Acceptance criteria

1. Indexed and naive join enumeration derive identical heads/dependencies over
   generated small clauses/states; all-old matches are not repeated indefinitely.
2. Every predicate head kind is handled explicitly and wrong sorts/inactive tuples are
   rejected/skipped according to contract.
3. Duplicate/satisfied/unit/empty disjunctions, deterministic clashes, learning on/off,
   and multi-level backjumps have exact state/result tests.
4. A clash dependency omits no necessary branch and never names a future/nonexistent
   level.
5. Cancellation during long joins/branch transitions restores the operation root or
   marks state unusable explicitly.
6. Upstream DL-clause/dependency/disjunction semantic cases and WPR1 trace fixtures pass.

