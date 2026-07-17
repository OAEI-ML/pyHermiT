# WPR2 — Rust merging, existentials, NI, and blocking

**Goal**: complete the native object-domain/cardinality/termination rules with exact
Python semantics and rollback.

## Read first

| What | Where |
|---|---|
| Merge/expansion/NI rules | `hypertableau.md` §§6–8, 10 |
| Blocking complete contract | `blocking.md` |
| State/rollback | `tableau-state.md` §§2, 5–6, 8–10 |
| Python semantics | WP10 and WP11 implementations/tests/traces |
| Java behavior | pinned merging/existential/nominal managers, `existentials/*`, `blocking/*` |

## Deliverables

- Native deterministic merge/copy/prune/unmerge, canonical distinct successor
  counting, min/max/exact consequences, creation-order and individual-reuse expansion.
- Full annotated-equality/NI key/root/level processing and rollback.
- Native single/pairwise direct checkers, ancestor/anywhere maintenance, direct/indirect
  blocking, signature cache, validated/core validation and invalidation/rescheduling.
- Exact replay of WP10/WP11 state/signature/strategy traces and generated interaction
  differentials; cancellation/resource safety at expansion/validation boundaries.
- Criterion profiles for merge/index copying, witnesses, NI, signatures, cache, and
  full-recompute versus incremental blocking.

## Depends on

WP10, WP11, WPR0, and WPR1.

## Acceptance criteria

1. All merge/cardinality/existential/NI state and semantic traces match Python exactly,
   including dependencies and rollback after every mutation category.
2. All blocking strategies/cache modes agree with Python full recomputation and return
   identical logical answers on cyclic/inverse/nominal/cardinality/role cases.
3. SAT cannot be returned with an unchecked invalid provisional block; unblocking
   reschedules each exposed obligation exactly once.
4. No stale arena handle/cache/index survives merge/prune/backtrack/cancel; invariant,
   sanitizer, fuzz, and leak lanes remain clean.
5. Strategy alternatives and internal hashes never affect canonical public results.
6. Hot operations remain within stored baseline and cross no fine-grained PyO3 calls.

