# WP11 — Pure-Python blocking

**Goal**: implement sound single/pairwise ancestor/anywhere blocking, signature caching,
and validated core blocking against the shared Python state.

## Read first

| What | Where |
|---|---|
| Full blocking contract | `blocking.md` |
| Expansion/state interaction | `hypertableau.md` §10; `tableau-state.md` §§2, 8–9 |
| Java behavior | all pinned `blocking/*`; `Reasoner.createTableau` strategy selection |
| Formal justification | Hypertableau paper blocking/core sections |

## Deliverables

- Eligible/direct/indirect blocking lifecycle and canonical label extraction.
- Single, pairwise, validated-single, and validated-pairwise direct checkers with stable
  debug signatures.
- Ancestor, anywhere, and anywhere-validated managers; deterministic candidate index,
  earliest-change recomputation, descendant invalidation/rescheduling.
- Safe bounded signature cache keyed by ontology/config and disabled for invalid
  expressivity/query/cancellation cases.
- Full validation/core promotion loop and rollback-safe blocking/cache state.
- Full-recompute reference implementation and mutation/backtrack property tests.

## Depends on

WP08. Coordinate expansion hooks with WP10/WP12; WP11 owns blocking algorithms.

## Acceptance criteria

1. Auto strategy selects single without inverses, pairwise with inverses, anywhere by
   default, and cache only under pinned soundness conditions.
2. Every relevant node/parent/edge/core/merge/prune/backtrack mutation invalidates stale
   blocks; incremental state equals full recomputation.
3. Anywhere finds legal nonancestor blockers; pairwise rejects false single-label
   matches; indirect unblocking reschedules exact pending work.
4. Provisional validated blocks cannot produce SAT until every block passes; invalid
   blocks/core promotions resume saturation and roll back safely.
5. Upstream validator/known-failure observations become semantic regressions, not skips.
6. All strategy/cache on/off combinations give identical generated and curated answers
   and deterministic WPR2 signature traces.

