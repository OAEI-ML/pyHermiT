# WP11 evidence — pure-Python blocking

Date: 2026-07-17

## Source and semantic scope

The implementation was reviewed against every class in the pinned HermiT
`blocking` package at commit
`37ec30aced32ac81ebecc5e33fad255ddefcb4c3`: `AncestorBlocking`,
`AnywhereBlocking`, `AnywhereValidatedBlocking`, `BlockingSignature`,
`BlockingSignatureCache`, `BlockingStrategy`, `BlockingValidator`,
`DirectBlockingChecker`, `PairWiseDirectBlockingChecker`, `SetFactory`,
`SingleDirectBlockingChecker`, `ValidatedPairwiseDirectBlockingChecker`, and
`ValidatedSingleDirectBlockingChecker`. Strategy construction was also checked
against `Reasoner.createTableau` at that commit.

The runtime is a Python-native port rather than a translation of HermiT's mutable
Java caches. It extracts one immutable, canonical projection of relevant concept,
parent, edge, and core labels per pass; compares exact tuples after indexed lookup;
and falls back to full recomputation whenever a precise notification was missed.
Predicate categories are supplied explicitly by the compiled-IR owner and are never
guessed from integer IDs.

## Delivered behavior

- Single, pairwise, validated-single, and validated-pairwise direct checkers with
  exact set semantics and stable binary/debug signatures.
- Deterministic ancestor, anywhere, and validated-anywhere plans, with automatic
  single/pairwise selection from inverse-role requirements.
- Stable creation-order candidate selection, direct and indirect blocking,
  descendant unblocking/rescheduling, earliest-dirty tracking, and a full-recompute
  reference implementation.
- Generation-safe handling of merge, prune, and rollback. Merge/prune clear all live
  references to affected blockers atomically and restore them through the shared
  trail.
- A bounded, thread-safe exact-signature LRU namespaced by ontology, vocabulary,
  checker, core mode, and configuration. Promotion is restricted to completed SAT
  models without nominals, additional/query-local axioms, aborts, or validated core
  blocking; eviction can only affect performance.
- Validated blocking's stable enumeration, rejection, rollback-safe core promotion,
  rescheduling, saturation fixed-point loop, cancellation polling, and the hard
  no-SAT-before-validation gate.

`BlockingValidator` is deliberately a narrow runtime protocol in this checkpoint.
WP06/WP09 own its compiled-clause implementation because WP11 depends only on WP08;
WP11 owns and tests all validation lifecycle behavior around that protocol.

## Frozen WPR2 fixture

| Artifact | SHA-256 |
|---|---|
| vocabulary fingerprint | `afef482dafc98b2e6ba3609daffe8b3454aebd38e5e7e920979c8e4515c4f9fe` |
| relevant state projection | `0207689b9aee994891e37af9d94ce124de6d22e902158b9a59271a7ae2c5c271` |
| blocked-node pairwise signature | `ca28b8412213a75045055e07b19a54add4e1cf86f1b1b4e61001d3696842cfb5` |
| canonical manager snapshot | `70af0ffc2cf93f840453fbccf51f8877928d6f382416cedce3da0856cab18498` |

The fixture fixes node creation order, concept/forward/inverse edge labels, selected
blocker, manager/checker/core mode, and logical blocking state. Hash equality is never
used as semantic equality by the runtime.

## Verification

- CPython 3.10.11: `75 passed` across blocking and tableau-state tests.
- CPython 3.12.3: `75 passed` across the same tests.
- Repository-wide, each interpreter: `146 passed; 4 subtests passed`.
- Random mutation/backtrack comparison: 20 deterministic seeds × 150 operations =
  3,000 steps. Announced and deliberately unannounced concept/role/core changes and
  LIFO rollbacks agree with full recomputation after every step.
- Curated checks cover nonancestor anywhere blocking, ancestor contrast,
  single/pairwise divergence, validated projections, cache gates and eviction,
  merge/prune rollback, invalid-block repair/fixed point, cancellation, and SAT
  gating.
- Ruff lint/format passes for WP11 runtime and tests; strict mypy passes for all 24
  Python backend source files.
- The runtime and ordinary tests do not invoke Java, JNI, JPype, a native compiler,
  the network, or the quarantined reference oracle.
