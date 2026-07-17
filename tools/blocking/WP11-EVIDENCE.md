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
Predicate categories are derived from `ClauseProgram` kinds rather than guessed from
integer IDs. The projection digest sorts logical facts and is therefore independent
of assertion insertion order.

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
- Rollback-safe manager internals: cache-block markers, earliest-dirty state,
  validation digests, rejected blocker pairs, and deterministic transition events are
  restored together with tableau facts and node assignments. Diagnostic traces have
  an explicit configurable event bound and never affect logical assignments.
- A bounded, thread-safe exact-signature LRU namespaced by ontology, vocabulary,
  checker, core mode, and configuration. Promotion is restricted to completed SAT
  models without nominals, additional/query-local axioms, aborts, or validated core
  blocking; eviction can only affect performance.
- Validated blocking's stable enumeration, rejection, rollback-safe core promotion,
  rescheduling, saturation fixed-point loop, cancellation polling, and the hard
  no-SAT-before-validation gate.
- `CompiledClauseBlockingValidator`, which consumes immutable `ClauseProgram` records
  and validates both pinned directions: copying a blocker into the blocked node's
  parent/edge context, and mirroring blocked successors while checking their parent's
  clauses and at-least obligations. Equality, annotated equality, role direction,
  global Z matches, deterministic repair selection, and bounded joins are covered.
  Its fact and blocker indexes are built at most once per manager validation pass,
  rather than once per provisional block, and are always released on success,
  rejection, cancellation, or failure.
- Conservative fallback for non-HT compiled clause shapes: a provisional block is
  rejected and expansion resumes. Unsupported validation can therefore cost time but
  cannot manufacture SAT.

`BlockingValidator` remains the minimal structural protocol, so custom validators are
still accepted. `CompiledClauseBlockingValidator` adds an optional cancellable method
and a pass-aware snapshot lifecycle that the manager detects without breaking the
original protocol.

## Frozen WPR2 fixture

| Artifact | SHA-256 |
|---|---|
| vocabulary fingerprint | `afef482dafc98b2e6ba3609daffe8b3454aebd38e5e7e920979c8e4515c4f9fe` |
| relevant state projection | `7a3e473b7645ea487009830e281bd4841bf7397cf81cf4ca08a155de57bf3871` |
| blocked-node pairwise signature | `ca28b8412213a75045055e07b19a54add4e1cf86f1b1b4e61001d3696842cfb5` |
| canonical manager snapshot | `0d5d6e6812947622116f8f0ac34fc3ded80192077dd869517819457f83230e90` |
| canonical transition trace | `39dfcc2ffa3d8ee2739faaf26b6214e058aa098848f3f044a8989670f8ccebf4` |

The fixture fixes node creation order, concept/forward/inverse edge labels, selected
blocker, manager/checker/core mode, and logical blocking state. Hash equality is never
used as semantic equality by the runtime.

## Verification

- CPython 3.10: `92 passed` across blocking and tableau-state tests.
- CPython 3.12: `92 passed` across the same tests.
- Focused blocking suite: `50 passed` on each interpreter.
- Random mutation/backtrack comparison: 20 deterministic seeds × 150 operations =
  3,000 steps. Announced and deliberately unannounced concept/role/core changes and
  LIFO rollbacks agree with full recomputation after every step.
- Scale fixture: 5,000 equal-signature tree nodes in one anywhere-blocking bucket;
  exactly one stable blocker is selected and the pass visits each node once.
- Curated checks cover nonancestor anywhere blocking, ancestor contrast,
  single/pairwise divergence, validated projections, cache gates and eviction,
  merge/prune rollback, invalid-block repair/fixed point, cancellation after repair,
  pinned parent/blocker validation shapes, at-least and annotated-equality failures,
  pass-aware lifecycle cleanup, resource and trace bounds, and SAT gating.
- Ruff lint/format passes for WP11 runtime and tests; strict mypy passes for all 14
  WP11 runtime/test modules.
- The runtime and ordinary tests do not invoke Java, JNI, JPype, a native compiler,
  the network, or the quarantined reference oracle.

## Integration boundary

WP12 constructs the vocabulary, plan, checker, manager, and compiled validator, then
calls `compute()` before existential expansion and `validate_to_fixed_point()` at
apparent saturation. No scheduler/export changes are included in WP11's bounded
ownership.

`BlockingRequirements.from_program(program)` consumes source-level expressivity, so
forward-only ontologies select single blocking while explicit inverse-role use selects
pairwise blocking. Callers can still provide explicit overrides for specialized
embedding scenarios.
