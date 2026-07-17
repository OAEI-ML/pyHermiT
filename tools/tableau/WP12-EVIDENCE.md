# WP12 evidence — complete pure-Python tableau session

Date: 2026-07-17

## Delivered integration

- A complete phase scheduler joins compiled ground initialization, hyperresolution
  delta generations, exact datatype components, nominal introduction, equality
  merging, existential expansion, disjunction branching, dependency-directed
  backjumping, blocking, and validated-block repair.
- Ordinary and annotated equalities use the semantic merge manager, including
  deterministic representative orientation, inequality clashes, subtree pruning,
  incident-row redispatch, and cancellation propagation.
- The scheduler computes blocking before selecting an existential candidate. At
  apparent saturation, validated blocking performs one deterministic validation
  pass; an invalid pass repairs/reschedules state and returns to the complete outer
  phase loop. Repeating this loop is the scheduler-level equivalent of
  `validate_to_fixed_point`, while ensuring NI, datatype, existential, and
  disjunction work—not only hyperresolution—is exhausted between passes. SAT also
  requires `ready_for_sat()`.
- Source expressivity now distinguishes explicit `ObjectInverseOf` use from the role
  model's internal inverse closure. Forward-only ontologies select single blocking;
  explicit inverse usage selects pairwise blocking.
- Exact datatype projection covers positive/negative range constraints, fixed
  literal identities, inequalities, disconnected components, semantic clashes,
  rollback invalidation, cancellation, and n-ary witness relations. Ontologies with
  no datatype usage take a constant-time fast path.
- Every backend `check` owns a fresh tableau. Permanent compiled bytes and the
  ontology fingerprint remain unchanged after SAT, UNSAT, branching, query batches,
  rebuild-required overlays, and interruption.
- Query overlays are prefix-checked and merged deterministically with permanent IR.
  Clauses, facts, disjunctions, disjunct provenance, and provenance tables are
  de-duplicated and assigned fresh dense canonical IDs without copying or reparsing
  OWL source. A query that genuinely changes the compilation strategy is rejected at
  the explicit full-rebuild boundary rather than partially executed.
- The concrete `BackendFactory`/`BackendSession` support consistency checks,
  independent ordered batches, progress events, reset, idempotent close, conservative
  delta rebuild outcomes, and typed statistics. WP13–WP15 service methods retain
  explicit work-package markers until their implementations replace them.
- Cancellation rollback streams active rows, polls during ontology-scale scans, and
  avoids release-mode whole-ontology invariant/arena compaction on the abort path.
  The exact trail restores the operation root; debug invariants can be checked
  afterward and are covered by tests.

## Semantic coverage

Integrated tests cover empty and Horn fixed points, positive/negative clashes,
cyclic existential termination, creation-order versus individual-reuse parity,
single/pairwise selection, ancestor/anywhere/validated strategy parity, datatype
membership, maximum/minimum cardinalities, NI, role chains, universals, same/different
individuals, keys, nominals, exhausted disjunctions, branch backtracking, and
permanent/query isolation—including a branch-heavy UNSAT query followed by a clean
permanent SAT check.

## Verification

- CPython 3.10: `630 passed` (`python -m pytest -q tests`).
- CPython 3.12: `630 passed` over the identical suite.
- Ruff: all project files clean.
- Strict mypy: no issues across `93` source files.
- Import contracts: `2 kept, 0 broken` across `89` analyzed runtime files and `588`
  dependencies.
- The complete runtime gate imports or invokes no Java, JNI, JPype, subprocess
  reasoner, network service, GPU runtime, or OpenRouter client. Java remains confined
  to the optional frozen-oracle development tooling.

## Reproducible scale probe

Command:

```text
python benchmarks/bench_wp12_tableau.py \
  --individuals 5000 --depth 4 --samples 2 \
  --cancellation-individuals 30000 --cancellation-timeout-ms 1
```

CPython 3.10 result on the local x86_64 macOS worker:

| Measure | Result |
|---|---:|
| source individuals | 5,000 |
| saturated active nodes | 5,000 |
| saturated facts | 35,000 |
| scheduler steps | 6 |
| median complete-tableau time | 4.856 s |
| p95 complete-tableau time | 4.926 s |
| source individuals/second | 1,029.6 |
| traced peak memory | 65,270,674 bytes |
| 30,000-individual cancellation elapsed | 1.171 ms |
| latency after 1 ms deadline | 0.171 ms |

The benchmark performs a warm-up, verifies one canonical saturated-state digest
across every measured sample, runs one separately traced memory sample, and verifies
that cancellation restores the initialized canonical operation-root snapshot. It
measures the correctness-first Python fallback; optional Rust service workpackages
own the accelerated scheduler and data structures.
