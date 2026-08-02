# Changelog

All notable user-visible changes are recorded here.

## 0.2.0 — 2026-08-02

- Migrated the shared ontology contract to `pyowl-core>=0.2,<0.3`, API 0.2,
  model schema 2, and wire format 1.2.
- Added native compilation from encoded structural-view schema 2 for snapshots,
  overlays, and composites while retaining the complete scalar Python and native-wire
  compatibility paths.
- Made encoded descriptor, fingerprint, and producer-version checks fail closed, with
  deterministic diagnostics and exact scalar/encoded compiler parity coverage.
- Invalidated pyowl-core 0.1 model, encoded-view, and persisted-cache identities. Users
  must regenerate persisted snapshot bytes and consumer caches before using 0.2.0.

## 0.1.2 — 2026-07-30

- Completed the fail-closed eight-platform native wheel matrix while retaining the
  compiler-free universal wheel and sdist fallback.
- Added tag-bound trusted PyPI publishing for the verified, attested ten-file
  distribution set.
- Hardened reproducible native builds, cross-platform artifact inspection, and
  pyowl-core backend compatibility checks.

## 0.1.1 — 2026-07-30

- Corrected the README quick start to call the public `Reasoner.class_hierarchy()`
  method and added an executable release regression test for the documented example.

## 0.1.0 — 2026-07-30

- Added a Java-free OWL 2 DL facade over immutable `pyowl-core` snapshots, overlays,
  composites, and one-call providers, with no repeated public-model parsing.
- Implemented complete Python and optional Rust reasoning sessions covering
  consistency, entailment, class/object/data-property classification, realization,
  buffered updates, cancellation, and resource limits.
- Added explicit `python`, `native`, `auto`, and exact `verify` modes. Explicit native
  selection is fail-closed; semantic failures never fall back silently.
- Added immutable public compiler/ingestion diagnostics and import-light compiler-cache,
  compiled-IR, and native-ABI schema constants for cache and provenance consumers; the public
  compiler digest is canonical across backend and ingestion-path selection, and the latest
  successful consumer compilation duration is measured independently of core loading.
- Added deterministic normalization/private IR, hyperresolution, branching and
  backjumping, equality/nominal/cardinality handling, existential blocking, role
  automata, and datatype semantics with Python/native parity evidence.
- Added compiler-free universal fallback builds and `cp310-abi3` native packaging for
  Python 3.10 and 3.12, artifact/SBOM inspection, and hosted eight-target workflows.
- Added WP17 user/developer guides, machine-readable release and coverage reports,
  hash-bound benchmark schemas/workloads, and fail-closed provisional performance
  targets.

The owner accepted the licensed W3C run, larger live reference sample, hosted native
matrix, and dedicated calibration as post-release follow-up. `LIC-001` is waived as-is
for this release without claiming legal review; see the explicit owner override under
`reports/release/`. Java remains limited to the opt-in development comparison lane and
is absent from runtime artifacts.
