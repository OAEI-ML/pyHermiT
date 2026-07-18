# Changelog

All notable user-visible changes are recorded here. The project has not issued a stable
release; dates describe repository evidence, not package-index publication.

## 0.1.0.dev0 — unreleased

- Added a Java-free OWL 2 DL facade over immutable `pyowl-core` snapshots, overlays,
  composites, and one-call providers, with no repeated public-model parsing.
- Implemented complete Python and optional Rust reasoning sessions covering
  consistency, entailment, class/object/data-property classification, realization,
  buffered updates, cancellation, and resource limits.
- Added explicit `python`, `native`, `auto`, and exact `verify` modes. Explicit native
  selection is fail-closed; semantic failures never fall back silently.
- Added deterministic normalization/private IR, hyperresolution, branching and
  backjumping, equality/nominal/cardinality handling, existential blocking, role
  automata, and datatype semantics with Python/native parity evidence.
- Added compiler-free universal fallback builds and `cp310-abi3` native packaging for
  Python 3.10 and 3.12, artifact/SBOM inspection, and hosted eight-target workflows.
- Added WP17 user/developer guides, machine-readable release and coverage reports,
  hash-bound benchmark schemas/workloads, and fail-closed provisional performance
  targets.

Publication remains blocked pending the licensed 350-check W3C execution, larger live
reference sample, hosted platform/sanitizer results, dedicated performance calibration,
and the remaining `LIC-001` owner/legal signoff. The four repository-owned provenance,
header, package/source, and artifact audits are complete but do not provide legal approval.
Java is permitted only in the opt-in development comparison lane and is absent from runtime
artifacts.
