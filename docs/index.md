# pyHermiT documentation

pyHermiT is a Java-free OWL 2 DL reasoner with a complete Python backend and an
optional Rust backend. It consumes the immutable ontology views defined by
`pyowl-core`; an existing snapshot, overlay, composite, or provider is retained rather
than parsed into a second public model.

- [User guide](user-guide.md): installation, backend selection, shared views, services,
  updates, errors, timeouts, and concurrency.
- [API reference](api-reference.md): the stable facade members, result shapes, and
  supporting public types.
- [Developer guide](developer-guide.md): architecture, private IR, calculus, native
  boundary, verification, provenance, and release evidence.
- [Specifications](../specs/README.md): normative behavior and work-package contracts.
- [Local release report](../reports/release-report-local.json) and
  [coverage matrix](../reports/coverage-matrix.json): machine-readable WP17 state.

The package is still `0.1.0.dev0`. A locally passing backend or artifact check is not a
1.0 release claim. The external W3C-body, live-reference, hosted-platform,
dedicated-performance, and `LIC-001` legal/provenance gates remain fail-closed in the
release report.
