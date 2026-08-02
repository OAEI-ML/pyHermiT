# pyHermiT documentation

pyHermiT is a Java-free OWL 2 DL reasoner with a complete Python backend and an
optional Rust backend. It consumes the immutable ontology views defined by
`pyowl-core`; an existing snapshot, overlay, composite, or provider is retained rather
than parsed into a second public model.

```bash
python -m pip install pyHermiT
```

- [User guide](user-guide.md): installation, backend selection, shared views, services,
  updates, errors, timeouts, and concurrency.
- [API reference](api-reference.md): the stable facade members, result shapes, and
  supporting public types.
- [Developer guide](developer-guide.md): architecture, private IR, calculus, native
  boundary, verification, provenance, and release evidence.
- [0.2 migration guide](migration-0.2.md): coordinated core upgrade, persisted-data
  invalidation, and native encoded-view compatibility.
- [Specifications](../specs/README.md): normative behavior and work-package contracts.
- [Local release report](../reports/release-report-local.json) and
  [coverage matrix](../reports/coverage-matrix.json): machine-readable WP17 state.

## Recommended first steps

1. Install pyHermiT in a fresh virtual environment.
2. Follow [Load once or reuse a shared view](user-guide.md#load-once-or-reuse-a-shared-view).
3. Use a `Reasoner` context manager and configure time and memory limits for
   untrusted or large inputs.
4. Record `backend_info()` and `reasoner.diagnostics()` with reproducible results.

The source tree identifies as production release `0.2.0`. The owner accepted the
remaining external W3C-body, live-reference, and dedicated-performance runs as
post-release follow-up and waived `LIC-001` as-is without claiming legal review.
The trusted publication workflow still requires every configured native target.
See the historical `0.1.1` release report and
[`0.2.0` owner override](../reports/release/0.2.0-owner-release-override.md)
for the exact qualification boundary.
