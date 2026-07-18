# Release reports

This directory contains closed, versioned JSON contracts for WP17 evidence:

- `release-report-local.json` records exact locally completed suites, backend and
  historical artifact checks, and every remaining external gate;
- `coverage-matrix.json` binds all live `Reasoner` members and the compatible
  `pyowl_core.MODEL_CONSTRUCTORS` count to positive, negative, interaction, and backend
  evidence; and
- `schema/` contains the corresponding JSON Schema documents.

The committed examples are validated without a new runtime dependency by
`tests/release/test_wp17_reports.py`. Evidence paths must resolve inside the repository,
unexpected fields are rejected, and any blocked or failed external gate prevents an
overall `pass`.

Artifact digests in the local report are the previously completed WPP0 artifacts named
by their linked evidence and explicit `source_revision`, not hashes of an archive
containing the report itself. A
release candidate must publish its artifact digest manifest as an external attestation
after the immutable artifacts have been built; embedding an archive's own SHA-256 inside
that archive is impossible. No report in this directory authorizes publication while
`LIC-001` or another external gate remains open.
