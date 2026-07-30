# Release reports

This directory contains closed, versioned JSON contracts for WP17 evidence:

- `release-report-local.json` records exact locally completed suites, backend checks,
  the published universal artifact set, and every remaining external gate;
- `release/0.1.1-publication.md` binds the `0.1.1` PyPI filenames and hashes to the
  tagged source and records the post-publication installation checks;
- `coverage-matrix.json` binds all live `Reasoner` members and the compatible
  `pyowl_core.MODEL_CONSTRUCTORS` count to positive, negative, interaction, and backend
  evidence; and
- `schema/` contains the corresponding JSON Schema documents.

The committed examples are validated without a new runtime dependency by
`tests/release/test_wp17_reports.py`. Evidence paths must resolve inside the repository,
unexpected fields are rejected, and any blocked or failed external gate prevents an
overall `pass`.

The report's `revision` identifies the immutable release source under audit. Most evidence
paths resolve at that revision. A post-publication record necessarily lives in a later
evidence-only commit; it names and hashes the release source and artifacts rather than
claiming inclusion in the earlier tag or sdist. Development tests, hosted workflows, and
reference-oracle paths are not necessarily copied into a release sdist.

Artifact digests in the local report are the externally verified PyPI files named by the
linked publication record and explicit `source_revision`, not hashes embedded inside the
archives themselves. The separately labeled historical artifact audit remains the record
of earlier WPP0 development artifacts. No report in this directory independently
authorizes publication while `LIC-001` or another external gate remains open.
