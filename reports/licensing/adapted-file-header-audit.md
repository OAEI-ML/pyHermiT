# LIC-001 adapted-file header audit

Audit date: 2026-07-18

Status: **repository-owned audit complete; owner/legal review pending**.

This audit implements the engineering inventory and notice requirements recorded in
`specs/deviations.md` §5. It is not legal advice and does not close LIC-001.
Publication remains blocked while `publish_allowed = false`.

## Scope and method

`adapted-files.toml` uses a conservative evidence rule: include every runtime file that
explicitly identifies HermiT-derived shapes, side conditions, or compatibility, every runtime
file already carrying the upstream Oxford modification notice, the complete Python blocking
subsystem that `tools/blocking/WP11-EVIDENCE.md` identifies as a port, plus the two WP10 test
files explicitly specified as ports of upstream `MergeTest` and `NIRuleTest`. The inventory
contains 32 files: 30 Python and 2 Rust. Absence from that list is not a clean-room or
originality claim; all distributed project code remains under `LGPL-3.0-or-later`.

The executable audit in `tests/release/test_licensing_evidence.py` verifies that:

1. the inventory is schema 1, names the hash-pinned HermiT repository, commit, tree, and
   `LGPL-3.0-or-later` license recorded by the reference manifest;
2. paths are unique, sorted, repository-relative runtime or adapted-test paths and every file
   exists;
3. each current file SHA-256 equals its inventory value;
4. every entry has a nonempty adaptation statement and one or more safe pinned-upstream Java
   component paths;
5. every adapted file retains the Oxford copyright, a 2026 pyHermiT modification notice,
   `SPDX-License-Identifier: LGPL-3.0-or-later`, the exact upstream commit, and a link back to
   the inventory; and
6. every explicit source-guided/ported/HermiT-compatible admission found in runtime sources or
   the two WP10 adapted-test locations is present in the inventory.

## Result

All 32 inventory hashes, provenance mappings, and file headers pass the executable audit. The
common adapted-file header deliberately uses a conservative aggregate Oxford 2008/2009/2010
notice. Individual pinned components include 2009-only headers and, for `XMLLiteral.java`, no
file-level header; the inventory records those variants instead of claiming the aggregate line
is a verbatim notice from every mapped Java file. Approval of that aggregate layout remains part
of owner/legal review. All 57 distinct upstream component paths resolved in the local
hash-pinned, fetch-only checkout. No HermiT Java source, class, JAR, or reference checkout is
present in the runtime package or release artifacts; upstream paths in the inventory identify
the fetch-only reference at commit
`37ec30aced32ac81ebecc5e33fad255ddefcb4c3`.

The repository-wide LGPL choice is intentionally broader than this adapted-file list. The
inventory neither offers unlisted original files under a second license nor asserts that the
32-file minimum is a legal determination of every possible derivative boundary. Other tests are
classified as project-authored semantic-intent/oracle coverage and their data artifacts are
separately bound by `tests/data/PROVENANCE.toml`; owner/legal review must affirm or revise that
classification. That judgment, the final notice layout, and the release decision remain
assigned to the pending
`owner-legal-review-signoff` gate.

## Reproduction

```text
PYTHONPATH=src:../pyOWLCore/src python -m pytest -q \
  tests/release/test_licensing_evidence.py tools/specs/tests/test_release_gate.py
python -m tools.specs.check_release_gate --assert-blocked
```
