# LIC-001 wheel/sdist license and source-obligation audit

Audit date: 2026-07-18

Status: **repository-owned packaging policy implemented and locally audited; owner/legal review
pending**.

This report records engineering evidence, not legal advice or permission to publish. LIC-001
remains open and `publish_allowed = false`.

## Declared license and notices

- `pyproject.toml` uses the PEP 639 expression `LGPL-3.0-or-later` and declares exactly
  `LICENSE`, `COPYING`, and `NOTICE.md` as license files.
- The Cargo workspace and private native crate use the same SPDX expression and are
  `publish = false`.
- `LICENSE` is the GNU Lesser General Public License version 3 text; `COPYING` is the GNU
  General Public License version 3 text incorporated by LGPLv3.
- `NOTICE.md` identifies the source-guided implementation mode, pinned HermiT repository and
  commit, upstream license/copyright, adapted-file inventory, lack of endorsement, and pending
  legal review.

The fail-closed artifact inspector parses metadata rather than grepping raw archives. It now
validates the exact three `License-File` fields, UTF-8 license payloads, LGPL/GPL text identity
markers, required NOTICE provenance values, exact audited payload SHA-256 identities, complete
wheel `RECORD` hashes, and identical license/notice payload hashes between pure and native
wheels.

## Distribution/source policy implemented by the repository

Every wheel release must be accompanied by the same-version source distribution from the same
immutable release. A wheel-only upload is not an accepted release shape. The sdist contains:

- the complete Python sources and the complete optional Rust extension sources;
- `Cargo.toml`, locked `native/Cargo.lock`, build configuration, and `deny.toml`;
- `LICENSE`, `COPYING`, and `NOTICE.md` at its root;
- `reports/licensing/adapted-files.toml`, both licensing audits, and the artifact audit;
- specifications and documentation required to understand the modifications and rebuild; and
- no compiled extension, Java/JVM artifact, quarantined reference source, or development oracle.

`MANIFEST.in` includes TOML evidence under `reports/`, and the artifact inspector rejects an
sdist missing any of the four LIC-001 repository-owned deliverables. Published source must
remain available with the corresponding binary release through the configured repository/index
channels; replacing that policy or distributing a binary without corresponding source requires
a new owner/legal-reviewed LIC-001 decision.

## Local artifact result

The current-tree local build and inspector result is recorded in
`../release/artifact-audit.md`. Pure/native wheel metadata, Python payloads, and license/notice
payloads were identical except for the single allowlisted native extension. The sdist included
all source and LIC-001 evidence listed above.

Hosted cross-platform wheel validation, signing, registry publication, long-term source-hosting
arrangements, and the legal sufficiency of this source strategy are not inferred from local
archive checks. They remain release-owner responsibilities; publication stays blocked pending
the explicit legal signoff document.
