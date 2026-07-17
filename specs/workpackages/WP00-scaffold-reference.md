# WP00 — Scaffold, reference pin, and build proof

**Goal**: establish a reproducible, Java-free project skeleton and prove the
same-version native/pure wheel strategy before semantic agents depend on it.

## Read first

| What | Where |
|---|---|
| Product architecture and global gates | `SPEC.md` §§1–4, 6, 9–10 |
| Native packaging decision | `native-backend.md` §§1–3, 9–12 |
| Provenance policy | `deviations.md` §§4–7 |
| Upstream identity/license/build | pinned HermiT `README.txt`, `pom.xml`, commit `37ec30a` |
| Work-package rules | this directory's `README.md` and `manifest.toml` |

## Deliverables

- `pyproject.toml` with Python ≥3.10, `src/` discovery, typed/lint/test/import-linter
  development configuration, `pyowl-core>=0.1,<0.2`, the recorded
  `LGPL-3.0-or-later` SPDX expression and license files, a machine-readable
  non-publishable `LIC-001` compliance gate, and setuptools/setuptools-rust build
  requirements.
- Minimal `setup.py`, `MANIFEST.in`, workspace `Cargo.toml`, and empty public package
  marker. No fake reasoner/backend is allowed.
- Directory skeleton implied by `SPEC.md` without placeholder semantic functions.
- CI for lint, types, unit smoke, spec-link/manifest validation, dependency/license
  audit hooks, and a no-Java artifact check.
- `tools/specs/check_workpackages.py` validating unique IDs, existing briefs, known
  dependencies, acyclic graph, dependency waves, and owned-path collision allowlist.
- A self-contained `tools/packaging_probe/` proving `PYHERMIT_BUILD_NATIVE=0|1|auto`,
  same-version tag selection, and optional-build failure behavior without becoming a
  runtime package.
- Developer commands in the root README or contributing stub for reproducible setup.
- A recorded PyPI/TestPyPI normalized-name availability/collision check; keep the
  `pyhermit` import namespace even if the distribution name needs an owner-approved
  adjustment.

## Depends on

None.

## Acceptance criteria

1. The pinned reference identifier, full SHA, date, and upstream version are present in
   one machine-readable project metadata location and match the specs.
2. Pure wheel and sdist metadata build in isolation with Cargo hidden; neither contains
   Java or the packaging probe.
3. The probe demonstrates a forced native wheel fails loudly on a broken compiler and
   `auto`/pure complete successfully without one.
4. Manifest validation proves the published graph is acyclic and wave-consistent.
5. Importing the empty package does not import a backend or perform I/O/network work.
6. CI is green on Linux and has matrix placeholders/issues for required later wheel
   platforms rather than falsely passing an absent extension.
7. `LIC-001` from `deviations.md` is machine-readable and release workflows refuse publish
   until the recorded source-guided LGPL strategy has complete provenance, adapted-file
   notices, package metadata, source-obligation evidence, artifact audits, and
   owner/legal-review sign-off.
