# WP00 verification evidence

Date: 2026-07-17 (Europe/London)

This report records the local implementation checkpoint for the
[WP00 brief](../../specs/workpackages/WP00-scaffold-reference.md). It is development
evidence, not a public-release artifact audit or legal sign-off. The implementation and
this report are committed atomically; the preceding specification/license baseline is
commit `c56a71c`.

## Scope and deliberate limits

- The package is `pyHermiT` `0.1.0.dev0`, import namespace `pyhermit`, with Python
  `>=3.10` and `pyowl-core>=0.1,<0.2` as its sole runtime dependency.
- The public package is intentionally inert and exports only `__version__`; WP00 does
  not claim to implement a parser, ontology model, reasoner, or native backend.
- No Java source, Java binary, bridge dependency, JVM command, or subprocess-backed
  reasoner is present in a built runtime artifact.
- `native/Cargo.toml` is intentionally absent until WPR0. The eight-platform
  [native target matrix](native-wheel-targets.toml) remains explicitly
  `planned-not-implemented`.
- The owner-recorded source-guided `LGPL-3.0-or-later` decision is represented by the
  [machine-readable LIC-001 gate](licensing.toml). Five requirements remain pending,
  so publication is denied. This checkpoint does not close LIC-001.
- `pyowl-core` was not installed for the inert foundation tests. Editable and wheel
  installs used `--no-deps`; integration begins only when WP01 consumes its frozen
  contract.

## Reproducible validation results

The checkout passed the following checks on macOS x86_64:

| Check | Result |
|---|---|
| Python unit/spec tests, CPython 3.10.11 | 19 passed; 4 subtests passed |
| Python unit/spec tests, CPython 3.12.3 | 19 passed; 4 subtests passed |
| `ruff format --check .` and `ruff check .` | passed |
| strict `mypy` over `src` and `tools` | 19 source files; no issues |
| `lint-imports` | 2 contracts kept; 0 broken |
| `compileall` under 3.10 and 3.12 | passed |
| Markdown link/fragment checker | 43 documentation files passed after adding this report |
| work-package validator | 24 packages, 51 dependencies, 13 waves, 12 allowlisted collisions |
| project metadata validator | 13 dependencies, 12 reference areas, 5 LIC-001 items pending, 8 planned native targets |
| release gate `--assert-blocked` | passed: publication blocked |
| release gate `--require-publishable` | failed as required |
| `git diff --check` | passed |

The test suite includes fail-closed release-gate mutation cases, inert isolated import,
build-mode checks, unsafe/Java archive rejection, packaging-probe exclusion, PEP 508
dependency parsing, work-package graph/ownership mutations, and same-version wheel-tag
selection.

## Compiler-free packaging proof

Both CPython 3.10.11 and 3.12.3 ran
`python -m tools.packaging_probe.run_probe --json` with `CARGO` and `RUSTC` pointing to
nonexistent executables:

- mode `0` built one `py3-none-any` wheel with no native member;
- mode `auto` reported the absent Rust compiler, completed through the optional
  extension path, and produced a wheel with no native member;
- mode `1` reported the absent Rust compiler, failed, and emitted no wheel;
- a compatible `cp310-abi3` same-version wheel outranked `py3-none-any`; and
- a simulated runtime without the native tag selected `py3-none-any`.

The actual project was copied to a temporary clean source tree and built with PEP 517
isolation under CPython 3.12.3 while Cargo and Rustc were hidden. The build produced:

| Artifact | Members |
|---|---:|
| `pyhermit-0.1.0.dev0-py3-none-any.whl` | 9 |
| `pyhermit-0.1.0.dev0.tar.gz` | 86 |

The artifact inspector accepted both. It verified the universal wheel tag, package/type
markers, `Requires-Python`, `pyowl-core` dependency, SPDX expression, three license
payloads, excluded build/spec paths from the wheel, excluded the probe/reference cache,
and rejected Java suffixes and Java bridge dependencies. The sdist retained the source,
specification, build, notice, and release-gate inputs required to rebuild and audit it.
A clean CPython 3.12 environment installed the wheel with `--no-deps` and imported
version `0.1.0.dev0` successfully. This local build is not a release-hash,
reproducibility, or LIC-001 artifact-audit claim.

## Reference and distribution-name records

The [reference manifest](reference.toml) pins HermiT commit
`37ec30aced32ac81ebecc5e33fad255ddefcb4c3` (`hermit-master-37ec30a`, upstream
`1.4.0.0-SNAPSHOT`, 2017-10-04 08:39:39 UTC) and classifies 12 source families without
vendoring the Java checkout.

The [distribution-name record](index-names.toml) queried the official JSON endpoints on
2026-07-17. `pyhermit` returned HTTP 404 on PyPI and TestPyPI, while the known alternate
`hermit-reasoner` returned HTTP 200 on PyPI. Availability is not a reservation and must
be rechecked immediately before any owner-approved upload.

## Remaining gates

WP00 leaves the following work visible rather than claiming it complete:

- five LIC-001 items: adapted-file inventory, file headers/modification notices,
  source/license layout obligations, release artifact audit, and owner/legal sign-off;
- all semantic, API, oracle, native-backend, conformance, performance, and release work
  assigned to WP01 and later packages; and
- actual native wheels and `abi3` verification assigned to WPR0/WPP0.
