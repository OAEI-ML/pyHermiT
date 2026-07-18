# WP17 local integration audit

Date: 2026-07-18

This tranche adds executable release-report and coverage-matrix contracts, final user/developer
guides, and a hash-bound phase benchmark harness. It records only locally reproducible evidence;
it does not turn any external WP17 gate into a pass.

## Machine-readable release contracts

- `reports/schema/release-report-v1.schema.json` closes the local report vocabulary and requires
  exact suite, backend, artifact, and external-gate evidence.
- `reports/schema/coverage-matrix-v1.schema.json` requires positive, negative, interaction, and
  four-backend evidence for every operation group.
- `tests/release/test_wp17_reports.py` validates both committed examples without a new runtime
  dependency, checks every evidence path, compares the constructor count with the live
  `pyowl_core.MODEL_CONSTRUCTORS`, compares the operation union with every public `Reasoner`
  member, and forces the overall report to fail closed.

The report remains `blocked`. In particular, an implemented `full_reasoner` capability is not a
claim that the licensed 350-check lane, hosted platform/sanitizer matrix, controlled Java
comparison, performance calibration, or `LIC-001` review has passed.

Adding the WP17 release tests exposed that the prior default `testpaths` omitted the committed
integration, differential, and native directories. Those three lanes are now part of the default
suite. The complete forced-backend results were:

| Runtime / forced default | Result | Wall time |
|---|---:|---:|
| CPython 3.10.11 / Python | 916 passed + 4 subtests | 176.37 s |
| CPython 3.12.3 / Python | 916 passed + 4 subtests | 151.62 s |
| CPython 3.10.11 / native | 916 passed + 4 subtests | 174.58 s |
| CPython 3.12.3 / native | 916 passed + 4 subtests | 150.11 s |

Each run emitted the same four expected `OverlayPerformanceWarning` records from tests that
deliberately construct a delta above the ten-percent advisory threshold. There were no failures,
skips, or unexpected warnings. Explicit native and verify parametrizations remain in the suite,
so forcing the default does not hide cross-backend cases.

`cargo test --manifest-path native/Cargo.toml --no-default-features --all-targets` passed 211
library tests, 8 input-wire tests, and 6 operation-control tests, then executed every Criterion
smoke target. `cargo fmt --all -- --check` and Clippy over all no-default-feature targets with
warnings denied also passed. The locked dependency graph did not change from the WPP0
`cargo-deny` evidence.

## Final local artifacts

The final fixed-epoch tree built a compiler-free `py3-none-any` wheel, source archive,
and forced `cp310-abi3` native wheel. The artifact inspector accepted each archive's
metadata, safe paths, Java/source/reference exclusions, type payload, and truthful tags;
its pure/native comparison found identical metadata and Python payloads plus exactly one
native extension. The pure wheel SHA-256 was
`548608fd4fb79622fe783268a0c6e65ce57dd5c14cf0e26215b1da92e3759e23`; the native wheel
SHA-256 was `19b3b8789bde9d6f1742e9aaae5e5bc48ea86d452999570f39d2e74fdb4bda63`.

Two independent fixed-epoch invocations produced byte-identical pure wheels, native
wheels, and sdists. The source-archive digest is intentionally not embedded in a file
inside that archive; it belongs in the external post-build attestation described in
`reports/README.md`. The optional local `abi3audit` executable was unavailable in this
shell. WPP0 already records the unchanged extension's successful ABI3 and linked-library
audit, while hosted target revalidation remains blocked rather than inferred.

## Local phase probe

Both backends ran three samples over the same generated eight-class/eight-individual taxonomy.
The input SHA-256 was
`71025acfc32b25e93f5c171599bfa187da5fd6b1a689ce2ffa305dd364e14e2a`; both produced result
SHA-256 `d01d0a30c4cf412b37bc4b1dc37ea6ade921c37efc8bd2bffe7cc2755b830b2d` while retaining the
same loaded core snapshot by identity.

| Median phase | Python | Native |
|---|---:|---:|
| load | 0.0516 s | 0.0532 s |
| compile/session | 0.1526 s | 0.1930 s |
| consistency | 0.0320 s | 0.00872 s |
| class classification | 1.9181 s | 0.1653 s |
| realization query | 0.4938 s | 0.3425 s |

The native classification median was about 11.6 times faster for this tiny local workload. Native
compile/session time was slower, and peak process RSS was 53.3 MB versus 51.8 MB. These values are
profiling evidence only: the process was not isolated, the workload is tiny, and three warm-process
samples cannot satisfy `specs/performance.md`.

Raw samples, environment, allocation/RSS peaks, backend versions, and hashes are stored in
`wp17-local-python.json` and `wp17-local-native.json`. `benchmarks/targets.toml` deliberately stays
`provisional-awaiting-dedicated-calibration`, and `benchmarks/baselines/` contains no accepted
baseline.

## Commands

```text
PYTHONPATH=src:../pyOWLCore/src .reference/venv312/bin/python \
  benchmarks/run_release.py --backend python --size small --samples 3
PYTHONPATH=src:../pyOWLCore/src .reference/venv312/bin/python \
  benchmarks/run_release.py --backend native --size small --samples 3
PYTHONPATH=src:../pyOWLCore/src .reference/venv310/bin/python -m pytest -q tests/release
PYTHONPATH=src:../pyOWLCore/src .reference/venv312/bin/python -m pytest -q tests/release
```

The dedicated runner must still execute cold processes and medium/large licensed and generated
families, retain failures/timeouts, compare identical result hashes with pinned Java, and obtain a
reviewed calibration before any target is frozen.
