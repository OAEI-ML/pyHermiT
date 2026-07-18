# WPP0 local ABI3 and compiler-free artifact evidence

This report records the final local packaging checks run on 2026-07-18 after the native
reasoner-service tranche (`6d02927`), repository formatting baseline (`d4c4f9e`), incremental
query optimization (`fac5263`), and native told-taxonomy fast path (`a01fecb`). The
uncommitted WPP0 packaging tranche used for these builds is committed atomically with this
report.

Setuptools is configured with `py_limited_api = cp310`, while the Rust crate pins
`pyo3/abi3-py310`. The package and extension both read the canonical Python version source.
The authoritative setuptools-rust ABI3 reference is:

- <https://setuptools-rust.readthedocs.io/en/latest/building_wheels.html#building-for-abi3>

## Final local artifact set

Forced native mode (`PYHERMIT_BUILD_NATIVE=1`) and fixed-epoch pure builds produced:

| Artifact | Members | Bytes | SHA-256 |
|---|---:|---:|---|
| `pyhermit-0.1.0.dev0-cp310-abi3-macosx_14_0_x86_64.whl` | 100 | 2,096,425 | `c63bb23525f9defb447770e4723e29c5a327d403765c79cc57edbd7cc76583e8` |
| `pyhermit-0.1.0.dev0-py3-none-any.whl` | 99 | 374,415 | `e8be980329d8e7a8af76d3e54eae0d722219960eba91e3e290078701f1fc2978` |
| `pyhermit-0.1.0.dev0.tar.gz` | 247 | 798,541 | `68b3755aeaae007362e178d827296547ab739ec8107e482bb5057d32504e6b3b` |

The native wheel adds exactly one `_native.abi3.so`; the Python payload and distribution
metadata otherwise compare exactly with the pure wheel. The extension reports package
version `0.1.0.dev0`, native ABI version `1`, and passes `self_test()`. `otool -L` found only
the extension install name plus macOS system `libiconv` and `libSystem` dependencies.

The fail-closed artifact inspector accepted all three artifacts. It validates safe archive
paths and sizes, exact project/core dependency/license metadata, license payloads, wheel
filename/WHEEL tag agreement, `Root-Is-Purelib`, complete SHA-256 `RECORD` entries, type
marker and native stub presence, source/build/reference/Java exclusion, and rooted build-path
leaks. The sdist includes `deny.toml`, the locked Cargo graph, complete Python/Rust sources,
specifications, build configuration, and no compiled/reference/probe material.

## Reproducibility

Two independently copied source trees were built under Python 3.12 with the exact pinned
frontend (`build 1.5.0`, `setuptools 83.0.0`, `setuptools-rust 1.13.0`, `wheel 0.46.3`),
`PYHERMIT_BUILD_NATIVE=0`, and `SOURCE_DATE_EPOCH=946684800`. Both pure-wheel copies and both
sdist copies compared byte-for-byte equal and produced the hashes above.

Release CI performs the equivalent native rebuild from a second independent checkout on
each target and requires byte equality before upload to the workflow artifact store.

## Installed compiler-free and ABI3 checks

Fresh CPython 3.10 and 3.12 virtual environments installed the native wheel and a pure
`pyowl-core` wheel. With compilers and Java hidden by the installed smoke harness, both
reported the native backend, consumed bytes/snapshot/provider inputs without reparsing, and
returned identical consistency/classification results.

Fresh CPython 3.10 and 3.12 environments also installed the pure wheel and selected the
Python backend. Separately, the sdist built and installed offline on both versions with
`CARGO` pointed at a nonexistent executable, compiler/Java paths unavailable, build
isolation disabled, and all pinned build inputs supplied from a local wheelhouse. Each sdist
installation produced a truthful `py3-none-any` wheel and passed the installed standalone,
shared-view, and provider smoke.

Forced native mode remains non-optional: hiding Cargo causes a clear build failure and can
never silently emit a pure wheel.

## Dependency and hosted release gates

The committed `deny.toml` policy passed the complete locked graph locally: advisories, crate
license allow-list, duplicate/wildcard bans, and source-registry policy were all clean. The
distribution workflow runs the same fail-closed policy using the commit-pinned
`cargo-deny-action`, in addition to pinned ABI and platform shared-library auditors. The
machine-readable project inventory contains all 23 direct Python, native Rust, build,
development, and packaging-probe dependencies; the SPDX SBOM expands the complete Cargo.lock
graph.

The hosted workflow is configured for the eight required manylinux 2.17, musllinux 1.2,
macOS, and Windows x86-64/ARM64 targets. It builds `cp310-abi3` wheels, installs on CPython
3.10 and 3.12 with pure/native core variants, exercises the full installed semantic suite,
and checks local-index native preference/fallback. Those cross-platform results remain
explicitly `configured-awaiting-hosted-validation` until GitHub Actions produces them.

Publication and release attestation also remain blocked by the five open LIC-001
provenance/source-obligation/legal-review items. The release workflow contains no package
index upload action or permission while that gate is open.
