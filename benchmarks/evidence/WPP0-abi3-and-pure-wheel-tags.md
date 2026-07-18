# WPP0 local ABI3 and pure-wheel evidence

Commit `fb6e128` fixes the local wheel-tag boundary by configuring setuptools' wheel
command with `py_limited_api = cp310`. This is the configuration required by
setuptools-rust for a PyO3 stable-ABI wheel; the `RustExtension` keeps its recommended
`py_limited_api="auto"` behavior and the Rust crate independently pins the
`pyo3/abi3-py310` feature.

Authoritative packaging reference:

- <https://setuptools-rust.readthedocs.io/en/latest/building_wheels.html#building-for-abi3>

## Clean-source builds

Both wheels were built from a fresh `git archive` extraction, outside the repository,
with build isolation disabled so the already-pinned local toolchain was used:

- forced native (`PYHERMIT_BUILD_NATIVE=1`) produced
  `pyhermit-0.1.0.dev0-cp310-abi3-macosx_14_0_x86_64.whl` containing exactly one
  `_native.abi3.so`;
- forced pure (`PYHERMIT_BUILD_NATIVE=0`) produced
  `pyhermit-0.1.0.dev0-py3-none-any.whl` containing no native library.

The repository artifact inspector accepted both wheels. Each was Java-free, excluded
the reference/packaging-probe trees, contained the required license payloads and type
marker, and declared only the expected Python runtime dependency boundary.

## Installed smoke checks

The same native `cp310-abi3` wheel installed and imported in fresh CPython 3.10.11 and
3.12.3 virtual environments. In both environments:

- `pyhermit.__version__` was `0.1.0.dev0`;
- the extension version was `0.1.0-dev` with native ABI version `1`; and
- `pyhermit._native.self_test()` completed successfully.

The pure wheel installed in a fresh CPython 3.10 environment with Cargo and Java absent
from `PATH`. Public import succeeded, no `pyhermit._native` module existed, and
`backend_info()` selected the Python backend while reporting native as `not_installed`.

This is a local macOS x86-64 proof, not a claim that the complete cibuildwheel platform
matrix or release-signing gate has passed; those remain WPP0/LIC-001 release work.
