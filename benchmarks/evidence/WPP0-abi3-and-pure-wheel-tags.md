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

## Compiler-free sdist smoke check

A clean-source `python -m build --sdist` run produced
`pyhermit-0.1.0.dev0.tar.gz`. The artifact inspector accepted all 256 members and found
the locked native Cargo manifest, lockfile, complete Rust source/benchmark trees, and no
Java or reference-probe material.

With Cargo and Java absent from `PATH`, the default optional-extension path built and
installed a working Python-only local wheel under CPython 3.10. The locally built file
retained a platform/ABI3 tag because the optional Rust extension had been declared
before its missing-compiler failure, but contained no native module; public import
selected Python. The separately published fallback remains the explicitly forced
`py3-none-any` wheel described above.

With `PYHERMIT_BUILD_NATIVE=1` and Cargo restored, the same sdist produced a
`cp310-abi3` wheel containing the extension. Its SHA-256 was
`7c04593492117d171e0b0c4e744956dc053fc67e0be74556e7d06f1f87f20ac1`, and the
repository artifact inspector accepted all 93 members as Java-free.

This is a local macOS x86-64 proof, not a claim that the complete cibuildwheel platform
matrix or release-signing gate has passed; those remain WPP0/LIC-001 release work.
