"""Conditional declaration of pyHermiT's future private Rust extension."""

from __future__ import annotations

import os
from pathlib import Path

from setuptools import setup

_VALID_MODES = frozenset({"auto", "0", "1"})


def _native_mode() -> str:
    value = os.environ.get("PYHERMIT_BUILD_NATIVE", "auto")
    if value not in _VALID_MODES:
        expected = "auto, 0, or 1"
        raise RuntimeError(f"PYHERMIT_BUILD_NATIVE must be {expected}; got {value!r}")
    return value


mode = _native_mode()
manifest = Path("native/Cargo.toml")
rust_extensions = []

if mode != "0" and manifest.is_file():
    from setuptools_rust import Binding, RustExtension

    rust_extensions.append(
        RustExtension(
            "pyhermit._native",
            path=str(manifest),
            binding=Binding.PyO3,
            optional=mode == "auto",
            cargo_manifest_args=("--locked",),
        )
    )
elif mode == "1":
    raise RuntimeError("native build required but native/Cargo.toml is not implemented yet")

setup(rust_extensions=rust_extensions, zip_safe=False)
