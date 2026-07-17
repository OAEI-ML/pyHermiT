"""Probe-only optional Rust extension declaration."""

from __future__ import annotations

import os

from setuptools import setup

mode = os.environ.get("PYHERMIT_BUILD_NATIVE", "auto")
if mode not in {"auto", "0", "1"}:
    raise RuntimeError(f"invalid PYHERMIT_BUILD_NATIVE probe mode: {mode!r}")

rust_extensions = []
if mode != "0":
    from setuptools_rust import Binding, RustExtension

    rust_extensions.append(
        RustExtension(
            "pyhermit_build_probe._native",
            path="native/Cargo.toml",
            binding=Binding.PyO3,
            optional=mode == "auto",
        )
    )

setup(rust_extensions=rust_extensions, zip_safe=False)
