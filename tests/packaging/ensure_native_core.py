#!/usr/bin/env python3
"""Provision the pinned native core prerequisite for compiled resource tests."""

from __future__ import annotations

import os
import shlex
import subprocess
import sys
import sysconfig

CORE_REQUIREMENT = "pyowl-core==0.2.1"
NATIVE_UNAVAILABLE = 3
PROBE = r"""
import importlib.metadata
from pathlib import Path

import pyowl_core as owl

installed_version = importlib.metadata.version("pyowl-core")
if installed_version != "0.2.1" or owl.__version__ != "0.2.1":
    raise RuntimeError(
        f"resource tests require pyowl-core==0.2.1; "
        f"installed={installed_version!r}, imported={owl.__version__!r}"
    )
if not owl.native_validation_available():
    raise SystemExit(3)

from pyowl_core.backends.native_views import (
    produce_encoded_structural_view_v2,
    validate_encoded_structural_view_v2,
)

snapshot = owl.load_snapshot(
    b"Prefix(:=<urn:resource-prerequisite#>) "
    b"Ontology(<urn:resource-prerequisite> "
    b"Declaration(Class(:A)) Declaration(Class(:B)) SubClassOf(:A :B))",
    options=owl.LoadOptions(
        format=owl.DocumentFormat.FUNCTIONAL,
        imports=owl.ImportPolicy.IGNORE,
        backend=owl.BackendPreference.NATIVE,
    ),
)
if snapshot.capabilities.backend != "native":
    raise RuntimeError("resource prerequisite did not create a native snapshot")
publication = produce_encoded_structural_view_v2(snapshot, require_native_validation=True)
validated = validate_encoded_structural_view_v2(
    publication,
    expected_owner=snapshot,
    expected_scope=owl.AxiomScope.CLOSURE,
    expected_document_key=None,
    require_native_validation=True,
)
if validated.owner is not snapshot or validated._native_receipt is None:
    raise RuntimeError("resource prerequisite lacks an owner-bound native receipt")
print(
    f"native core prerequisite passed: core={installed_version} "
    f"path={Path(owl.__file__).resolve()}"
)
"""


def _build_environment(environment: dict[str, str]) -> dict[str, str]:
    selected = environment.copy()
    selected["PYOWL_CORE_BUILD_NATIVE"] = "1"
    # Like pyhermit's wheel build, a musl extension needs the dynamic C runtime.
    host_gnu_type = str(sysconfig.get_config_var("HOST_GNU_TYPE") or "")
    if host_gnu_type.endswith("-linux-musl"):
        encoded_flags = selected.get("CARGO_ENCODED_RUSTFLAGS")
        rust_flags = (
            encoded_flags.split("\x1f")
            if encoded_flags
            else shlex.split(selected.get("RUSTFLAGS", ""))
        )
        rust_flags.append("-Ctarget-feature=-crt-static")
        selected["CARGO_ENCODED_RUSTFLAGS"] = "\x1f".join(rust_flags)
        selected.pop("RUSTFLAGS", None)
    return selected


def main() -> int:
    environment = os.environ.copy()
    environment.pop("PYTHONPATH", None)
    environment["PYTHONSAFEPATH"] = "1"
    probe = [sys.executable, "-I", "-c", PROBE]
    result = subprocess.run(probe, env=environment, check=False)
    if result.returncode == 0:
        return 0
    if result.returncode != NATIVE_UNAVAILABLE:
        result.check_returncode()

    print(f"Building the native resource-test prerequisite from {CORE_REQUIREMENT}", flush=True)
    subprocess.run(
        [
            sys.executable,
            "-m",
            "pip",
            "install",
            "--no-cache-dir",
            "--no-deps",
            "--no-binary=pyowl-core",
            "--force-reinstall",
            CORE_REQUIREMENT,
        ],
        env=_build_environment(environment),
        check=True,
    )
    # A fresh interpreter must prove the installed artifact; installation alone
    # cannot satisfy the prerequisite or reuse modules from the earlier probe.
    subprocess.run(probe, env=environment, check=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
