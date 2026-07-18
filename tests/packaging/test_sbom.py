"""Tests for deterministic release SBOM generation."""

from __future__ import annotations

from tools.packaging_probe.create_sbom import create_sbom
from tools.specs._compat import repository_root


def test_spdx_sbom_is_deterministic_and_contains_runtime_and_locked_components() -> None:
    namespace = "https://github.com/OAEI-ML/pyHermiT/sbom/test-revision"
    first = create_sbom(repository_root(), namespace)
    second = create_sbom(repository_root(), namespace)
    assert first == second
    assert first["spdxVersion"] == "SPDX-2.3"
    assert first["documentNamespace"] == namespace
    packages = first["packages"]
    assert isinstance(packages, list)
    assert all(package["copyrightText"] == "NOASSERTION" for package in packages)
    names = {package["name"] for package in packages}
    assert {"pyHermiT", "pyowl-core", "pyo3", "serde", "sha2"}.issubset(names)
