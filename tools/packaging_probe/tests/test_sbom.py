from __future__ import annotations

import unittest
from pathlib import Path
from typing import Any, cast

from tools.packaging_probe.create_sbom import (
    _cargo_packages,
    _production_lock_packages,
    create_sbom,
    verify_cargo_metadata,
)
from tools.specs._compat import load_toml


class SbomTests(unittest.TestCase):
    def setUp(self) -> None:
        self.root = Path(__file__).parents[3]

    def test_locked_production_closure_excludes_native_development_dependencies(self) -> None:
        packages = _production_lock_packages(
            load_toml(self.root / "native/Cargo.toml"),
            load_toml(self.root / "native/Cargo.lock"),
            "pyhermit-native",
        )
        names = {str(package["name"]) for package in packages}

        self.assertEqual(len(packages), 35)
        self.assertTrue(
            {
                "num-bigint",
                "pyo3",
                "pyo3-build-config",
                "quick-xml",
                "serde_json",
                "sha2",
            }
            <= names
        )
        self.assertTrue(
            {
                "anes",
                "ciborium",
                "clap",
                "criterion",
                "criterion-plot",
                "tinytemplate",
            }.isdisjoint(names)
        )

    def test_rust_spdx_packages_are_checksum_and_license_bound(self) -> None:
        packages = _cargo_packages(self.root)

        self.assertEqual(len(packages), 35)
        for package in packages:
            self.assertNotEqual(package["licenseDeclared"], "NOASSERTION")
            self.assertEqual(package["licenseConcluded"], package["licenseDeclared"])
            self.assertRegex(str(package["downloadLocation"]), r"^https://crates\.io/")
            checksums = cast(list[dict[str, str]], package["checksums"])
            self.assertEqual(
                checksums[0]["algorithm"],
                "SHA256",
            )
            self.assertRegex(
                checksums[0]["checksumValue"],
                r"^[0-9a-f]{64}$",
            )

    def test_audited_closure_matches_locked_cargo_metadata(self) -> None:
        self.assertEqual(verify_cargo_metadata(self.root), 35)

    def test_release_sbom_describes_only_the_exact_distribution_closure(self) -> None:
        namespace = "https://github.com/OAEI-ML/pyHermiT/sbom/test-revision"

        first = create_sbom(self.root, namespace)
        second = create_sbom(self.root, namespace)

        self.assertEqual(first, second)
        packages = cast(list[dict[str, Any]], first["packages"])
        self.assertEqual(len(packages), 37)  # project, pyowl-core, and 35 Rust crates
        by_name = {cast(str, package["name"]): package for package in packages}
        self.assertEqual(
            by_name["target-lexicon"]["licenseDeclared"],
            "Apache-2.0 WITH LLVM-exception",
        )
        self.assertNotIn("criterion", by_name)
        self.assertNotIn("clap", by_name)
        self.assertEqual(first["documentNamespace"], namespace)


if __name__ == "__main__":
    unittest.main()
