from __future__ import annotations

import tempfile
import textwrap
import unittest
from pathlib import Path

from tools.specs._compat import repository_root
from tools.specs.check_workpackages import ManifestError, validate_workpackages


class WorkPackageManifestTests(unittest.TestCase):
    def test_actual_manifest_is_valid(self) -> None:
        root = repository_root()
        summary = validate_workpackages(
            root / "specs/workpackages/manifest.toml",
            root / "tools/specs/ownership-allowlist.toml",
        )

        self.assertEqual(summary["packages"], 25)
        self.assertEqual(summary["waves"], 14)
        self.assertEqual(summary["allowed_collisions"], 19)

    def _validate_fixture(self, packages: str, allowances: str = "schema = 1\n") -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            manifest = root / "manifest.toml"
            allowlist = root / "allowlist.toml"
            manifest.write_text("schema = 2\nreference = 'test'\n" + packages, encoding="utf-8")
            allowlist.write_text(allowances, encoding="utf-8")
            for package_id in ("WP0", "WP1"):
                (root / f"{package_id}.md").write_text(f"# {package_id}\n", encoding="utf-8")
            validate_workpackages(manifest, allowlist)

    def test_unknown_dependency_is_rejected(self) -> None:
        packages = """
[[package]]
id = "WP0"
brief = "WP0.md"
wave = 0
depends = ["MISSING"]
owns = ["a.py"]
"""
        with self.assertRaisesRegex(ManifestError, "unknown dependencies"):
            self._validate_fixture(packages)

    def test_cycle_is_rejected(self) -> None:
        packages = """
[[package]]
id = "WP0"
brief = "WP0.md"
wave = 0
depends = ["WP1"]
owns = ["a.py"]
[[package]]
id = "WP1"
brief = "WP1.md"
wave = 1
depends = ["WP0"]
owns = ["b.py"]
"""
        with self.assertRaisesRegex(ManifestError, "dependency cycle"):
            self._validate_fixture(packages)

    def test_nonprior_dependency_wave_is_rejected(self) -> None:
        packages = """
[[package]]
id = "WP0"
brief = "WP0.md"
wave = 1
depends = []
owns = ["a.py"]
[[package]]
id = "WP1"
brief = "WP1.md"
wave = 1
depends = ["WP0"]
owns = ["b.py"]
"""
        with self.assertRaisesRegex(ManifestError, "does not follow"):
            self._validate_fixture(packages)

    def test_unapproved_collision_is_rejected(self) -> None:
        packages = textwrap.dedent(
            """
            [[package]]
            id = "WP0"
            brief = "WP0.md"
            wave = 0
            depends = []
            owns = ["src/"]
            [[package]]
            id = "WP1"
            brief = "WP1.md"
            wave = 1
            depends = ["WP0"]
            owns = ["src/value.py"]
            """
        )
        with self.assertRaisesRegex(ManifestError, "ownership collision"):
            self._validate_fixture(packages)


if __name__ == "__main__":
    unittest.main()
