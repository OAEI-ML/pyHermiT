from __future__ import annotations

import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from tools.packaging_probe.run_probe import _build, prove_same_version_tag_preference


class TagPreferenceTests(unittest.TestCase):
    def test_native_tag_outranks_same_version_pure_wheel(self) -> None:
        result = prove_same_version_tag_preference()

        self.assertIn("cp310-abi3", result["supported"])
        self.assertTrue(result["python_only"].endswith("-py3-none-any.whl"))

    @patch("tools.packaging_probe.run_probe.subprocess.run")
    def test_build_hides_the_host_toolchain(self, run: object) -> None:
        run.return_value.returncode = 0  # type: ignore[attr-defined]
        run.return_value.stdout = "probe"  # type: ignore[attr-defined]
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            project = root / "project"
            output = root / "output"
            project.mkdir()
            output.mkdir()

            _build("auto", project, output)

        environment = run.call_args.kwargs["env"]  # type: ignore[attr-defined]
        self.assertEqual(environment["PATH"], str(output / "unavailable-toolchain"))
        self.assertEqual(environment["CARGO"], str(output / "unavailable-toolchain/cargo"))
        self.assertEqual(environment["RUSTC"], str(output / "unavailable-toolchain/rustc"))


if __name__ == "__main__":
    unittest.main()
