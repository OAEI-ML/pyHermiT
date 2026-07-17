from __future__ import annotations

import unittest

from tools.packaging_probe.run_probe import prove_same_version_tag_preference


class TagPreferenceTests(unittest.TestCase):
    def test_native_tag_outranks_same_version_pure_wheel(self) -> None:
        result = prove_same_version_tag_preference()

        self.assertIn("cp310-abi3", result["supported"])
        self.assertTrue(result["python_only"].endswith("-py3-none-any.whl"))


if __name__ == "__main__":
    unittest.main()
