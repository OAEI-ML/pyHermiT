from __future__ import annotations

import json
import os
import subprocess
import sys
import unittest

from tools.specs._compat import repository_root


class FoundationTests(unittest.TestCase):
    def test_import_is_inert_and_exports_only_version(self) -> None:
        root = repository_root()
        environment = os.environ.copy()
        environment["PYTHONPATH"] = str(root / "src")
        code = """
import json, sys
before = set(sys.modules)
import pyhermit
added = sorted(set(sys.modules) - before)
for forbidden in (
    'pyowl_core', 'setuptools', 'setuptools_rust', 'socket', 'subprocess',
    'pyhermit.backends',
):
    assert forbidden not in added, (forbidden, added)
assert pyhermit.__all__ == ['__version__']
assert pyhermit.__version__ == '0.1.0.dev0'
print(json.dumps(added))
"""
        result = subprocess.run(
            [sys.executable, "-I", "-c", code],
            check=False,
            cwd=root,
            env=environment,
            text=True,
            capture_output=True,
        )
        # Isolated mode ignores PYTHONPATH, so explicitly prepend only the local src tree.
        if result.returncode != 0 and "No module named 'pyhermit'" in result.stderr:
            isolated_code = f"sys.path.insert(0, {str(root / 'src')!r});\n" + code
            result = subprocess.run(
                [sys.executable, "-I", "-c", "import sys\n" + isolated_code],
                check=False,
                cwd=root,
                text=True,
                capture_output=True,
            )
        self.assertEqual(result.returncode, 0, result.stderr)
        added = set(json.loads(result.stdout))
        self.assertIn("pyhermit", added)
        self.assertLessEqual(added, {"__future__", "pyhermit"})

    def test_main_setup_build_modes_fail_closed(self) -> None:
        root = repository_root()
        expectations = {"0": True, "auto": True, "1": False, "invalid": False}
        for mode, expected_success in expectations.items():
            with self.subTest(mode=mode):
                environment = os.environ.copy()
                environment["PYHERMIT_BUILD_NATIVE"] = mode
                result = subprocess.run(
                    [sys.executable, "setup.py", "--name"],
                    check=False,
                    cwd=root,
                    env=environment,
                    text=True,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.STDOUT,
                )
                self.assertEqual(result.returncode == 0, expected_success, result.stdout)
                if expected_success:
                    self.assertIn("pyHermiT", result.stdout)

    def test_package_marker_and_type_marker_exist(self) -> None:
        package = repository_root() / "src/pyhermit"
        self.assertTrue((package / "__init__.py").is_file())
        self.assertTrue((package / "py.typed").is_file())
        self.assertFalse((package / "api.py").exists())
        self.assertFalse((repository_root() / "native").exists())


if __name__ == "__main__":
    unittest.main()
