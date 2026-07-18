from __future__ import annotations

import configparser
import json
import os
import subprocess
import sys
import unittest

from tools.specs._compat import repository_root


class FoundationTests(unittest.TestCase):
    def test_public_import_is_java_free_and_does_not_load_native_extension(self) -> None:
        root = repository_root()
        core_src = root.parent / "pyOWLCore" / "src"
        code = """
import json, sys
before = set(sys.modules)
import pyhermit
added = sorted(set(sys.modules) - before)
for forbidden in (
    'jpype', 'owlready2', 'rdflib', 'requests', 'setuptools', 'setuptools_rust',
    'pyhermit._native', 'pyhermit.backends.native',
):
    assert forbidden not in added, (forbidden, added)
assert 'Reasoner' in pyhermit.__all__
assert 'backend_info' in pyhermit.__all__
assert pyhermit.__version__ == '0.1.0.dev0'
print(json.dumps(added))
"""
        # Isolated mode prevents editable-install state from hiding import side effects.
        isolated_code = (
            f"sys.path.insert(0, {str(core_src)!r});\n"
            f"sys.path.insert(0, {str(root / 'src')!r});\n" + code
        )
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
        self.assertIn("pyowl_core", added)
        self.assertNotIn("pyhermit._native", added)

    def test_main_setup_build_modes_fail_closed(self) -> None:
        root = repository_root()
        expectations = {"0": True, "auto": True, "1": True, "invalid": False}
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
        self.assertTrue((package / "facade.py").is_file())
        self.assertTrue((package / "py.typed").is_file())
        self.assertFalse((package / "api.py").exists())
        self.assertTrue((repository_root() / "native" / "Cargo.toml").is_file())

    def test_native_wheel_uses_the_python_310_stable_abi(self) -> None:
        configuration = configparser.ConfigParser()
        loaded = configuration.read(repository_root() / "setup.cfg")

        self.assertEqual(len(loaded), 1)
        self.assertEqual(configuration["bdist_wheel"]["py_limited_api"], "cp310")


if __name__ == "__main__":
    unittest.main()
