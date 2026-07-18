from __future__ import annotations

import io
import tarfile
import tempfile
import unittest
import zipfile
from pathlib import Path

from tools.packaging_probe.check_artifact import (
    ArchiveContent,
    ArtifactError,
    _check_runtime_dependencies,
    _contains_absolute_path,
    _runtime_version,
    _wheel_tags,
    inspect_artifact,
)


class ArtifactCheckerTests(unittest.TestCase):
    def test_pep_508_dependency_specifier_is_parsed(self) -> None:
        _check_runtime_dependencies(
            "\n".join(
                (
                    "Requires-Python: >=3.10",
                    "License-Expression: LGPL-3.0-or-later",
                    "Requires-Dist: pyowl-core<0.2,>=0.1",
                    "",
                )
            )
        )

    def test_runtime_version_source_is_parsed_without_importing_package(self) -> None:
        self.assertEqual(_runtime_version(b'__version__ = "0.1.0.dev0"\n'), "0.1.0.dev0")

    def test_runtime_dependency_range_must_be_exact(self) -> None:
        with self.assertRaisesRegex(ArtifactError, "exactly"):
            _check_runtime_dependencies("Requires-Dist: pyowl-core>=0.1\n")

    def test_unexpected_runtime_dependency_is_rejected(self) -> None:
        with self.assertRaisesRegex(ArtifactError, "outside pyowl-core"):
            _check_runtime_dependencies(
                "Requires-Dist: pyowl-core>=0.1,<0.2\nRequires-Dist: requests>=2\n"
            )

    def test_dev_extra_dependency_is_not_treated_as_runtime(self) -> None:
        _check_runtime_dependencies(
            'Requires-Dist: pyowl-core>=0.1,<0.2\nRequires-Dist: pytest; extra == "dev"\n'
        )

    def test_wheel_filename_version_must_match_metadata(self) -> None:
        content = ArchiveContent(
            {
                "pyhermit-0.1.0.dev0.dist-info/METADATA": b"",
                "pyhermit-0.1.0.dev0.dist-info/WHEEL": b"Tag: py3-none-any\n",
            }
        )
        with self.assertRaisesRegex(ArtifactError, "versions differ"):
            _wheel_tags(
                Path("pyhermit-9.0-py3-none-any.whl"),
                content,
                metadata_name="pyHermiT",
                metadata_version="0.1.0.dev0",
            )

    def test_java_member_is_rejected_before_metadata_trust(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            wheel = Path(temporary) / "bad-0-py3-none-any.whl"
            with zipfile.ZipFile(wheel, "w") as archive:
                archive.writestr("payload/reasoner.jar", b"not really a jar")

            with self.assertRaisesRegex(ArtifactError, "Java artifact"):
                inspect_artifact(wheel, pure=True)

    def test_parent_archive_member_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            wheel = Path(temporary) / "bad-0-py3-none-any.whl"
            with zipfile.ZipFile(wheel, "w") as archive:
                archive.writestr("../outside", b"payload")

            with self.assertRaisesRegex(ArtifactError, "unsafe archive member"):
                inspect_artifact(wheel, pure=True)

    def test_cibuildwheel_absolute_path_is_rejected_before_metadata_trust(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            wheel = Path(temporary) / "bad-0-py3-none-any.whl"
            with zipfile.ZipFile(wheel, "w") as archive:
                archive.writestr("payload/module.py", b"compiled from /project/src/lib.rs")

            with self.assertRaisesRegex(ArtifactError, "absolute build path"):
                inspect_artifact(wheel, pure=True)

    def test_project_path_marker_does_not_match_urls_or_relative_paths(self) -> None:
        marker = b"/project/"
        self.assertFalse(_contains_absolute_path(b"https://pypi.org/project/build/", marker))
        self.assertFalse(_contains_absolute_path(b"tools/packaging_probe/project/native", marker))
        self.assertTrue(_contains_absolute_path(b"compiled from /project/src/lib.rs", marker))

    def test_packaging_probe_is_rejected_from_sdist(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            sdist = Path(temporary) / "bad-0.tar.gz"
            with tarfile.open(sdist, "w:gz") as archive:
                payload = b"probe"
                info = tarfile.TarInfo("bad-0/tools/packaging_probe/README.md")
                info.size = len(payload)
                archive.addfile(info, io.BytesIO(payload))

            with self.assertRaisesRegex(ArtifactError, "packaging probe"):
                inspect_artifact(sdist)


if __name__ == "__main__":
    unittest.main()
