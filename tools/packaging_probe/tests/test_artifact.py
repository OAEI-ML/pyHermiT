from __future__ import annotations

import io
import tarfile
import tempfile
import unittest
import zipfile
from pathlib import Path

from tools.packaging_probe.check_artifact import (
    ArtifactError,
    _check_runtime_dependencies,
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
