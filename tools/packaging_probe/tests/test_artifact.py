from __future__ import annotations

import hashlib
import io
import os
import subprocess
import tarfile
import tempfile
import unittest
import zipfile
from pathlib import Path
from unittest import mock

from tools.packaging_probe.check_artifact import (
    ArchiveContent,
    ArtifactError,
    ArtifactReport,
    _check_runtime_dependencies,
    _contains_absolute_path,
    _license_hashes,
    _runtime_version,
    _wheel_tags,
    external_audit,
    inspect_artifact,
)


class ArtifactCheckerTests(unittest.TestCase):
    def test_license_payloads_are_content_checked(self) -> None:
        root = Path(__file__).parents[3]
        prefix = "pyhermit-0.dist-info/licenses"
        content = ArchiveContent(
            {
                f"{prefix}/{name}": (root / name).read_bytes()
                for name in ("LICENSE", "COPYING", "NOTICE.md")
            }
        )

        hashes = _license_hashes(content, wheel=True)

        self.assertEqual(set(hashes), {"LICENSE", "COPYING", "NOTICE.md"})
        self.assertTrue(all(len(value) == 64 for value in hashes.values()))

    def test_incomplete_notice_payload_is_rejected(self) -> None:
        root = Path(__file__).parents[3]
        prefix = "pyhermit-0.dist-info/licenses"
        content = ArchiveContent(
            {
                f"{prefix}/LICENSE": (root / "LICENSE").read_bytes(),
                f"{prefix}/COPYING": (root / "COPYING").read_bytes(),
                f"{prefix}/NOTICE.md": b"LGPL-3.0-or-later only",
            }
        )

        with self.assertRaisesRegex(ArtifactError, "missing required provenance"):
            _license_hashes(content, wheel=True)

    def test_modified_complete_notice_payload_is_rejected(self) -> None:
        root = Path(__file__).parents[3]
        prefix = "pyhermit-0.dist-info/licenses"
        content = ArchiveContent(
            {
                f"{prefix}/LICENSE": (root / "LICENSE").read_bytes(),
                f"{prefix}/COPYING": (root / "COPYING").read_bytes(),
                f"{prefix}/NOTICE.md": (root / "NOTICE.md").read_bytes() + b"\n",
            }
        )

        with self.assertRaisesRegex(ArtifactError, "payload identity"):
            _license_hashes(content, wheel=True)

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
        self.assertEqual(_runtime_version(b'__version__ = "0.1.1"\n'), "0.1.1")

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
                "pyhermit-0.1.1.dist-info/METADATA": b"",
                "pyhermit-0.1.1.dist-info/WHEEL": b"Tag: py3-none-any\n",
            }
        )
        with self.assertRaisesRegex(ArtifactError, "versions differ"):
            _wheel_tags(
                Path("pyhermit-9.0-py3-none-any.whl"),
                content,
                metadata_name="pyHermiT",
                metadata_version="0.1.1",
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

    def test_artifact_leaf_symlink_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            target = root / "target.whl"
            target.write_bytes(b"not a wheel")
            alias = root / "alias.whl"
            alias.symlink_to(target)

            with self.assertRaisesRegex(ArtifactError, "not a regular file"):
                inspect_artifact(alias)

    def test_artifact_swap_during_snapshot_read_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            wheel = root / "candidate.whl"
            wheel.write_bytes(b"original candidate bytes")
            replacement = root / "replacement.whl"
            replacement.write_bytes(b"replacement candidate")
            original_read = os.read
            swapped = False

            def swapping_read(descriptor: int, size: int) -> bytes:
                nonlocal swapped
                chunk = original_read(descriptor, size)
                if chunk and not swapped:
                    swapped = True
                    replacement.replace(wheel)
                return chunk

            with (
                mock.patch(
                    "tools.packaging_probe.check_artifact.os.read",
                    side_effect=swapping_read,
                ),
                self.assertRaisesRegex(ArtifactError, "pathname changed while reading"),
            ):
                inspect_artifact(wheel)

    def test_archive_digest_and_parser_share_one_snapshot(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            wheel = root / "candidate.whl"
            original = b"original candidate bytes"
            wheel.write_bytes(original)
            replacement = root / "replacement.whl"
            replacement.write_bytes(b"replacement candidate")

            def swapping_parser(path: Path, payload: bytes) -> ArchiveContent:
                self.assertEqual(payload, original)
                replacement.replace(path)
                return ArchiveContent({})

            expected_digest = hashlib.sha256(original).hexdigest()
            report = ArtifactReport(
                artifact=wheel.name,
                kind="pure-wheel",
                name="pyHermiT",
                version="0.1.1",
                requires_python=">=3.10",
                tags=("py3-none-any",),
                native_members=(),
                python_hashes={},
                license_hashes={},
                metadata_sha256="0" * 64,
                archive_sha256=expected_digest,
            )

            with (
                mock.patch(
                    "tools.packaging_probe.check_artifact._read_wheel",
                    side_effect=swapping_parser,
                ),
                mock.patch(
                    "tools.packaging_probe.check_artifact._check_names_and_payloads",
                    return_value=(),
                ),
                mock.patch(
                    "tools.packaging_probe.check_artifact._inspect_wheel",
                    return_value=report,
                ) as inspect_wheel,
            ):
                actual = inspect_artifact(wheel)

            self.assertEqual(actual.archive_sha256, expected_digest)
            self.assertEqual(
                inspect_wheel.call_args.kwargs["archive_sha256"],
                expected_digest,
            )

    def test_external_audit_rejects_artifact_mutation(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            wheel = root / "candidate.whl"
            original = b"original candidate bytes"
            wheel.write_bytes(original)
            replacement = root / "replacement.whl"
            replacement.write_bytes(b"replacement candidate")
            digest = hashlib.sha256(original).hexdigest()
            report = ArtifactReport(
                artifact=wheel.name,
                kind="native-wheel",
                name="pyHermiT",
                version="0.1.1",
                requires_python=">=3.10",
                tags=("cp310-abi3-manylinux_2_17_x86_64",),
                native_members=("pyhermit/_native.abi3.so",),
                python_hashes={},
                license_hashes={},
                metadata_sha256="0" * 64,
                archive_sha256=digest,
            )

            def mutating_auditor(
                command: list[str],
                **_: object,
            ) -> subprocess.CompletedProcess[str]:
                replacement.replace(wheel)
                return subprocess.CompletedProcess(command, 0, "")

            with (
                mock.patch(
                    "tools.packaging_probe.check_artifact._inspect_snapshot",
                    return_value=report,
                ),
                mock.patch(
                    "tools.packaging_probe.check_artifact.shutil.which",
                    return_value="/audit/tool",
                ),
                mock.patch(
                    "tools.packaging_probe.check_artifact.subprocess.run",
                    side_effect=mutating_auditor,
                ),
                self.assertRaisesRegex(ArtifactError, "changed during external audit"),
            ):
                external_audit(wheel, expected_archive_sha256=digest)


if __name__ == "__main__":
    unittest.main()
