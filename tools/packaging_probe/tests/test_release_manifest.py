from __future__ import annotations

import hashlib
import json
import os
import tempfile
import unittest
from pathlib import Path
from typing import cast
from unittest.mock import patch

from tools.packaging_probe.check_artifact import ArtifactReport
from tools.packaging_probe.release_manifest import (
    _INSTALLED_WP18_CONTRACT,
    _MATERIAL_FILES,
    ReleaseManifestError,
    _build_provenance,
    _checkout_provenance,
    _hash_regular,
    _read_regular,
    _workflow_actions,
    create_release_bundle,
    verify_release_bundle,
)

_REVISION = "a" * 40
_VERSION = "0.1.2"
_NATIVE_PLATFORMS = (
    "manylinux_2_17_x86_64",
    "manylinux_2_17_aarch64",
    "musllinux_1_2_x86_64",
    "musllinux_1_2_aarch64",
    "macosx_10_12_x86_64",
    "macosx_11_0_arm64",
    "win_amd64",
    "win_arm64",
)


def _artifact_report(path: Path) -> ArtifactReport:
    if path.name.endswith(".tar.gz"):
        kind = "sdist"
        tags: tuple[str, ...] = ()
    elif path.name.endswith("-py3-none-any.whl"):
        kind = "pure-wheel"
        tags = ("py3-none-any",)
    else:
        kind = "native-wheel"
        platform = path.name.removesuffix(".whl").split("-cp310-abi3-", 1)[1]
        tags = (f"cp310-abi3-{platform}",)
    return ArtifactReport(
        artifact=path.name,
        kind=kind,
        name="pyHermiT",
        version=_VERSION,
        requires_python=">=3.10",
        tags=tags,
        native_members=(),
        python_hashes={},
        license_hashes={},
        metadata_sha256="0" * 64,
        archive_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
    )


def _sbom_binding(
    _root: Path,
    bundle: Path,
    revision: str,
    _snapshots: object,
) -> dict[str, object]:
    payload = (bundle / "release-sbom.spdx.json").read_bytes()
    return {
        "document_namespace": f"https://github.com/OAEI-ML/pyHermiT/sbom/{revision}",
        "file": "release-sbom.spdx.json",
        "sha256": hashlib.sha256(payload).hexdigest(),
        "size": len(payload),
    }


class ReleaseManifestTests(unittest.TestCase):
    def setUp(self) -> None:
        self.root = Path(__file__).parents[3]

    def _stage_bundle(self, directory: Path) -> None:
        names = [
            f"pyhermit-{_VERSION}-py3-none-any.whl",
            f"pyhermit-{_VERSION}.tar.gz",
            *(f"pyhermit-{_VERSION}-cp310-abi3-{platform}.whl" for platform in _NATIVE_PLATFORMS),
        ]
        for index, name in enumerate(names):
            (directory / name).write_bytes(f"artifact-{index}\n".encode())
        (directory / "release-sbom.spdx.json").write_text("{}\n", encoding="utf-8")

    def test_release_bundle_is_complete_deterministic_and_tamper_evident(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            bundle = Path(temporary)
            self._stage_bundle(bundle)
            with (
                patch(
                    "tools.packaging_probe.release_manifest.inspect_artifact",
                    side_effect=_artifact_report,
                ),
                patch(
                    "tools.packaging_probe.release_manifest._validated_sbom_binding",
                    side_effect=_sbom_binding,
                ),
                patch(
                    "tools.packaging_probe.release_manifest._checkout_provenance",
                    return_value="b" * 40,
                ),
            ):
                created = create_release_bundle(self.root, bundle, _REVISION)
                verified = verify_release_bundle(self.root, bundle, _REVISION)

                self.assertEqual(created, verified)
                self.assertEqual(created["schema"], 2)
                self.assertEqual(len(cast(list[object], created["artifacts"])), 10)
                self.assertEqual(created["distribution"], {"name": "pyHermiT", "version": _VERSION})
                self.assertEqual(
                    len((bundle / "SHA256SUMS").read_text(encoding="utf-8").splitlines()),
                    12,
                )

                target = bundle / f"pyhermit-{_VERSION}-py3-none-any.whl"
                target.write_bytes(b"tampered\n")
                with self.assertRaisesRegex(ReleaseManifestError, "manifest differs"):
                    verify_release_bundle(self.root, bundle, _REVISION)

    def test_release_bundle_rejects_unbound_members(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            bundle = Path(temporary)
            self._stage_bundle(bundle)
            (bundle / "unreviewed.txt").write_text("surprise", encoding="utf-8")
            with (
                patch(
                    "tools.packaging_probe.release_manifest._checkout_provenance",
                    return_value="b" * 40,
                ),
                self.assertRaisesRegex(ReleaseManifestError, "unexpected"),
            ):
                create_release_bundle(self.root, bundle, _REVISION)

    def test_release_bundle_rejects_member_added_after_initial_enumeration(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            bundle = Path(temporary)
            self._stage_bundle(bundle)

            def adding_sbom_binding(
                root: Path,
                staged: Path,
                revision: str,
                snapshots: object,
            ) -> dict[str, object]:
                binding = _sbom_binding(root, staged, revision, snapshots)
                (staged / "late-unbound.txt").write_text("late", encoding="utf-8")
                return binding

            with (
                patch(
                    "tools.packaging_probe.release_manifest.inspect_artifact",
                    side_effect=_artifact_report,
                ),
                patch(
                    "tools.packaging_probe.release_manifest._validated_sbom_binding",
                    side_effect=adding_sbom_binding,
                ),
                patch(
                    "tools.packaging_probe.release_manifest._checkout_provenance",
                    return_value="b" * 40,
                ),
                self.assertRaisesRegex(ReleaseManifestError, "member set changed"),
            ):
                create_release_bundle(self.root, bundle, _REVISION)

    def test_release_file_binding_rejects_symlinks(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            target = directory / "target.whl"
            target.write_bytes(b"artifact")
            alias = directory / "alias.whl"
            alias.symlink_to(target)

            with self.assertRaisesRegex(ReleaseManifestError, "not a regular file"):
                _hash_regular(alias)

    def test_release_hash_rejects_path_replacement_during_read(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            path = directory / "artifact.whl"
            path.write_bytes(b"original artifact")
            moved = directory / "original.whl"
            original_read = os.read
            replaced = False

            def replacing_read(descriptor: int, size: int) -> bytes:
                nonlocal replaced
                if not replaced:
                    path.replace(moved)
                    path.write_bytes(b"replacement artifact")
                    replaced = True
                return original_read(descriptor, size)

            with (
                patch(
                    "tools.packaging_probe.release_manifest.os.read",
                    side_effect=replacing_read,
                ),
                self.assertRaisesRegex(ReleaseManifestError, "pathname changed while hashing"),
            ):
                _hash_regular(path)

    def test_release_metadata_read_rejects_path_replacement(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            path = directory / "metadata.json"
            path.write_bytes(b'{"original": true}\n')
            moved = directory / "original.json"
            original_read = os.read
            replaced = False

            def replacing_read(descriptor: int, size: int) -> bytes:
                nonlocal replaced
                if not replaced:
                    path.replace(moved)
                    path.write_bytes(b'{"replacement": true}\n')
                    replaced = True
                return original_read(descriptor, size)

            with (
                patch(
                    "tools.packaging_probe.release_manifest.os.read",
                    side_effect=replacing_read,
                ),
                self.assertRaisesRegex(ReleaseManifestError, "pathname changed while reading"),
            ):
                _read_regular(path)

    def test_release_artifact_cannot_change_between_hash_and_inspection(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            bundle = Path(temporary)
            self._stage_bundle(bundle)
            target = bundle / f"pyhermit-{_VERSION}-py3-none-any.whl"
            moved = bundle / "original-pure.whl"
            replaced = False

            def replacing_inspection(path: Path) -> ArtifactReport:
                nonlocal replaced
                if path == target and not replaced:
                    path.replace(moved)
                    path.write_bytes(b"replacement")
                    replaced = True
                return _artifact_report(path)

            with (
                patch(
                    "tools.packaging_probe.release_manifest.inspect_artifact",
                    side_effect=replacing_inspection,
                ),
                patch(
                    "tools.packaging_probe.release_manifest._checkout_provenance",
                    return_value="b" * 40,
                ),
                self.assertRaisesRegex(
                    ReleaseManifestError,
                    "changed between hashing and inspection",
                ),
            ):
                create_release_bundle(self.root, bundle, _REVISION)

    def test_release_revision_must_be_a_complete_git_sha(self) -> None:
        with (
            tempfile.TemporaryDirectory() as temporary,
            self.assertRaisesRegex(ReleaseManifestError, "complete lowercase Git SHA"),
        ):
            create_release_bundle(self.root, Path(temporary), "main")

    def test_release_revision_must_match_checkout_head(self) -> None:
        with self.assertRaisesRegex(ReleaseManifestError, "differs from checkout HEAD"):
            _checkout_provenance(self.root, "0" * 40)

    def test_build_provenance_binds_tools_actions_and_rustup_installers(self) -> None:
        provenance = _build_provenance(self.root)

        self.assertEqual(provenance["release_rust"], "1.97.1")
        self.assertEqual(provenance["rustup"], "1.28.2")
        self.assertEqual(
            provenance["installed_native_contracts"],
            [
                {
                    "capability": "encoded-structural-compiler-v1",
                    "capability_state": "advertised",
                    "command": _INSTALLED_WP18_CONTRACT,
                    "id": "wp18-encoded-public-dispatch-short",
                    "scope": "installed-public-dispatch-short",
                }
            ],
        )
        self.assertIn(
            "tests/differential/encoded_compiler/test_permanent_program_assembly.py",
            _MATERIAL_FILES,
        )
        self.assertIn("tests/packaging/installed_smoke.py", _MATERIAL_FILES)
        self.assertIn("release/core-compatibility.json", _MATERIAL_FILES)
        self.assertEqual(
            provenance["tested_runtime"],
            {
                "pyowl_core": {
                    "commit": "b0d8fd27537b2f177cfe9a5e0fd41f33b9f18f19",
                    "repository": "https://github.com/OAEI-ML/pyOWLCore",
                    "tree": "e72fc93248cd363a5c67dac9efffb367a71c2b1d",
                    "version": "0.1.1",
                }
            },
        )
        self.assertEqual(
            provenance["encoded_ingestion_contract"],
            {
                "capability_state": "advertised",
                "descriptor_sha256": (
                    "9ad29db6a7e616f65cea2957bc5ba8d1f9b99ef0eb1fe1432c09be25786267b5"
                ),
                "parity_contract": "wp18-encoded-public-dispatch-short",
                "required_ingestion_path": "encoded-native",
                "schema_name": "pyowl-core/structural-columns",
                "schema_version": 1,
            },
        )
        self.assertEqual(
            provenance["musllinux_smoke_image"],
            {
                "digest": (
                    "sha256:6d43704baacd1bfbe7c295d7f13079d5d8104ed33568873133f8fc69980419df"
                ),
                "repository": "docker.io/library/python",
                "tag": "3.12.13-alpine3.24",
            },
        )
        self.assertEqual(
            provenance["release_verifier_requirements"],
            [
                {
                    "name": "packaging",
                    "sha256": ("5fc45236b9446107ff2415ce77c807cee2862cb6fac22b8a73826d0693b0980e"),
                    "version": "26.2",
                }
            ],
        )
        self.assertEqual(
            len(cast(list[str], provenance["rustup_installer_sha256"])),
            4,
        )
        actions = cast(list[object], provenance["workflow_actions"])
        self.assertTrue(
            any(
                isinstance(action, dict)
                and action.get("action") == "pypa/cibuildwheel"
                and len(str(action.get("revision"))) == 40
                for action in actions
            )
        )

    def test_missing_installed_wp18_contract_is_rejected(self) -> None:
        pyproject = (self.root / "pyproject.toml").read_bytes()
        mutated = pyproject.replace(
            _INSTALLED_WP18_CONTRACT.encode(),
            b"python -m pytest tests/unit",
        )
        self.assertNotEqual(mutated, pyproject)

        def material_payload(
            root: Path,
            _snapshots: object,
            relative: str,
        ) -> bytes:
            if relative == "pyproject.toml":
                return mutated
            return (root / relative).read_bytes()

        with (
            patch(
                "tools.packaging_probe.release_manifest._material_payload",
                side_effect=material_payload,
            ),
            self.assertRaisesRegex(
                ReleaseManifestError,
                "bounded WP18 encoded public-dispatch contract",
            ),
        ):
            _build_provenance(self.root)

    def test_release_workflow_cannot_float_the_provenance_bound_core_version(self) -> None:
        workflow = (self.root / ".github/workflows/wheels.yml").read_bytes()
        mutated = workflow.replace(
            b'"pyowl-core==0.1.1"',
            b'"pyowl-core>=0.1,<0.2"',
            1,
        )
        self.assertNotEqual(mutated, workflow)

        def material_payload(
            root: Path,
            _snapshots: object,
            relative: str,
        ) -> bytes:
            if relative == ".github/workflows/wheels.yml":
                return mutated
            return (root / relative).read_bytes()

        with (
            patch(
                "tools.packaging_probe.release_manifest._material_payload",
                side_effect=material_payload,
            ),
            self.assertRaisesRegex(
                ReleaseManifestError,
                "exact provenance-bound pyowl-core release",
            ),
        ):
            _build_provenance(self.root)

    def test_unbound_core_implementation_is_rejected(self) -> None:
        compatibility = (self.root / "release/core-compatibility.json").read_bytes()
        mutated = compatibility.replace(
            b"b0d8fd27537b2f177cfe9a5e0fd41f33b9f18f19",
            b"a0d8fd27537b2f177cfe9a5e0fd41f33b9f18f19",
        )
        self.assertNotEqual(mutated, compatibility)

        def material_payload(
            root: Path,
            _snapshots: object,
            relative: str,
        ) -> bytes:
            if relative == "release/core-compatibility.json":
                return mutated
            return (root / relative).read_bytes()

        with (
            patch(
                "tools.packaging_probe.release_manifest._material_payload",
                side_effect=material_payload,
            ),
            self.assertRaisesRegex(ReleaseManifestError, "core compatibility pin"),
        ):
            _build_provenance(self.root)

    def test_divergent_core_tree_or_encoded_contract_is_rejected(self) -> None:
        compatibility = (self.root / "release/core-compatibility.json").read_bytes()
        mutations = (
            (
                b"e72fc93248cd363a5c67dac9efffb367a71c2b1d",
                b"f72fc93248cd363a5c67dac9efffb367a71c2b1d",
            ),
            (
                b"9ad29db6a7e616f65cea2957bc5ba8d1f9b99ef0eb1fe1432c09be25786267b5",
                b"8ad29db6a7e616f65cea2957bc5ba8d1f9b99ef0eb1fe1432c09be25786267b5",
            ),
            (b"encoded-native", b"scalar-wire"),
        )
        for bound_value, replacement in mutations:
            with self.subTest(bound_value=bound_value):
                mutated = compatibility.replace(bound_value, replacement)
                self.assertNotEqual(mutated, compatibility)

                def material_payload(
                    root: Path,
                    _snapshots: object,
                    relative: str,
                    mutated_payload: bytes = mutated,
                ) -> bytes:
                    if relative == "release/core-compatibility.json":
                        return mutated_payload
                    return (root / relative).read_bytes()

                with (
                    patch(
                        "tools.packaging_probe.release_manifest._material_payload",
                        side_effect=material_payload,
                    ),
                    self.assertRaisesRegex(
                        ReleaseManifestError,
                        "core compatibility pin",
                    ),
                ):
                    _build_provenance(self.root)

    def test_mutable_musllinux_smoke_image_is_rejected(self) -> None:
        workflow = (self.root / ".github/workflows/wheels.yml").read_bytes()
        mutated = workflow.replace(
            (
                b"docker.io/library/python:3.12.13-alpine3.24"
                b"@sha256:6d43704baacd1bfbe7c295d7f13079d5d8104ed33568873133f8fc69980419df"
            ),
            b"python:3.12-alpine",
        )

        def material_payload(
            root: Path,
            _snapshots: object,
            relative: str,
        ) -> bytes:
            if relative == ".github/workflows/wheels.yml":
                return mutated
            return (root / relative).read_bytes()

        with (
            patch(
                "tools.packaging_probe.release_manifest._material_payload",
                side_effect=material_payload,
            ),
            self.assertRaisesRegex(ReleaseManifestError, "audited version and index digest"),
        ):
            _build_provenance(self.root)

    def test_attestation_job_reverifies_the_hash_locked_bundle(self) -> None:
        release_workflow = (self.root / ".github/workflows/release.yml").read_text(encoding="utf-8")
        attestation_job = release_workflow.split("  attest-candidate:\n", 1)[1].split(
            "  publish-pypi:\n", 1
        )[0]

        self.assertIn("--require-hashes", attestation_job)
        self.assertIn("release-verifier-requirements.txt", attestation_job)
        self.assertLess(
            attestation_job.index("python -m tools.packaging_probe.release_manifest"),
            attestation_job.index("uses: actions/attest-build-provenance@"),
        )

    def test_publication_job_reverifies_after_attestation_and_requires_a_tag(self) -> None:
        release_workflow = (self.root / ".github/workflows/release.yml").read_text(encoding="utf-8")
        publication_job = release_workflow.split("  publish-pypi:\n", 1)[1]

        self.assertIn("needs: attest-candidate", publication_job)
        self.assertIn("--require-hashes", publication_job)
        self.assertIn('RELEASE_REF"].startswith("refs/tags/v")', publication_job)
        self.assertLess(
            publication_job.index("python -m tools.packaging_probe.release_manifest"),
            publication_job.index("uses: pypa/gh-action-pypi-publish@"),
        )

    def test_workflow_action_tags_are_rejected_as_mutable(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            workflows = root / ".github/workflows"
            workflows.mkdir(parents=True)
            (workflows / "wheels.yml").write_text(
                "steps:\n  - uses: actions/checkout@v6\n",
                encoding="utf-8",
            )
            (workflows / "release.yml").write_text("jobs: {}\n", encoding="utf-8")

            with self.assertRaisesRegex(ReleaseManifestError, "not commit-pinned"):
                _workflow_actions(root)

    def test_manifest_json_is_canonical(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            bundle = Path(temporary)
            self._stage_bundle(bundle)
            with (
                patch(
                    "tools.packaging_probe.release_manifest.inspect_artifact",
                    side_effect=_artifact_report,
                ),
                patch(
                    "tools.packaging_probe.release_manifest._validated_sbom_binding",
                    side_effect=_sbom_binding,
                ),
                patch(
                    "tools.packaging_probe.release_manifest._checkout_provenance",
                    return_value="b" * 40,
                ),
            ):
                created = create_release_bundle(self.root, bundle, _REVISION)

            manifest = (bundle / "release-manifest.json").read_text(encoding="utf-8")
            self.assertEqual(manifest, json.dumps(created, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    unittest.main()
