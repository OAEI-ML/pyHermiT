"""Create and verify the complete, provenance-bound pyHermiT release bundle.

This binds staged bytes to a clean checkout and its release recipes. The later hosted
attestation, rather than this local manifest, establishes build-run derivation.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import stat
import subprocess
from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from pathlib import Path
from typing import cast

from tools.packaging_probe.check_artifact import ArtifactReport, inspect_artifact
from tools.packaging_probe.create_sbom import create_sbom
from tools.specs._compat import (
    parse_toml,
    repository_root,
    require_list,
    require_mapping,
    require_str,
)

_SOURCE_DATE_EPOCH = 946684800
_MANIFEST_NAME = "release-manifest.json"
_CHECKSUM_NAME = "SHA256SUMS"
_SBOM_NAME = "release-sbom.spdx.json"
_MAX_METADATA_SIZE = 16 * 1024 * 1024
_MATERIAL_FILES = (
    ".github/workflows/release.yml",
    ".github/workflows/wheels.yml",
    "COPYING",
    "Cargo.toml",
    "LICENSE",
    "MANIFEST.in",
    "NOTICE.md",
    "deny.toml",
    "native/Cargo.lock",
    "native/Cargo.toml",
    "pyproject.toml",
    "reports/licensing/adapted-files.toml",
    "setup.cfg",
    "setup.py",
    "src/pyhermit/_version.py",
    "tools/packaging_probe/README.md",
    "tools/packaging_probe/check_artifact.py",
    "tools/packaging_probe/create_sbom.py",
    "tools/packaging_probe/release_manifest.py",
    "tools/specs/_compat.py",
    "tools/specs/dependencies.toml",
    "tools/specs/licensing.toml",
    "tools/specs/native-wheel-targets.toml",
    "tools/specs/rust-production-licenses.toml",
)
_SBOM_SOURCE_FILES = frozenset(
    {
        "native/Cargo.lock",
        "native/Cargo.toml",
        "pyproject.toml",
        "src/pyhermit/_version.py",
        "tools/specs/rust-production-licenses.toml",
    }
)
_EXPECTED_NATIVE_FAMILIES = frozenset(
    {
        "macos-arm64",
        "macos-x86_64",
        "manylinux-aarch64",
        "manylinux-x86_64",
        "musllinux-aarch64",
        "musllinux-x86_64",
        "windows-amd64",
        "windows-arm64",
    }
)
_EXPECTED_RUSTUP_HOSTS = frozenset(
    {
        "aarch64-unknown-linux-gnu",
        "aarch64-unknown-linux-musl",
        "x86_64-unknown-linux-gnu",
        "x86_64-unknown-linux-musl",
    }
)
_REQUIRED_WORKFLOW_TOOLS = frozenset(
    {
        "abi3audit==0.0.26",
        "auditwheel==6.7.0",
        "build==1.5.0",
        "delocate==0.13.0",
        "delvewheel==1.13.0",
        "setuptools-rust==1.13.0",
        "setuptools==83.0.0",
        "wheel==0.46.3",
    }
)


class ReleaseManifestError(ValueError):
    """A candidate release bundle is incomplete, mutable, or provenance-inconsistent."""


_FileIdentity = tuple[int, int, int, int, int, int]


@dataclass(frozen=True, slots=True)
class _MaterialSnapshot:
    payload: bytes
    identity: _FileIdentity


def _stat_identity(value: os.stat_result) -> _FileIdentity:
    return (
        value.st_mode,
        value.st_dev,
        value.st_ino,
        value.st_size,
        value.st_mtime_ns,
        value.st_ctime_ns,
    )


def _regular_lstat(path: Path) -> os.stat_result:
    try:
        result = path.lstat()
    except FileNotFoundError as error:
        raise ReleaseManifestError(f"release input does not exist: {path}") from error
    if not stat.S_ISREG(result.st_mode):
        raise ReleaseManifestError(f"release input is not a regular file: {path}")
    return result


def _regular_identity(path: Path) -> _FileIdentity:
    return _stat_identity(_regular_lstat(path))


def _confirm_regular_path(
    path: Path,
    opened: os.stat_result,
    completed: os.stat_result,
    operation: str,
) -> None:
    try:
        current = path.lstat()
    except FileNotFoundError as error:
        raise ReleaseManifestError(
            f"release input pathname changed while {operation}: {path}"
        ) from error
    identities = {
        _stat_identity(opened),
        _stat_identity(completed),
        _stat_identity(current),
    }
    if not stat.S_ISREG(current.st_mode) or len(identities) != 1:
        raise ReleaseManifestError(f"release input pathname changed while {operation}: {path}")


def _open_regular(path: Path) -> tuple[int, os.stat_result]:
    expected = _regular_lstat(path)
    flags = os.O_RDONLY | getattr(os, "O_CLOEXEC", 0) | getattr(os, "O_BINARY", 0)
    flags |= getattr(os, "O_NOFOLLOW", 0)
    try:
        descriptor = os.open(path, flags)
    except OSError as error:
        raise ReleaseManifestError(f"release input cannot be opened safely: {path}") from error
    opened = os.fstat(descriptor)
    if not stat.S_ISREG(opened.st_mode) or _stat_identity(expected) != _stat_identity(opened):
        os.close(descriptor)
        raise ReleaseManifestError(f"release input changed while opening: {path}")
    return descriptor, opened


def _hash_regular(path: Path) -> tuple[str, int]:
    descriptor, opened = _open_regular(path)
    digest = hashlib.sha256()
    try:
        while chunk := os.read(descriptor, 1024 * 1024):
            digest.update(chunk)
        completed = os.fstat(descriptor)
    finally:
        os.close(descriptor)
    _confirm_regular_path(path, opened, completed, "hashing")
    return digest.hexdigest(), completed.st_size


def _read_regular(path: Path) -> bytes:
    descriptor, opened = _open_regular(path)
    if opened.st_size > _MAX_METADATA_SIZE:
        os.close(descriptor)
        raise ReleaseManifestError(f"release metadata exceeds the size limit: {path}")
    chunks: list[bytes] = []
    try:
        while chunk := os.read(descriptor, 64 * 1024):
            chunks.append(chunk)
        completed = os.fstat(descriptor)
    finally:
        os.close(descriptor)
    _confirm_regular_path(path, opened, completed, "reading")
    return b"".join(chunks)


def _bundle_directory_identity(bundle: Path) -> _FileIdentity:
    try:
        result = bundle.lstat()
    except FileNotFoundError as error:
        raise ReleaseManifestError(f"release bundle does not exist: {bundle}") from error
    if bundle.is_symlink() or not stat.S_ISDIR(result.st_mode):
        raise ReleaseManifestError(f"release bundle is not a stable directory: {bundle}")
    return _stat_identity(result)


def _is_distribution(name: str) -> bool:
    return name.endswith(".whl") or name.endswith(".tar.gz")


def _bundle_distribution_paths(bundle: Path, *, allow_outputs: bool) -> tuple[Path, ...]:
    directory_identity = _bundle_directory_identity(bundle)
    distributions: list[Path] = []
    allowed_metadata = {_SBOM_NAME}
    if allow_outputs:
        allowed_metadata.update({_MANIFEST_NAME, _CHECKSUM_NAME})
    for path in sorted(bundle.iterdir(), key=lambda candidate: candidate.name):
        if _is_distribution(path.name):
            distributions.append(path)
        elif path.name not in allowed_metadata:
            raise ReleaseManifestError(f"unexpected release bundle member: {path.name}")
    if _bundle_directory_identity(bundle) != directory_identity:
        raise ReleaseManifestError("release bundle directory changed while enumerating")
    if len(distributions) != 10:
        raise ReleaseManifestError(
            f"release bundle must contain exactly ten distributions, found {len(distributions)}"
        )
    return tuple(distributions)


def _assert_exact_bundle_members(
    bundle: Path,
    distribution_paths: Sequence[Path],
    *,
    include_outputs: bool,
) -> None:
    expected = {path.name for path in distribution_paths}
    expected.add(_SBOM_NAME)
    if include_outputs:
        expected.update({_MANIFEST_NAME, _CHECKSUM_NAME})
    directory_identity = _bundle_directory_identity(bundle)
    actual = {path.name for path in bundle.iterdir()}
    if _bundle_directory_identity(bundle) != directory_identity:
        raise ReleaseManifestError("release bundle directory changed while re-enumerating")
    if actual != expected:
        raise ReleaseManifestError(
            "release bundle member set changed; "
            f"missing={sorted(expected - actual)}, extra={sorted(actual - expected)}"
        )


def _native_family(tags: Sequence[str]) -> str:
    families: set[str] = set()
    for tag in tags:
        parts = tag.split("-", 2)
        if len(parts) != 3 or parts[:2] != ["cp310", "abi3"]:
            raise ReleaseManifestError(f"native wheel has a non-abi3-py310 tag: {tag}")
        platform = parts[2]
        if platform.startswith("manylinux") and platform.endswith("_x86_64"):
            families.add("manylinux-x86_64")
        elif platform.startswith("manylinux") and platform.endswith("_aarch64"):
            families.add("manylinux-aarch64")
        elif platform.startswith("musllinux") and platform.endswith("_x86_64"):
            families.add("musllinux-x86_64")
        elif platform.startswith("musllinux") and platform.endswith("_aarch64"):
            families.add("musllinux-aarch64")
        elif platform.startswith("macosx") and platform.endswith("_x86_64"):
            families.add("macos-x86_64")
        elif platform.startswith("macosx") and platform.endswith("_arm64"):
            families.add("macos-arm64")
        elif platform == "win_amd64":
            families.add("windows-amd64")
        elif platform == "win_arm64":
            families.add("windows-arm64")
        else:
            raise ReleaseManifestError(f"native wheel has an unsupported platform tag: {tag}")
    if len(families) != 1:
        raise ReleaseManifestError(
            f"native wheel does not resolve to one target: {sorted(families)}"
        )
    return families.pop()


def _distribution_entries(paths: Sequence[Path]) -> tuple[list[dict[str, object]], str, str]:
    entries: list[dict[str, object]] = []
    reports: list[ArtifactReport] = []
    families: set[str] = set()
    kinds: dict[str, int] = {"native-wheel": 0, "pure-wheel": 0, "sdist": 0}
    for path in paths:
        identity = _regular_identity(path)
        digest, size = _hash_regular(path)
        if _regular_identity(path) != identity:
            raise ReleaseManifestError(f"artifact changed after hashing: {path.name}")
        report = inspect_artifact(path)
        if _regular_identity(path) != identity:
            raise ReleaseManifestError(
                f"artifact changed between hashing and inspection: {path.name}"
            )
        if report.archive_sha256 != digest:
            raise ReleaseManifestError(f"artifact inspection and digest differ for {path.name}")
        if report.artifact != path.name:
            raise ReleaseManifestError(f"artifact report filename differs for {path.name}")
        if report.kind not in kinds:
            raise ReleaseManifestError(f"unsupported release artifact kind: {report.kind}")
        kinds[report.kind] += 1
        if report.kind == "native-wheel":
            families.add(_native_family(report.tags))
        reports.append(report)
        entries.append(
            {
                "file": path.name,
                "kind": report.kind,
                "sha256": digest,
                "size": size,
                "tags": list(report.tags),
            }
        )
    if kinds != {"native-wheel": 8, "pure-wheel": 1, "sdist": 1}:
        raise ReleaseManifestError(f"release artifact kind counts are incomplete: {kinds}")
    if families != _EXPECTED_NATIVE_FAMILIES:
        raise ReleaseManifestError(
            "release native target set is incomplete; "
            f"missing={sorted(_EXPECTED_NATIVE_FAMILIES - families)}, "
            f"extra={sorted(families - _EXPECTED_NATIVE_FAMILIES)}"
        )
    identities = {(report.name, report.version, report.requires_python) for report in reports}
    if len(identities) != 1:
        raise ReleaseManifestError(f"release artifact identities differ: {sorted(identities)}")
    name, version, _requires_python = identities.pop()
    return entries, name, version


def _workflow_actions_from_texts(texts: Sequence[str]) -> list[dict[str, str]]:
    actions: set[tuple[str, str]] = set()
    pattern = re.compile(r"^\s*(?:-\s*)?uses:\s*(\S+)\s*(?:#.*)?$")
    for text in texts:
        for line in text.splitlines():
            match = pattern.fullmatch(line)
            if match is None:
                continue
            reference = match.group(1)
            if reference.startswith("./"):
                continue
            pinned = re.fullmatch(r"([^@]+)@([0-9a-f]{40})", reference)
            if pinned is None:
                raise ReleaseManifestError(f"workflow action is not commit-pinned: {reference}")
            actions.add((pinned.group(1), pinned.group(2)))
    if not actions:
        raise ReleaseManifestError("release workflows contain no external action provenance")
    return [{"action": action, "revision": revision} for action, revision in sorted(actions)]


def _workflow_actions(root: Path) -> list[dict[str, str]]:
    return _workflow_actions_from_texts(
        [
            _read_regular(root / relative).decode("utf-8")
            for relative in (".github/workflows/wheels.yml", ".github/workflows/release.yml")
        ]
    )


def _shell_assignment(script: str, name: str) -> str:
    matches = cast(
        list[str],
        re.findall(rf"(?m)^{re.escape(name)}=([A-Za-z0-9_.-]+)$", script),
    )
    if len(matches) != 1:
        raise ReleaseManifestError(f"Linux Rust bootstrap must set {name} exactly once")
    return matches[0]


def _material_payload(
    root: Path,
    snapshots: Mapping[str, _MaterialSnapshot] | None,
    relative: str,
) -> bytes:
    if snapshots is None:
        return _read_regular(root / relative)
    try:
        return snapshots[relative].payload
    except KeyError as error:
        raise ReleaseManifestError(f"release material snapshot is missing: {relative}") from error


def _build_provenance(
    root: Path,
    snapshots: Mapping[str, _MaterialSnapshot] | None = None,
) -> dict[str, object]:
    pyproject = parse_toml(_material_payload(root, snapshots, "pyproject.toml"))
    build_system = require_mapping(pyproject.get("build-system"), "build-system")
    backend = require_str(build_system.get("build-backend"), "build-system.build-backend")
    build_requirements = sorted(
        require_str(value, "build-system requirement")
        for value in require_list(build_system.get("requires"), "build-system.requires")
    )
    if not build_requirements or any(
        re.fullmatch(r"[A-Za-z0-9_.-]+==[A-Za-z0-9_.+-]+", requirement) is None
        for requirement in build_requirements
    ):
        raise ReleaseManifestError("every PEP 517 build requirement must be exactly pinned")

    workflow_text = _material_payload(
        root,
        snapshots,
        ".github/workflows/wheels.yml",
    ).decode("utf-8")
    workflow_tools = sorted(
        {
            f"{name}=={version}"
            for name, version in re.findall(
                r"(?<![A-Za-z0-9_.-])([A-Za-z0-9][A-Za-z0-9_.-]*)"
                r"==([A-Za-z0-9][A-Za-z0-9_.+-]*)",
                workflow_text,
            )
        }
    )
    missing_tools = _REQUIRED_WORKFLOW_TOOLS - set(workflow_tools)
    if missing_tools:
        raise ReleaseManifestError(
            f"release workflow omits pinned build/audit tools: {sorted(missing_tools)}"
        )

    tool = require_mapping(pyproject.get("tool"), "pyproject tool")
    cibuildwheel = require_mapping(tool.get("cibuildwheel"), "tool.cibuildwheel")
    linux = require_mapping(cibuildwheel.get("linux"), "tool.cibuildwheel.linux")
    before_all = require_str(linux.get("before-all"), "tool.cibuildwheel.linux.before-all")
    rustup_version = _shell_assignment(before_all, "rustup_version")
    rust_toolchain = _shell_assignment(before_all, "rust_toolchain")
    rustup_hosts = sorted(set(re.findall(r"rustup_host=([A-Za-z0-9_-]+)", before_all)))
    if set(rustup_hosts) != _EXPECTED_RUSTUP_HOSTS:
        raise ReleaseManifestError(f"Linux Rust bootstrap host set is incomplete: {rustup_hosts}")
    installer_checksums = sorted(set(re.findall(r"rustup_sha256=([0-9a-f]{64})", before_all)))
    if len(installer_checksums) != 4:
        raise ReleaseManifestError("Linux Rust bootstrap must bind four installer checksums")
    if (
        "https://static.rust-lang.org/rustup/archive/$rustup_version/$rustup_host/rustup-init"
        not in before_all
        or "sha256sum -c -" not in before_all
    ):
        raise ReleaseManifestError("Linux Rust bootstrap is not archive- and checksum-bound")

    cargo = parse_toml(_material_payload(root, snapshots, "Cargo.toml"))
    workspace = require_mapping(cargo.get("workspace"), "Cargo workspace")
    workspace_package = require_mapping(workspace.get("package"), "Cargo workspace package")
    minimum_rust = require_str(workspace_package.get("rust-version"), "Cargo rust-version")
    return {
        "build_backend": backend,
        "build_requirements": build_requirements,
        "minimum_rust": minimum_rust,
        "release_rust": rust_toolchain,
        "rustup": rustup_version,
        "rustup_hosts": rustup_hosts,
        "rustup_installer_sha256": installer_checksums,
        "workflow_actions": _workflow_actions_from_texts(
            [
                workflow_text,
                _material_payload(
                    root,
                    snapshots,
                    ".github/workflows/release.yml",
                ).decode("utf-8"),
            ]
        ),
        "workflow_python_tools": workflow_tools,
    }


def _capture_materials(
    root: Path,
) -> tuple[list[dict[str, object]], dict[str, _MaterialSnapshot]]:
    entries: list[dict[str, object]] = []
    snapshots: dict[str, _MaterialSnapshot] = {}
    for relative in _MATERIAL_FILES:
        path = root / relative
        identity = _regular_identity(path)
        payload = _read_regular(path)
        if _regular_identity(path) != identity:
            raise ReleaseManifestError(f"release material changed after capture: {relative}")
        snapshots[relative] = _MaterialSnapshot(payload=payload, identity=identity)
        entries.append(
            {
                "file": relative,
                "sha256": hashlib.sha256(payload).hexdigest(),
                "size": len(payload),
            }
        )
    return entries, snapshots


def _assert_snapshot_identities(
    root: Path,
    snapshots: Mapping[str, _MaterialSnapshot],
    relatives: Sequence[str],
) -> None:
    changed = sorted(
        relative
        for relative in relatives
        if _regular_identity(root / relative) != snapshots[relative].identity
    )
    if changed:
        raise ReleaseManifestError(f"release materials changed after capture: {changed}")


def _validated_sbom_binding(
    root: Path,
    bundle: Path,
    revision: str,
    snapshots: Mapping[str, _MaterialSnapshot],
) -> dict[str, object]:
    path = bundle / _SBOM_NAME
    raw = _read_regular(path)
    try:
        document: object = json.loads(raw)
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ReleaseManifestError("release SBOM is malformed") from error
    namespace = f"https://github.com/OAEI-ML/pyHermiT/sbom/{revision}"
    _assert_snapshot_identities(root, snapshots, sorted(_SBOM_SOURCE_FILES))
    expected = create_sbom(root, namespace)
    _assert_snapshot_identities(root, snapshots, sorted(_SBOM_SOURCE_FILES))
    if document != expected:
        raise ReleaseManifestError("release SBOM differs from the audited production closure")
    return {
        "document_namespace": namespace,
        "file": _SBOM_NAME,
        "sha256": hashlib.sha256(raw).hexdigest(),
        "size": len(raw),
    }


def _git_output(root: Path, *arguments: str) -> str:
    completed = subprocess.run(
        ["git", "-C", str(root), *arguments],
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
    )
    if completed.returncode != 0:
        raise ReleaseManifestError(
            f"Git could not establish release source provenance: {completed.stdout.strip()}"
        )
    return completed.stdout.strip()


def _checkout_provenance(root: Path, source_revision: str) -> str:
    checkout_root = Path(_git_output(root, "rev-parse", "--show-toplevel")).resolve()
    if checkout_root != root.resolve():
        raise ReleaseManifestError(
            f"release source root differs from the Git checkout: {checkout_root}"
        )
    head = _git_output(root, "rev-parse", "--verify", "HEAD")
    if head != source_revision:
        raise ReleaseManifestError(
            f"source revision differs from checkout HEAD: {source_revision} != {head}"
        )
    tree = _git_output(root, "rev-parse", "--verify", "HEAD^{tree}")
    if re.fullmatch(r"[0-9a-f]{40}", tree) is None:
        raise ReleaseManifestError("Git returned an invalid source tree identity")
    clean = subprocess.run(
        ["git", "-C", str(root), "diff", "--quiet", "HEAD", "--"],
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
    )
    if clean.returncode == 1:
        raise ReleaseManifestError("tracked release source differs from checkout HEAD")
    if clean.returncode != 0:
        raise ReleaseManifestError(
            f"Git could not audit the tracked release source: {clean.stdout.strip()}"
        )
    return tree


def _validate_source_inputs(source_revision: str, source_date_epoch: int) -> None:
    if re.fullmatch(r"[0-9a-f]{40}", source_revision) is None:
        raise ReleaseManifestError("source revision must be a complete lowercase Git SHA")
    if source_date_epoch != _SOURCE_DATE_EPOCH:
        raise ReleaseManifestError(
            f"source date epoch must be the audited value {_SOURCE_DATE_EPOCH}"
        )


def build_release_manifest(
    root: Path,
    bundle: Path,
    source_revision: str,
    source_date_epoch: int = _SOURCE_DATE_EPOCH,
    *,
    allow_outputs: bool = False,
) -> dict[str, object]:
    """Return the complete deterministic manifest for a staged release bundle."""

    _validate_source_inputs(source_revision, source_date_epoch)
    source_tree = _checkout_provenance(root, source_revision)
    paths = _bundle_distribution_paths(bundle, allow_outputs=allow_outputs)
    artifacts, name, version = _distribution_entries(paths)
    materials, snapshots = _capture_materials(root)
    build_provenance = _build_provenance(root, snapshots)
    sbom = _validated_sbom_binding(root, bundle, source_revision, snapshots)
    _assert_snapshot_identities(root, snapshots, list(_MATERIAL_FILES))
    if _checkout_provenance(root, source_revision) != source_tree:
        raise ReleaseManifestError("Git source tree changed while creating the release manifest")
    _assert_exact_bundle_members(
        bundle,
        paths,
        include_outputs=allow_outputs,
    )
    return {
        "artifacts": artifacts,
        "build_provenance": build_provenance,
        "distribution": {"name": name, "version": version},
        "materials": materials,
        "provenance_scope": "staged-bundle-and-clean-checkout-materials",
        "sbom": sbom,
        "schema": 2,
        "source_date_epoch": source_date_epoch,
        "source_revision": source_revision,
        "source_tree": source_tree,
    }


def _manifest_bytes(document: Mapping[str, object]) -> bytes:
    return (json.dumps(document, indent=2, sort_keys=True) + "\n").encode()


def _write_new_regular(path: Path, payload: bytes) -> None:
    flags = (
        os.O_WRONLY
        | os.O_CREAT
        | os.O_EXCL
        | getattr(os, "O_CLOEXEC", 0)
        | getattr(os, "O_BINARY", 0)
    )
    try:
        descriptor = os.open(path, flags, 0o644)
    except FileExistsError as error:
        raise ReleaseManifestError(f"release output already exists: {path}") from error
    with os.fdopen(descriptor, "wb") as stream:
        stream.write(payload)


def _checksum_payload(bundle: Path, expected: Mapping[str, str]) -> bytes:
    lines: list[str] = []
    for name, bound_digest in sorted(expected.items()):
        if re.fullmatch(r"[A-Za-z0-9_.+-]+", name) is None:
            raise ReleaseManifestError(f"release filename is unsafe for SHA256SUMS: {name}")
        digest, _size = _hash_regular(bundle / name)
        if digest != bound_digest:
            raise ReleaseManifestError(f"release file changed after manifest binding: {name}")
        lines.append(f"{digest}  {name}\n")
    return "".join(lines).encode()


def create_release_bundle(
    root: Path,
    bundle: Path,
    source_revision: str,
    source_date_epoch: int = _SOURCE_DATE_EPOCH,
) -> dict[str, object]:
    """Create a new manifest and checksum inventory without replacing existing outputs."""

    document = build_release_manifest(
        root,
        bundle,
        source_revision,
        source_date_epoch,
    )
    manifest_path = bundle / _MANIFEST_NAME
    rendered_manifest = _manifest_bytes(document)
    _write_new_regular(manifest_path, rendered_manifest)
    distribution_paths: list[Path] = []
    checksums: dict[str, str] = {}
    for entry in (
        require_mapping(raw, "release artifact")
        for raw in require_list(document.get("artifacts"), "release artifacts")
    ):
        name = require_str(entry.get("file"), "release artifact filename")
        distribution_paths.append(bundle / name)
        checksums[name] = require_str(
            entry.get("sha256"),
            "release artifact SHA-256",
        )
    sbom = require_mapping(document.get("sbom"), "release SBOM")
    checksums[require_str(sbom.get("file"), "release SBOM filename")] = require_str(
        sbom.get("sha256"),
        "release SBOM SHA-256",
    )
    checksums[_MANIFEST_NAME] = hashlib.sha256(rendered_manifest).hexdigest()
    _write_new_regular(bundle / _CHECKSUM_NAME, _checksum_payload(bundle, checksums))
    _assert_exact_bundle_members(bundle, distribution_paths, include_outputs=True)
    return document


def verify_release_bundle(
    root: Path,
    bundle: Path,
    source_revision: str,
    source_date_epoch: int = _SOURCE_DATE_EPOCH,
) -> dict[str, object]:
    """Verify manifest semantics, source provenance, artifacts, SBOM, and checksums."""

    expected = build_release_manifest(
        root,
        bundle,
        source_revision,
        source_date_epoch,
        allow_outputs=True,
    )
    actual_bytes = _read_regular(bundle / _MANIFEST_NAME)
    if actual_bytes != _manifest_bytes(expected):
        raise ReleaseManifestError("release manifest differs from the staged bundle or provenance")
    distribution_paths: list[Path] = []
    checksums: dict[str, str] = {}
    for entry in (
        require_mapping(raw, "release artifact")
        for raw in require_list(expected.get("artifacts"), "release artifacts")
    ):
        name = require_str(entry.get("file"), "release artifact filename")
        distribution_paths.append(bundle / name)
        checksums[name] = require_str(
            entry.get("sha256"),
            "release artifact SHA-256",
        )
    sbom = require_mapping(expected.get("sbom"), "release SBOM")
    checksums[_SBOM_NAME] = require_str(sbom.get("sha256"), "release SBOM SHA-256")
    checksums[_MANIFEST_NAME] = hashlib.sha256(actual_bytes).hexdigest()
    expected_checksums = _checksum_payload(bundle, checksums)
    if _read_regular(bundle / _CHECKSUM_NAME) != expected_checksums:
        raise ReleaseManifestError("SHA256SUMS differs from the complete release bundle")
    _assert_exact_bundle_members(bundle, distribution_paths, include_outputs=True)
    return expected


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bundle", type=Path, required=True)
    parser.add_argument("--source-revision", required=True)
    parser.add_argument("--source-date-epoch", type=int, default=_SOURCE_DATE_EPOCH)
    parser.add_argument("--verify", action="store_true")
    args = parser.parse_args(argv)
    try:
        if args.verify:
            document = verify_release_bundle(
                repository_root(),
                args.bundle,
                args.source_revision,
                args.source_date_epoch,
            )
            action = "verified"
        else:
            document = create_release_bundle(
                repository_root(),
                args.bundle,
                args.source_revision,
                args.source_date_epoch,
            )
            action = "created"
    except (OSError, ReleaseManifestError, ValueError) as error:
        print(f"release manifest invalid: {error}")
        return 1
    artifacts = require_list(document.get("artifacts"), "release artifacts")
    print(f"release manifest {action}: {len(artifacts)} distributions")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
