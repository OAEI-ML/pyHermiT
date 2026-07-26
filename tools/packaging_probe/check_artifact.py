"""Fail-closed audits for pyHermiT wheels and source distributions."""

from __future__ import annotations

import argparse
import base64
import csv
import hashlib
import io
import json
import re
import shutil
import stat
import subprocess
import tarfile
import zipfile
from collections.abc import Mapping, Sequence
from dataclasses import asdict, dataclass
from email.message import Message
from email.parser import BytesParser
from pathlib import Path, PurePosixPath

from packaging.requirements import InvalidRequirement, Requirement
from packaging.utils import canonicalize_name, parse_wheel_filename
from packaging.version import InvalidVersion, Version

_PROJECT_NAME = "pyhermit"
_CORE_SPECIFIERS = frozenset({">=0.1", "<0.2"})
_JAVA_SUFFIXES = (".class", ".jar", ".java", ".jmod", ".war", ".ear")
_NATIVE_SUFFIXES = (".so", ".pyd", ".dll", ".dylib")
_PYTHON_SUFFIXES = (".py", ".pyi")
_FORBIDDEN_DEPENDENCY_PARTS = ("java", "jni", "jpype", "jnius", "jvm", "py4j")
_ABSOLUTE_PATH_MARKERS = (
    b"/Users/",
    b"/home/runner/work/",
    b"/project/",
    b"/root/.cargo/",
    b"/tmp/cibuildwheel/",
    b"/github/workspace/",
    b"C:\\cibw\\",
    b"D:\\a\\",
    b"\\Users\\",
)
_MAX_MEMBER_SIZE = 256 * 1024 * 1024
_MAX_ARCHIVE_SIZE = 1024 * 1024 * 1024
_PATH_BOUNDARY_BYTES = frozenset(b"\x00\t\n\r \"'=(:,[{")
_LICENSE_PAYLOAD_SHA256 = {
    "COPYING": "3972dc9744f6499f0f9b2dbf76696f2ae7ad8af9b23dde66d6af86c9dfb36986",
    "LICENSE": "e3a994d82e644b03a792a930f574002658412f62407f5fee083f2555c5f23118",
    "NOTICE.md": "59fb5010cb7fb6bc6061b95551cab0e4f6b55223adfbe5510f1a9eabdff7adcc",
}


class ArtifactError(ValueError):
    """A built artifact violates the WPP0 packaging boundary."""


@dataclass(frozen=True, slots=True)
class ArchiveContent:
    files: Mapping[str, bytes]


@dataclass(frozen=True, slots=True)
class ArtifactReport:
    artifact: str
    kind: str
    name: str
    version: str
    requires_python: str
    tags: tuple[str, ...]
    native_members: tuple[str, ...]
    python_hashes: Mapping[str, str]
    license_hashes: Mapping[str, str]
    metadata_sha256: str
    archive_sha256: str
    java_free: bool = True
    probe_excluded: bool = True


def _contains_absolute_path(data: bytes, marker: bytes) -> bool:
    """Distinguish rooted build paths from URL and relative-path substrings."""

    offset = data.find(marker)
    while offset >= 0:
        if offset == 0 or data[offset - 1] in _PATH_BOUNDARY_BYTES:
            return True
        offset = data.find(marker, offset + 1)
    return False


def _safe_name(raw: str) -> str:
    if "\\" in raw:
        raise ArtifactError(f"archive member uses a backslash: {raw!r}")
    path = PurePosixPath(raw)
    if not path.parts or path.is_absolute() or any(part in {"", ".", ".."} for part in path.parts):
        raise ArtifactError(f"unsafe archive member path: {raw!r}")
    return path.as_posix()


def _read_wheel(path: Path) -> ArchiveContent:
    if path.stat().st_size > _MAX_ARCHIVE_SIZE:
        raise ArtifactError("wheel exceeds the audit size limit")
    try:
        with zipfile.ZipFile(path) as archive:
            files: dict[str, bytes] = {}
            total = 0
            for info in archive.infolist():
                name = _safe_name(info.filename)
                mode = (info.external_attr >> 16) & 0xFFFF
                if stat.S_ISLNK(mode):
                    raise ArtifactError(f"wheel contains a symbolic link: {name}")
                if info.is_dir():
                    continue
                if name in files:
                    raise ArtifactError(f"duplicate archive member: {name}")
                if info.file_size > _MAX_MEMBER_SIZE:
                    raise ArtifactError(f"archive member is too large: {name}")
                total += info.file_size
                if total > _MAX_ARCHIVE_SIZE:
                    raise ArtifactError("wheel expands beyond the audit size limit")
                files[name] = archive.read(info)
    except (OSError, zipfile.BadZipFile) as error:
        raise ArtifactError(f"invalid wheel archive {path}: {error}") from error
    return ArchiveContent(files)


def _read_sdist(path: Path) -> ArchiveContent:
    if path.stat().st_size > _MAX_ARCHIVE_SIZE:
        raise ArtifactError("sdist exceeds the audit size limit")
    try:
        with tarfile.open(path, mode="r:*") as archive:
            files: dict[str, bytes] = {}
            total = 0
            for member in archive.getmembers():
                name = _safe_name(member.name)
                if member.isdir():
                    continue
                if not member.isfile():
                    raise ArtifactError(f"sdist contains a non-regular member: {name}")
                if name in files:
                    raise ArtifactError(f"duplicate archive member: {name}")
                if member.size > _MAX_MEMBER_SIZE:
                    raise ArtifactError(f"archive member is too large: {name}")
                total += member.size
                if total > _MAX_ARCHIVE_SIZE:
                    raise ArtifactError("sdist expands beyond the audit size limit")
                stream = archive.extractfile(member)
                if stream is None:
                    raise ArtifactError(f"cannot read sdist member: {name}")
                files[name] = stream.read()
    except (OSError, tarfile.TarError) as error:
        raise ArtifactError(f"invalid sdist archive {path}: {error}") from error
    return ArchiveContent(files)


def _one_member(content: ArchiveContent, suffix: str) -> tuple[str, bytes]:
    matches = [(name, data) for name, data in content.files.items() if name.endswith(suffix)]
    if len(matches) != 1:
        raise ArtifactError(f"expected exactly one {suffix} member, found {len(matches)}")
    return matches[0]


def _metadata(content: ArchiveContent, *, wheel: bool) -> tuple[Message, bytes]:
    if wheel:
        _, raw = _one_member(content, ".dist-info/METADATA")
    else:
        matches = [
            data
            for name, data in content.files.items()
            if name.endswith("/PKG-INFO") and name.count("/") == 1
        ]
        if len(matches) != 1:
            raise ArtifactError(
                f"expected exactly one top-level PKG-INFO member, found {len(matches)}"
            )
        raw = matches[0]
    return BytesParser().parsebytes(raw), raw


def _check_metadata(message: Message) -> tuple[str, str, str]:
    name = message.get("Name", "")
    version = message.get("Version", "")
    requires_python = message.get("Requires-Python", "")
    if canonicalize_name(name) != _PROJECT_NAME:
        raise ArtifactError(f"unexpected project name: {name!r}")
    if not version:
        raise ArtifactError("artifact metadata has no Version")
    try:
        Version(version)
    except InvalidVersion as error:
        raise ArtifactError(f"artifact metadata has an invalid Version: {version!r}") from error
    if requires_python.replace(" ", "") != ">=3.10":
        raise ArtifactError(f"unexpected Requires-Python: {requires_python!r}")
    if message.get("License-Expression") != "LGPL-3.0-or-later":
        raise ArtifactError("License-Expression must be LGPL-3.0-or-later")
    license_files = tuple(message.get_all("License-File", []))
    if len(license_files) != 3 or set(license_files) != {"LICENSE", "COPYING", "NOTICE.md"}:
        raise ArtifactError("License-File metadata must name LICENSE, COPYING, and NOTICE.md")
    extras = tuple(message.get_all("Provides-Extra", []))
    if extras != ("dev",):
        raise ArtifactError("artifact metadata must declare exactly the dev extra")

    _check_runtime_dependencies(message)
    return name, version, requires_python


def _license_hashes(content: ArchiveContent, *, wheel: bool) -> dict[str, str]:
    """Validate required license payload content and return identity hashes."""

    payloads: dict[str, bytes] = {}
    for name in ("LICENSE", "COPYING", "NOTICE.md"):
        suffix = f".dist-info/licenses/{name}" if wheel else f"/{name}"
        _, payloads[name] = _one_member(content, suffix)
    try:
        license_text = payloads["LICENSE"].decode("utf-8")
        copying_text = payloads["COPYING"].decode("utf-8")
        notice_text = payloads["NOTICE.md"].decode("utf-8")
    except UnicodeDecodeError as error:
        raise ArtifactError("license and notice payloads must be UTF-8") from error
    if "GNU LESSER GENERAL PUBLIC LICENSE" not in license_text or "Version 3" not in license_text:
        raise ArtifactError("LICENSE must contain the GNU LGPL version 3 text")
    if "GNU GENERAL PUBLIC LICENSE" not in copying_text or "Version 3" not in copying_text:
        raise ArtifactError("COPYING must contain the GNU GPL version 3 text")
    required_notice = (
        "LGPL-3.0-or-later",
        "source-guided",
        "37ec30aced32ac81ebecc5e33fad255ddefcb4c3",
        "reports/licensing/adapted-files.toml",
    )
    missing = tuple(value for value in required_notice if value not in notice_text)
    if missing:
        raise ArtifactError(f"NOTICE.md is missing required provenance values: {missing}")
    hashes = {
        name: hashlib.sha256(payload).hexdigest() for name, payload in sorted(payloads.items())
    }
    if hashes != _LICENSE_PAYLOAD_SHA256:
        raise ArtifactError("license or notice payload identity differs from the audited files")
    return hashes


def _check_runtime_dependencies(metadata: Message | str) -> None:
    """Validate the exact runtime dependency boundary in parsed or text metadata."""

    message = (
        BytesParser().parsebytes(metadata.encode("utf-8"))
        if isinstance(metadata, str)
        else metadata
    )

    core_requirements: list[Requirement] = []
    for value in message.get_all("Requires-Dist", []):
        try:
            requirement = Requirement(value)
        except InvalidRequirement as error:
            raise ArtifactError(f"invalid Requires-Dist metadata: {error}") from error
        dependency = canonicalize_name(requirement.name)
        if any(part in dependency for part in _FORBIDDEN_DEPENDENCY_PARTS):
            raise ArtifactError(f"forbidden Java/JVM dependency: {value}")
        if dependency == "pyowl-core" and requirement.marker is None:
            core_requirements.append(requirement)
            continue
        marker = "" if requirement.marker is None else str(requirement.marker)
        if 'extra == "dev"' not in marker or " or " in marker:
            raise ArtifactError(f"unexpected runtime dependency outside pyowl-core: {value}")
    if len(core_requirements) != 1:
        raise ArtifactError("metadata must contain exactly one runtime pyowl-core requirement")
    actual_specifiers = frozenset(str(specifier) for specifier in core_requirements[0].specifier)
    if actual_specifiers != _CORE_SPECIFIERS:
        raise ArtifactError("pyowl-core requirement must be exactly pyowl-core>=0.1,<0.2")


def _check_names_and_payloads(content: ArchiveContent) -> tuple[str, ...]:
    native: list[str] = []
    current_root = str(Path.cwd().resolve()).encode()
    for name, data in content.files.items():
        lowered = name.lower()
        path = PurePosixPath(lowered)
        if lowered.endswith(_JAVA_SUFFIXES):
            raise ArtifactError(f"Java artifact present: {name}")
        if any(part in {"java", "jni", "jre", "jvm"} for part in path.parts):
            raise ArtifactError(f"Java/JVM archive path present: {name}")
        if "/tools/reference/" in f"/{lowered}/" or "/.reference/" in f"/{lowered}/":
            raise ArtifactError(f"development reference material present: {name}")
        if "/tools/packaging_probe/" in f"/{lowered}/":
            raise ArtifactError(f"self-test packaging probe present: {name}")
        if lowered.endswith(_NATIVE_SUFFIXES):
            native.append(name)
        for marker in (*_ABSOLUTE_PATH_MARKERS, current_root):
            if marker and _contains_absolute_path(data, marker):
                raise ArtifactError(f"absolute build path marker {marker!r} in {name}")
    return tuple(sorted(native))


def _python_hashes(content: ArchiveContent, *, sdist: bool) -> dict[str, str]:
    hashes: dict[str, str] = {}
    for name, data in content.files.items():
        logical = name.split("/", 1)[1] if sdist and "/" in name else name
        if logical.startswith("src/"):
            logical = logical[4:]
        if not logical.startswith("pyhermit/"):
            continue
        if not logical.endswith((*_PYTHON_SUFFIXES, "py.typed")):
            continue
        hashes[logical] = hashlib.sha256(data).hexdigest()
    return dict(sorted(hashes.items()))


def _check_record(content: ArchiveContent) -> None:
    record_name, raw = _one_member(content, ".dist-info/RECORD")
    try:
        rows = list(csv.reader(io.StringIO(raw.decode("utf-8"))))
    except (UnicodeDecodeError, csv.Error) as error:
        raise ArtifactError("wheel RECORD is not valid UTF-8 CSV") from error
    records: dict[str, tuple[str, str]] = {}
    for row in rows:
        if len(row) != 3:
            raise ArtifactError("wheel RECORD rows must have exactly three fields")
        name = _safe_name(row[0])
        if name in records:
            raise ArtifactError(f"duplicate RECORD entry: {name}")
        records[name] = (row[1], row[2])
    if set(records) != set(content.files):
        raise ArtifactError("wheel RECORD member set does not match archive member set")
    for name, data in content.files.items():
        digest, size = records[name]
        if name == record_name:
            if digest or size:
                raise ArtifactError("the RECORD self-entry must omit hash and size")
            continue
        expected = base64.urlsafe_b64encode(hashlib.sha256(data).digest()).rstrip(b"=").decode()
        if digest != f"sha256={expected}" or size != str(len(data)):
            raise ArtifactError(f"invalid RECORD hash or size for {name}")


def _runtime_version(source: bytes) -> str:
    try:
        text = source.decode("utf-8")
    except UnicodeDecodeError as error:
        raise ArtifactError("runtime version source is not UTF-8") from error
    match = re.search(r'^__version__ = "([^"]+)"$', text, flags=re.MULTILINE)
    if match is None:
        raise ArtifactError("runtime version source has no canonical __version__ assignment")
    return match.group(1)


def _wheel_tags(
    path: Path,
    content: ArchiveContent,
    *,
    metadata_name: str,
    metadata_version: str,
) -> tuple[str, ...]:
    try:
        filename_name, filename_version, build, filename_tags = parse_wheel_filename(path.name)
    except ValueError as error:
        raise ArtifactError(f"malformed wheel filename: {path.name}") from error
    if filename_name != canonicalize_name(metadata_name):
        raise ArtifactError("wheel filename and METADATA project names differ")
    if filename_version != Version(metadata_version):
        raise ArtifactError("wheel filename and METADATA versions differ")
    if build:
        raise ArtifactError("release wheels must not carry a build tag")
    metadata_member, _ = _one_member(content, ".dist-info/METADATA")
    expected_dist_info = f"{filename_name.replace('-', '_')}-{filename_version}.dist-info"
    if PurePosixPath(metadata_member).parent.as_posix() != expected_dist_info:
        raise ArtifactError("wheel dist-info directory does not match its filename identity")
    wheel_member, wheel_raw = _one_member(content, ".dist-info/WHEEL")
    if PurePosixPath(wheel_member).parent.as_posix() != expected_dist_info:
        raise ArtifactError("wheel metadata files use different dist-info directories")
    wheel_message = BytesParser().parsebytes(wheel_raw)
    metadata_tags = tuple(wheel_message.get_all("Tag", []))
    if set(metadata_tags) != {str(tag) for tag in filename_tags}:
        raise ArtifactError("wheel filename tags and WHEEL metadata differ")
    return tuple(sorted(metadata_tags))


def _inspect_wheel(path: Path, content: ArchiveContent, expected: str) -> ArtifactReport:
    metadata, metadata_raw = _metadata(content, wheel=True)
    name, version, requires_python = _check_metadata(metadata)
    tags = _wheel_tags(path, content, metadata_name=name, metadata_version=version)
    native = _check_names_and_payloads(content)
    inferred = "native-wheel" if native else "pure-wheel"
    if expected != "auto" and inferred != expected:
        raise ArtifactError(f"expected {expected}, found {inferred}")

    for forbidden in ("tools/", "specs/", "native/", "Cargo.toml", "setup.py"):
        if forbidden in content.files or any(name.startswith(forbidden) for name in content.files):
            raise ArtifactError(f"development/build path present in wheel: {forbidden}")
    for required in (
        "pyhermit/__init__.py",
        "pyhermit/_native.pyi",
        "pyhermit/_version.py",
        "pyhermit/py.typed",
    ):
        if required not in content.files:
            raise ArtifactError(f"wheel is missing runtime file: {required}")
    if _runtime_version(content.files["pyhermit/_version.py"]) != version:
        raise ArtifactError("wheel metadata and runtime version source differ")
    license_hashes = _license_hashes(content, wheel=True)

    _, wheel_raw = _one_member(content, ".dist-info/WHEEL")
    root_is_pure = BytesParser().parsebytes(wheel_raw).get("Root-Is-Purelib", "").lower()
    if inferred == "pure-wheel":
        if tags != ("py3-none-any",) or not path.name.endswith("-py3-none-any.whl"):
            raise ArtifactError(f"fallback wheel is not exactly py3-none-any: {tags}")
        if root_is_pure != "true":
            raise ArtifactError("fallback wheel must set Root-Is-Purelib: true")
    else:
        if not tags or not all(tag.startswith("cp310-abi3-") for tag in tags):
            raise ArtifactError(f"native wheel is not cp310-abi3: {tags}")
        if root_is_pure != "false":
            raise ArtifactError("native wheel must set Root-Is-Purelib: false")
        if len(native) != 1:
            raise ArtifactError(f"native wheel must contain one extension, found {native}")
        extension = native[0].lower()
        if not extension.startswith("pyhermit/_native"):
            raise ArtifactError(f"unallowlisted native library: {native[0]}")
        if extension.endswith(".so") and not extension.endswith(".abi3.so"):
            raise ArtifactError(f"non-ABI3 extension suffix: {native[0]}")
    _check_record(content)
    return ArtifactReport(
        artifact=path.name,
        kind=inferred,
        name=name,
        version=version,
        requires_python=requires_python,
        tags=tags,
        native_members=native,
        python_hashes=_python_hashes(content, sdist=False),
        license_hashes=license_hashes,
        metadata_sha256=hashlib.sha256(metadata_raw).hexdigest(),
        archive_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
    )


def _inspect_sdist(path: Path, content: ArchiveContent, expected: str) -> ArtifactReport:
    if expected not in {"auto", "sdist"}:
        raise ArtifactError(f"expected {expected}, found sdist")
    metadata, metadata_raw = _metadata(content, wheel=False)
    name, version, requires_python = _check_metadata(metadata)
    native = _check_names_and_payloads(content)
    if native:
        raise ArtifactError(f"sdist contains compiled native libraries: {native}")
    roots = {name.split("/", 1)[0] for name in content.files}
    if len(roots) != 1:
        raise ArtifactError(f"sdist must have one top-level directory, found {sorted(roots)}")
    root = next(iter(roots))
    expected_root = f"{canonicalize_name(name)}-{Version(version)}"
    if root != expected_root or path.name != f"{expected_root}.tar.gz":
        raise ArtifactError("sdist filename/root and PKG-INFO identity differ")
    logical = {name[len(root) + 1 :] for name in content.files if name.startswith(f"{root}/")}
    required = {
        "COPYING",
        "Cargo.toml",
        "deny.toml",
        "LICENSE",
        "MANIFEST.in",
        "NOTICE.md",
        "native/Cargo.lock",
        "native/Cargo.toml",
        "native/src/lib.rs",
        "pyproject.toml",
        "reports/licensing/adapted-file-header-audit.md",
        "reports/licensing/adapted-files.toml",
        "reports/licensing/package-license-audit.md",
        "reports/release/artifact-audit.md",
        "setup.cfg",
        "setup.py",
        "specs/SPEC.md",
        "src/pyhermit/__init__.py",
        "src/pyhermit/_native.pyi",
        "src/pyhermit/_version.py",
        "src/pyhermit/py.typed",
        "tools/specs/licensing.toml",
        "tools/specs/rust-production-licenses.toml",
    }
    missing = required - logical
    if missing:
        raise ArtifactError(f"sdist is missing required files: {sorted(missing)}")
    version_member = f"{root}/src/pyhermit/_version.py"
    if _runtime_version(content.files[version_member]) != version:
        raise ArtifactError("sdist metadata and runtime version source differ")
    license_hashes = _license_hashes(content, wheel=False)
    forbidden_prefixes = (
        ".reference/",
        "target/",
        "tests/",
        "tools/packaging_probe/",
        "tools/reference/",
    )
    forbidden = sorted(name for name in logical if name.startswith(forbidden_prefixes))
    if forbidden:
        raise ArtifactError(f"sdist contains release-excluded files: {forbidden[:5]}")
    return ArtifactReport(
        artifact=path.name,
        kind="sdist",
        name=name,
        version=version,
        requires_python=requires_python,
        tags=(),
        native_members=(),
        python_hashes=_python_hashes(content, sdist=True),
        license_hashes=license_hashes,
        metadata_sha256=hashlib.sha256(metadata_raw).hexdigest(),
        archive_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
    )


def inspect_artifact(path: Path, *, pure: bool = False, expected: str = "auto") -> ArtifactReport:
    """Inspect one artifact and return a deterministic report."""

    path = path.resolve()
    if not path.is_file():
        raise ArtifactError(f"artifact does not exist: {path}")
    if pure:
        expected = "pure-wheel"
    if path.name.endswith(".whl"):
        content = _read_wheel(path)
        _check_names_and_payloads(content)
        return _inspect_wheel(path, content, expected)
    if path.name.endswith((".tar.gz", ".tar.bz2", ".tar.xz")):
        content = _read_sdist(path)
        _check_names_and_payloads(content)
        return _inspect_sdist(path, content, expected)
    raise ArtifactError(f"unsupported artifact suffix: {path}")


def compare_wheels(pure: Path, native: Path) -> tuple[ArtifactReport, ArtifactReport]:
    """Require pure/native wheels to share identity, metadata, and Python payloads."""

    pure_report = inspect_artifact(pure, expected="pure-wheel")
    native_report = inspect_artifact(native, expected="native-wheel")
    identity = (pure_report.name, pure_report.version, pure_report.requires_python)
    native_identity = (native_report.name, native_report.version, native_report.requires_python)
    if identity != native_identity:
        raise ArtifactError(
            f"pure/native project identity differs: {identity} != {native_identity}"
        )
    if pure_report.metadata_sha256 != native_report.metadata_sha256:
        raise ArtifactError("pure/native METADATA bytes differ")
    if pure_report.python_hashes != native_report.python_hashes:
        raise ArtifactError("pure/native Python payload differs")
    if pure_report.license_hashes != native_report.license_hashes:
        raise ArtifactError("pure/native license or notice payload differs")
    return pure_report, native_report


def external_audit(path: Path) -> tuple[str, ...]:
    """Run ABI3 and host-platform shared-library auditors."""

    report = inspect_artifact(path, expected="native-wheel")
    commands: list[list[str]] = [["abi3audit", "--strict", "--report", str(path)]]
    platform = report.tags[0].split("-", 2)[-1]
    if "manylinux" in platform or "musllinux" in platform:
        commands.append(["auditwheel", "show", str(path)])
    elif "macosx" in platform:
        commands.append(["delocate-listdeps", "--all", str(path)])
    elif platform.startswith("win"):
        commands.append(["delvewheel", "show", str(path)])
    else:
        raise ArtifactError(f"no dependency auditor for platform tag: {platform}")
    rendered: list[str] = []
    for command in commands:
        if shutil.which(command[0]) is None:
            raise ArtifactError(f"required audit command is unavailable: {command[0]}")
        completed = subprocess.run(
            command,
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
        )
        if completed.stdout:
            print(completed.stdout, end="" if completed.stdout.endswith("\n") else "\n")
        if completed.returncode != 0:
            raise ArtifactError(
                f"external audit command failed with status {completed.returncode}: {command[0]}"
            )
        lowered = completed.stdout.casefold()
        if any(part in lowered for part in _FORBIDDEN_DEPENDENCY_PARTS):
            raise ArtifactError(f"external audit reports a Java/JVM library: {command[0]}")
        rendered.append(" ".join(command))
    return tuple(rendered)


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    expectation = parser.add_mutually_exclusive_group()
    expectation.add_argument("--pure", action="store_true", help="require a universal wheel")
    expectation.add_argument("--native", action="store_true", help="require a cp310-abi3 wheel")
    parser.add_argument("--external", action="store_true", help="run ABI/shared-library tools")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--compare", nargs=2, metavar=("PURE", "NATIVE"), type=Path)
    parser.add_argument("artifacts", nargs="*", type=Path)
    args = parser.parse_args(argv)
    try:
        if args.compare:
            reports = list(compare_wheels(*args.compare))
        else:
            if not args.artifacts:
                parser.error("at least one artifact is required")
            expected = "native-wheel" if args.native else "auto"
            reports = [
                inspect_artifact(path, pure=args.pure, expected=expected) for path in args.artifacts
            ]
            if args.external:
                for path in args.artifacts:
                    external_audit(path)
    except (OSError, subprocess.CalledProcessError, ArtifactError) as error:
        print(f"artifact invalid: {error}")
        return 1
    if args.json:
        print(json.dumps([asdict(report) for report in reports], sort_keys=True))
    else:
        for report in reports:
            print(f"artifact valid: {report.artifact} ({report.kind}, Java-free)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
