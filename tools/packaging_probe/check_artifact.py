"""Inspect pyHermiT wheel/sdist contents, metadata, and the no-Java boundary."""

from __future__ import annotations

import argparse
import json
import stat
import tarfile
import zipfile
from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from email.parser import Parser
from pathlib import Path, PurePosixPath

from packaging.requirements import InvalidRequirement, Requirement
from packaging.utils import canonicalize_name

_JAVA_SUFFIXES = (".class", ".jar", ".java", ".jmod", ".war", ".ear")
_NATIVE_SUFFIXES = (".so", ".pyd", ".dll", ".dylib")
_FORBIDDEN_DEPENDENCY_PREFIXES = (
    "jpype",
    "pyjnius",
    "jnius",
    "javabridge",
)


class ArtifactError(ValueError):
    """A built artifact violates the WP00 packaging boundary."""


@dataclass(frozen=True, slots=True)
class ArchiveContent:
    names: tuple[str, ...]
    files: Mapping[str, bytes]


def _safe_name(raw: str) -> str:
    normalized = raw.replace("\\", "/")
    while normalized.startswith("./"):
        normalized = normalized[2:]
    path = PurePosixPath(normalized)
    if (
        not path.parts
        or path.is_absolute()
        or path.parts[0].endswith(":")
        or any(part == ".." for part in path.parts)
    ):
        raise ArtifactError(f"unsafe archive member path: {raw!r}")
    return path.as_posix()


def _read_wheel(path: Path) -> ArchiveContent:
    try:
        with zipfile.ZipFile(path) as archive:
            files: dict[str, bytes] = {}
            names: list[str] = []
            for info in archive.infolist():
                name = _safe_name(info.filename)
                names.append(name)
                mode = (info.external_attr >> 16) & 0xFFFF
                if stat.S_ISLNK(mode):
                    raise ArtifactError(f"wheel contains a symbolic link: {name}")
                if not info.is_dir():
                    files[name] = archive.read(info)
    except (OSError, zipfile.BadZipFile) as error:
        raise ArtifactError(f"invalid wheel archive {path}: {error}") from error
    return ArchiveContent(tuple(names), files)


def _read_sdist(path: Path) -> ArchiveContent:
    try:
        with tarfile.open(path, mode="r:*") as archive:
            files: dict[str, bytes] = {}
            names: list[str] = []
            for member in archive.getmembers():
                name = _safe_name(member.name)
                names.append(name)
                if member.issym() or member.islnk():
                    raise ArtifactError(f"sdist contains a link member: {name}")
                if not member.isfile() and not member.isdir():
                    raise ArtifactError(f"sdist contains a special member: {name}")
                if member.isfile():
                    stream = archive.extractfile(member)
                    if stream is None:
                        raise ArtifactError(f"cannot read sdist member: {name}")
                    files[name] = stream.read()
    except (OSError, tarfile.TarError) as error:
        raise ArtifactError(f"invalid sdist archive {path}: {error}") from error
    return ArchiveContent(tuple(names), files)


def _relative_to_sdist_root(name: str) -> str:
    parts = PurePosixPath(name).parts
    return PurePosixPath(*parts[1:]).as_posix() if len(parts) > 1 else name


def _contains_path(names: Sequence[str], expected: str, *, sdist: bool) -> bool:
    normalized = [_relative_to_sdist_root(name) for name in names] if sdist else list(names)
    return expected in normalized or any(name.startswith(f"{expected}/") for name in normalized)


def _metadata(content: ArchiveContent) -> tuple[str, str]:
    metadata_names = [name for name in content.files if name.endswith(".dist-info/METADATA")]
    wheel_names = [name for name in content.files if name.endswith(".dist-info/WHEEL")]
    if len(metadata_names) != 1 or len(wheel_names) != 1:
        raise ArtifactError("wheel must contain exactly one METADATA and WHEEL file")
    try:
        metadata = content.files[metadata_names[0]].decode("utf-8")
        wheel = content.files[wheel_names[0]].decode("utf-8")
    except UnicodeDecodeError as error:
        raise ArtifactError("wheel metadata is not UTF-8") from error
    return metadata, wheel


def _check_java_boundary(names: Sequence[str]) -> None:
    for name in names:
        lowered = name.lower()
        if lowered.endswith(_JAVA_SUFFIXES):
            raise ArtifactError(f"Java artifact present: {name}")
        if "/tools/reference/" in f"/{lowered}/" or "/.reference/" in f"/{lowered}/":
            raise ArtifactError(f"development reference material present: {name}")


def _check_runtime_dependencies(metadata_text: str) -> None:
    message = Parser().parsestr(metadata_text)
    requirements = message.get_all("Requires-Dist", [])
    try:
        names = [canonicalize_name(Requirement(value).name) for value in requirements]
    except InvalidRequirement as error:
        raise ArtifactError(f"invalid Requires-Dist metadata: {error}") from error
    if "pyowl-core" not in names:
        raise ArtifactError("wheel metadata lacks the pyowl-core runtime dependency")
    forbidden = sorted(name for name in names if name.startswith(_FORBIDDEN_DEPENDENCY_PREFIXES))
    if forbidden:
        raise ArtifactError(f"Java bridge dependencies present: {forbidden}")
    if message.get("Requires-Python") != ">=3.10":
        raise ArtifactError("wheel Requires-Python must be >=3.10")
    if message.get("License-Expression") != "LGPL-3.0-or-later":
        raise ArtifactError("wheel License-Expression must be LGPL-3.0-or-later")


def inspect_artifact(path: Path, *, pure: bool = False) -> dict[str, object]:
    """Inspect one artifact and return a stable summary."""

    if path.name.endswith(".whl"):
        kind = "wheel"
        content = _read_wheel(path)
        sdist = False
    elif path.name.endswith((".tar.gz", ".tar.bz2", ".tar.xz", ".zip")):
        kind = "sdist"
        content = _read_sdist(path)
        sdist = True
    else:
        raise ArtifactError(f"unsupported artifact suffix: {path}")

    _check_java_boundary(content.names)
    if _contains_path(content.names, "tools/packaging_probe", sdist=sdist):
        raise ArtifactError("self-test packaging probe leaked into an artifact")

    if kind == "wheel":
        for forbidden in ("tools", "specs", "native", "Cargo.toml", "setup.py"):
            if _contains_path(content.names, forbidden, sdist=False):
                raise ArtifactError(f"development/build path present in wheel: {forbidden}")
        for required in ("pyhermit/__init__.py", "pyhermit/py.typed"):
            if required not in content.files:
                raise ArtifactError(f"wheel is missing runtime file: {required}")
        metadata_text, wheel_text = _metadata(content)
        _check_runtime_dependencies(metadata_text)
        for required_license in ("LICENSE", "COPYING", "NOTICE.md"):
            if not any(
                name.endswith(f".dist-info/licenses/{required_license}") for name in content.files
            ):
                raise ArtifactError(f"wheel is missing license payload: {required_license}")
        if pure:
            native = [name for name in content.files if name.lower().endswith(_NATIVE_SUFFIXES)]
            if native:
                raise ArtifactError(f"pure wheel contains native files: {native}")
            if "Tag: py3-none-any" not in wheel_text:
                raise ArtifactError("pure wheel is not tagged py3-none-any")
    else:
        for required in (
            "pyproject.toml",
            "setup.cfg",
            "setup.py",
            "Cargo.toml",
            "native/Cargo.toml",
            "native/Cargo.lock",
            "native/src/lib.rs",
            "LICENSE",
            "COPYING",
            "NOTICE.md",
            "src/pyhermit/__init__.py",
            "specs/SPEC.md",
            "tools/specs/licensing.toml",
        ):
            if not _contains_path(content.names, required, sdist=True):
                raise ArtifactError(f"sdist is missing required path: {required}")

    return {
        "artifact": path.name,
        "kind": kind,
        "members": len(content.names),
        "pure": pure,
        "java_free": True,
        "probe_excluded": True,
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pure", action="store_true", help="require a universal pure wheel")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("artifacts", nargs="+", type=Path)
    args = parser.parse_args(argv)
    summaries: list[dict[str, object]] = []
    try:
        for artifact in args.artifacts:
            summaries.append(inspect_artifact(artifact, pure=args.pure))
    except (OSError, ArtifactError) as error:
        print(f"artifact invalid: {error}")
        return 1
    if args.json:
        print(json.dumps(summaries, sort_keys=True))
    else:
        for summary in summaries:
            print(
                f"artifact valid: {summary['artifact']} ({summary['kind']}, "
                f"{summary['members']} members, Java-free, probe excluded)"
            )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
