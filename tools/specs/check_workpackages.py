"""Validate the work-package graph, briefs, waves, and exclusive path ownership."""

from __future__ import annotations

import argparse
import json
from collections.abc import Sequence
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any

from tools.specs._compat import (
    load_toml,
    repository_root,
    require_int,
    require_list,
    require_mapping,
    require_str,
)


class ManifestError(ValueError):
    """The published work-package manifest violates its frozen schema."""


@dataclass(frozen=True, slots=True)
class WorkPackage:
    id: str
    brief: str
    wave: int
    depends: tuple[str, ...]
    owns: tuple[str, ...]


@dataclass(frozen=True, slots=True)
class OwnershipAllowance:
    owners: frozenset[str]
    left: str
    right: str
    reason: str


def _string_tuple(value: object, context: str) -> tuple[str, ...]:
    values = require_list(value, context)
    result = tuple(require_str(item, f"{context} item") for item in values)
    if len(set(result)) != len(result):
        raise ManifestError(f"{context} contains duplicates")
    return result


def _normalized_owned_path(value: str, context: str) -> str:
    if "\\" in value:
        raise ManifestError(f"{context} must use POSIX separators: {value!r}")
    directory = value.endswith("/")
    stripped = value[:-1] if directory else value
    path = PurePosixPath(stripped)
    if path.is_absolute() or not path.parts or any(part in {"", ".", ".."} for part in path.parts):
        raise ManifestError(f"{context} is not a safe repository-relative path: {value!r}")
    normalized = path.as_posix()
    return f"{normalized}/" if directory else normalized


def _parse_packages(data: dict[str, Any]) -> tuple[WorkPackage, ...]:
    if require_int(data.get("schema"), "manifest schema") != 2:
        raise ManifestError("work-package manifest schema must be 2")
    raw_packages = require_list(data.get("package"), "manifest package")
    packages: list[WorkPackage] = []
    for index, raw in enumerate(raw_packages):
        table = require_mapping(raw, f"package[{index}]")
        package_id = require_str(table.get("id"), f"package[{index}].id")
        wave = require_int(table.get("wave"), f"{package_id}.wave")
        if wave < 0:
            raise ManifestError(f"{package_id}.wave must be nonnegative")
        owns = tuple(
            _normalized_owned_path(path, f"{package_id}.owns")
            for path in _string_tuple(table.get("owns"), f"{package_id}.owns")
        )
        packages.append(
            WorkPackage(
                id=package_id,
                brief=require_str(table.get("brief"), f"{package_id}.brief"),
                wave=wave,
                depends=_string_tuple(table.get("depends"), f"{package_id}.depends"),
                owns=owns,
            )
        )
    ids = [package.id for package in packages]
    if len(set(ids)) != len(ids):
        duplicates = sorted({item for item in ids if ids.count(item) > 1})
        raise ManifestError(f"duplicate work-package IDs: {duplicates}")
    if not packages:
        raise ManifestError("manifest defines no work packages")
    return tuple(packages)


def _parse_allowances(data: dict[str, Any]) -> tuple[OwnershipAllowance, ...]:
    if require_int(data.get("schema"), "ownership allowlist schema") != 1:
        raise ManifestError("ownership allowlist schema must be 1")
    result: list[OwnershipAllowance] = []
    for index, raw in enumerate(require_list(data.get("allow", []), "ownership allowlist")):
        table = require_mapping(raw, f"allow[{index}]")
        owners = frozenset(_string_tuple(table.get("owners"), f"allow[{index}].owners"))
        if len(owners) != 2:
            raise ManifestError(f"allow[{index}] must name exactly two owners")
        result.append(
            OwnershipAllowance(
                owners=owners,
                left=_normalized_owned_path(
                    require_str(table.get("left"), f"allow[{index}].left"),
                    f"allow[{index}].left",
                ),
                right=_normalized_owned_path(
                    require_str(table.get("right"), f"allow[{index}].right"),
                    f"allow[{index}].right",
                ),
                reason=require_str(table.get("reason"), f"allow[{index}].reason"),
            )
        )
    return tuple(result)


def _validate_briefs(packages: Sequence[WorkPackage], manifest_path: Path) -> None:
    for package in packages:
        brief = manifest_path.parent / package.brief
        if not brief.is_file():
            raise ManifestError(f"{package.id} brief does not exist: {brief}")
        first_heading = next(
            (
                line
                for line in brief.read_text(encoding="utf-8").splitlines()
                if line.startswith("# ")
            ),
            "",
        )
        if package.id not in first_heading:
            raise ManifestError(
                f"{package.id} brief heading does not contain its ID: {first_heading!r}"
            )


def _validate_dependencies(packages: Sequence[WorkPackage]) -> None:
    by_id = {package.id: package for package in packages}
    for package in packages:
        unknown = sorted(set(package.depends) - by_id.keys())
        if unknown:
            raise ManifestError(f"{package.id} has unknown dependencies: {unknown}")
        if package.id in package.depends:
            raise ManifestError(f"{package.id} depends on itself")

    visiting: set[str] = set()
    visited: set[str] = set()

    def visit(package_id: str, trail: tuple[str, ...]) -> None:
        if package_id in visiting:
            start = trail.index(package_id)
            cycle = (*trail[start:], package_id)
            raise ManifestError(f"dependency cycle: {' -> '.join(cycle)}")
        if package_id in visited:
            return
        visiting.add(package_id)
        for dependency in by_id[package_id].depends:
            visit(dependency, (*trail, package_id))
        visiting.remove(package_id)
        visited.add(package_id)

    for package in packages:
        visit(package.id, ())

    for package in packages:
        for dependency in package.depends:
            dependency_wave = by_id[dependency].wave
            if dependency_wave >= package.wave:
                raise ManifestError(
                    f"{package.id} wave {package.wave} does not follow "
                    f"{dependency} wave {dependency_wave}"
                )


def _paths_overlap(left: str, right: str) -> bool:
    if left == right:
        return True
    return (left.endswith("/") and right.startswith(left)) or (
        right.endswith("/") and left.startswith(right)
    )


def _allowance_matches(
    allowance: OwnershipAllowance,
    left_owner: str,
    left_path: str,
    right_owner: str,
    right_path: str,
) -> bool:
    if allowance.owners != frozenset({left_owner, right_owner}):
        return False
    return {(allowance.left, allowance.right), (allowance.right, allowance.left)} & {
        (left_path, right_path)
    } != set()


def _validate_ownership(
    packages: Sequence[WorkPackage], allowances: Sequence[OwnershipAllowance]
) -> int:
    collisions = 0
    used: set[int] = set()
    for left_index, left in enumerate(packages):
        for right in packages[left_index + 1 :]:
            for left_path in left.owns:
                for right_path in right.owns:
                    if not _paths_overlap(left_path, right_path):
                        continue
                    collisions += 1
                    matching = [
                        index
                        for index, allowance in enumerate(allowances)
                        if _allowance_matches(
                            allowance,
                            left.id,
                            left_path,
                            right.id,
                            right_path,
                        )
                    ]
                    if len(matching) != 1:
                        raise ManifestError(
                            "unapproved or ambiguously approved ownership collision: "
                            f"{left.id}:{left_path} <-> {right.id}:{right_path}"
                        )
                    used.add(matching[0])
    unused = sorted(set(range(len(allowances))) - used)
    if unused:
        raise ManifestError(f"unused ownership allowlist entries: {unused}")
    return collisions


def validate_workpackages(manifest_path: Path, allowlist_path: Path) -> dict[str, int]:
    """Validate both manifests and return stable summary counts."""

    try:
        packages = _parse_packages(load_toml(manifest_path))
        allowances = _parse_allowances(load_toml(allowlist_path))
        _validate_briefs(packages, manifest_path)
        _validate_dependencies(packages)
        collisions = _validate_ownership(packages, allowances)
    except (OSError, ValueError) as error:
        if isinstance(error, ManifestError):
            raise
        raise ManifestError(str(error)) from error
    return {
        "packages": len(packages),
        "waves": len({package.wave for package in packages}),
        "dependencies": sum(len(package.depends) for package in packages),
        "allowed_collisions": collisions,
    }


def _parser() -> argparse.ArgumentParser:
    root = repository_root()
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--manifest",
        type=Path,
        default=root / "specs/workpackages/manifest.toml",
    )
    parser.add_argument(
        "--allowlist",
        type=Path,
        default=root / "tools/specs/ownership-allowlist.toml",
    )
    parser.add_argument("--json", action="store_true", help="emit a JSON summary")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    try:
        summary = validate_workpackages(args.manifest, args.allowlist)
    except ManifestError as error:
        print(f"work-package manifest invalid: {error}")
        return 1
    if args.json:
        print(json.dumps(summary, sort_keys=True))
    else:
        print(
            "work-package manifest valid: "
            f"{summary['packages']} packages, {summary['dependencies']} dependencies, "
            f"{summary['waves']} waves, {summary['allowed_collisions']} allowed collisions"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
