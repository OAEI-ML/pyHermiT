"""Validate LIC-001 and fail closed when publication is requested."""

from __future__ import annotations

import argparse
from collections.abc import Sequence
from pathlib import Path, PurePosixPath

from tools.specs._compat import (
    load_toml,
    repository_root,
    require_bool,
    require_int,
    require_list,
    require_mapping,
    require_str,
)


class ReleaseGateError(ValueError):
    """The release gate is malformed or contradicts its checklist."""


_REQUIRED_REQUIREMENTS = frozenset(
    {
        "owner-license-decision",
        "license-texts",
        "initial-upstream-notice",
        "python-and-workspace-spdx",
        "adapted-file-provenance-inventory",
        "adapted-file-headers-and-modification-notices",
        "wheel-sdist-license-layout-and-source-obligations",
        "artifact-audit",
        "owner-legal-review-signoff",
    }
)

_REQUIRED_EVIDENCE = {
    "owner-license-decision": frozenset({"specs/deviations.md"}),
    "license-texts": frozenset({"LICENSE", "COPYING"}),
    "initial-upstream-notice": frozenset({"NOTICE.md"}),
    "python-and-workspace-spdx": frozenset({"pyproject.toml", "Cargo.toml"}),
    "adapted-file-provenance-inventory": frozenset({"reports/licensing/adapted-files.toml"}),
    "adapted-file-headers-and-modification-notices": frozenset(
        {"reports/licensing/adapted-file-header-audit.md"}
    ),
    "wheel-sdist-license-layout-and-source-obligations": frozenset(
        {"reports/licensing/package-license-audit.md"}
    ),
    "artifact-audit": frozenset({"reports/release/artifact-audit.md"}),
    "owner-legal-review-signoff": frozenset({"reports/licensing/owner-legal-review-signoff.md"}),
}


def _safe_evidence_name(value: str, requirement_id: str) -> str:
    relative = value.strip()
    candidate = PurePosixPath(relative)
    if (
        not relative
        or "\\" in relative
        or candidate.is_absolute()
        or any(part in {"", ".", ".."} for part in candidate.parts)
    ):
        raise ReleaseGateError(
            f"evidence for {requirement_id} must use safe repository-relative paths"
        )
    return candidate.as_posix()


def _evidence_paths(value: str, requirement_id: str, root: Path) -> tuple[str, ...]:
    paths: list[Path] = []
    names: list[str] = []
    for raw in value.split(","):
        relative = _safe_evidence_name(raw, requirement_id)
        candidate = PurePosixPath(relative)
        resolved = root.joinpath(*candidate.parts).resolve()
        try:
            resolved.relative_to(root.resolve())
        except ValueError as error:
            raise ReleaseGateError(
                f"evidence for {requirement_id} escapes the repository: {relative}"
            ) from error
        if not resolved.is_file():
            raise ReleaseGateError(f"evidence for {requirement_id} does not exist: {relative}")
        paths.append(resolved)
        names.append(relative)
    if len(set(paths)) != len(paths):
        raise ReleaseGateError(f"evidence for {requirement_id} contains duplicates")
    return tuple(names)


def _release_status(path: Path, evidence_root: Path) -> tuple[bool, tuple[str, ...]]:
    data = load_toml(path)
    if require_int(data.get("schema"), "release gate schema") != 1:
        raise ReleaseGateError("release gate schema must be 1")
    if require_str(data.get("gate_id"), "gate_id") != "LIC-001":
        raise ReleaseGateError("release gate must be LIC-001")
    if require_str(data.get("decision_status"), "decision_status") != "recorded":
        raise ReleaseGateError("the owner decision is not recorded")
    if require_str(data.get("implementation_mode"), "implementation_mode") != "source-guided":
        raise ReleaseGateError("implementation mode must remain source-guided")
    if require_str(data.get("project_license"), "project_license") != "LGPL-3.0-or-later":
        raise ReleaseGateError("project license must remain LGPL-3.0-or-later")
    authority = require_str(data.get("authority"), "authority")
    if not authority.startswith("specs/deviations.md#lic-001"):
        raise ReleaseGateError("release gate authority must point to LIC-001")
    requirements = require_list(data.get("requirement"), "requirement")
    pending: list[str] = []
    seen: set[str] = set()
    for index, raw in enumerate(requirements):
        table = require_mapping(raw, f"requirement[{index}]")
        requirement_id = require_str(table.get("id"), f"requirement[{index}].id")
        if requirement_id in seen:
            raise ReleaseGateError(f"duplicate requirement: {requirement_id}")
        seen.add(requirement_id)
        status = require_str(table.get("status"), f"requirement[{index}].status")
        if status == "pending":
            pending.append(requirement_id)
        elif status != "complete":
            raise ReleaseGateError(f"invalid status for {requirement_id}: {status}")
        evidence = table.get("evidence")
        if not isinstance(evidence, str):
            raise ReleaseGateError(f"evidence for {requirement_id} must be a string")
        declared_evidence = tuple(
            _safe_evidence_name(
                require_str(item, f"expected evidence for {requirement_id}"),
                requirement_id,
            )
            for item in require_list(
                table.get("expected_evidence"),
                f"expected evidence for {requirement_id}",
            )
        )
        if len(set(declared_evidence)) != len(declared_evidence):
            raise ReleaseGateError(f"expected evidence for {requirement_id} contains duplicates")
        expected_evidence = _REQUIRED_EVIDENCE.get(requirement_id)
        if expected_evidence is None or frozenset(declared_evidence) != expected_evidence:
            raise ReleaseGateError(f"expected evidence identity drift for {requirement_id}")
        if status == "complete":
            if not evidence:
                raise ReleaseGateError(f"completed requirement lacks evidence: {requirement_id}")
            actual_evidence = frozenset(_evidence_paths(evidence, requirement_id, evidence_root))
            if actual_evidence != expected_evidence:
                raise ReleaseGateError(f"completed evidence identity mismatch for {requirement_id}")
        elif evidence:
            raise ReleaseGateError(f"pending requirement must not claim evidence: {requirement_id}")
    if seen != _REQUIRED_REQUIREMENTS:
        missing = sorted(_REQUIRED_REQUIREMENTS - seen)
        extra = sorted(seen - _REQUIRED_REQUIREMENTS)
        raise ReleaseGateError(
            f"LIC-001 checklist identity mismatch; missing={missing}, extra={extra}"
        )
    publish_allowed = require_bool(data.get("publish_allowed"), "publish_allowed")
    gate_status = require_str(data.get("gate_status"), "gate_status")
    if gate_status not in {"open", "closed"}:
        raise ReleaseGateError("gate_status must be open or closed")
    calculated_open = bool(pending)
    if (gate_status == "open") != calculated_open:
        raise ReleaseGateError("gate status does not match the requirement checklist")
    if publish_allowed != (not calculated_open):
        raise ReleaseGateError("publish_allowed does not fail closed with the checklist")
    return publish_allowed, tuple(sorted(pending))


def release_status(
    path: Path, *, evidence_root: Path | None = None
) -> tuple[bool, tuple[str, ...]]:
    """Return release state, normalizing every malformed input to a fail-closed error."""

    try:
        return _release_status(path, repository_root() if evidence_root is None else evidence_root)
    except (OSError, ValueError) as error:
        if isinstance(error, ReleaseGateError):
            raise
        raise ReleaseGateError(str(error)) from error


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--manifest",
        type=Path,
        default=repository_root() / "tools/specs/licensing.toml",
    )
    parser.add_argument(
        "--evidence-root",
        type=Path,
        default=repository_root(),
        help="repository root against which evidence paths are resolved",
    )
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--assert-blocked", action="store_true")
    mode.add_argument("--require-publishable", action="store_true")
    args = parser.parse_args(argv)
    try:
        publish_allowed, pending = release_status(args.manifest, evidence_root=args.evidence_root)
    except (OSError, ValueError) as error:
        print(f"release gate invalid and publication denied: {error}")
        return 1
    if args.assert_blocked:
        if publish_allowed:
            print("release gate unexpectedly permits publication")
            return 1
        print(f"publication correctly blocked by LIC-001: {', '.join(pending)}")
        return 0
    if args.require_publishable and not publish_allowed:
        print(f"publication denied by LIC-001: {', '.join(pending)}")
        return 1
    print("publication permitted" if publish_allowed else "release gate valid; publication blocked")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
