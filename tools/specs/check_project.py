"""Validate WP00 project, reference, dependency, licensing, and target metadata."""

from __future__ import annotations

import argparse
import json
import re
from collections.abc import Sequence
from pathlib import Path
from typing import Any

from tools.specs._compat import (
    load_toml,
    repository_root,
    require_bool,
    require_int,
    require_list,
    require_mapping,
    require_str,
)

REFERENCE = {
    "compatibility_label": "hermit-master-37ec30a",
    "repository": "https://github.com/phillord/hermit-reasoner",
    "commit": "37ec30aced32ac81ebecc5e33fad255ddefcb4c3",
    "commit_date_utc": "2017-10-04T08:39:39Z",
    "upstream_version": "1.4.0.0-SNAPSHOT",
    "upstream_license": "LGPL-3.0-or-later",
}
EXPECTED_TARGETS = {
    ("manylinux_2_17", "x86_64"),
    ("manylinux_2_17", "aarch64"),
    ("musllinux_1_2", "x86_64"),
    ("musllinux_1_2", "aarch64"),
    ("macos", "x86_64"),
    ("macos", "arm64"),
    ("windows", "AMD64"),
    ("windows", "ARM64"),
}


class ProjectCheckError(ValueError):
    """A WP00 metadata invariant is broken."""


def _normalized_name(value: str) -> str:
    return re.sub(r"[-_.]+", "-", value).lower()


def _requirement_name(value: str) -> str:
    match = re.match(r"^\s*([A-Za-z0-9][A-Za-z0-9._-]*)", value)
    if match is None:
        raise ProjectCheckError(f"invalid requirement: {value!r}")
    return _normalized_name(match.group(1))


def _table_path(config: dict[str, Any], key: str, root: Path) -> Path:
    return root / require_str(config.get(key), f"tool.pyhermit.{key}")


def _validate_project_metadata(root: Path, pyproject: dict[str, Any]) -> dict[str, Any]:
    project = require_mapping(pyproject.get("project"), "project")
    if require_str(project.get("name"), "project.name") != "pyHermiT":
        raise ProjectCheckError("project.name must remain pyHermiT")
    if "version" in project:
        raise ProjectCheckError("project.version must use the runtime single source")
    dynamic = {
        require_str(value, "project.dynamic item")
        for value in require_list(project.get("dynamic"), "project.dynamic")
    }
    if dynamic != {"version"}:
        raise ProjectCheckError("project.dynamic must contain only version")
    tool = require_mapping(pyproject.get("tool"), "tool")
    setuptools = require_mapping(tool.get("setuptools"), "tool.setuptools")
    setuptools_dynamic = require_mapping(setuptools.get("dynamic"), "tool.setuptools.dynamic")
    version_config = require_mapping(
        setuptools_dynamic.get("version"), "tool.setuptools.dynamic.version"
    )
    if require_str(version_config.get("attr"), "dynamic version attr") != (
        "pyhermit._version.__version__"
    ):
        raise ProjectCheckError("setuptools must read pyhermit._version.__version__")
    version_source = (root / "src/pyhermit/_version.py").read_text(encoding="utf-8")
    match = re.search(r'^__version__ = "([^"]+)"$', version_source, flags=re.MULTILINE)
    if match is None or match.group(1) != "0.1.0.dev0":
        raise ProjectCheckError("runtime version source must be 0.1.0.dev0")
    if require_str(project.get("requires-python"), "project.requires-python") != ">=3.10":
        raise ProjectCheckError("project requires-python must be >=3.10")
    if require_str(project.get("license"), "project.license") != "LGPL-3.0-or-later":
        raise ProjectCheckError("project license must be LGPL-3.0-or-later")
    license_files = set(
        require_str(value, "project.license-files item")
        for value in require_list(project.get("license-files"), "project.license-files")
    )
    if license_files != {"LICENSE", "COPYING", "NOTICE.md"}:
        raise ProjectCheckError(f"unexpected license file set: {sorted(license_files)}")
    for relative in license_files:
        if not (root / relative).is_file():
            raise ProjectCheckError(f"missing project license file: {relative}")
    dependencies = [
        require_str(item, "project.dependencies item")
        for item in require_list(project.get("dependencies"), "project.dependencies")
    ]
    if dependencies != ["pyowl-core>=0.1,<0.2"]:
        raise ProjectCheckError("pyowl-core>=0.1,<0.2 must be the sole runtime dependency")
    return project


def _requirements_by_scope(pyproject: dict[str, Any], root: Path) -> dict[tuple[str, str], str]:
    result: dict[tuple[str, str], str] = {}

    def add(scope: str, raw: object, context: str) -> None:
        for item in require_list(raw, context):
            requirement = require_str(item, f"{context} item")
            key = (scope, _requirement_name(requirement))
            if key in result:
                raise ProjectCheckError(f"duplicate {scope} requirement for {key[1]}")
            result[key] = requirement

    build_system = require_mapping(pyproject.get("build-system"), "build-system")
    project = require_mapping(pyproject.get("project"), "project")
    optional = require_mapping(project.get("optional-dependencies"), "optional-dependencies")
    add("build", build_system.get("requires"), "build-system.requires")
    add("runtime", project.get("dependencies"), "project.dependencies")
    add("development", optional.get("dev"), "project.optional-dependencies.dev")

    tool = require_mapping(pyproject.get("tool"), "tool")
    pyhermit = require_mapping(tool.get("pyhermit"), "tool.pyhermit")
    verifier_path = _table_path(pyhermit, "release_verifier_requirements", root)
    verifier_requirement = verifier_path.read_text(encoding="utf-8")
    verifier_match = re.fullmatch(
        r"([A-Za-z0-9_.-]+)==([A-Za-z0-9_.+-]+) "
        r"--hash=sha256:([0-9a-f]{64})\n",
        verifier_requirement,
    )
    if verifier_match is None:
        raise ProjectCheckError("release verifier requirement must have one exact SHA-256 pin")
    verifier_name, verifier_version, _verifier_hash = verifier_match.groups()
    result[("release-verifier", _normalized_name(verifier_name))] = (
        f"{verifier_name}=={verifier_version}"
    )
    probe_path = _table_path(pyhermit, "packaging_probe_native_manifest", root)
    probe = load_toml(probe_path)
    probe_package = require_mapping(probe.get("package"), "packaging probe package")
    if require_str(probe_package.get("edition"), "packaging probe edition") != "2021":
        raise ProjectCheckError("packaging probe must use Rust edition 2021 at MSRV 1.83")
    if require_str(probe_package.get("rust-version"), "packaging probe MSRV") != "1.83":
        raise ProjectCheckError("packaging probe Rust MSRV must be 1.83")
    if require_bool(probe_package.get("publish"), "packaging probe publish"):
        raise ProjectCheckError("packaging probe crate must not be publishable")
    probe_dependencies = require_mapping(probe.get("dependencies"), "probe dependencies")
    pyo3 = require_mapping(probe_dependencies.get("pyo3"), "probe dependency pyo3")
    version = require_str(pyo3.get("version"), "probe pyo3 version")
    features = {
        require_str(item, "probe pyo3 feature")
        for item in require_list(pyo3.get("features"), "probe pyo3 features")
    }
    if features != {"extension-module", "abi3-py310"}:
        raise ProjectCheckError(f"unexpected probe pyo3 features: {sorted(features)}")
    result[("development-probe", "pyo3")] = f"pyo3=={version}"

    native = load_toml(root / "native/Cargo.toml")
    for table_name, scope in (
        ("dependencies", "native-runtime"),
        ("build-dependencies", "native-build"),
        ("dev-dependencies", "native-development"),
    ):
        dependencies = require_mapping(native.get(table_name), f"native {table_name}")
        for crate, raw in dependencies.items():
            if isinstance(raw, str):
                cargo_version = raw
            else:
                dependency = require_mapping(raw, f"native {table_name}.{crate}")
                cargo_version = require_str(
                    dependency.get("version"), f"native {table_name}.{crate}.version"
                )
            if not cargo_version.startswith("=") or cargo_version.startswith("=="):
                raise ProjectCheckError(f"native dependency must use an exact Cargo pin: {crate}")
            requirement = f"{crate}=={cargo_version[1:]}"
            key = (scope, _normalized_name(crate))
            if key in result:
                raise ProjectCheckError(f"duplicate {scope} requirement for {key[1]}")
            result[key] = requirement
    return result


def _validate_dependencies(root: Path, pyproject: dict[str, Any], path: Path) -> int:
    expected = _requirements_by_scope(pyproject, root)
    data = load_toml(path)
    if require_int(data.get("schema"), "dependency schema") != 1:
        raise ProjectCheckError("dependency manifest schema must be 1")
    actual: dict[tuple[str, str], str] = {}
    for index, raw in enumerate(require_list(data.get("dependency"), "dependency")):
        table = require_mapping(raw, f"dependency[{index}]")
        name = _normalized_name(require_str(table.get("name"), f"dependency[{index}].name"))
        scope = require_str(table.get("scope"), f"dependency[{index}].scope")
        requirement = require_str(table.get("requirement"), f"dependency[{index}].requirement")
        key = (scope, name)
        if key in actual:
            raise ProjectCheckError(f"duplicate dependency record: {scope}:{name}")
        if _requirement_name(requirement) != name:
            raise ProjectCheckError(f"dependency record name/requirement mismatch: {name}")
        require_str(table.get("license"), f"dependency[{index}].license")
        source = require_str(table.get("source"), f"dependency[{index}].source")
        if not source.startswith("https://"):
            raise ProjectCheckError(f"dependency source must be HTTPS: {name}")
        require_str(table.get("purpose"), f"dependency[{index}].purpose")
        require_str(table.get("linkage"), f"dependency[{index}].linkage")
        require_str(table.get("audit_owner"), f"dependency[{index}].audit_owner")
        require_bool(table.get("shipped"), f"dependency[{index}].shipped")
        actual[key] = requirement
    if actual != expected:
        missing = sorted(expected.keys() - actual.keys())
        extra = sorted(actual.keys() - expected.keys())
        mismatched = sorted(
            key for key in expected.keys() & actual.keys() if expected[key] != actual[key]
        )
        raise ProjectCheckError(
            f"dependency manifest mismatch; missing={missing}, extra={extra}, "
            f"requirements={mismatched}"
        )
    return len(actual)


def _validate_reference(path: Path, root: Path) -> int:
    data = load_toml(path)
    if require_int(data.get("schema"), "reference schema") != 1:
        raise ProjectCheckError("reference manifest schema must be 1")
    reference = require_mapping(data.get("reference"), "reference")
    for key, expected in REFERENCE.items():
        actual = require_str(reference.get(key), f"reference.{key}")
        if actual != expected:
            raise ProjectCheckError(f"reference.{key} is {actual!r}, expected {expected!r}")
    if require_int(reference.get("production_java_files"), "production_java_files") != 200:
        raise ProjectCheckError("reference production Java file count must be 200")
    if require_bool(reference.get("source_in_distribution"), "source_in_distribution"):
        raise ProjectCheckError("the Java reference cannot be included in distributions")
    fate_map = root / require_str(reference.get("fate_map"), "reference.fate_map")
    if not fate_map.is_file():
        raise ProjectCheckError(f"reference fate map is missing: {fate_map}")
    areas = require_list(data.get("area"), "reference area")
    if len(areas) < 10:
        raise ProjectCheckError("reference manifest must classify every top-level source family")
    for index, raw in enumerate(areas):
        table = require_mapping(raw, f"area[{index}]")
        require_str(table.get("path"), f"area[{index}].path")
        require_str(table.get("fate"), f"area[{index}].fate")
        require_str(table.get("owner"), f"area[{index}].owner")
    spec = fate_map.read_text(encoding="utf-8")
    spec_expected = {value for key, value in REFERENCE.items() if key != "commit_date_utc"}
    spec_expected.add("2017-10-04 08:39:39 UTC")
    for expected in spec_expected:
        if expected not in spec:
            raise ProjectCheckError(f"reference fate map does not contain {expected!r}")
    return len(areas)


def _validate_licensing(path: Path, root: Path) -> tuple[int, int]:
    data = load_toml(path)
    if require_int(data.get("schema"), "licensing schema") != 1:
        raise ProjectCheckError("licensing manifest schema must be 1")
    if require_str(data.get("gate_id"), "gate_id") != "LIC-001":
        raise ProjectCheckError("license gate must be LIC-001")
    if require_str(data.get("decision_status"), "decision_status") != "recorded":
        raise ProjectCheckError("the owner license decision must be recorded")
    if require_str(data.get("implementation_mode"), "implementation_mode") != "source-guided":
        raise ProjectCheckError("implementation mode must remain source-guided")
    if require_str(data.get("project_license"), "project_license") != "LGPL-3.0-or-later":
        raise ProjectCheckError("license gate project license is inconsistent")
    if require_bool(data.get("publish_allowed"), "publish_allowed"):
        raise ProjectCheckError("WP00 must fail closed: publish_allowed cannot be true")
    requirements = require_list(data.get("requirement"), "licensing requirement")
    statuses: list[str] = []
    seen: set[str] = set()
    for index, raw in enumerate(requirements):
        table = require_mapping(raw, f"requirement[{index}]")
        requirement_id = require_str(table.get("id"), f"requirement[{index}].id")
        if requirement_id in seen:
            raise ProjectCheckError(f"duplicate licensing requirement: {requirement_id}")
        seen.add(requirement_id)
        status = require_str(table.get("status"), f"requirement[{index}].status")
        if status not in {"complete", "pending"}:
            raise ProjectCheckError(f"invalid licensing requirement status: {status}")
        evidence = table.get("evidence")
        if not isinstance(evidence, str):
            raise ProjectCheckError(f"requirement[{index}].evidence must be a string")
        if status == "complete":
            if not evidence:
                raise ProjectCheckError(
                    f"completed licensing requirement lacks evidence: {requirement_id}"
                )
            for relative in evidence.split(","):
                if not (root / relative).exists():
                    raise ProjectCheckError(
                        f"licensing evidence for {requirement_id} is missing: {relative}"
                    )
        statuses.append(status)
    pending = statuses.count("pending")
    if not pending or require_str(data.get("gate_status"), "gate_status") != "open":
        raise ProjectCheckError("LIC-001 must remain open while requirements are pending")
    return len(statuses), pending


def _validate_index_record(path: Path) -> int:
    data = load_toml(path)
    if require_int(data.get("schema"), "index-name schema") != 1:
        raise ProjectCheckError("index-name schema must be 1")
    selected = require_str(data.get("selected_distribution"), "selected_distribution")
    if _normalized_name(selected) != "pyhermit":
        raise ProjectCheckError("selected distribution does not normalize to pyhermit")
    if require_str(data.get("normalized_name"), "normalized_name") != "pyhermit":
        raise ProjectCheckError("normalized index name must be pyhermit")
    if require_str(data.get("import_namespace"), "import_namespace") != "pyhermit":
        raise ProjectCheckError("import namespace must be pyhermit")
    if not require_bool(data.get("availability_is_not_a_reservation"), "availability caveat"):
        raise ProjectCheckError(
            "the index record must state that availability is not a reservation"
        )
    for index_name in ("pypi", "testpypi"):
        table = require_mapping(data.get(index_name), index_name)
        if require_int(table.get("http_status"), f"{index_name}.http_status") != 404:
            raise ProjectCheckError(f"{index_name} result must record the observed 404")
        if require_bool(table.get("project_found"), f"{index_name}.project_found"):
            raise ProjectCheckError(f"{index_name} unexpectedly records a project collision")
    collisions = require_list(data.get("known_collision"), "known_collision")
    if not any(
        require_str(
            require_mapping(item, "known_collision item").get("normalized_name"),
            "collision name",
        )
        == "hermit-reasoner"
        for item in collisions
    ):
        raise ProjectCheckError("existing hermit-reasoner distribution must be recorded")
    return len(collisions)


def _validate_targets(path: Path) -> int:
    data = load_toml(path)
    if require_int(data.get("schema"), "native target schema") != 1:
        raise ProjectCheckError("native target schema must be 1")
    expected_status = "configured-awaiting-hosted-validation"
    if require_str(data.get("status"), "native target status") != expected_status:
        raise ProjectCheckError("WPP0 target matrix must await hosted validation")
    workflow = path.parent.parent.parent / require_str(
        data.get("workflow"), "native target workflow"
    )
    if not workflow.is_file():
        raise ProjectCheckError(f"native wheel workflow is missing: {workflow}")
    actual: set[tuple[str, str]] = set()
    for index, raw in enumerate(require_list(data.get("target"), "native targets")):
        table = require_mapping(raw, f"target[{index}]")
        target = (
            require_str(table.get("platform"), f"target[{index}].platform"),
            require_str(table.get("architecture"), f"target[{index}].architecture"),
        )
        if require_str(table.get("status"), f"target[{index}].status") != expected_status:
            raise ProjectCheckError(f"native target must await hosted validation: {target}")
        if target in actual:
            raise ProjectCheckError(f"duplicate native target: {target}")
        actual.add(target)
    if actual != EXPECTED_TARGETS:
        raise ProjectCheckError(f"native target matrix mismatch: {sorted(actual)}")
    return len(actual)


def validate_project(root: Path) -> dict[str, int]:
    pyproject = load_toml(root / "pyproject.toml")
    _validate_project_metadata(root, pyproject)
    config = require_mapping(pyproject.get("tool"), "tool")
    pyhermit = require_mapping(config.get("pyhermit"), "tool.pyhermit")
    normalized = require_str(pyhermit.get("distribution_normalized_name"), "normalized name")
    if normalized != "pyhermit":
        raise ProjectCheckError("tool.pyhermit distribution name must be pyhermit")
    rust_license_inventory = _table_path(
        pyhermit,
        "rust_production_license_manifest",
        root,
    )
    if not rust_license_inventory.is_file():
        raise ProjectCheckError(
            f"Rust production license inventory is missing: {rust_license_inventory}"
        )
    release_verifier_requirements = _table_path(
        pyhermit,
        "release_verifier_requirements",
        root,
    )
    if not release_verifier_requirements.is_file():
        raise ProjectCheckError(
            f"release verifier requirements are missing: {release_verifier_requirements}"
        )
    cargo = load_toml(root / "Cargo.toml")
    workspace_package = require_mapping(
        require_mapping(cargo.get("workspace"), "Cargo workspace").get("package"),
        "Cargo workspace.package",
    )
    cargo_license = require_str(workspace_package.get("license"), "Cargo workspace license")
    if cargo_license != "LGPL-3.0-or-later":
        raise ProjectCheckError("Cargo workspace license must match the project")
    requirements, pending = _validate_licensing(
        _table_path(pyhermit, "license_gate_manifest", root), root
    )
    return {
        "dependencies": _validate_dependencies(
            root, pyproject, _table_path(pyhermit, "dependency_manifest", root)
        ),
        "reference_areas": _validate_reference(
            _table_path(pyhermit, "reference_manifest", root), root
        ),
        "licensing_requirements": requirements,
        "licensing_pending": pending,
        "known_name_collisions": _validate_index_record(
            _table_path(pyhermit, "index_name_record", root)
        ),
        "planned_native_targets": _validate_targets(
            _table_path(pyhermit, "native_target_manifest", root)
        ),
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=repository_root())
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)
    try:
        summary = validate_project(args.root.resolve())
    except (OSError, ValueError) as error:
        print(f"project metadata invalid: {error}")
        return 1
    if args.json:
        print(json.dumps(summary, sort_keys=True))
    else:
        print(
            "project metadata valid: "
            f"{summary['dependencies']} dependencies, "
            f"{summary['reference_areas']} reference areas, "
            f"{summary['licensing_pending']} LIC-001 items pending, "
            f"{summary['planned_native_targets']} native targets configured "
            "pending hosted validation"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
