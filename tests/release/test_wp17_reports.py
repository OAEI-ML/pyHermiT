from __future__ import annotations

import json
import re
from copy import deepcopy
from pathlib import Path
from typing import Any

from pyowl_core import (
    IRI,
    MODEL_CONSTRUCTORS,
    BackendPreference,
    CanonicalSet,
    Class,
    ImportPolicy,
    LoadOptions,
    OntologyDelta,
    SubClassOf,
    apply_delta,
    compose_views,
    load_snapshot,
)

from pyhermit import BackendName, Reasoner, ReasonerConfig

ROOT = Path(__file__).resolve().parents[2]
REPORTS = ROOT / "reports"
PUBLISHED_REVISION = "777725b3bf054dfc0bd0d3b98cc133c4b0469ca1"
PUBLICATION_RECORD = "reports/release/0.1.1-publication.md"
PUBLISHED_ARTIFACTS = {
    "pyhermit-0.1.1-py3-none-any.whl": (
        "pure-wheel",
        "631286d9a6f75a1b87aac14a56064ea43f6c77e5017423b4b6e1851ae698222e",
    ),
    "pyhermit-0.1.1.tar.gz": (
        "sdist",
        "0f010bd7db6a06827e0637594dfc553e5e27b21a9064e9856bca0a95b06c96da",
    ),
}
PUBLISHED_SIZES = {
    "pyhermit-0.1.1-py3-none-any.whl": "407,310",
    "pyhermit-0.1.1.tar.gz": "1,290,670",
}


def _load(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def _type_matches(expected: str | list[str], value: object) -> bool:
    if isinstance(expected, list):
        return any(_type_matches(item, value) for item in expected)
    if expected == "object":
        return isinstance(value, dict)
    if expected == "array":
        return isinstance(value, list)
    if expected == "string":
        return isinstance(value, str)
    if expected == "integer":
        return isinstance(value, int) and not isinstance(value, bool)
    if expected == "number":
        return isinstance(value, (int, float)) and not isinstance(value, bool)
    if expected == "boolean":
        return isinstance(value, bool)
    if expected == "null":
        return value is None
    raise AssertionError(f"unsupported test validator type: {expected}")


def _validate(schema: dict[str, Any], value: object, root: dict[str, Any], path: str) -> None:
    reference = schema.get("$ref")
    if reference is not None:
        assert isinstance(reference, str) and reference.startswith("#/")
        resolved: object = root
        for component in reference[2:].split("/"):
            assert isinstance(resolved, dict)
            resolved = resolved[component]
        assert isinstance(resolved, dict)
        _validate(resolved, value, root, path)
        return
    if "const" in schema:
        assert value == schema["const"], f"{path} does not match const"
    if "enum" in schema:
        assert value in schema["enum"], f"{path} is outside enum"
    expected = schema.get("type")
    if expected is not None:
        assert isinstance(expected, (str, list)) and _type_matches(expected, value), (
            f"{path} must be {expected}"
        )
    if isinstance(value, str):
        if "minLength" in schema:
            assert len(value) >= schema["minLength"], f"{path} is too short"
        if "pattern" in schema:
            assert re.search(schema["pattern"], value), f"{path} does not match pattern"
    if isinstance(value, (int, float)) and not isinstance(value, bool) and "minimum" in schema:
        assert value >= schema["minimum"], f"{path} is below minimum"
    if isinstance(value, list):
        if "minItems" in schema:
            assert len(value) >= schema["minItems"], f"{path} has too few items"
        item_schema = schema.get("items")
        if item_schema is not None:
            assert isinstance(item_schema, dict)
            for index, item in enumerate(value):
                _validate(item_schema, item, root, f"{path}[{index}]")
    if isinstance(value, dict):
        required = schema.get("required", [])
        assert set(required).issubset(value), f"{path} lacks required fields"
        properties = schema.get("properties", {})
        assert isinstance(properties, dict)
        if schema.get("additionalProperties") is False:
            assert set(value).issubset(properties), f"{path} has unexpected fields"
        for name, item in value.items():
            child_schema = properties.get(name)
            if child_schema is not None:
                assert isinstance(child_schema, dict)
                _validate(child_schema, item, root, f"{path}.{name}")


def _assert_evidence(paths: list[str]) -> None:
    assert paths
    for relative in paths:
        assert isinstance(relative, str) and relative
        assert (ROOT / relative).is_file(), f"missing release evidence: {relative}"


def _expected_overall_status(report: dict[str, Any]) -> str:
    statuses = [item["status"] for item in report["suites"]]
    statuses.extend(item["status"] for item in report["backend_matrix"])
    statuses.extend(item["status"] for item in report["artifacts"])
    statuses.extend(item["status"] for item in report["external_gates"])
    return "fail" if "fail" in statuses else "blocked" if "blocked" in statuses else "pass"


def test_committed_release_report_conforms_and_records_owner_gate_closures() -> None:
    schema = _load(REPORTS / "schema" / "release-report-v1.schema.json")
    report = _load(REPORTS / "release-report-local.json")
    _validate(schema, report, schema, "release-report")

    for suite in report["suites"]:
        _assert_evidence(suite["evidence"])
    for backend in report["backend_matrix"]:
        _assert_evidence(backend["evidence"])
    for artifact in report["artifacts"]:
        _assert_evidence([artifact["evidence"]])
    for gate in report["external_gates"]:
        _assert_evidence(gate["evidence"])

    assert report["overall_status"] == _expected_overall_status(report)
    assert report["overall_status"] == "pass"
    assert {item["backend"] for item in report["backend_matrix"]} == {
        "python",
        "native",
        "auto",
        "verify",
    }


def test_release_report_binds_the_exact_universal_pypi_publication() -> None:
    report = _load(REPORTS / "release-report-local.json")
    assert report["package_version"] == "0.1.1"
    assert report["revision"] == PUBLISHED_REVISION
    assert len(report["artifacts"]) == len(PUBLISHED_ARTIFACTS)

    observed = {
        artifact["filename"]: (artifact["kind"], artifact["sha256"])
        for artifact in report["artifacts"]
    }
    assert observed == PUBLISHED_ARTIFACTS
    assert all(
        artifact["source_revision"] == PUBLISHED_REVISION
        for artifact in report["artifacts"]
    )
    assert all(artifact["evidence"] == PUBLICATION_RECORD for artifact in report["artifacts"])
    assert all(artifact["kind"] != "native-wheel" for artifact in report["artifacts"])

    publication = (ROOT / PUBLICATION_RECORD).read_text(encoding="utf-8")
    assert "https://pypi.org/project/pyHermiT/0.1.1/" in publication
    assert PUBLISHED_REVISION in publication
    assert "universal-only" in publication
    assert "no native-artifact publication claim" in publication
    for filename, (_kind, sha256) in PUBLISHED_ARTIFACTS.items():
        assert filename in publication
        assert sha256 in publication
        assert PUBLISHED_SIZES[filename] in publication


def test_release_status_reducer_fails_closed_for_every_local_and_external_lane() -> None:
    report = _load(REPORTS / "release-report-local.json")
    lanes = ("suites", "backend_matrix", "artifacts", "external_gates")
    for lane in lanes:
        candidate = deepcopy(report)
        for collection in lanes:
            for item in candidate[collection]:
                item["status"] = "pass"
        candidate[lane][0]["status"] = "fail"
        assert _expected_overall_status(candidate) == "fail"
        candidate[lane][0]["status"] = "blocked"
        assert _expected_overall_status(candidate) == "blocked"


def test_coverage_matrix_matches_the_live_constructor_and_facade_contracts() -> None:
    schema = _load(REPORTS / "schema" / "coverage-matrix-v1.schema.json")
    matrix = _load(REPORTS / "coverage-matrix.json")
    _validate(schema, matrix, schema, "coverage-matrix")

    constructor = matrix["constructor_contract"]
    assert constructor["count"] == len(MODEL_CONSTRUCTORS)
    for field in ("positive", "negative", "interaction"):
        _assert_evidence(constructor[field])

    expected_members = {
        name
        for name, value in Reasoner.__dict__.items()
        if not name.startswith("_") and (callable(value) or isinstance(value, property))
    }
    observed_members: list[str] = []
    for group in matrix["operation_groups"]:
        observed_members.extend(group["members"])
        assert set(group["backends"]) == {"python", "native", "auto", "verify"}
        for field in ("positive", "negative", "interaction"):
            _assert_evidence(group[field])
    assert len(observed_members) == len(set(observed_members))
    assert set(observed_members) == expected_members

    for interaction in matrix["high_risk_interactions"]:
        _assert_evidence(interaction["evidence"])


def test_documentation_links_and_standalone_example_are_reproducible() -> None:
    for document in sorted((ROOT / "docs").glob("*.md")):
        for target in re.findall(r"\[[^]]+\]\(([^)]+)\)", document.read_text(encoding="utf-8")):
            relative = target.split("#", 1)[0]
            if not relative or "://" in relative or relative.startswith("mailto:"):
                continue
            assert (document.parent / relative).resolve().is_file(), (
                f"broken documentation link in {document.name}: {target}"
            )

    options = LoadOptions(
        imports=ImportPolicy.RESOLVE_STRICT,
        backend=BackendPreference.PYTHON,
    )
    source = (
        b"Prefix(:=<urn:guide#>) Ontology(<urn:guide> "
        b"Declaration(Class(:A)) Declaration(Class(:B)) SubClassOf(:A :B))"
    )
    snapshot = load_snapshot(source, options=options)
    with Reasoner(
        snapshot,
        config=ReasonerConfig(backend=BackendName.PYTHON),
    ) as reasoner:
        assert reasoner.ontology is snapshot
        assert reasoner.is_consistent()

    target = load_snapshot(
        b"Prefix(:=<urn:target#>) Ontology(<urn:target> Declaration(Class(:C)))",
        options=options,
    )
    bridge_axiom = SubClassOf(Class(IRI("urn:guide#A")), Class(IRI("urn:target#C")))
    candidate_source = apply_delta(
        snapshot,
        OntologyDelta(add_axioms=CanonicalSet((bridge_axiom,))),
    )
    combined = compose_views(candidate_source, target, roles=("source", "target"))
    with Reasoner(
        combined,
        config=ReasonerConfig(backend=BackendName.PYTHON),
    ) as reasoner:
        assert reasoner.ontology is combined
        assert reasoner.is_consistent()


def test_api_reference_names_every_stable_reasoner_member() -> None:
    documented = (ROOT / "docs" / "api-reference.md").read_text(encoding="utf-8")
    expected_members = {
        name
        for name, value in Reasoner.__dict__.items()
        if not name.startswith("_") and (callable(value) or isinstance(value, property))
    }
    missing = sorted(name for name in expected_members if f"`Reasoner.{name}`" not in documented)
    assert not missing, f"API reference omits stable Reasoner members: {missing}"
