from __future__ import annotations

import json
from collections.abc import Mapping
from pathlib import Path
from typing import Any

import pyowl_core.model as owl
import pytest

from pyhermit.datatypes import (
    DomainCardinalityConstraint,
    SemanticDatatypeConstraintComponent,
    SemanticFixedValueConstraint,
    SemanticRangeConstraint,
    compile_datatype_constraint_component,
    compile_datatype_semantic_model,
    compile_literal_semantic_payload,
    solve_datatype_constraints,
)

DATA = Path(__file__).parents[1] / "data"
CASES_PATH = DATA / "datatypes/ontology-component-cases-v1.json"
CASES = json.loads(CASES_PATH.read_text())["cases"]
PREFIXES = {
    "owl": "http://www.w3.org/2002/07/owl#",
    "rdf": "http://www.w3.org/1999/02/22-rdf-syntax-ns#",
    "xsd": "http://www.w3.org/2001/XMLSchema#",
}


def _iri(value: str) -> str:
    prefix, separator, local = value.partition(":")
    if separator and prefix in PREFIXES:
        return PREFIXES[prefix] + local
    return value


def _datatype(value: str) -> owl.Datatype:
    return owl.Datatype(owl.IRI(_iri(value)))


def _literal(spec: Mapping[str, Any]) -> owl.Literal:
    return owl.Literal(
        spec["lexical"],
        _datatype(spec["datatype"]),
        spec.get("language"),
    )


def _data_range(spec: Mapping[str, Any]) -> owl.DataRange:
    kind = spec["kind"]
    if kind == "datatype":
        return _datatype(spec["iri"])
    if kind == "restriction":
        facets = tuple(
            owl.FacetRestriction(owl.IRI(_iri(item["iri"])), _literal(item["value"]))
            for item in spec["facets"]
        )
        return owl.DatatypeRestriction(_datatype(spec["datatype"]), owl.CanonicalSet(facets))
    if kind == "one_of":
        return owl.DataOneOf(owl.CanonicalSet(tuple(_literal(item) for item in spec["values"])))
    if kind == "complement":
        return owl.DataComplementOf(_data_range(spec["operand"]))
    if kind == "intersection":
        return owl.DataIntersectionOf(
            owl.CanonicalSet(tuple(_data_range(item) for item in spec["operands"]))
        )
    if kind == "union":
        return owl.DataUnionOf(
            owl.CanonicalSet(tuple(_data_range(item) for item in spec["operands"]))
        )
    raise AssertionError(f"unknown project-authored data-range kind {kind!r}")


def _solve_projection(case: Mapping[str, Any]) -> bool:
    assertions = case.get("assertions", ())
    roots = tuple(_data_range(item["range"]) for item in assertions)
    model = compile_datatype_semantic_model(roots)
    semantic = SemanticDatatypeConstraintComponent(
        variables=tuple(case["variables"]),
        ranges=tuple(
            SemanticRangeConstraint(
                item["variable"],
                index,
                item.get("positive", True),
                frozenset({1000 + index}),
            )
            for index, item in enumerate(assertions)
        ),
        fixed_values=tuple(
            SemanticFixedValueConstraint(
                item["variable"],
                compile_literal_semantic_payload(_literal(item)),
                frozenset({2000 + index}),
            )
            for index, item in enumerate(case.get("fixed_values", ()))
        ),
        cardinalities=tuple(
            DomainCardinalityConstraint(
                item["variable"],
                item["minimum"],
                frozenset({3000 + index}),
            )
            for index, item in enumerate(case.get("minimum_cardinalities", ()))
        ),
    )
    executable = compile_datatype_constraint_component(model, semantic)
    return solve_datatype_constraints(executable).satisfiable


EXECUTABLE_CASES = [case for case in CASES if case["projection_kind"] == "datatype-component"]


@pytest.mark.parametrize("case", EXECUTABLE_CASES, ids=lambda case: case["id"])
def test_pinned_ontology_datatype_component_projection(case: Mapping[str, Any]) -> None:
    assert _solve_projection(case) is (case["expected"] == "SAT")


def test_projection_sources_are_pinned_without_copying_external_ontology_bodies() -> None:
    w3c = json.loads((DATA / "w3c/approved-direct-dl-inventory.json").read_text())
    w3c_by_identifier = {case["identifier"]: case for case in w3c["cases"]}
    hermit = json.loads((DATA / "datatypes/hermit-datatype-inventory-v1.json").read_text())
    hermit_methods = {
        f"{entry['path']}::{method}": entry["sha256"]
        for entry in hermit["files"]
        for method in entry["methods"]
    }
    for case in CASES:
        source = case["source"]
        if source["kind"] == "w3c":
            inventory_case = w3c_by_identifier[source["identifier"]]
            assert inventory_case["iri"] == source["iri"]
            assert source["premise_sha256"] in {
                body["sha256"] for body in inventory_case["body_metadata"].values()
            }
        else:
            assert hermit_methods[source["method_id"]] == source["source_sha256"]

    fixture_text = CASES_PATH.read_text()
    assert "Ontology(" not in fixture_text
    assert len(CASES) == 24
    assert len(EXECUTABLE_CASES) == 23


def test_tableau_only_datatype_named_case_is_not_overclaimed_as_component_coverage() -> None:
    deferred = [case for case in CASES if case["projection_kind"] == "tableau-only"]
    assert [case["id"] for case in deferred] == ["w3c-inconsistent-integer-filler"]
    assert "class subsumption" in deferred[0]["reason"]
    assert set(deferred[0]).isdisjoint({"variables", "assertions", "fixed_values"})


def test_complete_pinned_hermit_datatype_method_inventory_is_reproducible() -> None:
    from tools.datatypes.build_inventory import build_inventory

    generated = build_inventory(DATA / "reference/upstream-test-inventory.json")
    committed = json.loads((DATA / "datatypes/hermit-datatype-inventory-v1.json").read_text())
    assert committed == generated
    assert committed["counts"] == {
        "files": 9,
        "methods": 256,
        "methods_by_lane": {
            "clausification-WP06": 32,
            "datatype-library-WP07": 165,
            "ontology-tableau-WP12": 59,
        },
    }
    assert all(entry["methods"] for entry in committed["files"])
