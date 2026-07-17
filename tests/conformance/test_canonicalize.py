from __future__ import annotations

import json
from pathlib import Path

import pytest

from tools.reference.canonicalize import (
    CanonicalizationError,
    canonical_blank_node_triples,
    canonical_boolean,
    canonical_error,
    canonical_hierarchy,
    canonical_same_as,
    inverse_property,
    literal,
    typed_iri,
)

DATA = Path(__file__).parents[1] / "data/reference"


def test_typed_iri_and_inverse_property_are_explicit() -> None:
    assert canonical_boolean(True) is True
    with pytest.raises(CanonicalizationError):
        canonical_boolean(1)
    assert typed_iri("urn:test:A") == {"kind": "iri", "value": "urn:test:A"}
    assert inverse_property("urn:test:p") == {
        "kind": "inverse_object_property",
        "property": {"kind": "iri", "value": "urn:test:p"},
    }
    with pytest.raises(CanonicalizationError):
        typed_iri("relative")


def test_literal_keeps_term_identity_separate_from_value_identity() -> None:
    first = literal(
        "01",
        datatype="http://www.w3.org/2001/XMLSchema#integer",
        value_key="integer:1",
        comparison_key="numeric:1",
    )
    second = literal(
        "1",
        datatype="http://www.w3.org/2001/XMLSchema#integer",
        value_key="integer:1",
        comparison_key="numeric:1",
    )
    assert first["value_key"] == second["value_key"]
    assert first["comparison_key"] == second["comparison_key"]
    assert first["term_key"] != second["term_key"]
    assert literal("hello", language="EN")["language"] == "en"


def test_hierarchy_and_same_as_ignore_source_set_order() -> None:
    expected = canonical_hierarchy(
        [["urn:test:A", "urn:test:A2"], ["urn:test:B"]],
        [(["urn:test:B"], ["urn:test:A", "urn:test:A2"])],
    )
    reordered = canonical_hierarchy(
        [["urn:test:B"], ["urn:test:A2", "urn:test:A"]],
        [(["urn:test:B"], ["urn:test:A2", "urn:test:A"])],
    )
    assert reordered == expected
    assert canonical_same_as([["urn:test:i2", "urn:test:i1"]]) == canonical_same_as(
        [["urn:test:i1", "urn:test:i2"]]
    )


def test_blank_nodes_are_document_scoped_and_alpha_normalized() -> None:
    predicate = {"kind": "iri", "value": "urn:test:p"}
    terminal = {"kind": "iri", "value": "urn:test:end"}
    first = [
        ({"kind": "bnode", "id": "x9"}, predicate, {"kind": "bnode", "id": "x2"}),
        ({"kind": "bnode", "id": "x2"}, predicate, terminal),
    ]
    renamed_reordered = [
        ({"kind": "bnode", "id": "fresh-a"}, predicate, terminal),
        ({"kind": "bnode", "id": "fresh-b"}, predicate, {"kind": "bnode", "id": "fresh-a"}),
    ]
    assert canonical_blank_node_triples(first) == canonical_blank_node_triples(renamed_reordered)


def test_error_and_api_shape_fixture_are_stable() -> None:
    assert canonical_error("ERROR", " parse   failed ", error_type="ParseError") == {
        "category": "ERROR",
        "message": "parse failed",
        "type": "ParseError",
    }
    fixture = json.loads((DATA / "api-shapes.json").read_text())
    hierarchy = fixture["hierarchy"]
    assert canonical_hierarchy(hierarchy["nodes"], hierarchy["edges"])["kind"] == "hierarchy"
