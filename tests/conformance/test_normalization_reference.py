from __future__ import annotations

import json
from collections.abc import Mapping
from pathlib import Path
from typing import Any

import pytest

from tools.reference.canonicalize import CanonicalizationError, canonical_normalization
from tools.reference.goldens import load_jsonl

ROOT = Path(__file__).parents[2]
REFERENCE_DATA = ROOT / "tests/data/reference"
FAMILY_KEYS = {
    "asymmetric_object_properties",
    "complex_object_property_inclusions",
    "concept_inclusions",
    "data_property_inclusions",
    "data_range_inclusions",
    "defined_datatypes",
    "disjoint_data_properties",
    "disjoint_object_properties",
    "facts",
    "has_keys",
    "irreflexive_object_properties",
    "reflexive_object_properties",
    "simple_object_property_inclusions",
}


def _golden_value(request_id: str = "structural-normalization") -> dict[str, Any]:
    records = {
        record["request_id"]: record for record in load_jsonl(REFERENCE_DATA / "goldens-v1.jsonl")
    }
    value = records[request_id]["value"]
    assert isinstance(value, dict)
    return value


def _raw_private_names(value: Any, names: Mapping[str, str]) -> Any:
    if isinstance(value, dict):
        private = value.get("private")
        if isinstance(private, str):
            return {"kind": value["kind"], "iri": names[private]}
        return {key: _raw_private_names(item, names) for key, item in value.items()}
    if isinstance(value, list):
        return [_raw_private_names(item, names) for item in value]
    return value


def test_normalization_golden_covers_every_holder_family_and_is_canonical() -> None:
    value = _golden_value()
    assert value["kind"] == "structural_normalization"
    families = value["families"]
    assert set(families) == FAMILY_KEYS
    assert {name: len(items) for name, items in families.items()} == {
        "asymmetric_object_properties": 1,
        "complex_object_property_inclusions": 1,
        "concept_inclusions": 5,
        "data_property_inclusions": 1,
        "data_range_inclusions": 4,
        "defined_datatypes": 1,
        "disjoint_data_properties": 1,
        "disjoint_object_properties": 1,
        "facts": 7,
        "has_keys": 1,
        "irreflexive_object_properties": 1,
        "reflexive_object_properties": 1,
        "simple_object_property_inclusions": 1,
    }
    assert canonical_normalization(value) == value


def test_atomic_normalization_golden_has_exact_overlap_without_private_symbols() -> None:
    value = _golden_value("atomic-structural-normalization")
    families = value["families"]
    namespace = "urn:pyhermit:fixture:normalization-atomic#"
    assert families["concept_inclusions"] == [
        [
            {"kind": "class", "iri": f"{namespace}B"},
            {
                "kind": "object_complement",
                "operand": {"kind": "class", "iri": f"{namespace}A"},
            },
        ]
    ]
    assert families["simple_object_property_inclusions"] == [
        [
            {"kind": "object_property", "iri": f"{namespace}r"},
            {"kind": "object_property", "iri": f"{namespace}s"},
        ]
    ]
    assert families["data_property_inclusions"] == [
        [
            {"kind": "data_property", "iri": f"{namespace}age"},
            {"kind": "data_property", "iri": f"{namespace}score"},
        ]
    ]
    assert len(families["facts"]) == 5
    assert len(families["has_keys"]) == 1
    assert '"private"' not in json.dumps(value)
    assert canonical_normalization(value) == value


def test_normalization_private_symbols_are_alpha_canonical_and_order_independent() -> None:
    canonical = _golden_value()
    first = _raw_private_names(
        canonical,
        {
            "class:0": "internal:def#900",
            "class:1": "internal:def#2",
            "datatype:0": "internal:defdata#81",
        },
    )
    second = _raw_private_names(
        canonical,
        {
            "class:0": "internal:def#1",
            "class:1": "internal:nnq#77",
            "datatype:0": "internal:defdata#0",
        },
    )
    first["kind"] = "raw_structural_normalization"
    second["kind"] = "raw_structural_normalization"
    for items in first["families"].values():
        items.reverse()
    assert canonical_normalization(first) == canonical
    assert canonical_normalization(second) == canonical


def test_normalization_validation_rejects_unknown_or_malformed_families() -> None:
    value = _golden_value()
    malformed = json.loads(json.dumps(value))
    malformed["families"]["unknown"] = []
    with pytest.raises(CanonicalizationError, match="normalization families keys"):
        canonical_normalization(malformed)

    malformed = json.loads(json.dumps(value))
    malformed["families"]["simple_object_property_inclusions"][0].pop()
    with pytest.raises(CanonicalizationError, match="exactly two"):
        canonical_normalization(malformed)


def test_v1_schemas_publish_the_normalization_operation_and_family_contract() -> None:
    request_schema = json.loads(
        (ROOT / "tools/reference/schema/request-v1.schema.json").read_text()
    )
    assert "normalization" in request_schema["properties"]["operation"]["enum"]
    result_schema = json.loads((ROOT / "tools/reference/schema/result-v1.schema.json").read_text())
    required = set(result_schema["$defs"]["normalization"]["properties"]["families"]["required"])
    assert required == FAMILY_KEYS
