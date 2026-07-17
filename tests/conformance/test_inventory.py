from __future__ import annotations

import json
from collections import Counter
from pathlib import Path

DATA = Path(__file__).parents[1] / "data"


def test_complete_upstream_test_inventory() -> None:
    inventory = json.loads((DATA / "reference/upstream-test-inventory.json").read_text())
    assert inventory["reference"]["commit"] == "37ec30aced32ac81ebecc5e33fad255ddefcb4c3"
    assert inventory["reference"]["tree"] == "576db18fd8152be24d577b24c99e2af0d31ceef8"
    assert len(inventory["files"]) == inventory["counts"]["files"] == 186
    assert sum(len(entry["methods"]) for entry in inventory["files"]) == 598
    assert len({entry["path"] for entry in inventory["files"]}) == 186
    assert all(len(entry["sha256"]) == 64 for entry in inventory["files"])
    assert all(
        entry["scope"] in {"in-scope", "excluded", "observation"} for entry in inventory["files"]
    )


def test_extras_and_owllink_core_have_explicit_fates() -> None:
    inventory = json.loads((DATA / "reference/upstream-test-inventory.json").read_text())
    fates = Counter(entry["fate"] for entry in inventory["files"] for _method in entry["methods"])
    assert fates["excluded-extra-rules"] == 24
    assert fates["excluded-extra-datalog"] == 4
    assert fates["excluded-description-graph"] == 3
    assert fates["retained-semantic-api-core"] == 10
    owllink = inventory["scope_decisions"]["owllink_test"]
    assert len(owllink["method_ids"]) == 10
    assert "transport" in owllink["transport_exclusion"].lower()


def test_complete_w3c_inventory_has_no_embedded_ontology_bodies() -> None:
    inventory = json.loads((DATA / "w3c/approved-direct-dl-inventory.json").read_text())
    assert inventory["source"]["sha256"] == (
        "a703d36b774f55f14c0758cf20f2bdd635677045f7ba55053199660c10d6fefc"
    )
    assert len(inventory["cases"]) == inventory["counts"]["cases"] == 266
    assert sum(len(case["check_types"]) for case in inventory["cases"]) == 350
    assert inventory["counts"]["check_types"] == {
        "ConsistencyTest": 169,
        "InconsistencyTest": 97,
        "NegativeEntailmentTest": 9,
        "PositiveEntailmentTest": 75,
    }
    assert all(
        set(body) == {"bytes", "sha256"}
        for case in inventory["cases"]
        for body in case["body_metadata"].values()
    )
