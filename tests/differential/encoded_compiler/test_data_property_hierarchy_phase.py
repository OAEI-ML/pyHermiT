"""Exact scalar/encoded differential for data-property SCC and closure."""

# SPDX-License-Identifier: LGPL-3.0-or-later

from __future__ import annotations

import json
import random
import struct
from typing import cast

import pyowl_core
import pyowl_core.model as owl
import pytest
from pyowl_core.backends.native_views import produce_encoded_structural_view_v1

import pyhermit._native as native
from pyhermit import ReasonerConfig
from pyhermit.clauses.compiler import compile_captured_bundle
from pyhermit.encoded_input import ENCODED_NATIVE_FEATURE
from pyhermit.exceptions import BackendMismatchError
from pyhermit.inputs import capture_ontology
from pyhermit.normalize.model import NormalizedOntology
from pyhermit.roles import RoleAxiomGraph, build_role_axiom_graph
from pyhermit.roles.graph import reachability_members

OPTIONS = pyowl_core.LoadOptions(
    imports=pyowl_core.ImportPolicy.IGNORE,
    backend=pyowl_core.BackendPreference.PYTHON,
)


def functional(*body: str) -> bytes:
    return (
        "Prefix(:=<urn:test:data-hierarchy#>) "
        "Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>) "
        "Ontology(<urn:test:data-hierarchy> " + " ".join(body) + ")"
    ).encode()


def _slice_record(
    snapshot: pyowl_core.OntologyView,
    *,
    posting_mode: int = 0,
    postings: memoryview | None = None,
    member_tokens: tuple[bytes, ...] = (),
) -> tuple[object, ...]:
    buffers = produce_encoded_structural_view_v1(snapshot).buffers
    return (
        posting_mode,
        memoryview(b"") if postings is None else postings,
        member_tokens,
        (),
        buffers["root_kinds"],
        buffers["root_ids"],
        buffers["node_tags"],
        buffers["node_field_offsets"],
        buffers["field_kinds"],
        buffers["field_values"],
        buffers["field_lengths"],
        buffers["item_kinds"],
        buffers["item_values"],
        buffers["item_lengths"],
        buffers["scalar_bytes"],
    )


def _role_graph(normalized: NormalizedOntology) -> RoleAxiomGraph:
    axioms = [
        record.statement
        for record in normalized.records
        if isinstance(record.statement, owl.AxiomNode)
    ]
    axioms.extend(owl.Declaration(entity) for entity in normalized.declared_entities)
    return build_role_axiom_graph(axioms)


def _expected_manifest(snapshot: pyowl_core.OntologyView) -> dict[str, object]:
    normalized, _program, _ontology = compile_captured_bundle(
        capture_ontology(snapshot).captured,
        ReasonerConfig(),
    )
    roles = _role_graph(normalized)
    return {
        "schema_version": 1,
        "family": "data_property_hierarchy",
        "data_components": [list(component) for component in roles.data_components],
        "data_component_by_property": list(roles.data_component_by_property),
        "data_super_components": [
            list(reachability_members(value)) for value in roles.data_super_components
        ],
        "top_component_id": roles.data_component_by_property[roles.top_data_property_id],
        "bottom_component_id": roles.data_component_by_property[roles.bottom_data_property_id],
    }


def _native_manifest(snapshot: pyowl_core.OntologyView) -> dict[str, object]:
    buffers = produce_encoded_structural_view_v1(snapshot).buffers
    return cast(
        dict[str, object],
        json.loads(native._encoded_data_property_hierarchy_manifest_v1(**buffers)),
    )


def _native_slices_manifest(*records: tuple[object, ...]) -> dict[str, object]:
    return cast(
        dict[str, object],
        json.loads(native._encoded_data_property_hierarchy_slices_manifest_v1(slices=records)),
    )


def test_equivalence_sccs_and_transitive_superproperty_closure_match_scalar() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "Declaration(DataProperty(:q))",
            "Declaration(DataProperty(:r))",
            "Declaration(DataProperty(:s))",
            "Declaration(DataProperty(:t))",
            "SubDataPropertyOf(:p :q)",
            "EquivalentDataProperties(:q :r)",
            "SubDataPropertyOf(:r :s)",
            "EquivalentDataProperties(:s :t)",
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(snapshot)
    components = cast(list[list[int]], actual["data_components"])
    assert sorted(len(component) for component in components).count(2) == 2
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


def test_empty_model_retains_distinct_builtins_and_reflexive_closure() -> None:
    snapshot = pyowl_core.load_snapshot(functional(), options=OPTIONS)

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(snapshot)
    assert actual["data_super_components"] == [[0], [1]]
    assert actual["top_component_id"] != actual["bottom_component_id"]
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


def test_composite_cross_slice_cycle_collapses_only_after_union() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "Declaration(DataProperty(:q))",
            "SubDataPropertyOf(:p :q)",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "Declaration(DataProperty(:q))",
            "SubDataPropertyOf(:q :p)",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    actual = _native_slices_manifest(
        _slice_record(left, member_tokens=(b"1" * 32,)),
        _slice_record(right, member_tokens=(b"2" * 32,)),
    )

    assert actual == _expected_manifest(composite)
    assert sum(len(value) == 2 for value in cast(list[list[int]], actual["data_components"])) == 1
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


@pytest.mark.parametrize("posting_mode", [1, 2])
def test_source_local_include_and_exclude_rebuild_exact_hierarchy(posting_mode: int) -> None:
    source = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "Declaration(DataProperty(:q))",
            "Declaration(DataProperty(:r))",
            "SubDataPropertyOf(:p :q)",
            "SubDataPropertyOf(:q :p)",
            "SubDataPropertyOf(:q :r)",
        ),
        options=OPTIONS,
    )
    expected = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "Declaration(DataProperty(:q))",
            "SubDataPropertyOf(:p :q)",
            "SubDataPropertyOf(:q :p)",
        ),
        options=OPTIONS,
    )
    axioms = tuple(source.iter_axioms())
    selected = tuple(
        index
        for index, axiom in enumerate(axioms, start=1)
        if not (
            isinstance(axiom, owl.Declaration)
            and isinstance(axiom.entity, owl.DataProperty)
            and axiom.entity.iri.value.endswith("#r")
        )
        and not (
            isinstance(axiom, owl.SubDataPropertyOf)
            and axiom.super_property.iri.value.endswith("#r")
        )
    )
    posting_ids = (
        selected
        if posting_mode == 1
        else tuple(index for index in range(1, len(axioms) + 1) if index not in selected)
    )
    postings = memoryview(b"".join(struct.pack("<I", value) for value in posting_ids))

    actual = _native_slices_manifest(
        _slice_record(source, posting_mode=posting_mode, postings=postings)
    )

    assert actual == _expected_manifest(expected)


def test_unrelated_data_axioms_do_not_change_the_hierarchy_phase() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(DataProperty(:p))",
            "Declaration(DataProperty(:q))",
            "SubDataPropertyOf(:p :q)",
            "DataPropertyDomain(:p :A)",
            "DataPropertyRange(:q xsd:string)",
            "FunctionalDataProperty(:q)",
            "DisjointDataProperties(:p :q)",
            'DataPropertyAssertion(:p :i "value")',
        ),
        options=OPTIONS,
    )

    assert _native_manifest(snapshot) == _expected_manifest(snapshot)
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


def test_hostile_property_kind_rolls_back_and_valid_retry_is_byte_exact() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "Declaration(DataProperty(:q))",
            "SubDataPropertyOf(:p :q)",
        ),
        options=OPTIONS,
    )
    buffers = dict(produce_encoded_structural_view_v1(snapshot).buffers)
    baseline = native._encoded_data_property_hierarchy_manifest_v1(**buffers)
    scalar_bytes = bytes(buffers["scalar_bytes"])
    hostile = dict(buffers)
    hostile["scalar_bytes"] = memoryview(
        scalar_bytes.replace(b"data_property", b"xxxxxxxxxxxxx", 1)
    )

    with pytest.raises(BackendMismatchError) as caught:
        native._validate_encoded_columns_v1(**hostile)
    assert caught.value.code == "NATIVE_ENCODED_VIEW_INVALID"
    assert native._encoded_data_property_hierarchy_manifest_v1(**buffers) == baseline


def test_generated_hierarchy_permutations_match_scalar_exactly() -> None:
    generator = random.Random(18_120)
    properties = tuple(f":{name}" for name in "pqrst")
    for _case in range(24):
        body = [f"Declaration(DataProperty({property_}))" for property_ in properties]
        for _axiom in range(generator.randrange(2, 12)):
            first, second, third = generator.sample(properties, 3)
            if generator.randrange(2) == 0:
                body.append(f"SubDataPropertyOf({first} {second})")
            else:
                body.append(f"EquivalentDataProperties({first} {second} {third})")
        snapshot = pyowl_core.load_snapshot(functional(*body), options=OPTIONS)

        assert _native_manifest(snapshot) == _expected_manifest(snapshot)
