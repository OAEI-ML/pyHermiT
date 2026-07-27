"""Exact scalar/encoded parity for the private permanent-session symbol boundary."""

# SPDX-License-Identifier: LGPL-3.0-or-later

from __future__ import annotations

import json
import struct
from typing import cast

import pyowl_core
import pyowl_core.model as owl
import pytest
from pyowl_core.backends.native_views import produce_encoded_structural_view_v1
from tests.differential.encoded_compiler.test_named_class_phase import (
    OPTIONS,
    _slice_record,
    functional,
)

import pyhermit._native as native
from pyhermit import ReasonerConfig
from pyhermit.clauses.compiler import compile_captured_bundle
from pyhermit.encoded_input import ENCODED_NATIVE_FEATURE
from pyhermit.exceptions import BackendMismatchError, ReasonerInterruptedError
from pyhermit.inputs import capture_ontology


def _expected_manifest(view: pyowl_core.OntologyView) -> dict[str, object]:
    compiled = compile_captured_bundle(
        capture_ontology(view).captured,
        ReasonerConfig(),
    )[2]
    return {
        "schema_version": 1,
        "declared_entities": [
            {"id": entity.entity_id, "iri": entity.iri, "kind": entity.kind}
            for entity in compiled.declared_entities
        ],
        "named_individuals": list(compiled.named_individuals),
    }


def _native_manifest(
    view: pyowl_core.OntologyView,
    *records: tuple[object, ...],
) -> dict[str, object]:
    return cast(
        dict[str, object],
        json.loads(
            native._encoded_session_domain_slices_manifest_v1(
                slices=records,
                logical_fingerprint=memoryview(view.logical_fingerprint.digest),
            )
        ),
    )


def _source_declared_entity_ids(
    view: pyowl_core.OntologyView,
) -> dict[tuple[str, str], int]:
    buffers = produce_encoded_structural_view_v1(view).buffers
    manifest = cast(
        dict[str, object],
        json.loads(
            native._encoded_symbol_manifest_v1(
                root_kinds=buffers["root_kinds"],
                root_ids=buffers["root_ids"],
                node_tags=buffers["node_tags"],
                node_field_offsets=buffers["node_field_offsets"],
                field_kinds=buffers["field_kinds"],
                field_values=buffers["field_values"],
                field_lengths=buffers["field_lengths"],
                item_kinds=buffers["item_kinds"],
                item_values=buffers["item_values"],
                item_lengths=buffers["item_lengths"],
                scalar_bytes=buffers["scalar_bytes"],
            )
        ),
    )
    return {
        (cast(str, entity["kind"]), cast(str, entity["iri"])): cast(int, entity["entity_id"])
        for entity in cast(list[dict[str, object]], manifest["declared_entities"])
    }


def _declaration(
    view: pyowl_core.OntologyView,
    iri: str,
) -> owl.Declaration:
    return next(
        cast(owl.Declaration, axiom)
        for axiom in view.iter_axioms(owl.Declaration)
        if axiom.entity.iri.value == iri
    )


def _root_ordinal(
    view: pyowl_core.OntologyView,
    target: owl.AxiomNode,
) -> int:
    axioms = tuple(view.iter_axioms())
    ordinal = axioms.index(target) + 1
    buffers = produce_encoded_structural_view_v1(view).buffers
    root_ids = memoryview(buffers["root_ids"]).cast("I")
    node_tags = memoryview(buffers["node_tags"]).cast("H")
    assert node_tags[root_ids[ordinal - 1] - 1] == 60
    return ordinal


def test_direct_session_domain_matches_scalar_declared_and_named_sets() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:C))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(DataProperty(:d))",
            "Declaration(AnnotationProperty(:note))",
            "Declaration(NamedIndividual(:declared))",
            "ClassAssertion(:C :implicit)",
            "ObjectPropertyAssertion(:p :declared :implicit)",
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(snapshot, _slice_record(snapshot))

    assert actual == _expected_manifest(snapshot)
    assert len(cast(list[object], actual["declared_entities"])) == 5
    assert len(cast(list[object], actual["named_individuals"])) == 2
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_generated_reachability_remaps_local_declaration_ids_before_merge() -> None:
    long_iri = "urn:test:long:" + ("z" * 240)
    snapshot = pyowl_core.load_snapshot(
        functional(
            f"Declaration(Class(<{long_iri}>))",
            "Declaration(Class(:B))",
            "Declaration(Class(:C))",
            "Declaration(NamedIndividual(:i))",
            f"ClassAssertion(<{long_iri}> :i)",
            f"SubClassOf(<{long_iri}> ObjectIntersectionOf(:B :C))",
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(snapshot, _slice_record(snapshot))

    assert actual == _expected_manifest(snapshot)
    source_ids = _source_declared_entity_ids(snapshot)
    published_ids = {
        (cast(str, entity["kind"]), cast(str, entity["iri"])): cast(int, entity["id"])
        for entity in cast(list[dict[str, object]], actual["declared_entities"])
    }
    assert source_ids.keys() == published_ids.keys()
    assert any(source_ids[key] != published_ids[key] for key in source_ids)


def test_selected_overlay_filters_declarations_and_remaps_delta_domains() -> None:
    base = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:Drop))",
            "Declaration(Class(:Keep))",
            "Declaration(NamedIndividual(:base))",
            "ClassAssertion(:Keep :base)",
        ),
        options=OPTIONS,
    )
    delta_source = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:Added))",
            "Declaration(NamedIndividual(:added))",
            "ClassAssertion(:Added :added)",
        ),
        options=OPTIONS,
    )
    removed = _declaration(base, "urn:test:named#Drop")
    overlay = pyowl_core.apply_delta(
        base,
        pyowl_core.OntologyDelta(
            add_axioms=tuple(delta_source.iter_axioms()),
            remove_axioms=(removed,),
            policy=pyowl_core.DeltaPolicy.IDEMPOTENT,
        ),
    )
    posting = memoryview(struct.pack("<I", _root_ordinal(base, removed)))
    records = (
        _slice_record(base, posting_mode=2, postings=posting),
        _slice_record(delta_source),
    )

    forward = _native_manifest(overlay, *records)
    reverse = _native_manifest(overlay, *reversed(records))

    assert forward == reverse == _expected_manifest(overlay)
    declared = cast(list[dict[str, object]], forward["declared_entities"])
    assert "urn:test:named#Drop" not in {entity["iri"] for entity in declared}
    assert "urn:test:named#Added" in {entity["iri"] for entity in declared}


def test_composite_session_domain_is_source_order_independent() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:Z))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(NamedIndividual(:z))",
            "ClassAssertion(:Z :z)",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:Z))",
            "Declaration(DataProperty(:d))",
            "Declaration(NamedIndividual(:a))",
            "ClassAssertion(:A :a)",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))
    records = (_slice_record(left), _slice_record(right))

    forward = _native_manifest(composite, *records)
    reverse = _native_manifest(composite, *reversed(records))

    assert forward == reverse == _expected_manifest(composite)
    assert len(cast(list[object], forward["declared_entities"])) == 6
    assert cast(list[int], forward["named_individuals"]) == sorted(
        cast(list[int], forward["named_individuals"])
    )


def test_session_domain_failure_paths_publish_nothing_and_retry_exactly() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(NamedIndividual(:a))",
            "ClassAssertion(:A :a)",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:B))",
            "Declaration(NamedIndividual(:b))",
            "ClassAssertion(:B :b)",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))
    records = (_slice_record(left), _slice_record(right))
    baseline = _native_manifest(composite, *records)

    with pytest.raises(BackendMismatchError, match="field count"):
        native._encoded_session_domain_slices_manifest_v1(
            slices=(records[0][:-1], records[1]),
            logical_fingerprint=memoryview(composite.logical_fingerprint.digest),
        )
    assert _native_manifest(composite, *records) == baseline

    with pytest.raises(ReasonerInterruptedError) as interrupted:
        native._debug_validate_encoded_slices_cancel_v1(
            slices=records,
            cancel_at_checkpoint=33,
        )
    assert interrupted.value.context == {
        "checkpoint": "33",
        "phase": "merged-role-clause-publication",
    }
    assert _native_manifest(composite, *records) == baseline == _expected_manifest(composite)
