"""Exact scalar/encoded differential for the first native compiler phase."""

# SPDX-License-Identifier: LGPL-3.0-or-later

from __future__ import annotations

import json
import struct
from typing import cast

import pyowl_core
import pyowl_core.model as owl
import pytest
from pyowl_core.backends.native_views import produce_encoded_structural_view_v1

import pyhermit._native as native
from pyhermit import ReasonerConfig
from pyhermit.clauses.compiler import compile_captured_bundle
from pyhermit.clauses.model import SymbolKind
from pyhermit.encoded_input import ENCODED_NATIVE_FEATURE
from pyhermit.exceptions import BackendMismatchError
from pyhermit.inputs import capture_ontology

OPTIONS = pyowl_core.LoadOptions(
    imports=pyowl_core.ImportPolicy.IGNORE,
    backend=pyowl_core.BackendPreference.PYTHON,
)


def functional(*body: str) -> bytes:
    return (
        "Prefix(:=<urn:test:symbols#>) "
        "Prefix(owl:=<http://www.w3.org/2002/07/owl#>) "
        "Prefix(rdfs:=<http://www.w3.org/2000/01/rdf-schema#>) "
        "Ontology(<urn:test:symbols> " + " ".join(body) + ")"
    ).encode()


def _root_dispatch(view: pyowl_core.OntologyView) -> list[dict[str, object]]:
    rows: list[tuple[int, bytes, dict[str, object]]] = []
    for annotation in view.ontology_annotations():
        rows.append(
            (
                1,
                annotation.canonical_bytes(),
                {
                    "handler": "OntologyAnnotation",
                    "kind": "ontology_annotation",
                    "tag": owl.constructor_spec(annotation).tag,
                },
            )
        )
    for axiom in view.iter_axioms():
        rows.append(
            (
                2,
                axiom.canonical_bytes(),
                {
                    "handler": type(axiom).__name__,
                    "kind": "axiom",
                    "tag": owl.constructor_spec(axiom).tag,
                },
            )
        )
    for extension in view.iter_extensions():
        rows.append(
            (
                3,
                extension.canonical_bytes(),
                {
                    "handler": type(extension).__name__,
                    "kind": "extension",
                    "tag": owl.constructor_spec(extension).tag,
                },
            )
        )
    rows.sort(key=lambda row: (row[0], row[1]))
    return [row[2] for row in rows]


def test_encoded_root_and_entity_seed_manifest_matches_scalar_compiler_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            'Annotation(rdfs:label "ontology")',
            "Declaration(Class(:A))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(DataProperty(:d))",
            "Declaration(AnnotationProperty(:note))",
            "Declaration(NamedIndividual(:i))",
            'SubClassOf(Annotation(:note "edge") :A owl:Thing)',
            'AnnotationAssertion(:note <urn:test:symbols#A> "value")',
        ),
        options=OPTIONS,
    )
    validated = capture_ontology(snapshot)
    _normalized, scalar_program, scalar_ontology = compile_captured_bundle(
        validated.captured,
        ReasonerConfig(),
    )
    encoded = produce_encoded_structural_view_v1(snapshot)
    buffers = encoded.buffers
    raw_manifest = native._encoded_symbol_manifest_v1(
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
    observed = cast(dict[str, object], json.loads(raw_manifest))

    scalar_entities = scalar_program.symbols.domain(SymbolKind.ENTITY).values
    expected = {
        "schema_version": 1,
        "root_dispatch": _root_dispatch(snapshot),
        "entity_symbols": [
            {
                "identifier": value.identifier,
                "key_hex": value.key_hex,
                "display": value.display,
                "generated": value.generated,
                "query_local": value.query_local,
            }
            for value in scalar_entities
        ],
        "declared_entities": [
            {
                "kind": value.kind,
                "iri": value.iri,
                "entity_id": value.entity_id,
            }
            for value in scalar_ontology.declared_entities
        ],
    }
    assert observed == expected
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


def test_private_selection_preflight_accepts_source_local_exclusion() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional("Declaration(Class(:A))", "Declaration(Class(:B))"),
        options=OPTIONS,
    )
    buffers = produce_encoded_structural_view_v1(snapshot).buffers

    assert (
        native._validate_encoded_selection_v1(
            posting_mode=2,
            postings=memoryview(struct.pack("<I", 1)),
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
        is None
    )
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


def test_private_preflight_rejects_a_hostile_entity_iri_before_scalar_compilation() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional("Declaration(Class(<urn:C>))"),
        options=OPTIONS,
    )
    encoded = produce_encoded_structural_view_v1(snapshot)
    buffers = dict(encoded.buffers)
    scalar_bytes = bytes(buffers["scalar_bytes"])
    assert b"urn:C" in scalar_bytes
    buffers["scalar_bytes"] = memoryview(scalar_bytes.replace(b"urn:C", b"xxxxx"))

    with pytest.raises(BackendMismatchError, match="IRI") as caught:
        native._validate_encoded_columns_v1(
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
    assert caught.value.code == "NATIVE_ENCODED_VIEW_INVALID"
