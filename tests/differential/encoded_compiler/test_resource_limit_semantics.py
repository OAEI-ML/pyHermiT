"""Opting into a larger native index retains strict admission and query answers."""

# SPDX-License-Identifier: LGPL-3.0-or-later

from __future__ import annotations

import pyowl_core as core
import pyowl_core.model as owl
import pytest

from pyhermit import Reasoner, ReasonerConfig
from pyhermit.exceptions import OntologyProfileError

RAISED_SYMBOL_INDEX_BYTES = 4 * 1024 * 1024 * 1024
BASE = "urn:test:resource-limits#"


def _snapshot(*body: str) -> core.OntologyView:
    source = (
        f"Prefix(:=<{BASE}>) "
        "Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>) "
        "Ontology(<urn:test:resource-limits> " + " ".join(body) + ")"
    ).encode()
    return core.load_snapshot(
        source,
        options=core.LoadOptions(
            imports=core.ImportPolicy.IGNORE,
            backend=core.BackendPreference.NATIVE,
        ),
    )


@pytest.mark.parametrize(
    "body",
    (
        ("Declaration(Datatype(:unknown))",),
        (
            "Declaration(Datatype(:unknown))",
            "Declaration(AnnotationProperty(:metadata))",
            "AnnotationPropertyRange(:metadata :unknown)",
        ),
        (
            "Declaration(Datatype(:unknown))",
            "Declaration(DataProperty(:value))",
            "DataPropertyRange(:value :unknown)",
        ),
        (
            "Declaration(Datatype(:unknown))",
            "Declaration(DataProperty(:value))",
            "Declaration(NamedIndividual(:individual))",
            'DataPropertyAssertion(:value :individual "value"^^:unknown)',
        ),
    ),
    ids=("declaration-only", "annotation-range-only", "logical-range", "typed-literal"),
)
def test_raised_symbol_index_limit_preserves_unsupported_datatype_errors(
    body: tuple[str, ...],
) -> None:
    view = _snapshot(*body)
    failures = []
    for limit in (None, RAISED_SYMBOL_INDEX_BYTES):
        config = ReasonerConfig(
            backend="native",
            require_native_pipeline=True,
            max_native_symbol_index_bytes=limit,
        )
        with pytest.raises(OntologyProfileError, match="UNSUPPORTED_DATATYPE") as caught:
            Reasoner(view, config=config)
        failures.append(caught.value.as_dict())

    assert failures[0] == failures[1]
    assert failures[0]["code"] == "OWL2DL_PROFILE_VIOLATION"


def test_raised_symbol_index_limit_preserves_native_reasoning_answers() -> None:
    view = _snapshot(
        "Declaration(Class(:A))",
        "Declaration(Class(:B))",
        "Declaration(Class(:Impossible))",
        "Declaration(DataProperty(:value))",
        "Declaration(NamedIndividual(:individual))",
        "SubClassOf(:A :B)",
        "SubClassOf(:Impossible owl:Nothing)",
        "ClassAssertion(:A :individual)",
        "DataPropertyRange(:value xsd:integer)",
        'DataPropertyAssertion(:value :individual "1"^^xsd:integer)',
    )
    a = owl.Class(owl.IRI(f"{BASE}A"))
    b = owl.Class(owl.IRI(f"{BASE}B"))
    impossible = owl.Class(owl.IRI(f"{BASE}Impossible"))
    answers = []
    index_bytes = []
    for limit in (None, RAISED_SYMBOL_INDEX_BYTES):
        config = ReasonerConfig(
            backend="native",
            require_native_pipeline=True,
            max_native_symbol_index_bytes=limit,
        )
        with Reasoner(view, config=config) as reasoner:
            answers.append(
                (
                    reasoner.is_consistent(),
                    reasoner.is_subclass(a, b),
                    reasoner.is_subclass(b, a),
                    reasoner.is_satisfiable(a),
                    reasoner.is_satisfiable(impossible),
                    reasoner.entails(owl.SubClassOf(a, b)),
                    reasoner.class_hierarchy(),
                    reasoner.object_property_hierarchy(),
                    reasoner.data_property_hierarchy(),
                )
            )
            diagnostics = reasoner.diagnostics()
            assert diagnostics["ingestion_path"] == "encoded-native"
            assert diagnostics["native_pipeline_required"] is True
            index_bytes.append(diagnostics["native_symbol_index_bytes"])

    assert answers[0] == answers[1]
    assert answers[0][:6] == (True, True, False, True, False, True)
    assert index_bytes[0] == index_bytes[1]
    assert isinstance(index_bytes[0], int) and index_bytes[0] > 0
