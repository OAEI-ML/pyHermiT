"""Query syntax serialization never scans permanent domains or normalizes an ontology."""

from __future__ import annotations

import json
from collections.abc import Iterator

import pyowl_core.model as owl
import pytest

from pyhermit.backends import native_queries
from pyhermit.backends.native_context import NativeServiceContext, _NativeDomainMapping
from pyhermit.exceptions import FeatureNotImplementedError, ResourceLimitError

A = owl.Class(owl.IRI("urn:A"))
P = owl.ObjectProperty(owl.IRI("urn:p"))
INV = owl.ObjectInverseOf(P)
D = owl.DataProperty(owl.IRI("urn:d"))
INDIVIDUAL = owl.NamedIndividual(owl.IRI("urn:i"))
L = owl.Literal("bound", owl.XSD_STRING)
FRESH = owl.NamedIndividual(owl.IRI("urn:query:fresh"))


class Symbols:
    def __init__(self) -> None:
        self.lookups: list[tuple[str, bytes]] = []
        self.values = {
            ("class", A.canonical_bytes()): 3,
            ("class", owl.OWL_THING.canonical_bytes()): 4,
            ("class", owl.OWL_NOTHING.canonical_bytes()): 5,
            ("object_property", P.canonical_bytes()): 7,
            ("object_property", INV.canonical_bytes()): 8,
            ("data_property", D.canonical_bytes()): 9,
            ("individual", INDIVIDUAL.canonical_bytes()): 11,
            ("source_literal", L.canonical_bytes()): 13,
        }

    def find(self, domain: str, key: bytes) -> int | None:
        self.lookups.append((domain, key))
        return self.values.get((domain, key))

    def find_query_individual(self, key: bytes) -> int | None:
        self.lookups.append(("query_individual", key))
        return self.values.get(("query_individual", key))

    def metadata(self) -> tuple[str, str, bool, bool, int]:
        raise AssertionError("query serializer requested metadata again")

    def count(self, domain: str) -> int:
        raise AssertionError("query serializer counted a permanent domain")

    def ids(self, domain: str) -> list[int]:
        raise AssertionError("query serializer enumerated a permanent domain")

    def id_at(self, domain: str, offset: int) -> int | None:
        raise AssertionError("query serializer iterated a permanent domain")

    def key(self, domain: str, identifier: int) -> bytes | None:
        raise AssertionError("query serializer decoded a permanent symbol")


def context() -> tuple[NativeServiceContext, Symbols]:
    symbols = Symbols()
    return NativeServiceContext(
        query_scope_digest="1" * 64,
        compiler_digest="2" * 64,
        permanent_program_sha256="3" * 64,
        source_signature=frozenset(),
        source_literals=(),
        deterministic_program=True,
        semantic_equality_possible=False,
        class_ids=_NativeDomainMapping(symbols, "class"),
        object_property_ids=_NativeDomainMapping(symbols, "object_property"),
        data_property_ids=_NativeDomainMapping(symbols, "data_property"),
        individual_ids=_NativeDomainMapping(symbols, "individual"),
        source_literal_ids=_NativeDomainMapping(symbols, "source_literal"),
    ), symbols


def test_query_local_ids_are_deterministic_typed_and_isolated() -> None:
    ctx, symbols = context()
    fresh_class = owl.Class(FRESH.iri)
    axioms = (
        owl.ClassAssertion(A, INDIVIDUAL),
        owl.ClassAssertion(fresh_class, FRESH),
        owl.ClassAssertion(owl.ObjectComplementOf(fresh_class), FRESH),
        owl.ObjectPropertyAssertion(INV, INDIVIDUAL, FRESH),
        owl.NegativeDataPropertyAssertion(D, FRESH, L),
    )
    encoded = native_queries.serialize_query(axioms, ctx)
    payload = json.loads(encoded)
    assert payload["schema"] == 1
    assert payload["permanent_program_sha256"] == "3" * 64
    assert payload["individual_count"] == payload["class_count"] == 1
    assert payload["axioms"][0] == {
        "kind": "class",
        "expression": {"kind": "class", "symbol": {"base": 3}},
        "individual": {"base": 11},
    }
    assert payload["axioms"][1]["expression"]["symbol"] == {"local": 0}
    assert payload["axioms"][2]["expression"]["value"]["symbol"] == {"local": 0}
    assert payload["axioms"][3]["role"] == 8
    assert payload["axioms"][4]["literal"] == 13
    assert payload["axioms"][4]["negative"] is True
    assert native_queries.serialize_query(axioms, ctx) == encoded
    assert len(symbols.lookups) < 40
    assert (
        json.loads(native_queries.serialize_query((owl.ClassAssertion(A, INDIVIDUAL),), ctx))[
            "class_count"
        ]
        == 0
    )


@pytest.mark.parametrize(
    "expression,kind",
    [
        (owl.ObjectComplementOf(A), "not"),
        (owl.ObjectIntersectionOf((A, owl.OWL_THING)), "and"),
        (owl.ObjectUnionOf((A, owl.OWL_NOTHING)), "or"),
        (owl.ObjectOneOf((INDIVIDUAL, FRESH)), "one_of"),
        (owl.ObjectSomeValuesFrom(P, A), "some"),
        (owl.ObjectAllValuesFrom(INV, A), "all"),
        (owl.ObjectHasSelf(P), "self"),
        (owl.ObjectHasValue(INV, FRESH), "has_value"),
        (owl.DataHasValue(D, L), "data_value"),
    ],
)
def test_supported_expression_syntax_is_preserved(
    expression: owl.ClassExpression, kind: str
) -> None:
    ctx, _ = context()
    result = json.loads(
        native_queries.serialize_query((owl.ClassAssertion(expression, INDIVIDUAL),), ctx)
    )
    assert result["axioms"][0]["expression"]["kind"] == kind


@pytest.mark.parametrize(
    "axiom,kind,negative",
    [
        (owl.ObjectPropertyAssertion(P, INDIVIDUAL, FRESH), "object", False),
        (owl.NegativeObjectPropertyAssertion(P, INDIVIDUAL, FRESH), "object", True),
        (owl.DataPropertyAssertion(D, INDIVIDUAL, L), "data", False),
        (owl.NegativeDataPropertyAssertion(D, INDIVIDUAL, L), "data", True),
        (owl.SameIndividual((INDIVIDUAL, FRESH)), "same", None),
        (owl.DifferentIndividuals((INDIVIDUAL, FRESH)), "different", None),
    ],
)
def test_assertion_polarity_and_identity_are_retained(
    axiom: owl.AxiomNode, kind: str, negative: bool | None
) -> None:
    ctx, _ = context()
    row = json.loads(native_queries.serialize_query((axiom,), ctx))["axioms"][0]
    assert row["kind"] == kind
    if negative is not None:
        assert row["negative"] is negative


@pytest.mark.parametrize(
    "axiom",
    [
        owl.SubClassOf(A, owl.OWL_THING),
        owl.TransitiveObjectProperty(P),
        owl.Declaration(A),
        owl.ClassAssertion(owl.ObjectMinCardinality(2, P, A), INDIVIDUAL),
        owl.ObjectPropertyAssertion(
            owl.ObjectProperty(owl.IRI("urn:unknown:p")), INDIVIDUAL, FRESH
        ),
        owl.DataPropertyAssertion(D, INDIVIDUAL, owl.Literal("unbound", owl.XSD_STRING)),
        owl.ClassAssertion(
            A,
            INDIVIDUAL,
            (
                owl.Annotation(
                    owl.AnnotationProperty(owl.IRI("http://www.w3.org/2000/01/rdf-schema#label")), L
                ),
            ),
        ),
    ],
)
def test_unsupported_or_unbound_inputs_are_explicitly_ineligible(axiom: owl.AxiomNode) -> None:
    ctx, _ = context()
    with pytest.raises(FeatureNotImplementedError) as caught:
        native_queries.serialize_query((axiom,), ctx)
    assert caught.value.feature_id == "native_query_delta_ineligible"


def test_byte_node_and_depth_limits_do_not_select_fallback(monkeypatch: pytest.MonkeyPatch) -> None:
    ctx, _ = context()
    with monkeypatch.context() as patch:
        patch.setattr(native_queries, "MAX_QUERY_BYTES", 100)
        with pytest.raises(ResourceLimitError, match="resource limit") as caught:
            native_queries.serialize_query((owl.ClassAssertion(A, INDIVIDUAL),), ctx)
        assert caught.value.limit == "native_query_bytes"
    consumed = 0

    def axioms() -> Iterator[owl.AxiomNode]:
        nonlocal consumed
        for _ in range(1000):
            consumed += 1
            yield owl.ClassAssertion(A, INDIVIDUAL)

    with monkeypatch.context() as patch:
        patch.setattr(native_queries, "MAX_QUERY_NODES", 10)
        with pytest.raises(ResourceLimitError) as caught:
            native_queries.serialize_query(axioms(), ctx)
        assert caught.value.limit == "native_query_nodes"
        assert consumed < 10
    expression: owl.ClassExpression = A
    for _ in range(8):
        expression = owl.ObjectComplementOf(expression)
    monkeypatch.setattr(native_queries, "MAX_QUERY_DEPTH", 4)
    with pytest.raises(ResourceLimitError) as caught:
        native_queries.serialize_query((owl.ClassAssertion(expression, INDIVIDUAL),), ctx)
    assert caught.value.limit == "native_query_depth"


def test_scoped_anonymous_source_ids_and_fresh_witnesses_stay_distinct() -> None:
    ctx, symbols = context()
    source = owl.AnonymousIndividual(b"s" * 32, b"root")
    fresh = owl.AnonymousIndividual(b"q" * 32, b"root")
    symbols.values[("query_individual", source.canonical_bytes())] = 17
    axioms = (
        owl.ClassAssertion(A, source),
        owl.ClassAssertion(A, fresh),
        owl.ObjectPropertyAssertion(P, fresh, source),
        owl.ClassAssertion(owl.ObjectOneOf((fresh,)), fresh),
    )
    result = json.loads(native_queries.serialize_query(axioms, ctx))
    assert result["individual_count"] == 1
    assert result["axioms"][0]["individual"] == {"base": 17}
    assert result["axioms"][1]["individual"] == {"local": 0}
    assert result["axioms"][2]["source"] == {"local": 0}
    assert result["axioms"][2]["target"] == {"base": 17}
    assert result["axioms"][3]["expression"]["individuals"] == [{"local": 0}]
