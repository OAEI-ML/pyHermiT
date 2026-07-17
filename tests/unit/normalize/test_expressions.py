from __future__ import annotations

import pyowl_core.model as owl
import pytest

from pyhermit.normalize import ExpressionNormalizer


def cls(name: str) -> owl.Class:
    return owl.Class(owl.IRI(f"urn:test:{name}"))


def obj(name: str) -> owl.ObjectProperty:
    return owl.ObjectProperty(owl.IRI(f"urn:test:{name}"))


def data(name: str) -> owl.DataProperty:
    return owl.DataProperty(owl.IRI(f"urn:test:{name}"))


def test_class_nnf_uses_exact_duals_and_is_idempotent() -> None:
    normalizer = ExpressionNormalizer()
    first, second = cls("first"), cls("second")
    role = obj("role")
    expression = owl.ObjectComplementOf(
        owl.ObjectIntersectionOf(
            owl.CanonicalSet(
                (
                    owl.ObjectSomeValuesFrom(role, first),
                    owl.ObjectMaxCardinality(2, role, second),
                )
            )
        )
    )
    result = normalizer.class_nnf(expression)
    assert isinstance(result, owl.ObjectUnionOf)
    assert any(isinstance(item, owl.ObjectAllValuesFrom) for item in result.operands)
    assert any(
        isinstance(item, owl.ObjectMinCardinality) and item.cardinality == 3
        for item in result.operands
    )
    assert normalizer.class_nnf(result) == result


def test_cardinality_zero_never_underflows_and_exact_dual_is_complete() -> None:
    normalizer = ExpressionNormalizer()
    role = obj("role")
    filler = cls("filler")
    assert (
        normalizer.class_nnf(owl.ObjectMinCardinality(0, role, filler), negated=True)
        == owl.OWL_NOTHING
    )
    exact_zero = normalizer.class_nnf(owl.ObjectExactCardinality(0, role, filler), negated=True)
    assert isinstance(exact_zero, owl.ObjectSomeValuesFrom)
    exact_two = normalizer.class_nnf(owl.ObjectExactCardinality(2, role, filler), negated=True)
    assert isinstance(exact_two, owl.ObjectUnionOf)
    assert {
        (type(item), item.cardinality)
        for item in exact_two.operands
        if isinstance(item, (owl.ObjectMinCardinality, owl.ObjectMaxCardinality))
    } == {
        (owl.ObjectMaxCardinality, 1),
        (owl.ObjectMinCardinality, 3),
    }
    compound = owl.ObjectIntersectionOf(owl.CanonicalSet((filler, cls("other"))))
    maximum_zero = normalizer.class_nnf(owl.ObjectMaxCardinality(0, role, compound))
    assert isinstance(maximum_zero, owl.ObjectAllValuesFrom)
    assert isinstance(maximum_zero.filler, owl.ObjectUnionOf)
    assert all(
        isinstance(item, owl.ObjectComplementOf) and isinstance(item.operand, owl.Class)
        for item in maximum_zero.filler.operands
    )


def test_has_values_and_exact_cardinality_simplify_before_nnf() -> None:
    normalizer = ExpressionNormalizer()
    role = obj("role")
    individual = owl.NamedIndividual(owl.IRI("urn:test:individual"))
    has_value = normalizer.class_nnf(owl.ObjectHasValue(role, individual))
    assert isinstance(has_value, owl.ObjectSomeValuesFrom)
    assert isinstance(has_value.filler, owl.ObjectOneOf)
    data_property = data("value")
    literal = owl.Literal("x", owl.XSD_STRING)
    data_value = normalizer.class_nnf(owl.DataHasValue(data_property, literal))
    assert isinstance(data_value, owl.DataSomeValuesFrom)
    assert isinstance(data_value.filler, owl.DataOneOf)
    exact = normalizer.class_nnf(owl.ObjectExactCardinality(2, role, cls("C")))
    assert isinstance(exact, owl.ObjectIntersectionOf)


def test_top_bottom_property_simplifications_are_semantically_safe() -> None:
    normalizer = ExpressionNormalizer()
    filler = cls("filler")
    assert (
        normalizer.class_nnf(owl.ObjectSomeValuesFrom(owl.OWL_BOTTOM_OBJECT_PROPERTY, filler))
        == owl.OWL_NOTHING
    )
    assert (
        normalizer.class_nnf(owl.ObjectAllValuesFrom(owl.OWL_BOTTOM_OBJECT_PROPERTY, filler))
        == owl.OWL_THING
    )
    assert normalizer.class_nnf(owl.ObjectHasSelf(owl.OWL_TOP_OBJECT_PROPERTY)) == owl.OWL_THING
    assert (
        normalizer.class_nnf(
            owl.DataSomeValuesFrom((owl.OWL_BOTTOM_DATA_PROPERTY,), owl.RDFS_LITERAL)
        )
        == owl.OWL_NOTHING
    )
    assert (
        normalizer.class_nnf(
            owl.DataAllValuesFrom((owl.OWL_BOTTOM_DATA_PROPERTY,), owl.RDFS_LITERAL)
        )
        == owl.OWL_THING
    )


def test_data_range_nnf_duals_and_simplifies_top_bottom() -> None:
    normalizer = ExpressionNormalizer()
    first = owl.DataOneOf(owl.CanonicalSet((owl.Literal("a", owl.XSD_STRING),)))
    second = owl.DataOneOf(owl.CanonicalSet((owl.Literal("b", owl.XSD_STRING),)))
    result = normalizer.data_nnf(
        owl.DataComplementOf(owl.DataUnionOf(owl.CanonicalSet((first, second))))
    )
    assert isinstance(result, owl.DataIntersectionOf)
    assert all(isinstance(item, owl.DataComplementOf) for item in result.operands)
    assert normalizer.data_nnf(result) == result
    bottom = owl.DataComplementOf(owl.RDFS_LITERAL)
    assert normalizer.data_nnf(bottom, negated=True) == owl.RDFS_LITERAL


def test_every_class_constructor_has_stable_positive_and_negative_paths() -> None:
    normalizer = ExpressionNormalizer()
    first, second = cls("matrix-first"), cls("matrix-second")
    role = obj("matrix-role")
    data_property = data("matrix-data")
    individual = owl.NamedIndividual(owl.IRI("urn:test:matrix-individual"))
    literal = owl.Literal("matrix", owl.XSD_STRING)
    expressions: tuple[owl.ClassExpression, ...] = (
        first,
        owl.ObjectIntersectionOf(owl.CanonicalSet((first, second))),
        owl.ObjectUnionOf(owl.CanonicalSet((first, second))),
        owl.ObjectComplementOf(first),
        owl.ObjectOneOf(owl.CanonicalSet((individual,))),
        owl.ObjectSomeValuesFrom(role, first),
        owl.ObjectAllValuesFrom(role, first),
        owl.ObjectHasValue(role, individual),
        owl.ObjectHasSelf(role),
        owl.ObjectMinCardinality(2, role, first),
        owl.ObjectMaxCardinality(2, role, first),
        owl.ObjectExactCardinality(2, role, first),
        owl.DataSomeValuesFrom((data_property,), owl.XSD_STRING),
        owl.DataAllValuesFrom((data_property,), owl.XSD_STRING),
        owl.DataHasValue(data_property, literal),
        owl.DataMinCardinality(2, data_property, owl.XSD_STRING),
        owl.DataMaxCardinality(2, data_property, owl.XSD_STRING),
        owl.DataExactCardinality(2, data_property, owl.XSD_STRING),
    )
    assert {type(value) for value in expressions} == set(owl.CLASS_EXPRESSION_TYPES)
    for expression in expressions:
        positive = normalizer.class_nnf(expression)
        negative = normalizer.class_nnf(expression, negated=True)
        assert normalizer.class_nnf(positive) == positive
        assert normalizer.class_nnf(negative, negated=True) == positive


def test_every_data_range_constructor_has_stable_positive_and_negative_paths() -> None:
    normalizer = ExpressionNormalizer()
    first = owl.DataOneOf(owl.CanonicalSet((owl.Literal("1", owl.XSD_STRING),)))
    second = owl.DataOneOf(owl.CanonicalSet((owl.Literal("2", owl.XSD_STRING),)))
    facet = owl.FacetRestriction(
        owl.IRI("http://www.w3.org/2001/XMLSchema#minLength"),
        owl.Literal("1", owl.Datatype(owl.IRI("http://www.w3.org/2001/XMLSchema#integer"))),
    )
    ranges: tuple[owl.DataRange, ...] = (
        owl.XSD_STRING,
        owl.DataIntersectionOf(owl.CanonicalSet((first, second))),
        owl.DataUnionOf(owl.CanonicalSet((first, second))),
        owl.DataComplementOf(first),
        first,
        owl.DatatypeRestriction(owl.XSD_STRING, owl.CanonicalSet((facet,))),
    )
    assert {type(value) for value in ranges} == set(owl.DATA_RANGE_TYPES)
    for data_range in ranges:
        positive = normalizer.data_nnf(data_range)
        negative = normalizer.data_nnf(data_range, negated=True)
        assert normalizer.data_nnf(positive) == positive
        assert normalizer.data_nnf(negative, negated=True) == positive


def test_expression_depth_configuration_cannot_exceed_the_core_safe_limit() -> None:
    with pytest.raises(ValueError, match="safe/core limit 512"):
        ExpressionNormalizer(max_depth=1200)
