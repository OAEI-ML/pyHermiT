from __future__ import annotations

import itertools

import pytest
from pyowl_core.model import IRI, Datatype, Literal

from pyhermit.datatypes import (
    OWL_RATIONAL,
    XSD_BOOLEAN,
    XSD_DECIMAL,
    XSD_INTEGER,
    XSD_NAMESPACE,
    BooleanComparison,
    BooleanRange,
    DatatypeLimits,
    NumericComparison,
    NumericDomain,
    NumericInterval,
    NumericRange,
    compile_literal,
    numeric_domain_contains,
    range_for_datatype,
)
from pyhermit.events import CancellationSource
from pyhermit.exceptions import ReasonerInterruptedError, ResourceLimitError


def number(numerator: int, denominator: int = 1) -> NumericComparison:
    return NumericComparison(numerator, denominator)


def literal(lexical: str, datatype_iri: str) -> Literal:
    return Literal(lexical, Datatype(IRI(datatype_iri)))


@pytest.mark.parametrize(
    ("value", "integer", "decimal", "rational", "real"),
    [
        (number(2), True, True, True, True),
        (number(1, 2), False, True, True, True),
        (number(1, 8), False, True, True, True),
        (number(7, 125), False, True, True, True),
        (number(1, 3), False, False, True, True),
        (number(-22, 7), False, False, True, True),
    ],
)
def test_nested_numeric_domain_membership(
    value: NumericComparison,
    integer: bool,
    decimal: bool,
    rational: bool,
    real: bool,
) -> None:
    assert numeric_domain_contains(NumericDomain.INTEGER, value) is integer
    assert numeric_domain_contains(NumericDomain.DECIMAL, value) is decimal
    assert numeric_domain_contains(NumericDomain.RATIONAL, value) is rational
    assert numeric_domain_contains(NumericDomain.REAL, value) is real


def test_interval_open_closed_bounds_and_exact_integer_rounding() -> None:
    minimum = NumericRange.between(
        NumericDomain.INTEGER, lower=number(22, 10), lower_inclusive=True
    )
    maximum = NumericRange.between(
        NumericDomain.INTEGER, upper=number(52, 10), upper_inclusive=True
    )
    bounded = minimum.intersection(maximum)
    assert bounded.enumerate_values() == (number(3), number(4), number(5))
    assert bounded.finite_cardinality() == 3
    assert not bounded.contains(number(2))
    assert bounded.contains(number(5))
    assert not bounded.contains(number(6))

    exclusive = NumericRange.between(
        NumericDomain.INTEGER,
        lower=number(2),
        lower_inclusive=False,
        upper=number(5),
        upper_inclusive=False,
    )
    assert exclusive.enumerate_values() == (number(3), number(4))


def test_pinned_hermit_numeric_range_cases() -> None:
    decimal = NumericRange.between(
        NumericDomain.DECIMAL,
        lower=number(12, 10),
        lower_inclusive=True,
        upper=number(72, 10),
        upper_inclusive=True,
    )
    integers = NumericRange.between(
        NumericDomain.INTEGER,
        lower=number(22, 10),
        lower_inclusive=True,
        upper=number(52, 10),
        upper_inclusive=True,
    )
    retained = decimal.intersection(integers.complement())
    assert retained.domain is NumericDomain.INTEGER
    assert retained.enumerate_values() == (number(2), number(6), number(7))

    rational_singleton = NumericRange.between(
        NumericDomain.RATIONAL,
        lower=number(1, 3),
        lower_inclusive=True,
        upper=number(1, 3),
        upper_inclusive=True,
    )
    decimal_singleton = NumericRange.between(
        NumericDomain.DECIMAL,
        lower=number(1, 3),
        lower_inclusive=True,
        upper=number(1, 3),
        upper_inclusive=True,
    )
    assert rational_singleton.enumerate_values() == (number(1, 3),)
    assert decimal_singleton.is_empty_exact()


@pytest.mark.parametrize(
    ("datatype_iri", "inside", "outside"),
    [
        (XSD_NAMESPACE + "byte", (-128, 0, 127), (-129, 128)),
        (XSD_NAMESPACE + "unsignedByte", (0, 1, 255), (-1, 256)),
        (XSD_NAMESPACE + "positiveInteger", (1, 10**30), (-1, 0)),
        (XSD_NAMESPACE + "negativeInteger", (-1, -(10**30)), (0, 1)),
    ],
)
def test_builtin_integer_ranges_match_declared_boundaries(
    datatype_iri: str,
    inside: tuple[int, ...],
    outside: tuple[int, ...],
) -> None:
    value_range = range_for_datatype(datatype_iri)
    assert isinstance(value_range, NumericRange)
    for value in inside:
        assert value_range.contains(number(value))
    for value in outside:
        assert not value_range.contains(number(value))


def test_ranges_consume_compiled_comparison_not_source_or_python_equality() -> None:
    integer = range_for_datatype(XSD_INTEGER)
    decimal = range_for_datatype(XSD_DECIMAL)
    rational = range_for_datatype(OWL_RATIONAL)
    boolean = range_for_datatype(XSD_BOOLEAN)
    compiled_half = compile_literal(literal("1/2", OWL_RATIONAL))
    compiled_true = compile_literal(literal("1", XSD_BOOLEAN))
    assert isinstance(integer, NumericRange)
    assert isinstance(decimal, NumericRange)
    assert isinstance(rational, NumericRange)
    assert isinstance(boolean, BooleanRange)
    assert not integer.contains(compiled_half)
    assert decimal.contains(compiled_half)
    assert rational.contains(compiled_half)
    assert not integer.contains(compiled_true)
    assert boolean.contains(compiled_true)


def _sample_members(value_range: NumericRange) -> frozenset[int]:
    return frozenset(value for value in range(-4, 5) if value_range.contains(number(value)))


def _small_integer_ranges() -> tuple[NumericRange, ...]:
    values = []
    for lower, upper in itertools.product(range(-2, 3), repeat=2):
        for lower_inclusive, upper_inclusive in itertools.product((False, True), repeat=2):
            values.append(
                NumericRange.between(
                    NumericDomain.INTEGER,
                    lower=number(lower),
                    lower_inclusive=lower_inclusive,
                    upper=number(upper),
                    upper_inclusive=upper_inclusive,
                )
            )
    return tuple(values)


def test_exhaustive_small_integer_range_algebra_matches_set_oracle() -> None:
    ranges = _small_integer_ranges()
    universe = frozenset(range(-4, 5))
    for left in ranges:
        left_values = _sample_members(left)
        assert _sample_members(left.complement()) == universe - left_values
        assert left.is_empty_exact() is (not left_values)
        for right in ranges:
            right_values = _sample_members(right)
            assert _sample_members(left.intersection(right)) == left_values & right_values
            assert _sample_members(left.union(right)) == left_values | right_values


def test_exhaustive_boolean_range_algebra_matches_two_value_oracle() -> None:
    ranges = tuple(
        BooleanRange(
            frozenset(value for value, include in zip((False, True), mask, strict=True) if include)
        )
        for mask in itertools.product((False, True), repeat=2)
    )
    universe = frozenset((False, True))
    for left in ranges:
        assert left.finite_cardinality() == len(left.values)
        assert left.is_empty_exact() is (not left.values)
        assert left.complement().values == universe - left.values
        for right in ranges:
            assert left.intersection(right).values == left.values & right.values
            assert left.union(right).values == left.values | right.values
    assert BooleanRange.all().enumerate_values() == (
        BooleanComparison(False),
        BooleanComparison(True),
    )


def test_finite_enumeration_is_bounded_and_cancellable() -> None:
    value_range = NumericRange.between(
        NumericDomain.INTEGER,
        lower=number(0),
        lower_inclusive=True,
        upper=number(100),
        upper_inclusive=True,
    )
    with pytest.raises(ResourceLimitError) as caught:
        value_range.enumerate_values(limits=DatatypeLimits(max_enumeration_values=100))
    assert caught.value.limit == "max_enumeration_values"

    cancellation = CancellationSource()
    cancellation.interrupt("test cancellation")
    with pytest.raises(ReasonerInterruptedError, match="test cancellation"):
        value_range.enumerate_values(cancellation=cancellation.token)


def test_infinite_enumeration_and_mixed_domain_union_fail_explicitly() -> None:
    with pytest.raises(ValueError, match="infinite"):
        NumericRange.all(NumericDomain.INTEGER).enumerate_values()
    with pytest.raises(ValueError, match="mixed-domain union"):
        NumericRange.all(NumericDomain.INTEGER).union(NumericRange.all(NumericDomain.DECIMAL))


def test_interval_intersection_retains_restrictive_equal_endpoint_flags() -> None:
    inclusive = NumericInterval(number(0), True, number(1), True)
    exclusive = NumericInterval(number(0), False, number(1), False)
    result = inclusive.intersection(exclusive)
    assert not result.lower_inclusive
    assert not result.upper_inclusive
    assert not result.contains(number(0), domain=NumericDomain.RATIONAL)
    assert result.contains(number(1, 2), domain=NumericDomain.RATIONAL)
