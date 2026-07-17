from __future__ import annotations

import random
import struct

import pytest
from pyowl_core.model import IRI, Datatype, Literal

from pyhermit.datatypes import (
    XSD_DOUBLE,
    XSD_FLOAT,
    XSD_MAX_INCLUSIVE,
    XSD_MIN_EXCLUSIVE,
    XSD_MIN_INCLUSIVE,
    ComparisonOrder,
    FacetRestriction,
    IEEECategory,
    IEEEComparison,
    IEEEFormat,
    IEEEIdentity,
    IEEERange,
    compile_literal,
    restrict_datatype,
)
from pyhermit.datatypes.ieee754 import comparison_from_identity
from pyhermit.exceptions import InvalidLiteralError, OntologyProfileError


def literal(lexical: str, datatype_iri: str) -> Literal:
    return Literal(lexical, Datatype(IRI(datatype_iri)))


def compiled(lexical: str, datatype_iri: str):  # type: ignore[no-untyped-def]
    return compile_literal(literal(lexical, datatype_iri))


@pytest.mark.parametrize(
    ("datatype_iri", "lexical", "bits"),
    [
        (XSD_FLOAT, "0", 0x00000000),
        (XSD_FLOAT, "-0", 0x80000000),
        (XSD_FLOAT, "1.401298464324817e-45", 0x00000001),
        (XSD_FLOAT, "1.1754943508222875e-38", 0x00800000),
        (XSD_FLOAT, "3.4028234663852886e38", 0x7F7FFFFF),
        (XSD_DOUBLE, "5e-324", 0x0000000000000001),
        (XSD_DOUBLE, "2.2250738585072014e-308", 0x0010000000000000),
        (XSD_DOUBLE, "1.7976931348623157e308", 0x7FEFFFFFFFFFFFFF),
    ],
)
def test_ieee_boundary_bits_are_parsed_without_host_float(
    datatype_iri: str, lexical: str, bits: int
) -> None:
    value = compiled(lexical, datatype_iri)
    expected_format = IEEEFormat.FLOAT32 if datatype_iri == XSD_FLOAT else IEEEFormat.FLOAT64
    assert value.data_identity == IEEEIdentity(expected_format, bits)


@pytest.mark.parametrize("datatype_iri", [XSD_FLOAT, XSD_DOUBLE])
def test_ieee_special_values_and_overflow(datatype_iri: str) -> None:
    negative = compiled("-INF", datatype_iri)
    positive = compiled("INF", datatype_iri)
    overflow = compiled("1e9999", datatype_iri)
    nan = compiled("NaN", datatype_iri)
    assert negative.comparison.category is IEEECategory.NEGATIVE_INFINITY
    assert positive.comparison.category is IEEECategory.POSITIVE_INFINITY
    assert overflow.comparison == positive.comparison
    assert nan.comparison.compare(nan.comparison) is ComparisonOrder.UNORDERED


@pytest.mark.parametrize(
    "lexical",
    ["", "nan", "+NaN", "Infinity", "-Infinity", "1f", "0x1p0", " 1 ", "--1"],
)
def test_owl2_ieee_lexical_space_rejects_java_and_host_spellings(lexical: str) -> None:
    with pytest.raises(InvalidLiteralError):
        compiled(lexical, XSD_FLOAT)


def test_signed_zero_identity_is_distinct_but_facet_comparison_is_equal() -> None:
    negative = compiled("-0", XSD_FLOAT)
    positive = compiled("+0", XSD_FLOAT)
    assert negative.source_identity != positive.source_identity
    assert negative.data_identity != positive.data_identity
    assert negative.comparison == positive.comparison
    assert negative.comparison.compare(positive.comparison) is ComparisonOrder.EQUAL


def test_float_and_double_are_disjoint_even_for_same_mathematical_number() -> None:
    float_one = compiled("1", XSD_FLOAT)
    double_one = compiled("1", XSD_DOUBLE)
    assert float_one.data_identity != double_one.data_identity
    with pytest.raises(TypeError, match="same XML Schema datatype"):
        float_one.comparison.compare(double_one.comparison)


def test_round_trip_decimal_oracle_for_deterministic_random_ieee_bits() -> None:
    random_source = random.Random(0xC0FFEE)
    for format_, width, precision, unpack in (
        (IEEEFormat.FLOAT32, 32, 9, ">f"),
        (IEEEFormat.FLOAT64, 64, 17, ">d"),
    ):
        exponent_bits = 8 if width == 32 else 11
        fraction_bits = width - exponent_bits - 1
        exponent_mask = (1 << exponent_bits) - 1
        for _ in range(1_000):
            bits = random_source.getrandbits(width)
            exponent = (bits >> fraction_bits) & exponent_mask
            if exponent == exponent_mask:
                continue
            host_value = struct.unpack(unpack, bits.to_bytes(width // 8, "big"))[0]
            lexical = format(host_value, f".{precision}g")
            datatype = XSD_FLOAT if format_ is IEEEFormat.FLOAT32 else XSD_DOUBLE
            identity = compiled(lexical, datatype).data_identity
            assert identity == IEEEIdentity(format_, bits)


def test_ieee_range_zero_nan_complement_and_small_enumeration() -> None:
    negative_zero = compiled("-0", XSD_FLOAT)
    positive_zero = compiled("0", XSD_FLOAT)
    nan = compiled("NaN", XSD_FLOAT)
    at_zero = IEEERange.bounded(
        IEEEFormat.FLOAT32,
        lower=negative_zero,
        lower_inclusive=True,
        upper=positive_zero,
        upper_inclusive=True,
    )
    assert at_zero.finite_cardinality() == 2
    assert at_zero.contains(negative_zero)
    assert at_zero.contains(positive_zero)
    assert not at_zero.contains(nan)
    outside = at_zero.complement()
    assert not outside.contains(negative_zero)
    assert outside.contains(nan)
    assert at_zero.intersection(outside).is_empty_exact()
    assert at_zero.union(outside) == IEEERange.all(IEEEFormat.FLOAT32)


def test_ieee_bound_facets_treat_both_signed_zeros_as_one_comparison_point() -> None:
    zero = compiled("0", XSD_FLOAT)
    minimum = restrict_datatype(
        XSD_FLOAT,
        (FacetRestriction(XSD_MIN_INCLUSIVE, zero),),
    )
    assert isinstance(minimum, IEEERange)
    assert minimum.contains(compiled("-0", XSD_FLOAT))
    assert minimum.contains(compiled("+0", XSD_FLOAT))
    assert not minimum.contains(compiled("-1.401298464324817e-45", XSD_FLOAT))
    assert not minimum.contains(compiled("NaN", XSD_FLOAT))

    exclusive = restrict_datatype(
        XSD_FLOAT,
        (FacetRestriction(XSD_MIN_EXCLUSIVE, zero),),
    )
    assert isinstance(exclusive, IEEERange)
    assert not exclusive.contains(compiled("-0", XSD_FLOAT))
    assert not exclusive.contains(compiled("+0", XSD_FLOAT))


def test_nan_facet_produces_empty_range_and_wrong_ieee_family_is_rejected() -> None:
    restricted = restrict_datatype(
        XSD_DOUBLE,
        (
            FacetRestriction(XSD_MIN_INCLUSIVE, compiled("NaN", XSD_DOUBLE)),
            FacetRestriction(XSD_MAX_INCLUSIVE, compiled("INF", XSD_DOUBLE)),
        ),
    )
    assert isinstance(restricted, IEEERange)
    assert restricted.is_empty_exact()
    with pytest.raises(OntologyProfileError) as caught:
        restrict_datatype(
            XSD_FLOAT,
            (FacetRestriction(XSD_MIN_INCLUSIVE, compiled("0", XSD_DOUBLE)),),
        )
    assert caught.value.code == "INVALID_FACET_VALUE"


def test_all_ieee_comparison_categories_decode_from_identity() -> None:
    values = (
        IEEEIdentity(IEEEFormat.FLOAT32, 0xFF800000),
        IEEEIdentity(IEEEFormat.FLOAT32, 0x80000000),
        IEEEIdentity(IEEEFormat.FLOAT32, 0x00000000),
        IEEEIdentity(IEEEFormat.FLOAT32, 0x7F800000),
        IEEEIdentity(IEEEFormat.FLOAT32, 0x7FC00001),
    )
    comparisons = tuple(comparison_from_identity(value) for value in values)
    assert comparisons[0].category is IEEECategory.NEGATIVE_INFINITY
    assert (
        comparisons[1] == comparisons[2] == IEEEComparison(IEEEFormat.FLOAT32, IEEECategory.FINITE)
    )
    assert comparisons[3].category is IEEECategory.POSITIVE_INFINITY
    assert comparisons[4].category is IEEECategory.NAN
