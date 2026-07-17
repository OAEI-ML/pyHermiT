from __future__ import annotations

import dataclasses
import json

import pytest
from pyowl_core.model import IRI, Datatype, Literal, validate_lexical_form

from pyhermit.datatypes import (
    OWL_RATIONAL,
    OWL_REAL,
    SUPPORTED_DATATYPES,
    XSD_BOOLEAN,
    XSD_DECIMAL,
    XSD_INTEGER,
    XSD_NAMESPACE,
    BooleanComparison,
    BooleanIdentity,
    LexicalCompatibility,
    NumericComparison,
    NumericIdentity,
    compile_literal,
)
from pyhermit.exceptions import InvalidLiteralError, UnsupportedDatatypeError


def literal(lexical: str, datatype_iri: str) -> Literal:
    return Literal(lexical, Datatype(IRI(datatype_iri)))


def test_core_literal_is_retained_and_three_relations_stay_separate() -> None:
    sources = (
        literal("1", XSD_INTEGER),
        literal("+01", XSD_NAMESPACE + "int"),
        literal("1.0", XSD_DECIMAL),
        literal("2/2", OWL_RATIONAL),
    )
    compiled = tuple(compile_literal(source) for source in sources)

    assert all(
        value.source_literal is source for value, source in zip(compiled, sources, strict=True)
    )
    assert len({value.source_identity for value in compiled}) == 4
    assert {value.data_identity for value in compiled} == {NumericIdentity(1)}
    assert {value.comparison for value in compiled} == {NumericComparison(1)}
    assert all(value.data_identity is not value.comparison for value in compiled)
    assert compiled[0].source_identity.lexical_form == "1"
    with pytest.raises(dataclasses.FrozenInstanceError):
        compiled[0].data_identity = NumericIdentity(2)  # type: ignore[misc]


def test_numeric_one_and_boolean_true_are_not_one_data_value() -> None:
    number = compile_literal(literal("1", XSD_INTEGER))
    boolean = compile_literal(literal("true", XSD_BOOLEAN))
    assert number.data_identity == NumericIdentity(1)
    assert boolean.data_identity == BooleanIdentity(True)
    assert number.data_identity != boolean.data_identity
    assert isinstance(number.comparison, NumericComparison)
    assert isinstance(boolean.comparison, BooleanComparison)


def test_tagged_identity_record_is_deterministic_json_without_object_identity() -> None:
    source = literal("+0007", XSD_INTEGER)
    first = compile_literal(source).as_tagged()
    second = compile_literal(source).as_tagged()
    assert first == second
    encoded = json.dumps(first, sort_keys=True, separators=(",", ":"))
    assert encoded == json.dumps(second, sort_keys=True, separators=(",", ":"))
    assert "+0007" in encoded
    assert "object at" not in encoded


@pytest.mark.parametrize(
    ("lexical", "expected"),
    [("true", True), ("1", True), ("false", False), ("0", False)],
)
def test_boolean_standard_lexical_space(lexical: str, expected: bool) -> None:
    compiled = compile_literal(literal(lexical, XSD_BOOLEAN))
    assert compiled.data_identity == BooleanIdentity(expected)


@pytest.mark.parametrize("lexical", ["TRUE", "False", " true ", "yes", "", "+1", "00"])
def test_boolean_rejects_nonstandard_lexical_forms(lexical: str) -> None:
    with pytest.raises(InvalidLiteralError) as caught:
        compile_literal(literal(lexical, XSD_BOOLEAN))
    assert caught.value.code == "INVALID_LITERAL"
    assert caught.value.context == {"datatype_iri": XSD_BOOLEAN}


@pytest.mark.parametrize(
    ("lexical", "expected"),
    [("TRUE", True), (" False ", False), ("\t1\n", True), (" 0 ", False)],
)
def test_pinned_hermit_boolean_quirk_is_explicit_and_private(lexical: str, expected: bool) -> None:
    source = literal(lexical, XSD_BOOLEAN)
    compiled = compile_literal(source, compatibility=LexicalCompatibility.HERMIT_1_4)
    assert compiled.source_literal is source
    assert compiled.source_identity.lexical_form == lexical
    assert compiled.data_identity == BooleanIdentity(expected)
    assert compiled.compatibility is LexicalCompatibility.HERMIT_1_4


@pytest.mark.parametrize(
    ("datatype_iri", "valid"),
    [
        (XSD_INTEGER, ("0", "-0", "+0001", "999999999999999999999999")),
        (XSD_DECIMAL, ("0", "-0.0", "+1.", ".25", "000.2500")),
        (OWL_RATIONAL, ("0/1", "-0/7", "+17/3", "001/0002")),
    ],
)
def test_numeric_valid_lexical_matrix(datatype_iri: str, valid: tuple[str, ...]) -> None:
    for lexical in valid:
        assert isinstance(
            compile_literal(literal(lexical, datatype_iri)).data_identity,
            NumericIdentity,
        )


@pytest.mark.parametrize(
    ("datatype_iri", "invalid"),
    [
        (
            XSD_INTEGER,
            ("", "+", " 1", "1 ", "1.0", "1e0", "\N{ARABIC-INDIC DIGIT ONE}"),
        ),
        (XSD_DECIMAL, ("", ".", "+.", "1e2", "NaN", "INF", " 1.0")),
        (OWL_RATIONAL, ("", "1", "1/0", "1/-2", "1/+2", "1 /2", "1/ 2")),
        (OWL_REAL, ("0", "1.0", "1/2")),
    ],
)
def test_numeric_invalid_lexical_matrix(datatype_iri: str, invalid: tuple[str, ...]) -> None:
    for lexical in invalid:
        with pytest.raises(InvalidLiteralError):
            compile_literal(literal(lexical, datatype_iri))


def test_pinned_hermit_decimal_and_rational_quirks_are_not_owl2_defaults() -> None:
    decimal = literal("1.25E+2", XSD_DECIMAL)
    rational = literal("1/+2", OWL_RATIONAL)
    with pytest.raises(InvalidLiteralError):
        compile_literal(decimal)
    with pytest.raises(InvalidLiteralError):
        compile_literal(rational)
    assert compile_literal(
        decimal, compatibility=LexicalCompatibility.HERMIT_1_4
    ).data_identity == NumericIdentity(125)
    assert compile_literal(
        rational, compatibility=LexicalCompatibility.HERMIT_1_4
    ).data_identity == NumericIdentity(1, 2)


@pytest.mark.parametrize(
    ("datatype_iri", "lower", "upper"),
    [
        (XSD_NAMESPACE + "byte", -(2**7), 2**7 - 1),
        (XSD_NAMESPACE + "short", -(2**15), 2**15 - 1),
        (XSD_NAMESPACE + "int", -(2**31), 2**31 - 1),
        (XSD_NAMESPACE + "long", -(2**63), 2**63 - 1),
        (XSD_NAMESPACE + "unsignedByte", 0, 2**8 - 1),
        (XSD_NAMESPACE + "unsignedShort", 0, 2**16 - 1),
        (XSD_NAMESPACE + "unsignedInt", 0, 2**32 - 1),
        (XSD_NAMESPACE + "unsignedLong", 0, 2**64 - 1),
    ],
)
def test_bounded_integer_lexical_boundaries(datatype_iri: str, lower: int, upper: int) -> None:
    assert compile_literal(literal(str(lower), datatype_iri)).data_identity == NumericIdentity(
        lower
    )
    assert compile_literal(literal(str(upper), datatype_iri)).data_identity == NumericIdentity(
        upper
    )
    with pytest.raises(InvalidLiteralError):
        compile_literal(literal(str(lower - 1), datatype_iri))
    with pytest.raises(InvalidLiteralError):
        compile_literal(literal(str(upper + 1), datatype_iri))


@pytest.mark.parametrize(
    ("datatype_iri", "valid", "invalid"),
    [
        (XSD_NAMESPACE + "negativeInteger", -1, 0),
        (XSD_NAMESPACE + "nonPositiveInteger", 0, 1),
        (XSD_NAMESPACE + "nonNegativeInteger", 0, -1),
        (XSD_NAMESPACE + "positiveInteger", 1, 0),
    ],
)
def test_unbounded_derived_integer_boundaries(datatype_iri: str, valid: int, invalid: int) -> None:
    assert compile_literal(literal(str(valid), datatype_iri)).data_identity == NumericIdentity(
        valid
    )
    with pytest.raises(InvalidLiteralError):
        compile_literal(literal(str(invalid), datatype_iri))


def test_exact_cross_datatype_numeric_values_never_pass_through_float() -> None:
    half = (
        compile_literal(literal("0.50000000000000000000000000000000000000", XSD_DECIMAL)),
        compile_literal(literal("1/2", OWL_RATIONAL)),
    )
    third = compile_literal(literal("1/3", OWL_RATIONAL))
    long_decimal = compile_literal(literal("0.33333333333333333333333333333333333333", XSD_DECIMAL))
    assert half[0].data_identity == half[1].data_identity == NumericIdentity(1, 2)
    assert third.data_identity == NumericIdentity(1, 3)
    assert third.data_identity != long_decimal.data_identity
    assert compile_literal(literal("-0", XSD_INTEGER)).data_identity == NumericIdentity(0)
    assert compile_literal(literal("+0/999", OWL_RATIONAL)).data_identity == NumericIdentity(0)


def test_supported_inventory_covers_the_declared_builtin_map() -> None:
    assert len(SUPPORTED_DATATYPES) == 34
    assert XSD_BOOLEAN in SUPPORTED_DATATYPES
    assert OWL_REAL in SUPPORTED_DATATYPES
    assert compile_literal(literal("text", XSD_NAMESPACE + "string")).data_identity
    with pytest.raises(UnsupportedDatatypeError) as caught:
        compile_literal(literal("text", "urn:unsupported"))
    assert caught.value.code == "UNSUPPORTED_DATATYPE"


@pytest.mark.parametrize(
    ("source", "valid"),
    [
        (literal("+001", XSD_INTEGER), True),
        (literal("1.0", XSD_INTEGER), False),
        (literal(".125", XSD_DECIMAL), True),
        (literal("1E2", XSD_DECIMAL), False),
        (literal("false", XSD_BOOLEAN), True),
        (literal("FALSE", XSD_BOOLEAN), False),
        (literal("255", XSD_NAMESPACE + "unsignedByte"), True),
        (literal("256", XSD_NAMESPACE + "unsignedByte"), False),
    ],
)
def test_owl2_mode_agrees_with_core_recognized_lexical_boundary(
    source: Literal, valid: bool
) -> None:
    assert (not validate_lexical_form(source)) is valid
    if valid:
        assert compile_literal(source).source_literal is source
    else:
        with pytest.raises(InvalidLiteralError):
            compile_literal(source)
