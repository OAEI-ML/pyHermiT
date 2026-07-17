from __future__ import annotations

import dataclasses

import pytest
from pyowl_core.model import IRI, Datatype, Literal

from pyhermit.datatypes import (
    RDF_LANG_RANGE,
    RDF_PLAIN_LITERAL,
    RDF_XML_LITERAL,
    RDFS_LITERAL,
    XSD_ANY_URI,
    XSD_BASE64_BINARY,
    XSD_DATE_TIME,
    XSD_DATE_TIME_STAMP,
    XSD_HEX_BINARY,
    XSD_INTEGER,
    XSD_LANGUAGE,
    XSD_LENGTH,
    XSD_MAX_EXCLUSIVE,
    XSD_MAX_LENGTH,
    XSD_MIN_INCLUSIVE,
    XSD_MIN_LENGTH,
    XSD_NAME,
    XSD_NCNAME,
    XSD_NMTOKEN,
    XSD_NORMALIZED_STRING,
    XSD_PATTERN,
    XSD_STRING,
    XSD_TOKEN,
    BinaryIdentity,
    BinaryKind,
    BinaryRange,
    ComparisonOrder,
    DatatypeLimits,
    DateTimeRange,
    FacetRestriction,
    LengthRange,
    LexicalCompatibility,
    LiteralRange,
    StringIdentity,
    StringRange,
    URIIdentity,
    URIRange,
    XMLRange,
    XSDRegex,
    compile_literal,
    range_for_datatype,
    restrict_datatype,
)
from pyhermit.exceptions import InvalidLiteralError, OntologyProfileError, ResourceLimitError


def literal(lexical: str, datatype_iri: str, language: str | None = None) -> Literal:
    return Literal(lexical, Datatype(IRI(datatype_iri)), language)


def compiled(lexical: str, datatype_iri: str, language: str | None = None):  # type: ignore[no-untyped-def]
    return compile_literal(literal(lexical, datatype_iri, language))


def test_string_whitespace_value_mapping_and_hermit_compatibility_are_explicit() -> None:
    normalized = compiled("a\tb\nc", XSD_NORMALIZED_STRING)
    token = compiled(" \ta  b\n ", XSD_TOKEN)
    assert normalized.data_identity == StringIdentity("a b c")
    assert token.data_identity == StringIdentity("a b")
    with pytest.raises(InvalidLiteralError):
        compile_literal(
            literal(" a  b ", XSD_TOKEN),
            compatibility=LexicalCompatibility.HERMIT_1_4,
        )
    compatible = compile_literal(
        literal("a b", XSD_TOKEN),
        compatibility=LexicalCompatibility.HERMIT_1_4,
    )
    assert compatible.data_identity == StringIdentity("a b")


@pytest.mark.parametrize(
    ("datatype_iri", "valid", "invalid"),
    [
        (XSD_LANGUAGE, ("en", "en-GB", "abc-123"), ("", "9en", "en-", "toolonggg")),
        (XSD_NAME, ("a", ":a", "_x", "éclair"), ("", "1a", "a b")),
        (XSD_NCNAME, ("a", "_x", "éclair"), ("", ":a", "a:b", "1a")),
        (XSD_NMTOKEN, ("a", "1", "a:b", "a-b"), ("", "a b")),
    ],
)
def test_derived_string_lexical_boundaries(
    datatype_iri: str,
    valid: tuple[str, ...],
    invalid: tuple[str, ...],
) -> None:
    for lexical in valid:
        assert isinstance(compiled(lexical, datatype_iri).data_identity, StringIdentity)
    for lexical in invalid:
        with pytest.raises(InvalidLiteralError):
            compiled(lexical, datatype_iri)


def test_plain_string_overlap_and_language_identity_use_core_canonical_key() -> None:
    plain = compiled("same", RDF_PLAIN_LITERAL)
    string = compiled("same", XSD_STRING)
    english = compiled("same", RDF_PLAIN_LITERAL, "EN-gb")
    assert plain.data_identity == string.data_identity == StringIdentity("same")
    assert english.source_literal.language == "en-gb"
    assert english.data_identity == StringIdentity("same", "en-gb")
    assert english.data_identity != plain.data_identity


def test_binary_decoding_padding_and_primitive_disjointness() -> None:
    hex_value = compiled(" 0aFF ", XSD_HEX_BINARY)
    base64_value = compiled(" C v 8 = ", XSD_BASE64_BINARY)
    assert hex_value.data_identity == BinaryIdentity(BinaryKind.HEX, b"\x0a\xff")
    assert base64_value.data_identity == BinaryIdentity(BinaryKind.BASE64, b"\x0a\xff")
    assert hex_value.data_identity != base64_value.data_identity
    for lexical in ("0", "0g", "0a ff"):
        with pytest.raises(InvalidLiteralError):
            compiled(lexical, XSD_HEX_BINARY)
    for lexical in ("A===", "AB==", "AA=A", "AAA", "@@=="):
        with pytest.raises(InvalidLiteralError):
            compiled(lexical, XSD_BASE64_BINARY)


def test_any_uri_is_disjoint_from_strings_and_never_resolved() -> None:
    uri = compiled("../relative?q=1#fragment", XSD_ANY_URI)
    text = compiled("../relative?q=1#fragment", XSD_STRING)
    assert uri.data_identity == URIIdentity("../relative?q=1#fragment")
    assert uri.data_identity != text.data_identity
    assert uri.source_identity.lexical_form.startswith("..")


def test_date_time_identity_comparison_and_timezone_partial_order_are_separate() -> None:
    utc = compiled("2000-01-01T00:00:00Z", XSD_DATE_TIME)
    shifted = compiled("2000-01-01T01:00:00+01:00", XSD_DATE_TIME)
    unzoned = compiled("2000-01-01T00:00:00", XSD_DATE_TIME)
    much_later = compiled("2000-01-02T00:00:01Z", XSD_DATE_TIME)
    assert utc.data_identity != shifted.data_identity
    assert utc.comparison.compare(shifted.comparison) is ComparisonOrder.EQUAL
    assert utc.comparison.compare(unzoned.comparison) is ComparisonOrder.UNORDERED
    assert much_later.comparison.compare(unzoned.comparison) is ComparisonOrder.GREATER


def test_date_time_calendar_end_of_day_and_timestamp_boundaries() -> None:
    end = compiled("2000-02-29T24:00:00Z", XSD_DATE_TIME)
    next_day = compiled("2000-03-01T00:00:00Z", XSD_DATE_TIME)
    assert end.data_identity == next_day.data_identity
    assert compiled("0000-01-01T00:00:00Z", XSD_DATE_TIME)
    for lexical in (
        "-0000-01-01T00:00:00Z",
        "1900-02-29T00:00:00Z",
        "2000-01-01T24:00:00.1Z",
        "2000-01-01T00:00:00+14:01",
    ):
        with pytest.raises(InvalidLiteralError):
            compiled(lexical, XSD_DATE_TIME)
    with pytest.raises(InvalidLiteralError):
        compiled("2000-01-01T00:00:00", XSD_DATE_TIME_STAMP)


def test_pinned_hermit_end_of_day_quirk_stays_private() -> None:
    end = compile_literal(
        literal("2000-01-01T24:00:00Z", XSD_DATE_TIME),
        compatibility=LexicalCompatibility.HERMIT_1_4,
    )
    next_day = compile_literal(
        literal("2000-01-02T00:00:00Z", XSD_DATE_TIME),
        compatibility=LexicalCompatibility.HERMIT_1_4,
    )
    assert end.comparison == next_day.comparison
    assert end.data_identity != next_day.data_identity


def test_xml_literal_canonical_identity_and_entity_safety() -> None:
    empty_element = compiled("<a/>", RDF_XML_LITERAL)
    explicit_element = compiled("<a></a>", RDF_XML_LITERAL)
    reordered = compiled('<a y="2" x="1"/>', RDF_XML_LITERAL)
    canonical = compiled('<a x="1" y="2"></a>', RDF_XML_LITERAL)
    assert empty_element.data_identity == explicit_element.data_identity
    assert reordered.data_identity == canonical.data_identity
    assert empty_element.data_identity != StringIdentity("<a></a>")
    for lexical in (
        '<!DOCTYPE a [<!ENTITY x "boom">]><a>&x;</a>',
        "<a>&undefined;</a>",
        "<a>",
    ):
        with pytest.raises(InvalidLiteralError):
            compiled(lexical, RDF_XML_LITERAL)


def test_nonnumeric_values_and_ranges_are_immutable() -> None:
    value = compiled("ff", XSD_HEX_BINARY)
    with pytest.raises(dataclasses.FrozenInstanceError):
        value.data_identity = BinaryIdentity(BinaryKind.HEX, b"")  # type: ignore[misc]
    length = LengthRange.between(1, 2)
    assert length.contains(1)
    assert length.complement().contains(0)
    assert length.intersection(length.complement()).is_empty_exact()


def test_binary_length_facets_have_exact_cardinality_and_algebra() -> None:
    one_octet = restrict_datatype(
        XSD_HEX_BINARY,
        (FacetRestriction(XSD_LENGTH, compiled("1", XSD_INTEGER)),),
    )
    assert isinstance(one_octet, BinaryRange)
    assert one_octet.finite_cardinality() == 256
    assert one_octet.contains(compiled("00", XSD_HEX_BINARY))
    assert not one_octet.contains(compiled("", XSD_HEX_BINARY))
    assert not one_octet.contains(compiled("AA==", XSD_BASE64_BINARY))
    assert len(one_octet.enumerate_values()) == 256
    assert one_octet.intersection(one_octet.complement()).is_empty_exact()


def test_string_length_pattern_and_language_facets_compose_exactly() -> None:
    restricted = restrict_datatype(
        XSD_STRING,
        (
            FacetRestriction(XSD_MIN_LENGTH, compiled("2", XSD_INTEGER)),
            FacetRestriction(XSD_MAX_LENGTH, compiled("4", XSD_INTEGER)),
            FacetRestriction(XSD_PATTERN, compiled("[a-z]+", XSD_STRING)),
        ),
    )
    assert isinstance(restricted, StringRange)
    assert restricted.contains(compiled("ab", XSD_STRING))
    assert restricted.contains(compiled("abcd", RDF_PLAIN_LITERAL))
    assert not restricted.contains(compiled("a", XSD_STRING))
    assert not restricted.contains(compiled("ABCDE", XSD_STRING))
    assert restricted.complement().contains(compiled("A", XSD_STRING))
    assert restricted.intersection(restricted.complement()).is_empty_exact()

    english = restrict_datatype(
        RDF_PLAIN_LITERAL,
        (FacetRestriction(RDF_LANG_RANGE, compiled("EN", XSD_STRING)),),
    )
    assert isinstance(english, StringRange)
    assert english.contains(compiled("hello", RDF_PLAIN_LITERAL, "en"))
    assert english.contains(compiled("hello", RDF_PLAIN_LITERAL, "en-GB"))
    assert not english.contains(compiled("hello", RDF_PLAIN_LITERAL, "fr"))
    assert not english.contains(compiled("hello", RDF_PLAIN_LITERAL))
    assert english.complement().contains(compiled("hello", RDF_PLAIN_LITERAL, "fr"))


def test_uri_facets_and_nonnumeric_range_inventory() -> None:
    uri_range = restrict_datatype(
        XSD_ANY_URI,
        (
            FacetRestriction(XSD_MIN_LENGTH, compiled("3", XSD_INTEGER)),
            FacetRestriction(XSD_PATTERN, compiled("[a-z]+", XSD_STRING)),
        ),
    )
    assert isinstance(uri_range, URIRange)
    assert uri_range.contains(compiled("abc", XSD_ANY_URI))
    assert not uri_range.contains(compiled("ab", XSD_ANY_URI))
    assert not uri_range.contains(compiled("123", XSD_ANY_URI))
    assert isinstance(range_for_datatype(RDF_XML_LITERAL), XMLRange)
    assert isinstance(range_for_datatype(RDFS_LITERAL), LiteralRange)
    assert isinstance(range_for_datatype(XSD_DATE_TIME), DateTimeRange)


def test_bound_date_time_facets_preserve_partial_order_semantics() -> None:
    lower = compiled("2000-01-01T00:00:00Z", XSD_DATE_TIME)
    upper = compiled("2000-01-03T00:00:00Z", XSD_DATE_TIME)
    restricted = restrict_datatype(
        XSD_DATE_TIME,
        (
            FacetRestriction(XSD_MIN_INCLUSIVE, lower),
            FacetRestriction(XSD_MAX_EXCLUSIVE, upper),
        ),
    )
    assert isinstance(restricted, DateTimeRange)
    assert restricted.contains(lower)
    assert restricted.contains(compiled("2000-01-02T00:00:00+01:00", XSD_DATE_TIME))
    assert not restricted.contains(upper)


def test_illegal_facet_combinations_and_values_fail_before_reasoning() -> None:
    cases = (
        (XSD_HEX_BINARY, FacetRestriction(XSD_PATTERN, compiled(".*", XSD_STRING))),
        (XSD_STRING, FacetRestriction(RDF_LANG_RANGE, compiled("en", XSD_STRING))),
        (RDF_XML_LITERAL, FacetRestriction(XSD_LENGTH, compiled("1", XSD_INTEGER))),
    )
    for datatype_iri, facet in cases:
        with pytest.raises(OntologyProfileError) as caught:
            restrict_datatype(datatype_iri, (facet,))
        assert caught.value.code == "ILLEGAL_DATATYPE_FACET"
    with pytest.raises(OntologyProfileError) as caught:
        restrict_datatype(
            XSD_STRING,
            (FacetRestriction(XSD_LENGTH, compiled("-1", XSD_INTEGER)),),
        )
    assert caught.value.code == "INVALID_FACET_VALUE"
    with pytest.raises(OntologyProfileError, match="basic language range"):
        restrict_datatype(
            RDF_PLAIN_LITERAL,
            (FacetRestriction(RDF_LANG_RANGE, compiled("en-*", XSD_STRING)),),
        )


def test_xsd_regex_language_algebra_is_anchored_and_exact() -> None:
    consonants = XSDRegex.compile("[a-z-[aeiou]]+")
    two_or_three = XSDRegex.compile(".{2,3}")
    selected = consonants.intersection(two_or_three)
    assert selected.fullmatch("bc")
    assert selected.fullmatch("xyz")
    assert not selected.fullmatch("b")
    assert not selected.fullmatch("abc")
    assert not selected.fullmatch("xbcx")
    assert selected.intersection(selected.complement()).is_empty_exact()
    assert not selected.union(selected.complement()).is_empty_exact()
    assert XSDRegex.compile("[\\i-[:]][\\c-[:]]*").fullmatch("valid_Name")
    assert not XSDRegex.compile("[\\i-[:]][\\c-[:]]*").fullmatch("bad:name")


def test_nonnumeric_resource_limits_fire_before_unbounded_work() -> None:
    with pytest.raises(ResourceLimitError) as binary:
        compile_literal(
            literal("00" * 11, XSD_HEX_BINARY),
            limits=DatatypeLimits(max_binary_bytes=10),
        )
    assert binary.value.limit == "max_binary_bytes"

    with pytest.raises(ResourceLimitError) as xml_depth:
        compile_literal(
            literal("<a>" * 4 + "</a>" * 4, RDF_XML_LITERAL),
            limits=DatatypeLimits(max_xml_depth=3),
        )
    assert xml_depth.value.limit == "max_xml_depth"

    with pytest.raises(ResourceLimitError) as regex:
        XSDRegex.compile("a{11}", limits=DatatypeLimits(max_pattern_states=10))
    assert regex.value.limit == "max_pattern_states"

    with pytest.raises(ResourceLimitError) as length_automaton:
        restrict_datatype(
            XSD_STRING,
            (FacetRestriction(XSD_LENGTH, compiled("11", XSD_INTEGER)),),
            limits=DatatypeLimits(max_pattern_states=10),
        )
    assert length_automaton.value.limit == "max_pattern_states"
