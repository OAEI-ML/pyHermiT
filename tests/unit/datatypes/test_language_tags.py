from __future__ import annotations

import pyowl_core.model as owl
import pytest
from pyowl_core.exceptions import InvalidLiteralError as CoreInvalidLiteralError

from pyhermit.datatypes import (
    RDF_LANG_RANGE,
    RDF_PLAIN_LITERAL,
    XSD_STRING,
    FacetRestriction,
    LanguageTagRange,
    StringIdentity,
    StringRange,
    compile_literal,
    is_valid_language_tag,
    restrict_datatype,
)


def datatype(iri: str) -> owl.Datatype:
    return owl.Datatype(owl.IRI(iri))


def literal(text: str, iri: str, language: str | None = None) -> owl.Literal:
    return owl.Literal(text, datatype(iri), language)


@pytest.mark.parametrize(
    ("language", "valid"),
    [
        ("en", True),
        ("EN-gb", True),
        ("zh-cmn-Hans-CN", True),
        ("sl-rozaj-biske", True),
        ("de-a-aaa-b-bbb-x-private", True),
        ("x-private", True),
        ("i-klingon", True),
        ("sl-rozaj-rozaj", False),
        ("de-a-aaa-a-bbb", False),
        ("en-x", False),
        ("x", False),
        ("en--gb", False),
    ],
)
def test_language_tag_validator_matches_the_public_core_boundary(
    language: str,
    valid: bool,
) -> None:
    assert is_valid_language_tag(language) is valid
    if valid:
        assert literal("value", RDF_PLAIN_LITERAL, language).language == language.lower()
    else:
        with pytest.raises(CoreInvalidLiteralError):
            literal("value", RDF_PLAIN_LITERAL, language)


def test_basic_filter_algebra_is_relative_to_valid_canonical_tags() -> None:
    english = LanguageTagRange.basic("EN")
    not_english = english.complement()
    assert english.contains("en")
    assert english.contains("en-gb")
    assert not english.contains("fr")
    assert not english.contains("EN")
    assert not_english.contains("fr")
    assert english.intersection(not_english).is_empty_exact()
    assert english.union(not_english).complement().is_empty_exact()
    assert english.finite_cardinality() is None
    assert english.cardinality_at_least(100_000)


@pytest.mark.parametrize(
    "pathological_prefix",
    ("q", "sl-rozaj-rozaj", "de-a-aaa-a-bbb"),
)
def test_unrepairable_basic_prefixes_do_not_create_phantom_symbolic_values(
    pathological_prefix: str,
) -> None:
    selected = LanguageTagRange.basic(pathological_prefix)
    assert selected.is_empty_exact()
    assert selected.finite_cardinality() == 0
    assert selected.cardinality_up_to(10) == 0
    assert selected.enumerate_tags() == ()
    assert selected.complement().cardinality_at_least(10_000)


def test_grandfathered_finite_cells_have_exact_cardinality_and_enumeration() -> None:
    legacy_i = LanguageTagRange.basic("i")
    values = legacy_i.enumerate_tags()
    assert values == (
        "i-ami",
        "i-bnn",
        "i-default",
        "i-enochian",
        "i-hak",
        "i-klingon",
        "i-lux",
        "i-mingo",
        "i-navajo",
        "i-pwn",
        "i-tao",
        "i-tay",
        "i-tsu",
    )
    assert legacy_i.finite_cardinality() == len(values)
    assert not legacy_i.cardinality_at_least(len(values) + 1)

    irregular = LanguageTagRange.basic("en-gb-oed")
    assert irregular.enumerate_tags() == ("en-gb-oed",)
    assert irregular.complement().contains("en-gb")


def test_language_tag_witnesses_are_valid_deterministic_and_exclusion_aware() -> None:
    english = LanguageTagRange.basic("en")
    assert english.first_tag() == "en"
    alternative = english.first_tag(excluding=("en",))
    assert alternative == english.first_tag(excluding=("en",))
    assert alternative != "en"
    assert english.contains(alternative)
    assert is_valid_language_tag(alternative)

    private = LanguageTagRange.basic("x")
    assert private.first_tag() == "x-a"


def test_lang_range_facets_and_plain_literal_complements_never_admit_invalid_tags() -> None:
    facet_value = compile_literal(literal("sl-rozaj-rozaj", XSD_STRING))
    impossible = restrict_datatype(
        RDF_PLAIN_LITERAL,
        (FacetRestriction(RDF_LANG_RANGE, facet_value),),
    )
    assert isinstance(impossible, StringRange)
    assert impossible.is_empty_exact()
    assert impossible.finite_cardinality() == 0

    universe = StringRange.all(RDF_PLAIN_LITERAL)
    assert not universe.contains(StringIdentity("noncanonical", "EN"))
    assert not universe.contains(StringIdentity("phantom", "sl-rozaj-rozaj"))
    assert universe.intersection(impossible.complement()).contains(
        compile_literal(literal("real", RDF_PLAIN_LITERAL, "en"))
    )
