from __future__ import annotations

import itertools

import pyowl_core.model as owl
import pytest

from pyhermit.datatypes import (
    XSD_ANY_URI,
    XSD_HEX_BINARY,
    XSD_INTEGER,
    XSD_LENGTH,
    XSD_PATTERN,
    XSD_STRING,
    BinaryKind,
    BinaryRange,
    CompiledLiteral,
    DataDomainRange,
    DatatypeClashKind,
    DatatypeConstraintComponent,
    DatatypeConstraintSolver,
    DatatypeLimits,
    DomainCardinalityConstraint,
    FacetRestriction,
    InequalityConstraint,
    LengthRange,
    RangeConstraint,
    StringIdentity,
    StringRange,
    URIIdentity,
    URIRange,
    XSDRegex,
    compile_datatype_semantic_model,
    compile_literal,
    restrict_datatype,
)
from pyhermit.exceptions import ResourceLimitError


def datatype(iri: str) -> owl.Datatype:
    return owl.Datatype(owl.IRI(iri))


def literal(lexical: str, iri: str) -> owl.Literal:
    return owl.Literal(lexical, datatype(iri))


def compiled(lexical: str, iri: str = XSD_INTEGER) -> CompiledLiteral:
    return compile_literal(literal(lexical, iri))


def exact_length_domain(iri: str, length: int) -> DataDomainRange:
    restriction = owl.DatatypeRestriction(
        datatype(iri),
        owl.CanonicalSet(
            (
                owl.FacetRestriction(
                    owl.IRI(XSD_LENGTH),
                    literal(str(length), XSD_INTEGER),
                ),
            )
        ),
    )
    model = compile_datatype_semantic_model((restriction,))
    return DataDomainRange.from_model(model, 0)


@pytest.mark.parametrize(
    ("pattern", "cardinality", "values"),
    [
        ("", 1, ("",)),
        ("a|a", 1, ("a",)),
        ("[a-c]", 3, ("a", "b", "c")),
        ("[ab]{0,2}", 7, ("", "a", "b", "aa", "ab", "ba", "bb")),
    ],
)
def test_symbolic_dfa_has_exact_finite_cardinality_and_enumeration(
    pattern: str,
    cardinality: int,
    values: tuple[str, ...],
) -> None:
    language = XSDRegex.compile(pattern)
    assert language.finite_cardinality() == cardinality
    assert set(language.enumerate_strings()) == set(values)
    assert language.cardinality_at_least(cardinality)
    assert not language.cardinality_at_least(cardinality + 1)


def test_symbolic_dfa_boolean_algebra_matches_a_small_exhaustive_oracle() -> None:
    left = XSDRegex.compile("[ab]{0,2}")
    right = XSDRegex.compile("a?")
    candidates = tuple(
        "".join(value) for length in range(3) for value in itertools.product("ab", repeat=length)
    )
    operations = (
        left.intersection(right),
        left.union(right),
        left.intersection(right.complement()),
    )
    for language in operations:
        expected = {value for value in candidates if language.fullmatch(value)}
        assert language.finite_cardinality() == len(expected)
        assert set(language.enumerate_strings()) == expected

    empty = XSDRegex.all().complement()
    assert empty.finite_cardinality() == 0
    assert empty.enumerate_strings() == ()
    assert XSDRegex.compile("a*").finite_cardinality() is None
    assert XSDRegex.compile("a*").cardinality_at_least(1_000_000)


def test_finite_string_and_uri_ranges_materialize_semantic_identities() -> None:
    empty_string = restrict_datatype(
        XSD_STRING,
        (FacetRestriction(XSD_LENGTH, compiled("0")),),
    )
    assert isinstance(empty_string, StringRange)
    assert empty_string.finite_cardinality() == 1
    assert empty_string.enumerate_values() == (StringIdentity(""),)
    assert not empty_string.cardinality_at_least(2)

    two_strings = restrict_datatype(
        XSD_STRING,
        (
            FacetRestriction(XSD_LENGTH, compiled("1")),
            FacetRestriction(XSD_PATTERN, compiled("[ab]", XSD_STRING)),
        ),
    )
    assert isinstance(two_strings, StringRange)
    assert two_strings.finite_cardinality() == 2
    assert set(two_strings.enumerate_values()) == {StringIdentity("a"), StringIdentity("b")}

    empty_uri = restrict_datatype(
        XSD_ANY_URI,
        (FacetRestriction(XSD_LENGTH, compiled("0")),),
    )
    assert isinstance(empty_uri, URIRange)
    assert empty_uri.finite_cardinality() == 1
    assert empty_uri.enumerate_values() == (URIIdentity(""),)


def test_mixed_domain_and_solver_do_not_treat_singleton_regex_as_infinite() -> None:
    singleton = exact_length_domain(XSD_STRING, 0)
    assert singleton.finite_cardinality() == 1
    assert singleton.enumerate_identities() == (StringIdentity(""),)
    assert singleton.cardinality_at_least(1)
    assert not singleton.cardinality_at_least(2)

    component = DatatypeConstraintComponent(
        variables=(0, 1),
        ranges=(RangeConstraint(0, singleton), RangeConstraint(1, singleton)),
        inequalities=(InequalityConstraint(0, 1, frozenset({50})),),
    )
    result = DatatypeConstraintSolver().solve(component)
    assert result.clash is not None
    assert result.clash.kind is DatatypeClashKind.UNSATISFIABLE_INEQUALITIES
    assert result.clash.dependencies == frozenset({50})

    cardinality = DatatypeConstraintComponent(
        variables=(0,),
        ranges=(RangeConstraint(0, singleton, dependencies=frozenset({51})),),
        cardinalities=(DomainCardinalityConstraint(0, 2, frozenset({52})),),
    )
    result = DatatypeConstraintSolver().solve(cardinality)
    assert result.clash is not None
    assert result.clash.kind is DatatypeClashKind.INSUFFICIENT_CARDINALITY
    assert result.clash.dependencies == frozenset({51, 52})


def test_binary_cardinality_threshold_does_not_materialize_hostile_giant_integers() -> None:
    empty_bytes = BinaryRange(BinaryKind.HEX, LengthRange.between(0, 0))
    assert empty_bytes.cardinality_up_to(10) == 1
    assert empty_bytes.cardinality_at_least(1)
    assert not empty_bytes.cardinality_at_least(2)

    giant_finite = BinaryRange(
        BinaryKind.HEX,
        LengthRange.between(2_000_000, 2_000_000),
    )
    assert giant_finite.finite_cardinality() is None
    assert giant_finite.cardinality_up_to(10_000) == 10_000
    assert giant_finite.cardinality_at_least(10_000)


def test_finite_regex_enumeration_obeys_materialization_limit() -> None:
    language = XSDRegex.compile("[ab]{0,8}")
    assert language.finite_cardinality() == 511
    with pytest.raises(ResourceLimitError) as limited:
        language.enumerate_strings(limits=DatatypeLimits(max_enumeration_values=100))
    assert limited.value.limit == "max_enumeration_values"


def test_binary_datatype_domain_threshold_uses_capped_count() -> None:
    one_byte = exact_length_domain(XSD_HEX_BINARY, 1)
    assert one_byte.finite_cardinality() == 256
    assert one_byte.cardinality_at_least(256)
    assert not one_byte.cardinality_at_least(257)
