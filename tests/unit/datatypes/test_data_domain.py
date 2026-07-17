from __future__ import annotations

import itertools

import pyowl_core.model as owl
import pytest

from pyhermit.datatypes import (
    RDF_PLAIN_LITERAL,
    XSD_BOOLEAN,
    XSD_DATE_TIME,
    XSD_DATE_TIME_STAMP,
    XSD_DECIMAL,
    XSD_FLOAT,
    XSD_INTEGER,
    XSD_STRING,
    CompiledLiteral,
    DataDomainRange,
    DatatypeLimits,
    NumericIdentity,
    StringIdentity,
    compile_datatype_semantic_model,
    compile_literal,
)
from pyhermit.events import CancellationSource
from pyhermit.exceptions import (
    ReasonerInterruptedError,
    ResourceLimitError,
    UnsupportedDatatypeError,
)


def datatype(iri: str) -> owl.Datatype:
    return owl.Datatype(owl.IRI(iri))


def literal(lexical: str, iri: str, language: str | None = None) -> owl.Literal:
    return owl.Literal(lexical, datatype(iri), language)


def compiled(
    lexical: str,
    iri: str,
    language: str | None = None,
) -> CompiledLiteral:
    return compile_literal(literal(lexical, iri, language))


def domain(
    data_range: owl.DataRange,
    *,
    definitions: tuple[owl.DatatypeDefinition, ...] = (),
) -> DataDomainRange:
    model = compile_datatype_semantic_model((data_range,), definitions=definitions)
    return DataDomainRange.from_model(model, 0)


def test_mixed_disjoint_families_and_finite_union_cardinality_are_exact() -> None:
    disjoint = owl.DataIntersectionOf(
        owl.CanonicalSet((datatype(XSD_INTEGER), datatype(XSD_STRING)))
    )
    assert domain(disjoint).is_empty_exact()

    zero = owl.DataIntersectionOf(
        owl.CanonicalSet(
            (
                datatype("http://www.w3.org/2001/XMLSchema#nonNegativeInteger"),
                datatype("http://www.w3.org/2001/XMLSchema#nonPositiveInteger"),
            )
        )
    )
    word = owl.DataOneOf(owl.CanonicalSet((literal("abc", XSD_STRING),)))
    either = domain(owl.DataUnionOf(owl.CanonicalSet((word, zero))))
    assert either.finite_cardinality() == 2
    assert either.cardinality_at_least(2)
    assert not either.cardinality_at_least(3)
    assert set(either.enumerate_identities()) == {
        NumericIdentity(0),
        StringIdentity("abc"),
    }


def test_numeric_overlap_subtracts_proper_nested_domains_without_interval_loss() -> None:
    decimal_not_integer = domain(
        owl.DataIntersectionOf(
            owl.CanonicalSet(
                (
                    datatype(XSD_DECIMAL),
                    owl.DataComplementOf(datatype(XSD_INTEGER)),
                )
            )
        )
    )
    assert not decimal_not_integer.is_empty_exact()
    assert decimal_not_integer.finite_cardinality() is None
    assert decimal_not_integer.cardinality_at_least(100_000)
    assert decimal_not_integer.contains(compiled("0.5", XSD_DECIMAL))
    assert not decimal_not_integer.contains(compiled("1.0", XSD_DECIMAL))
    assert not decimal_not_integer.contains(compiled("1", XSD_INTEGER))

    singleton = DataDomainRange.enumeration((compiled("1.0", XSD_DECIMAL),))
    assert singleton.intersection(decimal_not_integer).is_empty_exact()


def test_string_plain_literal_overlap_and_data_domain_complement() -> None:
    strings = domain(datatype(XSD_STRING))
    assert strings.contains(compiled("text", XSD_STRING))
    assert strings.contains(compiled("text", RDF_PLAIN_LITERAL))
    assert not strings.contains(compiled("text", RDF_PLAIN_LITERAL, "en"))

    not_strings = strings.complement()
    assert not not_strings.contains(compiled("text", XSD_STRING))
    assert not_strings.contains(compiled("text", RDF_PLAIN_LITERAL, "en"))
    assert not_strings.contains(compiled("1", XSD_INTEGER))
    assert not not_strings.is_empty_exact()


def test_date_time_stamp_is_a_proper_subset_of_date_time() -> None:
    stamp = domain(datatype(XSD_DATE_TIME_STAMP))
    zoned = compiled("2000-01-01T00:00:00Z", XSD_DATE_TIME)
    unzoned = compiled("2000-01-01T00:00:00", XSD_DATE_TIME)
    assert stamp.contains(zoned)
    assert not stamp.contains(unzoned)
    assert stamp.complement().contains(unzoned)
    assert not stamp.complement().contains(zoned)


def test_enumeration_uses_data_identity_not_source_or_facet_comparison() -> None:
    numeric_aliases = domain(
        owl.DataOneOf(
            owl.CanonicalSet(
                (
                    literal("01", XSD_INTEGER),
                    literal("1.0", XSD_DECIMAL),
                )
            )
        )
    )
    assert numeric_aliases.finite_cardinality() == 1
    assert numeric_aliases.contains(compiled("1", XSD_INTEGER))

    positive_zero = domain(owl.DataOneOf(owl.CanonicalSet((literal("+0", XSD_FLOAT),))))
    assert positive_zero.contains(compiled("0", XSD_FLOAT))
    assert not positive_zero.contains(compiled("-0", XSD_FLOAT))


def test_custom_aliases_expand_before_boolean_algebra() -> None:
    custom = datatype("urn:test:data-domain:custom")
    definition = owl.DatatypeDefinition(
        custom,
        owl.DataOneOf(
            owl.CanonicalSet(
                (
                    literal("1", XSD_INTEGER),
                    literal("yes", XSD_STRING),
                )
            )
        ),
    )
    selected = domain(custom, definitions=(definition,))
    assert selected.finite_cardinality() == 2
    assert selected.contains(compiled("1.0", XSD_DECIMAL))
    assert selected.contains(compiled("yes", XSD_STRING))
    assert selected.complement().contains(compiled("no", XSD_STRING))


def test_boolean_algebra_matches_finite_sample_oracle_across_families() -> None:
    values = (
        compiled("0", XSD_INTEGER),
        compiled("1", XSD_INTEGER),
        compiled("false", XSD_BOOLEAN),
        compiled("word", XSD_STRING),
        compiled("word", RDF_PLAIN_LITERAL, "en"),
    )
    ranges = tuple(
        DataDomainRange.enumeration(
            value for value, include in zip(values, mask, strict=True) if include
        )
        for mask in itertools.product((False, True), repeat=len(values))
    )
    sample = tuple(value.data_identity for value in values)
    for left in ranges:
        left_members = {value.data_identity for value in values if left.contains(value)}
        complement = left.complement()
        assert {value.data_identity for value in values if complement.contains(value)} == (
            set(sample) - left_members
        )
        for right in ranges[::7]:
            right_members = {value.data_identity for value in values if right.contains(value)}
            assert {
                value.data_identity for value in values if left.intersection(right).contains(value)
            } == left_members & right_members
            assert {
                value.data_identity for value in values if left.union(right).contains(value)
            } == left_members | right_members


def test_mixed_domain_limits_cancellation_and_opaque_policy_fail_closed() -> None:
    one = owl.DataOneOf(owl.CanonicalSet((literal("1", XSD_INTEGER),)))
    two = owl.DataOneOf(owl.CanonicalSet((literal("2", XSD_INTEGER),)))
    union = owl.DataUnionOf(owl.CanonicalSet((one, two)))
    payload_model = compile_datatype_semantic_model((union,))
    with pytest.raises(ResourceLimitError) as limited:
        DataDomainRange.from_model(
            payload_model,
            0,
            limits=DatatypeLimits(max_data_range_nodes=1),
        )
    assert limited.value.limit == "max_data_range_nodes"

    cancellation = CancellationSource()
    cancellation.interrupt("domain test")
    with pytest.raises(ReasonerInterruptedError, match="domain test"):
        DataDomainRange.from_model(payload_model, 0, cancellation=cancellation.token)

    unknown = "urn:test:data-domain:opaque"
    opaque_model = compile_datatype_semantic_model(
        (datatype(unknown),),
        opaque_datatype_iris=(unknown,),
    )
    with pytest.raises(UnsupportedDatatypeError):
        DataDomainRange.from_model(opaque_model, 0)
