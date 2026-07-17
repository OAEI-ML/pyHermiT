from __future__ import annotations

import pyowl_core.model as owl
import pytest

from pyhermit.datatypes import (
    OWL_RATIONAL,
    OWL_REAL,
    RDF_PLAIN_LITERAL,
    RDF_XML_LITERAL,
    XSD_ANY_URI,
    XSD_BASE64_BINARY,
    XSD_BOOLEAN,
    XSD_DATE_TIME,
    XSD_DOUBLE,
    XSD_HEX_BINARY,
    XSD_INTEGER,
    XSD_STRING,
    BinaryIdentity,
    BooleanIdentity,
    DataDomainRange,
    DatatypeConstraintComponent,
    DatatypeConstraintSolver,
    DateTimeIdentity,
    IEEEIdentity,
    InequalityConstraint,
    NumericIdentity,
    RangeConstraint,
    StringIdentity,
    SymbolicDataWitness,
    URIIdentity,
    XMLIdentity,
    XSDRegex,
    compile_datatype_semantic_model,
)


def datatype(iri: str) -> owl.Datatype:
    return owl.Datatype(owl.IRI(iri))


def domain(root: owl.DataRange) -> DataDomainRange:
    model = compile_datatype_semantic_model((root,))
    return DataDomainRange.from_model(model, 0)


def test_regex_witness_search_is_shortest_deterministic_and_does_not_expand_unicode() -> None:
    language = XSDRegex.compile("[ab]*")
    assert language.first_string() == ""
    assert language.first_string(excluding=("", "a", "b", "aa")) == "ab"
    assert language.first_string(excluding=("", "a", "b", "aa")) == "ab"
    assert XSDRegex.all().first_string(excluding=("",)) == "\t"
    with pytest.raises(ValueError, match="empty"):
        XSDRegex.empty().first_string()


@pytest.mark.parametrize(
    ("datatype_iri", "identity_type"),
    [
        (XSD_INTEGER, NumericIdentity),
        (XSD_BOOLEAN, BooleanIdentity),
        (XSD_DOUBLE, IEEEIdentity),
        (XSD_STRING, StringIdentity),
        (RDF_PLAIN_LITERAL, StringIdentity),
        (XSD_HEX_BINARY, BinaryIdentity),
        (XSD_BASE64_BINARY, BinaryIdentity),
        (XSD_ANY_URI, URIIdentity),
        (RDF_XML_LITERAL, XMLIdentity),
        (XSD_DATE_TIME, DateTimeIdentity),
    ],
)
def test_every_literal_denotable_family_has_a_concrete_deterministic_witness(
    datatype_iri: str,
    identity_type: type[object],
) -> None:
    selected = domain(datatype(datatype_iri))
    first = selected.witness()
    second = selected.witness(excluding=(first,))
    assert isinstance(first, identity_type)
    assert isinstance(second, identity_type)
    assert first != second
    assert selected.witness() == first


def test_non_literal_denotable_real_cell_uses_stable_explicit_symbolic_certificates() -> None:
    irrational = domain(
        owl.DataIntersectionOf(
            owl.CanonicalSet(
                (
                    datatype(OWL_REAL),
                    owl.DataComplementOf(datatype(OWL_RATIONAL)),
                )
            )
        )
    )
    first = irrational.witness()
    second = irrational.witness(excluding=(first,))
    assert isinstance(first, SymbolicDataWitness)
    assert isinstance(second, SymbolicDataWitness)
    assert first.domain_digest == second.domain_digest
    assert (first.ordinal, second.ordinal) == (0, 1)
    assert irrational.witness() == first


def test_solver_reconstructs_distinct_witnesses_for_eliminated_infinite_variables() -> None:
    irrational = domain(
        owl.DataIntersectionOf(
            owl.CanonicalSet(
                (
                    datatype(OWL_REAL),
                    owl.DataComplementOf(datatype(OWL_RATIONAL)),
                )
            )
        )
    )
    component = DatatypeConstraintComponent(
        variables=(0, 1),
        ranges=(RangeConstraint(0, irrational), RangeConstraint(1, irrational)),
        inequalities=(InequalityConstraint(0, 1),),
    )
    solver = DatatypeConstraintSolver()
    result = solver.solve(component)
    assert result.satisfiable
    values = tuple(item.value for item in result.assignments)
    assert all(isinstance(value, SymbolicDataWitness) for value in values)
    assert len(set(values)) == 2
    assert result == solver.solve(component)
