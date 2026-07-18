from __future__ import annotations

from typing import Any

import pyowl_core.model as owl

from pyhermit.config import IndividualGrouping, ReasonerConfig
from pyhermit.datatypes import XSD_INTEGER


def _individual(name: str) -> owl.NamedIndividual:
    return owl.NamedIndividual(owl.IRI(f"urn:test:realization:property-individual:{name}"))


def _object(name: str) -> owl.ObjectProperty:
    return owl.ObjectProperty(owl.IRI(f"urn:test:realization:object:{name}"))


def _data(name: str) -> owl.DataProperty:
    return owl.DataProperty(owl.IRI(f"urn:test:realization:data:{name}"))


def test_object_values_cover_subproperties_inverses_equality_and_instance_map(
    make_realization: Any,
) -> None:
    p, q = _object("p"), _object("q")
    first, alias, target = (_individual(name) for name in ("first", "alias", "target"))
    harness = make_realization(
        (
            owl.SameIndividual(owl.CanonicalSet((first, alias))),
            owl.SubObjectPropertyOf(p, q),
            owl.ObjectPropertyAssertion(p, first, target),
        )
    )
    service = harness.realization

    assert service.object_property_values(alias, q) == frozenset((target,))
    assert service.object_property_values(target, owl.inverse_property(p)) == frozenset(
        (first, alias)
    )
    assert service.has_object_property_relationship(alias, q, target)
    assert service.object_property_instances(q) == {
        first: frozenset((target,)),
        alias: frozenset((target,)),
    }
    assert service.object_property_values(first, owl.OWL_BOTTOM_OBJECT_PROPERTY) == frozenset()
    assert service.object_property_values(first, owl.OWL_TOP_OBJECT_PROPERTY) == frozenset(
        (first, alias, target)
    )

    expected = frozenset(
        candidate
        for candidate in (first, alias, target)
        if harness.entailment.entails(owl.ObjectPropertyAssertion(q, alias, candidate))
    )
    assert service.object_property_values(alias, q) == expected


def test_data_values_preserve_explicit_lexical_aliases_and_never_invent_witnesses(
    make_realization: Any,
) -> None:
    p, q, other = _data("p"), _data("q"), _data("other")
    first, alias, unrelated = (_individual(name) for name in ("first", "alias", "unrelated"))
    integer = owl.Datatype(owl.IRI(XSD_INTEGER))
    canonical = owl.Literal("1", integer)
    lexical_alias = owl.Literal("01", integer)
    existential_only = owl.DataSomeValuesFrom((other,), integer)
    harness = make_realization(
        (
            owl.SameIndividual(owl.CanonicalSet((first, alias))),
            owl.SubDataPropertyOf(p, q),
            owl.DataPropertyAssertion(p, first, canonical),
            owl.DataPropertyAssertion(other, unrelated, lexical_alias),
            owl.ClassAssertion(existential_only, first),
        )
    )
    service = harness.realization

    assert service.source_literals == frozenset((canonical, lexical_alias))
    assert service.data_property_values(alias, q) == frozenset((canonical, lexical_alias))
    assert service.has_data_property_relationship(alias, q, lexical_alias)
    assert service.data_property_values(first, other) == frozenset()
    assert service.data_property_values(first, owl.OWL_TOP_DATA_PROPERTY) == frozenset(
        (canonical, lexical_alias)
    )
    assert service.data_property_values(first, owl.OWL_BOTTOM_DATA_PROPERTY) == frozenset()

    expected = frozenset(
        literal
        for literal in (canonical, lexical_alias)
        if harness.entailment.entails(owl.DataPropertyAssertion(q, alias, literal))
    )
    assert service.data_property_values(alias, q) == expected


def test_semantic_functional_merge_drives_same_as_and_grouped_object_answers(
    make_realization: Any,
) -> None:
    p = _object("functional")
    source, first, second = (
        _individual(name) for name in ("functional-source", "first-value", "second-value")
    )
    service = make_realization(
        (
            owl.FunctionalObjectProperty(p),
            owl.ObjectPropertyAssertion(p, source, first),
            owl.ObjectPropertyAssertion(p, source, second),
        ),
        config=ReasonerConfig(individual_grouping=IndividualGrouping.BY_SAME_AS),
    ).realization

    assert service.same_individuals(first) == frozenset((first, second))
    assert service.object_property_values(source, p) == frozenset((frozenset((first, second)),))


def test_generated_object_answers_match_naive_entailment_oracle(
    make_realization: Any,
) -> None:
    p, q, r = (_object(name) for name in ("generated-p", "generated-q", "generated-r"))
    first, second, third = (
        _individual(name) for name in ("generated-first", "generated-second", "generated-third")
    )
    harness = make_realization(
        (
            owl.SubObjectPropertyOf(p, q),
            owl.SubObjectPropertyOf(q, r),
            owl.ObjectPropertyAssertion(p, first, second),
            owl.ObjectPropertyAssertion(q, second, third),
        )
    )
    candidates = (first, second, third)

    for property_ in (p, q, r, owl.inverse_property(p)):
        for subject in candidates:
            expected = frozenset(
                target
                for target in candidates
                if harness.entailment.entails(
                    owl.ObjectPropertyAssertion(property_, subject, target)
                )
            )
            assert harness.realization.object_property_values(subject, property_) == expected
