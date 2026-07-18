"""Public-service differential coverage for the completed native backend.

This suite is intentionally outside the default pure-Python test path.  Native release lanes
build the extension and run this file explicitly with both forced-native and fail-closed verify
sessions.  Verify mode executes the Rust and Python sessions over the same compiled ontology and
compares their backend-neutral results before the public facade maps them back to OWL values.
"""

# SPDX-License-Identifier: LGPL-3.0-or-later

from __future__ import annotations

import random
from collections.abc import Iterator
from pathlib import Path

import pyowl_core
import pyowl_core.model as owl
import pytest

from pyhermit import InconsistentOntologyError, Reasoner, ReasonerConfig

pytest.importorskip("pyhermit._native")

OPTIONS = pyowl_core.LoadOptions(
    imports=pyowl_core.ImportPolicy.IGNORE,
    backend=pyowl_core.BackendPreference.PYTHON,
)
BASE = "urn:test:wpr4-differential#"
REFERENCE_INPUTS = Path(__file__).parents[1] / "data" / "reference" / "inputs"


@pytest.fixture(params=("native", "verify"))
def backend(request: pytest.FixtureRequest) -> str:
    return str(request.param)


def functional(*body: str) -> bytes:
    return (
        f"Prefix(:=<{BASE}>) "
        "Prefix(owl:=<http://www.w3.org/2002/07/owl#>) "
        "Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>) "
        f"Ontology(<{BASE[:-1]}> " + " ".join(body) + ")"
    ).encode()


def reasoner(source: bytes | Path, backend: str) -> Reasoner:
    return Reasoner(
        source,
        config=ReasonerConfig(backend=backend),
        load_options=OPTIONS,
    )


def cls(local: str) -> owl.Class:
    return owl.Class(owl.IRI(f"{BASE}{local}"))


def individual(local: str) -> owl.NamedIndividual:
    return owl.NamedIndividual(owl.IRI(f"{BASE}{local}"))


def object_property(local: str) -> owl.ObjectProperty:
    return owl.ObjectProperty(owl.IRI(f"{BASE}{local}"))


def data_property(local: str) -> owl.DataProperty:
    return owl.DataProperty(owl.IRI(f"{BASE}{local}"))


@pytest.mark.parametrize(
    ("fixture_name", "expected"),
    (
        ("empty.ofn", True),
        ("inconsistent.ofn", False),
        ("builtins.ofn", True),
    ),
)
def test_committed_hermit_black_box_goldens(
    backend: str,
    fixture_name: str,
    expected: bool,
) -> None:
    """Re-run every committed HermiT consistency golden through each complete backend."""

    with reasoner(REFERENCE_INPUTS / fixture_name, backend) as selected:
        assert selected.is_consistent() is expected
        if fixture_name == "builtins.ofn":
            hierarchy = selected.class_hierarchy()
            assert any(len(node) == 2 for node in hierarchy.nodes)


def test_classification_and_realization_cover_all_public_answer_tables(backend: str) -> None:
    source = functional(
        "Declaration(Class(:A))",
        "Declaration(Class(:B))",
        "Declaration(Class(:C))",
        "Declaration(Class(:D))",
        "EquivalentClasses(:B :C)",
        "SubClassOf(:A :B)",
        "DisjointClasses(:C :D)",
        "Declaration(ObjectProperty(:p))",
        "Declaration(ObjectProperty(:q))",
        "Declaration(ObjectProperty(:qInverse))",
        "SubObjectPropertyOf(:p :q)",
        "InverseObjectProperties(:q :qInverse)",
        "ObjectPropertyDomain(:q :B)",
        "ObjectPropertyRange(:q :D)",
        "Declaration(DataProperty(:age))",
        "Declaration(DataProperty(:measurement))",
        "SubDataPropertyOf(:age :measurement)",
        "DataPropertyDomain(:age :B)",
        "DataPropertyRange(:age xsd:integer)",
        "Declaration(NamedIndividual(:i))",
        "Declaration(NamedIndividual(:j))",
        "Declaration(NamedIndividual(:other))",
        "ClassAssertion(:A :i)",
        "ObjectPropertyAssertion(:p :i :j)",
        'DataPropertyAssertion(:age :i "01"^^xsd:integer)',
        "DifferentIndividuals(:i :other)",
    )
    a, b, c, d = (cls(local) for local in ("A", "B", "C", "D"))
    i, j, other = (individual(local) for local in ("i", "j", "other"))
    p, q, inverse = (object_property(local) for local in ("p", "q", "qInverse"))
    age, measurement = (data_property(local) for local in ("age", "measurement"))
    literal = owl.Literal(
        "01",
        owl.Datatype(owl.IRI("http://www.w3.org/2001/XMLSchema#integer")),
    )

    with reasoner(source, backend) as selected:
        assert selected.is_consistent()
        assert selected.is_subclass(a, c)
        assert selected.equivalent_classes(b) == frozenset((b, c))
        assert d in set().union(*selected.disjoint_classes(c))
        assert selected.superclasses(a, direct=True) == frozenset((frozenset((b, c)),))
        assert selected.object_property_hierarchy().nodes
        assert q in set().union(*selected.super_object_properties(p))
        assert inverse in selected.inverse_object_properties(q)
        assert b in set().union(*selected.object_property_domains(q))
        assert d in set().union(*selected.object_property_ranges(q))
        assert selected.data_property_hierarchy().nodes
        assert measurement in set().union(*selected.super_data_properties(age))
        assert b in set().union(*selected.data_property_domains(age))
        assert b in set().union(*selected.types(i))
        assert i in selected.instances(c)
        assert j in selected.object_property_values(i, q)
        assert i in selected.object_property_values(j, inverse)
        assert selected.has_object_property_relationship(i, q, j)
        assert literal in selected.data_property_values(i, measurement)
        assert selected.has_data_property_relationship(i, age, literal)
        assert other in selected.different_individuals(i)


def test_nondeterministic_query_overlay_blocking_and_cardinality_recovery(
    backend: str,
) -> None:
    source = functional(
        "Declaration(Class(:Choice))",
        "Declaration(Class(:Left))",
        "Declaration(Class(:Right))",
        "DisjointClasses(:Left :Right)",
        "EquivalentClasses(:Choice ObjectUnionOf(:Left :Right))",
        "Declaration(Class(:Loop))",
        "Declaration(ObjectProperty(:p))",
        "EquivalentClasses(:Loop ObjectSomeValuesFrom(:p :Loop))",
        "Declaration(NamedIndividual(:root))",
        "Declaration(NamedIndividual(:leftValue))",
        "Declaration(NamedIndividual(:rightValue))",
        "ClassAssertion(:Choice :root)",
        "ClassAssertion(:Loop :root)",
        "ClassAssertion(ObjectComplementOf(:Left) :root)",
        "ClassAssertion(ObjectMaxCardinality(1 :p owl:Thing) :root)",
        "ObjectPropertyAssertion(:p :root :leftValue)",
        "ObjectPropertyAssertion(:p :root :rightValue)",
    )
    root = individual("root")
    left_value = individual("leftValue")
    right_value = individual("rightValue")
    left = cls("Left")
    right = cls("Right")

    with reasoner(source, backend) as selected:
        # The first check leaves a live nondeterministic choice in its model.  Repeated checks and
        # temporary query overlays must still start from the immutable permanent program.
        assert selected.is_consistent()
        assert selected.is_consistent()
        assert not selected.entails(owl.ClassAssertion(left, root))
        assert selected.entails(owl.ClassAssertion(right, root))
        assert selected.same_individuals(left_value) == frozenset((left_value, right_value))
        assert selected.class_hierarchy().nodes
        assert selected.is_consistent()


def test_role_chains_transitivity_inverses_and_equality_substitution(backend: str) -> None:
    source = functional(
        "Declaration(ObjectProperty(:p))",
        "Declaration(ObjectProperty(:pInverse))",
        "Declaration(ObjectProperty(:r))",
        "Declaration(ObjectProperty(:s))",
        "Declaration(ObjectProperty(:t))",
        "TransitiveObjectProperty(:p)",
        "InverseObjectProperties(:p :pInverse)",
        "SubObjectPropertyOf(ObjectPropertyChain(:r :s) :t)",
        "Declaration(NamedIndividual(:a))",
        "Declaration(NamedIndividual(:b))",
        "Declaration(NamedIndividual(:c))",
        "Declaration(NamedIndividual(:alias))",
        "SameIndividual(:a :alias)",
        "ObjectPropertyAssertion(:p :a :b)",
        "ObjectPropertyAssertion(:p :b :c)",
        "ObjectPropertyAssertion(:r :alias :b)",
        "ObjectPropertyAssertion(:s :b :c)",
    )
    a, _b, c, alias = (individual(local) for local in ("a", "b", "c", "alias"))
    p, p_inverse, t = (object_property(local) for local in ("p", "pInverse", "t"))

    with reasoner(source, backend) as selected:
        assert selected.has_object_property_relationship(a, p, c)
        assert selected.has_object_property_relationship(c, p_inverse, a)
        assert selected.has_object_property_relationship(a, t, c)
        assert selected.has_object_property_relationship(alias, t, c)
        assert c in selected.object_property_values(a, p)
        assert a in selected.object_property_values(c, p_inverse)
        assert selected.same_individuals(a) == frozenset((a, alias))
        instances = selected.object_property_instances(t)
        assert c in instances[a]
        assert c in instances[alias]


def _permuted_chain_sources() -> Iterator[bytes]:
    declarations = [f"Declaration(Class(:C{index}))" for index in range(24)]
    links = [f"SubClassOf(:C{index} :C{index + 1})" for index in range(23)]
    assertions = [
        "Declaration(NamedIndividual(:generated))",
        "ClassAssertion(:C0 :generated)",
    ]
    axioms = declarations + links + assertions
    for seed in (0x4845524D, 0x4954, 0x57505234):
        shuffled = list(axioms)
        random.Random(seed).shuffle(shuffled)
        # Structural duplicate removal is a required metamorphic relation.  Add only duplicates
        # whose removal cannot change the ontology signature or its direct-semantics answers.
        shuffled.extend((links[3], links[11], declarations[7]))
        yield functional(*shuffled)


def test_generated_permutation_duplicate_and_query_campaign(backend: str) -> None:
    hierarchies = []
    generated = individual("generated")
    for source in _permuted_chain_sources():
        with reasoner(source, backend) as selected:
            assert selected.is_consistent()
            hierarchies.append(selected.class_hierarchy())
            for index in range(1, 24):
                assert selected.is_subclass(cls("C0"), cls(f"C{index}"))
                assert cls(f"C{index}") in set().union(*selected.types(generated))
            for index in range(1, 24):
                assert not selected.is_subclass(cls(f"C{index}"), cls("C0"))
    assert hierarchies[0] == hierarchies[1] == hierarchies[2]


def test_inconsistent_failures_are_exact_and_do_not_escape_as_results(backend: str) -> None:
    source = functional(
        "Declaration(Class(:A))",
        "Declaration(NamedIndividual(:i))",
        "ClassAssertion(:A :i)",
        "ClassAssertion(ObjectComplementOf(:A) :i)",
    )
    with reasoner(source, backend) as selected:
        assert not selected.is_consistent()
        for operation in (
            selected.class_hierarchy,
            lambda: selected.types(individual("i")),
            lambda: selected.instances(cls("A")),
        ):
            with pytest.raises(InconsistentOntologyError) as captured:
                operation()
            assert captured.value.code == "INCONSISTENT_ONTOLOGY"
