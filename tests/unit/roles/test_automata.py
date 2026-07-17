from __future__ import annotations

import itertools
import random

import pytest
from pyowl_core import (
    IRI,
    Declaration,
    ObjectProperty,
    ObjectPropertyChain,
    SubObjectPropertyOf,
    TransitiveObjectProperty,
)

from pyhermit.roles import build_role_axiom_graph, inverse_object_role


def prop(name: str) -> ObjectProperty:
    return ObjectProperty(IRI(f"urn:test:{name}"))


def words(alphabet: tuple[ObjectProperty, ...], maximum: int):
    for length in range(1, maximum + 1):
        yield from itertools.product(alphabet, repeat=length)


def assert_oracle_parity(graph, targets, alphabet, maximum=4) -> None:
    for target in targets:
        for word in words(alphabet, maximum):
            assert graph.accepts(target, word) == graph.slow_accepts(target, word), (
                target,
                word,
            )


def test_chain_and_simple_subrole_language_is_exact() -> None:
    target = prop("target")
    first = prop("first")
    first_sub = prop("first-sub")
    second = prop("second")
    graph = build_role_axiom_graph(
        (
            SubObjectPropertyOf(first_sub, first),
            SubObjectPropertyOf(ObjectPropertyChain((first, second)), target),
        )
    )
    assert graph.accepts(target, (first, second))
    assert graph.accepts(target, (first_sub, second))
    assert not graph.accepts(target, (first,))
    assert_oracle_parity(graph, (target, first), (target, first, first_sub, second))


def test_transitivity_left_right_recursion_and_overlapping_prefixes() -> None:
    target = prop("target")
    left = prop("left")
    right = prop("right")
    alternate = prop("alternate")
    graph = build_role_axiom_graph(
        (
            TransitiveObjectProperty(target),
            SubObjectPropertyOf(ObjectPropertyChain((left, target)), target),
            SubObjectPropertyOf(ObjectPropertyChain((target, right)), target),
            SubObjectPropertyOf(ObjectPropertyChain((left, alternate)), target),
        )
    )
    for accepted in (
        (target,),
        (target, target),
        (left, target),
        (target, right),
        (left, target, right),
        (left, alternate),
        (left, alternate, target),
    ):
        assert graph.accepts(target, accepted)
    assert_oracle_parity(graph, (target,), (target, left, right, alternate), maximum=4)


def test_inverse_chain_automaton_is_the_mirrored_language() -> None:
    target = prop("target")
    first = prop("first")
    second = prop("second")
    graph = build_role_axiom_graph(
        (SubObjectPropertyOf(ObjectPropertyChain((first, second)), target),)
    )
    inverse_target = inverse_object_role(target)
    assert graph.accepts(
        inverse_target,
        (inverse_object_role(second), inverse_object_role(first)),
    )
    assert not graph.accepts(
        inverse_target,
        (inverse_object_role(first), inverse_object_role(second)),
    )


@pytest.mark.parametrize("seed", range(20))
def test_generated_regular_hierarchies_match_slow_word_oracle(seed: int) -> None:
    randomizer = random.Random(seed)
    properties = tuple(prop(f"p{index}") for index in range(5))
    axioms = [Declaration(property) for property in properties]
    for lower in range(4):
        if randomizer.randrange(2):
            axioms.append(SubObjectPropertyOf(properties[lower], properties[lower + 1]))
    for target in range(1, 5):
        if randomizer.randrange(2):
            chain = tuple(
                randomizer.choice(properties[:target]) for _ in range(randomizer.choice((2, 3)))
            )
            axioms.append(SubObjectPropertyOf(ObjectPropertyChain(chain), properties[target]))
    graph = build_role_axiom_graph(axioms)
    assert graph.regular
    assert_oracle_parity(graph, properties, properties, maximum=3)
