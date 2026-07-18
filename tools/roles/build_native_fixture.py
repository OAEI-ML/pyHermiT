"""Build the deterministic WPR3 Python/Rust role-language fixture.

SPDX-License-Identifier: LGPL-3.0-or-later
"""

from __future__ import annotations

import argparse
import itertools
import json
import random
from pathlib import Path
from typing import Any

from pyowl_core import (
    IRI,
    ObjectProperty,
    ObjectPropertyChain,
    SubObjectPropertyOf,
    TransitiveObjectProperty,
)

from pyhermit.roles import build_role_axiom_graph

DEFAULT_OUTPUT = Path("tests/data/roles/wpr3-role-automata-v1.json")
GENERATOR_SEED = 0x5750_5233


def _property(name: str) -> ObjectProperty:
    return ObjectProperty(IRI(f"urn:pyhermit:wpr3:{name}"))


def build_fixture() -> dict[str, Any]:
    """Return a bounded corpus evaluated by the authoritative Python NFA runtime."""

    target = _property("target")
    left = _property("left")
    right = _property("right")
    alternate = _property("alternate")
    left_sub = _property("left-sub")
    graph = build_role_axiom_graph(
        (
            SubObjectPropertyOf(left_sub, left),
            TransitiveObjectProperty(target),
            SubObjectPropertyOf(ObjectPropertyChain((left, target)), target),
            SubObjectPropertyOf(ObjectPropertyChain((target, right)), target),
            SubObjectPropertyOf(ObjectPropertyChain((left, alternate)), target),
        )
    )
    alphabet = tuple(range(len(graph.object_roles)))
    words: set[tuple[int, ...]] = {()}
    for length in (1, 2):
        words.update(itertools.product(alphabet, repeat=length))
    randomizer = random.Random(GENERATOR_SEED)
    for _ in range(512):
        length = randomizer.randint(3, 6)
        words.add(tuple(randomizer.choice(alphabet) for _ in range(length)))
    word_corpus = tuple(sorted(words, key=lambda value: (len(value), value)))

    automata = []
    cases: list[dict[str, Any]] = []
    for component, automaton in sorted(graph.automata.items()):
        automata.append(
            {
                "component_id": component,
                "final_states": list(automaton.final_states),
                "initial_state": automaton.initial_state,
                "state_count": automaton.state_count,
                "transitions": [
                    {
                        "role_id": transition.role_id,
                        "source_state": transition.source_state,
                        "target_state": transition.target_state,
                    }
                    for transition in automaton.transitions
                ],
            }
        )
        cases.extend(
            {
                "accepts": automaton.accepts_ids(word),
                "component_id": component,
                "word": list(word),
            }
            for word in word_corpus
        )
    target_by_component = {
        component.component_id: graph.object_roles[component.member_role_ids[0]]
        for component in graph.object_components
    }
    propagation_cases = [
        {
            "accepted_components": [
                component
                for component in sorted(graph.automata)
                if graph.accepts(
                    target_by_component[component],
                    tuple(graph.object_roles[role_id] for role_id in word),
                )
            ],
            "word": list(word),
        }
        for word in word_corpus
    ]
    return {
        "automata": automata,
        "bottom_role_id": graph.bottom_object_role_id,
        "cases": cases,
        "generator_seed": GENERATOR_SEED,
        "inverse_role_ids": list(graph.inverse_role_ids),
        "propagation_cases": propagation_cases,
        "role_count": len(graph.object_roles),
        "schema_version": 1,
        "top_role_id": graph.top_object_role_id,
        "word_count_per_automaton": len(word_corpus),
    }


def canonical_bytes() -> bytes:
    return (
        json.dumps(build_fixture(), ensure_ascii=False, separators=(",", ":"), sort_keys=True)
        + "\n"
    ).encode()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    arguments = parser.parse_args()
    generated = canonical_bytes()
    if arguments.check:
        return 0 if arguments.output.read_bytes() == generated else 1
    arguments.output.parent.mkdir(parents=True, exist_ok=True)
    arguments.output.write_bytes(generated)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
