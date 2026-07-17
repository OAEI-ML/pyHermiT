from __future__ import annotations

import json
from collections import Counter
from pathlib import Path

import pyowl_core.model as owl

from pyhermit.clauses import PredicateKind, compile_normalized
from pyhermit.datatypes import XSD_INTEGER
from pyhermit.normalize import normalize_axioms

FINGERPRINT = "35" * 32
GOLDEN = Path(__file__).parents[2] / "data/clauses/java-semantic-shapes-v1.json"


def _kind_counts(program, atoms) -> dict[str, int]:  # type: ignore[no-untyped-def]
    return dict(
        sorted(
            Counter(
                program.predicates.predicate(atom.predicate_id).kind.value for atom in atoms
            ).items()
        )
    )


def test_pinned_java_qualified_at_most_shape_matches_semantic_projection() -> None:
    golden = json.loads(GOLDEN.read_text())["cases"]["qualified_at_most_2"]
    source = owl.Class(owl.IRI("urn:test:java-shape:source"))
    filler = owl.Class(owl.IRI("urn:test:java-shape:filler"))
    role = owl.ObjectProperty(owl.IRI("urn:test:java-shape:role"))
    program = compile_normalized(
        normalize_axioms(
            (owl.SubClassOf(source, owl.ObjectMaxCardinality(2, role, filler)),),
            logical_fingerprint=FINGERPRINT,
        )
    )
    clause = next(
        value
        for value in program.clauses
        if sum(
            program.predicates.predicate(atom.predicate_id).kind is PredicateKind.ANNOTATED_EQUALITY
            for atom in value.head
        )
        == 3
    )
    assert _kind_counts(program, clause.body) == golden["body_kind_counts"]
    assert _kind_counts(program, clause.head) == golden["head_kind_counts"]
    annotated = {
        program.predicates.predicate(atom.predicate_id)
        for atom in clause.head
        if program.predicates.predicate(atom.predicate_id).kind is PredicateKind.ANNOTATED_EQUALITY
    }
    assert len(annotated) == 1
    predicate = annotated.pop()
    assert predicate.cardinality == golden["annotated_equality_cardinality"]
    assert predicate.role_id is not None
    assert predicate.filler_predicate_id is not None


def test_pinned_java_key_shape_keeps_named_object_values_and_data_inequality() -> None:
    golden = json.loads(GOLDEN.read_text())["cases"]["has_key_object_and_data"]
    concept = owl.Class(owl.IRI("urn:test:java-shape:key-class"))
    object_role = owl.ObjectProperty(owl.IRI("urn:test:java-shape:key-object"))
    data_role = owl.DataProperty(owl.IRI("urn:test:java-shape:key-data"))
    integer = owl.Datatype(owl.IRI(XSD_INTEGER))
    program = compile_normalized(
        normalize_axioms(
            (
                owl.HasKey(
                    concept,
                    owl.CanonicalSet((object_role,)),
                    owl.CanonicalSet((data_role,)),
                ),
                owl.DataPropertyRange(data_role, integer),
            ),
            logical_fingerprint=FINGERPRINT,
        )
    )
    clause = next(
        value
        for value in program.clauses
        if PredicateKind.ORDERING_GUARD
        in {program.predicates.predicate(atom.predicate_id).kind for atom in value.body}
        and PredicateKind.INEQUALITY
        in {program.predicates.predicate(atom.predicate_id).kind for atom in value.head}
    )
    assert _kind_counts(program, clause.body) == golden["body_kind_counts"]
    assert _kind_counts(program, clause.head) == golden["head_kind_counts"]


def test_java_shape_golden_is_pinned_to_the_reviewed_reference() -> None:
    golden = json.loads(GOLDEN.read_text())
    assert golden["schema_version"] == "1.0"
    assert golden["reference"]["commit"] == ("37ec30aced32ac81ebecc5e33fad255ddefcb4c3")
