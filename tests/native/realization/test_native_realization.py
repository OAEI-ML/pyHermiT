"""Production PyO3 realization parity, cache, and recovery tests."""

# SPDX-License-Identifier: LGPL-3.0-or-later

from __future__ import annotations

import pyowl_core
import pyowl_core.model as owl
import pytest

import pyhermit._native as native
from pyhermit import Reasoner, ReasonerConfig
from pyhermit.backends.native_events import decode_events
from pyhermit.backends.native_input import encode_config, encode_ontology
from pyhermit.backends.native_mapping import CompiledResultMapper, MappedRealization
from pyhermit.backends.native_wire import decode_check, decode_realization
from pyhermit.exceptions import (
    InconsistentOntologyError,
    ReasonerInterruptedError,
    ResourceLimitError,
)

OPTIONS = pyowl_core.LoadOptions(
    imports=pyowl_core.ImportPolicy.IGNORE,
    backend=pyowl_core.BackendPreference.PYTHON,
)
BASE = "urn:test:native-realization#"


def functional(*body: str) -> bytes:
    return (
        f"Prefix(:=<{BASE}>) "
        "Prefix(owl:=<http://www.w3.org/2002/07/owl#>) "
        "Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>) "
        f"Ontology(<{BASE[:-1]}> " + " ".join(body) + ")"
    ).encode()


def native_runtime(
    source: bytes,
    *,
    cancellation: native.CancellationHandle | None = None,
) -> tuple[Reasoner, native.NativeSession, CompiledResultMapper]:
    reference = Reasoner(
        source,
        config=ReasonerConfig(backend="python"),
        load_options=OPTIONS,
    )
    runtime = reference._runtime  # Native contract integration fixture.
    handle = native.CancellationHandle() if cancellation is None else cancellation
    session = native.create_session(
        encode_ontology(runtime.compiled),
        encode_config(ReasonerConfig(backend="native")),
        handle,
    )
    mapper = CompiledResultMapper(
        runtime.program,
        signature=runtime.entailment.source_signature,
        source_literals=runtime.realization.source_literals,
    )
    return reference, session, mapper


def entity(local: str) -> owl.IRI:
    return owl.IRI(f"{BASE}{local}")


def individual(local: str) -> owl.NamedIndividual:
    return owl.NamedIndividual(entity(local))


def object_property(local: str) -> owl.ObjectProperty:
    return owl.ObjectProperty(entity(local))


def data_property(local: str) -> owl.DataProperty:
    return owl.DataProperty(entity(local))


def _group_id(value: MappedRealization, member: owl.NamedIndividual) -> int:
    return next(index for index, group in enumerate(value.same_as) if member in group)


def test_native_realization_matches_python_for_every_answer_table_and_caches() -> None:
    reference, session, mapper = native_runtime(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "SubClassOf(:A :B)",
            "Declaration(ObjectProperty(:p))",
            "Declaration(DataProperty(:d))",
            "Declaration(NamedIndividual(:i))",
            "Declaration(NamedIndividual(:j))",
            "Declaration(NamedIndividual(:k))",
            "SameIndividual(:i :j)",
            "DifferentIndividuals(:i :k)",
            "ClassAssertion(:A :i)",
            "ObjectPropertyAssertion(:p :i :k)",
            'DataPropertyAssertion(:d :i "1"^^xsd:integer)',
        )
    )
    i, j, k = (individual(local) for local in ("i", "j", "k"))
    p = object_property("p")
    d = data_property("d")
    try:
        first_wire = session.realize()
        first_events = decode_events(session.drain_events())
        second_wire = session.realize()
        second_events = decode_events(session.drain_events())
        assert first_wire == second_wire
        assert any(event.query_key is not None for event in first_events)
        assert not second_events

        hierarchy = reference.class_hierarchy()
        realized = mapper.realization(decode_realization(first_wire), hierarchy)
        i_group = _group_id(realized, i)
        k_group = _group_id(realized, k)
        assert realized.same_as[i_group] == reference.same_individuals(i) == frozenset((i, j))
        assert realized.same_as[k_group] == reference.same_individuals(k) == frozenset((k,))

        direct_nodes = dict(realized.direct_types)[i_group]
        assert frozenset(hierarchy.nodes[node] for node in direct_nodes) == reference.types(
            i, direct=True
        )

        object_rows = {
            (subject, property_): frozenset(
                member for target in targets for member in realized.same_as[target]
            )
            for subject, property_, targets in realized.object_targets
        }
        assert object_rows[(i_group, p)] == reference.object_property_values(i, p)
        inverse = owl.inverse_property(p)
        assert object_rows[(k_group, inverse)] == reference.object_property_values(k, inverse)

        data_rows = {
            (subject, property_): values
            for subject, property_, values in realized.data_targets
        }
        assert data_rows[(i_group, d)] == reference.data_property_values(i, d)
        assert (min(i_group, k_group), max(i_group, k_group)) in realized.different_from
        assert reference.different_individuals(i) == frozenset((k,))
        assert decode_check(session.check(None)).satisfiable
    finally:
        session.close()
        reference.dispose()


def test_functional_role_equality_is_reflected_in_native_same_as_partition() -> None:
    reference, session, mapper = native_runtime(
        functional(
            "Declaration(ObjectProperty(:p))",
            "FunctionalObjectProperty(:p)",
            "Declaration(NamedIndividual(:source))",
            "Declaration(NamedIndividual(:left))",
            "Declaration(NamedIndividual(:right))",
            "ObjectPropertyAssertion(:p :source :left)",
            "ObjectPropertyAssertion(:p :source :right)",
        )
    )
    left, right = (individual(local) for local in ("left", "right"))
    try:
        realized = mapper.realization(
            decode_realization(session.realize()), reference.class_hierarchy()
        )
        assert realized.same_as[_group_id(realized, left)] == frozenset((left, right))
        assert reference.same_individuals(left) == frozenset((left, right))
    finally:
        session.close()
        reference.dispose()


def test_realization_failure_is_typed_atomic_and_recoverable() -> None:
    cancellation = native.CancellationHandle()
    reference, session, mapper = native_runtime(
        functional(
            "Declaration(Class(:A))",
            "Declaration(NamedIndividual(:i))",
            "ClassAssertion(:A :i)",
        ),
        cancellation=cancellation,
    )
    try:
        assert cancellation.interrupt("stop realization")
        with pytest.raises(ReasonerInterruptedError, match="stop realization"):
            session.realize()

        cancellation.reset(max_memory_bytes=1)
        with pytest.raises(ResourceLimitError) as captured:
            session.realize()
        assert captured.value.limit == "max_memory_bytes"

        cancellation.reset()
        wire = session.realize()
        mapped = mapper.realization(decode_realization(wire), reference.class_hierarchy())
        assert mapped.same_as == (frozenset((individual("i"),)),)

        cancellation.reset(max_memory_bytes=1)
        with pytest.raises(ResourceLimitError):
            session.realize()
        cancellation.reset()
        assert session.realize() == wire
    finally:
        session.close()
        reference.dispose()


def test_realization_rejects_inconsistent_ontology() -> None:
    reference, session, _mapper = native_runtime(
        functional(
            "Declaration(Class(:A))",
            "Declaration(NamedIndividual(:i))",
            "ClassAssertion(:A :i)",
            "ClassAssertion(ObjectComplementOf(:A) :i)",
        )
    )
    try:
        with pytest.raises(InconsistentOntologyError) as captured:
            session.realize()
        assert captured.value.code == "INCONSISTENT_ONTOLOGY"
    finally:
        session.close()
        reference.dispose()


def test_ordinary_large_abox_does_not_generate_quadratic_same_as_queries() -> None:
    declarations = tuple(
        f"Declaration(NamedIndividual(:ordinary-{index}))" for index in range(250)
    )
    reference, session, _mapper = native_runtime(functional(*declarations))
    try:
        realized = decode_realization(session.realize())
        events = decode_events(session.drain_events())
        assert len(realized.same_as) == 250
        assert all(len(group) == 1 for group in realized.same_as)
        assert all(event.query_key is None for event in events)
    finally:
        session.close()
        reference.dispose()
