"""Production PyO3 classification parity, lifecycle, and cache tests."""

# SPDX-License-Identifier: LGPL-3.0-or-later

from __future__ import annotations

import pyowl_core
import pytest

import pyhermit._native as native
from pyhermit import Reasoner, ReasonerConfig
from pyhermit.backends.native_events import decode_events
from pyhermit.backends.native_input import encode_config, encode_ontology
from pyhermit.backends.native_mapping import CompiledResultMapper
from pyhermit.backends.native_wire import decode_check, decode_hierarchy
from pyhermit.exceptions import (
    InconsistentOntologyError,
    ReasonerInterruptedError,
    ResourceLimitError,
)

OPTIONS = pyowl_core.LoadOptions(
    imports=pyowl_core.ImportPolicy.IGNORE,
    backend=pyowl_core.BackendPreference.PYTHON,
)


def functional(*body: str) -> bytes:
    return (
        "Prefix(:=<urn:test:native-classification#>) "
        "Prefix(owl:=<http://www.w3.org/2002/07/owl#>) "
        "Ontology(<urn:test:native-classification> " + " ".join(body) + ")"
    ).encode()


def native_runtime(
    source: bytes,
    *,
    cancellation: native.CancellationHandle | None = None,
    force_quasi_order: bool = False,
) -> tuple[Reasoner, native.NativeSession, CompiledResultMapper]:
    reference = Reasoner(
        source,
        config=ReasonerConfig(
            backend="python",
            force_quasi_order_classification=force_quasi_order,
        ),
        load_options=OPTIONS,
    )
    runtime = reference._runtime  # Native contract integration fixture.
    handle = native.CancellationHandle() if cancellation is None else cancellation
    session = native.create_session(
        encode_ontology(runtime.compiled),
        encode_config(
            ReasonerConfig(
                backend="native",
                force_quasi_order_classification=force_quasi_order,
            )
        ),
        handle,
    )
    mapper = CompiledResultMapper(
        runtime.program,
        signature=runtime.entailment.source_signature,
        source_literals=runtime.realization.source_literals,
    )
    return reference, session, mapper


@pytest.mark.parametrize("force_quasi_order", (False, True))
def test_three_native_taxonomies_match_python_and_commit_complete_cache_only(
    force_quasi_order: bool,
) -> None:
    reference, session, mapper = native_runtime(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:C))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "Declaration(DataProperty(:d))",
            "Declaration(DataProperty(:e))",
            "SubClassOf(:A ObjectSomeValuesFrom(:p owl:Thing))",
            "ObjectPropertyDomain(:p :B)",
            "SubClassOf(:B :C)",
            "SubObjectPropertyOf(:p :q)",
            "SubDataPropertyOf(:d :e)",
        ),
        force_quasi_order=force_quasi_order,
    )
    try:
        calls = (
            (
                session.classify_classes,
                mapper.class_hierarchy,
                reference.class_hierarchy,
            ),
            (
                session.classify_object_properties,
                mapper.object_property_hierarchy,
                reference.object_property_hierarchy,
            ),
            (
                session.classify_data_properties,
                mapper.data_property_hierarchy,
                reference.data_property_hierarchy,
            ),
        )
        for native_call, map_result, reference_call in calls:
            first_wire = native_call()
            first_events = decode_events(session.drain_events())
            second_wire = native_call()
            second_events = decode_events(session.drain_events())

            assert first_wire == second_wire
            assert map_result(decode_hierarchy(first_wire)) == reference_call()
            assert any(event.query_key is not None for event in first_events)
            assert all(event.query_key is None for event in second_events)

        # Every classification query is isolated and rolled back from the permanent tableau.
        assert decode_check(session.check(None)).satisfiable
    finally:
        session.close()
        reference.dispose()


def test_classification_rejects_inconsistent_ontology_with_public_error() -> None:
    reference, session, _mapper = native_runtime(
        functional(
            "Declaration(Class(:A))",
            "Declaration(NamedIndividual(:i))",
            "ClassAssertion(:A :i)",
            "ClassAssertion(ObjectComplementOf(:A) :i)",
        )
    )
    try:
        assert not reference.is_consistent()
        for method in (
            session.classify_classes,
            session.classify_object_properties,
            session.classify_data_properties,
        ):
            with pytest.raises(InconsistentOntologyError) as captured:
                method()
            assert captured.value.code == "INCONSISTENT_ONTOLOGY"
    finally:
        session.close()
        reference.dispose()


def test_classification_cancellation_and_resource_failure_leave_session_reusable() -> None:
    cancellation = native.CancellationHandle()
    reference, session, _mapper = native_runtime(
        functional("Declaration(Class(:A))"),
        cancellation=cancellation,
    )
    try:
        assert cancellation.interrupt("stop classification")
        with pytest.raises(ReasonerInterruptedError, match="stop classification"):
            session.classify_classes()

        cancellation.reset(max_memory_bytes=1)
        with pytest.raises(ResourceLimitError) as captured:
            session.classify_classes()
        assert captured.value.limit == "max_memory_bytes"

        cancellation.reset()
        assert decode_hierarchy(session.classify_classes()).nodes
        assert decode_check(session.check(None)).satisfiable
    finally:
        session.close()
        reference.dispose()
