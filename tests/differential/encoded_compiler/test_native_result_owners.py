"""Native result receipts preserve canonical answers without Python graph validation."""

# SPDX-License-Identifier: LGPL-3.0-or-later
from __future__ import annotations

from typing import Any, cast

import pyowl_core.model as owl
import pytest
from tests.differential.encoded_compiler.test_permanent_program_assembly import (
    _direct_lifecycle_session,
    _direct_snapshot,
)

from pyhermit.backends import native_context, native_results, native_wire
from pyhermit.backends.native_mapping import CompiledResultMapper
from pyhermit.backends.protocol import Hierarchy, HierarchyIds, RealizationIds
from pyhermit.exceptions import BackendMismatchError, DisposedReasonerError


def _mapper(session: Any) -> CompiledResultMapper:
    context = native_context.native_service_context(
        session._encoded_service_symbols_v1(), query_scope_digest="1" * 64
    )
    return CompiledResultMapper._from_native_domain_mappings(
        classes=context.class_ids,
        object_properties=context.object_property_ids,
        data_properties=context.data_property_ids,
        individuals=context.individual_ids,
        source_literals=context.source_literal_ids,
    )


def test_native_result_parity_without_python_domain_or_graph_validation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    session = _direct_lifecycle_session(_direct_snapshot())
    try:
        expected_classes = native_wire.decode_hierarchy(session.classify_classes())
        expected_objects = native_wire.decode_hierarchy(session.classify_object_properties())
        expected_data = native_wire.decode_hierarchy(session.classify_data_properties())
        expected_realization = native_wire.decode_realization(session.realize())
        mapper = _mapper(session)
        expected = (
            mapper.class_hierarchy(expected_classes),
            mapper.object_property_hierarchy(expected_objects),
            mapper.data_property_hierarchy(expected_data),
        )
        expected_mapped = mapper.realization(expected_realization, expected[0])

        def forbidden(*args: object, **kwargs: object) -> None:
            raise AssertionError("Python result validation or full-domain scan")

        monkeypatch.setattr(HierarchyIds, "__post_init__", forbidden)
        monkeypatch.setattr(RealizationIds, "__post_init__", forbidden)
        monkeypatch.setattr(Hierarchy, "__post_init__", forbidden)
        monkeypatch.setattr(native_context._NativeDomainMapping, "__iter__", forbidden)
        actual = []
        for domain, mapping, ids in (
            ("class", mapper.class_hierarchy, expected_classes),
            ("object_property", mapper.object_property_hierarchy, expected_objects),
            ("data_property", mapper.data_property_hierarchy, expected_data),
        ):
            result = native_results.hierarchy_ids(session._hierarchy_result_v1(domain))
            assert result == ids
            actual.append(mapping(result))
        assert tuple(actual) == expected
        realization = native_results.realization_ids(session._realization_result_v1())
        assert realization == expected_realization
        assert (
            mapper.realization(realization, cast(Hierarchy[owl.Class], actual[0]))
            == expected_mapped
        )
    finally:
        session.close()


def test_native_result_rejects_wrong_owner_domain_and_closed_session() -> None:
    left = _direct_lifecycle_session(_direct_snapshot())
    right = _direct_lifecycle_session(_direct_snapshot())
    owner = left._hierarchy_result_v1("class")
    try:
        result = native_results.hierarchy_ids(owner)
        with pytest.raises(BackendMismatchError, match="another program"):
            _mapper(right).class_hierarchy(result)
        with pytest.raises(BackendMismatchError, match="symbol domain"):
            _mapper(left).data_property_hierarchy(result)
        with pytest.raises(BackendMismatchError, match="native-issued"):
            native_results.hierarchy_ids(object())
        with pytest.raises(TypeError):
            type(owner)()
    finally:
        left.close()
        right.close()
    with pytest.raises(DisposedReasonerError):
        native_results.hierarchy_ids(owner)


def test_native_hierarchy_public_queries_avoid_python_reindexing(
    monkeypatch: pytest.MonkeyPatch,
) -> None:

    from pyhermit import Reasoner, ReasonerConfig
    from pyhermit.config import BackendName
    from pyhermit.hierarchy.model import HierarchyIndex
    from pyhermit.services.classification import ClassificationService

    snapshot = _direct_snapshot()
    with Reasoner(snapshot, config=ReasonerConfig(backend=BackendName.PYTHON)) as reasoner:
        expected = reasoner.class_hierarchy()

    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("Python hierarchy indexing or source enumeration")

    monkeypatch.setattr(HierarchyIndex, "__post_init__", forbidden)
    monkeypatch.setattr(ClassificationService, "_class_elements", forbidden)
    monkeypatch.setattr(native_context._NativeSignature, "__iter__", forbidden)
    with Reasoner(snapshot, config=ReasonerConfig(backend=BackendName.NATIVE)) as reasoner:
        actual = reasoner.class_hierarchy()
        assert actual == expected
        for node in range(len(actual.nodes)):
            assert actual.ancestors(node) == expected.ancestors(node)
            assert actual.descendants(node) == expected.descendants(node)
        a = owl.Class(owl.IRI("urn:test:permanent#A"))
        b = owl.Class(owl.IRI("urn:test:permanent#B"))
        assert reasoner.is_subclass(a, b)
        assert a in set().union(*reasoner.subclasses(b))
