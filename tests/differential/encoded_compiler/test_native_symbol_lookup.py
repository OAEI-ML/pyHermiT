"""Opaque native symbol owners preserve facade answers without eager Python domains."""

# SPDX-License-Identifier: LGPL-3.0-or-later
from __future__ import annotations

import pyowl_core.model as owl
import pytest
from tests.differential.encoded_compiler.test_permanent_program_assembly import (
    _direct_lifecycle_session,
    _direct_snapshot,
)

from pyhermit import Reasoner, ReasonerConfig
from pyhermit.backends import native_context
from pyhermit.config import BackendName
from pyhermit.exceptions import BackendMismatchError, DisposedReasonerError


def test_native_context_matches_legacy_domains_and_owner_lifetime() -> None:
    session = _direct_lifecycle_session(_direct_snapshot())
    try:
        owner = session._encoded_service_symbols_v1()
        legacy = native_context.decode_service_context(
            session._encoded_service_context_v1(), query_scope_digest="1" * 64
        )
        actual = native_context.native_service_context(owner, query_scope_digest="1" * 64)
        assert actual.compiler_digest == legacy.compiler_digest
        assert actual.permanent_program_sha256 == legacy.permanent_program_sha256
        assert frozenset(actual.source_signature) == legacy.source_signature
        assert tuple(actual.source_literals) == legacy.source_literals
        for name in (
            "class_ids",
            "object_property_ids",
            "data_property_ids",
            "individual_ids",
            "source_literal_ids",
        ):
            assert dict(getattr(actual, name)) == dict(getattr(legacy, name))
        assert actual.native_index_bytes > 0
        with pytest.raises(BackendMismatchError):
            native_context.native_service_context(object(), query_scope_digest="1" * 64)
    finally:
        session.close()
    with pytest.raises(DisposedReasonerError):
        owner.count("class")


def test_native_facade_initialization_avoids_eager_signature_and_domain_enumeration(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    snapshot = _direct_snapshot()

    def forbidden(*args: object, **kwargs: object) -> object:
        raise AssertionError("eager Python symbol traversal")

    with monkeypatch.context() as patch:
        patch.setattr(native_context._NativeSignature, "__iter__", forbidden)
        patch.setattr(native_context._NativeDomainMapping, "__iter__", forbidden)
        patch.setattr(native_context, "decode_service_context", forbidden)
        patch.setattr(type(snapshot), "origin_index", property(forbidden))
        with Reasoner(snapshot, config=ReasonerConfig(backend=BackendName.NATIVE)) as reasoner:
            assert reasoner.is_consistent()
            diagnostics = reasoner.diagnostics()
            assert diagnostics["native_symbol_index"]
            assert diagnostics["python_symbol_validation_rows"] == 0
            index_bytes = diagnostics["native_symbol_index_bytes"]
            assert isinstance(index_bytes, int) and index_bytes > 0
    with Reasoner(snapshot, config=ReasonerConfig(backend=BackendName.NATIVE)) as reasoner:
        a = owl.Class(owl.IRI("urn:test:permanent#A"))
        b = owl.Class(owl.IRI("urn:test:permanent#B"))
        assert reasoner.is_subclass(a, b)
        assert a in set().union(*reasoner.subclasses(b))
        assert reasoner.class_hierarchy().nodes
