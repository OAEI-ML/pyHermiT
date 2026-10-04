"""Configurable native lookup limits preserve exact answers and cooperative guards."""

from __future__ import annotations

import struct

import pyowl_core.model as owl
import pytest
from tests.differential.encoded_compiler.test_permanent_program_assembly import (
    _compiled,
    _direct_lifecycle_session,
    _direct_snapshot,
)

import pyhermit._native as native
from pyhermit import Reasoner, ReasonerConfig
from pyhermit.backends import native_input
from pyhermit.backends.native_context import native_service_context
from pyhermit.exceptions import (
    BackendMismatchError,
    ReasonerInterruptedError,
    ResourceLimitError,
)


def test_explicit_index_limit_has_exact_boundary_and_preserves_public_answers() -> None:
    snapshot = _direct_snapshot()
    a = owl.Class(owl.IRI("urn:test:permanent#A"))
    b = owl.Class(owl.IRI("urn:test:permanent#B"))
    with Reasoner(snapshot, config=ReasonerConfig(backend="native")) as reasoner:
        required = int(reasoner.diagnostics()["native_symbol_index_bytes"])
        expected = (
            reasoner.is_consistent(),
            reasoner.is_subclass(a, b),
            reasoner.class_hierarchy(),
        )
    assert required > 1
    with pytest.raises(ResourceLimitError) as caught:
        Reasoner(
            snapshot,
            config=ReasonerConfig(
                backend="native",
                max_native_symbol_index_bytes=required - 1,
            ),
        )
    assert caught.value.context["limit"] == "native_symbol_index_bytes"
    assert int(caught.value.context["allowed"]) == required - 1
    assert int(caught.value.context["observed"]) == required
    for maximum in (required, 128 * 1024 * 1024, (1 << 64) - 1):
        with Reasoner(
            snapshot,
            config=ReasonerConfig(
                backend="native",
                max_native_symbol_index_bytes=maximum,
            ),
        ) as reasoner:
            assert reasoner.diagnostics()["native_symbol_index_bytes"] == required
            assert (
                reasoner.is_consistent(),
                reasoner.is_subclass(a, b),
                reasoner.class_hierarchy(),
            ) == expected


def test_configured_direct_index_preserves_every_public_domain_mapping() -> None:
    snapshot = _direct_snapshot()
    contexts = []
    sessions = []
    try:
        for maximum in (None, 128 * 1024 * 1024):
            session = _direct_lifecycle_session(
                snapshot, config=ReasonerConfig(max_native_symbol_index_bytes=maximum)
            )
            sessions.append(session)
            contexts.append(
                native_service_context(
                    session._encoded_service_symbols_v1(), query_scope_digest="1" * 64
                )
            )
        baseline, configured = contexts
        assert configured.permanent_program_sha256 == baseline.permanent_program_sha256
        assert frozenset(configured.source_signature) == frozenset(baseline.source_signature)
        assert tuple(configured.source_literals) == tuple(baseline.source_literals)
        for name in (
            "class_ids",
            "object_property_ids",
            "data_property_ids",
            "individual_ids",
            "source_literal_ids",
        ):
            assert dict(getattr(configured, name)) == dict(getattr(baseline, name))
    finally:
        for session in sessions:
            session.close()


@pytest.mark.parametrize("cached", [False, True])
def test_global_memory_and_cancellation_still_guard_native_index(cached: bool) -> None:
    handle = native.CancellationHandle()
    session = _direct_lifecycle_session(
        _direct_snapshot(),
        cancellation=handle,
        config=ReasonerConfig(max_native_symbol_index_bytes=(1 << 64) - 1),
    )
    try:
        if cached:
            session._encoded_service_symbols_v1()
        handle.reset(max_memory_bytes=1)
        with pytest.raises(ResourceLimitError) as caught:
            session._encoded_service_symbols_v1()
        assert caught.value.context["limit"] == "max_memory_bytes"
        handle.reset()
        handle.interrupt("stop index construction or cached reuse")
        with pytest.raises(ReasonerInterruptedError):
            session._encoded_service_symbols_v1()
        handle.reset()
        assert session._encoded_service_symbols_v1().count("class") > 0
    finally:
        session.close()


@pytest.mark.parametrize("values", [(), (0,), (1, 2)])
def test_native_decoder_rejects_nonpositive_or_nonsingleton_limit_section(
    values: tuple[int, ...],
) -> None:
    baseline = native_input.encode_config(ReasonerConfig())
    offset, length = struct.unpack_from("<QQ", baseline, native_input.HEADER_SIZE + 8)
    malformed = native_input._document(
        native_input.DocumentKind.CONFIG,
        [
            native_input._Section(
                native_input.SectionKind.CONFIG, 1, baseline[offset : offset + length]
            ),
            native_input._Section(
                native_input.SectionKind.NATIVE_SYMBOL_INDEX_LIMIT,
                len(values),
                b"".join(struct.pack("<Q", value) for value in values),
            ),
        ],
    )
    with pytest.raises(BackendMismatchError, match="native symbol index limit"):
        native.create_session(
            native_input.encode_ontology(_compiled(_direct_snapshot())),
            malformed,
            native.CancellationHandle(),
        )
