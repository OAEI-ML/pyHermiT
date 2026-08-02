"""Native ABI handshake, flat-wire validation, and semantic capability tests."""

# SPDX-License-Identifier: LGPL-3.0-or-later

from __future__ import annotations

import random
import struct
import sys

import pytest
from pyowl_core import (
    ADAPTER_PROTOCOL_VERSION,
    API_VERSION,
    MODEL_SCHEMA_VERSION,
    WIRE_FORMAT_VERSION,
)

import pyhermit._native as native
from pyhermit.backends.native_events import decode_events
from pyhermit.backends.native_wire import decode_check, decode_check_many
from pyhermit.exceptions import (
    BackendMismatchError,
    BackendVersionError,
    DisposedReasonerError,
    FeatureNotImplementedError,
    ResourceLimitError,
)

from ._builder import (
    ONTOLOGY_FINGERPRINT,
    append_unknown_section,
    directory_entry,
    first_padding_byte,
    rehash,
    section_offset,
    valid_documents,
    valid_query_documents,
)


def make_session() -> native.NativeSession:
    ontology, config = valid_documents()
    return native.create_session(ontology, config, native.CancellationHandle())


def test_private_abi_handshake_claims_only_completed_versioned_features() -> None:
    native.self_test()
    assert native.ABI_VERSION == 1
    assert native.IR_SCHEMA_VERSION == 1
    assert native.STATE_TRACE_VERSION == 1
    assert native.FEATURES == (
        "abi3-py310",
        "cancellable-mock-work",
        "classification",
        "encoded-structural-compiler-v2",
        "full_reasoner",
        "incremental_updates",
        "realization",
        "state-trace-v1",
        "wire-v1",
    )
    assert API_VERSION == (0, 2)
    assert MODEL_SCHEMA_VERSION == 2
    assert WIRE_FORMAT_VERSION == (1, 2)
    assert ADAPTER_PROTOCOL_VERSION == 1


def test_session_owns_wire_bytes_and_exposes_only_core_fingerprint() -> None:
    ontology, config = valid_documents()
    ontology_references = sys.getrefcount(ontology)
    config_references = sys.getrefcount(config)
    session = native.create_session(ontology, config, native.CancellationHandle())
    assert sys.getrefcount(ontology) == ontology_references
    assert sys.getrefcount(config) == config_references
    assert session.ontology_fingerprint == ONTOLOGY_FINGERPRINT
    session.close()
    session.close()
    with pytest.raises(DisposedReasonerError):
        _ = session.ontology_fingerprint


def test_rule_only_checks_use_the_transactional_scheduler_and_compact_wires() -> None:
    session = make_session()
    first = decode_check(session.check(None))
    second = decode_check(session.check(None))
    query, _rebuild = valid_query_documents()
    batch = decode_check_many(session.check_many([query]))

    assert first.satisfiable
    assert second.satisfiable == first.satisfiable
    assert len(batch) == 1
    assert batch[0].satisfiable
    events = decode_events(session.drain_events())
    assert [event.kind for event in events].count("operation_completed") == 3
    assert any(event.query_key is not None for event in events)
    assert decode_events(session.drain_events()) == ()
    session.close()


def test_query_wire_validation_and_rebuild_policy_fail_closed() -> None:
    session = make_session()
    with pytest.raises(BackendMismatchError):
        session.check_many([b"query"])
    _query, rebuild = valid_query_documents()
    with pytest.raises(FeatureNotImplementedError) as captured:
        session.check(rebuild)
    assert captured.value.feature_id == "query_rebuild"
    session.close()


def test_unknown_optional_sections_are_ignored_but_required_ones_fail() -> None:
    ontology, config = valid_documents()
    optional = append_unknown_section(ontology, optional=True)
    session = native.create_session(optional, config, native.CancellationHandle())
    assert session.ontology_fingerprint == ONTOLOGY_FINGERPRINT
    session.close()

    required = append_unknown_section(ontology, optional=False)
    with pytest.raises(BackendVersionError):
        native.create_session(required, config, native.CancellationHandle())


def test_corrupt_header_hash_count_offset_overlap_and_cross_reference_are_rejected() -> None:
    ontology, config = valid_documents()

    bad_magic = bytearray(ontology)
    bad_magic[0] ^= 0xFF
    with pytest.raises(BackendMismatchError):
        native.create_session(bytes(bad_magic), config, native.CancellationHandle())

    bad_schema = bytearray(ontology)
    struct.pack_into("<H", bad_schema, 8, 2)
    with pytest.raises(BackendVersionError):
        native.create_session(bytes(bad_schema), config, native.CancellationHandle())

    bad_hash = bytearray(ontology)
    bad_hash[-1] ^= 0xFF
    with pytest.raises(BackendMismatchError):
        native.create_session(bytes(bad_hash), config, native.CancellationHandle())

    bad_count = bytearray(ontology)
    metadata_entry = directory_entry(bad_count, 1)
    struct.pack_into("<I", bad_count, metadata_entry + 24, 2)
    with pytest.raises(BackendMismatchError):
        native.create_session(rehash(bad_count), config, native.CancellationHandle())

    bad_offset = bytearray(ontology)
    struct.pack_into("<Q", bad_offset, metadata_entry + 8, (1 << 64) - 1)
    with pytest.raises(BackendMismatchError):
        native.create_session(rehash(bad_offset), config, native.CancellationHandle())

    overlap = bytearray(ontology)
    first_offset = struct.unpack_from("<Q", overlap, 72 + 8)[0]
    struct.pack_into("<Q", overlap, 72 + 32 + 8, first_offset)
    with pytest.raises(BackendMismatchError):
        native.create_session(rehash(overlap), config, native.CancellationHandle())

    nonzero_padding = bytearray(ontology)
    nonzero_padding[first_padding_byte(nonzero_padding)] = 1
    with pytest.raises(BackendMismatchError):
        native.create_session(rehash(nonzero_padding), config, native.CancellationHandle())

    trailing = bytearray(ontology)
    trailing.append(0)
    struct.pack_into("<Q", trailing, 16, len(trailing))
    with pytest.raises(BackendMismatchError):
        native.create_session(rehash(trailing), config, native.CancellationHandle())

    wrong_string_count = bytearray(ontology)
    strings_entry = directory_entry(wrong_string_count, 2)
    string_count = struct.unpack_from("<I", wrong_string_count, strings_entry + 24)[0]
    struct.pack_into("<I", wrong_string_count, strings_entry + 24, string_count + 1)
    with pytest.raises(BackendMismatchError):
        native.create_session(rehash(wrong_string_count), config, native.CancellationHandle())


def test_wrong_document_kind_and_zero_core_version_are_rejected() -> None:
    ontology, config = valid_documents()
    with pytest.raises(BackendMismatchError):
        native.create_session(config, config, native.CancellationHandle())

    incompatible_version = bytearray(ontology)
    metadata_offset = section_offset(incompatible_version, 1)
    struct.pack_into("<H", incompatible_version, metadata_offset + 182, 0)
    with pytest.raises(BackendVersionError):
        native.create_session(rehash(incompatible_version), config, native.CancellationHandle())
    assert ontology != incompatible_version


def test_deterministic_corruption_sweep_never_panics_or_allocates_from_claims() -> None:
    ontology, config = valid_documents()
    randomizer = random.Random(0x4845524D4954)
    for _ in range(128):
        corrupt = bytearray(ontology)
        index = randomizer.randrange(len(corrupt))
        corrupt[index] ^= randomizer.randrange(1, 256)
        try:
            session = native.create_session(bytes(corrupt), config, native.CancellationHandle())
        except (BackendMismatchError, BackendVersionError, ResourceLimitError):
            continue
        session.close()
