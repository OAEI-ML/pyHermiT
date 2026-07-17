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
from pyhermit.exceptions import (
    BackendMismatchError,
    BackendVersionError,
    DisposedReasonerError,
    FeatureNotImplementedError,
)

from ._builder import (
    METADATA,
    ONTOLOGY,
    OPTIONAL_SECTION,
    SectionSpec,
    build_document,
    metadata_payload,
    rehash,
    valid_documents,
)


def make_session() -> native.NativeSession:
    ontology, config = valid_documents()
    return native.create_session(ontology, config, native.CancellationHandle())


def test_private_abi_handshake_is_versioned_and_does_not_claim_reasoning() -> None:
    native.self_test()
    assert native.ABI_VERSION == 1
    assert native.IR_SCHEMA_VERSION == 1
    assert native.STATE_TRACE_VERSION == 1
    assert native.FEATURES == (
        "abi3-py310",
        "wire-v1",
        "state-trace-v1",
        "cancellable-mock-work",
    )
    assert "full_reasoner" not in native.FEATURES
    assert API_VERSION == (0, 1)
    assert MODEL_SCHEMA_VERSION == 1
    assert WIRE_FORMAT_VERSION == (1, 0)
    assert ADAPTER_PROTOCOL_VERSION == 1


def test_session_owns_wire_bytes_and_exposes_only_core_fingerprint() -> None:
    ontology, config = valid_documents()
    ontology_references = sys.getrefcount(ontology)
    config_references = sys.getrefcount(config)
    session = native.create_session(ontology, config, native.CancellationHandle())
    assert sys.getrefcount(ontology) == ontology_references
    assert sys.getrefcount(config) == config_references
    assert session.ontology_fingerprint == "11" * 32
    session.close()
    session.close()
    with pytest.raises(DisposedReasonerError):
        _ = session.ontology_fingerprint


@pytest.mark.parametrize(
    ("method", "feature_id"),
    (
        (lambda session: session.check(None), "full_reasoner"),
        (lambda session: session.check_many([b"query"]), "full_reasoner"),
        (lambda session: session.classify_classes(), "classification"),
        (lambda session: session.classify_object_properties(), "classification"),
        (lambda session: session.classify_data_properties(), "classification"),
        (lambda session: session.realize(), "realization"),
        (lambda session: session.apply_delta(b"delta"), "incremental_updates"),
    ),
)
def test_forced_native_semantic_calls_raise_a_typed_feature_error(
    method: object,
    feature_id: str,
) -> None:
    session = make_session()
    with pytest.raises(FeatureNotImplementedError) as captured:
        method(session)  # type: ignore[operator]
    assert captured.value.feature_id == feature_id
    session.close()


def test_unknown_optional_sections_are_ignored_but_required_ones_fail() -> None:
    optional = build_document(
        ONTOLOGY,
        (
            SectionSpec(METADATA, metadata_payload(), 1),
            SectionSpec(60_000, b"future", 1, flags=OPTIONAL_SECTION),
        ),
    )
    _, config = valid_documents()
    session = native.create_session(optional, config, native.CancellationHandle())
    assert session.ontology_fingerprint == "11" * 32
    session.close()

    required = build_document(
        ONTOLOGY,
        (
            SectionSpec(METADATA, metadata_payload(), 1),
            SectionSpec(60_000, b"future", 1),
        ),
    )
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
    struct.pack_into("<I", bad_count, 72 + 24, 2)
    with pytest.raises(BackendMismatchError):
        native.create_session(rehash(bad_count), config, native.CancellationHandle())

    bad_offset = bytearray(ontology)
    struct.pack_into("<Q", bad_offset, 72 + 8, (1 << 64) - 1)
    with pytest.raises(BackendMismatchError):
        native.create_session(rehash(bad_offset), config, native.CancellationHandle())

    two_sections = build_document(
        ONTOLOGY,
        (
            SectionSpec(METADATA, metadata_payload(), 1),
            SectionSpec(2, b"names", 5),
        ),
    )
    overlap = bytearray(two_sections)
    first_offset = struct.unpack_from("<Q", overlap, 72 + 8)[0]
    struct.pack_into("<Q", overlap, 72 + 32 + 8, first_offset)
    with pytest.raises(BackendMismatchError):
        native.create_session(rehash(overlap), config, native.CancellationHandle())

    padded = build_document(
        ONTOLOGY,
        (
            SectionSpec(2, b"x", 1),
            SectionSpec(METADATA, metadata_payload(), 1),
        ),
    )
    nonzero_padding = bytearray(padded)
    string_offset = struct.unpack_from("<Q", nonzero_padding, 72 + 8)[0]
    nonzero_padding[string_offset + 1] = 1
    with pytest.raises(BackendMismatchError):
        native.create_session(rehash(nonzero_padding), config, native.CancellationHandle())

    trailing = bytearray(ontology)
    trailing.append(0)
    struct.pack_into("<Q", trailing, 16, len(trailing))
    with pytest.raises(BackendMismatchError):
        native.create_session(rehash(trailing), config, native.CancellationHandle())

    wrong_string_count = build_document(
        ONTOLOGY,
        (
            SectionSpec(METADATA, metadata_payload(), 1),
            SectionSpec(2, b"ok", 1),
        ),
    )
    with pytest.raises(BackendMismatchError):
        native.create_session(wrong_string_count, config, native.CancellationHandle())

    invalid_symbol = struct.pack("<BBHIII", 0, 0, 0, 99, 2, 0)
    bad_reference = build_document(
        ONTOLOGY,
        (
            SectionSpec(METADATA, metadata_payload(), 1),
            SectionSpec(2, b"ok", 2),
            SectionSpec(3, invalid_symbol, 1),
        ),
    )
    with pytest.raises(BackendMismatchError):
        native.create_session(bad_reference, config, native.CancellationHandle())


def test_wrong_document_kind_and_zero_core_version_are_rejected() -> None:
    ontology, config = valid_documents()
    with pytest.raises(BackendMismatchError):
        native.create_session(config, config, native.CancellationHandle())

    metadata = bytearray(metadata_payload())
    struct.pack_into("<I", metadata, 132, 0)
    zero_version = build_document(ONTOLOGY, (SectionSpec(METADATA, bytes(metadata), 1),))
    with pytest.raises(BackendVersionError):
        native.create_session(zero_version, config, native.CancellationHandle())
    assert ontology != zero_version


def test_deterministic_corruption_sweep_never_panics_or_allocates_from_claims() -> None:
    ontology, config = valid_documents()
    randomizer = random.Random(0x4845524D4954)
    for _ in range(128):
        corrupt = bytearray(ontology)
        index = randomizer.randrange(len(corrupt))
        corrupt[index] ^= randomizer.randrange(1, 256)
        try:
            session = native.create_session(bytes(corrupt), config, native.CancellationHandle())
        except (BackendMismatchError, BackendVersionError):
            continue
        session.close()
