"""Strict native event-wire decoding and hostile-input rejection."""

# SPDX-License-Identifier: LGPL-3.0-or-later

from __future__ import annotations

import hashlib
import struct

import pytest

from pyhermit.backends.native_events import (
    EVENT_HEADER_LENGTH,
    EVENT_MAGIC,
    EVENT_RECORD_LENGTH,
    decode_events,
)
from pyhermit.exceptions import BackendMismatchError

_HEADER = struct.Struct("<8sHHIQII32s")
_RECORD = struct.Struct("<HBBIQQII32sB7xII")


def _document(records: list[bytes], strings: bytes = b"") -> bytes:
    payload = b"".join(records) + strings
    return _HEADER.pack(
        EVENT_MAGIC,
        1,
        EVENT_RECORD_LENGTH,
        0,
        EVENT_HEADER_LENGTH + len(payload),
        len(records),
        len(strings),
        hashlib.sha256(payload).digest(),
    ) + payload


def _record(
    *,
    sequence: int,
    kind: int,
    flags: int = 0,
    completed: int = 0,
    query_key: bytes = bytes(32),
    satisfiable: int = 0,
    error_offset: int = 0,
    error_length: int = 0,
) -> bytes:
    return _RECORD.pack(
        1,
        2,
        kind,
        flags,
        sequence,
        9,
        completed,
        1,
        query_key,
        satisfiable,
        error_offset,
        error_length,
    )


def test_decodes_empty_and_complete_query_event_sequences() -> None:
    assert decode_events(_document([])) == ()
    encoded = _document(
        [
            _record(sequence=4, kind=1),
            _record(
                sequence=5,
                kind=2,
                flags=1,
                completed=1,
                query_key=bytes([7]) * 32,
                satisfiable=2,
            ),
            _record(sequence=6, kind=4, completed=1),
        ]
    )

    events = decode_events(encoded)

    assert tuple(event.kind for event in events) == (
        "operation_started",
        "check_completed",
        "operation_completed",
    )
    assert events[1].query_key == bytes([7]) * 32
    assert events[1].satisfiable is True


def test_decodes_abort_error_from_string_table() -> None:
    code = b"REASONER_INTERRUPTED"
    encoded = _document(
        [
            _record(sequence=1, kind=1),
            _record(
                sequence=2,
                kind=5,
                flags=2,
                error_length=len(code),
            ),
        ],
        code,
    )

    assert decode_events(encoded)[1].error_code == code.decode()


@pytest.mark.parametrize(
    "mutate",
    [
        lambda value: bytes([value[0] ^ 1]) + value[1:],
        lambda value: value[:8] + b"\x02\x00" + value[10:],
        lambda value: value[:-1],
        lambda value: value[:32] + bytes([value[32] ^ 1]) + value[33:],
    ],
)
def test_rejects_corrupt_headers_lengths_and_hashes(mutate: object) -> None:
    encoded = _document([_record(sequence=1, kind=1)])
    with pytest.raises(BackendMismatchError):
        decode_events(mutate(encoded))  # type: ignore[operator]


@pytest.mark.parametrize(
    "records,strings",
    [
        ([_record(sequence=0, kind=1)], b""),
        ([_record(sequence=2, kind=1), _record(sequence=2, kind=1)], b""),
        ([_record(sequence=1, kind=99)], b""),
        ([_record(sequence=1, kind=1, satisfiable=2)], b""),
        ([_record(sequence=1, kind=5, flags=2, error_length=20)], b"SHORT"),
        ([_record(sequence=1, kind=5, flags=2, error_length=3)], b"bad"),
    ],
)
def test_rejects_noncanonical_records(records: list[bytes], strings: bytes) -> None:
    with pytest.raises(BackendMismatchError):
        decode_events(_document(records, strings))


def test_requires_exact_bytes() -> None:
    with pytest.raises(TypeError):
        decode_events(bytearray(_document([])))  # type: ignore[arg-type]
