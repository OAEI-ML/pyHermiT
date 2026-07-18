"""Strict decoder for bounded native session-event drains.

SPDX-License-Identifier: LGPL-3.0-or-later
"""

from __future__ import annotations

import hashlib
import struct
from dataclasses import dataclass
from typing import Literal, NoReturn, TypeAlias

from pyhermit.exceptions import BackendMismatchError

EVENT_MAGIC = b"PYHMTEV\0"
EVENT_SCHEMA_VERSION = 1
EVENT_HEADER_LENGTH = 64
EVENT_RECORD_LENGTH = 80
MAX_EVENT_WIRE_BYTES = 16 * 1024 * 1024

_HEADER = struct.Struct("<8sHHIQII32s")
_RECORD = struct.Struct("<HBBIQQII32sB7xII")
_FLAG_QUERY_KEY = 1
_FLAG_ERROR_CODE = 2

NativeOperation: TypeAlias = Literal[
    "permanent_check", "query_check", "batch_check", "reset_query_state"
]
NativeEventKind: TypeAlias = Literal[
    "operation_started",
    "check_completed",
    "query_state_reset",
    "operation_completed",
    "operation_aborted",
]

_OPERATIONS: dict[int, NativeOperation] = {
    1: "permanent_check",
    2: "query_check",
    3: "batch_check",
    4: "reset_query_state",
}
_KINDS: dict[int, NativeEventKind] = {
    1: "operation_started",
    2: "check_completed",
    3: "query_state_reset",
    4: "operation_completed",
    5: "operation_aborted",
}


@dataclass(frozen=True, slots=True)
class NativeSessionEvent:
    """One validated scheduler event with no Python callback/object references."""

    sequence: int
    operation_id: int
    operation: NativeOperation
    kind: NativeEventKind
    completed: int
    total: int
    query_key: bytes | None = None
    satisfiable: bool | None = None
    error_code: str | None = None


def decode_events(encoded: bytes) -> tuple[NativeSessionEvent, ...]:
    """Validate a whole event document before exposing any record to the adapter."""

    if type(encoded) is not bytes:
        raise TypeError("native event drain must be bytes")
    if len(encoded) > MAX_EVENT_WIRE_BYTES:
        _fail("native event drain exceeds the Python validation cap")
    if len(encoded) < EVENT_HEADER_LENGTH:
        _fail("native event drain is shorter than its fixed header")
    magic, schema, record_length, flags, total_length, count, string_bytes, digest = (
        _HEADER.unpack_from(encoded)
    )
    if magic != EVENT_MAGIC:
        _fail("native event drain magic is invalid")
    if schema != EVENT_SCHEMA_VERSION or record_length != EVENT_RECORD_LENGTH:
        _fail("native event drain schema or record length is incompatible")
    if flags != 0 or total_length != len(encoded):
        _fail("native event drain header is noncanonical")
    records_length = _checked_product(count, EVENT_RECORD_LENGTH)
    payload_length = _checked_add(records_length, string_bytes)
    if _checked_add(EVENT_HEADER_LENGTH, payload_length) != len(encoded):
        _fail("native event drain counts do not match its byte length")
    payload = memoryview(encoded)[EVENT_HEADER_LENGTH:]
    if hashlib.sha256(payload).digest() != digest:
        _fail("native event drain content hash does not match its payload")
    strings = payload[records_length:]

    events: list[NativeSessionEvent] = []
    previous_sequence = 0
    for index in range(count):
        offset = index * EVENT_RECORD_LENGTH
        (
            version,
            operation_value,
            kind_value,
            record_flags,
            sequence,
            operation_id,
            completed,
            total,
            query_bytes,
            satisfiable_value,
            error_offset,
            error_length,
        ) = _RECORD.unpack_from(payload, offset)
        if version != EVENT_SCHEMA_VERSION:
            _fail("native event record version is incompatible")
        if record_flags & ~(_FLAG_QUERY_KEY | _FLAG_ERROR_CODE):
            _fail("native event record contains unsupported flags")
        operation = _OPERATIONS.get(operation_value)
        kind = _KINDS.get(kind_value)
        if operation is None or kind is None:
            _fail("native event record uses an unknown discriminant")
        if sequence == 0 or sequence <= previous_sequence or operation_id == 0:
            _fail("native event IDs and sequences are noncanonical")
        previous_sequence = sequence
        if completed > total:
            _fail("native event completed count exceeds its total")

        has_query = bool(record_flags & _FLAG_QUERY_KEY)
        query_key = bytes(query_bytes) if has_query else None
        if not has_query and any(query_bytes):
            _fail("native event has query bytes without its presence flag")
        if satisfiable_value == 0:
            satisfiable = None
        elif satisfiable_value == 1:
            satisfiable = False
        elif satisfiable_value == 2:
            satisfiable = True
        else:
            _fail("native event satisfiability discriminant is invalid")

        has_error = bool(record_flags & _FLAG_ERROR_CODE)
        if has_error:
            end = _checked_add(error_offset, error_length)
            if error_length == 0 or end > len(strings):
                _fail("native event error-code range is invalid")
            try:
                error_code = bytes(strings[error_offset:end]).decode("ascii")
            except UnicodeDecodeError as error:
                raise _mismatch("native event error code is not ASCII") from error
            if not _stable_code(error_code):
                _fail("native event error code is not a stable identifier")
        else:
            if error_offset != 0 or error_length != 0:
                _fail("native event has an error-code range without its presence flag")
            error_code = None

        event = NativeSessionEvent(
            sequence,
            operation_id,
            operation,
            kind,
            completed,
            total,
            query_key,
            satisfiable,
            error_code,
        )
        _validate_shape(event)
        events.append(event)
    return tuple(events)


def _validate_shape(event: NativeSessionEvent) -> None:
    if event.kind == "operation_started":
        valid = (
            event.completed == 0
            and event.query_key is None
            and event.satisfiable is None
            and event.error_code is None
        )
    elif event.kind == "check_completed":
        valid = event.completed > 0 and event.satisfiable is not None and event.error_code is None
    elif event.kind == "query_state_reset":
        valid = event.query_key is None and event.satisfiable is None and event.error_code is None
    elif event.kind == "operation_completed":
        valid = (
            event.completed == event.total
            and event.query_key is None
            and event.satisfiable is None
            and event.error_code is None
        )
    else:
        valid = (
            event.query_key is None and event.satisfiable is None and event.error_code is not None
        )
    if not valid:
        _fail(f"native {event.kind.replace('_', '-')} event fields are noncanonical")


def _stable_code(value: str) -> bool:
    return bool(value) and all(
        character.isupper() or character.isdigit() or character == "_" for character in value
    )


def _checked_product(left: int, right: int) -> int:
    value = left * right
    if value > MAX_EVENT_WIRE_BYTES:
        _fail("native event byte count exceeds its validation cap")
    return value


def _checked_add(left: int, right: int) -> int:
    value = left + right
    if value > MAX_EVENT_WIRE_BYTES:
        _fail("native event byte count exceeds its validation cap")
    return value


def _mismatch(message: str) -> BackendMismatchError:
    return BackendMismatchError(message, context={"reason": "native_event_invalid"})


def _fail(message: str) -> NoReturn:
    raise _mismatch(message)


__all__ = [
    "EVENT_HEADER_LENGTH",
    "EVENT_MAGIC",
    "EVENT_RECORD_LENGTH",
    "EVENT_SCHEMA_VERSION",
    "MAX_EVENT_WIRE_BYTES",
    "NativeEventKind",
    "NativeOperation",
    "NativeSessionEvent",
    "decode_events",
]
