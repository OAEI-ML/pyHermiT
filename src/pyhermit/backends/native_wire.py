"""Strict Python decoder for compact native result buffers.

SPDX-License-Identifier: LGPL-3.0-or-later
"""

from __future__ import annotations

import hashlib
import struct
from enum import IntEnum
from itertools import pairwise
from typing import NoReturn

from pyhermit.backends.protocol import (
    CheckResult,
    DeltaOutcome,
    HierarchyIds,
    RealizationIds,
    ReasoningStatistics,
)
from pyhermit.exceptions import BackendMismatchError

RESULT_MAGIC = b"PYHMTRS\0"
RESULT_SCHEMA_VERSION = 1
RESULT_HEADER_LENGTH = 64
MAX_RESULT_BYTES = 512 * 1024 * 1024

_HEADER = struct.Struct("<8sHHIQII32s")
_CHECK = struct.Struct("<B7x7Q")
_HIERARCHY_PREFIX = struct.Struct("<6I")
_REALIZATION_PREFIX = struct.Struct("<10I")


class ResultKind(IntEnum):
    CHECK = 1
    CHECK_MANY = 2
    HIERARCHY = 3
    REALIZATION = 4
    DELTA = 5


def decode_check(encoded: bytes) -> CheckResult:
    payload, count = _payload(encoded, ResultKind.CHECK)
    if count != 1 or len(payload) != _CHECK.size:
        _fail("single-check result has an invalid record count or byte length")
    return _decode_check_record(payload, 0)


def decode_check_many(encoded: bytes) -> tuple[CheckResult, ...]:
    payload, count = _payload(encoded, ResultKind.CHECK_MANY)
    expected = _checked_product(count, _CHECK.size, "check batch byte length")
    if len(payload) != expected:
        _fail("check-batch result length does not match its record count")
    return tuple(
        _decode_check_record(payload, offset) for offset in range(0, expected, _CHECK.size)
    )


def decode_hierarchy(encoded: bytes) -> HierarchyIds:
    payload, item_count = _payload(encoded, ResultKind.HIERARCHY)
    if len(payload) < _HIERARCHY_PREFIX.size:
        _fail("hierarchy result is shorter than its fixed prefix")
    node_count, member_count, edge_count, top_node, bottom_node, reserved = (
        _HIERARCHY_PREFIX.unpack_from(payload)
    )
    if reserved != 0 or item_count != node_count:
        _fail("hierarchy result prefix is noncanonical")
    offset_count = _checked_add(node_count, 1, "hierarchy offset count")
    word_count = _checked_add(
        _checked_add(offset_count, member_count, "hierarchy member words"),
        _checked_product(edge_count, 2, "hierarchy edge words"),
        "hierarchy total words",
    )
    expected = _checked_add(
        _HIERARCHY_PREFIX.size,
        _checked_product(word_count, 4, "hierarchy payload bytes"),
        "hierarchy payload length",
    )
    if len(payload) != expected:
        _fail("hierarchy result counts do not match its byte length")
    cursor = _HIERARCHY_PREFIX.size
    offsets, cursor = _read_u32s(payload, cursor, offset_count)
    members, cursor = _read_u32s(payload, cursor, member_count)
    edge_words, cursor = _read_u32s(payload, cursor, edge_count * 2)
    if cursor != len(payload):
        _fail("hierarchy result contains trailing bytes")
    if not offsets or offsets[0] != 0 or offsets[-1] != member_count:
        _fail("hierarchy member offsets do not cover the member table")
    if any(left >= right for left, right in pairwise(offsets)):
        _fail("hierarchy nodes must be nonempty and use increasing offsets")
    nodes = tuple(
        tuple(members[offsets[index] : offsets[index + 1]]) for index in range(node_count)
    )
    edges = tuple(zip(edge_words[::2], edge_words[1::2], strict=True))
    try:
        return HierarchyIds(nodes, edges, top_node, bottom_node)
    except (TypeError, ValueError) as error:
        raise _mismatch("native hierarchy result violates the backend contract") from error


def decode_realization(encoded: bytes) -> RealizationIds:
    payload, item_count = _payload(encoded, ResultKind.REALIZATION)
    if len(payload) < _REALIZATION_PREFIX.size:
        _fail("realization result is shorter than its fixed prefix")
    (
        group_count,
        individual_count,
        direct_count,
        direct_value_count,
        object_count,
        object_value_count,
        data_count,
        data_value_count,
        different_count,
        reserved,
    ) = _REALIZATION_PREFIX.unpack_from(payload)
    if reserved != 0 or item_count != group_count:
        _fail("realization result prefix is noncanonical")
    words = _realization_word_count(
        group_count,
        individual_count,
        direct_count,
        direct_value_count,
        object_count,
        object_value_count,
        data_count,
        data_value_count,
        different_count,
    )
    expected = _checked_add(
        _REALIZATION_PREFIX.size,
        _checked_product(words, 4, "realization payload bytes"),
        "realization payload length",
    )
    if len(payload) != expected:
        _fail("realization result counts do not match its byte length")

    cursor = _REALIZATION_PREFIX.size
    group_offsets, cursor = _read_u32s(payload, cursor, group_count + 1)
    individuals, cursor = _read_u32s(payload, cursor, individual_count)
    same_as = _partition(group_offsets, individuals, "same-as")

    direct_words, cursor = _read_u32s(payload, cursor, direct_count * 3)
    direct_values, cursor = _read_u32s(payload, cursor, direct_value_count)
    direct_types = _rows2(direct_words, direct_values, group_count, "direct-type")

    object_words, cursor = _read_u32s(payload, cursor, object_count * 4)
    object_values, cursor = _read_u32s(payload, cursor, object_value_count)
    object_targets = _rows3(object_words, object_values, group_count, "object-target")

    data_words, cursor = _read_u32s(payload, cursor, data_count * 4)
    data_values, cursor = _read_u32s(payload, cursor, data_value_count)
    data_targets = _rows3(data_words, data_values, group_count, "data-target")

    different_words, cursor = _read_u32s(payload, cursor, different_count * 2)
    if cursor != len(payload):
        _fail("realization result contains trailing bytes")
    different_from = tuple(zip(different_words[::2], different_words[1::2], strict=True))
    if different_from != tuple(sorted(set(different_from))) or any(
        left >= right or right >= group_count for left, right in different_from
    ):
        _fail("different-from rows are noncanonical or reference absent groups")
    try:
        return RealizationIds(
            same_as,
            direct_types,
            object_targets,
            data_targets,
            different_from,
        )
    except (TypeError, ValueError) as error:
        raise _mismatch("native realization result violates the backend contract") from error


def decode_delta(encoded: bytes) -> DeltaOutcome:
    payload, count = _payload(encoded, ResultKind.DELTA)
    if count != 1 or len(payload) != 8 or any(payload[1:]):
        _fail("delta result has invalid length, count, or reserved bytes")
    if payload[0] == 1:
        return DeltaOutcome.APPLIED_INCREMENTALLY
    if payload[0] == 2:
        return DeltaOutcome.REBUILD_REQUIRED
    _fail("delta result uses an unknown outcome discriminant")


def _payload(encoded: bytes, expected_kind: ResultKind) -> tuple[memoryview, int]:
    if type(encoded) is not bytes:
        raise TypeError("native result must be bytes")
    if len(encoded) > MAX_RESULT_BYTES:
        _fail("native result exceeds the Python validation cap")
    if len(encoded) < RESULT_HEADER_LENGTH:
        _fail("native result is shorter than its fixed header")
    magic, schema, kind, flags, total_length, item_count, reserved, expected_hash = (
        _HEADER.unpack_from(encoded)
    )
    if magic != RESULT_MAGIC:
        _fail("native result magic is invalid")
    if schema != RESULT_SCHEMA_VERSION:
        _fail("native result schema is incompatible")
    if kind != int(expected_kind):
        _fail("native result kind does not match the requested operation")
    if flags != 0 or reserved != 0:
        _fail("native result contains unsupported flags or reserved bits")
    if total_length != len(encoded):
        _fail("native result total length does not match its buffer")
    payload = memoryview(encoded)[RESULT_HEADER_LENGTH:]
    if hashlib.sha256(payload).digest() != expected_hash:
        _fail("native result content hash does not match its payload")
    return payload, item_count


def _decode_check_record(payload: memoryview, offset: int) -> CheckResult:
    satisfiable, elapsed, nodes, facts, branches, backtracks, merges, datatype_checks = (
        _CHECK.unpack_from(payload, offset)
    )
    if satisfiable not in (0, 1):
        _fail("native check result uses a non-Boolean satisfiability value")
    return CheckResult(
        bool(satisfiable),
        ReasoningStatistics(
            elapsed_seconds=elapsed / 1_000_000_000,
            nodes=nodes,
            facts=facts,
            branches=branches,
            backtracks=backtracks,
            merges=merges,
            datatype_checks=datatype_checks,
        ),
    )


def _partition(
    offsets: tuple[int, ...], values: tuple[int, ...], label: str
) -> tuple[tuple[int, ...], ...]:
    if not offsets or offsets[0] != 0 or offsets[-1] != len(values):
        _fail(f"{label} offsets do not cover their value table")
    if any(left >= right for left, right in pairwise(offsets)):
        _fail(f"{label} groups must be nonempty and use increasing offsets")
    return tuple(
        tuple(values[offsets[index] : offsets[index + 1]]) for index in range(len(offsets) - 1)
    )


def _rows2(
    words: tuple[int, ...],
    values: tuple[int, ...],
    group_count: int,
    label: str,
) -> tuple[tuple[int, tuple[int, ...]], ...]:
    result: list[tuple[int, tuple[int, ...]]] = []
    expected_offset = 0
    for group, offset, count in zip(words[::3], words[1::3], words[2::3], strict=True):
        if group >= group_count or offset != expected_offset:
            _fail(f"{label} row references an absent group or noncanonical offset")
        end = _checked_add(offset, count, f"{label} row end")
        if end > len(values):
            _fail(f"{label} row exceeds its value table")
        selected = tuple(values[offset:end])
        if selected != tuple(sorted(set(selected))):
            _fail(f"{label} values are not sorted and unique")
        result.append((group, selected))
        expected_offset = end
    if expected_offset != len(values) or result != sorted(result, key=lambda row: row[0]):
        _fail(f"{label} rows do not canonically cover their value table")
    if len({group for group, _ in result}) != len(result):
        _fail(f"{label} rows repeat a group")
    return tuple(result)


def _rows3(
    words: tuple[int, ...],
    values: tuple[int, ...],
    group_count: int,
    label: str,
) -> tuple[tuple[int, int, tuple[int, ...]], ...]:
    result: list[tuple[int, int, tuple[int, ...]]] = []
    expected_offset = 0
    for group, property_id, offset, count in zip(
        words[::4], words[1::4], words[2::4], words[3::4], strict=True
    ):
        if group >= group_count or offset != expected_offset:
            _fail(f"{label} row references an absent group or noncanonical offset")
        end = _checked_add(offset, count, f"{label} row end")
        if end > len(values):
            _fail(f"{label} row exceeds its value table")
        selected = tuple(values[offset:end])
        if selected != tuple(sorted(set(selected))):
            _fail(f"{label} values are not sorted and unique")
        result.append((group, property_id, selected))
        expected_offset = end
    keys = [(group, property_id) for group, property_id, _ in result]
    if expected_offset != len(values) or keys != sorted(set(keys)):
        _fail(f"{label} rows do not canonically cover their value table")
    return tuple(result)


def _read_u32s(payload: memoryview, offset: int, count: int) -> tuple[tuple[int, ...], int]:
    byte_count = _checked_product(count, 4, "u32 table byte length")
    end = _checked_add(offset, byte_count, "u32 table end")
    if end > len(payload):
        _fail("native result u32 table is truncated")
    values = tuple(value[0] for value in struct.iter_unpack("<I", payload[offset:end]))
    return values, end


def _realization_word_count(*counts: int) -> int:
    (
        group_count,
        individual_count,
        direct_count,
        direct_value_count,
        object_count,
        object_value_count,
        data_count,
        data_value_count,
        different_count,
    ) = counts
    result = _checked_add(group_count, 1, "realization group offsets")
    for count, width, label in (
        (individual_count, 1, "same-as members"),
        (direct_count, 3, "direct-type rows"),
        (direct_value_count, 1, "direct-type values"),
        (object_count, 4, "object-target rows"),
        (object_value_count, 1, "object-target values"),
        (data_count, 4, "data-target rows"),
        (data_value_count, 1, "data-target values"),
        (different_count, 2, "different-from rows"),
    ):
        result = _checked_add(result, _checked_product(count, width, label), label)
    return result


def _checked_add(left: int, right: int, label: str) -> int:
    value = left + right
    if value > MAX_RESULT_BYTES:
        _fail(f"{label} exceeds the native result validation cap")
    return value


def _checked_product(left: int, right: int, label: str) -> int:
    value = left * right
    if value > MAX_RESULT_BYTES:
        _fail(f"{label} exceeds the native result validation cap")
    return value


def _mismatch(message: str) -> BackendMismatchError:
    return BackendMismatchError(message, context={"reason": "native_result_invalid"})


def _fail(message: str) -> NoReturn:
    raise _mismatch(message)


__all__ = [
    "MAX_RESULT_BYTES",
    "RESULT_HEADER_LENGTH",
    "RESULT_MAGIC",
    "RESULT_SCHEMA_VERSION",
    "ResultKind",
    "decode_check",
    "decode_check_many",
    "decode_delta",
    "decode_hierarchy",
    "decode_realization",
]
