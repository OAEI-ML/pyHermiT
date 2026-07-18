from __future__ import annotations

import hashlib
import struct

import pytest

from pyhermit.backends.native_wire import (
    RESULT_HEADER_LENGTH,
    RESULT_MAGIC,
    ResultKind,
    decode_check,
    decode_check_many,
    decode_delta,
    decode_hierarchy,
    decode_realization,
)
from pyhermit.backends.protocol import DeltaOutcome
from pyhermit.exceptions import BackendMismatchError


def document(kind: ResultKind, count: int, payload: bytes) -> bytes:
    encoded = bytearray(RESULT_HEADER_LENGTH)
    encoded.extend(payload)
    struct.pack_into(
        "<8sHHIQII32s",
        encoded,
        0,
        RESULT_MAGIC,
        1,
        kind,
        0,
        len(encoded),
        count,
        0,
        hashlib.sha256(payload).digest(),
    )
    return bytes(encoded)


def u32s(*values: int) -> bytes:
    return struct.pack(f"<{len(values)}I", *values)


def test_check_and_batch_decode_exact_statistics() -> None:
    first = struct.pack("<B7x7Q", 1, 1_500_000_000, 2, 3, 4, 5, 6, 7)
    second = struct.pack("<B7x7Q", 0, 0, 0, 0, 0, 0, 0, 0)

    single = decode_check(document(ResultKind.CHECK, 1, first))
    batch = decode_check_many(document(ResultKind.CHECK_MANY, 2, first + second))

    assert single.satisfiable
    assert single.statistics.elapsed_seconds == 1.5
    assert (
        single.statistics.nodes,
        single.statistics.facts,
        single.statistics.branches,
        single.statistics.backtracks,
        single.statistics.merges,
        single.statistics.datatype_checks,
    ) == (2, 3, 4, 5, 6, 7)
    assert batch == (single, batch[1])
    assert not batch[1].satisfiable


def test_hierarchy_decodes_partition_and_direct_edges() -> None:
    payload = b"".join(
        (
            u32s(3, 4, 2, 2, 0, 0),
            u32s(0, 1, 3, 4),
            u32s(0, 1, 2, 3),
            u32s(0, 1, 1, 2),
        )
    )
    hierarchy = decode_hierarchy(document(ResultKind.HIERARCHY, 3, payload))
    assert hierarchy.nodes == ((0,), (1, 2), (3,))
    assert hierarchy.edges == ((0, 1), (1, 2))
    assert hierarchy.top_node == 2
    assert hierarchy.bottom_node == 0


def test_deep_hierarchy_decode_is_iterative_and_exact() -> None:
    size = 10_000
    edge_words = [value for child in range(size - 1) for value in (child, child + 1)]
    payload = b"".join(
        (
            u32s(size, size, size - 1, size - 1, 0, 0),
            u32s(*range(size + 1)),
            u32s(*range(size)),
            u32s(*edge_words),
        )
    )
    hierarchy = decode_hierarchy(document(ResultKind.HIERARCHY, size, payload))
    assert len(hierarchy.nodes) == size
    assert len(hierarchy.edges) == size - 1
    assert hierarchy.nodes[0] == (0,)
    assert hierarchy.nodes[-1] == (size - 1,)


def test_realization_decodes_all_canonical_tables() -> None:
    payload = b"".join(
        (
            u32s(2, 3, 2, 3, 1, 2, 1, 2, 1, 0),
            u32s(0, 2, 3),
            u32s(1, 2, 7),
            u32s(0, 0, 2, 1, 2, 1),
            u32s(3, 4, 5),
            u32s(0, 9, 0, 2),
            u32s(0, 1),
            u32s(1, 8, 0, 2),
            u32s(11, 12),
            u32s(0, 1),
        )
    )
    result = decode_realization(document(ResultKind.REALIZATION, 2, payload))
    assert result.same_as == ((1, 2), (7,))
    assert result.direct_types == ((0, (3, 4)), (1, (5,)))
    assert result.object_targets == ((0, 9, (0, 1)),)
    assert result.data_targets == ((1, 8, (11, 12)),)
    assert result.different_from == ((0, 1),)


def test_delta_decode_is_exact() -> None:
    assert (
        decode_delta(document(ResultKind.DELTA, 1, b"\x01" + b"\0" * 7))
        is DeltaOutcome.APPLIED_INCREMENTALLY
    )
    assert (
        decode_delta(document(ResultKind.DELTA, 1, b"\x02" + b"\0" * 7))
        is DeltaOutcome.REBUILD_REQUIRED
    )


@pytest.mark.parametrize("offset", (0, 8, 10, 12, 16, 24, 28, 32))
def test_header_and_hash_corruption_fail_closed(offset: int) -> None:
    encoded = bytearray(
        document(ResultKind.CHECK, 1, struct.pack("<B7x7Q", 1, 0, 0, 0, 0, 0, 0, 0))
    )
    encoded[offset] ^= 0xFF
    with pytest.raises(BackendMismatchError):
        decode_check(bytes(encoded))


def test_wrong_kind_nonboolean_trailing_and_nonbytes_are_rejected() -> None:
    valid = struct.pack("<B7x7Q", 1, 0, 0, 0, 0, 0, 0, 0)
    with pytest.raises(BackendMismatchError, match="kind"):
        decode_check(document(ResultKind.CHECK_MANY, 1, valid))
    with pytest.raises(BackendMismatchError, match="Boolean"):
        decode_check(document(ResultKind.CHECK, 1, b"\x02" + valid[1:]))
    with pytest.raises(BackendMismatchError, match="length"):
        decode_check(document(ResultKind.CHECK, 1, valid + b"x"))
    with pytest.raises(TypeError):
        decode_check(bytearray(document(ResultKind.CHECK, 1, valid)))  # type: ignore[arg-type]


def test_hostile_hierarchy_counts_offsets_and_redundancy_are_rejected() -> None:
    prefix = u32s(3, 3, 3, 2, 0, 0)
    redundant = prefix + u32s(0, 1, 2, 3) + u32s(0, 1, 2) + u32s(0, 1, 0, 2, 1, 2)
    with pytest.raises(BackendMismatchError):
        decode_hierarchy(document(ResultKind.HIERARCHY, 3, redundant))
    empty_node = u32s(3, 2, 2, 2, 0, 0) + u32s(0, 1, 1, 2) + u32s(0, 2) + u32s(0, 1, 1, 2)
    with pytest.raises(BackendMismatchError, match="nonempty"):
        decode_hierarchy(document(ResultKind.HIERARCHY, 3, empty_node))
    huge = u32s(0xFFFFFFFF, 0, 0, 0, 0, 0)
    with pytest.raises(BackendMismatchError, match="cap"):
        decode_hierarchy(document(ResultKind.HIERARCHY, 0xFFFFFFFF, huge))


def test_hostile_realization_offsets_rows_and_pairs_are_rejected() -> None:
    prefix = u32s(1, 1, 0, 0, 0, 0, 0, 0, 0, 0)
    bad_offsets = prefix + u32s(0, 2) + u32s(1)
    with pytest.raises(BackendMismatchError, match="offsets"):
        decode_realization(document(ResultKind.REALIZATION, 1, bad_offsets))

    pair_prefix = u32s(1, 1, 0, 0, 0, 0, 0, 0, 1, 0)
    bad_pair = pair_prefix + u32s(0, 1) + u32s(1) + u32s(0, 0)
    with pytest.raises(BackendMismatchError, match="different-from"):
        decode_realization(document(ResultKind.REALIZATION, 1, bad_pair))
