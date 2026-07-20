"""Private borrowed-column boundary for the unadvertised encoded preflight gate."""

# SPDX-License-Identifier: LGPL-3.0-or-later

from __future__ import annotations

import struct

import pytest

import pyhermit._native as native
from pyhermit.exceptions import BackendMismatchError

_COLUMN_NAMES = (
    "root_kinds",
    "root_ids",
    "node_tags",
    "node_field_offsets",
    "field_kinds",
    "field_values",
    "field_lengths",
    "item_kinds",
    "item_values",
    "item_lengths",
    "scalar_bytes",
)

_SLICE_COLUMN_ORDER = (
    "root_kinds",
    "root_ids",
    "node_tags",
    "node_field_offsets",
    "field_kinds",
    "field_values",
    "field_lengths",
    "item_kinds",
    "item_values",
    "item_lengths",
    "scalar_bytes",
)


def _empty_columns() -> dict[str, memoryview]:
    return {
        name: memoryview(struct.pack("<Q", 0) if name == "node_field_offsets" else b"")
        for name in _COLUMN_NAMES
    }


def _slice_record(
    columns: dict[str, memoryview],
    *,
    posting_mode: int = 0,
    postings: memoryview | None = None,
    member_tokens: object = (),
    anonymous_scope_maps: object = (),
) -> tuple[object, ...]:
    return (
        posting_mode,
        memoryview(b"") if postings is None else postings,
        member_tokens,
        anonymous_scope_maps,
        *(columns[name] for name in _SLICE_COLUMN_ORDER),
    )


def test_private_validator_accepts_an_empty_borrowed_canonical_model() -> None:
    columns = _empty_columns()

    assert native._validate_encoded_columns_v1(**columns) is None
    assert tuple(columns) == _COLUMN_NAMES
    assert all(type(column) is memoryview and column.readonly for column in columns.values())


def test_private_selection_validator_accepts_all_and_rejects_hostile_exclusions() -> None:
    columns = _empty_columns()
    empty = memoryview(b"")

    assert (
        native._validate_encoded_selection_v1(
            posting_mode=0,
            postings=empty,
            **columns,
        )
        is None
    )
    with pytest.raises(BackendMismatchError, match="empty"):
        native._validate_encoded_selection_v1(
            posting_mode=2,
            postings=empty,
            **columns,
        )
    with pytest.raises(BackendMismatchError, match="partial u32"):
        native._validate_encoded_selection_v1(
            posting_mode=2,
            postings=memoryview(b"\x01"),
            **columns,
        )
    with pytest.raises(BackendMismatchError, match="in-range"):
        native._validate_encoded_selection_v1(
            posting_mode=1,
            postings=memoryview(struct.pack("<I", 1)),
            **columns,
        )
    with pytest.raises(BackendMismatchError, match="unsupported"):
        native._validate_encoded_selection_v1(
            posting_mode=3,
            postings=memoryview(struct.pack("<I", 1)),
            **columns,
        )
    with pytest.raises(BackendMismatchError, match="exact memoryview"):
        native._validate_encoded_selection_v1(
            posting_mode=0,
            postings=b"",  # type: ignore[arg-type]
            **columns,
        )


def test_private_multi_slice_validator_consumes_exact_context_and_rejects_hostility() -> None:
    columns = _empty_columns()
    scope_map = memoryview(b"a" * 32 + b"b" * 32)
    record = _slice_record(
        columns,
        member_tokens=(b"t" * 32,),
        anonymous_scope_maps=(scope_map,),
    )

    assert native._validate_encoded_slices_v1(slices=(record,)) is None
    with pytest.raises(BackendMismatchError, match="program is not an exact tuple"):
        native._validate_encoded_slices_v1(slices=[record])  # type: ignore[arg-type]
    with pytest.raises(BackendMismatchError, match="record is not an exact tuple"):
        native._validate_encoded_slices_v1(slices=([*record],))
    with pytest.raises(BackendMismatchError, match="field count"):
        native._validate_encoded_slices_v1(slices=(record[:-1],))
    with pytest.raises(BackendMismatchError, match="member tokens are not an exact tuple"):
        native._validate_encoded_slices_v1(
            slices=(_slice_record(columns, member_tokens=[b"t" * 32]),)
        )
    with pytest.raises(BackendMismatchError, match="bytes32"):
        native._validate_encoded_slices_v1(
            slices=(_slice_record(columns, member_tokens=(b"short",)),)
        )
    with pytest.raises(BackendMismatchError, match="partial row"):
        native._validate_encoded_slices_v1(
            slices=(
                _slice_record(
                    columns,
                    anonymous_scope_maps=(memoryview(b"x"),),
                ),
            )
        )
    with pytest.raises(BackendMismatchError, match="identity rows"):
        native._validate_encoded_slices_v1(
            slices=(
                _slice_record(
                    columns,
                    anonymous_scope_maps=(memoryview(b"x" * 64),),
                ),
            )
        )


def test_private_validator_rejects_hostile_envelopes_and_structure() -> None:
    columns = _empty_columns()

    with pytest.raises(BackendMismatchError, match="exact memoryview"):
        native._validate_encoded_columns_v1(**{**columns, "scalar_bytes": b""})  # type: ignore[arg-type]
    with pytest.raises(BackendMismatchError, match="writable"):
        native._validate_encoded_columns_v1(**{**columns, "scalar_bytes": memoryview(bytearray())})
    with pytest.raises(BackendMismatchError, match="counts differ"):
        native._validate_encoded_columns_v1(**{**columns, "root_kinds": memoryview(b"\x01")})
