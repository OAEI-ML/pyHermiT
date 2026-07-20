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


def _empty_columns() -> dict[str, memoryview]:
    return {
        name: memoryview(struct.pack("<Q", 0) if name == "node_field_offsets" else b"")
        for name in _COLUMN_NAMES
    }


def test_private_validator_accepts_an_empty_borrowed_canonical_model() -> None:
    columns = _empty_columns()

    assert native._validate_encoded_columns_v1(**columns) is None
    assert tuple(columns) == _COLUMN_NAMES
    assert all(type(column) is memoryview and column.readonly for column in columns.values())


def test_private_validator_rejects_hostile_envelopes_and_structure() -> None:
    columns = _empty_columns()

    with pytest.raises(BackendMismatchError, match="exact memoryview"):
        native._validate_encoded_columns_v1(**{**columns, "scalar_bytes": b""})  # type: ignore[arg-type]
    with pytest.raises(BackendMismatchError, match="writable"):
        native._validate_encoded_columns_v1(**{**columns, "scalar_bytes": memoryview(bytearray())})
    with pytest.raises(BackendMismatchError, match="counts differ"):
        native._validate_encoded_columns_v1(**{**columns, "root_kinds": memoryview(b"\x01")})
