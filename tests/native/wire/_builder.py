"""Independent helpers for the production native-input-v1 golden documents."""

# SPDX-License-Identifier: LGPL-3.0-or-later

from __future__ import annotations

import hashlib
import json
import struct
from pathlib import Path

HEADER_LENGTH = 72
DIRECTORY_ENTRY_LENGTH = 32
OPTIONAL_SECTION = 1
ONTOLOGY_FINGERPRINT = hashlib.sha256(b"ontology").hexdigest()


def _golden_document(name: str) -> bytes:
    fixture = json.loads(
        (Path(__file__).parents[2] / "data" / "native-input-v1.json").read_text(
            encoding="utf-8"
        )
    )
    encoded = fixture["documents"][name]["hex"]
    if not isinstance(encoded, str):
        raise TypeError(f"native input fixture {name!r} is not a hexadecimal string")
    return bytes.fromhex(encoded)


def valid_documents() -> tuple[bytes, bytes]:
    """Return the canonical production ontology/config pair."""

    return _golden_document("ontology"), _golden_document("config")


def valid_query_documents() -> tuple[bytes, bytes]:
    """Return the canonical incremental and rebuild-required query documents."""

    return _golden_document("query"), _golden_document("query_rebuild")


def rehash(document: bytes | bytearray) -> bytes:
    """Refresh the native-input-v1 payload hash after a deliberate mutation."""

    mutable = bytearray(document)
    mutable[40:72] = hashlib.sha256(mutable[HEADER_LENGTH:]).digest()
    return bytes(mutable)


def directory_entry(document: bytes | bytearray, kind: int) -> int:
    """Return the directory-record offset for one required section kind."""

    count = struct.unpack_from("<I", document, 32)[0]
    for index in range(count):
        start = HEADER_LENGTH + index * DIRECTORY_ENTRY_LENGTH
        if struct.unpack_from("<H", document, start)[0] == kind:
            return start
    raise ValueError(f"native input fixture has no section kind {kind}")


def section_offset(document: bytes | bytearray, kind: int) -> int:
    """Return the payload offset for one section kind."""

    return struct.unpack_from("<Q", document, directory_entry(document, kind) + 8)[0]


def append_unknown_section(document: bytes, *, optional: bool) -> bytes:
    """Append one canonical zero-length future section to a valid document."""

    mutable = bytearray(document)
    count = struct.unpack_from("<I", mutable, 32)[0]
    insertion = HEADER_LENGTH + count * DIRECTORY_ENTRY_LENGTH
    mutable[insertion:insertion] = bytes(DIRECTORY_ENTRY_LENGTH)
    for index in range(count):
        start = HEADER_LENGTH + index * DIRECTORY_ENTRY_LENGTH
        offset = struct.unpack_from("<Q", mutable, start + 8)[0]
        struct.pack_into("<Q", mutable, start + 8, offset + DIRECTORY_ENTRY_LENGTH)
    new_entry = HEADER_LENGTH + count * DIRECTORY_ENTRY_LENGTH
    struct.pack_into(
        "<HHIQQII",
        mutable,
        new_entry,
        60_000,
        OPTIONAL_SECTION if optional else 0,
        0,
        len(mutable),
        0,
        0,
        8,
    )
    struct.pack_into("<I", mutable, 32, count + 1)
    struct.pack_into("<Q", mutable, 16, len(mutable))
    return rehash(mutable)


def first_padding_byte(document: bytes | bytearray) -> int:
    """Return one validated alignment byte between directory/payload sections."""

    count = struct.unpack_from("<I", document, 32)[0]
    cursor = HEADER_LENGTH + count * DIRECTORY_ENTRY_LENGTH
    coverage: list[tuple[int, int]] = []
    for index in range(count):
        start = HEADER_LENGTH + index * DIRECTORY_ENTRY_LENGTH
        offset, length = struct.unpack_from("<QQ", document, start + 8)
        coverage.append((offset, offset + length))
    for start, end in sorted(coverage):
        if start > cursor:
            return cursor
        cursor = end
    raise ValueError("native input fixture contains no alignment padding")
