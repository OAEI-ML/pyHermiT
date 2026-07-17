"""Independent Python builder for the private WPR0 flat-wire test documents."""

# SPDX-License-Identifier: LGPL-3.0-or-later

from __future__ import annotations

import hashlib
import struct
from dataclasses import dataclass

MAGIC = b"PYHMTIR\0"
HEADER_LENGTH = 72
DIRECTORY_ENTRY_LENGTH = 32
ONTOLOGY = 1
CONFIG = 2
METADATA = 1
CONFIG_SECTION = 32
OPTIONAL_SECTION = 1


@dataclass(frozen=True, slots=True)
class SectionSpec:
    """One language-neutral section supplied to the independent test encoder."""

    kind: int
    payload: bytes
    count: int
    flags: int = 0
    alignment: int = 8


def metadata_payload(*, ontology_byte: int = 0x11) -> bytes:
    """Return a valid fixed-width v1 metadata record."""

    return b"".join(
        (
            bytes([ontology_byte]) * 32,
            b"\x22" * 32,
            b"\x33" * 32,
            b"\x44" * 32,
            struct.pack("<HHIHHI", 0, 1, 1, 1, 0, 1),
        )
    )


def build_document(
    kind: int,
    sections: tuple[SectionSpec, ...] | None = None,
) -> bytes:
    """Encode a canonical v1 document without calling any Rust implementation code."""

    if sections is None:
        if kind == ONTOLOGY:
            sections = (SectionSpec(METADATA, metadata_payload(), 1),)
        elif kind == CONFIG:
            sections = (SectionSpec(CONFIG_SECTION, b"", 1),)
        else:
            raise ValueError(f"no default section for document kind {kind}")

    document = bytearray(HEADER_LENGTH + DIRECTORY_ENTRY_LENGTH * len(sections))
    entries: list[tuple[SectionSpec, int]] = []
    for section in sections:
        padding = (-len(document)) % section.alignment
        document.extend(b"\0" * padding)
        offset = len(document)
        document.extend(section.payload)
        entries.append((section, offset))

    document[:8] = MAGIC
    struct.pack_into(
        "<HHIQQII",
        document,
        8,
        1,
        kind,
        0,
        len(document),
        HEADER_LENGTH,
        len(sections),
        0,
    )
    for index, (section, offset) in enumerate(entries):
        struct.pack_into(
            "<HHIQQII",
            document,
            HEADER_LENGTH + index * DIRECTORY_ENTRY_LENGTH,
            section.kind,
            section.flags,
            0,
            offset,
            len(section.payload),
            section.count,
            section.alignment,
        )
    return rehash(document)


def rehash(document: bytes | bytearray) -> bytes:
    """Refresh only the v1 payload hash after a deliberate test mutation."""

    mutable = bytearray(document)
    mutable[40:72] = hashlib.sha256(mutable[HEADER_LENGTH:]).digest()
    return bytes(mutable)


def valid_documents() -> tuple[bytes, bytes]:
    """Return a minimal valid ontology/config pair."""

    return build_document(ONTOLOGY), build_document(CONFIG)
