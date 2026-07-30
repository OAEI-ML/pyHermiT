"""Tests for deterministic, loadable Mach-O UUID normalization."""

from __future__ import annotations

import hashlib
import struct
from pathlib import Path

import pytest
from pyhermit_build import normalize_macho_uuid


def _macho(uuid: bytes = b"\x11" * 16) -> bytes:
    header = bytearray(32)
    header[:4] = b"\xcf\xfa\xed\xfe"
    struct.pack_into("<I", header, 16, 1)
    command = struct.pack("<II", 0x1B, 24) + uuid
    return bytes(header + command + b"native-payload")


def test_macho_uuid_is_content_derived_and_idempotent(tmp_path: Path) -> None:
    extension = tmp_path / "_native.abi3.so"
    extension.write_bytes(_macho())

    normalize_macho_uuid(extension)
    normalized = extension.read_bytes()
    expected = bytearray(normalized)
    expected[40:56] = b"\0" * 16

    assert normalized[40:56] == hashlib.sha256(expected).digest()[:16]
    normalize_macho_uuid(extension)
    assert extension.read_bytes() == normalized


def test_macho_uuid_requires_exactly_one_load_command(tmp_path: Path) -> None:
    extension = tmp_path / "_native.abi3.so"
    header = bytearray(_macho()[:32])
    struct.pack_into("<I", header, 16, 0)
    extension.write_bytes(header)

    with pytest.raises(RuntimeError, match="exactly one LC_UUID"):
        normalize_macho_uuid(extension)
