"""Tests for deterministic, loadable Mach-O UUID normalization."""

from __future__ import annotations

import hashlib
import struct
from pathlib import Path
from unittest.mock import patch

import pytest
from pyhermit_build import normalize_macho_binary, normalize_macho_uuid


def _macho(uuid: bytes = b"\x11" * 16) -> bytes:
    header = bytearray(32)
    header[:4] = b"\xcf\xfa\xed\xfe"
    struct.pack_into("<I", header, 16, 1)
    command = struct.pack("<II", 0x1B, 24) + uuid
    return bytes(header + command + b"native-payload")


def _signed_macho(signature: bytes) -> bytes:
    header = bytearray(32)
    header[:4] = b"\xcf\xfa\xed\xfe"
    struct.pack_into("<I", header, 16, 2)
    uuid_command = struct.pack("<II", 0x1B, 24) + b"\x11" * 16
    signature_offset = len(header) + len(uuid_command) + 16 + len(b"native-payload")
    signature_command = struct.pack("<IIII", 0x1D, 16, signature_offset, len(signature))
    return bytes(header + uuid_command + signature_command + b"native-payload" + signature)


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


def test_macho_uuid_ignores_nondeterministic_code_signature(tmp_path: Path) -> None:
    first = tmp_path / "first.so"
    second = tmp_path / "second.so"
    first.write_bytes(_signed_macho(b"\x22" * 32))
    second.write_bytes(_signed_macho(b"\x33" * 32))

    normalize_macho_uuid(first)
    normalize_macho_uuid(second)

    assert first.read_bytes()[40:56] == second.read_bytes()[40:56]


def test_macho_binary_resigns_with_stable_identity(tmp_path: Path) -> None:
    extension = tmp_path / "_native.abi3.so"
    extension.write_bytes(_signed_macho(b"\x22" * 32))

    with patch("pyhermit_build.subprocess.run") as run:
        normalize_macho_binary(extension)

    run.assert_called_once_with(
        [
            "codesign",
            "--force",
            "--sign",
            "-",
            "--identifier",
            "org.oaeiml.pyhermit._native",
            "--timestamp=none",
            str(extension),
        ],
        check=True,
    )


def test_macho_uuid_requires_exactly_one_load_command(tmp_path: Path) -> None:
    extension = tmp_path / "_native.abi3.so"
    header = bytearray(_macho()[:32])
    struct.pack_into("<I", header, 16, 0)
    extension.write_bytes(header)

    with pytest.raises(RuntimeError, match="exactly one LC_UUID"):
        normalize_macho_uuid(extension)
