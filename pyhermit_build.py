"""Small reproducibility helpers for pyHermiT's native build."""

from __future__ import annotations

import hashlib
import struct
import subprocess
from pathlib import Path


def _macho_variable_offsets(payload: bytearray) -> tuple[int, tuple[int, int] | None]:
    """Return the UUID offset and optional code-signature byte range."""

    if len(payload) < 32:
        raise RuntimeError("pyHermiT produced a truncated macOS native extension")
    formats = {
        b"\xce\xfa\xed\xfe": ("<", 28),
        b"\xcf\xfa\xed\xfe": ("<", 32),
        b"\xfe\xed\xfa\xce": (">", 28),
        b"\xfe\xed\xfa\xcf": (">", 32),
    }
    selected = formats.get(bytes(payload[:4]))
    if selected is None:
        raise RuntimeError("pyHermiT produced an unsupported macOS Mach-O format")
    endian, header_size = selected
    (command_count,) = struct.unpack_from(f"{endian}I", payload, 16)
    offset = header_size
    uuid_offsets: list[int] = []
    signature_range: tuple[int, int] | None = None
    for _ in range(command_count):
        if offset + 8 > len(payload):
            raise RuntimeError("pyHermiT produced malformed macOS load commands")
        command, command_size = struct.unpack_from(f"{endian}II", payload, offset)
        if command_size < 8 or offset + command_size > len(payload):
            raise RuntimeError("pyHermiT produced malformed macOS load commands")
        if command == 0x1B:  # LC_UUID
            if command_size != 24:
                raise RuntimeError("pyHermiT produced a malformed LC_UUID command")
            uuid_offsets.append(offset + 8)
        elif command == 0x1D:  # LC_CODE_SIGNATURE
            if command_size != 16 or signature_range is not None:
                raise RuntimeError("pyHermiT produced a malformed LC_CODE_SIGNATURE command")
            signature_offset, signature_size = struct.unpack_from(
                f"{endian}II", payload, offset + 8
            )
            signature_end = signature_offset + signature_size
            if signature_end > len(payload):
                raise RuntimeError("pyHermiT produced a truncated macOS code signature")
            signature_range = (signature_offset, signature_end)
        offset += command_size
    if len(uuid_offsets) != 1:
        raise RuntimeError(
            "pyHermiT macOS binary must have exactly one LC_UUID command, "
            f"found {len(uuid_offsets)}"
        )
    return uuid_offsets[0], signature_range


def normalize_macho_uuid(path: Path) -> None:
    """Replace one Mach-O LC_UUID payload with a content-derived UUID."""

    payload = bytearray(path.read_bytes())
    uuid_offset, signature_range = _macho_variable_offsets(payload)
    stable_payload = payload.copy()
    stable_payload[uuid_offset : uuid_offset + 16] = b"\0" * 16
    if signature_range is not None:
        signature_start, signature_end = signature_range
        stable_payload[signature_start:signature_end] = b"\0" * (signature_end - signature_start)
    payload[uuid_offset : uuid_offset + 16] = hashlib.sha256(stable_payload).digest()[:16]
    path.write_bytes(payload)


def normalize_macho_binary(path: Path) -> None:
    """Canonicalize the UUID and any existing Apple Silicon ad-hoc signature."""

    normalize_macho_uuid(path)
    _, signature_range = _macho_variable_offsets(bytearray(path.read_bytes()))
    if signature_range is None:
        return
    subprocess.run(
        [
            "codesign",
            "--force",
            "--sign",
            "-",
            "--identifier",
            "org.oaeiml.pyhermit._native",
            "--timestamp=none",
            str(path),
        ],
        check=True,
    )


__all__ = ["normalize_macho_binary", "normalize_macho_uuid"]
