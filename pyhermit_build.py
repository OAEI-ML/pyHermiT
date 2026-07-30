"""Small reproducibility helpers for pyHermiT's native build."""

from __future__ import annotations

import hashlib
import struct
from pathlib import Path


def normalize_macho_uuid(path: Path) -> None:
    """Replace one Mach-O LC_UUID payload with a content-derived UUID."""

    payload = bytearray(path.read_bytes())
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
        offset += command_size
    if len(uuid_offsets) != 1:
        raise RuntimeError(
            "pyHermiT macOS binary must have exactly one LC_UUID command, "
            f"found {len(uuid_offsets)}"
        )
    uuid_offset = uuid_offsets[0]
    payload[uuid_offset : uuid_offset + 16] = b"\0" * 16
    payload[uuid_offset : uuid_offset + 16] = hashlib.sha256(payload).digest()[:16]
    path.write_bytes(payload)


__all__ = ["normalize_macho_uuid"]
