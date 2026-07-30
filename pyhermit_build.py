"""Small reproducibility helpers for pyHermiT's native build."""

from __future__ import annotations

import base64
import csv
import hashlib
import io
import os
import struct
import subprocess
import zipfile
from pathlib import Path


def normalize_wheel_metadata(path: Path) -> None:
    """Canonicalize generated wheel metadata to LF and refresh its RECORD row."""

    temporary = path.with_name(f".{path.name}.normalized")
    with zipfile.ZipFile(path) as source:
        members = source.infolist()
        names = [member.filename for member in members]
        if len(names) != len(set(names)):
            raise RuntimeError(f"pyHermiT wheel contains duplicate members: {path.name}")
        metadata_names = [name for name in names if name.endswith(".dist-info/METADATA")]
        record_names = [name for name in names if name.endswith(".dist-info/RECORD")]
        if len(metadata_names) != 1 or len(record_names) != 1:
            raise RuntimeError("pyHermiT wheel must contain exactly one METADATA and RECORD member")
        metadata_name = metadata_names[0]
        record_name = record_names[0]
        payloads = {member.filename: source.read(member) for member in members}
        comment = source.comment

    metadata = payloads[metadata_name]
    normalized_metadata = metadata.replace(b"\r\n", b"\n").replace(b"\r", b"\n")
    if normalized_metadata == metadata:
        return
    payloads[metadata_name] = normalized_metadata

    record_input = io.StringIO(payloads[record_name].decode("utf-8"), newline="")
    rows = list(csv.reader(record_input))
    metadata_rows = [row for row in rows if row and row[0] == metadata_name]
    record_rows = [row for row in rows if row and row[0] == record_name]
    if len(metadata_rows) != 1 or len(record_rows) != 1:
        raise RuntimeError("pyHermiT wheel RECORD does not bind METADATA and itself exactly once")
    digest = base64.urlsafe_b64encode(hashlib.sha256(normalized_metadata).digest())
    metadata_rows[0][1] = f"sha256={digest.rstrip(b'=').decode('ascii')}"
    metadata_rows[0][2] = str(len(normalized_metadata))
    record_rows[0][1:] = ["", ""]
    record_output = io.StringIO(newline="")
    csv.writer(record_output, lineterminator="\n").writerows(rows)
    payloads[record_name] = record_output.getvalue().encode("utf-8")

    try:
        with zipfile.ZipFile(temporary, "w") as target:
            target.comment = comment
            for member in members:
                target.writestr(member, payloads[member.filename])
        os.replace(temporary, path)
    finally:
        temporary.unlink(missing_ok=True)


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


__all__ = ["normalize_macho_binary", "normalize_macho_uuid", "normalize_wheel_metadata"]
