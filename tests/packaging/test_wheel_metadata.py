"""Regression tests for cross-platform generated wheel metadata."""

from __future__ import annotations

import base64
import csv
import hashlib
import io
import zipfile
from pathlib import Path

from pyhermit_build import normalize_wheel_metadata


def _record_row(name: str, payload: bytes) -> list[str]:
    digest = base64.urlsafe_b64encode(hashlib.sha256(payload).digest()).rstrip(b"=")
    return [name, f"sha256={digest.decode('ascii')}", str(len(payload))]


def test_normalize_wheel_metadata_rewrites_crlf_and_record_once(tmp_path: Path) -> None:
    wheel = tmp_path / "pyhermit-0.1.2-py3-none-any.whl"
    metadata_name = "pyhermit-0.1.2.dist-info/METADATA"
    record_name = "pyhermit-0.1.2.dist-info/RECORD"
    module_name = "pyhermit/__init__.py"
    metadata = b"Metadata-Version: 2.4\r\nName: pyHermiT\r\nVersion: 0.1.2\r\n"
    module = b'"""Runtime payload."""\n'
    record_buffer = io.StringIO(newline="")
    csv.writer(record_buffer, lineterminator="\r\n").writerows(
        [
            _record_row(metadata_name, metadata),
            _record_row(module_name, module),
            [record_name, "", ""],
        ]
    )
    with zipfile.ZipFile(wheel, "w", compression=zipfile.ZIP_DEFLATED) as archive:
        archive.writestr(metadata_name, metadata)
        archive.writestr(module_name, module)
        archive.writestr(record_name, record_buffer.getvalue().encode("utf-8"))

    normalize_wheel_metadata(wheel)
    once = wheel.read_bytes()
    normalize_wheel_metadata(wheel)
    assert wheel.read_bytes() == once

    with zipfile.ZipFile(wheel) as archive:
        normalized = archive.read(metadata_name)
        assert normalized == metadata.replace(b"\r\n", b"\n")
        assert archive.read(module_name) == module
        rows = list(csv.reader(io.StringIO(archive.read(record_name).decode("utf-8"))))

    assert next(row for row in rows if row[0] == metadata_name) == _record_row(
        metadata_name, normalized
    )
    assert next(row for row in rows if row[0] == record_name) == [record_name, "", ""]
