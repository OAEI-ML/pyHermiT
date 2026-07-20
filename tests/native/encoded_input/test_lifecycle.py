"""Borrowed-column lifetime, thread, fork, and panic containment coverage."""

# SPDX-License-Identifier: LGPL-3.0-or-later

from __future__ import annotations

import mmap
import os
import struct
from concurrent.futures import ThreadPoolExecutor
from contextlib import suppress
from pathlib import Path

import pyowl_core
import pytest
from pyowl_core.backends.native_views import produce_encoded_structural_view_v1

import pyhermit._native as native
from pyhermit.encoded_input import ENCODED_NATIVE_FEATURE
from pyhermit.exceptions import BackendPoisonedError

_OPTIONS = pyowl_core.LoadOptions(
    imports=pyowl_core.ImportPolicy.IGNORE,
    backend=pyowl_core.BackendPreference.PYTHON,
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


def _direct_columns() -> tuple[object, dict[str, memoryview]]:
    snapshot = pyowl_core.load_snapshot(
        b"Prefix(:=<urn:lifecycle#>) Ontology(<urn:lifecycle> "
        b"Declaration(Class(:A)) Declaration(Class(:B)))",
        options=_OPTIONS,
    )
    encoded = produce_encoded_structural_view_v1(snapshot)
    return encoded, dict(encoded.buffers)


def _validate(
    columns: dict[str, memoryview],
    *,
    posting_mode: int = 0,
    postings: memoryview | None = None,
) -> None:
    selected = memoryview(b"") if postings is None else postings
    assert (
        native._validate_encoded_selection_v1(
            posting_mode=posting_mode,
            postings=selected,
            **columns,
        )
        is None
    )


def _slice_record(
    columns: dict[str, memoryview],
    *,
    member_tokens: tuple[bytes, ...] = (),
    anonymous_scope_maps: tuple[memoryview, ...] = (),
) -> tuple[object, ...]:
    return (
        0,
        memoryview(b""),
        member_tokens,
        anonymous_scope_maps,
        *(columns[name] for name in _SLICE_COLUMN_ORDER),
    )


def test_mmap_columns_are_borrowed_for_one_call_and_release_cleanly(tmp_path: Path) -> None:
    encoded, original = _direct_columns()
    names = tuple(original)
    payload = b"".join(bytes(original[name]) for name in names)
    path = tmp_path / "encoded-columns.bin"
    path.write_bytes(payload)
    with path.open("rb") as stream:
        mapping = mmap.mmap(stream.fileno(), 0, access=mmap.ACCESS_READ)
    exported = memoryview(mapping)
    cursor = 0
    columns: dict[str, memoryview] = {}
    for name in names:
        following = cursor + original[name].nbytes
        columns[name] = exported[cursor:following]
        cursor = following
    exported.release()
    postings = memoryview(struct.pack("<I", 1))
    try:
        assert cursor == len(mapping)
        assert all(value.readonly and value.obj is mapping for value in columns.values())
        _validate(columns, posting_mode=2, postings=postings)
        with pytest.raises(BufferError):
            mapping.close()
        for value in columns.values():
            value.release()
        mapping.close()
        assert mapping.closed
    finally:
        postings.release()
        for value in columns.values():
            with suppress(ValueError):
                value.release()
        if not mapping.closed:
            mapping.close()
        del encoded


def test_contextual_multi_slice_call_releases_every_borrow_after_return() -> None:
    encoded, columns = _direct_columns()
    context_mapping = mmap.mmap(-1, 64)
    context_mapping[:] = b"a" * 32 + b"b" * 32
    writable_scope = memoryview(context_mapping)
    scope_map = writable_scope.toreadonly()
    writable_scope.release()
    record = _slice_record(
        columns,
        member_tokens=(b"t" * 32,),
        anonymous_scope_maps=(scope_map,),
    )
    try:
        assert native._validate_encoded_slices_v1(slices=(record, record)) is None
        with pytest.raises(BufferError):
            context_mapping.close()
        del record
        scope_map.release()
        context_mapping.close()
        assert context_mapping.closed
        assert encoded.owner is not None
    finally:
        with suppress(ValueError):
            scope_map.release()
        if not context_mapping.closed:
            context_mapping.close()


def test_shared_immutable_columns_are_safe_across_python_threads() -> None:
    encoded, columns = _direct_columns()

    def preflight(index: int) -> int:
        if index % 2:
            _validate(
                columns,
                posting_mode=2,
                postings=memoryview(struct.pack("<I", 1)),
            )
        else:
            _validate(columns)
        return index

    with ThreadPoolExecutor(max_workers=8) as executor:
        observed = tuple(executor.map(preflight, range(64)))

    assert observed == tuple(range(64))
    assert encoded.owner is not None


@pytest.mark.skipif(not hasattr(os, "fork"), reason="requires POSIX fork")
def test_stateless_encoded_preflight_is_reusable_after_fork() -> None:
    encoded, columns = _direct_columns()
    read_fd, write_fd = os.pipe()
    child = os.fork()
    if child == 0:
        os.close(read_fd)
        try:
            _validate(columns, posting_mode=2, postings=memoryview(struct.pack("<I", 1)))
        except BaseException as error:
            os.write(write_fd, f"{type(error).__name__}:{error}".encode())
            os._exit(2)
        os.write(write_fd, b"ok")
        os._exit(0)

    os.close(write_fd)
    result = os.read(read_fd, 512)
    os.close(read_fd)
    _, status = os.waitpid(child, 0)
    assert os.waitstatus_to_exitcode(status) == 0
    assert result == b"ok"
    _validate(columns)
    assert encoded.owner is not None


def test_encoded_selection_panic_is_redacted_and_does_not_poison_later_calls(
    capsys: pytest.CaptureFixture[str],
) -> None:
    encoded, columns = _direct_columns()

    with pytest.raises(BackendPoisonedError) as captured:
        native._debug_encoded_selection_panic_v1()

    diagnostics = capsys.readouterr()
    assert captured.value.code == "NATIVE_PANIC"
    assert str(captured.value) == "native encoded-selection validation panic was contained"
    assert "content must not escape" not in diagnostics.err
    _validate(columns)
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES
    assert encoded.owner is not None
