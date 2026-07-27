"""Borrowed-column lifetime, thread, fork, and panic containment coverage."""

# SPDX-License-Identifier: LGPL-3.0-or-later

from __future__ import annotations

import gc
import mmap
import os
import struct
import time
from concurrent.futures import ThreadPoolExecutor
from contextlib import suppress
from pathlib import Path

import pyowl_core
import pytest
from pyowl_core.backends.native_views import produce_encoded_structural_view_v1
from pyowl_core.exceptions import SnapshotInUseError

import pyhermit._native as native
from pyhermit import ReasonerConfig
from pyhermit.backends.native_input import encode_config, encode_encoded_session_metadata
from pyhermit.backends.native_wire import decode_check
from pyhermit.core import capture_compatible_view
from pyhermit.encoded_input import ENCODED_NATIVE_FEATURE
from pyhermit.exceptions import BackendPoisonedError, ReasonerInterruptedError

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
        b"Declaration(Class(:A)) Declaration(Class(:B)) "
        b"Declaration(ObjectProperty(:p)) Declaration(ObjectProperty(:q)) "
        b"SubObjectPropertyOf(:p :q) TransitiveObjectProperty(:q))",
        options=_OPTIONS,
    )
    encoded = produce_encoded_structural_view_v1(snapshot)
    return encoded, dict(encoded.buffers)


def _wide_declaration_columns(
    count: int = 5_000,
) -> tuple[object, dict[str, memoryview]]:
    declarations = b" ".join(
        f"Declaration(Class(<urn:lifecycle:poll#{index:05d}>))".encode() for index in range(count)
    )
    snapshot = pyowl_core.load_snapshot(
        b"Ontology(<urn:lifecycle:poll> " + declarations + b")",
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


def test_mmap_direct_session_owns_program_after_handoff_release(tmp_path: Path) -> None:
    source = pyowl_core.load_snapshot(
        b"Prefix(:=<urn:lifecycle#>) Ontology(<urn:lifecycle> "
        b"Declaration(Class(:A)) Declaration(Class(:B)) SubClassOf(:A :B))",
        options=_OPTIONS,
    )
    path = tmp_path / "direct-session.pyocore"
    path.write_bytes(pyowl_core.encode_snapshot(source))
    mapped = pyowl_core.open_snapshot(path, mmap=True, verify=True)
    config = ReasonerConfig()
    captured = capture_compatible_view(mapped)
    encoded = produce_encoded_structural_view_v1(mapped)
    columns = dict(encoded.buffers)
    slices = (_slice_record(columns),)

    assert all(type(value.obj) is mmap.mmap for value in columns.values())
    with pytest.raises(SnapshotInUseError):
        mapped.close()

    session = native._create_encoded_session_v1(
        slices=slices,
        metadata=encode_encoded_session_metadata(captured, config),
        config=encode_config(config),
        cancellation=native.CancellationHandle(),
    )
    assert session.encoded_compiler_gil_released is False
    del slices, columns, encoded, captured
    gc.collect()
    mapped.close()

    try:
        assert mapped.closed
        assert decode_check(session.check(None)).satisfiable
        assert session.classify_classes()
    finally:
        session.close()


def test_exact_bytes_columns_release_the_gil_and_packed_owner_is_released() -> None:
    encoded, columns = _direct_columns()
    source = encoded.owner
    config = ReasonerConfig()
    captured = capture_compatible_view(source)
    packed_owner = b"".join(bytes(columns[name]) for name in _SLICE_COLUMN_ORDER)
    packed_view = memoryview(packed_owner)
    packed_columns: dict[str, memoryview] = {}
    cursor = 0
    for name in _SLICE_COLUMN_ORDER:
        following = cursor + columns[name].nbytes
        packed_columns[name] = packed_view[cursor:following]
        cursor = following
    packed_view.release()
    record = _slice_record(packed_columns)

    assert cursor == len(packed_owner)
    assert all(value.obj is packed_owner for value in packed_columns.values())
    session = native._create_encoded_session_v1(
        slices=(record,),
        metadata=encode_encoded_session_metadata(captured, config),
        config=encode_config(config),
        cancellation=native.CancellationHandle(),
    )
    assert session.encoded_compiler_gil_released is True

    del record, packed_owner, captured, columns, encoded
    for value in packed_columns.values():
        value.release()
    packed_columns.clear()
    gc.collect()
    try:
        assert decode_check(session.check(None)).satisfiable
        assert session.classify_classes()
    finally:
        session.close()


def test_detached_scope_map_compilation_observes_cross_thread_interrupt_and_retries() -> None:
    encoded, columns = _direct_columns()
    source = encoded.owner
    config = ReasonerConfig()
    captured = capture_compatible_view(source)
    row_count = 50_000
    scope_bytes = b"".join(
        index.to_bytes(32, "big") + (row_count + index).to_bytes(32, "big")
        for index in range(row_count)
    )
    scope_map = memoryview(scope_bytes)
    record = _slice_record(
        columns,
        member_tokens=(b"m" * 32,),
        anonymous_scope_maps=(scope_map,),
    )
    cancellation = native.CancellationHandle()

    def interrupt_after_detached_poll() -> bool:
        deadline = time.monotonic() + 10.0
        while cancellation._debug_poll_count == 0:
            if time.monotonic() >= deadline:
                return False
            time.sleep(0.000_1)
        return cancellation.interrupt("cancel detached encoded scope compilation")

    with ThreadPoolExecutor(max_workers=1) as executor:
        interrupted = executor.submit(interrupt_after_detached_poll)
        with pytest.raises(
            ReasonerInterruptedError,
            match="cancel detached encoded scope compilation",
        ):
            native._create_encoded_session_v1(
                slices=(record,),
                metadata=encode_encoded_session_metadata(captured, config),
                config=encode_config(config),
                cancellation=cancellation,
            )
        assert interrupted.result(timeout=10.0)

    cancellation.reset()
    retry = native._create_encoded_session_v1(
        slices=(record,),
        metadata=encode_encoded_session_metadata(captured, config),
        config=encode_config(config),
        cancellation=cancellation,
    )
    assert retry.encoded_compiler_gil_released is True
    scope_map.release()
    del record, scope_bytes, captured, columns, encoded
    gc.collect()
    try:
        assert decode_check(retry.check(None)).satisfiable
    finally:
        retry.close()


def test_detached_source_traversal_observes_cross_thread_interrupt_and_retries() -> None:
    encoded, columns = _wide_declaration_columns()
    source = encoded.owner
    config = ReasonerConfig()
    captured = capture_compatible_view(source)
    record = _slice_record(columns)
    cancellation = native.CancellationHandle()

    def interrupt_inside_source_scan() -> bool:
        deadline = time.monotonic() + 10.0
        # Program preflight is checkpoint one. Reaching three proves that
        # detached source traversal crossed multiple bounded inner strides.
        while cancellation._debug_poll_count < 3:
            if time.monotonic() >= deadline:
                return False
            time.sleep(0.000_1)
        return cancellation.interrupt("cancel detached encoded source traversal")

    with ThreadPoolExecutor(max_workers=1) as executor:
        interrupted = executor.submit(interrupt_inside_source_scan)
        with pytest.raises(
            ReasonerInterruptedError,
            match="cancel detached encoded source traversal",
        ):
            native._create_encoded_session_v1(
                slices=(record,),
                metadata=encode_encoded_session_metadata(captured, config),
                config=encode_config(config),
                cancellation=cancellation,
                validate_profile=False,
            )
        assert interrupted.result(timeout=10.0)

    cancellation.reset()
    retry = native._create_encoded_session_v1(
        slices=(record,),
        metadata=encode_encoded_session_metadata(captured, config),
        config=encode_config(config),
        cancellation=cancellation,
        validate_profile=False,
    )
    try:
        assert retry.encoded_compiler_gil_released is True
        assert decode_check(retry.check(None)).satisfiable
    finally:
        retry.close()


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


def test_contextual_multi_slice_cancellation_is_transactional_and_reusable() -> None:
    encoded, columns = _direct_columns()
    record = _slice_record(columns, member_tokens=(b"t" * 32,))
    slices = (record, record)
    baseline = native._encoded_role_clause_slices_manifest_v1(slices=slices)

    cancellation = native.CancellationHandle()
    assert cancellation.interrupt("cancel encoded composite")
    with pytest.raises(
        ReasonerInterruptedError,
        match="cancel encoded composite",
    ) as interrupted:
        native._validate_encoded_slices_v1(
            slices=slices,
            cancellation=cancellation,
        )
    assert interrupted.value.code == "REASONER_INTERRUPTED"

    cancellation.reset()
    assert native._validate_encoded_slices_v1(slices=slices, cancellation=cancellation) is None

    source_phases = (
        "source-object-role",
        "source-data-role",
        "source-data-inclusion",
        "source-simple-role",
        "source-complex-role",
        "source-role-characteristic",
        "source-named-class",
        "source-slice",
    )
    expected_phases = (
        "program-preflight",
        "source-symbol",
        "source-symbol",
        "source-declaration-proof",
        *source_phases,
        *source_phases,
        "merged-object-role",
        "merged-data-role",
        "merged-named-class",
        "merged-data-inclusion",
        "merged-data-hierarchy",
        "merged-simple-role",
        "merged-complex-role",
        "merged-role-characteristic",
        "merged-object-role-hierarchy",
        "merged-role-semantics",
        "merged-role-automata",
        "merged-role-model",
        "merged-role-clause-publication",
    )
    for checkpoint, expected_phase in enumerate(expected_phases, start=1):
        with pytest.raises(ReasonerInterruptedError) as injected:
            native._debug_validate_encoded_slices_cancel_v1(
                slices=slices,
                cancel_at_checkpoint=checkpoint,
            )
        assert injected.value.code == "REASONER_INTERRUPTED"
        assert injected.value.context == {
            "checkpoint": str(checkpoint),
            "phase": expected_phase,
        }

    assert (
        native._debug_validate_encoded_slices_cancel_v1(
            slices=slices,
            cancel_at_checkpoint=len(expected_phases) + 1,
        )
        is None
    )
    assert native._encoded_role_clause_slices_manifest_v1(slices=slices) == baseline
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES
    assert encoded.owner is not None


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
