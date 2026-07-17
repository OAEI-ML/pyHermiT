"""Native ownership, cancellation, concurrency, fork, and panic containment tests."""

# SPDX-License-Identifier: LGPL-3.0-or-later

from __future__ import annotations

import os
import threading
import time
from collections.abc import Callable

import pytest
from tests.native.wire._builder import valid_documents

import pyhermit._native as native
from pyhermit.exceptions import (
    BackendMismatchError,
    BackendPoisonedError,
    ConcurrentMutationError,
    DisposedReasonerError,
    ReasonerInterruptedError,
    ReasonerStateError,
    ReasonerTimeoutError,
    ResourceLimitError,
)


def make_session(
    cancellation: native.CancellationHandle | None = None,
) -> native.NativeSession:
    ontology, config = valid_documents()
    return native.create_session(
        ontology,
        config,
        cancellation if cancellation is not None else native.CancellationHandle(),
    )


def capture_error(target: Callable[[], object], errors: list[BaseException]) -> None:
    try:
        target()
    except BaseException as error:
        errors.append(error)


def test_cancellation_configuration_is_validated() -> None:
    with pytest.raises(BackendMismatchError):
        native.CancellationHandle(timeout=0.0)
    with pytest.raises(BackendMismatchError):
        native.CancellationHandle(timeout=float("inf"))
    with pytest.raises(BackendMismatchError):
        native.CancellationHandle(max_memory_bytes=0)


def test_long_work_releases_gil_enforces_busy_and_is_cancellable() -> None:
    cancellation = native.CancellationHandle()
    session = make_session(cancellation)
    errors: list[BaseException] = []
    started = threading.Event()

    def work() -> None:
        started.set()
        capture_error(lambda: session._debug_long_work(1_000_000_000, 1024), errors)

    worker = threading.Thread(target=work)
    worker.start()
    assert started.wait(timeout=2)
    deadline = time.monotonic() + 2
    saw_busy = False
    while time.monotonic() < deadline and worker.is_alive():
        try:
            _ = session.ontology_fingerprint
        except ConcurrentMutationError:
            saw_busy = True
            break
    assert saw_busy, "same-session operation did not observe the native busy guard"
    with pytest.raises(ConcurrentMutationError):
        session.close()
    assert cancellation.interrupt("stop-for-test")
    assert not cancellation.interrupt("ignored-second-reason")
    worker.join(timeout=5)
    assert not worker.is_alive()
    assert len(errors) == 1
    assert isinstance(errors[0], ReasonerInterruptedError)
    assert str(errors[0]) == "stop-for-test"
    session.close()


def test_timeout_and_resource_limits_map_to_public_errors() -> None:
    timeout = native.CancellationHandle(timeout=0.001)
    timed_session = make_session(timeout)
    time.sleep(0.005)
    with pytest.raises(ReasonerTimeoutError):
        timed_session._debug_long_work(1)
    timed_session.close()

    resource = native.CancellationHandle(max_memory_bytes=8)
    resource.observe_memory(9)
    resource_session = make_session(resource)
    with pytest.raises(ResourceLimitError) as captured:
        resource_session._debug_long_work(1)
    assert captured.value.limit == "max_memory_bytes"
    assert captured.value.observed == 9
    assert captured.value.allowed == 8
    resource_session.close()


def test_independent_sessions_run_without_cross_session_busy_state() -> None:
    first = make_session()
    second = make_session()
    barrier = threading.Barrier(3)
    errors: list[BaseException] = []

    def work(session: native.NativeSession) -> None:
        barrier.wait()
        capture_error(lambda: session._debug_long_work(5_000_000, 4096), errors)

    threads = [threading.Thread(target=work, args=(session,)) for session in (first, second)]
    for thread in threads:
        thread.start()
    barrier.wait()
    for thread in threads:
        thread.join(timeout=5)
    assert all(not thread.is_alive() for thread in threads)
    assert errors == []
    first.close()
    second.close()


def test_event_queue_is_bounded_and_drained_after_reattachment() -> None:
    session = make_session()
    for _ in range(300):
        session._debug_long_work(0)
    events = session._drain_debug_events()
    assert len(events) == 256
    assert set(events) == {("debug_work_complete", 0)}
    assert session._drain_debug_events() == []
    session.close()


def test_panic_is_redacted_and_permanently_poisons_only_one_session(
    capsys: pytest.CaptureFixture[str],
) -> None:
    session = make_session()
    healthy = make_session()
    with pytest.raises(BackendPoisonedError) as captured:
        session._debug_inject_panic()
    diagnostics = capsys.readouterr()
    assert "content must not escape" not in str(captured.value)
    assert "content must not escape" not in diagnostics.err
    assert session.poisoned
    with pytest.raises(BackendPoisonedError):
        _ = session.ontology_fingerprint
    assert healthy.ontology_fingerprint == "11" * 32
    session.close()
    healthy.close()


@pytest.mark.skipif(not hasattr(os, "fork"), reason="requires POSIX fork")
def test_inherited_session_fails_before_touching_owned_state() -> None:
    session = make_session()
    read_fd, write_fd = os.pipe()
    child = os.fork()
    if child == 0:
        os.close(read_fd)
        try:
            _ = session.ontology_fingerprint
        except ReasonerStateError as error:
            os.write(write_fd, f"{type(error).__name__}:{error.code}".encode())
            os._exit(0)
        except BaseException as error:
            os.write(write_fd, f"unexpected:{type(error).__name__}".encode())
            os._exit(2)
        os.write(write_fd, b"unexpected:success")
        os._exit(3)

    os.close(write_fd)
    result = os.read(read_fd, 256).decode()
    os.close(read_fd)
    _, status = os.waitpid(child, 0)
    assert os.waitstatus_to_exitcode(status) == 0
    assert result == "ReasonerStateError:NATIVE_FORK"
    assert session.ontology_fingerprint == "11" * 32
    session.close()


def test_close_is_idempotent_and_rejects_future_operations() -> None:
    session = make_session()
    session.close()
    session.close()
    assert session.closed
    with pytest.raises(DisposedReasonerError):
        session.reset_query_state()
