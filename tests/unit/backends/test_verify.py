"""Fail-closed exact differential behavior for verify mode."""

# SPDX-License-Identifier: LGPL-3.0-or-later

from __future__ import annotations

from collections.abc import Sequence

import pytest

from pyhermit.backends.protocol import (
    CheckResult,
    DeltaOutcome,
    HierarchyIds,
    RealizationIds,
)
from pyhermit.backends.verify import VerifyBackendSession
from pyhermit.exceptions import (
    BackendMismatchError,
    BackendPoisonedError,
    DisposedReasonerError,
    ReasonerInterruptedError,
)


class _Session:
    def __init__(self) -> None:
        self.fingerprint = "11" * 32
        self.check_result: object = CheckResult(True)
        self.closed = False
        self.reset_count = 0
        self.received_queries: tuple[object, ...] = ()

    @property
    def ontology_fingerprint(self) -> str:
        self._require_open()
        return self.fingerprint

    def check(self, query: object = None) -> object:
        self._require_open()
        return _raise_or_return(self.check_result)

    def check_many(self, queries: Sequence[object]) -> object:
        self._require_open()
        self.received_queries = tuple(queries)
        if isinstance(self.check_result, Exception):
            raise self.check_result
        return tuple(self.check_result for _ in queries)

    def classify_classes(self) -> HierarchyIds:
        self._require_open()
        return HierarchyIds(((0,), (1,)), ((1, 0),), 0, 1)

    def classify_object_properties(self) -> HierarchyIds:
        return self.classify_classes()

    def classify_data_properties(self) -> HierarchyIds:
        return self.classify_classes()

    def realize(self) -> RealizationIds:
        self._require_open()
        return RealizationIds(((0,),))

    def apply_delta(self, delta: object) -> DeltaOutcome:
        self._require_open()
        return DeltaOutcome.REBUILD_REQUIRED

    def reset_query_state(self) -> None:
        self._require_open()
        self.reset_count += 1

    def close(self) -> None:
        self.closed = True

    def _require_open(self) -> None:
        if self.closed:
            raise DisposedReasonerError("fake session is closed")


def _raise_or_return(value: object) -> object:
    if isinstance(value, Exception):
        raise value
    return value


def test_equal_results_are_returned_and_batches_are_snapshotted_once() -> None:
    native = _Session()
    python = _Session()
    session = VerifyBackendSession(native, python)  # type: ignore[arg-type]

    assert session.check() == CheckResult(True)
    assert session.classify_classes() == HierarchyIds(((0,), (1,)), ((1, 0),), 0, 1)
    assert session.realize() == RealizationIds(((0,),))
    assert session.check_many((object(), object())) == (CheckResult(True), CheckResult(True))
    assert native.received_queries == python.received_queries
    session.reset_query_state()
    assert (native.reset_count, python.reset_count) == (1, 1)


def test_equal_public_errors_are_re_raised_without_fallback() -> None:
    native = _Session()
    python = _Session()
    native.check_result = ReasonerInterruptedError("native wording")
    python.check_result = ReasonerInterruptedError("python wording")
    session = VerifyBackendSession(native, python)  # type: ignore[arg-type]

    with pytest.raises(ReasonerInterruptedError, match="native wording"):
        session.check()


def test_result_mismatch_poisoning_is_fail_closed_but_close_remains_available() -> None:
    native = _Session()
    python = _Session()
    python.check_result = CheckResult(False)
    session = VerifyBackendSession(native, python)  # type: ignore[arg-type]

    with pytest.raises(BackendMismatchError) as caught:
        session.check()
    assert caught.value.code == "VERIFY_BACKEND_MISMATCH"
    assert caught.value.context["reason"] == "result_mismatch"
    with pytest.raises(BackendPoisonedError):
        session.check()
    session.close()
    assert native.closed and python.closed


def test_exception_mismatch_is_not_treated_as_a_python_recovery() -> None:
    native = _Session()
    python = _Session()
    native.check_result = ReasonerInterruptedError("stop")
    session = VerifyBackendSession(native, python)  # type: ignore[arg-type]

    with pytest.raises(BackendMismatchError) as caught:
        session.check()
    assert caught.value.context["reason"] == "exception_mismatch"


def test_construction_rejects_different_ontology_fingerprints() -> None:
    native = _Session()
    python = _Session()
    python.fingerprint = "22" * 32
    with pytest.raises(BackendMismatchError):
        VerifyBackendSession(native, python)  # type: ignore[arg-type]


def test_close_is_paired_and_idempotent() -> None:
    native = _Session()
    python = _Session()
    session = VerifyBackendSession(native, python)  # type: ignore[arg-type]
    session.close()
    session.close()
    assert native.closed and python.closed
    with pytest.raises(DisposedReasonerError):
        session.check()
