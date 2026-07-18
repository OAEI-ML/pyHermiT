"""Exact development-time differential wrapper for the two complete backends.

SPDX-License-Identifier: LGPL-3.0-or-later

Verify mode deliberately executes both sessions. It never substitutes a Python answer after a
native failure: equal native/Python failures are re-raised, and every disagreement poisons the
wrapper and raises :class:`BackendMismatchError`.
"""

from __future__ import annotations

import os
import threading
from collections.abc import Callable, Iterator, Sequence
from contextlib import contextmanager, suppress
from dataclasses import dataclass, replace
from typing import TypeVar, cast

from pyhermit import __version__
from pyhermit.backends.protocol import (
    BackendFactory,
    BackendInfo,
    BackendSession,
    CheckResult,
    CompiledDelta,
    CompiledOntology,
    CompiledQuery,
    DeltaOutcome,
    HierarchyIds,
    RealizationIds,
)
from pyhermit.backends.python import PythonBackendFactory
from pyhermit.config import ReasonerConfig
from pyhermit.events import CancellationToken
from pyhermit.exceptions import (
    BackendMismatchError,
    BackendPoisonedError,
    BackendVersionError,
    ConcurrentMutationError,
    DisposedReasonerError,
    PyHermiTError,
    ReasonerStateError,
)

_T = TypeVar("_T")


@dataclass(frozen=True, slots=True)
class _Outcome:
    value: object | None = None
    error: Exception | None = None


class VerifyBackendFactory:
    """Create paired native/Python sessions over the exact same compiled ontology."""

    __slots__ = ("_info", "_native", "_python")

    def __init__(self, native: BackendFactory) -> None:
        if not callable(getattr(native, "create_session", None)):
            raise TypeError("native must satisfy BackendFactory")
        native_info = native.info
        if not isinstance(native_info, BackendInfo) or native_info.name != "native":
            raise BackendVersionError(
                "verify mode requires a native backend factory",
                context={"reason": "verify_native_factory_invalid"},
            )
        python = PythonBackendFactory()
        python_info = python.info
        _require_matching_info(native_info, python_info)
        self._native = native
        self._python = python
        self._info = BackendInfo(
            name="verify",
            package_version=__version__,
            ir_schema_version=native_info.ir_schema_version,
            implementation_version=(
                f"verify:{native_info.implementation_version}+{python_info.implementation_version}"
            ),
            core_package_version=native_info.core_package_version,
            core_api_version=native_info.core_api_version,
            core_model_schema_version=native_info.core_model_schema_version,
            core_wire_format_version=native_info.core_wire_format_version,
            core_adapter_protocol_version=native_info.core_adapter_protocol_version,
            complete_features=native_info.complete_features & python_info.complete_features,
            accelerated=False,
        )

    @property
    def info(self) -> BackendInfo:
        return self._info

    def create_session(
        self,
        ontology: CompiledOntology,
        config: ReasonerConfig,
        cancellation: CancellationToken,
    ) -> VerifyBackendSession:
        native = self._native.create_session(ontology, config, cancellation)
        try:
            # Verify mode has one user-visible operation.  The Python session is a semantic
            # shadow and must not replay progress/warning side effects after the native call.
            # Cancellation and every semantic option remain shared exactly.
            shadow_config = replace(config, progress=None, warnings=None)
            python = self._python.create_session(ontology, shadow_config, cancellation)
        except BaseException:
            with suppress(Exception):
                native.close()
            raise
        try:
            return VerifyBackendSession(native, python, cancellation)
        except BaseException:
            with suppress(Exception):
                native.close()
            with suppress(Exception):
                python.close()
            raise


class VerifyBackendSession:
    """One fail-closed pair of complete sessions with exact result/error comparison."""

    __slots__ = (
        "_cancellation",
        "_closed",
        "_lock",
        "_mismatch_operation",
        "_native",
        "_owner_pid",
        "_python",
    )

    def __init__(
        self,
        native: BackendSession,
        python: BackendSession,
        cancellation: CancellationToken | None = None,
    ) -> None:
        for name, session in (("native", native), ("python", python)):
            if not all(
                callable(getattr(session, method, None))
                for method in (
                    "apply_delta",
                    "check",
                    "check_many",
                    "classify_classes",
                    "classify_data_properties",
                    "classify_object_properties",
                    "close",
                    "realize",
                    "reset_query_state",
                )
            ):
                raise TypeError(f"{name} must satisfy BackendSession")
        self._native = native
        self._python = python
        self._cancellation = cancellation
        self._owner_pid = os.getpid()
        self._lock = threading.Lock()
        self._closed = False
        self._mismatch_operation: str | None = None
        # Fail during construction rather than allowing differently bound sessions to run.
        _ = self.ontology_fingerprint

    @property
    def ontology_fingerprint(self) -> str:
        return self._compare(
            "ontology_fingerprint",
            lambda: self._native.ontology_fingerprint,
            lambda: self._python.ontology_fingerprint,
        )

    def check(self, query: CompiledQuery | None = None) -> CheckResult:
        return self._compare(
            "check",
            lambda: self._native.check(query),
            lambda: self._python.check(query),
        )

    def check_many(self, queries: object) -> tuple[CheckResult, ...]:
        if isinstance(queries, (str, bytes)) or not isinstance(queries, Sequence):
            raise TypeError("queries must be a sequence of compiled queries")
        values = tuple(queries)
        return self._compare(
            "check_many",
            lambda: self._native.check_many(values),
            lambda: self._python.check_many(values),
        )

    def classify_classes(self) -> HierarchyIds:
        return self._compare(
            "classify_classes",
            self._native.classify_classes,
            self._python.classify_classes,
        )

    def classify_object_properties(self) -> HierarchyIds:
        return self._compare(
            "classify_object_properties",
            self._native.classify_object_properties,
            self._python.classify_object_properties,
        )

    def classify_data_properties(self) -> HierarchyIds:
        return self._compare(
            "classify_data_properties",
            self._native.classify_data_properties,
            self._python.classify_data_properties,
        )

    def realize(self) -> RealizationIds:
        return self._compare("realize", self._native.realize, self._python.realize)

    def apply_delta(self, delta: CompiledDelta) -> DeltaOutcome:
        return self._compare(
            "apply_delta",
            lambda: self._native.apply_delta(delta),
            lambda: self._python.apply_delta(delta),
        )

    def reset_query_state(self) -> None:
        self._compare(
            "reset_query_state",
            self._native.reset_query_state,
            self._python.reset_query_state,
        )

    def close(self) -> None:
        if self._closed:
            return
        with self._operation("close", allow_poisoned=True):
            native = _capture(self._native.close)
            python = _capture(self._python.close)
            self._closed = True
            self._resolve("close", native, python)

    def _compare(
        self,
        operation: str,
        native_call: Callable[[], _T],
        python_call: Callable[[], _T],
    ) -> _T:
        with self._operation(operation):
            native = _capture(native_call)
            cancellation = self._cancellation
            if cancellation is not None and (
                cancellation.interrupted or cancellation.deadline_exceeded
            ):
                # The native call owns user-visible callbacks.  Once one of those callbacks or
                # an external thread cancels the shared token, running the callback-free Python
                # shadow can only manufacture a timing-dependent mismatch.  Preserve the native
                # error, or let the shared token raise before any shadow side effects occur.
                if native.error is not None:
                    raise native.error
                cancellation.check()
            python = _capture(python_call)
            return cast(_T, self._resolve(operation, native, python))

    def _resolve(self, operation: str, native: _Outcome, python: _Outcome) -> object:
        if native.error is not None or python.error is not None:
            if _same_error(native.error, python.error):
                assert native.error is not None
                raise native.error
            self._mismatch(
                operation,
                native,
                python,
                reason="exception_mismatch",
            )
        if type(native.value) is not type(python.value) or native.value != python.value:
            self._mismatch(operation, native, python, reason="result_mismatch")
        return native.value

    @contextmanager
    def _operation(
        self,
        operation: str,
        *,
        allow_poisoned: bool = False,
    ) -> Iterator[None]:
        if os.getpid() != self._owner_pid:
            raise ReasonerStateError(
                "verify backend session cannot be reused after fork",
                code="VERIFY_FORK",
            )
        if self._closed:
            raise DisposedReasonerError("verify backend session is closed")
        if self._mismatch_operation is not None and not allow_poisoned:
            raise BackendPoisonedError(
                "verify backend session is poisoned after a differential mismatch",
                code="VERIFY_MISMATCH_POISONED",
                context={"operation": self._mismatch_operation},
            )
        if not self._lock.acquire(blocking=False):
            raise ConcurrentMutationError("verify backend session already has an active operation")
        try:
            yield
        finally:
            self._lock.release()

    def _mismatch(
        self,
        operation: str,
        native: _Outcome,
        python: _Outcome,
        *,
        reason: str,
    ) -> None:
        self._mismatch_operation = operation
        raise BackendMismatchError(
            "native and Python backends disagree in verify mode",
            code="VERIFY_BACKEND_MISMATCH",
            context={
                "native": _outcome_kind(native),
                "operation": operation,
                "python": _outcome_kind(python),
                "reason": reason,
            },
        )


def _capture(call: Callable[[], object]) -> _Outcome:
    try:
        return _Outcome(value=call())
    except Exception as error:
        return _Outcome(error=error)


def _same_error(left: Exception | None, right: Exception | None) -> bool:
    if left is None or right is None or type(left) is not type(right):
        return False
    if isinstance(left, PyHermiTError) and isinstance(right, PyHermiTError):
        return left.code == right.code
    return True


def _outcome_kind(outcome: _Outcome) -> str:
    error = outcome.error
    if error is None:
        return type(outcome.value).__name__
    if isinstance(error, PyHermiTError):
        return f"{type(error).__name__}:{error.code}"
    return type(error).__name__


def _require_matching_info(native: BackendInfo, python: BackendInfo) -> None:
    fields = (
        "ir_schema_version",
        "core_package_version",
        "core_api_version",
        "core_model_schema_version",
        "core_wire_format_version",
        "core_adapter_protocol_version",
    )
    for field in fields:
        if getattr(native, field) != getattr(python, field):
            raise BackendVersionError(
                "native and Python backend metadata differ",
                context={"field": field, "reason": "verify_metadata_mismatch"},
            )


__all__ = ["VerifyBackendFactory", "VerifyBackendSession"]
