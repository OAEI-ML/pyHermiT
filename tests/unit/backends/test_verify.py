"""Fail-closed exact differential behavior for verify mode."""

# SPDX-License-Identifier: LGPL-3.0-or-later

from __future__ import annotations

from collections.abc import Callable, Sequence
from types import SimpleNamespace

import pytest

from pyhermit.backends.protocol import (
    BackendInfo,
    CheckResult,
    CompiledOntology,
    DeltaOutcome,
    HierarchyIds,
    RealizationIds,
)
from pyhermit.backends.verify import VerifyBackendFactory, VerifyBackendSession
from pyhermit.config import ReasonerConfig
from pyhermit.events import CancellationSource, CancellationToken
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
        self.check_count = 0
        self.closed = False
        self.reset_count = 0
        self.received_queries: tuple[object, ...] = ()

    @property
    def ontology_fingerprint(self) -> str:
        self._require_open()
        return self.fingerprint

    def check(self, query: object = None) -> object:
        self._require_open()
        self.check_count += 1
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


class _Factory:
    def __init__(self, name: str, session: _Session) -> None:
        self.session = session
        self.config: ReasonerConfig | None = None
        self._info = BackendInfo(
            name=name,  # type: ignore[arg-type]
            package_version="0.1.1",
            ir_schema_version=1,
            implementation_version=f"{name}-test",
            core_package_version="0.2.0",
            core_api_version=(1, 0),
            core_model_schema_version=2,
            core_wire_format_version=(1, 2),
            core_adapter_protocol_version=1,
            complete_features=frozenset({"full_reasoner"}),
            accelerated=name == "native",
        )

    @property
    def info(self) -> BackendInfo:
        return self._info

    def create_session(
        self,
        _ontology: object,
        config: ReasonerConfig,
        _cancellation: CancellationToken,
    ) -> _Session:
        self.config = config
        return self.session


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


def test_shared_cancellation_after_native_skips_the_timing_dependent_shadow() -> None:
    cancellation = CancellationSource()
    cancellation.begin_operation()

    class InterruptingSession(_Session):
        def check(self, query: object = None) -> object:
            self._require_open()
            self.check_count += 1
            cancellation.interrupt("cancelled during native callback")
            return CheckResult(True)

    native = InterruptingSession()
    python = _Session()
    session = VerifyBackendSession(  # type: ignore[arg-type]
        native,
        python,
        cancellation.token,
    )

    with pytest.raises(ReasonerInterruptedError, match="native callback"):
        session.check()
    assert native.check_count == 1
    assert python.check_count == 0


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


def test_verify_factory_suppresses_callbacks_only_on_python_shadow(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    native = _Factory("native", _Session())
    python = _Factory("python", _Session())
    monkeypatch.setattr("pyhermit.backends.verify.PythonBackendFactory", lambda: python)

    def progress(_event: object) -> None:
        return None

    def warning(_event: object) -> None:
        return None

    config = ReasonerConfig(progress=progress, warnings=warning)

    factory = VerifyBackendFactory(native)  # type: ignore[arg-type]
    session = factory.create_session(object(), config, CancellationToken())  # type: ignore[arg-type]

    assert native.config is config
    assert python.config is not None
    assert python.config.progress is None
    assert python.config.warnings is None
    assert python.config.semantic_items() == config.semantic_items()
    session.close()


def test_verify_factory_forwards_the_private_encoded_gate(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    class NativeFactory(_Factory):
        def __init__(self) -> None:
            super().__init__("native", _Session())
            self.validated: list[object] = []
            self.profile_validated: list[tuple[object, object, object, object, object]] = []

        def _validate_encoded_handoff(self, view: object) -> None:
            self.validated.append(view)

        def _validate_encoded_profile_handoff(
            self,
            view: object,
            profile: object,
            unsupported_datatypes: object,
            cancellation: object,
            *,
            max_memory_bytes: object,
        ) -> None:
            self.profile_validated.append(
                (
                    view,
                    profile,
                    unsupported_datatypes,
                    cancellation,
                    max_memory_bytes,
                )
            )

    native = NativeFactory()
    python = _Factory("python", _Session())
    monkeypatch.setattr("pyhermit.backends.verify.PythonBackendFactory", lambda: python)
    factory = VerifyBackendFactory(native)  # type: ignore[arg-type]
    view = object()
    profile = object()
    policy = object()
    cancellation = CancellationToken()

    factory._validate_encoded_handoff(view)
    factory._validate_encoded_profile_handoff(
        view,
        profile,
        policy,
        cancellation,
        max_memory_bytes=4_096,
    )

    assert native.validated == [view]
    assert native.profile_validated == [(view, profile, policy, cancellation, 4_096)]


def test_verify_factory_pairs_direct_native_compilation_with_scalar_shadow(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    expected_digest = "ab" * 32
    native_session = _Session()
    native_session.compiler_digest = expected_digest
    native_session.ingestion_counters = {"encoded_buffer_count": 1}
    context = SimpleNamespace(compiler_digest=expected_digest)
    native_session._encoded_service_context = lambda: context

    class NativeFactory(_Factory):
        def __init__(self) -> None:
            super().__init__("native", native_session)
            self.direct_calls: list[tuple[object, object, object, bool]] = []

        def _create_encoded_lifecycle_handoff(
            self,
            captured: object,
            config: object,
            cancellation: object,
            *,
            validate_profile: bool,
        ) -> _Session:
            self.direct_calls.append((captured, config, cancellation, validate_profile))
            return native_session

    native = NativeFactory()
    python = _Factory("python", _Session())
    monkeypatch.setattr("pyhermit.backends.verify.PythonBackendFactory", lambda: python)
    captured = object()
    compiled = object.__new__(CompiledOntology)
    config = ReasonerConfig()
    cancellation = CancellationToken()

    def compile_bundle(
        actual_captured: object,
        actual_config: object,
        *,
        cancelled: Callable[[], bool],
    ) -> tuple[object, object, CompiledOntology]:
        assert actual_captured is captured
        assert actual_config is config
        assert cancelled() is False
        return object(), object(), compiled

    def compiler_digest(actual: object) -> str:
        assert actual is compiled
        return expected_digest

    monkeypatch.setattr("pyhermit.backends.verify.compile_captured_bundle", compile_bundle)
    monkeypatch.setattr("pyhermit.backends.verify.canonical_compiler_digest", compiler_digest)
    factory = VerifyBackendFactory(native)  # type: ignore[arg-type]

    session = factory._create_encoded_lifecycle_handoff(  # type: ignore[arg-type]
        captured,
        config,
        cancellation,
        validate_profile=False,
    )

    assert session is not None
    assert native.direct_calls == [(captured, config, cancellation, False)]
    assert session.compiler_digest == expected_digest
    assert session.ingestion_counters == {"encoded_buffer_count": 1}
    assert session._encoded_service_context() is context
    assert session.check() == CheckResult(True)
    session.close()
    assert native_session.closed
    assert python.session.closed
    with pytest.raises(DisposedReasonerError):
        _ = session.compiler_digest


def test_verify_factory_discards_native_candidate_on_compiler_digest_mismatch(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    native_session = _Session()
    native_session.compiler_digest = "00" * 32

    class NativeFactory(_Factory):
        def _create_encoded_lifecycle_handoff(
            self,
            _captured: object,
            _config: object,
            _cancellation: object,
            *,
            validate_profile: bool,
        ) -> _Session:
            assert validate_profile
            return native_session

    native = NativeFactory("native", native_session)
    python = _Factory("python", _Session())
    monkeypatch.setattr("pyhermit.backends.verify.PythonBackendFactory", lambda: python)
    monkeypatch.setattr(
        "pyhermit.backends.verify.compile_captured_bundle",
        lambda *_args, **_kwargs: (object(), object(), object()),
    )
    monkeypatch.setattr(
        "pyhermit.backends.verify.canonical_compiler_digest",
        lambda _compiled: "11" * 32,
    )
    factory = VerifyBackendFactory(native)  # type: ignore[arg-type]

    with pytest.raises(BackendMismatchError) as caught:
        factory._create_encoded_lifecycle_handoff(  # type: ignore[arg-type]
            object(),
            ReasonerConfig(),
            CancellationToken(),
        )

    assert caught.value.code == "VERIFY_BACKEND_MISMATCH"
    assert caught.value.context == {
        "native": "str",
        "operation": "compiler_digest",
        "python": "str",
        "reason": "compiler_digest_mismatch",
    }
    assert native_session.closed
    assert python.config is None
