from __future__ import annotations

import dataclasses
import threading
from unittest import mock

import pytest

from pyhermit.config import (
    BackendName,
    BlockingMode,
    ExistentialMode,
    FreshEntityPolicy,
    IndividualGrouping,
    ReasonerConfig,
    UnsupportedDatatypePolicy,
)
from pyhermit.events import CancellationSource, ProgressEvent, WarningEvent
from pyhermit.exceptions import (
    BackendError,
    FeatureNotImplementedError,
    OntologyInputError,
    PyHermiTError,
    ReasonerInterruptedError,
    ReasonerTimeoutError,
    ReasoningAbortedError,
    ResourceLimitError,
)


def test_reasoner_config_defaults_are_frozen_and_canonical() -> None:
    config = ReasonerConfig()
    assert config.backend is BackendName.AUTO
    assert config.fresh_entities is FreshEntityPolicy.ALLOW
    assert config.individual_grouping is IndividualGrouping.BY_NAME
    assert config.unsupported_datatypes is UnsupportedDatatypePolicy.ERROR
    assert config.blocking is BlockingMode.AUTO
    assert config.existentials is ExistentialMode.AUTO
    assert config.workers == 0
    assert list(config.as_dict()) == sorted(config.as_dict())
    with pytest.raises(dataclasses.FrozenInstanceError):
        config.workers = 2  # type: ignore[misc]


def test_reasoner_config_accepts_user_strings_but_stores_enums() -> None:
    config = ReasonerConfig(
        backend="native",  # type: ignore[arg-type]
        fresh_entities="disallow",  # type: ignore[arg-type]
        individual_grouping="by_same_as",  # type: ignore[arg-type]
        unsupported_datatypes="ignore_with_warning",  # type: ignore[arg-type]
        blocking="validated_anywhere",  # type: ignore[arg-type]
        existentials="creation_order",  # type: ignore[arg-type]
    )
    assert config.backend is BackendName.NATIVE
    assert config.fresh_entities is FreshEntityPolicy.DISALLOW
    assert config.individual_grouping is IndividualGrouping.BY_SAME_AS
    assert config.unsupported_datatypes is UnsupportedDatatypePolicy.IGNORE_WITH_WARNING
    assert config.blocking is BlockingMode.VALIDATED_ANYWHERE
    assert config.existentials is ExistentialMode.CREATION_ORDER


@pytest.mark.parametrize("timeout", [0, -1, float("inf"), float("nan"), True])
def test_reasoner_config_rejects_invalid_timeout(timeout: object) -> None:
    with pytest.raises((TypeError, ValueError)):
        ReasonerConfig(timeout=timeout)  # type: ignore[arg-type]


@pytest.mark.parametrize("workers", [-1, True, 1.5])
def test_reasoner_config_rejects_invalid_workers(workers: object) -> None:
    with pytest.raises((TypeError, ValueError)):
        ReasonerConfig(workers=workers)  # type: ignore[arg-type]


def test_callbacks_do_not_affect_configuration_identity_or_cache_items() -> None:
    def progress(event: object) -> None:
        pass

    def warnings(event: object) -> None:
        pass

    plain = ReasonerConfig()
    observed = ReasonerConfig(progress=progress, warnings=warnings)
    assert plain == observed
    assert plain.semantic_items() == observed.semantic_items()


def test_progress_and_warning_events_freeze_details() -> None:
    details = {"phase": "compile"}
    event = ProgressEvent(1, "op-1", "normalize", 2, 4, 0.25, details)
    warning = WarningEvent(1, "op-1", "UNSUPPORTED_DATATYPE", "ignored", details)
    details["phase"] = "changed"
    assert event.details == {"phase": "compile"}
    assert warning.details == {"phase": "compile"}
    with pytest.raises(TypeError):
        event.details["x"] = 1  # type: ignore[index]
    assert event.as_dict()["version"] == 1


def test_cancellation_interrupt_is_thread_safe_and_idempotent() -> None:
    source = CancellationSource()
    changed: list[bool] = []

    def interrupt() -> None:
        changed.append(source.interrupt("stop"))

    threads = [threading.Thread(target=interrupt) for _ in range(8)]
    for thread in threads:
        thread.start()
    for thread in threads:
        thread.join()
    assert changed.count(True) == 1
    with pytest.raises(ReasonerInterruptedError, match="stop"):
        source.token.check()


def test_cancellation_deadline_maps_to_timeout_error() -> None:
    with mock.patch("pyhermit.events.time.monotonic", side_effect=[100.0, 102.0]):
        token = CancellationSource(timeout=1.0).token
        with pytest.raises(ReasonerTimeoutError):
            token.check()


def test_cancellation_memory_limit_maps_to_stable_resource_error() -> None:
    token = CancellationSource(max_memory_bytes=10).token
    token.observe_memory(11)
    with pytest.raises(ResourceLimitError) as caught:
        token.check()
    assert caught.value.as_dict()["context"] == {
        "allowed": 10,
        "limit": "max_memory_bytes",
        "observed": 11,
    }


def test_cancellation_source_resets_the_same_token_between_operations() -> None:
    source = CancellationSource()
    token = source.token
    source.interrupt("first")
    with pytest.raises(ReasonerInterruptedError):
        token.check()

    retained = source.begin_operation(timeout=None, max_memory_bytes=5)

    assert retained is token
    assert not retained.interrupted
    assert retained.reason is None
    retained.observe_memory(6)
    with pytest.raises(ResourceLimitError):
        retained.check()


def test_cancellation_observer_tracks_operation_resets_and_interrupts() -> None:
    class Observer:
        def __init__(self) -> None:
            self.resets: list[tuple[float | None, int | None]] = []
            self.interruptions: list[str | None] = []

        def reset(
            self,
            timeout: float | None = None,
            max_memory_bytes: int | None = None,
        ) -> None:
            self.resets.append((timeout, max_memory_bytes))

        def interrupt(self, reason: str | None = None) -> bool:
            self.interruptions.append(reason)
            return True

    source = CancellationSource()
    observer = Observer()
    observer_id = source.token._attach(observer)

    source.begin_operation(timeout=2.5, max_memory_bytes=128)
    assert source.interrupt("native-stop")
    assert observer.resets == [(2.5, 128)]
    assert observer.interruptions == ["native-stop"]

    source.token._detach(observer_id)
    source.begin_operation(timeout=None, max_memory_bytes=None)
    assert observer.resets == [(2.5, 128)]


def test_exception_taxonomy_and_canonical_diagnostic() -> None:
    error = FeatureNotImplementedError("keys are not available", feature_id="OWL_HAS_KEY")
    assert isinstance(error, (PyHermiTError, NotImplementedError))
    assert error.as_dict() == {
        "code": "FEATURE_NOT_IMPLEMENTED",
        "context": {"feature_id": "OWL_HAS_KEY"},
        "message": "keys are not available",
        "type": "FeatureNotImplementedError",
    }
    assert issubclass(OntologyInputError, PyHermiTError)
    assert issubclass(ReasoningAbortedError, PyHermiTError)
    assert issubclass(BackendError, PyHermiTError)
