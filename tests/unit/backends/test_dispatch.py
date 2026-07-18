from __future__ import annotations

import importlib
from types import ModuleType

import pytest

from pyhermit import __version__
from pyhermit.backends.dispatch import (
    REQUIRED_NATIVE_FEATURES,
    _probe_native,
    backend_info,
    select_backend_factory,
)
from pyhermit.backends.python import PythonBackendFactory
from pyhermit.config import BackendName, ReasonerConfig
from pyhermit.exceptions import (
    BackendVersionError,
    NativeBackendUnavailableError,
)


def native_module(
    *,
    abi: int = 1,
    schema: int = 1,
    version: str = __version__,
    features: tuple[str, ...] | None = None,
) -> ModuleType:
    module = ModuleType("pyhermit._native")
    module.__version__ = version
    module.ABI_VERSION = abi
    module.IR_SCHEMA_VERSION = schema
    module.FEATURES = tuple(sorted(REQUIRED_NATIVE_FEATURES)) if features is None else features
    module.self_test = lambda: None
    return module


def test_explicit_python_never_probes_or_imports_native(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setenv("PYHERMIT_BACKEND", "native")

    def forbidden(_name: str) -> ModuleType:
        raise AssertionError("native import was attempted")

    monkeypatch.setattr(importlib, "import_module", forbidden)

    factory = select_backend_factory(ReasonerConfig(backend=BackendName.PYTHON))

    assert isinstance(factory, PythonBackendFactory)


def test_auto_falls_back_cleanly_and_forced_native_reports_reason(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def absent(name: str) -> ModuleType:
        raise ModuleNotFoundError("absent", name=name)

    monkeypatch.delenv("PYHERMIT_BACKEND", raising=False)
    monkeypatch.setattr(importlib, "import_module", absent)

    assert isinstance(select_backend_factory(ReasonerConfig()), PythonBackendFactory)
    with pytest.raises(NativeBackendUnavailableError) as caught:
        select_backend_factory(ReasonerConfig(backend="native"))
    assert caught.value.context["reason"] == "not_installed"


def test_constructor_choice_wins_and_invalid_environment_is_rejected(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setenv("PYHERMIT_BACKEND", "invalid")
    assert isinstance(
        select_backend_factory(ReasonerConfig(backend="python")),
        PythonBackendFactory,
    )
    with pytest.raises(ValueError, match="PYHERMIT_BACKEND"):
        select_backend_factory(ReasonerConfig())


def test_probe_validates_schema_features_and_self_test(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    module = native_module(schema=2)
    monkeypatch.setattr(importlib, "import_module", lambda _name: module)
    mismatch = _probe_native().availability
    assert not mismatch.available and mismatch.reason == "schema_mismatch"
    with pytest.raises(BackendVersionError):
        select_backend_factory(ReasonerConfig(backend="native"))

    incomplete = native_module(features=("wire",))
    monkeypatch.setattr(importlib, "import_module", lambda _name: incomplete)
    assert _probe_native().availability.reason == "incomplete_features"
    with pytest.raises(NativeBackendUnavailableError):
        select_backend_factory(ReasonerConfig(backend="native"))

    broken = native_module()

    def fail() -> None:
        raise RuntimeError("broken")

    broken.self_test = fail
    monkeypatch.setattr(importlib, "import_module", lambda _name: broken)
    assert _probe_native().availability.reason == "self_test_failed"


def test_probe_rejects_native_package_version_mismatch(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    module = native_module(version="0.1.0.other")
    monkeypatch.setattr(importlib, "import_module", lambda _name: module)

    availability = _probe_native().availability

    assert not availability.available
    assert availability.reason == "package_version_mismatch"
    with pytest.raises(BackendVersionError):
        select_backend_factory(ReasonerConfig(backend="native"))


def test_backend_info_is_stable_and_does_not_create_a_session(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    incomplete = native_module(features=("wire",))
    monkeypatch.setattr(importlib, "import_module", lambda _name: incomplete)
    monkeypatch.delenv("PYHERMIT_BACKEND", raising=False)

    status = backend_info()

    assert status.python.available
    assert not status.native.available
    assert status.native.reason == "incomplete_features"
    assert status.default_selection == "python"
