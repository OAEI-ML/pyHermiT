"""Compatibility and fail-closed routing for encoded-native compilation budgets."""

# SPDX-License-Identifier: LGPL-3.0-or-later

from __future__ import annotations

import hashlib
import importlib
import inspect
from dataclasses import replace
from types import SimpleNamespace

import pyowl_core
import pytest
from tests.unit.backends.test_dispatch import native_module
from tests.unit.backends.test_native_adapter import (
    _compiled,
    _extension,
    _profile_fixture,
    _Session,
)

import pyhermit.backends.native as native_backend
from pyhermit.backends.dispatch import select_backend_factory
from pyhermit.backends.native_input import encode_config
from pyhermit.config import ReasonerConfig
from pyhermit.core import (
    capture_compatible_view,
    capture_compatible_view_deferred,
    compiler_cache_key,
    deferred_compiler_cache_template,
)
from pyhermit.encoded_input import ENCODED_NATIVE_FEATURE
from pyhermit.events import CancellationSource
from pyhermit.exceptions import BackendVersionError, NativeBackendUnavailableError

_RESOURCE_FEATURE = "native-compilation-resource-limits-v1"


@pytest.mark.parametrize("value", [True, False, 1.5, "1024", object()])
def test_work_limit_rejects_invalid_types(value: object) -> None:
    with pytest.raises(TypeError, match="max_compile_work"):
        ReasonerConfig(max_compile_work=value)  # type: ignore[arg-type]


@pytest.mark.parametrize("value", [0, -1, 1 << 64, 1 << 100])
def test_work_limit_rejects_out_of_range_integers(value: int) -> None:
    with pytest.raises(ValueError, match="max_compile_work"):
        ReasonerConfig(max_compile_work=value)


def test_work_limit_preserves_default_wire_and_semantic_items() -> None:
    default = ReasonerConfig()
    assert default == ReasonerConfig(max_compile_work=None)
    assert default.semantic_items() == (
        ("backend", "auto"),
        ("blocking", "auto"),
        ("buffer_changes", True),
        ("deterministic", True),
        ("disjunction_learning", True),
        ("existentials", "auto"),
        ("force_quasi_order_classification", False),
        ("fresh_entities", "allow"),
        ("individual_grouping", "by_name"),
        ("max_memory_bytes", None),
        ("timeout", None),
        ("unsupported_datatypes", "error"),
        ("workers", 0),
    )
    # Release 0.2.2's exact default wire digest; compilation work remains a private kwarg.
    assert hashlib.sha256(encode_config(default)).hexdigest() == (
        "8a711a465f41cfed59bb514ea73ea79fb3daf0c0fff9a8f8b8fee2df383a4fc9"
    )
    for maximum in (1, (1 << 64) - 1):
        configured = ReasonerConfig(max_compile_work=maximum)
        assert configured != default
        assert configured.as_dict()["max_compile_work"] == maximum
        assert list(configured.as_dict()) == sorted(configured.as_dict())
        assert encode_config(configured) == encode_config(default)


def test_optional_resource_limits_preserve_legacy_positional_constructor() -> None:
    signature = inspect.signature(ReasonerConfig)
    assert signature.parameters["max_compile_work"].kind is inspect.Parameter.KEYWORD_ONLY
    assert (
        signature.parameters["max_native_symbol_index_bytes"].kind is inspect.Parameter.KEYWORD_ONLY
    )
    positional = [
        value
        for value in signature.parameters.values()
        if value.kind is inspect.Parameter.POSITIONAL_OR_KEYWORD
    ]
    assert len(positional) == 16
    values = ReasonerConfig(deterministic=False, progress=print, warnings=len).__getstate__()[:16]
    config = ReasonerConfig(*values, max_compile_work=5, max_native_symbol_index_bytes=8192)
    assert config.deterministic is False
    assert config.progress is print
    assert config.warnings is len
    assert config.max_compile_work == 5
    assert config.max_native_symbol_index_bytes == 8192


def test_resource_limits_independently_partition_eager_and_deferred_cache_keys() -> None:
    snapshot, _profile = _profile_fixture()
    view = pyowl_core.apply_delta(snapshot, pyowl_core.OntologyDelta())
    captured = capture_compatible_view(view)
    deferred = capture_compatible_view_deferred(view)
    baseline = ReasonerConfig()
    configured = ReasonerConfig(
        max_memory_bytes=16384,
        max_native_symbol_index_bytes=8192,
        max_compile_work=1024,
    )
    configs = [baseline, configured]
    for option in ("max_memory_bytes", "max_native_symbol_index_bytes", "max_compile_work"):
        configs.append(replace(configured, **{option: None}))
    assert len({compiler_cache_key(captured, config) for config in configs}) == len(configs)
    assert len({deferred_compiler_cache_template(deferred, config) for config in configs}) == len(
        configs
    )
    assert encode_config(configured) == encode_config(replace(configured, max_compile_work=None))
    assert ReasonerConfig(max_compile_work=None).semantic_items() == baseline.semantic_items()


@pytest.mark.parametrize("selected_backend", ["python", "verify"])
@pytest.mark.parametrize("from_environment", [False, True])
def test_explicit_work_rejects_python_or_verify_without_probing_native(
    monkeypatch: pytest.MonkeyPatch,
    selected_backend: str,
    from_environment: bool,
) -> None:
    def forbidden(_name: str) -> None:
        raise AssertionError("native import was attempted")

    monkeypatch.setenv("PYHERMIT_BACKEND", selected_backend)
    monkeypatch.setattr(importlib, "import_module", forbidden)
    backend = "auto" if from_environment else selected_backend
    with pytest.raises(NativeBackendUnavailableError) as caught:
        select_backend_factory(ReasonerConfig(backend=backend, max_compile_work=1))
    assert caught.value.context["reason"] == "native_compile_work_backend_mismatch"


def test_explicit_auto_work_never_falls_back_when_native_is_absent(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def absent(name: str) -> None:
        raise ModuleNotFoundError("absent", name=name)

    monkeypatch.delenv("PYHERMIT_BACKEND", raising=False)
    monkeypatch.setattr(importlib, "import_module", absent)
    with pytest.raises(NativeBackendUnavailableError) as caught:
        select_backend_factory(ReasonerConfig(max_compile_work=1))
    assert caught.value.context["reason"] == "not_installed"


@pytest.mark.parametrize("backend", ["auto", "native"])
def test_explicit_work_rejects_an_older_native_extension(
    monkeypatch: pytest.MonkeyPatch,
    backend: str,
) -> None:
    monkeypatch.delenv("PYHERMIT_BACKEND", raising=False)
    module = native_module()
    monkeypatch.setattr(importlib, "import_module", lambda _name: module)
    with pytest.raises(BackendVersionError) as caught:
        select_backend_factory(ReasonerConfig(backend=backend, max_compile_work=1))
    assert caught.value.context["reason"] == "native_compile_work_unavailable"


@pytest.mark.parametrize("supported", [False, True])
def test_direct_scalar_adapter_rejects_work_before_encoding_or_constructing(
    monkeypatch: pytest.MonkeyPatch,
    supported: bool,
) -> None:
    module, handles, sessions = _extension()
    if supported:
        module.FEATURES = tuple(sorted((*module.FEATURES, _RESOURCE_FEATURE)))
    factory = native_backend.NativeBackendFactory(module)

    def forbidden() -> None:
        raise AssertionError("scalar input codec was requested")

    monkeypatch.setattr(native_backend, "_load_input_codec", forbidden)
    with pytest.raises(BackendVersionError) as caught:
        factory.create_session(
            _compiled(), ReasonerConfig(max_compile_work=1), CancellationSource().token
        )
    assert caught.value.context["reason"] == (
        "native_compile_work_requires_encoded_input"
        if supported
        else "native_compile_work_unavailable"
    )
    assert not handles and not sessions


@pytest.mark.parametrize("path", ["compiled", "captured", "deferred"])
@pytest.mark.parametrize("maximum", [None, 1, (1 << 64) - 1])
def test_every_encoded_handoff_forwards_explicit_work_and_omits_default(
    monkeypatch: pytest.MonkeyPatch,
    path: str,
    maximum: int | None,
) -> None:
    module, _handles, _sessions = _extension()
    module.FEATURES = tuple(sorted((*module.FEATURES, _RESOURCE_FEATURE, ENCODED_NATIVE_FEATURE)))
    snapshot, _profile = _profile_fixture()
    view = (
        pyowl_core.apply_delta(snapshot, pyowl_core.OntologyDelta())
        if path == "deferred"
        else snapshot
    )
    captured = capture_compatible_view(view)
    config = ReasonerConfig(max_compile_work=maximum, max_memory_bytes=16384)
    fingerprint = "0" * 64 if path == "compiled" else compiler_cache_key(captured, config)
    received: dict[str, object] = {}

    def construct(**kwargs: object) -> _Session:
        received.update(kwargs)
        session = _Session(fingerprint)
        session.encoded_compiler_gil_released = False
        return session

    module._create_encoded_session_v1 = construct
    module._validate_encoded_columns_v1 = lambda **_kwargs: None
    module._validate_encoded_slices_v1 = lambda **_kwargs: None
    module._encoded_profile_slices_manifest_v1 = lambda **_kwargs: b"{}"
    codec = SimpleNamespace(
        encode_config=encode_config,
        encode_ontology_metadata=lambda _ontology: b"metadata",
        encode_encoded_session_metadata=lambda _captured, _config: b"metadata",
        encode_deferred_encoded_session_metadata=lambda *_args, **_kwargs: (b"metadata", None),
    )
    monkeypatch.setattr(native_backend, "_load_input_codec", lambda: codec)
    monkeypatch.setattr(native_backend, "_deferred_structural_mode", lambda _lease: "effective")
    monkeypatch.setattr(
        native_backend.NativeBackendFactory,
        "_encoded_session_request",
        lambda *_args, **_kwargs: (construct, (), {}, object()),
    )
    factory = native_backend.NativeBackendFactory(module)
    cancellation = CancellationSource().token
    if path == "compiled":
        session = factory._create_encoded_session_handoff(view, _compiled(), config, cancellation)
    else:
        if path == "deferred":
            captured = capture_compatible_view_deferred(view)
        session = factory._create_encoded_lifecycle_handoff(captured, config, cancellation)
    assert session is not None
    try:
        assert received["config"] == encode_config(config)
        assert received["cancellation"].resets == [(None, 16384)]
        if maximum is None:
            assert "max_compile_work" not in received
        else:
            assert received["max_compile_work"] == maximum
    finally:
        session.close()
