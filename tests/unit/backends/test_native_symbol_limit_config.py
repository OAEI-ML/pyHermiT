"""Public configuration and compatibility gates for native symbol-index limits."""

from __future__ import annotations

import importlib
import inspect
import struct

import pytest
from tests.unit.backends.test_dispatch import native_module
from tests.unit.backends.test_native_adapter import _compiled, _extension

import pyhermit.backends.native as native_backend
from pyhermit.backends.dispatch import select_backend_factory
from pyhermit.backends.native_input import HEADER_SIZE, SectionKind, encode_config
from pyhermit.config import ReasonerConfig
from pyhermit.events import CancellationSource
from pyhermit.exceptions import BackendVersionError, NativeBackendUnavailableError


@pytest.mark.parametrize("value", [True, False, 1.5, "1024", object()])
def test_symbol_limit_rejects_invalid_types(value: object) -> None:
    with pytest.raises(TypeError, match="max_native_symbol_index_bytes"):
        ReasonerConfig(max_native_symbol_index_bytes=value)  # type: ignore[arg-type]


@pytest.mark.parametrize("value", [0, -1, 1 << 64, 1 << 100])
def test_symbol_limit_rejects_out_of_range_integers(value: int) -> None:
    with pytest.raises(ValueError, match="max_native_symbol_index_bytes"):
        ReasonerConfig(max_native_symbol_index_bytes=value)


def test_symbol_limit_is_keyword_only_and_default_identity_is_unchanged() -> None:
    signature = inspect.signature(ReasonerConfig)
    parameter = signature.parameters["max_native_symbol_index_bytes"]
    assert parameter.kind is inspect.Parameter.KEYWORD_ONLY
    default = ReasonerConfig()
    explicit_default = ReasonerConfig(max_native_symbol_index_bytes=None)
    assert default == explicit_default
    assert "max_native_symbol_index_bytes" not in default.as_dict()
    assert default.semantic_items() == explicit_default.semantic_items()
    assert encode_config(default) == encode_config(explicit_default)
    configured = ReasonerConfig(max_native_symbol_index_bytes=(1 << 64) - 1)
    assert configured.as_dict()["max_native_symbol_index_bytes"] == (1 << 64) - 1
    assert list(configured.as_dict()) == sorted(configured.as_dict())


def test_explicit_limit_adds_one_optional_section_without_changing_config_record() -> None:
    def sections(data: bytes) -> dict[int, bytes]:
        count = struct.unpack_from("<I", data, 32)[0]
        result = {}
        for index in range(count):
            directory = HEADER_SIZE + index * 32
            kind = struct.unpack_from("<H", data, directory)[0]
            offset, length = struct.unpack_from("<QQ", data, directory + 8)
            result[kind] = data[offset : offset + length]
        return result

    baseline = sections(encode_config(ReasonerConfig()))
    configured = sections(encode_config(ReasonerConfig(max_native_symbol_index_bytes=8192)))
    assert baseline.keys() == {SectionKind.CONFIG}
    assert configured == {
        **baseline,
        SectionKind.NATIVE_SYMBOL_INDEX_LIMIT: struct.pack("<Q", 8192),
    }


def test_explicit_limit_rejects_python_without_probing_native(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(_name: str) -> None:
        raise AssertionError("native import was attempted")

    monkeypatch.setattr(importlib, "import_module", forbidden)
    with pytest.raises(NativeBackendUnavailableError) as caught:
        select_backend_factory(ReasonerConfig(backend="python", max_native_symbol_index_bytes=1))
    assert caught.value.context["reason"] == "native_symbol_index_backend_mismatch"


def test_explicit_auto_limit_never_falls_back_when_native_is_absent(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def absent(name: str) -> None:
        raise ModuleNotFoundError("absent", name=name)

    monkeypatch.delenv("PYHERMIT_BACKEND", raising=False)
    monkeypatch.setattr(importlib, "import_module", absent)
    with pytest.raises(NativeBackendUnavailableError) as caught:
        select_backend_factory(ReasonerConfig(max_native_symbol_index_bytes=1))
    assert caught.value.context["reason"] == "not_installed"


@pytest.mark.parametrize("backend", ["auto", "native", "verify"])
def test_explicit_limit_rejects_an_older_native_extension(
    monkeypatch: pytest.MonkeyPatch,
    backend: str,
) -> None:
    monkeypatch.delenv("PYHERMIT_BACKEND", raising=False)
    module = native_module()
    monkeypatch.setattr(importlib, "import_module", lambda _name: module)
    with pytest.raises(BackendVersionError) as caught:
        select_backend_factory(ReasonerConfig(backend=backend, max_native_symbol_index_bytes=1))
    assert caught.value.context["reason"] == "native_symbol_index_limit_unavailable"


def test_direct_adapter_rejects_unsupported_limit_before_creating_native_session(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    module, handles, sessions = _extension()
    factory = native_backend.NativeBackendFactory(module)

    class Codec:
        def encode_ontology(self, _ontology: object) -> bytes:
            return b"ontology"

        def encode_config(self, _config: object) -> bytes:
            return b"config"

    monkeypatch.setattr(native_backend, "_load_input_codec", Codec)
    with pytest.raises(BackendVersionError) as caught:
        factory.create_session(
            _compiled(), ReasonerConfig(max_native_symbol_index_bytes=1), CancellationSource().token
        )
    assert caught.value.context["reason"] == "native_symbol_index_limit_unavailable"
    assert not handles and not sessions
