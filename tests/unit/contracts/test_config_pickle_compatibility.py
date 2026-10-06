"""Restore trusted configuration states across optional native resource limits."""

# SPDX-License-Identifier: LGPL-3.0-or-later

from __future__ import annotations

import base64
import pickle
from dataclasses import FrozenInstanceError

import pytest

from pyhermit.config import ReasonerConfig

# Actual protocol-4 output from config.py at commit
# 977a83b3c9cb7fe85fa14cdf446f511fac7458e5, with deterministic=False,
# progress=builtins.print and warnings=builtins.len. Keep this historical state
# independent of the current dataclass field order and generated __getstate__.
_LEGACY_CONFIG_PICKLE = base64.b64decode(
    b"gASVHwEAAAAAAACMD3B5aGVybWl0LmNvbmZpZ5SMDlJlYXNvbmVyQ29uZmlnlJOUKYGUXZQoaACMC0JhY2tlbmRO"
    b"YW1llJOUjARhdXRvlIWUUpSJTohoAIwRRnJlc2hFbnRpdHlQb2xpY3mUk5SMBWFsbG93lIWUUpRoAIwSSW5kaXZp"
    b"ZHVhbEdyb3VwaW5nlJOUjAdieV9uYW1llIWUUpRoAIwZVW5zdXBwb3J0ZWREYXRhdHlwZVBvbGljeZSTlIwFZXJy"
    b"b3KUhZRSlGgAjAxCbG9ja2luZ01vZGWUk5RoB4WUUpRoAIwPRXhpc3RlbnRpYWxNb2RllJOUaAeFlFKUiIlLAE6J"
    b"jAhidWlsdGluc5SMBXByaW50lJOUaCGMA2xlbpSTlGViLg=="
)


# Actual protocol-4 output from release 0.2.2 at commit 71ab3bcd, with
# max_native_symbol_index_bytes=8192 and the same legacy callbacks/boolean.
_SYMBOL_LIMIT_CONFIG_PICKLE = base64.b64decode(
    b"gASVIgEAAAAAAACMD3B5aGVybWl0LmNvbmZpZ5SMDlJlYXNvbmVyQ29uZmlnlJOUKYGUXZQoaACMC0JhY2tlbmRO"
    b"YW1llJOUjARhdXRvlIWUUpSJTohoAIwRRnJlc2hFbnRpdHlQb2xpY3mUk5SMBWFsbG93lIWUUpRoAIwSSW5kaXZp"
    b"ZHVhbEdyb3VwaW5nlJOUjAdieV9uYW1llIWUUpRoAIwZVW5zdXBwb3J0ZWREYXRhdHlwZVBvbGljeZSTlIwFZXJy"
    b"b3KUhZRSlGgAjAxCbG9ja2luZ01vZGWUk5RoB4WUUpRoAIwPRXhpc3RlbnRpYWxNb2RllJOUaAeFlFKUiIlLAE6J"
    b"jAhidWlsdGluc5SMBXByaW50lJOUaCGMA2xlbpSTlE0AIGViLg=="
)


def test_config_restores_actual_pre_limit_pickle_without_shifting_fields() -> None:
    config = pickle.loads(_LEGACY_CONFIG_PICKLE)

    assert type(config) is ReasonerConfig
    assert config == ReasonerConfig(deterministic=False)
    assert config.max_native_symbol_index_bytes is None
    assert config.max_compile_work is None
    assert config.deterministic is False
    assert config.progress is print
    assert config.warnings is len
    assert config.semantic_items() == ReasonerConfig(deterministic=False).semantic_items()


def test_config_restores_actual_symbol_limit_pickle_without_shifting_fields() -> None:
    config = pickle.loads(_SYMBOL_LIMIT_CONFIG_PICKLE)

    assert type(config) is ReasonerConfig
    assert config == ReasonerConfig(max_native_symbol_index_bytes=8192, deterministic=False)
    assert config.max_compile_work is None
    assert config.max_native_symbol_index_bytes == 8192
    assert config.deterministic is False
    assert config.progress is print
    assert config.warnings is len


@pytest.mark.parametrize("limit", (None, 8_192, (1 << 64) - 1))
@pytest.mark.parametrize("work", (None, 1, (1 << 64) - 1))
@pytest.mark.parametrize("protocol", (4, 5))
def test_config_pickle_round_trip_preserves_option_and_callbacks(
    limit: int | None,
    work: int | None,
    protocol: int,
) -> None:
    config = ReasonerConfig(
        max_native_symbol_index_bytes=limit,
        max_compile_work=work,
        deterministic=False,
        progress=print,
        warnings=len,
    )

    restored = pickle.loads(pickle.dumps(config, protocol=protocol))

    assert restored == config
    assert hash(restored) == hash(config)
    assert not hasattr(restored, "__dict__")
    with pytest.raises(FrozenInstanceError):
        restored.deterministic = True
    assert restored.max_native_symbol_index_bytes == limit
    assert restored.max_compile_work == work
    assert restored.deterministic is False
    assert restored.progress is print
    assert restored.warnings is len
    assert restored.semantic_items() == config.semantic_items()


@pytest.mark.parametrize("missing_fields", (0, 1, 2))
@pytest.mark.parametrize("as_tuple", (False, True))
def test_config_restores_current_and_legacy_sequence_states(
    missing_fields: int,
    as_tuple: bool,
) -> None:
    expected = ReasonerConfig(deterministic=False)
    state = expected.__getstate__()
    if missing_fields:
        state = state[:-missing_fields]
    config = object.__new__(ReasonerConfig)

    config.__setstate__(tuple(state) if as_tuple else state)

    assert config == expected
    assert config.max_native_symbol_index_bytes is None
    assert config.max_compile_work is None


@pytest.mark.parametrize("state", (None, {}, "not a state", 17))
def test_config_pickle_rejects_invalid_state_type(state: object) -> None:
    config = object.__new__(ReasonerConfig)

    with pytest.raises(TypeError, match="list or tuple"):
        config.__setstate__(state)


@pytest.mark.parametrize("size", (0, 15, 19))
def test_config_pickle_rejects_unknown_state_length(size: int) -> None:
    config = object.__new__(ReasonerConfig)

    with pytest.raises(ValueError, match="field count"):
        config.__setstate__([None] * size)


@pytest.mark.parametrize("option", ("max_native_symbol_index_bytes", "max_compile_work"))
@pytest.mark.parametrize("limit", (True, 0, -1, 1 << 64))
def test_config_pickle_validates_restored_resource_limit(option: str, limit: object) -> None:
    state = ReasonerConfig().__getstate__()
    state[-2 if option == "max_native_symbol_index_bytes" else -1] = limit
    config = object.__new__(ReasonerConfig)

    with pytest.raises((TypeError, ValueError), match=option):
        config.__setstate__(state)


def test_config_pickle_validates_restored_legacy_values() -> None:
    state = ReasonerConfig().__getstate__()[:-2]
    state[13] = "not a boolean"
    config = object.__new__(ReasonerConfig)

    with pytest.raises(TypeError, match="deterministic must be bool"):
        config.__setstate__(state)
