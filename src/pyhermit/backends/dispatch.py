"""Side-effect-light backend probing and one-time session selection.

SPDX-License-Identifier: LGPL-3.0-or-later
"""

from __future__ import annotations

import importlib
import os
import sys
import sysconfig
from dataclasses import dataclass
from types import ModuleType
from typing import Literal, cast

from pyhermit._version import __version__
from pyhermit.backends.protocol import (
    COMPILED_IR_SCHEMA_VERSION,
    BackendAvailability,
    BackendFactory,
    BackendStatus,
)
from pyhermit.config import BackendName, ReasonerConfig
from pyhermit.core import current_core_versions
from pyhermit.exceptions import (
    BackendVersionError,
    NativeBackendUnavailableError,
)

NATIVE_ABI_VERSION = 1
REQUIRED_NATIVE_FEATURES = frozenset(
    {
        "classification",
        "full_reasoner",
        "incremental_updates",
        "realization",
    }
)


@dataclass(frozen=True, slots=True)
class _NativeProbe:
    availability: BackendAvailability
    module: ModuleType | None = None


def backend_info() -> BackendStatus:
    """Report backend availability without creating a reasoning session."""

    from pyhermit.backends.python import PythonBackendFactory

    environment = os.environ.get("PYHERMIT_BACKEND")
    python = PythonBackendFactory().info
    native = _probe_native().availability
    default: Literal["python", "native"] = "native" if native.available else "python"
    core = current_core_versions()
    return BackendStatus(
        environment,
        default,
        BackendAvailability(
            "python",
            True,
            python.implementation_version,
            python.ir_schema_version,
            None,
        ),
        native,
        core.package_version,
        core.api_version,
    )


def select_backend_factory(config: ReasonerConfig) -> BackendFactory:
    """Select exactly once, with an explicit constructor choice over the environment."""

    if not isinstance(config, ReasonerConfig):
        raise TypeError("config must be ReasonerConfig")
    selected = _effective_backend(config)
    if selected is BackendName.PYTHON:
        from pyhermit.backends.python import PythonBackendFactory

        return PythonBackendFactory()

    probe = _probe_native()
    if selected is BackendName.AUTO and not probe.availability.available:
        from pyhermit.backends.python import PythonBackendFactory

        return PythonBackendFactory()
    if not probe.availability.available:
        _raise_native_unavailable(probe.availability)

    # WPR4 owns the complete adapter. Importing this module is deliberately deferred until
    # a complete extension has passed its handshake, so Python mode never imports native code.
    try:
        native_adapter = importlib.import_module("pyhermit.backends.native")
    except ModuleNotFoundError as error:
        if error.name != "pyhermit.backends.native":
            raise
        raise NativeBackendUnavailableError(
            "the complete native extension is present but its Python adapter is unavailable",
            context={"reason": "adapter_not_installed"},
        ) from error
    factory_type = getattr(native_adapter, "NativeBackendFactory", None)
    if not isinstance(factory_type, type):
        raise NativeBackendUnavailableError(
            "the native backend adapter has no NativeBackendFactory",
            context={"reason": "adapter_invalid"},
        )
    factory = factory_type(probe.module)
    if not _is_backend_factory(factory):
        raise NativeBackendUnavailableError(
            "the native backend adapter does not satisfy BackendFactory",
            context={"reason": "adapter_invalid"},
        )
    native_factory = cast(BackendFactory, factory)
    if selected is BackendName.VERIFY:
        verifier_type = getattr(native_adapter, "VerifyBackendFactory", None)
        if not isinstance(verifier_type, type):
            raise NativeBackendUnavailableError(
                "the native backend adapter has no VerifyBackendFactory",
                context={"reason": "verify_adapter_unavailable"},
            )
        verifier = verifier_type(native_factory)
        if not _is_backend_factory(verifier):
            raise NativeBackendUnavailableError(
                "the verify backend adapter does not satisfy BackendFactory",
                context={"reason": "adapter_invalid"},
            )
        return cast(BackendFactory, verifier)
    return native_factory


def _effective_backend(config: ReasonerConfig) -> BackendName:
    if config.backend is not BackendName.AUTO:
        return config.backend
    environment = os.environ.get("PYHERMIT_BACKEND")
    if environment is None:
        return BackendName.AUTO
    try:
        return BackendName(environment)
    except ValueError as error:
        choices = ", ".join(value.value for value in BackendName)
        raise ValueError(f"PYHERMIT_BACKEND must be one of: {choices}") from error


def _probe_native() -> _NativeProbe:
    unsupported = _unsupported_runtime_reason()
    if unsupported is not None:
        return _NativeProbe(BackendAvailability("native", False, None, None, unsupported))
    try:
        module = importlib.import_module("pyhermit._native")
    except ModuleNotFoundError as error:
        if error.name != "pyhermit._native":
            return _NativeProbe(BackendAvailability("native", False, None, None, "import_failed"))
        return _NativeProbe(BackendAvailability("native", False, None, None, "not_installed"))
    except (ImportError, OSError):
        return _NativeProbe(BackendAvailability("native", False, None, None, "import_failed"))

    implementation = getattr(module, "__version__", None)
    abi = getattr(module, "ABI_VERSION", None)
    schema = getattr(module, "IR_SCHEMA_VERSION", None)
    if not isinstance(implementation, str) or not implementation:
        return _NativeProbe(
            BackendAvailability("native", False, None, None, "metadata_invalid"),
            module,
        )
    if implementation != __version__:
        return _NativeProbe(
            BackendAvailability(
                "native", False, implementation, schema, "package_version_mismatch"
            ),
            module,
        )
    if abi != NATIVE_ABI_VERSION:
        return _NativeProbe(
            BackendAvailability("native", False, implementation, schema, "abi_mismatch"),
            module,
        )
    if schema != COMPILED_IR_SCHEMA_VERSION:
        return _NativeProbe(
            BackendAvailability("native", False, implementation, schema, "schema_mismatch"),
            module,
        )
    self_test = getattr(module, "self_test", None)
    if not callable(self_test):
        return _NativeProbe(
            BackendAvailability("native", False, implementation, schema, "metadata_invalid"),
            module,
        )
    try:
        self_test()
    except Exception:
        return _NativeProbe(
            BackendAvailability("native", False, implementation, schema, "self_test_failed"),
            module,
        )
    features = getattr(module, "FEATURES", None)
    if (
        not isinstance(features, tuple)
        or not all(isinstance(value, str) and value for value in features)
        or tuple(sorted(set(features))) != features
    ):
        return _NativeProbe(
            BackendAvailability("native", False, implementation, schema, "metadata_invalid"),
            module,
        )
    if not REQUIRED_NATIVE_FEATURES.issubset(features):
        return _NativeProbe(
            BackendAvailability("native", False, implementation, schema, "incomplete_features"),
            module,
        )
    return _NativeProbe(
        BackendAvailability("native", True, implementation, schema, None),
        module,
    )


def _unsupported_runtime_reason() -> str | None:
    if sys.implementation.name != "cpython":
        return "unsupported_runtime"
    if bool(sysconfig.get_config_var("Py_GIL_DISABLED")):
        return "unsupported_runtime"
    return None


def _is_backend_factory(value: object) -> bool:
    return getattr(value, "info", None) is not None and callable(
        getattr(value, "create_session", None)
    )


def _raise_native_unavailable(availability: BackendAvailability) -> None:
    reason = availability.reason or "unavailable"
    if reason in {
        "abi_mismatch",
        "metadata_invalid",
        "package_version_mismatch",
        "schema_mismatch",
    }:
        raise BackendVersionError(
            "the installed native backend is incompatible",
            context={"reason": reason},
        )
    raise NativeBackendUnavailableError(
        "a complete native backend is unavailable",
        context={"reason": reason},
    )


__all__ = [
    "NATIVE_ABI_VERSION",
    "REQUIRED_NATIVE_FEATURES",
    "backend_info",
    "select_backend_factory",
]
