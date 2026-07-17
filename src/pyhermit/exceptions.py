"""Stable backend-independent pyHermiT exception taxonomy.

SPDX-License-Identifier: LGPL-3.0-or-later
"""

from __future__ import annotations

import math
import re
from collections.abc import Mapping
from types import MappingProxyType
from typing import ClassVar, TypeAlias

ContextScalar: TypeAlias = str | int | float | bool | None
_CODE = re.compile(r"^[A-Z][A-Z0-9_]*$")


class PyHermiTError(Exception):
    """Base for errors produced after the pyowl-core input boundary."""

    DEFAULT_CODE: ClassVar[str] = "PYHERMIT_ERROR"

    def __init__(
        self,
        message: str,
        *,
        code: str | None = None,
        context: Mapping[str, ContextScalar] | None = None,
    ) -> None:
        if not isinstance(message, str) or not message:
            raise ValueError("exception message must be a nonempty string")
        selected = code or self.DEFAULT_CODE
        if not isinstance(selected, str) or _CODE.fullmatch(selected) is None:
            raise ValueError("exception code must match ^[A-Z][A-Z0-9_]*$")
        clean: dict[str, ContextScalar] = {}
        for key, value in (context or {}).items():
            if not isinstance(key, str) or not key:
                raise TypeError("exception context keys must be nonempty strings")
            if value is not None and not isinstance(value, (str, int, float, bool)):
                raise TypeError("exception context values must be scalar")
            if isinstance(value, float) and not math.isfinite(value):
                raise ValueError("exception context floats must be finite")
            clean[key] = value
        self.code = selected
        self.context: Mapping[str, ContextScalar] = MappingProxyType(dict(sorted(clean.items())))
        super().__init__(message)

    def as_dict(self) -> dict[str, object]:
        return {
            "code": self.code,
            "context": dict(self.context),
            "message": str(self),
            "type": type(self).__name__,
        }


class OntologyInputError(PyHermiTError):
    DEFAULT_CODE = "ONTOLOGY_INPUT_ERROR"


class IncompleteImportClosureError(OntologyInputError):
    DEFAULT_CODE = "INCOMPLETE_IMPORT_CLOSURE"


class OntologyProfileError(OntologyInputError):
    DEFAULT_CODE = "ONTOLOGY_PROFILE_ERROR"


class InvalidLiteralError(OntologyInputError):
    """A literal rejected by the HermiT semantic datatype layer.

    Parse-time ``pyowl_core.InvalidLiteralError`` values propagate unchanged and are
    intentionally a distinct class.
    """

    DEFAULT_CODE = "INVALID_LITERAL"


class UnsupportedDatatypeError(OntologyInputError):
    DEFAULT_CODE = "UNSUPPORTED_DATATYPE"


class ReasonerStateError(PyHermiTError):
    DEFAULT_CODE = "REASONER_STATE_ERROR"


class DisposedReasonerError(ReasonerStateError):
    DEFAULT_CODE = "DISPOSED_REASONER"


class InconsistentOntologyError(ReasonerStateError):
    DEFAULT_CODE = "INCONSISTENT_ONTOLOGY"


class FreshEntityError(ReasonerStateError):
    DEFAULT_CODE = "FRESH_ENTITY"


class ConcurrentMutationError(ReasonerStateError):
    DEFAULT_CODE = "CONCURRENT_MUTATION"


class ReasoningAbortedError(PyHermiTError):
    DEFAULT_CODE = "REASONING_ABORTED"


class ReasonerTimeoutError(ReasoningAbortedError, TimeoutError):
    DEFAULT_CODE = "REASONER_TIMEOUT"


class ReasonerInterruptedError(ReasoningAbortedError):
    DEFAULT_CODE = "REASONER_INTERRUPTED"


class ResourceLimitError(ReasoningAbortedError):
    DEFAULT_CODE = "RESOURCE_LIMIT"

    def __init__(
        self,
        message: str,
        *,
        limit: str | None = None,
        observed: int | float | None = None,
        allowed: int | float | None = None,
        context: Mapping[str, ContextScalar] | None = None,
    ) -> None:
        details = dict(context or {})
        if limit is not None:
            details["limit"] = limit
        if observed is not None:
            details["observed"] = observed
        if allowed is not None:
            details["allowed"] = allowed
        self.limit = limit
        self.observed = observed
        self.allowed = allowed
        super().__init__(message, context=details)


class BackendError(PyHermiTError):
    DEFAULT_CODE = "BACKEND_ERROR"


class NativeBackendUnavailableError(BackendError):
    DEFAULT_CODE = "NATIVE_BACKEND_UNAVAILABLE"


class BackendVersionError(BackendError):
    DEFAULT_CODE = "BACKEND_VERSION"


class BackendMismatchError(BackendError):
    DEFAULT_CODE = "BACKEND_MISMATCH"


class BackendPoisonedError(BackendError):
    DEFAULT_CODE = "BACKEND_POISONED"


class FeatureNotImplementedError(PyHermiTError, NotImplementedError):
    DEFAULT_CODE = "FEATURE_NOT_IMPLEMENTED"

    def __init__(self, message: str, *, feature_id: str) -> None:
        if not isinstance(feature_id, str) or not feature_id:
            raise ValueError("feature_id must be a nonempty string")
        self.feature_id = feature_id
        super().__init__(message, context={"feature_id": feature_id})


class InternalInvariantError(PyHermiTError):
    DEFAULT_CODE = "INTERNAL_INVARIANT"


__all__ = [
    "BackendError",
    "BackendMismatchError",
    "BackendPoisonedError",
    "BackendVersionError",
    "ConcurrentMutationError",
    "ContextScalar",
    "DisposedReasonerError",
    "FeatureNotImplementedError",
    "FreshEntityError",
    "IncompleteImportClosureError",
    "InconsistentOntologyError",
    "InternalInvariantError",
    "InvalidLiteralError",
    "NativeBackendUnavailableError",
    "OntologyInputError",
    "OntologyProfileError",
    "PyHermiTError",
    "ReasonerInterruptedError",
    "ReasonerStateError",
    "ReasonerTimeoutError",
    "ReasoningAbortedError",
    "ResourceLimitError",
    "UnsupportedDatatypeError",
]
