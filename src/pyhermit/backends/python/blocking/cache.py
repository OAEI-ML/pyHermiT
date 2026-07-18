# Copyright 2008, 2009, 2010 by the Oxford University Computing Laboratory
# Modifications Copyright 2026 pyHermiT contributors
# Adapted from HermiT commit 37ec30aced32ac81ebecc5e33fad255ddefcb4c3;
# see reports/licensing/adapted-files.toml.

"""Bounded soundness-gated blocking signature cache.

SPDX-License-Identifier: LGPL-3.0-or-later
"""

from __future__ import annotations

import threading
from collections import OrderedDict
from collections.abc import Iterable
from dataclasses import dataclass

from .signatures import BlockingSignature, DirectCheckerKind
from .strategy import CoreBlockingMode


@dataclass(frozen=True, slots=True)
class BlockingCacheNamespace:
    ontology_fingerprint: str
    vocabulary_fingerprint: str
    checker_kind: DirectCheckerKind
    core_mode: CoreBlockingMode = CoreBlockingMode.NONE
    configuration_fingerprint: str = "default"

    def __post_init__(self) -> None:
        for name in (
            "ontology_fingerprint",
            "vocabulary_fingerprint",
            "configuration_fingerprint",
        ):
            value = getattr(self, name)
            if not isinstance(value, str) or not value:
                raise ValueError(f"{name} must be a nonempty string")
        if not isinstance(self.checker_kind, DirectCheckerKind):
            raise TypeError("checker_kind must be DirectCheckerKind")
        if not isinstance(self.core_mode, CoreBlockingMode):
            raise TypeError("core_mode must be CoreBlockingMode")

    @property
    def key(self) -> tuple[str, str, str, str, str]:
        return (
            self.ontology_fingerprint,
            self.vocabulary_fingerprint,
            self.checker_kind.value,
            self.core_mode.value,
            self.configuration_fingerprint,
        )


class BlockingSignatureCache:
    """Thread-safe LRU; eviction changes performance only."""

    __slots__ = (
        "_bytes",
        "_entries",
        "_lock",
        "max_bytes",
        "max_entries",
        "namespace",
    )

    def __init__(
        self,
        namespace: BlockingCacheNamespace,
        *,
        max_entries: int = 4_096,
        max_bytes: int = 16 * 1024 * 1024,
    ) -> None:
        if not isinstance(namespace, BlockingCacheNamespace):
            raise TypeError("namespace must be BlockingCacheNamespace")
        for name, value in (("max_entries", max_entries), ("max_bytes", max_bytes)):
            if isinstance(value, bool) or not isinstance(value, int) or value <= 0:
                raise ValueError(f"{name} must be a positive integer")
        self.namespace = namespace
        self.max_entries = max_entries
        self.max_bytes = max_bytes
        self._entries: OrderedDict[bytes, BlockingSignature] = OrderedDict()
        self._bytes = 0
        self._lock = threading.RLock()

    def contains(self, signature: BlockingSignature) -> bool:
        self._require_compatible(signature)
        key = signature.canonical_bytes()
        with self._lock:
            known = self._entries.get(key)
            if known is None or known != signature:
                return False
            self._entries.move_to_end(key)
            return True

    def add(self, signature: BlockingSignature) -> bool:
        self._require_compatible(signature)
        key = signature.canonical_bytes()
        size = self._entry_size(key)
        if size > self.max_bytes:
            return False
        with self._lock:
            known = self._entries.get(key)
            if known is not None:
                if known != signature:
                    raise RuntimeError("canonical blocking signature collision")
                self._entries.move_to_end(key)
                return False
            self._entries[key] = signature
            self._bytes += size
            self._evict()
            return key in self._entries

    def promote_model(
        self,
        signatures: Iterable[BlockingSignature],
        *,
        satisfiable: bool,
        completed: bool,
        has_nominals: bool,
        has_additional_ontology: bool,
        query_local_axioms: bool,
        aborted: bool = False,
    ) -> int:
        flags = (
            satisfiable,
            completed,
            has_nominals,
            has_additional_ontology,
            query_local_axioms,
            aborted,
        )
        if not all(isinstance(flag, bool) for flag in flags):
            raise TypeError("cache promotion flags must be bool")
        if (
            not satisfiable
            or not completed
            or has_nominals
            or has_additional_ontology
            or query_local_axioms
            or aborted
            or self.namespace.core_mode is not CoreBlockingMode.NONE
        ):
            return 0
        inserted = 0
        for signature in signatures:
            inserted += int(self.add(signature))
        return inserted

    def clear(self) -> None:
        with self._lock:
            self._entries.clear()
            self._bytes = 0

    @property
    def entry_count(self) -> int:
        with self._lock:
            return len(self._entries)

    @property
    def size_bytes(self) -> int:
        with self._lock:
            return self._bytes

    def fingerprints(self) -> tuple[str, ...]:
        with self._lock:
            return tuple(signature.sha256 for signature in self._entries.values())

    def _require_compatible(self, signature: BlockingSignature) -> None:
        if not isinstance(signature, BlockingSignature):
            raise TypeError("signature must be BlockingSignature")
        if signature.kind is not self.namespace.checker_kind:
            raise ValueError("blocking signature checker kind does not match cache namespace")

    @staticmethod
    def _entry_size(key: bytes) -> int:
        return len(key) + 128

    def _evict(self) -> None:
        while len(self._entries) > self.max_entries or self._bytes > self.max_bytes:
            key, _signature = self._entries.popitem(last=False)
            self._bytes -= self._entry_size(key)


__all__ = ["BlockingCacheNamespace", "BlockingSignatureCache"]
