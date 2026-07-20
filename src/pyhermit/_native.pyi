"""Authoritative typing contract for the private optional Rust extension."""

# SPDX-License-Identifier: LGPL-3.0-or-later

from collections.abc import Sequence
from typing import Final

__version__: Final[str]
ABI_VERSION: Final[int]
IR_SCHEMA_VERSION: Final[int]
STATE_TRACE_VERSION: Final[int]
FEATURES: Final[tuple[str, ...]]

class CancellationHandle:
    def __init__(
        self,
        timeout: float | None = ...,
        max_memory_bytes: int | None = ...,
    ) -> None: ...
    @property
    def interrupted(self) -> bool: ...
    def interrupt(self, reason: str | None = ...) -> bool: ...
    def observe_memory(self, memory_bytes: int) -> None: ...
    def reset(
        self,
        timeout: float | None = ...,
        max_memory_bytes: int | None = ...,
    ) -> None: ...

class NativeSession:
    @property
    def ontology_fingerprint(self) -> str: ...
    @property
    def closed(self) -> bool: ...
    @property
    def poisoned(self) -> bool: ...
    def check(self, query: bytes | None) -> bytes: ...
    def check_many(self, queries: Sequence[bytes]) -> bytes: ...
    def classify_classes(self) -> bytes: ...
    def classify_object_properties(self) -> bytes: ...
    def classify_data_properties(self) -> bytes: ...
    def realize(self) -> bytes: ...
    def apply_delta(self, delta: bytes) -> bytes: ...
    def drain_events(self) -> bytes: ...
    def reset_query_state(self) -> None: ...
    def close(self) -> None: ...
    def _debug_replay_state_trace(self, trace: bytes) -> list[str]: ...
    def _debug_long_work(self, iterations: int, poll_stride: int = ...) -> int: ...
    def _drain_debug_events(self) -> list[tuple[str, int]]: ...
    def _debug_inject_panic(self) -> None: ...

def _validate_encoded_columns_v1(
    *,
    root_kinds: memoryview,
    root_ids: memoryview,
    node_tags: memoryview,
    node_field_offsets: memoryview,
    field_kinds: memoryview,
    field_values: memoryview,
    field_lengths: memoryview,
    item_kinds: memoryview,
    item_values: memoryview,
    item_lengths: memoryview,
    scalar_bytes: memoryview,
) -> None: ...
def _validate_encoded_selection_v1(
    *,
    posting_mode: int,
    postings: memoryview,
    root_kinds: memoryview,
    root_ids: memoryview,
    node_tags: memoryview,
    node_field_offsets: memoryview,
    field_kinds: memoryview,
    field_values: memoryview,
    field_lengths: memoryview,
    item_kinds: memoryview,
    item_values: memoryview,
    item_lengths: memoryview,
    scalar_bytes: memoryview,
) -> None: ...
def _validate_encoded_slices_v1(*, slices: tuple[tuple[object, ...], ...]) -> None: ...
def _debug_encoded_selection_panic_v1() -> None: ...
def _encoded_symbol_manifest_v1(
    *,
    root_kinds: memoryview,
    root_ids: memoryview,
    node_tags: memoryview,
    node_field_offsets: memoryview,
    field_kinds: memoryview,
    field_values: memoryview,
    field_lengths: memoryview,
    item_kinds: memoryview,
    item_values: memoryview,
    item_lengths: memoryview,
    scalar_bytes: memoryview,
) -> bytes: ...
def _encoded_object_role_manifest_v1(
    *,
    root_kinds: memoryview,
    root_ids: memoryview,
    node_tags: memoryview,
    node_field_offsets: memoryview,
    field_kinds: memoryview,
    field_values: memoryview,
    field_lengths: memoryview,
    item_kinds: memoryview,
    item_values: memoryview,
    item_lengths: memoryview,
    scalar_bytes: memoryview,
) -> bytes: ...
def _encoded_object_role_slices_manifest_v1(*, slices: tuple[tuple[object, ...], ...]) -> bytes: ...
def _encoded_named_class_manifest_v1(
    *,
    root_kinds: memoryview,
    root_ids: memoryview,
    node_tags: memoryview,
    node_field_offsets: memoryview,
    field_kinds: memoryview,
    field_values: memoryview,
    field_lengths: memoryview,
    item_kinds: memoryview,
    item_values: memoryview,
    item_lengths: memoryview,
    scalar_bytes: memoryview,
) -> bytes: ...
def _encoded_named_class_slices_manifest_v1(*, slices: tuple[tuple[object, ...], ...]) -> bytes: ...
def self_test() -> None: ...
def create_session(
    ir: bytes,
    config: bytes,
    cancellation: CancellationHandle,
) -> NativeSession: ...
