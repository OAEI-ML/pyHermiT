from __future__ import annotations

import hashlib
from collections.abc import Iterator
from types import SimpleNamespace
from typing import TypeVar, cast

import pyowl_core as owl
import pytest
from pyowl_core.backends.native_views import (
    produce_encoded_structural_view_v1,
)

import pyhermit.encoded_input as encoded_input
from pyhermit.encoded_input import (
    ENCODED_BUFFER_WIDTHS,
    ENCODED_DESCRIPTOR_SHA256,
    ENCODED_SCHEMA_NAME,
    EncodedStructuralSegmentLease,
    negotiate_encoded_input,
)

V = TypeVar("V")
_FEATURES = frozenset(
    {
        "document-boundaries",
        "document-scoped-anonymous",
        "import-manifest",
        "ontology-identity-index",
        "owl2-structural",
    }
)


class _EncodedStructuralView:
    def __init__(self, owner: _View) -> None:
        published = produce_encoded_structural_view_v1(_as_view(owner))
        self.schema_name = published.schema_name
        self.schema_version = published.schema_version
        self.model_schema = published.model_schema
        self.owner = published.owner
        self.scope = published.scope
        self.document_key = published.document_key
        self.descriptor = published.descriptor
        self.descriptor_digest = hashlib.sha256(self.descriptor).digest()
        self.buffers = published.buffers
        self.segments = published.segments
        self.structural_fingerprint = published.structural_fingerprint


class _View:
    def __init__(self, *, advertise: bool = True) -> None:
        self.capabilities = owl.CoreCapabilities(
            adapter_protocol=1,
            model_schema=1,
            wire_format=(1, 0),
            features=_FEATURES,
            encoded_view_schemas=({ENCODED_SCHEMA_NAME: 1} if advertise else {}),
        )
        self.structural_fingerprint = owl.Fingerprint("sha256", 1, b"s" * 32)
        self.logical_fingerprint = owl.Fingerprint("sha256", 1, b"l" * 32)
        self.signature_fingerprint = owl.Fingerprint("sha256", 1, b"g" * 32)
        self.report = object()
        self.origin_index = owl.OriginIndex()
        self.is_complete = True
        self.encoded = _EncodedStructuralView(self)
        self.requests: list[tuple[type[object], dict[str, object]]] = []

    def iter_axioms(
        self,
        axiom_type: type[owl.AxiomNode] | None = None,
        *,
        scope: owl.AxiomScope = owl.AxiomScope.CLOSURE,
        document_key: str | None = None,
    ) -> Iterator[owl.AxiomNode]:
        return iter(())

    def iter_extensions(
        self,
        namespace: str | None = None,
        *,
        scope: owl.AxiomScope = owl.AxiomScope.CLOSURE,
        document_key: str | None = None,
    ) -> Iterator[owl.StructuralNode]:
        return iter(())

    def contains(
        self,
        axiom: owl.AxiomNode,
        *,
        scope: owl.AxiomScope = owl.AxiomScope.CLOSURE,
        document_key: str | None = None,
    ) -> bool:
        return False

    def ontology_annotations(
        self,
        *,
        scope: owl.AxiomScope = owl.AxiomScope.CLOSURE,
        document_key: str | None = None,
    ) -> owl.CanonicalSet[owl.Annotation]:
        return owl.CanonicalSet()

    def signature(
        self,
        kind: owl.EntityKind | None = None,
        *,
        scope: owl.AxiomScope = owl.AxiomScope.CLOSURE,
        document_key: str | None = None,
        include_builtins: bool = True,
    ) -> tuple[owl.Entity, ...]:
        return ()

    def view(self, view_type: type[V], /, **options: object) -> V:
        self.requests.append((cast(type[object], view_type), dict(options)))
        return cast(V, self.encoded)


def _as_view(value: _View) -> owl.OntologyView:
    return cast(owl.OntologyView, value)


def _segment(
    *,
    role: int,
    owner: _View,
    source: _EncodedStructuralView | None,
    posting_mode: int = 0,
    root_ids: memoryview | None = None,
    anonymous_scope_map: memoryview | None = None,
    member_token: bytes | None = None,
) -> object:
    return SimpleNamespace(
        role=role,
        owner=owner,
        source=source,
        posting_mode=posting_mode,
        root_ids=memoryview(b"") if root_ids is None else root_ids,
        anonymous_scope_map=(
            memoryview(b"") if anonymous_scope_map is None else anonymous_scope_map
        ),
        member_token=member_token,
    )


def test_native_capability_absence_does_not_request_core_buffers(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.delattr(owl, "EncodedStructuralView", raising=False)
    view = _View()

    result = negotiate_encoded_input(_as_view(view), {})

    assert not result.available
    assert result.native_schema_version is None
    assert view.requests == []


def test_scalar_only_core_is_a_compatible_fallback(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.delattr(owl, "EncodedStructuralView", raising=False)
    view = _View(advertise=False)

    result = negotiate_encoded_input(_as_view(view), {ENCODED_SCHEMA_NAME: 1})

    assert not result.available
    assert result.core_schema_version is None
    assert view.requests == []


def test_valid_handoff_retains_owner_and_read_only_buffers(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(owl, "EncodedStructuralView", _EncodedStructuralView, raising=False)
    view = _View()

    result = negotiate_encoded_input(_as_view(view), {ENCODED_SCHEMA_NAME: 1})

    assert result.available
    lease = result.lease
    assert lease is not None
    assert cast(object, lease.owner) is view
    assert lease.encoded_view is view.encoded
    assert lease.structural_fingerprint is view.encoded.structural_fingerprint
    assert lease.structural_fingerprint != view.structural_fingerprint
    assert tuple(lease.buffers) == tuple(ENCODED_BUFFER_WIDTHS)
    assert lease.buffer_count == 11
    assert lease.buffer_bytes == 8
    assert all(buffer.readonly for buffer in lease.buffers.values())
    assert lease.descriptor_digest == ENCODED_DESCRIPTOR_SHA256
    assert view.requests == [
        (
            _EncodedStructuralView,
            {"schema_version": 1, "scope": owl.AxiomScope.CLOSURE},
        )
    ]


def test_overlay_segment_graph_retains_and_orders_each_local_column_owner(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(owl, "EncodedStructuralView", _EncodedStructuralView, raising=False)
    source_owner = _View()
    source_result = negotiate_encoded_input(_as_view(source_owner), {ENCODED_SCHEMA_NAME: 1})
    source_lease = source_result.lease
    assert source_lease is not None
    owner = _View()
    raw_segment = _segment(
        role=2,
        owner=source_owner,
        source=source_owner.encoded,
    )
    fingerprint_segment = EncodedStructuralSegmentLease(
        segment=raw_segment,
        role=2,
        owner=_as_view(source_owner),
        source=source_lease,
        posting_mode=0,
        root_ids=memoryview(b""),
        anonymous_scope_map=memoryview(b""),
        member_token=None,
    )
    owner.encoded.segments = (raw_segment,)
    owner.encoded.structural_fingerprint = encoded_input._encoded_fingerprint(
        owner.encoded.buffers,
        (fingerprint_segment,),
        owner.encoded.descriptor,
    )

    result = negotiate_encoded_input(_as_view(owner), {ENCODED_SCHEMA_NAME: 1})

    lease = result.lease
    assert lease is not None
    assert lease.segments[0].segment is raw_segment
    assert lease.segments[0].source is not None
    assert tuple(item.encoded_view for item in lease.local_leases()) == (
        owner.encoded,
        source_owner.encoded,
    )


@pytest.mark.parametrize("defect", ["role", "posting", "scope_map", "cycle"])
def test_hostile_segment_graphs_fail_closed(
    monkeypatch: pytest.MonkeyPatch,
    defect: str,
) -> None:
    monkeypatch.setattr(owl, "EncodedStructuralView", _EncodedStructuralView, raising=False)
    owner = _View()
    if defect == "role":
        segment = _segment(role=99, owner=owner, source=None)
    elif defect == "posting":
        segment = _segment(
            role=1,
            owner=owner,
            source=None,
            root_ids=memoryview(b"\x01\x00\x00\x00"),
        )
    elif defect == "scope_map":
        segment = _segment(
            role=1,
            owner=owner,
            source=None,
            anonymous_scope_map=memoryview(b"x" * 64),
        )
    else:
        segment = _segment(role=2, owner=owner, source=owner.encoded)
    owner.encoded.segments = (segment,)

    with pytest.raises(owl.BackendProtocolError, match="encoded"):
        negotiate_encoded_input(_as_view(owner), {ENCODED_SCHEMA_NAME: 1})


def test_encoded_publication_fingerprint_is_recomputed_fail_closed(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(owl, "EncodedStructuralView", _EncodedStructuralView, raising=False)
    owner = _View()
    owner.encoded.structural_fingerprint = owl.Fingerprint("sha256", 1, b"x" * 32)

    with pytest.raises(owl.BackendProtocolError, match="fingerprint"):
        negotiate_encoded_input(_as_view(owner), {ENCODED_SCHEMA_NAME: 1})


def test_descriptor_digest_is_derived_when_core_uses_the_minimal_public_surface(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(owl, "EncodedStructuralView", _EncodedStructuralView, raising=False)
    view = _View()
    del view.encoded.descriptor_digest

    result = negotiate_encoded_input(_as_view(view), {ENCODED_SCHEMA_NAME: 1})

    assert result.lease is not None
    assert result.lease.descriptor_digest == hashlib.sha256(view.encoded.descriptor).digest()


def test_self_consistent_descriptor_drift_fails_closed(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(owl, "EncodedStructuralView", _EncodedStructuralView, raising=False)
    view = _View()
    view.encoded.descriptor += b" "
    view.encoded.descriptor_digest = hashlib.sha256(view.encoded.descriptor).digest()

    with pytest.raises(owl.BackendProtocolError, match="frozen"):
        negotiate_encoded_input(_as_view(view), {ENCODED_SCHEMA_NAME: 1})


@pytest.mark.parametrize(
    "buffers",
    [
        {name: memoryview(b"") for name in ENCODED_BUFFER_WIDTHS if name != "root_ids"},
        {
            **{name: memoryview(b"") for name in ENCODED_BUFFER_WIDTHS},
            "private_layout": memoryview(b""),
        },
        {
            **{name: memoryview(b"") for name in ENCODED_BUFFER_WIDTHS},
            "root_ids": memoryview(b"\x00"),
        },
    ],
)
def test_buffer_ledger_and_scalar_widths_fail_closed(
    monkeypatch: pytest.MonkeyPatch,
    buffers: dict[str, memoryview],
) -> None:
    monkeypatch.setattr(owl, "EncodedStructuralView", _EncodedStructuralView, raising=False)
    view = _View()
    view.encoded.buffers = buffers

    with pytest.raises(owl.BackendProtocolError, match="buffer"):
        negotiate_encoded_input(_as_view(view), {ENCODED_SCHEMA_NAME: 1})


@pytest.mark.parametrize(
    ("field", "invalid"),
    [
        ("schema_name", "wrong/schema"),
        ("schema_version", 2),
        ("model_schema", 2),
        ("descriptor", b""),
        ("descriptor_digest", b"x" * 32),
        ("structural_fingerprint", object()),
        ("buffers", {}),
        ("buffers", {"writable": memoryview(bytearray(b"bad"))}),
        ("segments", []),
        ("scope", owl.AxiomScope.ROOT),
    ],
)
def test_malformed_advertised_envelope_fails_closed(
    monkeypatch: pytest.MonkeyPatch,
    field: str,
    invalid: object,
) -> None:
    monkeypatch.setattr(owl, "EncodedStructuralView", _EncodedStructuralView, raising=False)
    view = _View()
    setattr(view.encoded, field, invalid)

    with pytest.raises(owl.BackendProtocolError):
        negotiate_encoded_input(_as_view(view), {ENCODED_SCHEMA_NAME: 1})


def test_false_advertising_requires_public_core_type(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.delattr(owl, "EncodedStructuralView", raising=False)
    view = _View()

    with pytest.raises(owl.AdapterCompatibilityError, match="exports no"):
        negotiate_encoded_input(_as_view(view), {ENCODED_SCHEMA_NAME: 1})
    assert view.requests == []
