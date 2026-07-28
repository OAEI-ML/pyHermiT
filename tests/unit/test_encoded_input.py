from __future__ import annotations

import hashlib
import mmap
import weakref
from collections.abc import Iterator
from gc import collect
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
from pyhermit.exceptions import ResourceLimitError

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


def _postings(*root_ids: int) -> memoryview:
    return memoryview(b"".join(root_id.to_bytes(4, "little") for root_id in root_ids))


def _set_local_root_count(owner: _View, root_count: int) -> None:
    buffers = dict(owner.encoded.buffers)
    buffers["root_kinds"] = memoryview(b"\x02" * root_count)
    buffers["root_ids"] = _postings(*range(1, root_count + 1))
    owner.encoded.buffers = buffers
    raw_direct = owner.encoded.segments[0]
    direct = EncodedStructuralSegmentLease(
        segment=raw_direct,
        role=1,
        owner=_as_view(owner),
        source=None,
        posting_mode=0,
        root_ids=memoryview(b""),
        anonymous_scope_map=memoryview(b""),
        member_token=None,
    )
    owner.encoded.structural_fingerprint = encoded_input._encoded_fingerprint(
        buffers,
        (direct,),
        owner.encoded.descriptor,
    )


def _move_local_buffers_to_mmap(owner: _View) -> mmap.mmap:
    names = tuple(owner.encoded.buffers)
    payload = b"".join(bytes(owner.encoded.buffers[name]) for name in names)
    mapping = mmap.mmap(-1, len(payload))
    mapping[:] = payload
    exported = memoryview(mapping).toreadonly()
    cursor = 0
    buffers: dict[str, memoryview] = {}
    for name in names:
        following = cursor + owner.encoded.buffers[name].nbytes
        buffers[name] = exported[cursor:following]
        cursor = following
    exported.release()
    owner.encoded.buffers = buffers
    raw_direct = owner.encoded.segments[0]
    direct = EncodedStructuralSegmentLease(
        segment=raw_direct,
        role=1,
        owner=_as_view(owner),
        source=None,
        posting_mode=0,
        root_ids=memoryview(b""),
        anonymous_scope_map=memoryview(b""),
        member_token=None,
    )
    owner.encoded.structural_fingerprint = encoded_input._encoded_fingerprint(
        buffers,
        (direct,),
        owner.encoded.descriptor,
    )
    return mapping


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


def test_profile_side_contexts_are_canonical_and_union_composite_origins(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    options = owl.LoadOptions(
        imports=owl.ImportPolicy.IGNORE,
        backend=owl.BackendPreference.PYTHON,
    )
    body = (
        b"Prefix(:=<urn:context#>) Ontology(<urn:context:left> "
        b"Declaration(Class(:A)) Declaration(Class(:B)) SubClassOf(:A :B))"
    )
    left = owl.load_snapshot(body, document_iri="urn:document:z", options=options)
    right = owl.load_snapshot(
        body.replace(b"urn:context:left", b"urn:context:right"),
        document_iri="urn:document:a",
        options=options,
    )
    composite = owl.compose_views(left, right, roles=("left", "right"))

    def forbidden(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("profile side-context construction traversed scalar roots")

    monkeypatch.setattr(type(composite), "iter_axioms", forbidden)
    monkeypatch.setattr(type(composite), "iter_extensions", forbidden)
    monkeypatch.setattr(type(composite), "signature", forbidden)

    contexts = encoded_input._encoded_profile_contexts(composite)

    identity_version, identity_rows = contexts.ontology_identity_context
    assert identity_version == 1
    assert identity_rows == tuple(sorted(identity_rows))
    assert {row[1:] for row in identity_rows} == {
        ("urn:context:left", None),
        ("urn:context:right", None),
    }
    origin_version, origin_rows = contexts.origin_context
    assert origin_version == 1
    assert origin_rows == tuple(sorted(origin_rows))
    assert len(origin_rows) == 3
    assert {digest for digest, _document_keys in origin_rows} == set(
        composite.origin_index.entries
    )
    assert all(len(provenance) == 32 for provenance, _document_keys in origin_rows)
    assert all(
        document_keys == tuple(sorted(document_keys)) and len(document_keys) == 2
        for _provenance, document_keys in origin_rows
    )


def test_native_slice_records_share_one_exact_column_ledger() -> None:
    buffers = {
        name: memoryview(bytes((index,)))
        for index, name in enumerate(ENCODED_BUFFER_WIDTHS)
    }
    root_ids = memoryview(b"\x01\x00\x00\x00")
    member_token = b"m" * 32
    scope_map = memoryview(b"a" * 32 + b"b" * 32)
    root_slice = SimpleNamespace(
        lease=SimpleNamespace(buffers=buffers),
        posting_mode=1,
        root_ids=root_ids,
        member_tokens=(member_token,),
        anonymous_scope_maps=(scope_map,),
    )

    records = encoded_input._encoded_slice_records((root_slice,))

    assert records[0][:4] == (1, root_ids, (member_token,), (scope_map,))
    assert records[0][4:] == tuple(
        buffers[name]
        for name in (
            "root_kinds",
            "root_ids",
            "node_tags",
            "node_field_offsets",
            "field_kinds",
            "field_values",
            "field_lengths",
            "item_kinds",
            "item_values",
            "item_lengths",
            "scalar_bytes",
        )
    )


def test_lease_retains_closeable_buffer_owner_until_the_handoff_is_released(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(owl, "EncodedStructuralView", _EncodedStructuralView, raising=False)
    owner = _View()
    mapping = _move_local_buffers_to_mmap(owner)
    owner_reference = weakref.ref(owner)

    result = negotiate_encoded_input(_as_view(owner), {ENCODED_SCHEMA_NAME: 1})
    lease = result.lease
    assert lease is not None
    del owner
    collect()

    assert owner_reference() is lease.owner
    with pytest.raises(BufferError):
        mapping.close()

    del lease, result
    collect()
    assert owner_reference() is None
    mapping.close()
    assert mapping.closed


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
    root_slices = lease.overlay_root_slices()
    assert root_slices is not None
    assert tuple(root_slice.lease.encoded_view for root_slice in root_slices) == (
        source_owner.encoded,
        owner.encoded,
    )
    assert tuple(root_slice.posting_mode for root_slice in root_slices) == (0, 0)
    assert root_slices[0].lease is lease.segments[0].source
    assert all(
        root_slices[0].lease.buffers[name].obj is source_owner.encoded.buffers[name].obj
        for name in ENCODED_BUFFER_WIDTHS
    )


def test_overlay_exclusion_selects_only_immediate_source_roots_without_column_copy(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(owl, "EncodedStructuralView", _EncodedStructuralView, raising=False)
    source_owner = _View()
    _set_local_root_count(source_owner, 2)
    source_result = negotiate_encoded_input(_as_view(source_owner), {ENCODED_SCHEMA_NAME: 1})
    source_lease = source_result.lease
    assert source_lease is not None
    owner = _View()
    raw_segment = _segment(
        role=2,
        owner=source_owner,
        source=source_owner.encoded,
        posting_mode=2,
        root_ids=_postings(1),
    )
    fingerprint_segment = EncodedStructuralSegmentLease(
        segment=raw_segment,
        role=2,
        owner=_as_view(source_owner),
        source=source_lease,
        posting_mode=2,
        root_ids=raw_segment.root_ids,
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
    root_slices = lease.overlay_root_slices()
    assert root_slices is not None
    assert tuple(root_slice.lease.encoded_view for root_slice in root_slices) == (
        source_owner.encoded,
        owner.encoded,
    )
    assert root_slices[0].lease is lease.segments[0].source
    assert root_slices[1].lease is lease
    assert tuple(root_slice.posting_mode for root_slice in root_slices) == (2, 0)
    assert root_slices[0].root_ids is lease.segments[0].root_ids
    assert bytes(root_slices[0].root_ids) == _postings(1)
    assert root_slices[1].root_ids.nbytes == 0
    assert all(
        root_slices[0].lease.buffers[name].obj is source_owner.encoded.buffers[name].obj
        for name in ENCODED_BUFFER_WIDTHS
    )


def test_nested_overlay_exclusions_remain_source_local(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(owl, "EncodedStructuralView", _EncodedStructuralView, raising=False)
    base_owner = _View()
    _set_local_root_count(base_owner, 2)
    base_lease = negotiate_encoded_input(_as_view(base_owner), {ENCODED_SCHEMA_NAME: 1}).lease
    assert base_lease is not None
    inner_owner = _View()
    _set_local_root_count(inner_owner, 2)
    raw_inner_base = _segment(
        role=2,
        owner=base_owner,
        source=base_owner.encoded,
        posting_mode=2,
        root_ids=_postings(1),
    )
    raw_inner_delta = _segment(role=3, owner=inner_owner, source=None)
    inner_segments = (
        EncodedStructuralSegmentLease(
            raw_inner_base,
            2,
            _as_view(base_owner),
            base_lease,
            2,
            raw_inner_base.root_ids,
            memoryview(b""),
            None,
        ),
        EncodedStructuralSegmentLease(
            raw_inner_delta,
            3,
            _as_view(inner_owner),
            None,
            0,
            memoryview(b""),
            memoryview(b""),
            None,
        ),
    )
    inner_owner.encoded.segments = (raw_inner_base, raw_inner_delta)
    inner_owner.encoded.structural_fingerprint = encoded_input._encoded_fingerprint(
        inner_owner.encoded.buffers,
        inner_segments,
        inner_owner.encoded.descriptor,
    )
    inner_lease = negotiate_encoded_input(_as_view(inner_owner), {ENCODED_SCHEMA_NAME: 1}).lease
    assert inner_lease is not None
    outer_owner = _View()
    raw_outer_base = _segment(
        role=2,
        owner=inner_owner,
        source=inner_owner.encoded,
        posting_mode=2,
        root_ids=_postings(2),
    )
    outer_segment = EncodedStructuralSegmentLease(
        raw_outer_base,
        2,
        _as_view(inner_owner),
        inner_lease,
        2,
        raw_outer_base.root_ids,
        memoryview(b""),
        None,
    )
    outer_owner.encoded.segments = (raw_outer_base,)
    outer_owner.encoded.structural_fingerprint = encoded_input._encoded_fingerprint(
        outer_owner.encoded.buffers,
        (outer_segment,),
        outer_owner.encoded.descriptor,
    )

    lease = negotiate_encoded_input(_as_view(outer_owner), {ENCODED_SCHEMA_NAME: 1}).lease

    assert lease is not None
    root_slices = lease.overlay_root_slices()
    assert root_slices is not None
    assert tuple(root_slice.lease.encoded_view for root_slice in root_slices) == (
        base_owner.encoded,
        inner_owner.encoded,
        outer_owner.encoded,
    )
    assert tuple(root_slice.posting_mode for root_slice in root_slices) == (2, 2, 0)
    assert tuple(bytes(root_slice.root_ids) for root_slice in root_slices) == (
        bytes(_postings(1)),
        bytes(_postings(2)),
        b"",
    )
    inner_source = lease.segments[0].source
    assert inner_source is not None
    assert root_slices[0].root_ids is inner_source.segments[0].root_ids
    assert root_slices[1].root_ids is lease.segments[0].root_ids


def test_composite_include_exclude_tokens_and_scope_maps_compose_exactly(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(owl, "EncodedStructuralView", _EncodedStructuralView, raising=False)
    base_owner = _View()
    _set_local_root_count(base_owner, 2)
    base_lease = negotiate_encoded_input(_as_view(base_owner), {ENCODED_SCHEMA_NAME: 1}).lease
    assert base_lease is not None

    inner_owner = _View()
    _set_local_root_count(inner_owner, 2)
    inner_scope = memoryview(b"a" * 32 + b"b" * 32)
    raw_inner_base = _segment(
        role=2,
        owner=base_owner,
        source=base_owner.encoded,
        posting_mode=2,
        root_ids=_postings(1),
        anonymous_scope_map=inner_scope,
    )
    raw_inner_delta = _segment(role=3, owner=inner_owner, source=None)
    inner_segments = (
        EncodedStructuralSegmentLease(
            raw_inner_base,
            2,
            _as_view(base_owner),
            base_lease,
            2,
            raw_inner_base.root_ids,
            inner_scope,
            None,
        ),
        EncodedStructuralSegmentLease(
            raw_inner_delta,
            3,
            _as_view(inner_owner),
            None,
            0,
            raw_inner_delta.root_ids,
            raw_inner_delta.anonymous_scope_map,
            None,
        ),
    )
    inner_owner.encoded.segments = (raw_inner_base, raw_inner_delta)
    inner_owner.encoded.structural_fingerprint = encoded_input._encoded_fingerprint(
        inner_owner.encoded.buffers,
        inner_segments,
        inner_owner.encoded.descriptor,
    )
    inner_lease = negotiate_encoded_input(_as_view(inner_owner), {ENCODED_SCHEMA_NAME: 1}).lease
    assert inner_lease is not None

    owner = _View()
    include_scope = memoryview(b"c" * 32 + b"d" * 32)
    exclude_scope = memoryview(b"e" * 32 + b"f" * 32)
    include_token = b"1" * 32
    exclude_token = b"2" * 32
    raw_include = _segment(
        role=4,
        owner=inner_owner,
        source=inner_owner.encoded,
        posting_mode=1,
        root_ids=_postings(1),
        anonymous_scope_map=include_scope,
        member_token=include_token,
    )
    raw_exclude = _segment(
        role=4,
        owner=inner_owner,
        source=inner_owner.encoded,
        posting_mode=2,
        root_ids=_postings(2),
        anonymous_scope_map=exclude_scope,
        member_token=exclude_token,
    )
    outer_segments = (
        EncodedStructuralSegmentLease(
            raw_include,
            4,
            _as_view(inner_owner),
            inner_lease,
            1,
            raw_include.root_ids,
            include_scope,
            include_token,
        ),
        EncodedStructuralSegmentLease(
            raw_exclude,
            4,
            _as_view(inner_owner),
            inner_lease,
            2,
            raw_exclude.root_ids,
            exclude_scope,
            exclude_token,
        ),
    )
    owner.encoded.segments = (raw_include, raw_exclude)
    owner.encoded.structural_fingerprint = encoded_input._encoded_fingerprint(
        owner.encoded.buffers,
        outer_segments,
        owner.encoded.descriptor,
    )

    lease = negotiate_encoded_input(_as_view(owner), {ENCODED_SCHEMA_NAME: 1}).lease

    assert lease is not None
    root_slices = lease.root_slices()
    assert tuple(root_slice.lease.encoded_view for root_slice in root_slices) == (
        inner_owner.encoded,
        base_owner.encoded,
        inner_owner.encoded,
        owner.encoded,
    )
    assert tuple(root_slice.posting_mode for root_slice in root_slices) == (1, 2, 2, 0)
    assert tuple(bytes(root_slice.root_ids) for root_slice in root_slices) == (
        _postings(1),
        _postings(1),
        _postings(2),
        b"",
    )
    assert tuple(root_slice.member_tokens for root_slice in root_slices) == (
        (include_token,),
        (exclude_token,),
        (exclude_token,),
        (),
    )
    assert tuple(root_slice.anonymous_scope_maps for root_slice in root_slices) == (
        (lease.segments[0].anonymous_scope_map,),
        (
            lease.segments[1].source.segments[0].anonymous_scope_map,
            lease.segments[1].anonymous_scope_map,
        ),
        (lease.segments[1].anonymous_scope_map,),
        (),
    )
    assert root_slices[0].root_ids is lease.segments[0].root_ids
    assert root_slices[1].root_ids is lease.segments[1].source.segments[0].root_ids
    assert root_slices[2].root_ids is lease.segments[1].root_ids
    nested = encoded_input._prefix_member_token((root_slices[0],), b"0" * 32)
    assert nested[0].member_tokens == (b"0" * 32, include_token)
    monkeypatch.setattr(encoded_input, "_MAX_ROOT_SLICES", 3)
    with pytest.raises(ResourceLimitError, match="root-slice plan"):
        lease.root_slices()


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
