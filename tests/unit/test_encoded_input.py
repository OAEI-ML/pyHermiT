from __future__ import annotations

import hashlib
from collections.abc import Iterator
from typing import TypeVar, cast

import pyowl_core as owl
import pytest

from pyhermit.encoded_input import (
    ENCODED_SCHEMA_NAME,
    ENCODED_SCHEMA_VERSION,
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
        self.schema_name = ENCODED_SCHEMA_NAME
        self.schema_version = ENCODED_SCHEMA_VERSION
        self.model_schema = 1
        self.owner = owner
        self.scope = owl.AxiomScope.CLOSURE
        self.descriptor = b"pyhermit encoded input fixture"
        self.descriptor_digest = hashlib.sha256(self.descriptor).digest()
        self.buffers = {
            "components": memoryview(b"components"),
            "roots": memoryview(b"roots"),
        }
        self.segments: tuple[object, ...] = ()
        self.structural_fingerprint = owner.structural_fingerprint


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
    assert tuple(lease.buffers) == ("components", "roots")
    assert lease.buffer_count == 2
    assert lease.buffer_bytes == 15
    assert all(buffer.readonly for buffer in lease.buffers.values())
    assert view.requests == [
        (
            _EncodedStructuralView,
            {"schema_version": 1, "scope": owl.AxiomScope.CLOSURE},
        )
    ]


def test_descriptor_digest_is_derived_when_core_uses_the_minimal_public_surface(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(owl, "EncodedStructuralView", _EncodedStructuralView, raising=False)
    view = _View()
    del view.encoded.descriptor_digest

    result = negotiate_encoded_input(_as_view(view), {ENCODED_SCHEMA_NAME: 1})

    assert result.lease is not None
    assert result.lease.descriptor_digest == hashlib.sha256(
        view.encoded.descriptor
    ).digest()


@pytest.mark.parametrize(
    ("field", "invalid"),
    [
        ("schema_name", "wrong/schema"),
        ("schema_version", 2),
        ("model_schema", 2),
        ("descriptor", b""),
        ("descriptor_digest", b"x" * 32),
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
