from __future__ import annotations

import io

import pyowl_core
from pyowl_core import (
    BackendPreference,
    ImportPolicy,
    LoadOptions,
    OntologyDelta,
    apply_delta,
    compose_views,
)

from pyhermit.encoded_input import (
    ENCODED_BUFFER_WIDTHS,
    ENCODED_DESCRIPTOR_SHA256,
    ENCODED_SCHEMA_NAME,
    ENCODED_SCHEMA_VERSION,
    negotiate_encoded_input,
)
from pyhermit.inputs import capture_ontology

OPTIONS = LoadOptions(imports=ImportPolicy.IGNORE, backend=BackendPreference.PYTHON)


def functional(identity: str, *body: str) -> bytes:
    return (
        f"Prefix(:=<urn:{identity}#>) Ontology(<urn:{identity}> " + " ".join(body) + ")"
    ).encode()


class Provider:
    def __init__(self, value: pyowl_core.OntologyView) -> None:
        self.value = value
        self.calls = 0

    def owl_snapshot(self) -> pyowl_core.OntologyView:
        self.calls += 1
        return self.value


def test_all_shared_view_shapes_remain_zero_copy_and_semantically_equal() -> None:
    source = pyowl_core.load_snapshot(
        functional("source", "Declaration(Class(:A))"),
        options=OPTIONS,
    )
    target = pyowl_core.load_snapshot(
        functional("target", "Declaration(Class(:B))"),
        options=OPTIONS,
    )
    added = pyowl_core.Declaration(pyowl_core.Class(pyowl_core.IRI("urn:source#C")))
    overlay = apply_delta(source, OntologyDelta(add_axioms={added}))
    composite = compose_views(overlay, target, roles=("source", "target"))
    provider = Provider(composite)

    for candidate in (source, overlay, composite):
        captured = capture_ontology(candidate)
        assert captured.view is candidate
        assert captured.profile.conforms
        assert captured.identity.is_complete
        assert len(captured.identity.import_manifest_digest) == 32
    provided = capture_ontology(provider)

    assert provided.view is composite
    assert provider.calls == 1
    assert overlay.base is source
    assert composite.members[0].view is overlay
    assert composite.members[1].view is target


def test_current_core_public_encoded_producer_crosses_the_exact_handoff() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "encoded-public",
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "SubClassOf(:A :B)",
        ),
        options=OPTIONS,
    )

    assert snapshot.capabilities.encoded_view_schemas == {
        ENCODED_SCHEMA_NAME: ENCODED_SCHEMA_VERSION
    }
    negotiated = negotiate_encoded_input(
        snapshot,
        {ENCODED_SCHEMA_NAME: ENCODED_SCHEMA_VERSION},
    )
    assert negotiated.available
    assert negotiated.core_schema_version == ENCODED_SCHEMA_VERSION
    assert negotiated.native_schema_version == ENCODED_SCHEMA_VERSION
    assert negotiated.reason is None

    lease = negotiated.lease
    assert lease is not None
    assert lease.owner is snapshot
    assert isinstance(lease.encoded_view, pyowl_core.EncodedStructuralView)
    assert lease.encoded_view.owner is snapshot
    assert lease.descriptor_digest == ENCODED_DESCRIPTOR_SHA256
    assert lease.structural_fingerprint is lease.encoded_view.structural_fingerprint
    assert tuple(lease.buffers) == tuple(ENCODED_BUFFER_WIDTHS)
    assert all(
        lease.buffers[name].obj is lease.encoded_view.buffers[name].obj
        for name in ENCODED_BUFFER_WIDTHS
    )

    assert len(lease.segments) == 1
    segment = lease.segments[0]
    assert segment.role == 1
    assert segment.owner is snapshot
    assert segment.source is None
    assert segment.posting_mode == 0
    assert segment.root_ids.nbytes == 0
    assert segment.anonymous_scope_map.nbytes == 0
    assert segment.member_token is None


def test_path_bytes_stream_document_and_snapshot_share_logical_identity(tmp_path) -> None:  # type: ignore[no-untyped-def]
    source = functional(
        "forms",
        "Declaration(Class(:A))",
        "Declaration(Class(:B))",
        "SubClassOf(:A :B)",
    )
    path = tmp_path / "forms.ofn"
    path.write_bytes(source)
    stream = io.BytesIO(source)
    text_stream = io.StringIO(source.decode())
    document = pyowl_core.parse_document(source, options=OPTIONS)
    snapshot = pyowl_core.load_snapshot(document, options=OPTIONS)
    text_options = LoadOptions(
        format=pyowl_core.DocumentFormat.FUNCTIONAL,
        imports=ImportPolicy.IGNORE,
        backend=BackendPreference.PYTHON,
    )

    captures = (
        capture_ontology(path, load_options=OPTIONS),
        capture_ontology(source, load_options=OPTIONS),
        capture_ontology(bytearray(source), load_options=OPTIONS),
        capture_ontology(memoryview(source), load_options=OPTIONS),
        capture_ontology(
            stream,
            document_iri="urn:forms:stream",
            load_options=OPTIONS,
        ),
        capture_ontology(
            text_stream,
            document_iri="urn:forms:text-stream",
            load_options=text_options,
        ),
        capture_ontology(document, load_options=OPTIONS),
        capture_ontology(snapshot),
    )

    assert not stream.closed
    assert not text_stream.closed
    assert len({item.captured.logical_fingerprint for item in captures}) == 1
    assert len({item.captured.signature_fingerprint for item in captures}) == 1
    assert all(item.profile.conforms for item in captures)


def test_explicit_resolver_builds_a_proven_complete_import_closure() -> None:
    root = functional(
        "root",
        "Import(<urn:leaf>)",
        "Declaration(Class(:Root))",
    )
    leaf = functional("leaf", "Declaration(Class(:Leaf))")
    options = LoadOptions(
        imports=ImportPolicy.RESOLVE_STRICT,
        backend=BackendPreference.PYTHON,
    )

    captured = capture_ontology(
        root,
        load_options=options,
        resolver=pyowl_core.MappingResolver({"urn:leaf": leaf}),
    )

    assert captured.view.is_complete
    assert captured.profile.conforms
    assert captured.profile.axioms_checked == 2


def test_direct_decoded_and_mapped_views_share_identity_metadata(tmp_path) -> None:  # type: ignore[no-untyped-def]
    direct = pyowl_core.load_snapshot(
        functional("wire", "Declaration(Class(:A))"),
        options=OPTIONS,
    )
    encoded = pyowl_core.encode_snapshot(direct)
    decoded = pyowl_core.decode_snapshot(encoded)
    path = tmp_path / "wire.pyocore"
    path.write_bytes(encoded)

    with pyowl_core.open_snapshot(path) as mapped:
        captures = tuple(capture_ontology(value) for value in (direct, decoded, mapped))

        assert all(
            item.view is value
            for item, value in zip(captures, (direct, decoded, mapped), strict=True)
        )
        assert len({item.identity.documents for item in captures}) == 1
        assert len({item.identity.import_manifest_digest for item in captures}) == 1
        assert len({item.identity.loader_diagnostics_digest for item in captures}) == 1
