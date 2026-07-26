"""Exact parity and transactional boundaries for permanent-program assembly."""

# SPDX-License-Identifier: LGPL-3.0-or-later

from __future__ import annotations

import hashlib
import json
from dataclasses import replace
from types import ModuleType, SimpleNamespace
from typing import Any, cast

import pyowl_core
import pytest
from pyowl_core.backends.native_views import produce_encoded_structural_view_v1

import pyhermit._native as native
from pyhermit import Reasoner, ReasonerConfig
from pyhermit.backends import native as native_backend
from pyhermit.backends import native_input
from pyhermit.backends.native import NativeBackendFactory
from pyhermit.backends.native_input import (
    encode_config,
    encode_ontology,
    encode_ontology_metadata,
)
from pyhermit.backends.native_wire import decode_check
from pyhermit.backends.protocol import CompiledOntology
from pyhermit.clauses.compiler import compile_captured_bundle
from pyhermit.encoded_input import ENCODED_NATIVE_FEATURE
from pyhermit.events import CancellationSource, CancellationToken
from pyhermit.exceptions import (
    BackendMismatchError,
    ReasonerInterruptedError,
    ResourceLimitError,
)
from pyhermit.inputs import capture_ontology

OPTIONS = pyowl_core.LoadOptions(
    imports=pyowl_core.ImportPolicy.IGNORE,
    backend=pyowl_core.BackendPreference.PYTHON,
)
PROGRAM_SECTIONS = {
    "symbol_domains",
    "predicates",
    "clauses",
    "positive_facts",
    "negative_facts",
    "ground_disjunctions",
    "role_model",
    "datatype_model",
    "expressivity",
    "provenance",
}


def functional(*body: str) -> bytes:
    return (
        "Prefix(:=<urn:test:permanent#>) "
        "Prefix(owl:=<http://www.w3.org/2002/07/owl#>) "
        "Ontology(<urn:test:permanent> " + " ".join(body) + ")"
    ).encode()


def _slice_record(
    snapshot: pyowl_core.OntologyView,
    *,
    posting_mode: int = 0,
    postings: memoryview | None = None,
    member_tokens: tuple[bytes, ...] = (),
    anonymous_scope_maps: tuple[memoryview, ...] = (),
) -> tuple[object, ...]:
    buffers = produce_encoded_structural_view_v1(snapshot).buffers
    return (
        posting_mode,
        memoryview(b"") if postings is None else postings,
        member_tokens,
        anonymous_scope_maps,
        buffers["root_kinds"],
        buffers["root_ids"],
        buffers["node_tags"],
        buffers["node_field_offsets"],
        buffers["field_kinds"],
        buffers["field_values"],
        buffers["field_lengths"],
        buffers["item_kinds"],
        buffers["item_values"],
        buffers["item_lengths"],
        buffers["scalar_bytes"],
    )


def _scope_map(replacements: dict[bytes, bytes]) -> memoryview:
    return memoryview(b"".join(source + target for source, target in sorted(replacements.items())))


def _composite_records(
    composite: pyowl_core.OntologyView,
    sources: tuple[pyowl_core.OntologyView, ...],
) -> tuple[tuple[object, ...], ...]:
    tokens = cast(tuple[bytes, ...], cast(Any, composite)._source_tokens())
    mappings = cast(
        tuple[dict[bytes, bytes], ...],
        cast(Any, composite)._scope_replacements(),
    )
    rows = sorted(zip(tokens, sources, mappings, strict=True), key=lambda row: row[0])
    return tuple(
        _slice_record(
            source,
            member_tokens=(token,),
            anonymous_scope_maps=(() if not mapping else (_scope_map(mapping),)),
        )
        for token, source, mapping in rows
    )


def _compiled(snapshot: pyowl_core.OntologyView) -> CompiledOntology:
    _normalized, _program, ontology = compile_captured_bundle(
        capture_ontology(snapshot).captured,
        ReasonerConfig(),
    )
    return ontology


def _manifest(
    snapshot: pyowl_core.OntologyView,
    *,
    records: tuple[tuple[object, ...], ...] | None = None,
    reference: CompiledOntology | None = None,
    reference_ir: bytes | None = None,
    max_owned_bytes: int | None = None,
    cancel_at_checkpoint: int | None = None,
) -> dict[str, object]:
    encoded = native._encoded_permanent_program_parity_v1(
        slices=records or (_slice_record(snapshot),),
        reference_ir=(
            reference_ir
            if reference_ir is not None
            else encode_ontology(reference or _compiled(snapshot))
        ),
        logical_fingerprint=memoryview(snapshot.logical_fingerprint.digest),
        max_owned_bytes=max_owned_bytes,
        cancel_at_checkpoint=cancel_at_checkpoint,
    )
    return cast(dict[str, object], json.loads(encoded))


def _direct_session(
    snapshot: pyowl_core.OntologyView,
    *,
    records: tuple[tuple[object, ...], ...] | None = None,
    reference: CompiledOntology | None = None,
    max_owned_bytes: int | None = None,
    cancel_at_checkpoint: int | None = None,
) -> Any:
    compiled = reference or _compiled(snapshot)
    return native._create_encoded_session_v1(
        slices=records or (_slice_record(snapshot),),
        metadata=encode_ontology_metadata(compiled),
        config=encode_config(ReasonerConfig()),
        cancellation=native.CancellationHandle(),
        max_owned_bytes=max_owned_bytes,
        cancel_at_checkpoint=cancel_at_checkpoint,
    )


def _check_signature(encoded: bytes) -> tuple[bool, int, int, int, int, int, int]:
    result = decode_check(encoded)
    statistics = result.statistics
    return (
        result.satisfiable,
        statistics.nodes,
        statistics.facts,
        statistics.branches,
        statistics.backtracks,
        statistics.merges,
        statistics.datatype_checks,
    )


def _assert_dense_program(program: dict[str, object]) -> None:
    domains = cast(list[dict[str, object]], program["symbol_domains"])
    assert len(domains) == 8
    for domain in domains:
        values = cast(list[dict[str, object]], domain["values"])
        assert [value["identifier"] for value in values] == list(range(len(values)))

    predicates = cast(list[dict[str, object]], program["predicates"])
    assert [value["predicate_id"] for value in predicates] == list(range(len(predicates)))
    predicate_count = len(predicates)
    for predicate in predicates:
        filler = predicate["filler_predicate_id"]
        assert filler is None or 0 <= cast(int, filler) < predicate_count

    provenance = cast(list[dict[str, object]], program["provenance"])
    assert [value["provenance_id"] for value in provenance] == list(range(len(provenance)))
    provenance_count = len(provenance)

    clauses = cast(list[dict[str, object]], program["clauses"])
    assert [value["clause_id"] for value in clauses] == list(range(len(clauses)))
    for clause in clauses:
        body = cast(list[dict[str, object]], clause["body"])
        head = cast(list[dict[str, object]], clause["head"])
        assert sorted(cast(list[int], clause["join_order"])) == list(range(len(body)))
        assert all(
            0 <= identifier < provenance_count
            for identifier in cast(list[int], clause["provenance_ids"])
        )
        for atom in body + head:
            assert 0 <= cast(int, atom["predicate_id"]) < predicate_count

    for section in ("positive_facts", "negative_facts"):
        facts = cast(list[dict[str, object]], program[section])
        for fact in facts:
            assert 0 <= cast(int, fact["predicate_id"]) < predicate_count
            assert all(
                0 <= identifier < provenance_count
                for identifier in cast(list[int], fact["provenance_ids"])
            )


def _direct_snapshot() -> pyowl_core.OntologyView:
    return pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:C))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "Declaration(NamedIndividual(:i))",
            "Declaration(NamedIndividual(:j))",
            "SubClassOf(:A :B)",
            "SubObjectPropertyOf(:p :q)",
            "SubClassOf(:B ObjectSomeValuesFrom(:q :C))",
            "ClassAssertion(:A :i)",
            "ObjectPropertyAssertion(:p :i :j)",
            "NegativeObjectPropertyAssertion(:q :j :i)",
        ),
        options=OPTIONS,
    )


def test_direct_assembly_publishes_one_complete_dense_scalar_equal_manifest() -> None:
    snapshot = _direct_snapshot()

    manifest = _manifest(snapshot)

    assert set(manifest) == {"schema_version", "program_sha256", "program"}
    assert manifest["schema_version"] == 1
    program = cast(dict[str, object], manifest["program"])
    assert set(program) == PROGRAM_SECTIONS
    encoded_program = json.dumps(
        program,
        ensure_ascii=False,
        separators=(",", ":"),
    ).encode()
    assert manifest["program_sha256"] == hashlib.sha256(encoded_program).hexdigest()
    _assert_dense_program(program)
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


def test_reversed_composite_slice_order_has_the_same_complete_program() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(ObjectProperty(:p))",
            "SubClassOf(:A ObjectSomeValuesFrom(:p :B))",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:B))",
            "Declaration(Class(:C))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "SubObjectPropertyOf(:p :q)",
            "SubClassOf(:B :C)",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))
    records = _composite_records(composite, (left, right))
    reference = _compiled(composite)

    forward = _manifest(composite, records=records, reference=reference)
    reversed_order = _manifest(
        composite,
        records=tuple(reversed(records)),
        reference=reference,
    )

    assert reversed_order == forward
    _assert_dense_program(cast(dict[str, object], forward["program"]))
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


def test_interleaved_source_local_namespaces_freeze_to_one_canonical_namespace() -> None:
    sources = (
        pyowl_core.load_snapshot(
            functional(
                "Declaration(Class(:A))",
                "Declaration(Class(:D))",
                "SubClassOf(:A :D)",
            ),
            options=OPTIONS,
        ),
        pyowl_core.load_snapshot(
            functional(
                "Declaration(Class(:A))",
                "Declaration(Class(:B))",
                "Declaration(ObjectProperty(:p))",
                "SubClassOf(:A ObjectSomeValuesFrom(:p :B))",
            ),
            options=OPTIONS,
        ),
        pyowl_core.load_snapshot(
            functional(
                "Declaration(Class(:B))",
                "Declaration(Class(:C))",
                "Declaration(ObjectProperty(:p))",
                "Declaration(ObjectProperty(:q))",
                "SubObjectPropertyOf(:p :q)",
                "SubClassOf(:B :C)",
            ),
            options=OPTIONS,
        ),
    )
    composite = pyowl_core.compose_views(
        *sources,
        roles=("left", "middle", "right"),
    )
    records = _composite_records(composite, sources)
    reference = _compiled(composite)

    canonical = _manifest(composite, records=records, reference=reference)
    first_interleaving = _manifest(
        composite,
        records=(records[2], records[0], records[1]),
        reference=reference,
    )
    second_interleaving = _manifest(
        composite,
        records=(records[1], records[2], records[0]),
        reference=reference,
    )

    assert first_interleaving == canonical == second_interleaving
    program = cast(dict[str, object], canonical["program"])
    _assert_dense_program(program)
    predicate_kinds = {
        value["kind"] for value in cast(list[dict[str, object]], program["predicates"])
    }
    assert {"Concept", "ObjectRole", "AtLeastObject"} <= predicate_kinds


def test_peak_owned_byte_limit_is_exact_and_retry_is_transactional() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "SubClassOf(:A :B)",
        ),
        options=OPTIONS,
    )
    reference = _compiled(snapshot)
    records = (_slice_record(snapshot),)
    baseline = _manifest(snapshot, records=records, reference=reference)
    lower = 0
    upper = 1 << 20
    while lower < upper:
        middle = (lower + upper) // 2
        try:
            _manifest(
                snapshot,
                records=records,
                reference=reference,
                max_owned_bytes=middle,
            )
        except ResourceLimitError:
            lower = middle + 1
        else:
            upper = middle
    minimum = lower

    assert minimum > 0
    assert (
        _manifest(
            snapshot,
            records=records,
            reference=reference,
            max_owned_bytes=minimum,
        )
        == baseline
    )
    with pytest.raises(ResourceLimitError):
        _manifest(
            snapshot,
            records=records,
            reference=reference,
            max_owned_bytes=minimum - 1,
        )
    assert _manifest(snapshot, records=records, reference=reference) == baseline


def test_clause_assembly_cancellation_discards_candidate_and_retry_succeeds() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "SubClassOf(:A :B)",
        ),
        options=OPTIONS,
    )
    reference = _compiled(snapshot)
    records = (_slice_record(snapshot),)
    baseline = _manifest(snapshot, records=records, reference=reference)

    with pytest.raises(ReasonerInterruptedError) as captured:
        _manifest(
            snapshot,
            records=records,
            reference=reference,
            cancel_at_checkpoint=33,
        )

    assert captured.value.context["phase"] == "permanent-program-clause"
    assert _manifest(snapshot, records=records, reference=reference) == baseline


def test_hostile_reference_wire_fails_closed_without_poisoning_retry() -> None:
    snapshot = _direct_snapshot()
    reference = _compiled(snapshot)
    reference_ir = encode_ontology(reference)
    baseline = _manifest(snapshot, reference=reference)

    with pytest.raises(BackendMismatchError):
        _manifest(snapshot, reference_ir=reference_ir[:-1])

    assert _manifest(snapshot, reference=reference) == baseline


def test_shared_dag_keeps_assertion_context_and_fences_ground_disjunctions() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:C))",
            "Declaration(NamedIndividual(:i))",
            "SubClassOf(ObjectUnionOf(:A :B) :C)",
            "ClassAssertion(ObjectUnionOf(:A :B) :i)",
        ),
        options=OPTIONS,
    )
    node_tags = memoryview(produce_encoded_structural_view_v1(snapshot).buffers["node_tags"]).cast(
        "H"
    )
    assert list(node_tags).count(31) == 1

    with pytest.raises(BackendMismatchError, match="ground-disjunction"):
        _manifest(snapshot)


def test_source_datatype_semantics_are_not_silently_optimized_away() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "Declaration(NamedIndividual(:i))",
            'DataPropertyAssertion(:p :i "value")',
        ),
        options=OPTIONS,
    )

    with pytest.raises(BackendMismatchError, match="datatype semantic phase"):
        _manifest(snapshot)


def test_reference_expressivity_mismatch_fails_closed_and_retry_succeeds() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "SubClassOf(:A :B)",
        ),
        options=OPTIONS,
    )
    reference = _compiled(snapshot)
    baseline = _manifest(snapshot, reference=reference)
    assert not reference.expressivity.inverse_roles
    hostile = replace(
        reference,
        expressivity=replace(reference.expressivity, inverse_roles=True),
    )

    with pytest.raises(BackendMismatchError) as captured:
        _manifest(snapshot, reference=hostile)

    assert captured.value.context["section"] == "expressivity"
    assert _manifest(snapshot, reference=reference) == baseline


def test_direct_program_publication_constructs_the_same_native_session() -> None:
    snapshot = _direct_snapshot()
    compiled = _compiled(snapshot)
    config_wire = encode_config(ReasonerConfig())
    encoded = _direct_session(snapshot, reference=compiled)
    scalar = native.create_session(
        encode_ontology(compiled),
        config_wire,
        native.CancellationHandle(),
    )
    try:
        assert encoded.ontology_fingerprint == scalar.ontology_fingerprint
        assert _check_signature(encoded.check(None)) == _check_signature(scalar.check(None))
        assert encoded.classify_classes() == scalar.classify_classes()
        assert encoded.classify_object_properties() == scalar.classify_object_properties()
    finally:
        encoded.close()
        scalar.close()
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


def test_reversed_and_interleaved_slices_publish_identical_sessions() -> None:
    sources = (
        pyowl_core.load_snapshot(
            functional(
                "Declaration(Class(:A))",
                "Declaration(Class(:D))",
                "SubClassOf(:A :D)",
            ),
            options=OPTIONS,
        ),
        pyowl_core.load_snapshot(
            functional(
                "Declaration(Class(:A))",
                "Declaration(Class(:B))",
                "Declaration(ObjectProperty(:p))",
                "SubClassOf(:A ObjectSomeValuesFrom(:p :B))",
            ),
            options=OPTIONS,
        ),
        pyowl_core.load_snapshot(
            functional(
                "Declaration(Class(:B))",
                "Declaration(Class(:C))",
                "Declaration(ObjectProperty(:p))",
                "Declaration(ObjectProperty(:q))",
                "SubObjectPropertyOf(:p :q)",
                "SubClassOf(:B :C)",
            ),
            options=OPTIONS,
        ),
    )
    composite = pyowl_core.compose_views(
        *sources,
        roles=("left", "middle", "right"),
    )
    records = _composite_records(composite, sources)
    reference = _compiled(composite)
    sessions = tuple(
        _direct_session(composite, records=order, reference=reference)
        for order in (
            records,
            tuple(reversed(records)),
            (records[2], records[0], records[1]),
        )
    )
    try:
        baseline = (
            sessions[0].ontology_fingerprint,
            _check_signature(sessions[0].check(None)),
            sessions[0].classify_classes(),
        )
        assert all(
            (
                session.ontology_fingerprint,
                _check_signature(session.check(None)),
                session.classify_classes(),
            )
            == baseline
            for session in sessions[1:]
        )
    finally:
        for session in sessions:
            session.close()


def test_direct_publication_limit_and_cancellation_discard_then_retry() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "SubClassOf(:A :B)",
        ),
        options=OPTIONS,
    )
    reference = _compiled(snapshot)
    records = (_slice_record(snapshot),)

    with pytest.raises(ResourceLimitError):
        _direct_session(
            snapshot,
            records=records,
            reference=reference,
            max_owned_bytes=1,
        )
    with pytest.raises(ReasonerInterruptedError) as captured:
        _direct_session(
            snapshot,
            records=records,
            reference=reference,
            cancel_at_checkpoint=33,
        )
    assert captured.value.context["phase"] == "permanent-program-clause"

    retry = _direct_session(snapshot, records=records, reference=reference)
    try:
        assert retry.ontology_fingerprint == reference.ontology_fingerprint
        assert retry.check(None)
    finally:
        retry.close()


def test_direct_publication_fails_closed_for_unrepresented_semantics() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "Declaration(NamedIndividual(:i))",
            'DataPropertyAssertion(:p :i "value")',
        ),
        options=OPTIONS,
    )

    with pytest.raises(BackendMismatchError, match="datatype semantic phase"):
        _direct_session(snapshot)


def test_advertised_adapter_uses_no_scalar_wire_fallback(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    snapshot = _direct_snapshot()
    compiled = _compiled(snapshot)
    direct_calls = 0

    extension = ModuleType("encoded_session_test_extension")
    extension.__version__ = native.__version__
    extension.ABI_VERSION = native.ABI_VERSION
    extension.IR_SCHEMA_VERSION = native.IR_SCHEMA_VERSION
    extension.FEATURES = tuple(sorted((*native.FEATURES, ENCODED_NATIVE_FEATURE)))
    extension.CancellationHandle = native.CancellationHandle
    extension.self_test = native.self_test

    def forbidden_scalar_constructor(*_args: object) -> object:
        raise AssertionError("scalar native session constructor was called")

    def direct_constructor(**kwargs: object) -> object:
        nonlocal direct_calls
        direct_calls += 1
        return native._create_encoded_session_v1(**kwargs)

    extension.create_session = forbidden_scalar_constructor
    extension._create_encoded_session_v1 = direct_constructor

    def forbidden_ontology_wire(_ontology: CompiledOntology) -> bytes:
        raise AssertionError("proportional ontology wire was encoded")

    monkeypatch.setattr(native_input, "encode_ontology", forbidden_ontology_wire)
    buffers = produce_encoded_structural_view_v1(snapshot).buffers
    local_lease = SimpleNamespace(buffers=buffers)
    root_slice = SimpleNamespace(
        lease=local_lease,
        posting_mode=0,
        root_ids=memoryview(b""),
        member_tokens=(),
        anonymous_scope_maps=(),
    )
    lease = SimpleNamespace(root_slices=lambda: (root_slice,))
    monkeypatch.setattr(
        native_backend,
        "negotiate_encoded_input",
        lambda *_args, **_kwargs: SimpleNamespace(lease=lease),
    )
    factory = NativeBackendFactory(extension)
    session = factory._create_encoded_session_handoff(
        snapshot,
        compiled,
        ReasonerConfig(),
        CancellationToken(),
    )
    assert session is not None
    try:
        assert direct_calls == 1
        assert session.ontology_fingerprint == compiled.ontology_fingerprint
        assert session.check(None).satisfiable
    finally:
        session.close()


def test_facade_session_dispatch_never_replays_an_observed_encoded_failure() -> None:
    snapshot = _direct_snapshot()
    compiled = _compiled(snapshot)
    reasoner = object.__new__(Reasoner)
    reasoner._config = ReasonerConfig()
    reasoner._cancellation = CancellationSource()
    reasoner._cancellation.begin_operation(timeout=None, max_memory_bytes=None)
    expected = object()
    scalar_calls = 0

    def create_encoded(
        view: object,
        ontology: object,
        config: object,
        cancellation: object,
    ) -> object:
        assert view is snapshot
        assert ontology is compiled
        assert config is reasoner._config
        assert cancellation is reasoner._cancellation.token
        return expected

    def create_scalar(*_args: object) -> object:
        nonlocal scalar_calls
        scalar_calls += 1
        raise AssertionError("scalar fallback was called")

    reasoner._factory = SimpleNamespace(
        _create_encoded_session_handoff=create_encoded,
        create_session=create_scalar,
    )
    assert reasoner._create_backend_session(snapshot, compiled) is expected
    assert scalar_calls == 0

    failure = BackendMismatchError("encoded construction failed")

    def reject_encoded(*_args: object) -> object:
        raise failure

    reasoner._factory = SimpleNamespace(
        _create_encoded_session_handoff=reject_encoded,
        create_session=create_scalar,
    )
    with pytest.raises(BackendMismatchError) as captured:
        reasoner._create_backend_session(snapshot, compiled)
    assert captured.value is failure
    assert scalar_calls == 0
