"""Exact parity and transactional boundaries for permanent-program assembly."""

# SPDX-License-Identifier: LGPL-3.0-or-later

from __future__ import annotations

import hashlib
import json
from dataclasses import replace
from types import ModuleType, SimpleNamespace
from typing import Any, cast

import pyowl_core
import pyowl_core.model as owl
import pytest
from pyowl_core import (
    DetectionBasis,
    DigestKind,
    DocumentFormat,
    DocumentProvenance,
    OntologyDocument,
    OntologyID,
)
from pyowl_core.backends.native_views import produce_encoded_structural_view_v1
from pyowl_core.extensions import swrl

import pyhermit._native as native
import pyhermit.backends.verify as verify_backend
import pyhermit.facade as facade_module
from pyhermit import Reasoner, ReasonerConfig
from pyhermit.backends import native as native_backend
from pyhermit.backends import native_input
from pyhermit.backends.native import NativeBackendFactory
from pyhermit.backends.native_context import decode_service_context
from pyhermit.backends.native_input import (
    encode_config,
    encode_encoded_session_metadata,
    encode_ontology,
    encode_ontology_metadata,
)
from pyhermit.backends.native_wire import decode_check
from pyhermit.backends.protocol import CompiledOntology
from pyhermit.backends.verify import VerifyBackendFactory
from pyhermit.clauses.compiler import compile_captured_bundle
from pyhermit.config import UnsupportedDatatypePolicy
from pyhermit.core import capture_compatible_view
from pyhermit.datatypes import SUPPORTED_DATATYPES
from pyhermit.encoded_input import (
    ENCODED_BUFFER_WIDTHS,
    ENCODED_NATIVE_FEATURE,
    _validate_encoded_view,
)
from pyhermit.events import CancellationSource, CancellationToken
from pyhermit.exceptions import (
    BackendMismatchError,
    DisposedReasonerError,
    OntologyProfileError,
    ReasonerInterruptedError,
    ResourceLimitError,
    UnsupportedDatatypeError,
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


def _encoded_negotiation(view: pyowl_core.OntologyView) -> object:
    encoded = produce_encoded_structural_view_v1(view)
    lease = _validate_encoded_view(
        view,
        encoded,
        pyowl_core.AxiomScope.CLOSURE,
        document_key=None,
        active=frozenset(),
        validated={},
    )
    return SimpleNamespace(lease=lease)


def _advertise_encoded_compiler(extension: ModuleType) -> None:
    extension.FEATURES = tuple(sorted((*native.FEATURES, ENCODED_NATIVE_FEATURE)))
    extension._validate_encoded_columns_v1 = native._validate_encoded_columns_v1
    extension._validate_encoded_slices_v1 = native._validate_encoded_slices_v1
    extension._encoded_profile_slices_manifest_v1 = native._encoded_profile_slices_manifest_v1


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


def _compiled(
    snapshot: pyowl_core.OntologyView,
    *,
    config: ReasonerConfig | None = None,
) -> CompiledOntology:
    selected_config = ReasonerConfig() if config is None else config
    _normalized, _program, ontology = compile_captured_bundle(
        capture_ontology(snapshot, config=selected_config).captured,
        selected_config,
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
    selected_reference = reference
    if reference_ir is None and selected_reference is None:
        selected_reference = _compiled(snapshot)
    encoded = native._encoded_permanent_program_parity_v1(
        slices=records or (_slice_record(snapshot),),
        reference_ir=(
            reference_ir
            if reference_ir is not None
            else encode_ontology(cast(CompiledOntology, selected_reference))
        ),
        logical_fingerprint=memoryview(snapshot.logical_fingerprint.digest),
        max_owned_bytes=max_owned_bytes,
        cancel_at_checkpoint=cancel_at_checkpoint,
    )
    manifest = cast(dict[str, object], json.loads(encoded))
    if selected_reference is not None:
        scalar_program = native_input._program_from_ontology(selected_reference)
        expected_digest = hashlib.sha256(scalar_program.canonical_bytes()).hexdigest()
        assert manifest["program_sha256"] == expected_digest
    return manifest


def _direct_session(
    snapshot: pyowl_core.OntologyView,
    *,
    records: tuple[tuple[object, ...], ...] | None = None,
    reference: CompiledOntology | None = None,
    config: ReasonerConfig | None = None,
    max_owned_bytes: int | None = None,
    cancel_at_checkpoint: int | None = None,
) -> Any:
    selected_config = ReasonerConfig() if config is None else config
    compiled = reference or _compiled(snapshot, config=selected_config)
    session = native._create_encoded_session_v1(
        slices=records or (_slice_record(snapshot),),
        metadata=encode_ontology_metadata(compiled),
        config=encode_config(selected_config),
        cancellation=native.CancellationHandle(),
        max_owned_bytes=max_owned_bytes,
        cancel_at_checkpoint=cancel_at_checkpoint,
    )
    try:
        assert session.compiler_digest == facade_module._canonical_compiler_digest(compiled)
    except BaseException:
        session.close()
        raise
    return session


def _direct_lifecycle_session(
    snapshot: pyowl_core.OntologyView,
    *,
    records: tuple[tuple[object, ...], ...] | None = None,
    config: ReasonerConfig | None = None,
    cancellation: native.CancellationHandle | None = None,
    max_owned_bytes: int | None = None,
    cancel_at_checkpoint: int | None = None,
) -> Any:
    selected_config = ReasonerConfig() if config is None else config
    captured = capture_ontology(snapshot, config=selected_config).captured
    return native._create_encoded_session_v1(
        slices=records or (_slice_record(snapshot),),
        metadata=encode_encoded_session_metadata(captured, selected_config),
        config=encode_config(selected_config),
        cancellation=native.CancellationHandle() if cancellation is None else cancellation,
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


def _extension_snapshot() -> pyowl_core.OntologyView:
    class_a = owl.Class(owl.IRI("urn:test:permanent#A"))
    variable = swrl.Variable(owl.IRI("urn:test:permanent#x"))
    rule = swrl.SWRLRule(
        owl.CanonicalSet((swrl.ClassAtom(class_a, variable),)),
        owl.CanonicalSet((swrl.ClassAtom(class_a, variable),)),
    )
    provenance = DocumentProvenance(
        hashlib.sha256(b"permanent-extension").digest(),
        DigestKind.EXACT_BYTES,
        0,
        0,
        None,
        None,
        DocumentFormat.FUNCTIONAL,
        DetectionBasis.EXPLICIT,
    )
    document = OntologyDocument(
        OntologyID(owl.IRI("urn:test:permanent:extension")),
        None,
        (),
        owl.CanonicalSet(),
        owl.CanonicalSet((owl.Declaration(class_a),)),
        owl.CanonicalSet((rule,)),
        provenance,
    )
    return pyowl_core.load_snapshot(document, options=OPTIONS)


def _object_query_snapshot() -> pyowl_core.OntologyView:
    return pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:C))",
            "Declaration(Class(:D))",
            "EquivalentClasses(:B :C)",
            "SubClassOf(:A :B)",
            "DisjointClasses(:C :D)",
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "Declaration(ObjectProperty(:qInverse))",
            "SubObjectPropertyOf(:p :q)",
            "InverseObjectProperties(:q :qInverse)",
            "ObjectPropertyDomain(:q :B)",
            "ObjectPropertyRange(:q :D)",
            "Declaration(NamedIndividual(:i))",
            "Declaration(NamedIndividual(:j))",
            "Declaration(NamedIndividual(:other))",
            "ClassAssertion(:A :i)",
            "ObjectPropertyAssertion(:p :i :j)",
            "NegativeObjectPropertyAssertion(:q :j :i)",
            "DifferentIndividuals(:i :other)",
        ),
        options=OPTIONS,
    )


def _object_service_results(reasoner: Reasoner) -> dict[str, object]:
    base = "urn:test:permanent#"
    a, b, c, d = (owl.Class(owl.IRI(f"{base}{local}")) for local in ("A", "B", "C", "D"))
    p, q, _inverse = (
        owl.ObjectProperty(owl.IRI(f"{base}{local}")) for local in ("p", "q", "qInverse")
    )
    i, j, other = (owl.NamedIndividual(owl.IRI(f"{base}{local}")) for local in ("i", "j", "other"))
    impossible = owl.ObjectIntersectionOf(owl.CanonicalSet((c, d)))
    expressions = {
        "named": a,
        "intersection-negation": owl.ObjectIntersectionOf(
            owl.CanonicalSet((a, owl.ObjectComplementOf(b)))
        ),
        "union": owl.ObjectUnionOf(owl.CanonicalSet((a, d))),
        "complement": owl.ObjectComplementOf(d),
        "one-of": owl.ObjectOneOf(owl.CanonicalSet((i, j))),
        "some": owl.ObjectSomeValuesFrom(p, d),
        "all": owl.ObjectAllValuesFrom(q, d),
        "has-value": owl.ObjectHasValue(p, j),
        "has-self": owl.ObjectHasSelf(q),
        "minimum": owl.ObjectMinCardinality(2, p, d),
        "maximum": owl.ObjectMaxCardinality(1, p, d),
        "exact": owl.ObjectExactCardinality(1, p, d),
    }
    entailed_axioms = (
        owl.SubClassOf(a, c),
        owl.SubObjectPropertyOf(p, q),
        owl.ObjectPropertyDomain(q, b),
        owl.ObjectPropertyRange(q, d),
        owl.ClassAssertion(c, i),
        owl.ObjectPropertyAssertion(q, i, j),
        owl.NegativeObjectPropertyAssertion(q, j, i),
        owl.DifferentIndividuals(owl.CanonicalSet((i, other))),
    )
    return {
        "class_disjoint": reasoner.disjoint_classes(c),
        "class_equivalent": reasoner.equivalent_classes(b),
        "class_hierarchy": reasoner.class_hierarchy(),
        "class_sub_direct": reasoner.subclasses(c, direct=True),
        "class_subclass": reasoner.is_subclass(a, c),
        "class_super": reasoner.superclasses(a),
        "class_unsatisfiable": reasoner.unsatisfiable_classes(),
        "consistent": reasoner.is_consistent(),
        "different": reasoner.different_individuals(i),
        "entails_all": reasoner.entails_all(entailed_axioms),
        "entails_each": tuple(reasoner.entails(axiom) for axiom in entailed_axioms),
        "has_object_relationship": reasoner.has_object_property_relationship(i, q, j),
        "has_type": reasoner.has_type(i, c),
        "instances": reasoner.instances(c),
        "object_disjoint": reasoner.disjoint_object_properties(p),
        "object_domain": reasoner.object_property_domains(q),
        "object_equivalent": reasoner.equivalent_object_properties(q),
        "object_hierarchy": reasoner.object_property_hierarchy(),
        "object_instances": reasoner.object_property_instances(q),
        "object_inverse": reasoner.inverse_object_properties(q),
        "object_range": reasoner.object_property_ranges(q),
        "object_sub": reasoner.sub_object_properties(q),
        "object_super_direct": reasoner.super_object_properties(p, direct=True),
        "object_values": reasoner.object_property_values(i, q),
        "object_expression_queries": {
            family: (
                reasoner.is_satisfiable(expression),
                reasoner.is_subclass(expression, b),
                reasoner.is_subclass(b, expression),
                reasoner.entails(owl.ClassAssertion(expression, i)),
                reasoner.entails(owl.SubClassOf(expression, b)),
                reasoner.entails(owl.SubClassOf(b, expression)),
                reasoner.entails(
                    owl.EquivalentClasses(owl.CanonicalSet((expression, b)))
                ),
                reasoner.entails(
                    owl.DisjointClasses(owl.CanonicalSet((expression, b)))
                ),
                reasoner.has_type(i, expression),
                reasoner.has_type(i, expression, direct=True),
                reasoner.instances(expression),
                reasoner.instances(expression, direct=True),
                reasoner.equivalent_classes(expression),
                reasoner.superclasses(expression),
                reasoner.superclasses(expression, direct=True),
                reasoner.subclasses(expression),
                reasoner.subclasses(expression, direct=True),
                reasoner.disjoint_classes(expression),
            )
            for family, expression in expressions.items()
        },
        "same": reasoner.same_individuals(i),
        "satisfiable": reasoner.is_satisfiable(a),
        "unsatisfiable_expression": reasoner.is_satisfiable(impossible),
        "types": reasoner.types(i),
    }


def _data_query_snapshot() -> pyowl_core.OntologyView:
    return pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(DataProperty(:d))",
            "Declaration(DataProperty(:e))",
            "Declaration(DataProperty(:f))",
            "Declaration(DataProperty(:g))",
            "SubDataPropertyOf(:d :e)",
            "EquivalentDataProperties(:e :f)",
            "DisjointDataProperties(:d :g)",
            "FunctionalDataProperty(:e)",
            "DataPropertyDomain(:e :A)",
            "DataPropertyRange(:e <http://www.w3.org/2000/01/rdf-schema#Literal>)",
            "Declaration(NamedIndividual(:i))",
            "ClassAssertion(:A :i)",
            "SubClassOf(:A DataSomeValuesFrom("
            ":d <http://www.w3.org/2000/01/rdf-schema#Literal>))",
        ),
        options=OPTIONS,
    )


def _data_service_results(reasoner: Reasoner) -> dict[str, object]:
    base = "urn:test:permanent#"
    a, b = (owl.Class(owl.IRI(f"{base}{local}")) for local in ("A", "B"))
    d, e, f, g = (
        owl.DataProperty(owl.IRI(f"{base}{local}")) for local in ("d", "e", "f", "g")
    )
    i = owl.NamedIndividual(owl.IRI(f"{base}i"))
    expressions = {
        "some": owl.DataSomeValuesFrom((d,), owl.RDFS_LITERAL),
        "all": owl.DataAllValuesFrom((e,), owl.RDFS_LITERAL),
        "minimum": owl.DataMinCardinality(2, d, owl.RDFS_LITERAL),
        "maximum": owl.DataMaxCardinality(1, e, owl.RDFS_LITERAL),
        "exact": owl.DataExactCardinality(1, d, owl.RDFS_LITERAL),
    }
    entailed_axioms = (
        owl.SubDataPropertyOf(d, e),
        owl.EquivalentDataProperties(owl.CanonicalSet((e, f))),
        owl.DisjointDataProperties(owl.CanonicalSet((d, g))),
        owl.FunctionalDataProperty(e),
        owl.DataPropertyDomain(e, a),
    )
    return {
        "data_disjoint": reasoner.disjoint_data_properties(d),
        "data_domain": reasoner.data_property_domains(e),
        "data_equivalent": reasoner.equivalent_data_properties(e),
        "data_hierarchy": reasoner.data_property_hierarchy(),
        "data_sub": reasoner.sub_data_properties(e),
        "data_super_direct": reasoner.super_data_properties(d, direct=True),
        "data_values": reasoner.data_property_values(i, d),
        "entails_all": reasoner.entails_all(entailed_axioms),
        "entails_each": tuple(reasoner.entails(axiom) for axiom in entailed_axioms),
        "expression_queries": {
            family: (
                reasoner.is_satisfiable(expression),
                reasoner.is_subclass(expression, b),
                reasoner.is_subclass(b, expression),
                reasoner.entails(owl.ClassAssertion(expression, i)),
                reasoner.entails(owl.SubClassOf(expression, b)),
                reasoner.entails(owl.SubClassOf(b, expression)),
                reasoner.entails(
                    owl.EquivalentClasses(owl.CanonicalSet((expression, b)))
                ),
                reasoner.entails(
                    owl.DisjointClasses(owl.CanonicalSet((expression, b)))
                ),
                reasoner.has_type(i, expression),
                reasoner.has_type(i, expression, direct=True),
                reasoner.instances(expression),
                reasoner.instances(expression, direct=True),
                reasoner.equivalent_classes(expression),
                reasoner.superclasses(expression),
                reasoner.superclasses(expression, direct=True),
                reasoner.subclasses(expression),
                reasoner.subclasses(expression, direct=True),
                reasoner.disjoint_classes(expression),
            )
            for family, expression in expressions.items()
        },
    }


def test_direct_assembly_publishes_one_complete_dense_scalar_equal_manifest() -> None:
    snapshot = _direct_snapshot()

    manifest = _manifest(snapshot)

    assert set(manifest) == {"schema_version", "program_sha256", "program"}
    assert manifest["schema_version"] == 1
    program = cast(dict[str, object], manifest["program"])
    assert set(program) == PROGRAM_SECTIONS
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
            cancel_at_checkpoint=34,
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


def test_shared_union_dag_has_exact_scalar_program_without_ground_disjunctions() -> None:
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

    manifest = _manifest(snapshot)

    assert cast(dict[str, object], manifest["program"])["ground_disjunctions"] == []


@pytest.mark.parametrize(
    "expression",
    (
        ":A",
        "ObjectIntersectionOf(:A :B)",
        "ObjectUnionOf(:A :B)",
        "ObjectComplementOf(:A)",
        "ObjectOneOf(:i :j)",
        "ObjectSomeValuesFrom(:p :A)",
        "ObjectAllValuesFrom(:p :A)",
        "ObjectHasValue(:p :i)",
        "ObjectHasSelf(:p)",
        "ObjectMinCardinality(2 :p :A)",
        "ObjectMaxCardinality(2 :p :A)",
        "ObjectExactCardinality(2 :p :A)",
    ),
    ids=(
        "named",
        "intersection",
        "union",
        "complement",
        "one-of",
        "some",
        "all",
        "has-value",
        "has-self",
        "minimum",
        "maximum",
        "exact",
    ),
)
def test_supported_object_expression_families_have_complete_program_parity(
    expression: str,
) -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:C))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(NamedIndividual(:i))",
            "Declaration(NamedIndividual(:j))",
            f"SubClassOf({expression} :C)",
            f"SubClassOf(:C {expression})",
            f"ClassAssertion({expression} :i)",
        ),
        options=OPTIONS,
    )

    manifest = _manifest(snapshot)

    _assert_dense_program(cast(dict[str, object], manifest["program"]))


def test_conjunction_with_negated_superclass_is_inconsistent_with_scalar_parity() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(NamedIndividual(:i))",
            "SubClassOf(:A :B)",
            "ClassAssertion(ObjectIntersectionOf(:A ObjectComplementOf(:B)) :i)",
        ),
        options=OPTIONS,
    )
    compiled = _compiled(snapshot)
    _manifest(snapshot, reference=compiled)
    encoded = _direct_lifecycle_session(snapshot)
    scalar = native.create_session(
        encode_ontology(compiled),
        encode_config(ReasonerConfig()),
        native.CancellationHandle(),
    )
    try:
        encoded_check = _check_signature(encoded.check(None))
        scalar_check = _check_signature(scalar.check(None))

        assert encoded_check == scalar_check
        assert not encoded_check[0]
    finally:
        encoded.close()
        scalar.close()


@pytest.mark.parametrize(
    "expression",
    (
        "DataSomeValuesFrom(:d <http://www.w3.org/2000/01/rdf-schema#Literal>)",
        "DataAllValuesFrom(:d <http://www.w3.org/2000/01/rdf-schema#Literal>)",
        "DataMinCardinality(2 :d <http://www.w3.org/2000/01/rdf-schema#Literal>)",
        "DataMaxCardinality(2 :d <http://www.w3.org/2000/01/rdf-schema#Literal>)",
        "DataExactCardinality(2 :d <http://www.w3.org/2000/01/rdf-schema#Literal>)",
    ),
    ids=("some", "all", "minimum", "maximum", "exact"),
)
def test_default_data_expression_families_have_program_and_reasoning_parity(
    expression: str,
) -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(DataProperty(:d))",
            "Declaration(NamedIndividual(:i))",
            f"SubClassOf({expression} :A)",
            f"SubClassOf(:B {expression})",
            f"ClassAssertion({expression} :i)",
        ),
        options=OPTIONS,
    )
    compiled = _compiled(snapshot)
    manifest = _manifest(snapshot, reference=compiled)
    encoded = _direct_lifecycle_session(snapshot)
    scalar = native.create_session(
        encode_ontology(compiled),
        encode_config(ReasonerConfig()),
        native.CancellationHandle(),
    )
    try:
        assert _check_signature(encoded.check(None)) == _check_signature(scalar.check(None))
        assert encoded.classify_data_properties() == scalar.classify_data_properties()
        _assert_dense_program(cast(dict[str, object], manifest["program"]))
    finally:
        encoded.close()
        scalar.close()


def test_default_data_property_schema_has_complete_program_parity() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(DataProperty(:d))",
            "Declaration(DataProperty(:e))",
            "Declaration(DataProperty(:f))",
            "Declaration(DataProperty(:g))",
            "SubDataPropertyOf(:d :e)",
            "EquivalentDataProperties(:e :f)",
            "DisjointDataProperties(:d :g)",
            "FunctionalDataProperty(:e)",
            "DataPropertyDomain(:e :A)",
            "DataPropertyRange(:e <http://www.w3.org/2000/01/rdf-schema#Literal>)",
        ),
        options=OPTIONS,
    )
    compiled = _compiled(snapshot)
    _manifest(snapshot, reference=compiled)
    encoded = _direct_lifecycle_session(snapshot)
    scalar = native.create_session(
        encode_ontology(compiled),
        encode_config(ReasonerConfig()),
        native.CancellationHandle(),
    )
    try:
        assert _check_signature(encoded.check(None)) == _check_signature(scalar.check(None))
        assert encoded.classify_data_properties() == scalar.classify_data_properties()
    finally:
        encoded.close()
        scalar.close()


def test_plain_literal_source_semantics_have_exact_program_parity() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "Declaration(NamedIndividual(:i))",
            'DataPropertyAssertion(:p :i "value")',
        ),
        options=OPTIONS,
    )

    _manifest(snapshot)


def test_xsd_string_literal_semantics_have_exact_program_and_session_parity() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "Declaration(NamedIndividual(:i))",
            "DataPropertyAssertion(:p :i "
            '"hello world"^^<http://www.w3.org/2001/XMLSchema#string>)',
        ),
        options=OPTIONS,
    )
    compiled = _compiled(snapshot)
    manifest = _manifest(snapshot, reference=compiled)
    encoded = _direct_lifecycle_session(snapshot)
    scalar = native.create_session(
        encode_ontology(compiled),
        encode_config(ReasonerConfig()),
        native.CancellationHandle(),
    )
    try:
        assert _check_signature(encoded.check(None)) == _check_signature(scalar.check(None))
        assert encoded.realize() == scalar.realize()
        datatype_model = cast(dict[str, object], manifest["program"])["datatype_model"]
        assert len(cast(dict[str, object], datatype_model)["literal_identities"]) == 1
    finally:
        encoded.close()
        scalar.close()


@pytest.mark.parametrize(
    "assertions",
    (
        (
            "DataPropertyAssertion(:p :i "
            '"true"^^<http://www.w3.org/2001/XMLSchema#boolean>)',
            "DataPropertyAssertion(:p :i "
            '"1"^^<http://www.w3.org/2001/XMLSchema#boolean>)',
        ),
        (
            "DataPropertyAssertion(:p :i "
            '"+01"^^<http://www.w3.org/2001/XMLSchema#int>)',
            "DataPropertyAssertion(:p :i "
            '"1.0"^^<http://www.w3.org/2001/XMLSchema#decimal>)',
            "DataPropertyAssertion(:p :i "
            '"1/1"^^<http://www.w3.org/2002/07/owl#rational>)',
        ),
    ),
    ids=("boolean-aliases", "cross-datatype-numeric-aliases"),
)
def test_boolean_and_exact_numeric_literal_semantics_have_program_and_session_parity(
    assertions: tuple[str, ...],
) -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "Declaration(NamedIndividual(:i))",
            *assertions,
        ),
        options=OPTIONS,
    )
    compiled = _compiled(snapshot)
    manifest = _manifest(snapshot, reference=compiled)
    datatype_model = cast(dict[str, object], manifest["program"])["datatype_model"]
    identities = cast(
        list[dict[str, object]],
        cast(dict[str, object], datatype_model)["literal_identities"],
    )
    assert len(identities) == len(assertions)
    assert len({identity["data_identity_id"] for identity in identities}) == 1

    encoded = _direct_lifecycle_session(snapshot)
    scalar = native.create_session(
        encode_ontology(compiled),
        encode_config(ReasonerConfig()),
        native.CancellationHandle(),
    )
    try:
        assert _check_signature(encoded.check(None)) == _check_signature(scalar.check(None))
        assert encoded.realize() == scalar.realize()
    finally:
        encoded.close()
        scalar.close()


@pytest.mark.parametrize("datatype_iri", sorted(SUPPORTED_DATATYPES))
def test_supported_named_datatype_ranges_have_exact_program_parity(
    datatype_iri: str,
) -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(DataProperty(:d))",
            f"SubClassOf(:A DataSomeValuesFrom(:d <{datatype_iri}>))",
        ),
        options=OPTIONS,
    )

    _manifest(snapshot)


@pytest.mark.parametrize(
    "datatype_iri",
    (
        "http://www.w3.org/2001/XMLSchema#int",
        "http://www.w3.org/2001/XMLSchema#boolean",
        "http://www.w3.org/2001/XMLSchema#dateTime",
    ),
    ids=("integer", "boolean", "date-time"),
)
def test_representative_named_datatype_ranges_have_runtime_parity(
    datatype_iri: str,
) -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(DataProperty(:d))",
            "Declaration(NamedIndividual(:i))",
            f"SubClassOf(:A DataSomeValuesFrom(:d <{datatype_iri}>))",
            "ClassAssertion(:A :i)",
        ),
        options=OPTIONS,
    )
    compiled = _compiled(snapshot)
    encoded = _direct_lifecycle_session(snapshot)
    scalar = native.create_session(
        encode_ontology(compiled),
        encode_config(ReasonerConfig()),
        native.CancellationHandle(),
    )
    try:
        assert _check_signature(encoded.check(None)) == _check_signature(scalar.check(None))
        assert encoded.classify_data_properties() == scalar.classify_data_properties()
    finally:
        encoded.close()
        scalar.close()


def test_complemented_named_datatype_ranges_have_program_and_runtime_parity() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(DataProperty(:d))",
            "Declaration(DataProperty(:e))",
            "Declaration(NamedIndividual(:i))",
            "SubClassOf(:A DataSomeValuesFrom(:d DataComplementOf("
            "<http://www.w3.org/2001/XMLSchema#int>)))",
            "SubClassOf(DataAllValuesFrom(:d DataComplementOf("
            "<http://www.w3.org/2001/XMLSchema#string>)) :B)",
            "SubClassOf(:A DataMinCardinality(2 :e DataComplementOf("
            "<http://www.w3.org/2001/XMLSchema#boolean>)))",
            "SubClassOf(DataMaxCardinality(3 :e DataComplementOf("
            "<http://www.w3.org/2001/XMLSchema#decimal>)) :B)",
            "SubClassOf(:A DataExactCardinality(1 :e DataComplementOf("
            "<http://www.w3.org/2001/XMLSchema#integer>)))",
            "DataPropertyRange(:e DataComplementOf("
            "<http://www.w3.org/2001/XMLSchema#double>))",
            "ClassAssertion(:A :i)",
        ),
        options=OPTIONS,
    )
    compiled = _compiled(snapshot)
    _manifest(snapshot, reference=compiled)
    encoded = _direct_lifecycle_session(snapshot)
    scalar = native.create_session(
        encode_ontology(compiled),
        encode_config(ReasonerConfig()),
        native.CancellationHandle(),
    )
    try:
        assert _check_signature(encoded.check(None)) == _check_signature(scalar.check(None))
        assert encoded.classify_classes() == scalar.classify_classes()
        assert encoded.classify_data_properties() == scalar.classify_data_properties()
    finally:
        encoded.close()
        scalar.close()


def test_boolean_composite_named_datatype_ranges_have_program_and_runtime_parity() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(DataProperty(:d))",
            "Declaration(DataProperty(:e))",
            "SubClassOf(:A DataSomeValuesFrom(:d DataIntersectionOf("
            "<http://www.w3.org/2001/XMLSchema#int> "
            "<http://www.w3.org/2001/XMLSchema#boolean>)))",
            "SubClassOf(DataAllValuesFrom(:d DataUnionOf("
            "<http://www.w3.org/2001/XMLSchema#string> "
            "<http://www.w3.org/2001/XMLSchema#integer>)) :B)",
            "SubClassOf(:A DataMinCardinality(2 :e DataIntersectionOf("
            "<http://www.w3.org/2001/XMLSchema#boolean> "
            "DataComplementOf(<http://www.w3.org/2001/XMLSchema#string>))))",
            "SubClassOf(DataMaxCardinality(3 :e DataUnionOf("
            "<http://www.w3.org/2001/XMLSchema#decimal> "
            "<http://www.w3.org/2001/XMLSchema#double>)) :B)",
            "SubClassOf(:A DataExactCardinality(1 :e DataIntersectionOf("
            "<http://www.w3.org/2001/XMLSchema#string> "
            "DataUnionOf(<http://www.w3.org/2001/XMLSchema#integer> "
            "<http://www.w3.org/2001/XMLSchema#boolean>))))",
            "DataPropertyRange(:e DataUnionOf("
            "<http://www.w3.org/2001/XMLSchema#int> "
            "DataComplementOf(<http://www.w3.org/2001/XMLSchema#boolean>)))",
        ),
        options=OPTIONS,
    )
    compiled = _compiled(snapshot)
    _manifest(snapshot, reference=compiled)
    encoded = _direct_lifecycle_session(snapshot)
    scalar = native.create_session(
        encode_ontology(compiled),
        encode_config(ReasonerConfig()),
        native.CancellationHandle(),
    )
    try:
        assert _check_signature(encoded.check(None)) == _check_signature(scalar.check(None))
        with pytest.raises(UnsupportedDatatypeError) as encoded_classes:
            encoded.classify_classes()
        with pytest.raises(UnsupportedDatatypeError) as scalar_classes:
            scalar.classify_classes()
        assert str(encoded_classes.value) == str(scalar_classes.value)

        with pytest.raises(UnsupportedDatatypeError) as encoded_data_properties:
            encoded.classify_data_properties()
        with pytest.raises(UnsupportedDatatypeError) as scalar_data_properties:
            scalar.classify_data_properties()
        assert str(encoded_data_properties.value) == str(scalar_data_properties.value)
    finally:
        encoded.close()
        scalar.close()


def test_enumerated_data_ranges_have_program_and_runtime_parity() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(DataProperty(:d))",
            "Declaration(DataProperty(:e))",
            "SubClassOf(:A DataSomeValuesFrom(:d DataOneOf("
            '"1"^^<http://www.w3.org/2001/XMLSchema#integer> '
            '"+1"^^<http://www.w3.org/2001/XMLSchema#integer> '
            '"alpha" '
            '"true"^^<http://www.w3.org/2001/XMLSchema#boolean>)))',
            "SubClassOf(DataAllValuesFrom(:d DataComplementOf(DataOneOf("
            '"beta" '
            '"false"^^<http://www.w3.org/2001/XMLSchema#boolean>))) :B)',
            "SubClassOf(:A DataMinCardinality(2 :e DataOneOf("
            '"-0"^^<http://www.w3.org/2001/XMLSchema#float> '
            '"+0"^^<http://www.w3.org/2001/XMLSchema#float>)))',
            "DataPropertyRange(:e DataUnionOf(DataOneOf("
            '"2024-01-01T00:00:00Z"^^'
            "<http://www.w3.org/2001/XMLSchema#dateTime> "
            '"0A"^^<http://www.w3.org/2001/XMLSchema#hexBinary>) '
            "<http://www.w3.org/2001/XMLSchema#string>))",
        ),
        options=OPTIONS,
    )
    compiled = _compiled(snapshot)
    manifest = _manifest(snapshot, reference=compiled)
    datatype_model = cast(
        dict[str, object],
        cast(dict[str, object], manifest["program"])["datatype_model"],
    )
    semantic_model = cast(
        dict[str, object],
        json.loads(cast(str, datatype_model["semantic_payload_json"])),
    )
    enumerations = [
        cast(dict[str, object], value)
        for value in cast(list[object], semantic_model["data_ranges"])
        if cast(dict[str, object], value)["kind"] == "enumeration"
    ]
    lexical_forms = {
        cast(str, literal["lexical_form"])
        for enumeration in enumerations
        for literal in cast(list[dict[str, object]], enumeration["values"])
    }
    assert {"1", "+1", "alpha", "true", "-0", "+0"} <= lexical_forms

    encoded = _direct_lifecycle_session(snapshot)
    scalar = native.create_session(
        encode_ontology(compiled),
        encode_config(ReasonerConfig()),
        native.CancellationHandle(),
    )
    try:
        assert _check_signature(encoded.check(None)) == _check_signature(scalar.check(None))
        with pytest.raises(UnsupportedDatatypeError) as encoded_classes:
            encoded.classify_classes()
        with pytest.raises(UnsupportedDatatypeError) as scalar_classes:
            scalar.classify_classes()
        assert str(encoded_classes.value) == str(scalar_classes.value)

        with pytest.raises(UnsupportedDatatypeError) as encoded_data_properties:
            encoded.classify_data_properties()
        with pytest.raises(UnsupportedDatatypeError) as scalar_data_properties:
            scalar.classify_data_properties()
        assert str(encoded_data_properties.value) == str(scalar_data_properties.value)
    finally:
        encoded.close()
        scalar.close()


@pytest.mark.parametrize(
    "restriction",
    (
        (
            "DatatypeRestriction(<http://www.w3.org/2001/XMLSchema#integer> "
            "<http://www.w3.org/2001/XMLSchema#minInclusive> "
            '"0"^^<http://www.w3.org/2001/XMLSchema#integer> '
            "<http://www.w3.org/2001/XMLSchema#maxExclusive> "
            '"10"^^<http://www.w3.org/2001/XMLSchema#integer>)'
        ),
        (
            "DatatypeRestriction(<http://www.w3.org/2001/XMLSchema#decimal> "
            "<http://www.w3.org/2001/XMLSchema#minExclusive> "
            '"0.5"^^<http://www.w3.org/2001/XMLSchema#decimal> '
            "<http://www.w3.org/2001/XMLSchema#maxInclusive> "
            '"9.5"^^<http://www.w3.org/2001/XMLSchema#decimal>)'
        ),
        (
            "DatatypeRestriction(<http://www.w3.org/2001/XMLSchema#float> "
            "<http://www.w3.org/2001/XMLSchema#minExclusive> "
            '"-0"^^<http://www.w3.org/2001/XMLSchema#float> '
            "<http://www.w3.org/2001/XMLSchema#maxInclusive> "
            '"INF"^^<http://www.w3.org/2001/XMLSchema#float>)'
        ),
        (
            "DatatypeRestriction(<http://www.w3.org/2001/XMLSchema#dateTime> "
            "<http://www.w3.org/2001/XMLSchema#minInclusive> "
            '"2024-01-01T00:00:00Z"^^'
            "<http://www.w3.org/2001/XMLSchema#dateTime> "
            "<http://www.w3.org/2001/XMLSchema#maxExclusive> "
            '"2025-01-01T00:00:00Z"^^'
            "<http://www.w3.org/2001/XMLSchema#dateTime>)"
        ),
        (
            "DatatypeRestriction(<http://www.w3.org/2001/XMLSchema#hexBinary> "
            "<http://www.w3.org/2001/XMLSchema#length> "
            '"2"^^<http://www.w3.org/2001/XMLSchema#integer> '
            "<http://www.w3.org/2001/XMLSchema#minLength> "
            '"1"^^<http://www.w3.org/2001/XMLSchema#integer> '
            "<http://www.w3.org/2001/XMLSchema#maxLength> "
            '"3"^^<http://www.w3.org/2001/XMLSchema#integer>)'
        ),
        (
            "DatatypeRestriction(<http://www.w3.org/2001/XMLSchema#string> "
            "<http://www.w3.org/2001/XMLSchema#length> "
            '"3"^^<http://www.w3.org/2001/XMLSchema#integer> '
            "<http://www.w3.org/2001/XMLSchema#pattern> "
            '"[a-z]+")'
        ),
        (
            "DatatypeRestriction(<http://www.w3.org/2001/XMLSchema#anyURI> "
            "<http://www.w3.org/2001/XMLSchema#minLength> "
            '"1"^^<http://www.w3.org/2001/XMLSchema#integer> '
            "<http://www.w3.org/2001/XMLSchema#pattern> "
            '"https://.*")'
        ),
        (
            "DatatypeRestriction("
            "<http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral> "
            "<http://www.w3.org/1999/02/22-rdf-syntax-ns#langRange> "
            '"en")'
        ),
    ),
    ids=(
        "exact-numeric",
        "decimal",
        "ieee",
        "date-time",
        "binary-lengths",
        "string",
        "uri",
        "language",
    ),
)
def test_datatype_restriction_families_have_program_and_runtime_parity(
    restriction: str,
) -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:d))",
            f"DataPropertyRange(:d {restriction})",
        ),
        options=OPTIONS,
    )
    compiled = _compiled(snapshot)
    manifest = _manifest(snapshot, reference=compiled)
    datatype_model = cast(
        dict[str, object],
        cast(dict[str, object], manifest["program"])["datatype_model"],
    )
    semantic_model = cast(
        dict[str, object],
        json.loads(cast(str, datatype_model["semantic_payload_json"])),
    )
    assert any(
        cast(dict[str, object], value)["kind"] == "restriction"
        for value in cast(list[object], semantic_model["data_ranges"])
    )

    encoded = _direct_lifecycle_session(snapshot)
    scalar = native.create_session(
        encode_ontology(compiled),
        encode_config(ReasonerConfig()),
        native.CancellationHandle(),
    )
    try:
        assert _check_signature(encoded.check(None)) == _check_signature(scalar.check(None))
        assert encoded.classify_data_properties() == scalar.classify_data_properties()
    finally:
        encoded.close()
        scalar.close()


def test_nested_datatype_restrictions_have_exact_fail_closed_runtime_parity() -> None:
    restriction = (
        "DatatypeRestriction(<http://www.w3.org/2001/XMLSchema#integer> "
        "<http://www.w3.org/2001/XMLSchema#minInclusive> "
        '"0"^^<http://www.w3.org/2001/XMLSchema#integer>)'
    )
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(DataProperty(:d))",
            "SubClassOf(:A DataSomeValuesFrom(:d DataUnionOf("
            "<http://www.w3.org/2001/XMLSchema#boolean> "
            f"DataComplementOf({restriction}))))",
        ),
        options=OPTIONS,
    )
    compiled = _compiled(snapshot)
    _manifest(snapshot, reference=compiled)
    encoded = _direct_lifecycle_session(snapshot)
    scalar = native.create_session(
        encode_ontology(compiled),
        encode_config(ReasonerConfig()),
        native.CancellationHandle(),
    )
    try:
        assert _check_signature(encoded.check(None)) == _check_signature(scalar.check(None))
        with pytest.raises(UnsupportedDatatypeError) as encoded_error:
            encoded.classify_classes()
        with pytest.raises(UnsupportedDatatypeError) as scalar_error:
            scalar.classify_classes()
        assert str(encoded_error.value) == str(scalar_error.value)
    finally:
        encoded.close()
        scalar.close()


def test_custom_datatype_definition_graphs_have_program_and_runtime_parity() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Datatype(:alias))",
            "Declaration(Datatype(:bounded))",
            "Declaration(Datatype(:topish))",
            "Declaration(DataProperty(:d))",
            "DatatypeDefinition(:bounded DataUnionOf("
            "DatatypeRestriction(<http://www.w3.org/2001/XMLSchema#integer> "
            "<http://www.w3.org/2001/XMLSchema#minInclusive> "
            '"0"^^<http://www.w3.org/2001/XMLSchema#integer>) '
            'DataOneOf("alpha" '
            '"true"^^<http://www.w3.org/2001/XMLSchema#boolean>) '
            "DataComplementOf(<http://www.w3.org/2001/XMLSchema#dateTime>)))",
            "DatatypeDefinition(:alias :bounded)",
            "DatatypeDefinition(:topish DataUnionOf("
            "<http://www.w3.org/2000/01/rdf-schema#Literal> "
            "<http://www.w3.org/2001/XMLSchema#string>))",
            "DataPropertyRange(:d :alias)",
        ),
        options=OPTIONS,
    )
    compiled = _compiled(snapshot)
    manifest = _manifest(snapshot, reference=compiled)
    datatype_model = cast(
        dict[str, object],
        cast(dict[str, object], manifest["program"])["datatype_model"],
    )
    assert len(cast(list[object], datatype_model["datatype_definitions"])) == 3
    semantic_model = cast(
        dict[str, object],
        json.loads(cast(str, datatype_model["semantic_payload_json"])),
    )
    definitions = cast(
        list[dict[str, object]],
        semantic_model["definitions"],
    )
    assert [definition["datatype_iri"] for definition in definitions] == [
        "urn:test:permanent#alias",
        "urn:test:permanent#bounded",
        "urn:test:permanent#topish",
    ]
    assert {
        cast(dict[str, object], definition["data_range"])["kind"]
        for definition in definitions
    } == {"datatype", "union"}

    encoded = _direct_lifecycle_session(snapshot)
    scalar = native.create_session(
        encode_ontology(compiled),
        encode_config(ReasonerConfig()),
        native.CancellationHandle(),
    )
    try:
        assert _check_signature(encoded.check(None)) == _check_signature(scalar.check(None))
        assert encoded.classify_data_properties() == scalar.classify_data_properties()
    finally:
        encoded.close()
        scalar.close()


def test_opaque_literal_semantics_have_exact_program_and_runtime_parity() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Datatype(:opaque))",
            "Declaration(DataProperty(:d))",
            "Declaration(NamedIndividual(:i))",
            "DataPropertyRange(:d :opaque)",
            'DataPropertyAssertion(:d :i "unparsed source"^^:opaque)',
        ),
        options=OPTIONS,
    )
    config = ReasonerConfig(
        unsupported_datatypes=UnsupportedDatatypePolicy.IGNORE_WITH_WARNING,
    )
    compiled = _compiled(snapshot, config=config)
    manifest = _manifest(snapshot, reference=compiled)
    datatype_model = cast(
        dict[str, object],
        cast(dict[str, object], manifest["program"])["datatype_model"],
    )
    identities = cast(list[dict[str, object]], datatype_model["literal_identities"])
    assert len(identities) == 1
    semantic = cast(
        dict[str, object],
        json.loads(cast(str, identities[0]["semantic_payload_json"])),
    )
    assert semantic["record"] == "opaque_literal_semantic"
    assert semantic["opaque_identity"] == [
        "opaque-source-literal-v1",
        "unparsed source",
        "urn:test:permanent#opaque",
        None,
    ]
    assert cast(list[int], datatype_model["unknown_datatype_ids"])

    encoded = _direct_session(snapshot, reference=compiled, config=config)
    scalar = native.create_session(
        encode_ontology(compiled),
        encode_config(config),
        native.CancellationHandle(),
    )

    def outcome(session: Any) -> tuple[str, object]:
        try:
            return ("result", _check_signature(session.check(None)))
        except UnsupportedDatatypeError as error:
            return ("unsupported", str(error))

    try:
        assert outcome(encoded) == outcome(scalar)
    finally:
        encoded.close()
        scalar.close()


def test_composite_custom_datatype_definitions_are_canonical_across_slice_order() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(Datatype(:bounded))",
            "Declaration(DataProperty(:d))",
            "DatatypeDefinition(:bounded DataUnionOf("
            "<http://www.w3.org/2001/XMLSchema#int> "
            "<http://www.w3.org/2001/XMLSchema#string>))",
            "DataPropertyRange(:d :bounded)",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(Datatype(:alias))",
            "Declaration(Datatype(:bounded))",
            "Declaration(DataProperty(:e))",
            "DatatypeDefinition(:alias :bounded)",
            "DataPropertyRange(:e :alias)",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))
    records = _composite_records(composite, (left, right))
    reference = _compiled(composite)

    canonical = _manifest(composite, records=records, reference=reference)
    reversed_order = _manifest(
        composite,
        records=tuple(reversed(records)),
        reference=reference,
    )

    assert reversed_order == canonical
    datatype_model = cast(
        dict[str, object],
        cast(dict[str, object], canonical["program"])["datatype_model"],
    )
    definitions = cast(
        list[dict[str, object]],
        cast(
            dict[str, object],
            json.loads(cast(str, datatype_model["semantic_payload_json"])),
        )["definitions"],
    )
    assert [definition["datatype_iri"] for definition in definitions] == [
        "urn:test:permanent#alias",
        "urn:test:permanent#bounded",
    ]


def test_ieee_literal_semantics_preserve_identity_ordering_and_runtime_parity() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "Declaration(NamedIndividual(:i))",
            "DataPropertyAssertion(:p :i "
            '"-0"^^<http://www.w3.org/2001/XMLSchema#float>)',
            "DataPropertyAssertion(:p :i "
            '"+0"^^<http://www.w3.org/2001/XMLSchema#float>)',
            "DataPropertyAssertion(:p :i "
            '"NaN"^^<http://www.w3.org/2001/XMLSchema#float>)',
            "DataPropertyAssertion(:p :i "
            '"INF"^^<http://www.w3.org/2001/XMLSchema#float>)',
            "DataPropertyAssertion(:p :i "
            '"-INF"^^<http://www.w3.org/2001/XMLSchema#double>)',
            "DataPropertyAssertion(:p :i "
            '"1.401298464324817e-45"^^<http://www.w3.org/2001/XMLSchema#float>)',
        ),
        options=OPTIONS,
    )
    compiled = _compiled(snapshot)
    manifest = _manifest(snapshot, reference=compiled)
    datatype_model = cast(dict[str, object], manifest["program"])["datatype_model"]
    identities = cast(
        list[dict[str, object]],
        cast(dict[str, object], datatype_model)["literal_identities"],
    )
    payloads = {
        cast(str, payload["lexical_form"]): (identity, payload)
        for identity in identities
        for payload in (
            cast(
                dict[str, object],
                json.loads(cast(str, identity["semantic_payload_json"])),
            ),
        )
    }
    negative_zero, negative_zero_payload = payloads["-0"]
    positive_zero, positive_zero_payload = payloads["+0"]
    assert negative_zero["data_identity_id"] != positive_zero["data_identity_id"]
    assert negative_zero["comparison_key"] == positive_zero["comparison_key"]
    assert negative_zero_payload["comparison"] == positive_zero_payload["comparison"]
    assert cast(dict[str, object], payloads["NaN"][1])["comparison"] == [
        "ieee-comparison-v1",
        "float32",
        "nan",
        "+0",
        "+1",
    ]

    encoded = _direct_lifecycle_session(snapshot)
    scalar = native.create_session(
        encode_ontology(compiled),
        encode_config(ReasonerConfig()),
        native.CancellationHandle(),
    )
    try:
        assert _check_signature(encoded.check(None)) == _check_signature(scalar.check(None))
        assert encoded.realize() == scalar.realize()
    finally:
        encoded.close()
        scalar.close()


def test_remaining_nonnumeric_literal_families_have_program_and_runtime_parity() -> None:
    assertions = (
        'DataPropertyAssertion(:p :i "  alpha   beta  "^^'
        "<http://www.w3.org/2001/XMLSchema#token>)",
        'DataPropertyAssertion(:p :i "alpha beta"^^'
        "<http://www.w3.org/2001/XMLSchema#string>)",
        'DataPropertyAssertion(:p :i "alpha beta"^^'
        "<http://www.w3.org/2001/XMLSchema#normalizedString>)",
        'DataPropertyAssertion(:p :i "en-US"^^'
        "<http://www.w3.org/2001/XMLSchema#language>)",
        'DataPropertyAssertion(:p :i "a:b"^^'
        "<http://www.w3.org/2001/XMLSchema#Name>)",
        'DataPropertyAssertion(:p :i "alpha"^^'
        "<http://www.w3.org/2001/XMLSchema#NCName>)",
        'DataPropertyAssertion(:p :i "a:b"^^'
        "<http://www.w3.org/2001/XMLSchema#NMTOKEN>)",
        'DataPropertyAssertion(:p :i "colour"@en-GB)',
        'DataPropertyAssertion(:p :i "0aFF"^^'
        "<http://www.w3.org/2001/XMLSchema#hexBinary>)",
        'DataPropertyAssertion(:p :i " C v 8 = "^^'
        "<http://www.w3.org/2001/XMLSchema#base64Binary>)",
        'DataPropertyAssertion(:p :i "../café?q=one two"^^'
        "<http://www.w3.org/2001/XMLSchema#anyURI>)",
        'DataPropertyAssertion(:p :i "<a y=\\"2\\" x=\\"1\\"/>"^^'
        "<http://www.w3.org/1999/02/22-rdf-syntax-ns#XMLLiteral>)",
        'DataPropertyAssertion(:p :i "2000-01-01T01:00:00+01:00"^^'
        "<http://www.w3.org/2001/XMLSchema#dateTime>)",
        'DataPropertyAssertion(:p :i "2000-01-01T01:00:00+01:00"^^'
        "<http://www.w3.org/2001/XMLSchema#dateTimeStamp>)",
    )
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "Declaration(NamedIndividual(:i))",
            *assertions,
        ),
        options=OPTIONS,
    )
    compiled = _compiled(snapshot)
    manifest = _manifest(snapshot, reference=compiled)
    datatype_model = cast(dict[str, object], manifest["program"])["datatype_model"]
    identities = cast(
        list[dict[str, object]],
        cast(dict[str, object], datatype_model)["literal_identities"],
    )
    assert len(identities) == len(assertions)
    payloads = [
        cast(
            dict[str, object],
            json.loads(cast(str, identity["semantic_payload_json"])),
        )
        for identity in identities
    ]
    assert {
        cast(list[object], payload["data_identity"])[0] for payload in payloads
    }.issuperset(
        {
            "plain-string-v1",
            "binary-identity-v1",
            "any-uri-v1",
            "xml-literal-c14n-v1",
            "date-time-identity-v1",
        }
    )

    encoded = _direct_lifecycle_session(snapshot)
    scalar = native.create_session(
        encode_ontology(compiled),
        encode_config(ReasonerConfig()),
        native.CancellationHandle(),
    )
    try:
        assert _check_signature(encoded.check(None)) == _check_signature(scalar.check(None))
        assert encoded.realize() == scalar.realize()
    finally:
        encoded.close()
        scalar.close()


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
        assert encoded.compiler_digest == facade_module._canonical_compiler_digest(compiled)
        assert scalar.compiler_digest is None
        assert _check_signature(encoded.check(None)) == _check_signature(scalar.check(None))
        assert encoded.classify_classes() == scalar.classify_classes()
        assert encoded.classify_object_properties() == scalar.classify_object_properties()
    finally:
        encoded.close()
        scalar.close()
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


def test_direct_program_publication_rejects_false_program_digest_then_retries() -> None:
    snapshot = _direct_snapshot()
    compiled = _compiled(snapshot)
    metadata = bytearray(encode_ontology_metadata(compiled))
    program_digest_offset = 32 * 4
    metadata[program_digest_offset] ^= 0xFF

    with pytest.raises(BackendMismatchError) as rejected:
        native._create_encoded_session_v1(
            slices=(_slice_record(snapshot),),
            metadata=bytes(metadata),
            config=encode_config(ReasonerConfig()),
            cancellation=native.CancellationHandle(),
        )

    assert rejected.value.code == "NATIVE_ENCODED_PARITY_MISMATCH"
    assert rejected.value.context == {"section": "program_sha256"}

    retry = _direct_session(snapshot, reference=compiled)
    try:
        assert (
            retry.permanent_program_sha256
            == hashlib.sha256(
                native_input._program_from_ontology(compiled).canonical_bytes()
            ).hexdigest()
        )
        assert retry.compiler_digest == facade_module._canonical_compiler_digest(compiled)
    finally:
        retry.close()


def test_no_reference_lifecycle_matches_scalar_consistency_and_classification() -> None:
    snapshot = _direct_snapshot()

    encoded = _direct_lifecycle_session(snapshot)
    try:
        encoded_digest = encoded.permanent_program_sha256
        encoded_check = _check_signature(encoded.check(None))
        encoded_classes = encoded.classify_classes()
        encoded_objects = encoded.classify_object_properties()
        encoded_data = encoded.classify_data_properties()
        encoded_realization = encoded.realize()

        # Construct the scalar reference only after the direct session has already
        # saturated and answered every coarse operation above.
        compiled = _compiled(snapshot)
        scalar = native.create_session(
            encode_ontology(compiled),
            encode_config(ReasonerConfig()),
            native.CancellationHandle(),
        )
        try:
            assert encoded.ontology_fingerprint == scalar.ontology_fingerprint
            assert encoded_check == _check_signature(scalar.check(None))
            assert encoded_classes == scalar.classify_classes()
            assert encoded_objects == scalar.classify_object_properties()
            assert encoded_data == scalar.classify_data_properties()
            assert encoded_realization == scalar.realize()
            assert encoded_digest == scalar.permanent_program_sha256
            assert encoded.compiler_digest == facade_module._canonical_compiler_digest(compiled)
            assert len(encoded_digest) == 64
            assert encoded_digest != "0" * 64
        finally:
            scalar.close()
    finally:
        encoded.close()

    with pytest.raises(DisposedReasonerError):
        encoded.check(None)
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


def test_direct_lifecycle_discards_nested_data_boolean_beside_absorber() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:d))",
            "Declaration(DataProperty(:e))",
            "Declaration(Datatype(:T))",
            "DataPropertyRange(:d DataUnionOf(rdfs:Literal "
            "DataIntersectionOf(xsd:string xsd:integer)))",
            "DataPropertyRange(:e DataIntersectionOf("
            "DataComplementOf(rdfs:Literal) "
            "DataUnionOf(xsd:boolean xsd:decimal)))",
            "DatatypeDefinition(:T DataComplementOf(DataIntersectionOf("
            "DataComplementOf(rdfs:Literal) "
            "DataUnionOf(xsd:boolean xsd:decimal))))",
        ),
        options=OPTIONS,
    )

    encoded = _direct_lifecycle_session(snapshot)
    compiled = _compiled(snapshot)
    scalar = native.create_session(
        encode_ontology(compiled),
        encode_config(ReasonerConfig()),
        native.CancellationHandle(),
    )
    try:
        assert encoded.permanent_program_sha256 == scalar.permanent_program_sha256
        assert encoded.compiler_digest == facade_module._canonical_compiler_digest(compiled)
        assert _check_signature(encoded.check(None)) == _check_signature(scalar.check(None))
        assert encoded.classify_data_properties() == scalar.classify_data_properties()
    finally:
        encoded.close()
        scalar.close()
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


def test_direct_lifecycle_profile_gate_rejects_before_publication_and_allows_retry() -> None:
    invalid = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(DataProperty(:p))",
            "Declaration(DataProperty(:q))",
            "SubClassOf(:A DataSomeValuesFrom(:p :q xsd:string))",
        ),
        options=OPTIONS,
    )
    config = ReasonerConfig()
    captured = capture_compatible_view(invalid)

    with pytest.raises(OntologyProfileError) as rejected:
        native._create_encoded_session_v1(
            slices=(_slice_record(invalid),),
            metadata=encode_encoded_session_metadata(captured, config),
            config=encode_config(config),
            cancellation=native.CancellationHandle(),
        )

    assert rejected.value.code == "OWL2DL_PROFILE_VIOLATION"
    assert rejected.value.context == {
        "issue_count": 1,
        "rule_ids": "OWL2_DATA_RANGE_ARITY",
    }

    retry = _direct_lifecycle_session(_direct_snapshot())
    try:
        assert retry.check(None)
    finally:
        retry.close()
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


@pytest.mark.parametrize(
    "body",
    [
        (
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(ObjectProperty(:p))",
            "SubClassOf(:A ObjectMinCardinality(4294967296 :p :B))",
        ),
        (
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(ObjectProperty(:p))",
            "EquivalentClasses(:A ObjectIntersectionOf(:B ObjectMinCardinality(4294967296 :p :B)))",
        ),
        (
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:U))",
            "Declaration(ObjectProperty(:p))",
            "DisjointUnion(:U ObjectIntersectionOf(:A :B) ObjectMinCardinality(4294967296 :p :B))",
        ),
        (
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "ObjectPropertyRange(ObjectInverseOf(:p) ObjectIntersectionOf("
            "ObjectSomeValuesFrom(:q :A) "
            "ObjectMinCardinality(4294967296 :q :B)))",
        ),
        (
            "Declaration(Class(:A))",
            "Declaration(ObjectProperty(:q))",
            "Declaration(DataProperty(:p))",
            "DataPropertyDomain(:p ObjectMinCardinality(4294967296 :q :A))",
        ),
        (
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "Declaration(DataProperty(:d))",
            "HasKey(ObjectIntersectionOf(:A ObjectMinCardinality(4294967296 :q :B)) (:p) (:d))",
        ),
        (
            "Declaration(Class(:A))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(NamedIndividual(:i))",
            "ClassAssertion(ObjectMinCardinality(4294967296 :p :A) :i)",
        ),
    ],
    ids=[
        "subclass",
        "equivalent-classes",
        "disjoint-union",
        "object-property-range",
        "data-property-domain",
        "has-key",
        "class-assertion",
    ],
)
def test_direct_lifecycle_matches_scalar_u32_limit_for_every_cardinality_root(
    body: tuple[str, ...],
) -> None:
    snapshot = pyowl_core.load_snapshot(functional(*body), options=OPTIONS)

    with pytest.raises(ResourceLimitError) as scalar:
        _compiled(snapshot)
    with pytest.raises(ResourceLimitError) as encoded:
        _direct_lifecycle_session(snapshot)

    assert encoded.value.as_dict() == scalar.value.as_dict()
    assert encoded.value.context == {
        "allowed": 4_294_967_295,
        "limit": "u32",
        "observed": 4_294_967_296,
    }


@pytest.mark.parametrize(
    ("constructor", "property", "filler", "side", "observed"),
    [
        pytest.param(
            "ObjectMinCardinality", ":p", ":B", side, 4_294_967_296, id=f"object-min-{side}"
        )
        for side in ("antecedent", "consequent")
    ]
    + [
        pytest.param(
            "ObjectMaxCardinality",
            ":p",
            ":B",
            "antecedent",
            4_294_967_297,
            id="object-max-antecedent",
        ),
        pytest.param(
            "ObjectMaxCardinality",
            ":p",
            ":B",
            "consequent",
            4_294_967_296,
            id="object-max-consequent",
        ),
    ]
    + [
        pytest.param(
            "ObjectExactCardinality",
            ":p",
            ":B",
            side,
            4_294_967_296,
            id=f"object-exact-{side}",
        )
        for side in ("antecedent", "consequent")
    ]
    + [
        pytest.param(
            "DataMinCardinality",
            ":d",
            "xsd:string",
            side,
            4_294_967_296,
            id=f"data-min-{side}",
        )
        for side in ("antecedent", "consequent")
    ]
    + [
        pytest.param(
            "DataMaxCardinality",
            ":d",
            "xsd:string",
            side,
            4_294_967_297,
            id=f"data-max-{side}",
        )
        for side in ("antecedent", "consequent")
    ]
    + [
        pytest.param(
            "DataExactCardinality",
            ":d",
            "xsd:string",
            side,
            4_294_967_296,
            id=f"data-exact-{side}",
        )
        for side in ("antecedent", "consequent")
    ],
)
def test_direct_lifecycle_matches_scalar_constructor_cardinality_transform(
    constructor: str,
    property: str,
    filler: str,
    side: str,
    observed: int,
) -> None:
    restriction = f"{constructor}(4294967296 {property} {filler})"
    statement = (
        f"SubClassOf({restriction} :A)"
        if side == "antecedent"
        else f"SubClassOf(:A {restriction})"
    )
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(DataProperty(:d))",
            statement,
        ),
        options=OPTIONS,
    )

    with pytest.raises(ResourceLimitError) as scalar:
        _compiled(snapshot)
    with pytest.raises(ResourceLimitError) as encoded:
        _direct_lifecycle_session(snapshot)

    assert scalar.value.context["observed"] == observed
    assert encoded.value.as_dict() == scalar.value.as_dict()


@pytest.mark.parametrize(
    ("constructor", "property", "filler", "side", "observed"),
    [
        pytest.param(
            "ObjectMinCardinality",
            ":p",
            ":B",
            "antecedent",
            10_000_000_000,
            id="object-min-negated-antecedent",
        ),
        pytest.param(
            "ObjectMinCardinality",
            ":p",
            ":B",
            "consequent",
            9_999_999_999,
            id="object-min-negated-consequent",
        ),
        *[
            pytest.param(
                "ObjectMaxCardinality",
                ":p",
                ":B",
                side,
                10_000_000_001,
                id=f"object-max-negated-{side}",
            )
            for side in ("antecedent", "consequent")
        ],
        pytest.param(
            "ObjectExactCardinality",
            ":p",
            ":B",
            "antecedent",
            10_000_000_000,
            id="object-exact-negated-antecedent",
        ),
        pytest.param(
            "ObjectExactCardinality",
            ":p",
            ":B",
            "consequent",
            9_999_999_999,
            id="object-exact-negated-consequent",
        ),
        *[
            pytest.param(
                "DataMinCardinality",
                ":d",
                "xsd:string",
                side,
                10_000_000_000,
                id=f"data-min-negated-{side}",
            )
            for side in ("antecedent", "consequent")
        ],
        *[
            pytest.param(
                "DataMaxCardinality",
                ":d",
                "xsd:string",
                side,
                10_000_000_001,
                id=f"data-max-negated-{side}",
            )
            for side in ("antecedent", "consequent")
        ],
        *[
            pytest.param(
                "DataExactCardinality",
                ":d",
                "xsd:string",
                side,
                10_000_000_000,
                id=f"data-exact-negated-{side}",
            )
            for side in ("antecedent", "consequent")
        ],
    ],
)
def test_direct_lifecycle_matches_scalar_negated_cardinality_transform(
    constructor: str,
    property: str,
    filler: str,
    side: str,
    observed: int,
) -> None:
    restriction = (
        f"ObjectComplementOf({constructor}(10000000000 {property} {filler}))"
    )
    statement = (
        f"SubClassOf({restriction} :A)"
        if side == "antecedent"
        else f"SubClassOf(:A {restriction})"
    )
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(DataProperty(:d))",
            statement,
        ),
        options=OPTIONS,
    )

    with pytest.raises(ResourceLimitError) as scalar:
        _compiled(snapshot)
    with pytest.raises(ResourceLimitError) as encoded:
        _direct_lifecycle_session(snapshot)

    assert scalar.value.context["observed"] == observed
    assert encoded.value.as_dict() == scalar.value.as_dict()


@pytest.mark.parametrize(
    ("constructor", "side"),
    [
        pytest.param(constructor, side, id=f"{kind}-{side}")
        for kind, constructor in (
            ("object-min", "ObjectMinCardinality"),
            ("object-exact", "ObjectExactCardinality"),
        )
        for side in ("antecedent", "consequent")
    ],
)
def test_negated_object_decrement_at_u32_successor_keeps_overflowing_target(
    constructor: str,
    side: str,
) -> None:
    restriction = (
        f"ObjectComplementOf({constructor}(4294967296 :p :B))"
    )
    statement = (
        f"SubClassOf({restriction} :A)"
        if side == "antecedent"
        else f"SubClassOf(:A {restriction})"
    )
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(ObjectProperty(:p))",
            statement,
        ),
        options=OPTIONS,
    )

    with pytest.raises(ResourceLimitError) as scalar:
        _compiled(snapshot)
    with pytest.raises(ResourceLimitError) as encoded:
        _direct_lifecycle_session(snapshot)

    assert scalar.value.context["observed"] == 4_294_967_296
    assert encoded.value.as_dict() == scalar.value.as_dict()


@pytest.mark.parametrize(
    ("constructor", "property", "filler", "side"),
    [
        pytest.param(constructor, property, filler, side, id=f"{domain}-{kind}-{side}")
        for domain, constructor, property, filler in (
            ("object", "ObjectMaxCardinality", ":p", ":B"),
            ("object", "ObjectExactCardinality", ":p", ":B"),
            ("data", "DataMaxCardinality", ":d", "xsd:string"),
            ("data", "DataExactCardinality", ":d", "xsd:string"),
        )
        for kind in (constructor.removeprefix("Object").removeprefix("Data"),)
        for side in ("antecedent", "consequent")
    ],
)
def test_direct_lifecycle_matches_scalar_u32_boundary_successor(
    constructor: str,
    property: str,
    filler: str,
    side: str,
) -> None:
    restriction = f"{constructor}(4294967295 {property} {filler})"
    statement = (
        f"SubClassOf({restriction} :A)"
        if side == "antecedent"
        else f"SubClassOf(:A {restriction})"
    )
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(DataProperty(:d))",
            statement,
        ),
        options=OPTIONS,
    )

    with pytest.raises(ResourceLimitError) as scalar:
        _compiled(snapshot)
    with pytest.raises(ResourceLimitError) as encoded:
        _direct_lifecycle_session(snapshot)

    assert scalar.value.context["observed"] == 4_294_967_296
    assert encoded.value.as_dict() == scalar.value.as_dict()


@pytest.mark.parametrize(
    "restriction",
    [
        "ObjectMinCardinality(4294967296 :p owl:Nothing)",
        "ObjectMaxCardinality(4294967296 :p owl:Nothing)",
        "ObjectExactCardinality(4294967296 :p owl:Nothing)",
        "DataMinCardinality(4294967296 owl:bottomDataProperty xsd:string)",
        "DataMaxCardinality(4294967296 owl:bottomDataProperty xsd:string)",
        "DataExactCardinality(4294967296 owl:bottomDataProperty xsd:string)",
    ],
)
def test_reducible_oversized_cardinality_does_not_raise_resource_limit(
    restriction: str,
) -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(ObjectProperty(:p))",
            f"SubClassOf(:A {restriction})",
        ),
        options=OPTIONS,
    )

    _compiled(snapshot)
    session = _direct_lifecycle_session(snapshot)
    session.close()


def test_direct_lifecycle_preserves_arbitrary_precision_cardinality_error_context() -> None:
    observed = 1_208_925_819_614_629_174_706_299
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(ObjectProperty(:p))",
            f"SubClassOf(:A ObjectMinCardinality({observed} :p :B))",
        ),
        options=OPTIONS,
    )

    with pytest.raises(ResourceLimitError) as scalar:
        _compiled(snapshot)
    with pytest.raises(ResourceLimitError) as encoded:
        _direct_lifecycle_session(snapshot)

    assert encoded.value.as_dict() == scalar.value.as_dict()
    assert encoded.value.context["observed"] == observed


@pytest.mark.parametrize(
    "restrictions",
    [
        (
            "SubClassOf(:A ObjectMinCardinality(4294967296 :p :C))",
            "SubClassOf(:B ObjectMinCardinality(10000000000 :p :C))",
        ),
        (
            "SubClassOf(:A ObjectMinCardinality(4294967296 :p :C))",
            "SubClassOf(:B DataMinCardinality(10000000000 :d xsd:string))",
        ),
        (
            "SubClassOf(:A DataMinCardinality(4294967296 :d xsd:string))",
            "SubClassOf(:B DataMinCardinality(10000000000 :e xsd:integer))",
        ),
    ],
    ids=["object-fillers", "object-data", "data-roles-fillers"],
)
def test_direct_lifecycle_selects_resource_safe_minimum_cardinality_error(
    restrictions: tuple[str, str],
) -> None:
    numeric_minimum = 4_294_967_296
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:C))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(DataProperty(:d))",
            "Declaration(DataProperty(:e))",
            *restrictions,
        ),
        options=OPTIONS,
    )

    with pytest.raises(ResourceLimitError) as scalar:
        _compiled(snapshot)
    with pytest.raises(ResourceLimitError) as encoded:
        _direct_lifecycle_session(snapshot)

    assert scalar.value.context["observed"] == numeric_minimum
    assert encoded.value.as_dict() == scalar.value.as_dict()
    assert encoded.value.context == {
        "allowed": 4_294_967_295,
        "limit": "u32",
        "observed": numeric_minimum,
    }


@pytest.mark.parametrize(
    "body",
    [
        (
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "SubObjectPropertyOf(:p :q)",
        ),
        (
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "Declaration(ObjectProperty(:r))",
            "SubObjectPropertyOf(ObjectPropertyChain(:p :q) :r)",
        ),
        (
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "EquivalentObjectProperties(:p :q)",
        ),
        (
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "DisjointObjectProperties(:p :q)",
        ),
        (
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "InverseObjectProperties(:p :q)",
        ),
        (
            "Declaration(ObjectProperty(:p))",
            "IrreflexiveObjectProperty(:p)",
        ),
        (
            "Declaration(ObjectProperty(:p))",
            "SymmetricObjectProperty(:p)",
        ),
        (
            "Declaration(ObjectProperty(:p))",
            "AsymmetricObjectProperty(:p)",
        ),
        (
            "Declaration(ObjectProperty(:p))",
            "TransitiveObjectProperty(:p)",
        ),
        (
            "Declaration(DataProperty(:p))",
            "Declaration(DataProperty(:q))",
            "SubDataPropertyOf(:p :q)",
        ),
        (
            "Declaration(DataProperty(:p))",
            "Declaration(DataProperty(:q))",
            "EquivalentDataProperties(:p :q)",
        ),
        (
            "Declaration(DataProperty(:p))",
            "Declaration(DataProperty(:q))",
            "DisjointDataProperties(:p :q)",
        ),
    ],
    ids=[
        "simple-object-inclusion",
        "complex-object-inclusion",
        "equivalent-object-properties",
        "disjoint-object-properties",
        "inverse-object-properties",
        "irreflexive-object-property",
        "symmetric-object-property",
        "asymmetric-object-property",
        "transitive-object-property",
        "sub-data-property",
        "equivalent-data-properties",
        "disjoint-data-properties",
    ],
)
def test_direct_publication_accepts_every_delegated_role_root(
    body: tuple[str, ...],
) -> None:
    snapshot = pyowl_core.load_snapshot(functional(*body), options=OPTIONS)

    session = _direct_session(snapshot)
    try:
        assert session.permanent_program_sha256 != "0" * 64
    finally:
        session.close()


def test_encoded_service_context_is_compact_strict_cancel_safe_and_close_safe() -> None:
    snapshot = _direct_snapshot()
    cancellation = native.CancellationHandle()
    session = _direct_lifecycle_session(snapshot, cancellation=cancellation)
    encoded = session._encoded_service_context_v1()
    payload = cast(dict[str, object], json.loads(encoded))

    assert set(payload) == {
        "compiler_digest",
        "deterministic_program",
        "domains",
        "permanent_program_sha256",
        "schema_version",
        "semantic_equality_possible",
    }
    assert not {
        "clauses",
        "compiled_ontology",
        "normalized",
        "predicates",
        "provenance",
    }.intersection(payload)
    context = decode_service_context(
        encoded,
        query_scope_digest=session.ontology_fingerprint,
        signature=snapshot.signature(),
    )
    assert context.compiler_digest == session.compiler_digest
    assert context.permanent_program_sha256 == session.permanent_program_sha256
    assert context.source_signature.issuperset(snapshot.signature())

    cancellation.interrupt("cancel encoded service context")
    with pytest.raises(ReasonerInterruptedError):
        session._encoded_service_context_v1()
    cancellation.reset()
    assert session._encoded_service_context_v1() == encoded

    hostile = dict(payload)
    hostile["schema_version"] = 3
    with pytest.raises(BackendMismatchError):
        decode_service_context(
            json.dumps(hostile, separators=(",", ":")).encode(),
            query_scope_digest=session.ontology_fingerprint,
            signature=snapshot.signature(),
        )

    session.close()
    with pytest.raises(DisposedReasonerError):
        session._encoded_service_context_v1()


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
            cancel_at_checkpoint=74,
        )
    assert captured.value.context["phase"] == "permanent-program-clause"

    retry = _direct_session(snapshot, records=records, reference=reference)
    try:
        assert retry.ontology_fingerprint == reference.ontology_fingerprint
        assert retry.check(None)
    finally:
        retry.close()


def test_no_reference_lifecycle_limit_interrupt_close_and_retry_are_transactional() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "SubClassOf(:A :B)",
        ),
        options=OPTIONS,
    )
    records = (_slice_record(snapshot),)

    with pytest.raises(ResourceLimitError):
        _direct_lifecycle_session(
            snapshot,
            records=records,
            max_owned_bytes=1,
        )
    with pytest.raises(ReasonerInterruptedError) as captured:
        _direct_lifecycle_session(
            snapshot,
            records=records,
            cancel_at_checkpoint=81,
        )
    assert captured.value.context["phase"] == "permanent-program-digest"

    interrupted = native.CancellationHandle()
    interrupted.interrupt("cancel before encoded lifecycle construction")
    with pytest.raises(ReasonerInterruptedError):
        _direct_lifecycle_session(
            snapshot,
            records=records,
            cancellation=interrupted,
        )

    first = _direct_lifecycle_session(snapshot, records=records)
    first_digest = first.permanent_program_sha256
    first.close()
    with pytest.raises(DisposedReasonerError):
        first.check(None)

    retry = _direct_lifecycle_session(snapshot, records=records)
    try:
        assert retry.permanent_program_sha256 == first_digest
        assert _check_signature(retry.check(None))[0]
    finally:
        retry.close()


def test_direct_publication_rejects_profile_extensions_before_assembly() -> None:
    snapshot = _extension_snapshot()
    reference = _compiled(_direct_snapshot())

    with pytest.raises(OntologyProfileError) as rejected:
        _direct_session(snapshot, reference=reference)

    assert rejected.value.context == {
        "issue_count": 1,
        "rule_ids": "OWL2DL_EXTENSION_COMPONENT",
    }


def test_advertised_lifecycle_adapter_uses_no_reference_program_or_scalar_wire(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    snapshot = _direct_snapshot()
    config = ReasonerConfig()
    captured = capture_ontology(snapshot, config=config).captured
    direct_calls = 0

    extension = ModuleType("encoded_session_test_extension")
    extension.__version__ = native.__version__
    extension.ABI_VERSION = native.ABI_VERSION
    extension.IR_SCHEMA_VERSION = native.IR_SCHEMA_VERSION
    _advertise_encoded_compiler(extension)
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

    def forbidden_reference_metadata(_ontology: CompiledOntology) -> bytes:
        raise AssertionError("Python reference-program metadata was encoded")

    monkeypatch.setattr(native_input, "encode_ontology", forbidden_ontology_wire)
    monkeypatch.setattr(
        native_input,
        "encode_ontology_metadata",
        forbidden_reference_metadata,
    )
    monkeypatch.setattr(
        native_backend,
        "negotiate_encoded_input",
        lambda view, *_args, **_kwargs: _encoded_negotiation(view),
    )
    factory = NativeBackendFactory(extension)
    session = factory._create_encoded_lifecycle_handoff(
        captured,
        config,
        CancellationToken(),
    )
    assert session is not None
    try:
        assert direct_calls == 1
        assert session.ontology_fingerprint
        assert session.permanent_program_sha256 != "0" * 64
        assert session.check(None).satisfiable
        counters = session.ingestion_counters
        assert counters["encoded_buffer_count"] == len(ENCODED_BUFFER_WIDTHS)
        assert counters["encoded_buffer_bytes"] > 0
        assert counters["encoded_detached_buffer_count"] == counters["encoded_buffer_count"]
        assert counters["encoded_zero_copy_buffers"] == counters["encoded_buffer_count"]
        assert counters["encoded_private_ir_bytes"] == 0
    finally:
        session.close()


def test_advertised_lifecycle_preserves_cardinality_limit_without_fallback(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    unsupported = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(ObjectProperty(:p))",
            "SubClassOf(:A ObjectMinCardinality(4294967296 :p :B))",
        ),
        options=OPTIONS,
    )
    direct_calls = 0
    scalar_calls = 0

    extension = ModuleType("encoded_root_eligibility_test_extension")
    extension.__version__ = native.__version__
    extension.ABI_VERSION = native.ABI_VERSION
    extension.IR_SCHEMA_VERSION = native.IR_SCHEMA_VERSION
    _advertise_encoded_compiler(extension)
    extension.CancellationHandle = native.CancellationHandle
    extension.self_test = native.self_test

    def forbidden_scalar_constructor(*_args: object) -> object:
        nonlocal scalar_calls
        scalar_calls += 1
        raise AssertionError("scalar fallback was called after direct input consumption")

    def direct_constructor(**kwargs: object) -> object:
        nonlocal direct_calls
        direct_calls += 1
        return native._create_encoded_session_v1(**kwargs)

    extension.create_session = forbidden_scalar_constructor
    extension._create_encoded_session_v1 = direct_constructor
    factory = NativeBackendFactory(extension)
    monkeypatch.setattr(
        native_backend,
        "negotiate_encoded_input",
        lambda view, *_args, **_kwargs: _encoded_negotiation(view),
    )
    monkeypatch.setattr(facade_module, "select_backend_factory", lambda _config: factory)

    with pytest.raises(ResourceLimitError) as scalar:
        _compiled(unsupported)
    with pytest.raises(ResourceLimitError) as encoded:
        Reasoner(unsupported)
    assert encoded.value.as_dict() == scalar.value.as_dict()
    assert direct_calls == 1
    assert scalar_calls == 0

    with Reasoner(_direct_snapshot()) as retry:
        assert retry.is_consistent()
        assert retry.diagnostics()["ingestion_path"] == "encoded-native"
    assert direct_calls == 2
    assert scalar_calls == 0


def test_facade_rejects_mismatched_compiler_digest_then_retries(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    snapshot = _direct_snapshot()
    config = ReasonerConfig()
    expected_digest = facade_module._canonical_compiler_digest(_compiled(snapshot))
    corrupt_digest = True
    candidates: list[Any] = []

    class CompilerDigestProxy:
        def __init__(self, raw: object) -> None:
            self._raw = raw

        @property
        def compiler_digest(self) -> str:
            return "0" * 64

        def __getattr__(self, name: str) -> object:
            return getattr(self._raw, name)

    extension = ModuleType("encoded_compiler_digest_mismatch_extension")
    extension.__version__ = native.__version__
    extension.ABI_VERSION = native.ABI_VERSION
    extension.IR_SCHEMA_VERSION = native.IR_SCHEMA_VERSION
    _advertise_encoded_compiler(extension)
    extension.CancellationHandle = native.CancellationHandle
    extension.self_test = native.self_test

    def forbidden_scalar_constructor(*_args: object) -> object:
        raise AssertionError("scalar native session constructor was called")

    def direct_constructor(**kwargs: object) -> object:
        raw = native._create_encoded_session_v1(**kwargs)
        candidates.append(raw)
        return CompilerDigestProxy(raw) if corrupt_digest else raw

    extension.create_session = forbidden_scalar_constructor
    extension._create_encoded_session_v1 = direct_constructor
    factory = NativeBackendFactory(extension)
    monkeypatch.setattr(
        native_backend,
        "negotiate_encoded_input",
        lambda view, *_args, **_kwargs: _encoded_negotiation(view),
    )
    monkeypatch.setattr(facade_module, "select_backend_factory", lambda _config: factory)

    with pytest.raises(BackendMismatchError) as rejected:
        Reasoner(snapshot, config=config)
    assert rejected.value.context["reason"] == "compiler_digest_mismatch"
    assert len(candidates) == 1
    assert candidates[0].closed

    corrupt_digest = False
    with Reasoner(snapshot, config=config) as retry:
        assert retry.diagnostics()["compiler_digest"] == expected_digest
        assert retry.is_consistent()
    assert len(candidates) == 2
    assert candidates[1].closed


def test_facade_constructs_encoded_services_without_scalar_service_context(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    snapshot = _direct_snapshot()
    expected_compiler_digest = facade_module._canonical_compiler_digest(_compiled(snapshot))
    events: list[str] = []

    extension = ModuleType("encoded_lifecycle_facade_test_extension")
    extension.__version__ = native.__version__
    extension.ABI_VERSION = native.ABI_VERSION
    extension.IR_SCHEMA_VERSION = native.IR_SCHEMA_VERSION
    _advertise_encoded_compiler(extension)
    extension.CancellationHandle = native.CancellationHandle
    extension.self_test = native.self_test

    def forbidden_scalar_constructor(*_args: object) -> object:
        raise AssertionError("scalar native session constructor was called")

    def direct_constructor(**kwargs: object) -> object:
        events.append("encoded-session")
        return native._create_encoded_session_v1(**kwargs)

    extension.create_session = forbidden_scalar_constructor
    extension._create_encoded_session_v1 = direct_constructor
    factory = NativeBackendFactory(extension)

    monkeypatch.setattr(
        native_backend,
        "negotiate_encoded_input",
        lambda view, *_args, **_kwargs: _encoded_negotiation(view),
    )
    monkeypatch.setattr(facade_module, "select_backend_factory", lambda _config: factory)

    def forbidden_compile(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("scalar service context was compiled")

    def forbidden_ontology_wire(_ontology: CompiledOntology) -> bytes:
        raise AssertionError("proportional ontology wire was encoded")

    def forbidden_reference_metadata(_ontology: CompiledOntology) -> bytes:
        raise AssertionError("Python reference-program metadata was encoded")

    monkeypatch.setattr(facade_module, "compile_captured_bundle", forbidden_compile)
    monkeypatch.setattr(native_input, "encode_ontology", forbidden_ontology_wire)
    monkeypatch.setattr(
        native_input,
        "encode_ontology_metadata",
        forbidden_reference_metadata,
    )

    with Reasoner(snapshot, config=ReasonerConfig()) as reasoner:
        assert events == ["encoded-session"]
        runtime = cast(Any, reasoner)._runtime
        assert runtime.normalized is None
        assert runtime.program is None
        assert runtime.compiled is None
        assert runtime.compiler_digest == runtime.session.compiler_digest
        assert runtime.compiler_digest == expected_compiler_digest
        diagnostics = reasoner.diagnostics()
        assert diagnostics["ingestion_path"] == "encoded-native"
        assert diagnostics["encoded_buffer_count"] > 0
        assert diagnostics["encoded_buffer_bytes"] > 0
        assert (
            diagnostics["encoded_detached_buffer_count"]
            == diagnostics["encoded_buffer_count"]
            == diagnostics["encoded_zero_copy_buffers"]
        )
        assert reasoner.is_consistent()
        hierarchy = reasoner.class_hierarchy()
        assert hierarchy.nodes[hierarchy.top_node]
        assert hierarchy.nodes[hierarchy.bottom_node]
        assert reasoner.object_property_hierarchy().nodes
        assert reasoner.data_property_hierarchy().nodes
        base = "urn:test:permanent#"
        a = owl.Class(owl.IRI(f"{base}A"))
        b = owl.Class(owl.IRI(f"{base}B"))
        c = owl.Class(owl.IRI(f"{base}C"))
        p = owl.ObjectProperty(owl.IRI(f"{base}p"))
        i = owl.NamedIndividual(owl.IRI(f"{base}i"))
        j = owl.NamedIndividual(owl.IRI(f"{base}j"))
        assert reasoner.is_satisfiable(a)
        assert reasoner.is_subclass(a, b)
        assert reasoner.entails(owl.SubClassOf(a, b))
        assert a in set().union(*reasoner.subclasses(b))
        assert b in set().union(*reasoner.types(i))
        assert i in reasoner.instances(b)
        assert j in reasoner.object_property_values(i, p)
        before_update = len(events)
        initial_digest = reasoner.diagnostics()["compiler_digest"]
        addition = owl.SubClassOf(c, a)
        reasoner.add_axioms((addition,))
        reasoner.flush()
        assert len(events) == before_update + 1
        assert c in set().union(*reasoner.subclasses(a))
        updated_digest = reasoner.diagnostics()["compiler_digest"]
        assert updated_digest != initial_digest
        updated_diagnostics = reasoner.diagnostics()
        assert updated_diagnostics["ingestion_path"] == "encoded-native"
        assert updated_diagnostics["encoded_segment_count"] > 0
        assert updated_diagnostics["encoded_referenced_view_count"] > 0
        assert (
            updated_diagnostics["encoded_detached_buffer_count"]
            >= updated_diagnostics["encoded_zero_copy_buffers"]
        )
        fresh = factory._create_encoded_lifecycle_handoff(
            capture_ontology(reasoner.ontology).captured,
            ReasonerConfig(),
            CancellationToken(),
        )
        assert fresh is not None
        try:
            assert fresh.compiler_digest == updated_digest
        finally:
            fresh.close()
        reasoner.remove_axioms((addition,))
        reasoner.flush()
        assert len(events) == before_update + 3
        assert reasoner.diagnostics()["compiler_digest"] == initial_digest

    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


def test_verify_facade_pairs_direct_native_compiler_with_scalar_shadow(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    snapshot = _direct_snapshot()
    config = ReasonerConfig(backend="verify")
    expected_digest = facade_module._canonical_compiler_digest(
        _compiled(snapshot, config=config)
    )
    native_candidates: list[Any] = []
    native_compiles = 0
    scalar_compiles = 0

    extension = ModuleType("encoded_verify_lifecycle_extension")
    extension.__version__ = native.__version__
    extension.ABI_VERSION = native.ABI_VERSION
    extension.IR_SCHEMA_VERSION = native.IR_SCHEMA_VERSION
    _advertise_encoded_compiler(extension)
    extension.CancellationHandle = native.CancellationHandle
    extension.self_test = native.self_test

    def forbidden_scalar_constructor(*_args: object) -> object:
        raise AssertionError("scalar native session constructor was called")

    def direct_constructor(**kwargs: object) -> object:
        nonlocal native_compiles
        native_compiles += 1
        candidate = native._create_encoded_session_v1(**kwargs)
        native_candidates.append(candidate)
        return candidate

    extension.create_session = forbidden_scalar_constructor
    extension._create_encoded_session_v1 = direct_constructor
    factory = VerifyBackendFactory(NativeBackendFactory(extension))
    original_scalar_compile = verify_backend.compile_captured_bundle

    def tracked_scalar_compile(*args: object, **kwargs: object) -> object:
        nonlocal scalar_compiles
        scalar_compiles += 1
        return original_scalar_compile(*args, **kwargs)

    monkeypatch.setattr(verify_backend, "compile_captured_bundle", tracked_scalar_compile)
    monkeypatch.setattr(
        native_backend,
        "negotiate_encoded_input",
        lambda view, *_args, **_kwargs: _encoded_negotiation(view),
    )
    monkeypatch.setattr(facade_module, "select_backend_factory", lambda _config: factory)

    def forbidden_facade_scalar_compile(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("facade scalar-wire bundle was compiled")

    monkeypatch.setattr(
        facade_module,
        "compile_captured_bundle",
        forbidden_facade_scalar_compile,
    )

    with Reasoner(snapshot, config=config) as reasoner:
        runtime = cast(Any, reasoner)._runtime
        assert runtime.normalized is None
        assert runtime.program is None
        assert runtime.compiled is None
        assert runtime.session.compiler_digest == expected_digest
        assert reasoner.diagnostics()["compiler_digest"] == expected_digest
        assert reasoner.diagnostics()["ingestion_path"] == "encoded-native"
        assert reasoner.diagnostics()["encoded_buffer_count"] > 0
        assert reasoner.is_consistent()
        assert reasoner.class_hierarchy().nodes
        base = "urn:test:permanent#"
        class_a = owl.Class(owl.IRI(f"{base}A"))
        class_c = owl.Class(owl.IRI(f"{base}C"))
        addition = owl.SubClassOf(class_c, class_a)
        reasoner.add_axioms((addition,))
        reasoner.flush()
        assert reasoner.is_subclass(class_c, class_a)
        assert reasoner.diagnostics()["compiler_digest"] != expected_digest
        assert reasoner.diagnostics()["ingestion_path"] == "encoded-native"
        reasoner.remove_axioms((addition,))
        reasoner.flush()
        assert reasoner.diagnostics()["compiler_digest"] == expected_digest

    assert native_compiles == 3
    assert scalar_compiles == 3
    assert len(native_candidates) == 3
    assert all(candidate.closed for candidate in native_candidates)
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


def test_encoded_services_match_scalar_object_query_families_without_scalar_callbacks(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    snapshot = _object_query_snapshot()
    with Reasoner(snapshot, config=ReasonerConfig(backend="python")) as reference:
        expected = _object_service_results(reference)

    extension = ModuleType("encoded_query_family_test_extension")
    extension.__version__ = native.__version__
    extension.ABI_VERSION = native.ABI_VERSION
    extension.IR_SCHEMA_VERSION = native.IR_SCHEMA_VERSION
    _advertise_encoded_compiler(extension)
    extension.CancellationHandle = native.CancellationHandle
    extension.self_test = native.self_test

    def forbidden_scalar_constructor(*_args: object) -> object:
        raise AssertionError("scalar native session constructor was called")

    def forbidden_compile(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("scalar service context was compiled")

    def forbidden_ontology_wire(_ontology: CompiledOntology) -> bytes:
        raise AssertionError("proportional ontology wire was encoded")

    def forbidden_reference_metadata(_ontology: CompiledOntology) -> bytes:
        raise AssertionError("Python reference-program metadata was encoded")

    extension.create_session = forbidden_scalar_constructor
    extension._create_encoded_session_v1 = native._create_encoded_session_v1
    factory = NativeBackendFactory(extension)

    monkeypatch.setattr(
        native_backend,
        "negotiate_encoded_input",
        lambda view, *_args, **_kwargs: _encoded_negotiation(view),
    )
    monkeypatch.setattr(facade_module, "select_backend_factory", lambda _config: factory)
    monkeypatch.setattr(
        facade_module,
        "compile_captured_bundle",
        forbidden_compile,
    )
    monkeypatch.setattr(
        native_input,
        "encode_ontology",
        forbidden_ontology_wire,
    )
    monkeypatch.setattr(
        native_input,
        "encode_ontology_metadata",
        forbidden_reference_metadata,
    )

    with Reasoner(snapshot, config=ReasonerConfig()) as candidate:
        assert _object_service_results(candidate) == expected

    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


def test_encoded_services_match_scalar_data_query_families_without_scalar_callbacks(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    snapshot = _data_query_snapshot()
    with Reasoner(snapshot, config=ReasonerConfig(backend="python")) as reference:
        expected = _data_service_results(reference)

    extension = ModuleType("encoded_data_query_family_test_extension")
    extension.__version__ = native.__version__
    extension.ABI_VERSION = native.ABI_VERSION
    extension.IR_SCHEMA_VERSION = native.IR_SCHEMA_VERSION
    _advertise_encoded_compiler(extension)
    extension.CancellationHandle = native.CancellationHandle
    extension.self_test = native.self_test

    def forbidden_scalar_constructor(*_args: object) -> object:
        raise AssertionError("scalar native session constructor was called")

    def forbidden_compile(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("scalar service context was compiled")

    def forbidden_ontology_wire(_ontology: CompiledOntology) -> bytes:
        raise AssertionError("proportional ontology wire was encoded")

    def forbidden_reference_metadata(_ontology: CompiledOntology) -> bytes:
        raise AssertionError("Python reference-program metadata was encoded")

    extension.create_session = forbidden_scalar_constructor
    extension._create_encoded_session_v1 = native._create_encoded_session_v1
    factory = NativeBackendFactory(extension)

    monkeypatch.setattr(
        native_backend,
        "negotiate_encoded_input",
        lambda view, *_args, **_kwargs: _encoded_negotiation(view),
    )
    monkeypatch.setattr(facade_module, "select_backend_factory", lambda _config: factory)
    monkeypatch.setattr(facade_module, "compile_captured_bundle", forbidden_compile)
    monkeypatch.setattr(native_input, "encode_ontology", forbidden_ontology_wire)
    monkeypatch.setattr(
        native_input,
        "encode_ontology_metadata",
        forbidden_reference_metadata,
    )

    with Reasoner(snapshot, config=ReasonerConfig()) as candidate:
        assert _data_service_results(candidate) == expected

    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


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
