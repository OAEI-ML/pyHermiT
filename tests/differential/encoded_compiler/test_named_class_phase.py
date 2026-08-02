"""Exact scalar/encoded differential for named classes and the first ABox phase."""

# SPDX-License-Identifier: LGPL-3.0-or-later

from __future__ import annotations

import json
import random
import struct
from typing import Any, cast

import pyowl_core
import pyowl_core.model as owl
import pytest
from pyowl_core.backends.native_views import produce_encoded_structural_view_v2

import pyhermit._native as native
from pyhermit import ReasonerConfig
from pyhermit.clauses.compiler import compile_captured_bundle
from pyhermit.clauses.model import (
    Atom,
    DataConstant,
    DLClause,
    GroundAtom,
    IndividualTerm,
    PredicateKind,
    SymbolKind,
    SymbolValue,
    TermSort,
    Variable,
)
from pyhermit.datatypes import SUPPORTED_DATATYPES
from pyhermit.encoded_input import ENCODED_NATIVE_FEATURE
from pyhermit.exceptions import BackendMismatchError
from pyhermit.inputs import capture_ontology
from pyhermit.normalize import DataRangeInclusion

OPTIONS = pyowl_core.LoadOptions(
    imports=pyowl_core.ImportPolicy.IGNORE,
    backend=pyowl_core.BackendPreference.PYTHON,
)


def functional(*body: str) -> bytes:
    return (
        "Prefix(:=<urn:test:named#>) "
        "Prefix(owl:=<http://www.w3.org/2002/07/owl#>) "
        "Ontology(<urn:test:named> " + " ".join(body) + ")"
    ).encode()


def _native_manifest(snapshot: pyowl_core.OntologyView) -> dict[str, object]:
    buffers = produce_encoded_structural_view_v2(snapshot).buffers
    encoded = native._encoded_named_class_manifest_v1(
        logical_fingerprint=memoryview(snapshot.logical_fingerprint.digest),
        root_kinds=buffers["root_kinds"],
        root_ids=buffers["root_ids"],
        node_tags=buffers["node_tags"],
        node_field_offsets=buffers["node_field_offsets"],
        field_kinds=buffers["field_kinds"],
        field_values=buffers["field_values"],
        field_lengths=buffers["field_lengths"],
        item_kinds=buffers["item_kinds"],
        item_values=buffers["item_values"],
        item_lengths=buffers["item_lengths"],
        scalar_bytes=buffers["scalar_bytes"],
    )
    return cast(dict[str, object], json.loads(encoded))


def _slice_record(
    snapshot: pyowl_core.OntologyView,
    *,
    posting_mode: int = 0,
    postings: memoryview | None = None,
    member_tokens: tuple[bytes, ...] = (),
    anonymous_scope_maps: tuple[memoryview, ...] = (),
) -> tuple[object, ...]:
    buffers = produce_encoded_structural_view_v2(snapshot).buffers
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


def _native_slices_manifest(
    *records: tuple[object, ...],
    logical_fingerprint: bytes | None = None,
) -> dict[str, object]:
    encoded = native._encoded_named_class_slices_manifest_v1(
        slices=records,
        logical_fingerprint=(
            None if logical_fingerprint is None else memoryview(logical_fingerprint)
        ),
    )
    return cast(dict[str, object], json.loads(encoded))


def _scope_map(replacements: dict[bytes, bytes]) -> memoryview:
    return memoryview(b"".join(source + target for source, target in sorted(replacements.items())))


def _composite_records(
    composite: pyowl_core.OntologyView,
    sources: tuple[pyowl_core.OntologyView, ...],
) -> tuple[tuple[object, ...], ...]:
    return _composite_selected_records(
        composite,
        sources,
        tuple((0, None) for _source in sources),
    )


def _composite_selected_records(
    composite: pyowl_core.OntologyView,
    sources: tuple[pyowl_core.OntologyView, ...],
    selections: tuple[tuple[int, memoryview | None], ...],
) -> tuple[tuple[object, ...], ...]:
    tokens = cast(tuple[bytes, ...], cast(Any, composite)._source_tokens())
    mappings = cast(
        tuple[dict[bytes, bytes], ...],
        cast(Any, composite)._scope_replacements(),
    )
    rows = sorted(
        zip(tokens, sources, mappings, selections, strict=True),
        key=lambda row: row[0],
    )
    return tuple(
        _slice_record(
            source,
            posting_mode=posting_mode,
            postings=postings,
            member_tokens=(token,),
            anonymous_scope_maps=(() if not mapping else (_scope_map(mapping),)),
        )
        for token, source, mapping, (posting_mode, postings) in rows
    )


def _symbol_payload(value: SymbolValue) -> dict[str, object]:
    return {
        "identifier": value.identifier,
        "key_hex": value.key_hex,
        "display": value.display,
        "generated": value.generated,
        "query_local": value.query_local,
    }


def _expected_source_literal_symbols(
    snapshot: pyowl_core.OntologyView,
) -> list[dict[str, object]]:
    _normalized, program, _ontology = compile_captured_bundle(
        capture_ontology(snapshot).captured,
        ReasonerConfig(),
    )
    return [
        _symbol_payload(value) for value in program.symbols.domain(SymbolKind.SOURCE_LITERAL).values
    ]


def _expected_data_value_symbols(
    snapshot: pyowl_core.OntologyView,
) -> list[dict[str, object]]:
    _normalized, program, _ontology = compile_captured_bundle(
        capture_ontology(snapshot).captured,
        ReasonerConfig(),
    )
    return [
        _symbol_payload(value) for value in program.symbols.domain(SymbolKind.DATA_VALUE).values
    ]


def _projected_atom_payload(
    value: Atom,
    predicate_remap: dict[int, int],
) -> dict[str, object]:
    arguments: list[dict[str, object]] = []
    for argument in value.arguments:
        if isinstance(argument, Variable):
            arguments.append({"index": argument.index, "sort": argument.sort.value})
        else:
            assert isinstance(argument, IndividualTerm)
            arguments.append({"individual_id": argument.individual_id})
    return {
        "predicate_id": predicate_remap[value.predicate_id],
        "arguments": arguments,
    }


def _projected_atom_key(
    value: Atom,
    predicate_remap: dict[int, int],
) -> dict[str, object]:
    arguments: list[dict[str, object]] = []
    for argument in value.arguments:
        if isinstance(argument, Variable):
            arguments.append(
                {
                    "type": "Variable",
                    "index": argument.index,
                    "sort": argument.sort.value,
                    "schema_version": 1,
                }
            )
        else:
            assert isinstance(argument, IndividualTerm)
            arguments.append(
                {
                    "type": "IndividualTerm",
                    "individual_id": argument.individual_id,
                    "schema_version": 1,
                }
            )
    return {
        "type": "Atom",
        "predicate_id": predicate_remap[value.predicate_id],
        "arguments": arguments,
        "schema_version": 1,
    }


def _projected_rule_key(
    clause: DLClause,
    predicate_remap: dict[int, int],
) -> bytes:
    payload = {
        "body": [_projected_atom_key(value, predicate_remap) for value in clause.body],
        "head": [_projected_atom_key(value, predicate_remap) for value in clause.head],
    }
    return json.dumps(payload, separators=(",", ":"), sort_keys=True).encode()


def _ground_atom_payload(
    value: GroundAtom,
    predicate_remap: dict[int, int],
) -> dict[str, object]:
    arguments = []
    for argument in value.arguments:
        if isinstance(argument, IndividualTerm):
            arguments.append({"individual_id": argument.individual_id})
        else:
            assert isinstance(argument, DataConstant)
            arguments.append(
                {
                    "source_literal_id": argument.source_literal_id,
                    "data_identity_id": argument.data_identity_id,
                }
            )
    return {
        "predicate_id": predicate_remap[value.predicate_id],
        "arguments": arguments,
        "provenance_ids": list(value.provenance_ids),
    }


def _expected_manifest(
    snapshot: pyowl_core.OntologyView,
    *,
    compiled_roots: int,
    include_object_constraints: bool = False,
    include_object_characteristics: bool = False,
    include_generated_object_self_definitions: bool = False,
    include_generated_object_quantifier_definitions: bool = False,
    include_generated_object_cardinality_definitions: bool = False,
    include_at_least_object_predicates: bool = False,
    include_generated_data_quantifier_definitions: bool = False,
    include_generated_data_cardinality_definitions: bool = False,
    include_at_least_data_predicates: bool = False,
    include_annotated_equality_predicates: bool = False,
    include_data_domains: bool = False,
    include_data_ranges: bool = False,
    include_generated_data_definitions: bool = False,
    include_datatype_definitions: bool = False,
    include_keys: bool = False,
    include_data_functionalities: bool = False,
    include_object_assertions: bool = False,
    include_negative_object_assertions: bool = False,
    include_data_assertions: bool = False,
    include_negative_data_assertions: bool = False,
) -> dict[str, object]:
    normalized, program, ontology = compile_captured_bundle(
        capture_ontology(snapshot).captured,
        ReasonerConfig(),
    )
    class_domain = program.symbols.domain(SymbolKind.CLASS_EXPRESSION)
    data_range_domain = program.symbols.domain(SymbolKind.DATA_RANGE)
    individual_domain = program.symbols.domain(SymbolKind.INDIVIDUAL)
    source_literal_domain = program.symbols.domain(SymbolKind.SOURCE_LITERAL)
    data_value_domain = program.symbols.domain(SymbolKind.DATA_VALUE)
    entity_domain = program.symbols.domain(SymbolKind.ENTITY)
    retained_data_ranges = [
        value
        for value in data_range_domain.values
        if value.display.startswith(
            (
                "datatype:",
                "DataComplementOf:",
                "DataOneOf:",
                "DatatypeRestriction:",
                "DataIntersectionOf:",
                "DataUnionOf:",
            )
        )
    ]
    data_range_remap = {
        value.identifier: identifier for identifier, value in enumerate(retained_data_ranges)
    }
    entity_id_by_key = {value.key_hex: value.identifier for value in entity_domain.values}
    declared_class_ids = {
        value.entity_id for value in ontology.declared_entities if value.kind == "class"
    }
    declared_individual_ids = {
        value.entity_id for value in ontology.declared_entities if value.kind == "named_individual"
    }

    fragment_kinds = {
        PredicateKind.CONCEPT,
        PredicateKind.NEGATED_CONCEPT,
        PredicateKind.NOMINAL,
        PredicateKind.NEGATED_NOMINAL,
        PredicateKind.DISJOINT_GUARD,
        PredicateKind.EQUALITY,
        PredicateKind.INEQUALITY,
        PredicateKind.NAMED_INDIVIDUAL,
        PredicateKind.ORDERING_GUARD,
    }
    if include_at_least_object_predicates:
        fragment_kinds.add(PredicateKind.AT_LEAST_OBJECT)
    if include_at_least_data_predicates:
        fragment_kinds.add(PredicateKind.AT_LEAST_DATA)
    if include_annotated_equality_predicates:
        fragment_kinds.add(PredicateKind.ANNOTATED_EQUALITY)
    constraint_provenance_ids: set[int] = set()
    characteristic_provenance_ids: set[int] = set()
    self_definition_provenance_ids: set[int] = set()
    quantifier_definition_provenance_ids: set[int] = set()
    cardinality_definition_provenance_ids: set[int] = set()
    data_quantifier_definition_provenance_ids: set[int] = set()
    data_cardinality_definition_provenance_ids: set[int] = set()
    data_domain_provenance_ids: set[int] = set()
    data_range_provenance_ids: set[int] = set()
    generated_data_definition_provenance_ids: set[int] = set()
    datatype_definition_provenance_ids: set[int] = set()
    key_provenance_ids: set[int] = set()
    data_functionality_provenance_ids: set[int] = set()
    assertion_provenance_ids: set[int] = set()
    negative_assertion_provenance_ids: set[int] = set()
    data_assertion_provenance_ids: set[int] = set()
    negative_data_assertion_provenance_ids: set[int] = set()
    if (
        include_object_constraints
        or include_object_characteristics
        or include_generated_object_self_definitions
        or include_generated_object_quantifier_definitions
        or include_generated_object_cardinality_definitions
        or include_generated_data_quantifier_definitions
        or include_generated_data_cardinality_definitions
        or include_data_domains
        or include_data_ranges
        or include_generated_data_definitions
        or include_datatype_definitions
        or include_keys
        or include_data_functionalities
        or include_object_assertions
        or include_negative_object_assertions
        or include_data_assertions
        or include_negative_data_assertions
    ):
        provenance_id_by_key = {
            (value.source_sha256, value.generated): value.provenance_id
            for value in program.provenance.entries
        }
    if include_object_constraints:
        constraint_provenance_ids = {
            provenance_id_by_key[(record.provenance_sha256, record.generated)]
            for record in normalized.records
            if isinstance(
                record.statement,
                (owl.ObjectPropertyDomain, owl.ObjectPropertyRange),
            )
        }
    if include_object_characteristics:
        characteristic_provenance_ids = {
            provenance_id_by_key[(record.provenance_sha256, record.generated)]
            for record in normalized.records
            if isinstance(
                record.statement,
                (
                    owl.FunctionalObjectProperty,
                    owl.InverseFunctionalObjectProperty,
                    owl.ReflexiveObjectProperty,
                ),
            )
        }
    if include_generated_object_self_definitions:
        self_definition_provenance_ids = {
            provenance_id_by_key[(record.provenance_sha256, record.generated)]
            for record in normalized.records
            if record.generated
            and isinstance(record.statement, owl.SubClassOf)
            and (
                isinstance(record.statement.sub_class, owl.ObjectHasSelf)
                or isinstance(record.statement.super_class, owl.ObjectHasSelf)
            )
        }
    if include_generated_object_quantifier_definitions:
        quantifier_definition_provenance_ids = {
            provenance_id_by_key[(record.provenance_sha256, record.generated)]
            for record in normalized.records
            if record.generated
            and isinstance(record.statement, owl.SubClassOf)
            and (
                isinstance(
                    record.statement.sub_class,
                    (owl.ObjectSomeValuesFrom, owl.ObjectAllValuesFrom),
                )
                or isinstance(
                    record.statement.super_class,
                    (owl.ObjectSomeValuesFrom, owl.ObjectAllValuesFrom),
                )
            )
        }
    if include_generated_object_cardinality_definitions:
        cardinality_definition_provenance_ids = {
            provenance_id_by_key[(record.provenance_sha256, record.generated)]
            for record in normalized.records
            if record.generated
            and isinstance(record.statement, owl.SubClassOf)
            and (
                isinstance(
                    record.statement.sub_class,
                    (owl.ObjectMinCardinality, owl.ObjectMaxCardinality),
                )
                or isinstance(
                    record.statement.super_class,
                    (owl.ObjectMinCardinality, owl.ObjectMaxCardinality),
                )
            )
        }
    if include_generated_data_quantifier_definitions:
        data_quantifier_definition_provenance_ids = {
            provenance_id_by_key[(record.provenance_sha256, record.generated)]
            for record in normalized.records
            if record.generated
            and isinstance(record.statement, owl.SubClassOf)
            and (
                isinstance(
                    record.statement.sub_class,
                    (owl.DataSomeValuesFrom, owl.DataAllValuesFrom),
                )
                or isinstance(
                    record.statement.super_class,
                    (owl.DataSomeValuesFrom, owl.DataAllValuesFrom),
                )
            )
        }
    if include_generated_data_cardinality_definitions:
        data_cardinality_definition_provenance_ids = {
            provenance_id_by_key[(record.provenance_sha256, record.generated)]
            for record in normalized.records
            if record.generated
            and isinstance(record.statement, owl.SubClassOf)
            and (
                isinstance(
                    record.statement.sub_class,
                    (owl.DataMinCardinality, owl.DataMaxCardinality),
                )
                or isinstance(
                    record.statement.super_class,
                    (owl.DataMinCardinality, owl.DataMaxCardinality),
                )
            )
        }
    if include_data_domains:
        data_domain_provenance_ids = {
            provenance_id_by_key[(record.provenance_sha256, record.generated)]
            for record in normalized.records
            if isinstance(record.statement, owl.DataPropertyDomain)
        }
    if include_data_ranges:
        data_range_provenance_ids = {
            provenance_id_by_key[(record.provenance_sha256, record.generated)]
            for record in normalized.records
            if isinstance(record.statement, owl.DataPropertyRange)
        }
    if include_generated_data_definitions:
        generated_data_definition_provenance_ids = {
            provenance_id_by_key[(record.provenance_sha256, record.generated)]
            for record in normalized.records
            if isinstance(record.statement, DataRangeInclusion)
        }
    if include_datatype_definitions:
        datatype_definition_provenance_ids = {
            provenance_id_by_key[(record.provenance_sha256, record.generated)]
            for record in normalized.records
            if isinstance(record.statement, owl.DatatypeDefinition)
        }
    if include_keys:
        key_provenance_ids = {
            provenance_id_by_key[(record.provenance_sha256, record.generated)]
            for record in normalized.records
            if isinstance(record.statement, owl.HasKey)
        }
    if include_data_functionalities:
        data_functionality_provenance_ids = {
            provenance_id_by_key[(record.provenance_sha256, record.generated)]
            for record in normalized.records
            if isinstance(record.statement, owl.FunctionalDataProperty)
        }
    if include_object_assertions:
        assertion_provenance_ids = {
            provenance_id_by_key[(record.provenance_sha256, record.generated)]
            for record in normalized.records
            if isinstance(record.statement, owl.ObjectPropertyAssertion)
        }
    if include_negative_object_assertions:
        negative_assertion_provenance_ids = {
            provenance_id_by_key[(record.provenance_sha256, record.generated)]
            for record in normalized.records
            if isinstance(record.statement, owl.NegativeObjectPropertyAssertion)
        }
    if include_data_assertions:
        data_assertion_provenance_ids = {
            provenance_id_by_key[(record.provenance_sha256, record.generated)]
            for record in normalized.records
            if isinstance(record.statement, owl.DataPropertyAssertion)
        }
    if include_negative_data_assertions:
        negative_data_assertion_provenance_ids = {
            provenance_id_by_key[(record.provenance_sha256, record.generated)]
            for record in normalized.records
            if isinstance(record.statement, owl.NegativeDataPropertyAssertion)
        }
    predicates_by_id = {value.predicate_id: value for value in program.predicates.predicates}
    constraint_clauses = {
        clause.clause_id
        for clause in program.clauses
        if constraint_provenance_ids.intersection(clause.provenance_ids)
    }
    characteristic_clauses = {
        clause.clause_id
        for clause in program.clauses
        if characteristic_provenance_ids.intersection(clause.provenance_ids)
    }
    self_definition_clauses = {
        clause.clause_id
        for clause in program.clauses
        if self_definition_provenance_ids.intersection(clause.provenance_ids)
    }
    quantifier_definition_clauses = {
        clause.clause_id
        for clause in program.clauses
        if quantifier_definition_provenance_ids.intersection(clause.provenance_ids)
    }
    cardinality_definition_clauses = {
        clause.clause_id
        for clause in program.clauses
        if cardinality_definition_provenance_ids.intersection(clause.provenance_ids)
    }
    data_quantifier_definition_clauses = {
        clause.clause_id
        for clause in program.clauses
        if data_quantifier_definition_provenance_ids.intersection(clause.provenance_ids)
    }
    data_cardinality_definition_clauses = {
        clause.clause_id
        for clause in program.clauses
        if data_cardinality_definition_provenance_ids.intersection(clause.provenance_ids)
    }
    data_domain_clauses = {
        clause.clause_id
        for clause in program.clauses
        if data_domain_provenance_ids.intersection(clause.provenance_ids)
    }
    data_range_clauses = {
        clause.clause_id
        for clause in program.clauses
        if data_range_provenance_ids.intersection(clause.provenance_ids)
    }
    generated_data_definition_clauses = {
        clause.clause_id
        for clause in program.clauses
        if generated_data_definition_provenance_ids.intersection(clause.provenance_ids)
    }
    datatype_definition_clauses = {
        clause.clause_id
        for clause in program.clauses
        if datatype_definition_provenance_ids.intersection(clause.provenance_ids)
    }
    key_clauses = {
        clause.clause_id
        for clause in program.clauses
        if key_provenance_ids.intersection(clause.provenance_ids)
    }
    data_functionality_clauses = {
        clause.clause_id
        for clause in program.clauses
        if data_functionality_provenance_ids.intersection(clause.provenance_ids)
    }
    constraint_role_predicates = {
        atom.predicate_id
        for clause in program.clauses
        if clause.clause_id in constraint_clauses
        for atom in clause.body + clause.head
        if predicates_by_id[atom.predicate_id].kind is PredicateKind.OBJECT_ROLE
    }
    characteristic_role_predicates = {
        atom.predicate_id
        for clause in program.clauses
        if clause.clause_id in characteristic_clauses
        for atom in clause.body + clause.head
        if predicates_by_id[atom.predicate_id].kind is PredicateKind.OBJECT_ROLE
    }
    self_definition_role_predicates = {
        atom.predicate_id
        for clause in program.clauses
        if clause.clause_id in self_definition_clauses
        for atom in clause.body + clause.head
        if predicates_by_id[atom.predicate_id].kind is PredicateKind.OBJECT_ROLE
    }
    quantifier_definition_role_predicates = {
        atom.predicate_id
        for clause in program.clauses
        if clause.clause_id in quantifier_definition_clauses
        for atom in clause.body + clause.head
        if predicates_by_id[atom.predicate_id].kind is PredicateKind.OBJECT_ROLE
    }
    cardinality_definition_role_predicates = {
        atom.predicate_id
        for clause in program.clauses
        if clause.clause_id in cardinality_definition_clauses
        for atom in clause.body + clause.head
        if predicates_by_id[atom.predicate_id].kind is PredicateKind.OBJECT_ROLE
    }
    data_quantifier_definition_role_predicates = {
        atom.predicate_id
        for clause in program.clauses
        if clause.clause_id in data_quantifier_definition_clauses
        for atom in clause.body + clause.head
        if predicates_by_id[atom.predicate_id].kind is PredicateKind.DATA_ROLE
    }
    data_cardinality_definition_role_predicates = {
        atom.predicate_id
        for clause in program.clauses
        if clause.clause_id in data_cardinality_definition_clauses
        for atom in clause.body + clause.head
        if predicates_by_id[atom.predicate_id].kind is PredicateKind.DATA_ROLE
    }
    at_least_object_role_ids = (
        {
            value.role_id
            for value in program.predicates.predicates
            if value.kind is PredicateKind.AT_LEAST_OBJECT and value.role_id is not None
        }
        if include_at_least_object_predicates
        else set()
    )
    at_least_object_role_predicates = {
        value.predicate_id
        for value in program.predicates.predicates
        if value.kind is PredicateKind.OBJECT_ROLE and value.role_id in at_least_object_role_ids
    }
    annotated_equality_role_ids = (
        {
            value.role_id
            for value in program.predicates.predicates
            if value.kind is PredicateKind.ANNOTATED_EQUALITY and value.role_id is not None
        }
        if include_annotated_equality_predicates
        else set()
    )
    annotated_equality_role_predicates = {
        value.predicate_id
        for value in program.predicates.predicates
        if value.kind is PredicateKind.OBJECT_ROLE and value.role_id in annotated_equality_role_ids
    }
    at_least_data_role_ids = (
        {
            role_id
            for value in program.predicates.predicates
            if value.kind is PredicateKind.AT_LEAST_DATA
            for role_id in value.annotation
        }
        if include_at_least_data_predicates
        else set()
    )
    at_least_data_role_predicates = {
        value.predicate_id
        for value in program.predicates.predicates
        if value.kind is PredicateKind.DATA_ROLE and value.role_id in at_least_data_role_ids
    }
    data_domain_role_predicates = {
        atom.predicate_id
        for clause in program.clauses
        if clause.clause_id in data_domain_clauses
        for atom in clause.body + clause.head
        if predicates_by_id[atom.predicate_id].kind is PredicateKind.DATA_ROLE
    }
    data_range_role_predicates = {
        atom.predicate_id
        for clause in program.clauses
        if clause.clause_id in data_range_clauses
        for atom in clause.body + clause.head
        if predicates_by_id[atom.predicate_id].kind is PredicateKind.DATA_ROLE
    }
    data_range_predicates = {
        atom.predicate_id
        for clause in program.clauses
        if clause.clause_id in data_range_clauses
        for atom in clause.body + clause.head
        if predicates_by_id[atom.predicate_id].kind
        in {PredicateKind.DATA_RANGE, PredicateKind.NEGATED_DATA_RANGE}
    }
    generated_data_definition_predicates = {
        atom.predicate_id
        for clause in program.clauses
        if clause.clause_id in generated_data_definition_clauses
        for atom in clause.body + clause.head
        if predicates_by_id[atom.predicate_id].kind
        in {PredicateKind.DATA_RANGE, PredicateKind.NEGATED_DATA_RANGE}
    }
    data_quantifier_definition_predicates = {
        atom.predicate_id
        for clause in program.clauses
        if clause.clause_id in data_quantifier_definition_clauses
        for atom in clause.body + clause.head
        if predicates_by_id[atom.predicate_id].kind
        in {PredicateKind.DATA_RANGE, PredicateKind.NEGATED_DATA_RANGE}
    }
    data_cardinality_definition_predicates = {
        atom.predicate_id
        for clause in program.clauses
        if clause.clause_id in data_cardinality_definition_clauses
        for atom in clause.body + clause.head
        if predicates_by_id[atom.predicate_id].kind
        in {PredicateKind.DATA_RANGE, PredicateKind.NEGATED_DATA_RANGE}
    }
    if include_at_least_data_predicates:
        data_quantifier_definition_predicates.update(
            cast(int, value.filler_predicate_id)
            for value in program.predicates.predicates
            if value.kind is PredicateKind.AT_LEAST_DATA and value.filler_predicate_id is not None
        )
    datatype_definition_predicates = {
        atom.predicate_id
        for clause in program.clauses
        if clause.clause_id in datatype_definition_clauses
        for atom in clause.body + clause.head
        if predicates_by_id[atom.predicate_id].kind
        in {PredicateKind.DATA_RANGE, PredicateKind.NEGATED_DATA_RANGE}
    }
    selected_data_range_predicates = (
        data_range_predicates
        | generated_data_definition_predicates
        | data_quantifier_definition_predicates
        | data_cardinality_definition_predicates
        | datatype_definition_predicates
    )
    complemented_data_range_symbols = {
        predicates_by_id[predicate_id].symbol_id
        for predicate_id in selected_data_range_predicates
        if predicates_by_id[predicate_id].kind is PredicateKind.NEGATED_DATA_RANGE
    }
    if complemented_data_range_symbols:
        universal_data_range_id = next(
            value.identifier
            for value in retained_data_ranges
            if value.display == "datatype:http://www.w3.org/2000/01/rdf-schema#Literal"
        )
        selected_data_range_predicates.update(
            value.predicate_id
            for value in program.predicates.predicates
            if value.kind is PredicateKind.DATA_RANGE
            and value.symbol_id in complemented_data_range_symbols | {universal_data_range_id}
        )
    key_role_predicates = {
        atom.predicate_id
        for clause in program.clauses
        if clause.clause_id in key_clauses
        for atom in clause.body + clause.head
        if predicates_by_id[atom.predicate_id].kind
        in {PredicateKind.OBJECT_ROLE, PredicateKind.DATA_ROLE}
    }
    data_functionality_role_predicates = {
        atom.predicate_id
        for clause in program.clauses
        if clause.clause_id in data_functionality_clauses
        for atom in clause.body + clause.head
        if predicates_by_id[atom.predicate_id].kind is PredicateKind.DATA_ROLE
    }
    assertion_role_predicates = {
        fact.predicate_id
        for fact in program.positive_facts
        if assertion_provenance_ids.intersection(fact.provenance_ids)
        and predicates_by_id[fact.predicate_id].kind is PredicateKind.OBJECT_ROLE
    }
    negative_assertion_role_predicates = {
        fact.predicate_id
        for fact in program.negative_facts
        if negative_assertion_provenance_ids.intersection(fact.provenance_ids)
        and predicates_by_id[fact.predicate_id].kind is PredicateKind.NEGATED_OBJECT_ROLE
    }
    data_assertion_role_predicates = {
        fact.predicate_id
        for fact in program.positive_facts
        if data_assertion_provenance_ids.intersection(fact.provenance_ids)
        and predicates_by_id[fact.predicate_id].kind is PredicateKind.DATA_ROLE
    }
    negative_data_assertion_role_predicates = {
        fact.predicate_id
        for fact in program.negative_facts
        if negative_data_assertion_provenance_ids.intersection(fact.provenance_ids)
        and predicates_by_id[fact.predicate_id].kind is PredicateKind.NEGATED_DATA_ROLE
    }
    selected_role_predicates = (
        constraint_role_predicates
        | characteristic_role_predicates
        | self_definition_role_predicates
        | quantifier_definition_role_predicates
        | cardinality_definition_role_predicates
        | data_quantifier_definition_role_predicates
        | data_cardinality_definition_role_predicates
        | at_least_object_role_predicates
        | at_least_data_role_predicates
        | annotated_equality_role_predicates
        | data_domain_role_predicates
        | data_range_role_predicates
        | data_functionality_role_predicates
        | key_role_predicates
        | assertion_role_predicates
        | negative_assertion_role_predicates
        | data_assertion_role_predicates
        | negative_data_assertion_role_predicates
    )
    fragment_predicates = [
        value
        for value in program.predicates.predicates
        if value.kind in fragment_kinds
        or value.predicate_id in selected_role_predicates
        or value.predicate_id in selected_data_range_predicates
    ]
    predicate_remap = {
        value.predicate_id: identifier for identifier, value in enumerate(fragment_predicates)
    }
    predicates = [
        {
            "predicate_id": identifier,
            "kind": value.kind.value,
            "argument_sorts": [sort.value for sort in value.argument_sorts],
            "symbol_id": (
                data_range_remap[value.symbol_id]
                if value.kind in {PredicateKind.DATA_RANGE, PredicateKind.NEGATED_DATA_RANGE}
                and value.symbol_id is not None
                else value.symbol_id
            ),
            "role_id": value.role_id,
            "cardinality": value.cardinality,
            "filler_predicate_id": (
                None
                if value.filler_predicate_id is None
                else predicate_remap[value.filler_predicate_id]
            ),
            "annotation": list(value.annotation),
            "internal_key": value.internal_key,
        }
        for identifier, value in enumerate(fragment_predicates)
    ]

    expected_variables = {
        (Variable(0, TermSort.OBJECT),),
        (Variable(0, TermSort.DATA),),
    }
    projected: list[tuple[bytes, DLClause]] = []
    for clause in program.clauses:
        unary_named_clause = bool(clause.body) and not any(
            atom.arguments not in expected_variables for atom in clause.body + clause.head
        )
        nominal_clause = any(
            predicates_by_id[atom.predicate_id].kind
            in {PredicateKind.NOMINAL, PredicateKind.NEGATED_NOMINAL}
            for atom in clause.body + clause.head
        ) and all(
            isinstance(argument, IndividualTerm) or argument == Variable(0, TermSort.OBJECT)
            for atom in clause.body + clause.head
            for argument in atom.arguments
        )
        if (
            not unary_named_clause
            and not nominal_clause
            and clause.clause_id not in constraint_clauses
            and clause.clause_id not in characteristic_clauses
            and clause.clause_id not in self_definition_clauses
            and clause.clause_id not in quantifier_definition_clauses
            and clause.clause_id not in cardinality_definition_clauses
            and clause.clause_id not in data_quantifier_definition_clauses
            and clause.clause_id not in data_cardinality_definition_clauses
            and clause.clause_id not in data_domain_clauses
            and clause.clause_id not in data_range_clauses
            and clause.clause_id not in generated_data_definition_clauses
            and clause.clause_id not in datatype_definition_clauses
            and clause.clause_id not in key_clauses
            and clause.clause_id not in data_functionality_clauses
        ):
            continue
        if any(atom.predicate_id not in predicate_remap for atom in clause.body + clause.head):
            continue
        projected.append((_projected_rule_key(clause, predicate_remap), clause))
    projected.sort(key=lambda value: value[0])
    clauses = [
        {
            "clause_id": identifier,
            "body": [_projected_atom_payload(value, predicate_remap) for value in clause.body],
            "head": [_projected_atom_payload(value, predicate_remap) for value in clause.head],
            "provenance_ids": list(clause.provenance_ids),
            "join_order": list(clause.join_order),
        }
        for identifier, (_key, clause) in enumerate(projected)
    ]
    positive_facts = [
        _ground_atom_payload(value, predicate_remap)
        for value in program.positive_facts
        if value.predicate_id in predicate_remap
    ]
    negative_facts = [
        _ground_atom_payload(value, predicate_remap)
        for value in program.negative_facts
        if value.predicate_id in predicate_remap
    ]

    return {
        "schema_version": 1,
        "family": "named_class_axioms",
        "compiled_roots": compiled_roots,
        "deferred_roots": 0,
        "class_expression_symbols": [_symbol_payload(value) for value in class_domain.values],
        "class_signature": [
            {
                "class_expression_id": value.identifier,
                "entity_id": entity_id_by_key[value.key_hex],
                "declared": entity_id_by_key[value.key_hex] in declared_class_ids,
            }
            for value in class_domain.values
            if value.key_hex in entity_id_by_key
        ],
        "data_range_symbols": [
            {**_symbol_payload(value), "identifier": identifier}
            for identifier, value in enumerate(retained_data_ranges)
        ],
        "individual_symbols": [_symbol_payload(value) for value in individual_domain.values],
        "source_literal_symbols": [
            _symbol_payload(value) for value in source_literal_domain.values
        ],
        "data_value_symbols": [_symbol_payload(value) for value in data_value_domain.values],
        "individual_signature": [
            {
                "individual_id": value.identifier,
                "entity_id": entity_id_by_key[value.key_hex],
                "declared": entity_id_by_key[value.key_hex] in declared_individual_ids,
            }
            for value in individual_domain.values
            if value.key_hex in entity_id_by_key
        ],
        "named_individuals": list(ontology.named_individuals),
        "predicates": predicates,
        "clauses": clauses,
        "positive_facts": positive_facts,
        "negative_facts": negative_facts,
        "provenance": [
            {
                "provenance_id": value.provenance_id,
                "source_sha256": list(value.source_sha256),
                "generated": value.generated,
            }
            for value in program.provenance.entries
        ],
    }


def test_named_class_signature_predicates_clauses_and_provenance_match_scalar() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:C))",
            "SubClassOf(:A :B)",
            "EquivalentClasses(:B :C)",
            # This merges with one normalized edge from EquivalentClasses and
            # exercises scalar-compatible multi-source provenance ownership.
            "SubClassOf(:B :C)",
        ),
        options=OPTIONS,
    )

    assert _native_manifest(snapshot) == _expected_manifest(snapshot, compiled_roots=3)
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_atomic_complement_subclass_literals_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:C))",
            "Declaration(AnnotationProperty(:note))",
            "SubClassOf(:A ObjectComplementOf(:B))",
            'SubClassOf(Annotation(:note "duplicate") :A ObjectComplementOf(:B))',
            "SubClassOf(ObjectComplementOf(:B) :C)",
            "SubClassOf(ObjectComplementOf(:A) ObjectComplementOf(:C))",
            "SubClassOf(ObjectComplementOf(:A) owl:Nothing)",
            "SubClassOf(owl:Thing ObjectComplementOf(:A))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(snapshot, compiled_roots=6)
    class_symbols = cast(list[dict[str, object]], manifest["class_expression_symbols"])
    complement_count = sum(
        str(value["display"]).startswith("ObjectComplementOf:") for value in class_symbols
    )
    assert complement_count == 3
    assert len(cast(list[object], manifest["class_signature"])) == (
        len(class_symbols) - complement_count
    )
    assert (
        sum(
            predicate["kind"] == PredicateKind.NEGATED_CONCEPT.value
            for predicate in cast(list[dict[str, object]], manifest["predicates"])
        )
        == 3
    )
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


@pytest.mark.parametrize(
    "axiom",
    [
        "SubClassOf(ObjectComplementOf(:A) ObjectComplementOf(:A))",
        "SubClassOf(ObjectComplementOf(:A) owl:Thing)",
        "SubClassOf(owl:Nothing ObjectComplementOf(:A))",
    ],
)
def test_trivial_atomic_complement_subclasses_normalize_without_symbol_leaks(
    axiom: str,
) -> None:
    snapshot = pyowl_core.load_snapshot(
        functional("Declaration(Class(:A))", axiom),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(snapshot, compiled_roots=1)
    assert all(
        not str(value["display"]).startswith("ObjectComplementOf:")
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
    )
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_atomic_complement_equivalent_classes_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:C))",
            "Declaration(AnnotationProperty(:note))",
            "EquivalentClasses(:A ObjectComplementOf(:B) :C)",
            'EquivalentClasses(Annotation(:note "duplicate") :A ObjectComplementOf(:B) :C)',
            "EquivalentClasses(ObjectComplementOf(:A) ObjectComplementOf(:C))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(snapshot, compiled_roots=3)
    assert (
        sum(
            str(value["display"]).startswith("ObjectComplementOf:")
            for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
        )
        == 3
    )
    assert (
        sum(
            predicate["kind"] == PredicateKind.NEGATED_CONCEPT.value
            for predicate in cast(list[dict[str, object]], manifest["predicates"])
        )
        == 3
    )
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_atomic_complement_disjoint_classes_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:C))",
            "Declaration(AnnotationProperty(:note))",
            "DisjointClasses(:A ObjectComplementOf(:B) :C)",
            'DisjointClasses(Annotation(:note "duplicate") :A ObjectComplementOf(:B) :C)',
            "DisjointClasses(ObjectComplementOf(:A) ObjectComplementOf(:C))",
            "DisjointClasses(:A ObjectComplementOf(:A))",
            "DisjointClasses(owl:Thing ObjectComplementOf(:B))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(snapshot, compiled_roots=5)
    assert (
        sum(
            str(value["display"]).startswith("ObjectComplementOf:")
            for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
        )
        == 3
    )
    assert (
        sum(
            predicate["kind"] == PredicateKind.NEGATED_CONCEPT.value
            for predicate in cast(list[dict[str, object]], manifest["predicates"])
        )
        == 3
    )
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_trivial_complement_disjoint_with_bottom_drops_without_symbol_leaks() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "DisjointClasses(owl:Nothing ObjectComplementOf(:A))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(snapshot, compiled_roots=1)
    assert all(
        not str(value["display"]).startswith("ObjectComplementOf:")
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
    )
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_atomic_complement_property_constraints_and_keys_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:C))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "Declaration(DataProperty(:d))",
            "Declaration(AnnotationProperty(:note))",
            "ObjectPropertyDomain(:p ObjectComplementOf(:A))",
            'ObjectPropertyDomain(Annotation(:note "duplicate") :p ObjectComplementOf(:A))',
            "ObjectPropertyRange(ObjectInverseOf(:q) ObjectComplementOf(:B))",
            "DataPropertyDomain(:d ObjectComplementOf(:C))",
            "HasKey(ObjectComplementOf(:A) (:p) (:d))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=5,
        include_object_constraints=True,
        include_data_domains=True,
        include_keys=True,
    )
    assert (
        sum(
            str(value["display"]).startswith("ObjectComplementOf:")
            for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
        )
        == 3
    )
    assert (
        sum(
            predicate["kind"] == PredicateKind.NEGATED_CONCEPT.value
            for predicate in cast(list[dict[str, object]], manifest["predicates"])
        )
        == 3
    )
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_builtin_complements_normalize_without_expression_symbol_leaks() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(DataProperty(:d))",
            "Declaration(NamedIndividual(:i))",
            "SubClassOf(ObjectComplementOf(owl:Thing) :A)",
            "EquivalentClasses(ObjectComplementOf(owl:Nothing) :A)",
            "DisjointClasses(ObjectComplementOf(owl:Thing) :A)",
            "ClassAssertion(ObjectComplementOf(owl:Nothing) :i)",
            "ObjectPropertyDomain(:p ObjectComplementOf(owl:Nothing))",
            "ObjectPropertyRange(:p ObjectComplementOf(owl:Thing))",
            "DataPropertyDomain(:d ObjectComplementOf(owl:Nothing))",
            "HasKey(ObjectComplementOf(owl:Thing) (:p) (:d))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=8,
        include_object_constraints=True,
        include_data_domains=True,
        include_keys=True,
    )
    assert all(
        not str(value["display"]).startswith("ObjectComplementOf:")
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
    )
    assert all(
        predicate["kind"] != PredicateKind.NEGATED_CONCEPT.value
        for predicate in cast(list[dict[str, object]], manifest["predicates"])
    )
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_semantic_source_literal_symbols_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "Declaration(NamedIndividual(:i))",
            "Declaration(AnnotationProperty(:note))",
            'DataPropertyAssertion(Annotation(:note "annotation-only") :p :i "plain")',
            'DataPropertyAssertion(:p :i "01"^^xsd:integer)',
            'DataPropertyAssertion(:p :i "can\'t")',
            'DataPropertyAssertion(:p :i "café")',
            'DataPropertyAssertion(:p :i "non\u00a0breaking")',
            'DataPropertyAssertion(:p :i "zero\u200bwidth")',
            'NegativeDataPropertyAssertion(:p :i "salut"@FR)',
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(snapshot)

    assert actual["source_literal_symbols"] == _expected_source_literal_symbols(snapshot)
    assert all(
        "annotation-only" not in cast(str, value["display"])
        for value in cast(list[dict[str, object]], actual["source_literal_symbols"])
    )
    assert actual["compiled_roots"] == 7
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_source_literal_symbols_merge_by_canonical_key() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "Declaration(NamedIndividual(:i))",
            'DataPropertyAssertion(:p :i "z")',
            'DataPropertyAssertion(:p :i "shared")',
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "Declaration(NamedIndividual(:i))",
            'DataPropertyAssertion(:p :i "a")',
            'DataPropertyAssertion(:p :i "shared")',
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    actual = _native_slices_manifest(*_composite_records(composite, (left, right)))

    assert actual["source_literal_symbols"] == _expected_source_literal_symbols(composite)
    assert len(cast(list[object], actual["source_literal_symbols"])) == 3
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_source_literal_symbols_follow_source_local_root_selection() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "Declaration(NamedIndividual(:i))",
            'DataPropertyAssertion(:p :i "left")',
            'DataPropertyAssertion(:p :i "right")',
        ),
        options=OPTIONS,
    )
    buffers = produce_encoded_structural_view_v2(snapshot).buffers
    root_ids = memoryview(buffers["root_ids"]).cast("I")
    node_tags = memoryview(buffers["node_tags"]).cast("H")
    assertion_rows = [
        index + 1 for index, node_id in enumerate(root_ids) if node_tags[node_id - 1] == 115
    ]
    assert len(assertion_rows) == 2

    selected_keys: set[str] = set()
    for root_id in assertion_rows:
        actual = _native_slices_manifest(
            _slice_record(
                snapshot,
                posting_mode=1,
                postings=memoryview(struct.pack("<I", root_id)),
            )
        )
        symbols = cast(list[dict[str, object]], actual["source_literal_symbols"])
        assert len(symbols) == 1
        selected_keys.add(cast(str, symbols[0]["key_hex"]))

    assert selected_keys == {
        cast(str, value["key_hex"]) for value in _expected_source_literal_symbols(snapshot)
    }
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_string_data_value_symbols_match_scalar_and_collapse_aliases() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "Declaration(NamedIndividual(:i))",
            'DataPropertyAssertion(:p :i "same")',
            'DataPropertyAssertion(:p :i "same"^^xsd:string)',
            'DataPropertyAssertion(:p :i "  a   b  "^^xsd:token)',
            'DataPropertyAssertion(:p :i "a b"^^xsd:string)',
            'DataPropertyAssertion(:p :i "normalized"^^xsd:normalizedString)',
            'DataPropertyAssertion(:p :i "en-US"^^xsd:language)',
            'DataPropertyAssertion(:p :i "ns:item"^^xsd:Name)',
            'DataPropertyAssertion(:p :i "item"^^xsd:NCName)',
            'DataPropertyAssertion(:p :i "ns:item-1"^^xsd:NMTOKEN)',
            'DataPropertyAssertion(:p :i "bonjour"@FR)',
            'DataPropertyAssertion(:p :i "café"^^xsd:string)',
            'DataPropertyAssertion(:p :i "non\u00a0breaking"^^xsd:string)',
            'DataPropertyAssertion(:p :i "zero\u200bwidth"^^xsd:string)',
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(snapshot)
    source_symbols = cast(list[object], actual["source_literal_symbols"])
    data_symbols = cast(list[dict[str, object]], actual["data_value_symbols"])

    assert data_symbols == _expected_data_value_symbols(snapshot)
    assert len(data_symbols) < len(source_symbols)
    assert all(cast(str, value["display"]).startswith("data-value:") for value in data_symbols)
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_string_aliases_share_one_global_data_identity() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "Declaration(NamedIndividual(:i))",
            'DataPropertyAssertion(:p :i "shared")',
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "Declaration(NamedIndividual(:i))",
            'DataPropertyAssertion(:p :i "shared"^^xsd:string)',
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    actual = _native_slices_manifest(*_composite_records(composite, (left, right)))

    assert actual["data_value_symbols"] == _expected_data_value_symbols(composite)
    assert len(cast(list[object], actual["source_literal_symbols"])) == 2
    assert len(cast(list[object], actual["data_value_symbols"])) == 1
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_contextual_multi_slice_program_matches_scalar_composite_exactly() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(NamedIndividual(:i))",
            "SubClassOf(:A :B)",
            "ClassAssertion(:A :i)",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:B))",
            "Declaration(Class(:C))",
            "Declaration(NamedIndividual(:j))",
            "EquivalentClasses(:B :C)",
            "DifferentIndividuals(:i :j)",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))
    left_scope = memoryview(b"a" * 32 + b"b" * 32)
    right_scope = memoryview(b"c" * 32 + b"d" * 32)

    actual = _native_slices_manifest(
        _slice_record(
            left,
            member_tokens=(b"1" * 32,),
            anonymous_scope_maps=(left_scope,),
        ),
        _slice_record(
            right,
            member_tokens=(b"2" * 32,),
            anonymous_scope_maps=(right_scope,),
        ),
    )

    assert actual == _expected_manifest(composite, compiled_roots=4)
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_atomic_complement_subclasses_remap_exactly() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:Y))",
            "Declaration(Class(:Z))",
            "SubClassOf(ObjectComplementOf(:Z) :Y)",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "SubClassOf(:A ObjectComplementOf(:B))",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    actual = _native_slices_manifest(*_composite_records(composite, (left, right)))

    assert actual == _expected_manifest(composite, compiled_roots=2)
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_atomic_complement_equivalences_remap_exactly() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:Y))",
            "Declaration(Class(:Z))",
            "EquivalentClasses(ObjectComplementOf(:Z) :Y)",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "EquivalentClasses(:A ObjectComplementOf(:B))",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    actual = _native_slices_manifest(*_composite_records(composite, (left, right)))

    assert actual == _expected_manifest(composite, compiled_roots=2)
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_atomic_complement_disjoints_remap_exactly() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:Y))",
            "Declaration(Class(:Z))",
            "DisjointClasses(ObjectComplementOf(:Z) :Y)",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "DisjointClasses(:A ObjectComplementOf(:B))",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    actual = _native_slices_manifest(*_composite_records(composite, (left, right)))

    assert actual == _expected_manifest(composite, compiled_roots=2)
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_atomic_complement_constraints_and_keys_remap_exactly() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:Y))",
            "Declaration(ObjectProperty(:z))",
            "Declaration(DataProperty(:zd))",
            "ObjectPropertyDomain(:z ObjectComplementOf(:Y))",
            "HasKey(ObjectComplementOf(:Y) (:z) (:zd))",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(ObjectProperty(:a))",
            "Declaration(DataProperty(:ad))",
            "ObjectPropertyRange(:a ObjectComplementOf(:A))",
            "DataPropertyDomain(:ad ObjectComplementOf(:A))",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    actual = _native_slices_manifest(*_composite_records(composite, (left, right)))

    assert actual == _expected_manifest(
        composite,
        compiled_roots=4,
        include_object_constraints=True,
        include_data_domains=True,
        include_keys=True,
    )
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_multi_slice_merge_deduplicates_the_same_semantic_root_across_members() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "SubClassOf(:A :B)",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:C))",
            "SubClassOf(:A :B)",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    actual = _native_slices_manifest(_slice_record(left), _slice_record(right))

    assert actual == _expected_manifest(composite, compiled_roots=1)


@pytest.mark.parametrize("posting_mode", [1, 2])
def test_source_local_include_and_exclude_match_scalar_root_selection(
    posting_mode: int,
) -> None:
    source = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "SubClassOf(:A :B)",
        ),
        options=OPTIONS,
    )
    root_ids = (3,) if posting_mode == 1 else (1, 2)
    postings = memoryview(b"".join(struct.pack("<I", value) for value in root_ids))

    actual = _native_slices_manifest(
        _slice_record(source, posting_mode=posting_mode, postings=postings)
    )

    expected = _expected_manifest(source, compiled_roots=1)
    for binding in cast(list[dict[str, object]], expected["class_signature"]):
        binding["declared"] = False
    assert actual == expected


@pytest.mark.parametrize("posting_mode", [1, 2])
def test_source_local_selection_retains_generated_restriction_dependencies(
    posting_mode: int,
) -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "Declaration(DataProperty(:d))",
            "Declaration(AnnotationProperty(:note))",
            'ObjectPropertyRange(Annotation(:note "selected") ObjectInverseOf(:p) '
            "ObjectIntersectionOf(ObjectExactCardinality(2 :q "
            "ObjectIntersectionOf(:A :B)) DataExactCardinality(1 :d "
            "DataUnionOf(xsd:string xsd:integer))))",
        ),
        options=OPTIONS,
    )
    buffers = produce_encoded_structural_view_v2(snapshot).buffers
    root_ids = memoryview(buffers["root_ids"]).cast("I")
    node_tags = memoryview(buffers["node_tags"]).cast("H")
    range_roots = tuple(
        index + 1 for index, node_id in enumerate(root_ids) if node_tags[node_id - 1] == 75
    )
    declaration_roots = tuple(
        index + 1 for index, node_id in enumerate(root_ids) if node_tags[node_id - 1] == 60
    )
    assert len(range_roots) == 1
    selected_roots = range_roots if posting_mode == 1 else declaration_roots
    postings = memoryview(b"".join(struct.pack("<I", value) for value in selected_roots))

    actual = _native_slices_manifest(
        _slice_record(snapshot, posting_mode=posting_mode, postings=postings),
        logical_fingerprint=snapshot.logical_fingerprint.digest,
    )

    expected = _expected_manifest(
        snapshot,
        compiled_roots=1,
        include_object_constraints=True,
        include_generated_object_quantifier_definitions=True,
        include_generated_object_cardinality_definitions=True,
        include_at_least_object_predicates=True,
        include_annotated_equality_predicates=True,
        include_generated_data_quantifier_definitions=True,
        include_generated_data_cardinality_definitions=True,
        include_at_least_data_predicates=True,
        include_generated_data_definitions=True,
    )
    for binding in cast(list[dict[str, object]], expected["class_signature"]):
        binding["declared"] = False
    assert actual == expected
    class_namespace = f":class:{snapshot.logical_fingerprint.hex}:"
    data_namespace = f":data:{snapshot.logical_fingerprint.hex}:"
    assert all(
        class_namespace in str(value["display"])
        for value in cast(list[dict[str, object]], actual["class_expression_symbols"])
        if value["generated"]
    )
    assert all(
        data_namespace in str(value["display"])
        for value in cast(list[dict[str, object]], actual["data_range_symbols"])
        if value["generated"]
    )
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_source_local_selection_excludes_unsupported_restriction_without_leaks() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:C))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "Declaration(ObjectProperty(:r))",
            "Declaration(DataProperty(:d))",
            "ObjectPropertyRange(ObjectInverseOf(:p) ObjectIntersectionOf("
            "ObjectExactCardinality(2 :q ObjectIntersectionOf(:A :B)) "
            "DataExactCardinality(1 :d DataUnionOf(xsd:string xsd:integer))))",
            "SubClassOf(ObjectIntersectionOf(:C ObjectSomeValuesFrom(:r :C)) "
            "ObjectMinCardinality(4294967296 :r :C))",
        ),
        options=OPTIONS,
    )
    buffers = produce_encoded_structural_view_v2(snapshot).buffers
    root_ids = memoryview(buffers["root_ids"]).cast("I")
    node_tags = memoryview(buffers["node_tags"]).cast("H")
    range_roots = tuple(
        index + 1 for index, node_id in enumerate(root_ids) if node_tags[node_id - 1] == 75
    )
    excluded_roots = tuple(
        index + 1 for index, node_id in enumerate(root_ids) if node_tags[node_id - 1] in {60, 61}
    )
    assert len(range_roots) == 1
    included = _native_slices_manifest(
        _slice_record(
            snapshot,
            posting_mode=1,
            postings=memoryview(struct.pack("<I", range_roots[0])),
        ),
        logical_fingerprint=snapshot.logical_fingerprint.digest,
    )
    excluded = _native_slices_manifest(
        _slice_record(
            snapshot,
            posting_mode=2,
            postings=memoryview(b"".join(struct.pack("<I", value) for value in excluded_roots)),
        ),
        logical_fingerprint=snapshot.logical_fingerprint.digest,
    )

    assert included == excluded
    assert included["compiled_roots"] == 1
    assert included["deferred_roots"] == 0
    assert any(
        value["generated"]
        for value in cast(list[dict[str, object]], included["class_expression_symbols"])
    )
    assert any(
        value["generated"]
        for value in cast(list[dict[str, object]], included["data_range_symbols"])
    )
    assert all(
        value["display"] != "class:urn:test:named#C"
        for value in cast(list[dict[str, object]], included["class_expression_symbols"])
    )
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


@pytest.mark.parametrize("reverse_slices", [False, True])
def test_composite_selection_retains_cross_slice_restriction_declarations(
    reverse_slices: bool,
) -> None:
    declarations = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "Declaration(DataProperty(:d))",
        ),
        options=OPTIONS,
    )
    logical = pyowl_core.load_snapshot(
        functional(
            "ObjectPropertyRange(ObjectInverseOf(:p) ObjectIntersectionOf("
            "ObjectExactCardinality(2 :q ObjectIntersectionOf(:A :B)) "
            "DataExactCardinality(1 :d DataUnionOf(xsd:string xsd:integer))))",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(
        declarations,
        logical,
        roles=("declarations", "logical"),
    )
    declaration_buffers = produce_encoded_structural_view_v2(declarations).buffers
    declaration_count = len(memoryview(declaration_buffers["root_ids"]).cast("I"))
    declaration_postings = memoryview(
        b"".join(struct.pack("<I", root_id) for root_id in range(1, declaration_count + 1))
    )
    records = _composite_selected_records(
        composite,
        (declarations, logical),
        (
            (2, declaration_postings),
            (1, memoryview(struct.pack("<I", 1))),
        ),
    )
    if reverse_slices:
        records = tuple(reversed(records))

    actual = _native_slices_manifest(
        *records,
        logical_fingerprint=composite.logical_fingerprint.digest,
    )

    expected = _expected_manifest(
        composite,
        compiled_roots=1,
        include_object_constraints=True,
        include_generated_object_quantifier_definitions=True,
        include_generated_object_cardinality_definitions=True,
        include_at_least_object_predicates=True,
        include_annotated_equality_predicates=True,
        include_generated_data_quantifier_definitions=True,
        include_generated_data_cardinality_definitions=True,
        include_at_least_data_predicates=True,
        include_generated_data_definitions=True,
    )
    for binding in cast(list[dict[str, object]], expected["class_signature"]):
        binding["declared"] = False
    assert actual == expected
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


@pytest.mark.parametrize("reverse_slices", [False, True])
def test_composite_selection_excludes_unreachable_declaration_proof_without_leaks(
    reverse_slices: bool,
) -> None:
    declarations = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:C))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "Declaration(ObjectProperty(:r))",
            "Declaration(DataProperty(:d))",
        ),
        options=OPTIONS,
    )
    logical = pyowl_core.load_snapshot(
        functional(
            "ObjectPropertyRange(ObjectInverseOf(:p) ObjectIntersectionOf("
            "ObjectExactCardinality(2 :q ObjectIntersectionOf(:A :B)) "
            "DataExactCardinality(1 :d DataUnionOf(xsd:string xsd:integer))))",
            "SubClassOf(ObjectIntersectionOf(:C ObjectSomeValuesFrom(:r :C)) "
            "ObjectMinCardinality(4294967296 :r :C))",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(
        declarations,
        logical,
        roles=("declarations", "logical"),
    )
    declaration_buffers = produce_encoded_structural_view_v2(declarations).buffers
    declaration_count = len(memoryview(declaration_buffers["root_ids"]).cast("I"))
    declaration_postings = memoryview(
        b"".join(struct.pack("<I", root_id) for root_id in range(1, declaration_count + 1))
    )
    logical_buffers = produce_encoded_structural_view_v2(logical).buffers
    root_ids = memoryview(logical_buffers["root_ids"]).cast("I")
    node_tags = memoryview(logical_buffers["node_tags"]).cast("H")
    range_root = next(
        index + 1 for index, node_id in enumerate(root_ids) if node_tags[node_id - 1] == 75
    )
    unsupported_root = next(
        index + 1 for index, node_id in enumerate(root_ids) if node_tags[node_id - 1] == 61
    )
    included = _composite_selected_records(
        composite,
        (declarations, logical),
        (
            (2, declaration_postings),
            (1, memoryview(struct.pack("<I", range_root))),
        ),
    )
    excluded = _composite_selected_records(
        composite,
        (declarations, logical),
        (
            (2, declaration_postings),
            (2, memoryview(struct.pack("<I", unsupported_root))),
        ),
    )
    if reverse_slices:
        included = tuple(reversed(included))
        excluded = tuple(reversed(excluded))

    include_manifest = _native_slices_manifest(
        *included,
        logical_fingerprint=composite.logical_fingerprint.digest,
    )
    exclude_manifest = _native_slices_manifest(
        *excluded,
        logical_fingerprint=composite.logical_fingerprint.digest,
    )

    assert include_manifest == exclude_manifest
    assert include_manifest["compiled_roots"] == 1
    assert include_manifest["deferred_roots"] == 0
    assert all(
        value["display"] != "class:urn:test:named#C"
        for value in cast(list[dict[str, object]], include_manifest["class_expression_symbols"])
    )
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_double_digit_fragment_ids_preserve_scalar_predicate_and_clause_order() -> None:
    declarations = [f"Declaration(Class(:C{index}))" for index in range(12)]
    inclusions = [f"SubClassOf(:C{index} :C{index + 1})" for index in range(11)]
    snapshot = pyowl_core.load_snapshot(
        functional(*declarations, *inclusions),
        options=OPTIONS,
    )

    assert _native_manifest(snapshot) == _expected_manifest(
        snapshot,
        compiled_roots=len(inclusions),
    )


def test_named_disjoint_classes_match_linear_guards_and_normalization_shortcuts() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:C))",
            "Declaration(NamedIndividual(:i))",
            "ClassAssertion(:A :i)",
            "DisjointClasses(:A :B)",
            # owl:Nothing is removed, so this merges provenance into the same
            # normalized disjoint record as the preceding source axiom.
            "DisjointClasses(:A :B owl:Nothing)",
            # owl:Thing forces every other live member to bottom.
            "DisjointClasses(:C owl:Thing)",
            # A set containing only one live member normalizes away entirely.
            "DisjointClasses(:C owl:Nothing)",
        ),
        options=OPTIONS,
    )

    assert _native_manifest(snapshot) == _expected_manifest(snapshot, compiled_roots=5)


def test_named_class_assertions_and_individual_signature_match_scalar() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(NamedIndividual(:declared))",
            "ClassAssertion(:A :declared)",
            # This source provenance merges with the builtin owl:Thing fact.
            "ClassAssertion(owl:Thing :declared)",
            # Undeclared named individuals remain in the exact individual
            # domain/signature and receive the same builtin facts as scalar.
            "ClassAssertion(owl:Nothing :implicit)",
        ),
        options=OPTIONS,
    )

    assert _native_manifest(snapshot) == _expected_manifest(snapshot, compiled_roots=3)


def test_atomic_complement_class_assertions_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(AnnotationProperty(:note))",
            "Declaration(NamedIndividual(:i))",
            'ClassAssertion(Annotation(:note "first") ObjectComplementOf(:A) :i)',
            'ClassAssertion(Annotation(:note "second") ObjectComplementOf(:A) :i)',
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(snapshot, compiled_roots=2)
    class_symbols = cast(list[dict[str, object]], manifest["class_expression_symbols"])
    assert len(cast(list[object], manifest["class_signature"])) == len(class_symbols) - 1
    assert (
        sum(str(value["display"]).startswith("ObjectComplementOf:") for value in class_symbols) == 1
    )
    predicates = cast(list[dict[str, object]], manifest["predicates"])
    negative_facts = cast(list[dict[str, object]], manifest["negative_facts"])
    assert len(negative_facts) == 1
    assert predicates[cast(int, negative_facts[0]["predicate_id"])]["kind"] == (
        PredicateKind.NEGATED_CONCEPT.value
    )
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_named_nominal_class_assertions_match_scalar_semantics_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(NamedIndividual(:a))",
            "Declaration(NamedIndividual(:b))",
            "Declaration(NamedIndividual(:c))",
            "Declaration(NamedIndividual(:d))",
            "Declaration(AnnotationProperty(:note))",
            "ClassAssertion(ObjectOneOf(:a :b) :c)",
            'ClassAssertion(Annotation(:note "duplicate") ObjectOneOf(:a :b) :c)',
            "ClassAssertion(ObjectOneOf(:d) :d)",
            "ClassAssertion(ObjectComplementOf(ObjectOneOf(:a :b)) :d)",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(snapshot, compiled_roots=4)
    class_symbols = cast(list[dict[str, object]], manifest["class_expression_symbols"])
    assert sum(str(value["display"]).startswith("ObjectOneOf:") for value in class_symbols) == 2
    predicates = cast(list[dict[str, object]], manifest["predicates"])
    assert sum(predicate["kind"] == PredicateKind.NOMINAL.value for predicate in predicates) == 2
    assert (
        sum(predicate["kind"] == PredicateKind.NEGATED_NOMINAL.value for predicate in predicates)
        == 1
    )
    assert sum(predicate["kind"] == PredicateKind.EQUALITY.value for predicate in predicates) == 1
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_named_nominal_class_axioms_constraints_and_keys_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(NamedIndividual(:a))",
            "Declaration(NamedIndividual(:b))",
            "Declaration(NamedIndividual(:c))",
            "Declaration(NamedIndividual(:member))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(DataProperty(:data))",
            "Declaration(AnnotationProperty(:note))",
            "SubClassOf(ObjectOneOf(:a :b) :A)",
            'SubClassOf(Annotation(:note "duplicate") ObjectOneOf(:a :b) :A)',
            "SubClassOf(:A ObjectComplementOf(ObjectOneOf(:c)))",
            "EquivalentClasses(:A ObjectOneOf(:member))",
            "DisjointClasses(:A ObjectOneOf(:a) ObjectComplementOf(ObjectOneOf(:b)))",
            "ObjectPropertyDomain(:p ObjectOneOf(:a :b))",
            "ObjectPropertyRange(ObjectInverseOf(:p) ObjectComplementOf(ObjectOneOf(:c)))",
            "DataPropertyDomain(:data ObjectOneOf(:member))",
            "HasKey(ObjectComplementOf(ObjectOneOf(:a :b)) (:p) (:data))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=9,
        include_object_constraints=True,
        include_data_domains=True,
        include_keys=True,
    )
    class_symbols = cast(list[dict[str, object]], manifest["class_expression_symbols"])
    assert sum(str(value["display"]).startswith("ObjectOneOf:") for value in class_symbols) == 5
    assert (
        sum(str(value["display"]).startswith("ObjectComplementOf:") for value in class_symbols) == 3
    )
    predicates = cast(list[dict[str, object]], manifest["predicates"])
    assert sum(predicate["kind"] == PredicateKind.NOMINAL.value for predicate in predicates) == 5
    assert (
        sum(predicate["kind"] == PredicateKind.NEGATED_NOMINAL.value for predicate in predicates)
        == 3
    )
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_nested_atomic_class_complements_reduce_by_parity_exactly() -> None:
    double_a = "ObjectComplementOf(ObjectComplementOf(:A))"
    triple_a = f"ObjectComplementOf({double_a})"
    double_b = "ObjectComplementOf(ObjectComplementOf(:B))"
    triple_b = f"ObjectComplementOf({double_b})"
    double_nominal = "ObjectComplementOf(ObjectComplementOf(ObjectOneOf(:a)))"
    triple_nominal = f"ObjectComplementOf({double_nominal})"
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(DataProperty(:data))",
            "Declaration(NamedIndividual(:a))",
            "Declaration(NamedIndividual(:i))",
            f"ClassAssertion({double_a} :i)",
            f"ClassAssertion({triple_a} :i)",
            f"SubClassOf({double_a} {triple_b})",
            f"EquivalentClasses({triple_a} {double_b})",
            f"DisjointClasses({double_a} {triple_b})",
            f"ObjectPropertyDomain(:p {double_nominal})",
            f"ObjectPropertyRange(:p {triple_nominal})",
            f"DataPropertyDomain(:data {triple_a})",
            f"HasKey({double_nominal} (:p) (:data))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=9,
        include_object_constraints=True,
        include_data_domains=True,
        include_keys=True,
    )
    class_symbols = cast(list[dict[str, object]], manifest["class_expression_symbols"])
    assert (
        sum(str(value["display"]).startswith("ObjectComplementOf:") for value in class_symbols) == 3
    )
    assert sum(str(value["display"]).startswith("ObjectOneOf:") for value in class_symbols) == 1
    predicates = cast(list[dict[str, object]], manifest["predicates"])
    assert (
        sum(predicate["kind"] == PredicateKind.NEGATED_CONCEPT.value for predicate in predicates)
        == 2
    )
    assert (
        sum(predicate["kind"] == PredicateKind.NEGATED_NOMINAL.value for predicate in predicates)
        == 1
    )
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_reducible_class_booleans_collapse_to_atomic_literals_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(DataProperty(:d))",
            "Declaration(NamedIndividual(:a))",
            "Declaration(NamedIndividual(:i))",
            "ClassAssertion(ObjectIntersectionOf(:A owl:Thing) :i)",
            "SubClassOf(ObjectUnionOf(:A owl:Nothing) ObjectIntersectionOf(:B owl:Thing))",
            "EquivalentClasses(ObjectIntersectionOf(ObjectComplementOf(:A) "
            "owl:Thing) ObjectUnionOf(:B owl:Nothing))",
            "DisjointClasses(ObjectUnionOf(ObjectOneOf(:a) owl:Nothing) "
            "ObjectIntersectionOf(:B owl:Thing))",
            "ObjectPropertyDomain(:p ObjectIntersectionOf(:A owl:Thing))",
            "ObjectPropertyRange(:p ObjectUnionOf(:B owl:Nothing))",
            "DataPropertyDomain(:d ObjectIntersectionOf(ObjectComplementOf(:A) owl:Thing))",
            "HasKey(ObjectUnionOf(ObjectOneOf(:a) owl:Nothing) (:p) (:d))",
            "SubClassOf(ObjectIntersectionOf(:A owl:Nothing) :B)",
            "SubClassOf(:A ObjectUnionOf(:B owl:Thing))",
            "SubClassOf(ObjectIntersectionOf(:A ObjectComplementOf(ObjectComplementOf(:A))) :B)",
            "SubClassOf(ObjectComplementOf(ObjectUnionOf(ObjectComplementOf(:A) owl:Nothing)) :B)",
            "DisjointClasses(ObjectIntersectionOf(:A owl:Thing) ObjectUnionOf(:A owl:Nothing))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=13,
        include_object_constraints=True,
        include_data_domains=True,
        include_keys=True,
    )
    class_symbols = cast(list[dict[str, object]], manifest["class_expression_symbols"])
    assert not any(
        str(value["display"]).startswith(("ObjectIntersectionOf:", "ObjectUnionOf:"))
        for value in class_symbols
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_absorbing_booleans_discard_supported_nested_operands_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(DataProperty(:d))",
            "Declaration(DataProperty(:e))",
            "Declaration(Datatype(:T))",
            "SubClassOf(ObjectUnionOf(owl:Thing ObjectSomeValuesFrom(:p :A)) :B)",
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

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=4,
        include_data_ranges=True,
        include_datatype_definitions=True,
    )
    assert not any(
        value["generated"]
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
    )
    assert (
        sum(
            predicate["kind"] == PredicateKind.DATA_ROLE.value
            for predicate in cast(list[dict[str, object]], manifest["predicates"])
        )
        == 2
    )
    assert not any(
        value["generated"]
        or str(value["display"]).startswith(("DataIntersectionOf:", "DataUnionOf:"))
        for value in cast(list[dict[str, object]], manifest["data_range_symbols"])
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_flat_boolean_subclass_definitions_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:C))",
            "Declaration(Class(:D))",
            "Declaration(NamedIndividual(:i))",
            "Declaration(AnnotationProperty(:note))",
            "SubClassOf(:A ObjectIntersectionOf(:B :C))",
            'SubClassOf(Annotation(:note "same definition") :A ObjectIntersectionOf(:B :C))',
            "SubClassOf(ObjectIntersectionOf(ObjectComplementOf(:A) :B) :C)",
            "SubClassOf(:A ObjectUnionOf(ObjectComplementOf(:B) :C))",
            "SubClassOf(ObjectUnionOf(ObjectOneOf(:i) :B) :C)",
            "SubClassOf(ObjectIntersectionOf(:A :B) ObjectUnionOf(:C :D))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(snapshot, compiled_roots=6)
    generated = [
        value
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
        if value["generated"]
    ]
    assert len(generated) == 6
    namespace = f":class:{snapshot.logical_fingerprint.hex}:"
    assert all(namespace in str(value["display"]) for value in generated)
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_recursive_class_boolean_definitions_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:C))",
            "Declaration(Class(:D))",
            "Declaration(Class(:E))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(DataProperty(:d))",
            "Declaration(NamedIndividual(:i))",
            "Declaration(AnnotationProperty(:note))",
            "SubClassOf(:A ObjectUnionOf(:B ObjectIntersectionOf(:C :D)))",
            'SubClassOf(Annotation(:note "same recursive definition") :A '
            "ObjectUnionOf(:B ObjectIntersectionOf(:C :D)))",
            "ClassAssertion(ObjectComplementOf(ObjectIntersectionOf("
            "ObjectComplementOf(:B) ObjectComplementOf("
            "ObjectIntersectionOf(:C :D)))) :i)",
            "SubClassOf(ObjectIntersectionOf(:A ObjectUnionOf(:B :C)) :D)",
            "EquivalentClasses(:E ObjectIntersectionOf(:A ObjectUnionOf(:B :C)))",
            "ObjectPropertyDomain(:p ObjectIntersectionOf(:A ObjectUnionOf(:B :C)))",
            "DataPropertyDomain(:d ObjectUnionOf(:B ObjectIntersectionOf(:C :D)))",
            "HasKey(ObjectIntersectionOf(:A ObjectUnionOf(:B :C)) (:p) (:d))",
            "DisjointClasses(ObjectIntersectionOf(:A ObjectUnionOf(:B :C)) :D)",
            "ObjectPropertyRange(:p ObjectUnionOf("
            "ObjectIntersectionOf(:A :B) ObjectIntersectionOf("
            ":C ObjectUnionOf(:D :E))))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=10,
        include_object_constraints=True,
        include_data_domains=True,
        include_keys=True,
    )
    generated = [
        value
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
        if value["generated"]
    ]
    assert len(generated) == 10
    assert {str(value["display"]).split(":")[-2] for value in generated} == {"negative", "positive"}
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_horn_object_quantifier_definitions_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:C))",
            "Declaration(NamedIndividual(:i))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "Declaration(DataProperty(:d))",
            "Declaration(AnnotationProperty(:note))",
            "SubClassOf(ObjectSomeValuesFrom(:p :A) :B)",
            'SubClassOf(Annotation(:note "same definition") ObjectSomeValuesFrom(:p :A) :B)',
            "SubClassOf(:A ObjectAllValuesFrom(:q :B))",
            "SubClassOf(ObjectComplementOf(ObjectAllValuesFrom(ObjectInverseOf(:p) :A)) :C)",
            "SubClassOf(:C ObjectComplementOf(ObjectSomeValuesFrom(ObjectInverseOf(:q) :B)))",
            "ClassAssertion(ObjectAllValuesFrom(:p :A) :i)",
            "ObjectPropertyDomain(:q ObjectAllValuesFrom(:p :A))",
            "DataPropertyDomain(:d ObjectAllValuesFrom(:q :B))",
            "HasKey(ObjectSomeValuesFrom(:p :A) (:q) (:d))",
            "DisjointClasses(ObjectSomeValuesFrom(:p :A) :C)",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=10,
        include_object_constraints=True,
        include_generated_object_quantifier_definitions=True,
        include_data_domains=True,
        include_keys=True,
    )
    generated = [
        value
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
        if value["generated"]
    ]
    assert len(generated) == 5
    assert {str(value["display"]).split(":")[-2] for value in generated} == {"negative", "positive"}
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_recursive_horn_object_quantifiers_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:C))",
            "Declaration(Class(:D))",
            "Declaration(NamedIndividual(:i))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "SubClassOf(ObjectIntersectionOf(:A ObjectSomeValuesFrom(:p :B)) :C)",
            "SubClassOf(:A ObjectUnionOf(:B ObjectAllValuesFrom(:q :C)))",
            "ClassAssertion(ObjectIntersectionOf(:D "
            "ObjectComplementOf(ObjectSomeValuesFrom(:p :B))) :i)",
            "DisjointClasses(ObjectUnionOf(:D ObjectComplementOf(ObjectAllValuesFrom(:q :C))) :A)",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=4,
        include_generated_object_quantifier_definitions=True,
    )
    assert (
        sum(
            bool(value["generated"])
            for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
        )
        == 8
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_recursive_object_quantifier_fillers_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:C))",
            "Declaration(Class(:D))",
            "Declaration(Class(:E))",
            "Declaration(NamedIndividual(:i))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "Declaration(AnnotationProperty(:note))",
            "SubClassOf(ObjectSomeValuesFrom(:p ObjectIntersectionOf(:A :B)) :C)",
            'SubClassOf(Annotation(:note "same nested definition") '
            "ObjectSomeValuesFrom(:p ObjectIntersectionOf(:A :B)) :C)",
            "SubClassOf(:A ObjectAllValuesFrom(:p ObjectUnionOf(:B :C)))",
            "SubClassOf(ObjectSomeValuesFrom(:p ObjectSomeValuesFrom(:q :B)) :D)",
            "SubClassOf(:D ObjectAllValuesFrom(:p ObjectAllValuesFrom(:q :C)))",
            "SubClassOf(ObjectComplementOf(ObjectAllValuesFrom(ObjectInverseOf(:p) "
            "ObjectUnionOf(:A :B))) :E)",
            "SubClassOf(:E ObjectComplementOf(ObjectSomeValuesFrom(:q "
            "ObjectIntersectionOf(:B :C))))",
            "ClassAssertion(ObjectAllValuesFrom(:p ObjectHasSelf(:q)) :i)",
            "DisjointClasses(ObjectSomeValuesFrom(:p ObjectUnionOf(:A ObjectHasSelf(:q))) :E)",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=9,
        include_generated_object_self_definitions=True,
        include_generated_object_quantifier_definitions=True,
    )
    assert (
        sum(
            bool(value["generated"])
            for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
        )
        == 17
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_recursive_object_quantifier_fillers_reuse_global_identity() -> None:
    declarations = (
        "Declaration(Class(:A))",
        "Declaration(Class(:B))",
        "Declaration(Class(:C))",
        "Declaration(ObjectProperty(:p))",
        "Declaration(ObjectProperty(:q))",
    )
    left = pyowl_core.load_snapshot(
        functional(
            *declarations,
            "SubClassOf(ObjectSomeValuesFrom(:p ObjectIntersectionOf(:A :B)) :C)",
            "SubClassOf(:A ObjectAllValuesFrom(:q ObjectUnionOf(:B :C)))",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            *declarations,
            "DisjointClasses(ObjectSomeValuesFrom(:p ObjectIntersectionOf(:A :B)) :C)",
            "ObjectPropertyDomain(:p ObjectAllValuesFrom(:q ObjectUnionOf(:B :C)))",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    manifest = _native_slices_manifest(
        *_composite_records(composite, (left, right)),
        logical_fingerprint=composite.logical_fingerprint.digest,
    )

    assert manifest == _expected_manifest(
        composite,
        compiled_roots=4,
        include_object_constraints=True,
        include_generated_object_quantifier_definitions=True,
    )
    generated = [
        value
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
        if value["generated"]
    ]
    assert len(generated) == 4
    namespace = f":class:{composite.logical_fingerprint.hex}:"
    assert all(namespace in str(value["display"]) for value in generated)
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_unsupported_recursive_quantifier_cardinality_fillers_defer_without_symbol_leaks() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:C))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "SubClassOf(ObjectSomeValuesFrom(:p ObjectMinCardinality(4294967296 :q :A)) :B)",
            "SubClassOf(:A ObjectAllValuesFrom(:p ObjectMinCardinality(4294967296 :q :B)))",
            "SubClassOf(ObjectSomeValuesFrom(:p ObjectIntersectionOf("
            "ObjectSomeValuesFrom(:q :A) "
            "ObjectMinCardinality(4294967296 :q :B))) :C)",
            "SubClassOf(ObjectAllValuesFrom(ObjectInverseOf(:p) "
            "ObjectMinCardinality(4294967296 :q :A)) :C)",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest["compiled_roots"] == 0
    assert manifest["deferred_roots"] == 4
    assert not any(
        value["generated"]
        or str(value["display"]).startswith(
            ("ObjectSomeValuesFrom:", "ObjectAllValuesFrom:", "ObjectMinCardinality:")
        )
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
    )
    assert all(
        predicate["kind"] != PredicateKind.OBJECT_ROLE.value
        for predicate in cast(list[dict[str, object]], manifest["predicates"])
    )
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_horn_object_quantifiers_reuse_global_identity() -> None:
    declarations = (
        "Declaration(Class(:A))",
        "Declaration(Class(:B))",
        "Declaration(ObjectProperty(:p))",
        "Declaration(ObjectProperty(:q))",
    )
    left = pyowl_core.load_snapshot(
        functional(
            *declarations,
            "SubClassOf(ObjectSomeValuesFrom(:p :A) :B)",
            "SubClassOf(:A ObjectAllValuesFrom(:q :B))",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            *declarations,
            "DisjointClasses(ObjectSomeValuesFrom(:p :A) :B)",
            "ObjectPropertyDomain(:p ObjectAllValuesFrom(:q :B))",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    manifest = _native_slices_manifest(
        *_composite_records(composite, (left, right)),
        logical_fingerprint=composite.logical_fingerprint.digest,
    )

    assert manifest == _expected_manifest(
        composite,
        compiled_roots=4,
        include_object_constraints=True,
        include_generated_object_quantifier_definitions=True,
    )
    generated = [
        value
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
        if value["generated"]
    ]
    assert len(generated) == 2
    namespace = f":class:{composite.logical_fingerprint.hex}:"
    assert all(namespace in str(value["display"]) for value in generated)
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_at_least_object_quantifier_polarities_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:C))",
            "Declaration(ObjectProperty(:p))",
            "SubClassOf(:A ObjectSomeValuesFrom(:p :B))",
            "SubClassOf(ObjectAllValuesFrom(:p :A) :B)",
            "EquivalentClasses(:A ObjectSomeValuesFrom(:p :B))",
            "SubClassOf(ObjectIntersectionOf(ObjectSomeValuesFrom(:p :A) "
            "ObjectAllValuesFrom(:p :B)) :C)",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=4,
        include_generated_object_quantifier_definitions=True,
        include_at_least_object_predicates=True,
    )
    assert (
        sum(
            predicate["kind"] == PredicateKind.AT_LEAST_OBJECT.value
            for predicate in cast(list[dict[str, object]], manifest["predicates"])
        )
        == 3
    )
    assert all(
        predicate["cardinality"] == 1
        and predicate["role_id"] is not None
        and predicate["filler_predicate_id"] is not None
        for predicate in cast(list[dict[str, object]], manifest["predicates"])
        if predicate["kind"] == PredicateKind.AT_LEAST_OBJECT.value
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_at_least_object_definitions_cover_duality_and_recursive_fillers() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:C))",
            "Declaration(NamedIndividual(:i))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "Declaration(AnnotationProperty(:note))",
            "SubClassOf(:A ObjectSomeValuesFrom(:p :B))",
            'SubClassOf(Annotation(:note "same at-least") :A ObjectSomeValuesFrom(:p :B))',
            "SubClassOf(:C ObjectComplementOf(ObjectAllValuesFrom("
            "ObjectInverseOf(:p) ObjectComplementOf(:A))))",
            "SubClassOf(ObjectComplementOf(ObjectSomeValuesFrom("
            "ObjectInverseOf(:p) ObjectComplementOf(:B))) :C)",
            "ClassAssertion(ObjectSomeValuesFrom(:q ObjectIntersectionOf(:A :B)) :i)",
            "DisjointClasses(ObjectAllValuesFrom(:q ObjectUnionOf(:A :B)) :C)",
            "SubClassOf(:B ObjectSomeValuesFrom(:p ObjectOneOf(:i)))",
            "SubClassOf(ObjectAllValuesFrom(:p ObjectOneOf(:i)) :B)",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=8,
        include_generated_object_quantifier_definitions=True,
        include_at_least_object_predicates=True,
    )
    assert (
        sum(
            predicate["kind"] == PredicateKind.AT_LEAST_OBJECT.value
            for predicate in cast(list[dict[str, object]], manifest["predicates"])
        )
        == 7
    )
    assert (
        sum(
            bool(value["generated"])
            for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
        )
        == 9
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_at_least_object_definitions_reuse_global_identity() -> None:
    declarations = (
        "Declaration(Class(:A))",
        "Declaration(Class(:B))",
        "Declaration(Class(:C))",
        "Declaration(ObjectProperty(:p))",
        "Declaration(ObjectProperty(:q))",
    )
    some = "ObjectSomeValuesFrom(:p ObjectIntersectionOf(:B :C))"
    all_values = "ObjectAllValuesFrom(:q ObjectUnionOf(:B :C))"
    left = pyowl_core.load_snapshot(
        functional(
            *declarations,
            f"SubClassOf(:A {some})",
            f"SubClassOf({all_values} :A)",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            *declarations,
            f"ObjectPropertyDomain(:q {some})",
            f"DisjointClasses({all_values} :A)",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    manifest = _native_slices_manifest(
        *_composite_records(composite, (left, right)),
        logical_fingerprint=composite.logical_fingerprint.digest,
    )

    assert manifest == _expected_manifest(
        composite,
        compiled_roots=4,
        include_object_constraints=True,
        include_generated_object_quantifier_definitions=True,
        include_at_least_object_predicates=True,
    )
    generated = [
        value
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
        if value["generated"]
    ]
    assert len(generated) == 4
    assert (
        sum(
            predicate["kind"] == PredicateKind.AT_LEAST_OBJECT.value
            for predicate in cast(list[dict[str, object]], manifest["predicates"])
        )
        == 2
    )
    namespace = f":class:{composite.logical_fingerprint.hex}:"
    assert all(namespace in str(value["display"]) for value in generated)
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_object_self_definitions_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:C))",
            "Declaration(NamedIndividual(:i))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "Declaration(DataProperty(:d))",
            "Declaration(AnnotationProperty(:note))",
            "SubClassOf(:A ObjectHasSelf(:p))",
            'SubClassOf(Annotation(:note "same definition") :A ObjectHasSelf(:p))',
            "SubClassOf(ObjectHasSelf(:p) :B)",
            "EquivalentClasses(:A ObjectHasSelf(:q))",
            "ClassAssertion(ObjectHasSelf(:p) :i)",
            "ObjectPropertyDomain(:q ObjectHasSelf(:p))",
            "ObjectPropertyRange(:q ObjectHasSelf(:p))",
            "DataPropertyDomain(:d ObjectHasSelf(:p))",
            "HasKey(ObjectHasSelf(:p) (:q) (:d))",
            "DisjointClasses(ObjectHasSelf(:p) :C)",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=10,
        include_object_constraints=True,
        include_generated_object_self_definitions=True,
        include_data_domains=True,
        include_keys=True,
    )
    generated = [
        value
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
        if value["generated"]
    ]
    assert len(generated) == 4
    assert {str(value["display"]).split(":")[-2] for value in generated} == {"negative", "positive"}
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_object_self_definitions_use_global_namespace() -> None:
    declarations = (
        "Declaration(Class(:A))",
        "Declaration(Class(:B))",
        "Declaration(NamedIndividual(:i))",
        "Declaration(ObjectProperty(:p))",
    )
    left = pyowl_core.load_snapshot(
        functional(
            *declarations,
            "SubClassOf(:A ObjectHasSelf(:p))",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            *declarations,
            "ClassAssertion(ObjectHasSelf(:p) :i)",
            "SubClassOf(ObjectHasSelf(:p) :B)",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    manifest = _native_slices_manifest(
        *_composite_records(composite, (left, right)),
        logical_fingerprint=composite.logical_fingerprint.digest,
    )

    assert manifest == _expected_manifest(
        composite,
        compiled_roots=3,
        include_generated_object_self_definitions=True,
    )
    generated = [
        value
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
        if value["generated"]
    ]
    assert len(generated) == 2
    namespace = f":class:{composite.logical_fingerprint.hex}:"
    assert all(namespace in str(value["display"]) for value in generated)
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_recursive_object_self_definitions_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:C))",
            "Declaration(Class(:U))",
            "Declaration(Class(:V))",
            "Declaration(NamedIndividual(:i))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "Declaration(DataProperty(:d))",
            "Declaration(AnnotationProperty(:note))",
            "SubClassOf(:A ObjectComplementOf(ObjectHasSelf(:p)))",
            'SubClassOf(Annotation(:note "same definition") :A '
            "ObjectComplementOf(ObjectHasSelf(:p)))",
            "SubClassOf(ObjectComplementOf(ObjectHasSelf(:p)) :B)",
            "EquivalentClasses(:A ObjectIntersectionOf(:B ObjectHasSelf(:q)))",
            "ClassAssertion(ObjectUnionOf(:B ObjectHasSelf(:p)) :i)",
            "ObjectPropertyDomain(:q ObjectComplementOf(ObjectHasSelf(:p)))",
            "ObjectPropertyRange(:q ObjectIntersectionOf(:A ObjectHasSelf(:p)))",
            "DataPropertyDomain(:d ObjectComplementOf(ObjectHasSelf(:p)))",
            "HasKey(ObjectUnionOf(:B ObjectHasSelf(:p)) (:q) (:d))",
            "DisjointClasses(ObjectComplementOf(ObjectHasSelf(:p)) :C)",
            "DisjointUnion(:U ObjectHasSelf(ObjectInverseOf(:p)) :A)",
            "DisjointUnion(:V ObjectIntersectionOf(:A ObjectHasSelf(:p)) :B)",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=12,
        include_object_constraints=True,
        include_generated_object_self_definitions=True,
        include_data_domains=True,
        include_keys=True,
    )
    assert (
        sum(
            bool(value["generated"])
            for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
        )
        == 16
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_recursive_object_self_definitions_reuse_global_identity() -> None:
    declarations = (
        "Declaration(Class(:A))",
        "Declaration(Class(:B))",
        "Declaration(Class(:U))",
        "Declaration(NamedIndividual(:i))",
        "Declaration(ObjectProperty(:p))",
    )
    left = pyowl_core.load_snapshot(
        functional(
            *declarations,
            "SubClassOf(:A ObjectUnionOf(:B ObjectComplementOf(ObjectHasSelf(:p))))",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            *declarations,
            "ClassAssertion(ObjectUnionOf(:B ObjectComplementOf(ObjectHasSelf(:p))) :i)",
            "DisjointUnion(:U ObjectHasSelf(:p) :A)",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    manifest = _native_slices_manifest(
        *_composite_records(composite, (left, right)),
        logical_fingerprint=composite.logical_fingerprint.digest,
    )

    assert manifest == _expected_manifest(
        composite,
        compiled_roots=3,
        include_generated_object_self_definitions=True,
    )
    generated = [
        value
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
        if value["generated"]
    ]
    assert len(generated) == 5
    namespace = f":class:{composite.logical_fingerprint.hex}:"
    assert all(namespace in str(value["display"]) for value in generated)
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_object_minimum_definitions_match_scalar_at_least_predicates() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:C))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "SubClassOf(:A ObjectMinCardinality(2 :p :B))",
            "SubClassOf(ObjectMinCardinality(3 ObjectInverseOf(:q) :C) :A)",
            "EquivalentClasses(:B ObjectMinCardinality(4 :p :C))",
            "SubClassOf(:C ObjectMinCardinality(4294967295 :q :A))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=4,
        include_generated_object_cardinality_definitions=True,
        include_at_least_object_predicates=True,
    )
    at_least = [
        predicate
        for predicate in cast(list[dict[str, object]], manifest["predicates"])
        if predicate["kind"] == PredicateKind.AT_LEAST_OBJECT.value
    ]
    assert {predicate["cardinality"] for predicate in at_least} == {
        2,
        3,
        4,
        4294967295,
    }
    assert all(predicate["filler_predicate_id"] is not None for predicate in at_least)
    assert any(
        predicate["kind"] == PredicateKind.INEQUALITY.value
        for predicate in cast(list[dict[str, object]], manifest["predicates"])
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_object_minimum_cardinality_above_u32_defers_without_symbol_leaks() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(ObjectProperty(:p))",
            "SubClassOf(:A ObjectMinCardinality(4294967296 :p :B))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest["compiled_roots"] == 0
    assert manifest["deferred_roots"] == 1
    assert not any(
        value["generated"] or str(value["display"]).startswith("ObjectMinCardinality:")
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
    )
    assert all(
        predicate["kind"]
        not in {
            PredicateKind.AT_LEAST_OBJECT.value,
            PredicateKind.OBJECT_ROLE.value,
            PredicateKind.INEQUALITY.value,
        }
        for predicate in cast(list[dict[str, object]], manifest["predicates"])
    )
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_object_minimum_definitions_cover_recursive_and_nominal_fillers() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:C))",
            "Declaration(NamedIndividual(:i))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "Declaration(AnnotationProperty(:note))",
            "SubClassOf(:A ObjectMinCardinality(2 :p ObjectIntersectionOf(:B ObjectHasSelf(:q))))",
            'SubClassOf(Annotation(:note "same minimum") :A '
            "ObjectMinCardinality(2 :p "
            "ObjectIntersectionOf(:B ObjectHasSelf(:q))))",
            "SubClassOf(ObjectMinCardinality(3 :p ObjectUnionOf(:B :C)) :A)",
            "ClassAssertion(ObjectMinCardinality(4 ObjectInverseOf(:p) ObjectOneOf(:i)) :i)",
            "DisjointClasses(ObjectMinCardinality(2 :q ObjectComplementOf(:B)) :C)",
            "ObjectPropertyDomain(:q ObjectMinCardinality(3 :p ObjectSomeValuesFrom(:q :B)))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=6,
        include_object_constraints=True,
        include_generated_object_self_definitions=True,
        include_generated_object_quantifier_definitions=True,
        include_generated_object_cardinality_definitions=True,
        include_at_least_object_predicates=True,
    )
    at_least = [
        predicate
        for predicate in cast(list[dict[str, object]], manifest["predicates"])
        if predicate["kind"] == PredicateKind.AT_LEAST_OBJECT.value
    ]
    assert {predicate["cardinality"] for predicate in at_least} == {1, 2, 3, 4}
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_object_minimum_definitions_reuse_global_identity() -> None:
    declarations = (
        "Declaration(Class(:A))",
        "Declaration(Class(:B))",
        "Declaration(Class(:C))",
        "Declaration(ObjectProperty(:p))",
        "Declaration(ObjectProperty(:q))",
    )
    minimum = "ObjectMinCardinality(2 :p ObjectIntersectionOf(:B :C))"
    left = pyowl_core.load_snapshot(
        functional(
            *declarations,
            f"SubClassOf(:A {minimum})",
            "SubClassOf(ObjectMinCardinality(3 :q ObjectUnionOf(:B :C)) :A)",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(*declarations, f"ObjectPropertyDomain(:q {minimum})"),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    manifest = _native_slices_manifest(
        *_composite_records(composite, (left, right)),
        logical_fingerprint=composite.logical_fingerprint.digest,
    )

    assert manifest == _expected_manifest(
        composite,
        compiled_roots=3,
        include_object_constraints=True,
        include_generated_object_cardinality_definitions=True,
        include_at_least_object_predicates=True,
    )
    at_least = [
        predicate
        for predicate in cast(list[dict[str, object]], manifest["predicates"])
        if predicate["kind"] == PredicateKind.AT_LEAST_OBJECT.value
    ]
    assert len(at_least) == 2
    generated = [
        value
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
        if value["generated"]
    ]
    namespace = f":class:{composite.logical_fingerprint.hex}:"
    assert generated and all(namespace in str(value["display"]) for value in generated)
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_object_minimum_one_normalizes_to_scalar_existential_identity() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:C))",
            "Declaration(NamedIndividual(:i))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "Declaration(AnnotationProperty(:note))",
            "SubClassOf(:A ObjectMinCardinality(1 :p ObjectIntersectionOf(:B :C)))",
            'SubClassOf(Annotation(:note "same existential") :A '
            "ObjectMinCardinality(1 :p ObjectIntersectionOf(:B :C)))",
            "SubClassOf(:A ObjectSomeValuesFrom(:p ObjectIntersectionOf(:B :C)))",
            "SubClassOf(ObjectMinCardinality(1 ObjectInverseOf(:q) ObjectOneOf(:i)) :A)",
            "SubClassOf(:C ObjectMinCardinality(1 :q ObjectSomeValuesFrom(:p :B)))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=5,
        include_generated_object_quantifier_definitions=True,
        include_at_least_object_predicates=True,
    )
    assert not any(
        str(value["display"]).startswith("ObjectMinCardinality:")
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
    )
    assert {
        predicate["cardinality"]
        for predicate in cast(list[dict[str, object]], manifest["predicates"])
        if predicate["kind"] == PredicateKind.AT_LEAST_OBJECT.value
    } == {1}
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_object_minimum_one_covers_generated_class_contexts() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:C))",
            "Declaration(Class(:U))",
            "Declaration(NamedIndividual(:i))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "Declaration(DataProperty(:data))",
            "ClassAssertion(ObjectMinCardinality(1 :p ObjectUnionOf(:A :B)) :i)",
            "ObjectPropertyDomain(:q ObjectMinCardinality(1 :p "
            "ObjectIntersectionOf(:A ObjectHasSelf(:q))))",
            "DataPropertyDomain(:data ObjectMinCardinality(1 ObjectInverseOf(:q) ObjectOneOf(:i)))",
            "HasKey(ObjectMinCardinality(1 :p ObjectSomeValuesFrom(:q :B)) (:q) (:data))",
            "DisjointClasses(ObjectMinCardinality(1 :q ObjectComplementOf(:A)) :C)",
            "DisjointUnion(:U ObjectMinCardinality(1 :p :B) :A)",
            "SubClassOf(ObjectIntersectionOf(:B ObjectMinCardinality(1 :p "
            "ObjectUnionOf(:A :C))) :A)",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=7,
        include_object_constraints=True,
        include_generated_object_self_definitions=True,
        include_generated_object_quantifier_definitions=True,
        include_at_least_object_predicates=True,
        include_data_domains=True,
        include_keys=True,
    )
    assert not any(
        str(value["display"]).startswith("ObjectMinCardinality:")
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_object_minimum_one_reuses_explicit_existential_identity() -> None:
    declarations = (
        "Declaration(Class(:A))",
        "Declaration(Class(:B))",
        "Declaration(Class(:C))",
        "Declaration(ObjectProperty(:p))",
        "Declaration(ObjectProperty(:q))",
    )
    filler = "ObjectIntersectionOf(:B ObjectSomeValuesFrom(:q :C))"
    minimum = f"ObjectMinCardinality(1 :p {filler})"
    existential = f"ObjectSomeValuesFrom(:p {filler})"
    left = pyowl_core.load_snapshot(
        functional(
            *declarations,
            f"SubClassOf(:A {minimum})",
            f"SubClassOf({minimum} :A)",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            *declarations,
            f"ObjectPropertyDomain(:q {existential})",
            f"DisjointClasses({minimum} :A)",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    manifest = _native_slices_manifest(
        *_composite_records(composite, (left, right)),
        logical_fingerprint=composite.logical_fingerprint.digest,
    )

    assert manifest == _expected_manifest(
        composite,
        compiled_roots=4,
        include_object_constraints=True,
        include_generated_object_quantifier_definitions=True,
        include_at_least_object_predicates=True,
    )
    generated = [
        value
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
        if value["generated"]
    ]
    namespace = f":class:{composite.logical_fingerprint.hex}:"
    assert len(generated) == 6
    assert all(namespace in str(value["display"]) for value in generated)
    assert not any(
        str(value["display"]).startswith("ObjectMinCardinality:")
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_object_maximum_definitions_match_scalar_annotated_equalities() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:C))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "SubClassOf(:A ObjectMaxCardinality(1 :p :B))",
            "SubClassOf(ObjectMaxCardinality(2 ObjectInverseOf(:q) :C) :A)",
            "EquivalentClasses(:B ObjectMaxCardinality(2 :p :C))",
            "SubClassOf(:C ObjectComplementOf(ObjectMaxCardinality(1 :q :A)))",
            "SubClassOf(:A ObjectComplementOf(ObjectMinCardinality(3 :q :B)))",
            "SubClassOf(:B ObjectMaxCardinality(0 :p :C))",
            "SubClassOf(:C ObjectComplementOf(ObjectMaxCardinality(0 :q :A)))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=7,
        include_generated_object_quantifier_definitions=True,
        include_generated_object_cardinality_definitions=True,
        include_at_least_object_predicates=True,
        include_annotated_equality_predicates=True,
    )
    predicates = cast(list[dict[str, object]], manifest["predicates"])
    annotated = [
        predicate
        for predicate in predicates
        if predicate["kind"] == PredicateKind.ANNOTATED_EQUALITY.value
    ]
    assert {predicate["cardinality"] for predicate in annotated} == {1, 2}
    assert all(
        predicate["role_id"] is not None and predicate["filler_predicate_id"] is not None
        for predicate in annotated
    )
    at_least = [
        predicate
        for predicate in predicates
        if predicate["kind"] == PredicateKind.AT_LEAST_OBJECT.value
    ]
    assert {predicate["cardinality"] for predicate in at_least} == {1, 2, 3}
    assert any(predicate["kind"] == PredicateKind.ORDERING_GUARD.value for predicate in predicates)
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_object_maximum_cardinality_overflow_defers_without_symbol_leaks() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(ObjectProperty(:p))",
            "SubClassOf(:A ObjectMaxCardinality(4294967295 :p :B))",
            "SubClassOf(:A ObjectMaxCardinality(4294967296 :p :B))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest["compiled_roots"] == 0
    assert manifest["deferred_roots"] == 2
    assert not any(
        value["generated"] or str(value["display"]).startswith("ObjectMaxCardinality:")
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
    )
    assert all(
        predicate["kind"]
        not in {
            PredicateKind.ANNOTATED_EQUALITY.value,
            PredicateKind.AT_LEAST_OBJECT.value,
            PredicateKind.OBJECT_ROLE.value,
            PredicateKind.ORDERING_GUARD.value,
        }
        for predicate in cast(list[dict[str, object]], manifest["predicates"])
    )
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_object_maximum_definitions_cover_recursive_and_nominal_fillers() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:C))",
            "Declaration(NamedIndividual(:i))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "Declaration(AnnotationProperty(:note))",
            "SubClassOf(:A ObjectMaxCardinality(2 ObjectInverseOf(:p) "
            "ObjectIntersectionOf(:B ObjectHasSelf(:q))))",
            'SubClassOf(Annotation(:note "same maximum") :A '
            "ObjectMaxCardinality(2 ObjectInverseOf(:p) "
            "ObjectIntersectionOf(:B ObjectHasSelf(:q))))",
            "SubClassOf(ObjectMaxCardinality(1 :p ObjectUnionOf(:B :C)) :A)",
            "ClassAssertion(ObjectMaxCardinality(2 ObjectInverseOf(:p) ObjectOneOf(:i)) :i)",
            "DisjointClasses(ObjectMaxCardinality(1 :q ObjectComplementOf(:B)) :C)",
            "ObjectPropertyDomain(:q ObjectMaxCardinality(2 :p ObjectSomeValuesFrom(:q :B)))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=6,
        include_object_constraints=True,
        include_generated_object_self_definitions=True,
        include_generated_object_quantifier_definitions=True,
        include_generated_object_cardinality_definitions=True,
        include_at_least_object_predicates=True,
        include_annotated_equality_predicates=True,
    )
    predicates = cast(list[dict[str, object]], manifest["predicates"])
    annotated = [
        predicate
        for predicate in predicates
        if predicate["kind"] == PredicateKind.ANNOTATED_EQUALITY.value
    ]
    assert {predicate["cardinality"] for predicate in annotated} == {2}
    assert all(predicate["filler_predicate_id"] is not None for predicate in annotated)
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_object_maximum_definitions_reuse_global_identity() -> None:
    declarations = (
        "Declaration(Class(:A))",
        "Declaration(Class(:B))",
        "Declaration(Class(:C))",
        "Declaration(ObjectProperty(:p))",
        "Declaration(ObjectProperty(:q))",
    )
    maximum = "ObjectMaxCardinality(2 :p ObjectIntersectionOf(:B :C))"
    left = pyowl_core.load_snapshot(
        functional(
            *declarations,
            f"SubClassOf(:A {maximum})",
            "SubClassOf(ObjectMaxCardinality(1 :q ObjectUnionOf(:B :C)) :A)",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(*declarations, f"ObjectPropertyDomain(:q {maximum})"),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    manifest = _native_slices_manifest(
        *_composite_records(composite, (left, right)),
        logical_fingerprint=composite.logical_fingerprint.digest,
    )

    assert manifest == _expected_manifest(
        composite,
        compiled_roots=3,
        include_object_constraints=True,
        include_generated_object_cardinality_definitions=True,
        include_at_least_object_predicates=True,
        include_annotated_equality_predicates=True,
    )
    annotated = [
        predicate
        for predicate in cast(list[dict[str, object]], manifest["predicates"])
        if predicate["kind"] == PredicateKind.ANNOTATED_EQUALITY.value
    ]
    assert len(annotated) == 1
    generated = [
        value
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
        if value["generated"]
    ]
    namespace = f":class:{composite.logical_fingerprint.hex}:"
    assert generated and all(namespace in str(value["display"]) for value in generated)
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_object_exact_definitions_match_scalar_minimum_maximum_expansion() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:C))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "SubClassOf(:A ObjectExactCardinality(2 :p :B))",
            "SubClassOf(ObjectExactCardinality(3 ObjectInverseOf(:q) :C) :A)",
            "EquivalentClasses(:B ObjectExactCardinality(2 :p :C))",
            "SubClassOf(:C ObjectComplementOf(ObjectExactCardinality(2 :q :A)))",
            "SubClassOf(:A ObjectExactCardinality(1 :q :B))",
            "SubClassOf(:B ObjectComplementOf(ObjectExactCardinality(1 :p :C)))",
            "SubClassOf(:B ObjectExactCardinality(0 :p :C))",
            "SubClassOf(:C ObjectComplementOf(ObjectExactCardinality(0 :q :A)))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=8,
        include_generated_object_quantifier_definitions=True,
        include_generated_object_cardinality_definitions=True,
        include_at_least_object_predicates=True,
        include_annotated_equality_predicates=True,
    )
    predicates = cast(list[dict[str, object]], manifest["predicates"])
    annotated = [
        predicate
        for predicate in predicates
        if predicate["kind"] == PredicateKind.ANNOTATED_EQUALITY.value
    ]
    assert {predicate["cardinality"] for predicate in annotated} == {1, 2}
    at_least = [
        predicate
        for predicate in predicates
        if predicate["kind"] == PredicateKind.AT_LEAST_OBJECT.value
    ]
    assert {predicate["cardinality"] for predicate in at_least} == {1, 2, 3, 4}
    assert not any(
        str(value["display"]).startswith("ObjectExactCardinality:")
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_object_exact_cardinality_overflow_defers_without_symbol_leaks() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(ObjectProperty(:p))",
            "SubClassOf(:A ObjectExactCardinality(4294967295 :p :B))",
            "SubClassOf(:A ObjectComplementOf(ObjectExactCardinality(4294967295 :p :B)))",
            "SubClassOf(:A ObjectExactCardinality(4294967296 :p :B))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest["compiled_roots"] == 0
    assert manifest["deferred_roots"] == 3
    assert not any(
        value["generated"]
        or str(value["display"]).startswith(
            (
                "ObjectIntersectionOf:",
                "ObjectUnionOf:",
                "ObjectMinCardinality:",
                "ObjectMaxCardinality:",
                "ObjectExactCardinality:",
            )
        )
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
    )
    assert all(
        predicate["kind"]
        not in {
            PredicateKind.ANNOTATED_EQUALITY.value,
            PredicateKind.AT_LEAST_OBJECT.value,
            PredicateKind.OBJECT_ROLE.value,
            PredicateKind.ORDERING_GUARD.value,
            PredicateKind.INEQUALITY.value,
        }
        for predicate in cast(list[dict[str, object]], manifest["predicates"])
    )
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_object_exact_definitions_cover_recursive_and_nominal_fillers() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:C))",
            "Declaration(NamedIndividual(:i))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "Declaration(AnnotationProperty(:note))",
            "SubClassOf(:A ObjectExactCardinality(2 ObjectInverseOf(:p) "
            "ObjectIntersectionOf(:B ObjectHasSelf(:q))))",
            'SubClassOf(Annotation(:note "same exact") :A '
            "ObjectExactCardinality(2 ObjectInverseOf(:p) "
            "ObjectIntersectionOf(:B ObjectHasSelf(:q))))",
            "SubClassOf(ObjectExactCardinality(1 :p ObjectUnionOf(:B :C)) :A)",
            "ClassAssertion(ObjectExactCardinality(2 ObjectInverseOf(:p) ObjectOneOf(:i)) :i)",
            "DisjointClasses(ObjectComplementOf(ObjectExactCardinality(2 :q "
            "ObjectComplementOf(:B))) :C)",
            "ObjectPropertyDomain(:q ObjectExactCardinality(3 :p ObjectSomeValuesFrom(:q :B)))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=6,
        include_object_constraints=True,
        include_generated_object_self_definitions=True,
        include_generated_object_quantifier_definitions=True,
        include_generated_object_cardinality_definitions=True,
        include_at_least_object_predicates=True,
        include_annotated_equality_predicates=True,
    )
    annotated = [
        predicate
        for predicate in cast(list[dict[str, object]], manifest["predicates"])
        if predicate["kind"] == PredicateKind.ANNOTATED_EQUALITY.value
    ]
    assert {predicate["cardinality"] for predicate in annotated} == {2, 3}
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_object_exact_definitions_reuse_global_identity() -> None:
    declarations = (
        "Declaration(Class(:A))",
        "Declaration(Class(:B))",
        "Declaration(Class(:C))",
        "Declaration(ObjectProperty(:p))",
        "Declaration(ObjectProperty(:q))",
    )
    exact = "ObjectExactCardinality(2 :p ObjectIntersectionOf(:B :C))"
    left = pyowl_core.load_snapshot(
        functional(
            *declarations,
            f"SubClassOf(:A {exact})",
            "SubClassOf(ObjectComplementOf(ObjectExactCardinality(3 :q ObjectUnionOf(:B :C))) :A)",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(*declarations, f"ObjectPropertyDomain(:q {exact})"),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    manifest = _native_slices_manifest(
        *_composite_records(composite, (left, right)),
        logical_fingerprint=composite.logical_fingerprint.digest,
    )

    assert manifest == _expected_manifest(
        composite,
        compiled_roots=3,
        include_object_constraints=True,
        include_generated_object_cardinality_definitions=True,
        include_at_least_object_predicates=True,
        include_annotated_equality_predicates=True,
    )
    annotated = [
        predicate
        for predicate in cast(list[dict[str, object]], manifest["predicates"])
        if predicate["kind"] == PredicateKind.ANNOTATED_EQUALITY.value
    ]
    assert len(annotated) == 1
    generated = [
        value
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
        if value["generated"]
    ]
    namespace = f":class:{composite.logical_fingerprint.hex}:"
    assert generated and all(namespace in str(value["display"]) for value in generated)
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_object_has_value_definitions_match_scalar_singleton_nominals() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(NamedIndividual(:i))",
            "Declaration(NamedIndividual(:j))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "Declaration(AnnotationProperty(:note))",
            "SubClassOf(:A ObjectHasValue(:p :i))",
            'SubClassOf(Annotation(:note "same value") :A ObjectHasValue(:p :i))',
            "SubClassOf(ObjectHasValue(ObjectInverseOf(:q) :j) :A)",
            "EquivalentClasses(:B ObjectHasValue(:p :j))",
            "SubClassOf(:A ObjectComplementOf(ObjectHasValue(ObjectInverseOf(:p) :i)))",
            "SubClassOf(ObjectComplementOf(ObjectHasValue(:q :j)) :B)",
            "SubClassOf(:A ObjectSomeValuesFrom(:p ObjectOneOf(:i)))",
            "SubClassOf(:A ObjectAllValuesFrom(ObjectInverseOf(:p) "
            "ObjectComplementOf(ObjectOneOf(:i))))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=8,
        include_generated_object_quantifier_definitions=True,
        include_at_least_object_predicates=True,
    )
    predicates = cast(list[dict[str, object]], manifest["predicates"])
    nominals = [
        predicate
        for predicate in predicates
        if predicate["kind"]
        in {
            PredicateKind.NOMINAL.value,
            PredicateKind.NEGATED_NOMINAL.value,
        }
    ]
    assert {tuple(cast(list[int], predicate["annotation"])) for predicate in nominals} == {
        (0,),
        (1,),
    }
    assert not any(
        str(value["display"]).startswith("ObjectHasValue:")
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_object_has_value_definitions_cover_generated_class_contexts() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(NamedIndividual(:i))",
            "Declaration(NamedIndividual(:j))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "ClassAssertion(ObjectHasValue(:p :i) :j)",
            "ObjectPropertyDomain(:q ObjectHasValue(ObjectInverseOf(:p) :i))",
            "HasKey(ObjectHasValue(:q :i) (:p) ())",
            "DisjointClasses(ObjectComplementOf(ObjectHasValue(:p :i)) :A)",
            "SubClassOf(:A ObjectIntersectionOf(:B ObjectHasValue(:q :i)))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=5,
        include_object_constraints=True,
        include_generated_object_quantifier_definitions=True,
        include_at_least_object_predicates=True,
        include_keys=True,
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_undeclared_named_object_has_value_matches_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "SubClassOf(:A ObjectHasValue(:p :implicit))",
            "SubClassOf(ObjectComplementOf(ObjectHasValue(ObjectInverseOf(:q) :implicit)) :B)",
            "SubClassOf(:A ObjectSomeValuesFrom(:p ObjectOneOf(:implicit)))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=3,
        include_generated_object_quantifier_definitions=True,
        include_at_least_object_predicates=True,
    )
    assert cast(list[dict[str, object]], manifest["individual_signature"])[0]["declared"] is False
    singleton_nominals = [
        value
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
        if str(value["display"]).startswith("ObjectOneOf:")
    ]
    assert len(singleton_nominals) == 1
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_object_has_value_reuses_explicit_quantifier_identity() -> None:
    declarations = (
        "Declaration(Class(:A))",
        "Declaration(Class(:B))",
        "Declaration(NamedIndividual(:i))",
        "Declaration(ObjectProperty(:p))",
        "Declaration(ObjectProperty(:q))",
    )
    left = pyowl_core.load_snapshot(
        functional(
            *declarations,
            "SubClassOf(:A ObjectHasValue(:p :i))",
            "SubClassOf(ObjectComplementOf(ObjectHasValue(ObjectInverseOf(:q) :i)) :B)",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            *declarations,
            "ObjectPropertyDomain(:q ObjectSomeValuesFrom(:p ObjectOneOf(:i)))",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    manifest = _native_slices_manifest(
        *_composite_records(composite, (left, right)),
        logical_fingerprint=composite.logical_fingerprint.digest,
    )

    assert manifest == _expected_manifest(
        composite,
        compiled_roots=3,
        include_object_constraints=True,
        include_generated_object_quantifier_definitions=True,
        include_at_least_object_predicates=True,
    )
    singleton_nominals = [
        value
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
        if str(value["display"]).startswith("ObjectOneOf:")
    ]
    assert len(singleton_nominals) == 1
    generated = [
        value
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
        if value["generated"]
    ]
    namespace = f":class:{composite.logical_fingerprint.hex}:"
    assert generated and all(namespace in str(value["display"]) for value in generated)
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_undeclared_named_object_has_value_remaps_exactly() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(ObjectProperty(:p))",
            "SubClassOf(:A ObjectHasValue(:p :implicit))",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:B))",
            "Declaration(ObjectProperty(:p))",
            "SubClassOf(:B ObjectSomeValuesFrom(:p ObjectOneOf(:implicit)))",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))
    records = _composite_records(composite, (left, right))

    forward = _native_slices_manifest(
        *records,
        logical_fingerprint=composite.logical_fingerprint.digest,
    )
    reverse = _native_slices_manifest(
        *reversed(records),
        logical_fingerprint=composite.logical_fingerprint.digest,
    )

    assert (
        forward
        == reverse
        == _expected_manifest(
            composite,
            compiled_roots=2,
            include_generated_object_quantifier_definitions=True,
            include_at_least_object_predicates=True,
        )
    )
    assert cast(list[dict[str, object]], forward["individual_signature"])[0]["declared"] is False
    assert forward["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_object_has_value_partially_unsupported_inputs_defer_without_symbol_leaks() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(NamedIndividual(:i))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(DataProperty(:d))",
            "SubClassOf(:A ObjectHasValue(:p :undeclared))",
            "SubClassOf(:A ObjectHasValue(:p _:anonymous))",
            'EquivalentClasses(:A ObjectHasValue(:p :i) DataHasValue(:undeclared "value"))',
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest["compiled_roots"] == 1
    assert manifest["deferred_roots"] == 2
    class_symbols = cast(list[dict[str, object]], manifest["class_expression_symbols"])
    assert sum(value["generated"] for value in class_symbols) == 1
    assert sum(str(value["display"]).startswith("ObjectOneOf:") for value in class_symbols) == 1
    assert (
        sum(str(value["display"]).startswith("ObjectSomeValuesFrom:") for value in class_symbols)
        == 1
    )
    assert not any(
        str(value["display"]).startswith(
            ("ObjectComplementOf:", "ObjectAllValuesFrom:", "ObjectHasValue:")
        )
        for value in class_symbols
    )
    predicates = cast(list[dict[str, object]], manifest["predicates"])
    nominal_predicates = [
        predicate for predicate in predicates if predicate["kind"] == PredicateKind.NOMINAL.value
    ]
    assert [predicate["annotation"] for predicate in nominal_predicates] == [[1]]
    assert (
        sum(predicate["kind"] == PredicateKind.AT_LEAST_OBJECT.value for predicate in predicates)
        == 1
    )
    assert (
        sum(predicate["kind"] == PredicateKind.OBJECT_ROLE.value for predicate in predicates) == 1
    )
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_atomic_data_quantifier_definitions_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(DataProperty(:d))",
            "Declaration(DataProperty(:e))",
            "Declaration(AnnotationProperty(:note))",
            "SubClassOf(DataSomeValuesFrom(:d xsd:string) :A)",
            'SubClassOf(Annotation(:note "same definition") DataSomeValuesFrom(:d xsd:string) :A)',
            "SubClassOf(:A DataSomeValuesFrom(:d xsd:boolean))",
            "SubClassOf(DataAllValuesFrom(:d xsd:decimal) :B)",
            "SubClassOf(:A DataAllValuesFrom(:e xsd:integer))",
            "SubClassOf(ObjectComplementOf(DataAllValuesFrom(:e xsd:string)) :B)",
            "SubClassOf(:B ObjectComplementOf(DataSomeValuesFrom(:d xsd:integer)))",
            'EquivalentClasses(:A DataSomeValuesFrom(:e DataOneOf("value")))',
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=8,
        include_generated_data_quantifier_definitions=True,
        include_at_least_data_predicates=True,
    )
    predicates = cast(list[dict[str, object]], manifest["predicates"])
    at_least = [
        predicate
        for predicate in predicates
        if predicate["kind"] == PredicateKind.AT_LEAST_DATA.value
    ]
    assert at_least
    assert all(
        predicate["cardinality"] == 1
        and predicate["role_id"] is not None
        and predicate["annotation"] == [predicate["role_id"]]
        and predicate["filler_predicate_id"] is not None
        for predicate in at_least
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_atomic_data_quantifiers_cover_generated_class_contexts() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(NamedIndividual(:i))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(DataProperty(:d))",
            "Declaration(DataProperty(:e))",
            "ClassAssertion(DataAllValuesFrom(:d xsd:string) :i)",
            "ObjectPropertyDomain(:p DataSomeValuesFrom(:d xsd:boolean))",
            "DataPropertyDomain(:e DataAllValuesFrom(:d xsd:decimal))",
            "HasKey(DataSomeValuesFrom(:e xsd:integer) (:p) (:d))",
            "DisjointClasses(ObjectComplementOf(DataSomeValuesFrom(:d xsd:string)) :A)",
            'SubClassOf(ObjectIntersectionOf(:B DataAllValuesFrom(:e DataOneOf("value"))) :A)',
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=6,
        include_object_constraints=True,
        include_generated_data_quantifier_definitions=True,
        include_at_least_data_predicates=True,
        include_data_domains=True,
        include_keys=True,
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_atomic_data_quantifiers_reuse_global_identity() -> None:
    declarations = (
        "Declaration(Class(:A))",
        "Declaration(Class(:B))",
        "Declaration(ObjectProperty(:p))",
        "Declaration(DataProperty(:d))",
        "Declaration(DataProperty(:e))",
    )
    left = pyowl_core.load_snapshot(
        functional(
            *declarations,
            "SubClassOf(:A DataSomeValuesFrom(:d xsd:string))",
            "SubClassOf(DataAllValuesFrom(:e xsd:integer) :B)",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            *declarations,
            "ObjectPropertyDomain(:p DataSomeValuesFrom(:d xsd:string))",
            "DisjointClasses(DataAllValuesFrom(:e xsd:integer) :A)",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    manifest = _native_slices_manifest(
        *_composite_records(composite, (left, right)),
        logical_fingerprint=composite.logical_fingerprint.digest,
    )

    assert manifest == _expected_manifest(
        composite,
        compiled_roots=4,
        include_object_constraints=True,
        include_generated_data_quantifier_definitions=True,
        include_at_least_data_predicates=True,
    )
    generated = [
        value
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
        if value["generated"]
    ]
    namespace = f":class:{composite.logical_fingerprint.hex}:"
    assert len(generated) == 2
    assert all(namespace in str(value["display"]) for value in generated)
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_recursive_data_quantifier_fillers_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(DataProperty(:d))",
            "Declaration(DataProperty(:e))",
            "Declaration(AnnotationProperty(:note))",
            "SubClassOf(DataSomeValuesFrom(:d DataIntersectionOf(xsd:string xsd:integer)) :A)",
            'SubClassOf(Annotation(:note "same definitions") '
            "DataSomeValuesFrom(:d "
            "DataIntersectionOf(xsd:string xsd:integer)) :A)",
            "SubClassOf(:A DataSomeValuesFrom(:d DataUnionOf(xsd:boolean xsd:decimal)))",
            "DataPropertyRange(:e DataUnionOf(xsd:boolean xsd:decimal))",
            "SubClassOf(DataAllValuesFrom(:e DataUnionOf(xsd:string xsd:integer)) :B)",
            "SubClassOf(:B DataAllValuesFrom(:e DataIntersectionOf(xsd:boolean xsd:decimal)))",
            "SubClassOf(ObjectComplementOf(DataSomeValuesFrom(:e "
            "DataIntersectionOf(xsd:string xsd:decimal))) :A)",
            "SubClassOf(:B ObjectComplementOf(DataAllValuesFrom(:d "
            "DataUnionOf(xsd:boolean xsd:integer))))",
            "SubClassOf(:A DataSomeValuesFrom(:e DataIntersectionOf("
            "xsd:string DataUnionOf(xsd:integer xsd:decimal))))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=9,
        include_generated_data_quantifier_definitions=True,
        include_at_least_data_predicates=True,
        include_data_ranges=True,
        include_generated_data_definitions=True,
    )
    assert any(
        value["generated"]
        for value in cast(list[dict[str, object]], manifest["data_range_symbols"])
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_recursive_data_quantifier_fillers_cover_generated_class_contexts() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(NamedIndividual(:i))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(DataProperty(:d))",
            "Declaration(DataProperty(:e))",
            "ClassAssertion(DataAllValuesFrom(:d DataUnionOf(xsd:string xsd:integer)) :i)",
            "ObjectPropertyDomain(:p DataSomeValuesFrom(:d "
            "DataIntersectionOf(xsd:boolean xsd:decimal)))",
            "DataPropertyDomain(:e DataAllValuesFrom(:d DataUnionOf(xsd:decimal xsd:integer)))",
            "HasKey(DataSomeValuesFrom(:e DataIntersectionOf(xsd:string xsd:boolean)) (:p) (:d))",
            "DisjointClasses(ObjectComplementOf(DataSomeValuesFrom(:d "
            "DataUnionOf(xsd:string xsd:decimal))) :A)",
            "SubClassOf(ObjectIntersectionOf(:B DataAllValuesFrom(:e "
            "DataIntersectionOf(xsd:boolean xsd:integer))) :A)",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=6,
        include_object_constraints=True,
        include_generated_data_quantifier_definitions=True,
        include_at_least_data_predicates=True,
        include_generated_data_definitions=True,
        include_data_domains=True,
        include_keys=True,
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_recursive_data_quantifier_fillers_reuse_global_identity() -> None:
    declarations = (
        "Declaration(Class(:A))",
        "Declaration(Class(:B))",
        "Declaration(ObjectProperty(:p))",
        "Declaration(DataProperty(:d))",
    )
    restriction = (
        "DataSomeValuesFrom(:d DataIntersectionOf(xsd:string DataUnionOf(xsd:integer xsd:boolean)))"
    )
    left = pyowl_core.load_snapshot(
        functional(
            *declarations,
            f"SubClassOf(:A {restriction})",
            f"SubClassOf({restriction} :B)",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            *declarations,
            f"ObjectPropertyDomain(:p {restriction})",
            f"DisjointClasses({restriction} :A)",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    manifest = _native_slices_manifest(
        *_composite_records(composite, (left, right)),
        logical_fingerprint=composite.logical_fingerprint.digest,
    )

    assert manifest == _expected_manifest(
        composite,
        compiled_roots=4,
        include_object_constraints=True,
        include_generated_data_quantifier_definitions=True,
        include_at_least_data_predicates=True,
        include_generated_data_definitions=True,
    )
    class_namespace = f":class:{composite.logical_fingerprint.hex}:"
    data_namespace = f":data:{composite.logical_fingerprint.hex}:"
    assert (
        sum(
            class_namespace in str(value["display"])
            for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
            if value["generated"]
        )
        == 2
    )
    assert (
        sum(
            data_namespace in str(value["display"])
            for value in cast(list[dict[str, object]], manifest["data_range_symbols"])
            if value["generated"]
        )
        == 4
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_unsupported_data_quantifier_inputs_defer_without_symbol_leaks() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(DataProperty(:d))",
            "Declaration(DataProperty(:e))",
            "SubClassOf(:A DataSomeValuesFrom(:d :e xsd:string))",
            "SubClassOf(DataAllValuesFrom(:d :e DataIntersectionOf(xsd:string xsd:integer)) :B)",
            "SubClassOf(:A DataSomeValuesFrom(:undeclared xsd:string))",
            "EquivalentClasses(:A DataSomeValuesFrom(:d "
            "DataUnionOf(xsd:string xsd:integer)) "
            'DataHasValue(:undeclared "value"))',
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest["compiled_roots"] == 0
    assert manifest["deferred_roots"] == 4
    assert not any(
        value["generated"]
        or str(value["display"]).startswith(("DataSomeValuesFrom:", "DataAllValuesFrom:"))
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
    )
    assert not any(
        value["generated"]
        or str(value["display"]).startswith(("DataIntersectionOf:", "DataUnionOf:"))
        for value in cast(list[dict[str, object]], manifest["data_range_symbols"])
    )
    assert all(
        predicate["kind"]
        not in {
            PredicateKind.DATA_ROLE.value,
            PredicateKind.AT_LEAST_DATA.value,
        }
        for predicate in cast(list[dict[str, object]], manifest["predicates"])
    )
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_data_minimum_definitions_match_scalar_at_least_predicates() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(DataProperty(:d))",
            "Declaration(DataProperty(:e))",
            "Declaration(AnnotationProperty(:note))",
            "SubClassOf(:A DataMinCardinality(2 :d xsd:string))",
            'SubClassOf(Annotation(:note "same minimum") :A DataMinCardinality(2 :d xsd:string))',
            "SubClassOf(DataMinCardinality(3 :e xsd:boolean) :B)",
            'EquivalentClasses(:A DataMinCardinality(4 :e DataOneOf("value")))',
            "SubClassOf(:B DataMinCardinality(4294967295 :d DataComplementOf(xsd:integer)))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=5,
        include_generated_data_cardinality_definitions=True,
        include_at_least_data_predicates=True,
    )
    at_least = [
        predicate
        for predicate in cast(list[dict[str, object]], manifest["predicates"])
        if predicate["kind"] == PredicateKind.AT_LEAST_DATA.value
    ]
    assert {predicate["cardinality"] for predicate in at_least} == {
        2,
        3,
        4,
        4294967295,
    }
    assert all(
        predicate["role_id"] is not None
        and predicate["annotation"] == [predicate["role_id"]]
        and predicate["filler_predicate_id"] is not None
        for predicate in at_least
    )
    assert any(
        predicate["kind"] == PredicateKind.INEQUALITY.value
        and predicate["argument_sorts"] == [TermSort.DATA.value, TermSort.DATA.value]
        for predicate in cast(list[dict[str, object]], manifest["predicates"])
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_data_minimum_definitions_cover_generated_class_contexts() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(NamedIndividual(:i))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(DataProperty(:d))",
            "Declaration(DataProperty(:e))",
            "ClassAssertion(DataMinCardinality(2 :d xsd:string) :i)",
            "ObjectPropertyDomain(:p DataMinCardinality(3 :e xsd:boolean))",
            "DataPropertyDomain(:d DataMinCardinality(4 :e xsd:decimal))",
            "HasKey(DataMinCardinality(5 :d xsd:integer) (:p) (:e))",
            'DisjointClasses(DataMinCardinality(2 :e DataOneOf("value")) :A)',
            "SubClassOf(ObjectIntersectionOf(:B DataMinCardinality(3 :d "
            "DataComplementOf(xsd:string))) :A)",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=6,
        include_object_constraints=True,
        include_generated_data_cardinality_definitions=True,
        include_at_least_data_predicates=True,
        include_data_domains=True,
        include_keys=True,
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_data_minimum_definitions_reuse_global_identity() -> None:
    declarations = (
        "Declaration(Class(:A))",
        "Declaration(Class(:B))",
        "Declaration(ObjectProperty(:p))",
        "Declaration(DataProperty(:d))",
        "Declaration(DataProperty(:e))",
    )
    minimum = "DataMinCardinality(2 :d xsd:string)"
    left = pyowl_core.load_snapshot(
        functional(
            *declarations,
            f"SubClassOf(:A {minimum})",
            "SubClassOf(DataMinCardinality(3 :e xsd:integer) :B)",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            *declarations,
            f"ObjectPropertyDomain(:p {minimum})",
            "DisjointClasses(DataMinCardinality(3 :e xsd:integer) :A)",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    manifest = _native_slices_manifest(
        *_composite_records(composite, (left, right)),
        logical_fingerprint=composite.logical_fingerprint.digest,
    )

    assert manifest == _expected_manifest(
        composite,
        compiled_roots=4,
        include_object_constraints=True,
        include_generated_data_cardinality_definitions=True,
        include_at_least_data_predicates=True,
    )
    generated = [
        value
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
        if value["generated"]
    ]
    namespace = f":class:{composite.logical_fingerprint.hex}:"
    assert len(generated) == 2
    assert all(namespace in str(value["display"]) for value in generated)
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_recursive_data_minimum_fillers_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(DataProperty(:d))",
            "Declaration(DataProperty(:e))",
            "Declaration(AnnotationProperty(:note))",
            "SubClassOf(:A DataMinCardinality(2 :d DataIntersectionOf(xsd:string xsd:integer)))",
            'SubClassOf(Annotation(:note "same dependencies") :A '
            "DataMinCardinality(2 :d "
            "DataIntersectionOf(xsd:string xsd:integer)))",
            "SubClassOf(DataMinCardinality(3 :e DataUnionOf(xsd:boolean xsd:decimal)) :B)",
            "SubClassOf(:B DataMinCardinality(1 :d DataIntersectionOf("
            "xsd:string DataUnionOf(xsd:integer xsd:boolean))))",
            "SubClassOf(ObjectComplementOf(DataMinCardinality(3 :d "
            "DataUnionOf(xsd:string xsd:decimal))) :A)",
            "SubClassOf(:A ObjectComplementOf(DataMinCardinality(1 :e "
            "DataIntersectionOf(xsd:boolean xsd:integer))))",
            "DataPropertyRange(:e DataIntersectionOf(xsd:string xsd:integer))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=7,
        include_generated_data_quantifier_definitions=True,
        include_generated_data_cardinality_definitions=True,
        include_at_least_data_predicates=True,
        include_data_ranges=True,
        include_generated_data_definitions=True,
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_recursive_data_minimum_fillers_cover_generated_class_contexts() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(NamedIndividual(:i))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(DataProperty(:d))",
            "Declaration(DataProperty(:e))",
            "ClassAssertion(DataMinCardinality(2 :d DataUnionOf(xsd:string xsd:integer)) :i)",
            "ObjectPropertyDomain(:p DataMinCardinality(3 :e "
            "DataIntersectionOf(xsd:boolean xsd:decimal)))",
            "DataPropertyDomain(:d DataMinCardinality(4 :e DataUnionOf(xsd:decimal xsd:integer)))",
            "HasKey(DataMinCardinality(5 :d DataIntersectionOf(xsd:string xsd:boolean)) (:p) (:e))",
            "DisjointClasses(DataMinCardinality(2 :e DataUnionOf(xsd:string xsd:decimal)) :A)",
            "SubClassOf(ObjectIntersectionOf(:B DataMinCardinality(3 :d "
            "DataIntersectionOf(xsd:boolean xsd:integer))) :A)",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=6,
        include_object_constraints=True,
        include_generated_data_cardinality_definitions=True,
        include_at_least_data_predicates=True,
        include_generated_data_definitions=True,
        include_data_domains=True,
        include_keys=True,
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_recursive_data_minimum_fillers_reuse_global_identity() -> None:
    declarations = (
        "Declaration(Class(:A))",
        "Declaration(Class(:B))",
        "Declaration(ObjectProperty(:p))",
        "Declaration(DataProperty(:d))",
    )
    minimum = (
        "DataMinCardinality(2 :d "
        "DataIntersectionOf(xsd:string DataUnionOf(xsd:integer xsd:boolean)))"
    )
    left = pyowl_core.load_snapshot(
        functional(
            *declarations,
            f"SubClassOf(:A {minimum})",
            f"SubClassOf({minimum} :B)",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            *declarations,
            f"ObjectPropertyDomain(:p {minimum})",
            f"DisjointClasses({minimum} :A)",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    manifest = _native_slices_manifest(
        *_composite_records(composite, (left, right)),
        logical_fingerprint=composite.logical_fingerprint.digest,
    )

    assert manifest == _expected_manifest(
        composite,
        compiled_roots=4,
        include_object_constraints=True,
        include_generated_data_cardinality_definitions=True,
        include_at_least_data_predicates=True,
        include_generated_data_definitions=True,
    )
    class_namespace = f":class:{composite.logical_fingerprint.hex}:"
    data_namespace = f":data:{composite.logical_fingerprint.hex}:"
    assert (
        sum(
            class_namespace in str(value["display"])
            for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
            if value["generated"]
        )
        == 2
    )
    assert (
        sum(
            data_namespace in str(value["display"])
            for value in cast(list[dict[str, object]], manifest["data_range_symbols"])
            if value["generated"]
        )
        == 4
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_unsupported_data_minimum_inputs_defer_without_symbol_leaks() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(DataProperty(:d))",
            "SubClassOf(:A DataMinCardinality(4294967296 :d xsd:string))",
            "SubClassOf(:A ObjectComplementOf(DataMinCardinality(4294967296 :d xsd:string)))",
            "SubClassOf(:A DataMinCardinality(2 :undeclared xsd:string))",
            "EquivalentClasses(:A DataMinCardinality(2 :d "
            "DataIntersectionOf(xsd:string xsd:integer)) "
            'DataHasValue(:undeclared "value"))',
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest["compiled_roots"] == 0
    assert manifest["deferred_roots"] == 4
    assert not any(
        value["generated"] or str(value["display"]).startswith("DataMinCardinality:")
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
    )
    assert not any(
        value["generated"]
        or str(value["display"]).startswith(("DataIntersectionOf:", "DataUnionOf:"))
        for value in cast(list[dict[str, object]], manifest["data_range_symbols"])
    )
    assert all(
        predicate["kind"]
        not in {
            PredicateKind.AT_LEAST_DATA.value,
            PredicateKind.DATA_ROLE.value,
            PredicateKind.INEQUALITY.value,
        }
        for predicate in cast(list[dict[str, object]], manifest["predicates"])
    )
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_data_maximum_definitions_match_scalar_at_most_clauses() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(DataProperty(:d))",
            "Declaration(DataProperty(:e))",
            "Declaration(AnnotationProperty(:note))",
            "SubClassOf(:A DataMaxCardinality(1 :d xsd:string))",
            'SubClassOf(Annotation(:note "same maximum") :A DataMaxCardinality(1 :d xsd:string))',
            "SubClassOf(DataMaxCardinality(2 :e xsd:boolean) :B)",
            'EquivalentClasses(:A DataMaxCardinality(3 :e DataOneOf("value")))',
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=4,
        include_generated_data_cardinality_definitions=True,
        include_at_least_data_predicates=True,
    )
    at_least = [
        predicate
        for predicate in cast(list[dict[str, object]], manifest["predicates"])
        if predicate["kind"] == PredicateKind.AT_LEAST_DATA.value
    ]
    assert {predicate["cardinality"] for predicate in at_least} == {3, 4}
    assert any(
        predicate["kind"] == PredicateKind.EQUALITY.value
        and predicate["argument_sorts"] == [TermSort.DATA.value, TermSort.DATA.value]
        for predicate in cast(list[dict[str, object]], manifest["predicates"])
    )
    assert any(
        predicate["kind"] == PredicateKind.INEQUALITY.value
        and predicate["argument_sorts"] == [TermSort.DATA.value, TermSort.DATA.value]
        for predicate in cast(list[dict[str, object]], manifest["predicates"])
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_data_cardinality_boundaries_and_complement_duals_match_scalar() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(DataProperty(:d))",
            "Declaration(DataProperty(:e))",
            "SubClassOf(:A DataMaxCardinality(0 :d xsd:string))",
            "SubClassOf(ObjectComplementOf(DataMaxCardinality(0 :d xsd:string)) :B)",
            "SubClassOf(:A ObjectComplementOf(DataMinCardinality(2 :d xsd:string)))",
            "SubClassOf(ObjectComplementOf(DataMaxCardinality(2 :e xsd:boolean)) :B)",
            "SubClassOf(:A DataMinCardinality(1 :e xsd:integer))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=5,
        include_generated_data_quantifier_definitions=True,
        include_generated_data_cardinality_definitions=True,
        include_at_least_data_predicates=True,
    )
    assert {
        predicate["cardinality"]
        for predicate in cast(list[dict[str, object]], manifest["predicates"])
        if predicate["kind"] == PredicateKind.AT_LEAST_DATA.value
    } == {1, 3}
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_data_maximum_definitions_cover_generated_class_contexts() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(NamedIndividual(:i))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(DataProperty(:d))",
            "Declaration(DataProperty(:e))",
            "ClassAssertion(DataMaxCardinality(1 :d xsd:string) :i)",
            "ObjectPropertyDomain(:p DataMaxCardinality(2 :e xsd:boolean))",
            "DataPropertyDomain(:d DataMaxCardinality(3 :e xsd:decimal))",
            "HasKey(DataMaxCardinality(1 :d xsd:integer) (:p) (:e))",
            'DisjointClasses(DataMaxCardinality(2 :e DataOneOf("value")) :A)',
            "SubClassOf(ObjectIntersectionOf(:B DataMaxCardinality(1 :d "
            "DataComplementOf(xsd:string))) :A)",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=6,
        include_object_constraints=True,
        include_generated_data_cardinality_definitions=True,
        include_at_least_data_predicates=True,
        include_data_domains=True,
        include_keys=True,
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_data_maximum_definitions_reuse_global_identity() -> None:
    declarations = (
        "Declaration(Class(:A))",
        "Declaration(Class(:B))",
        "Declaration(ObjectProperty(:p))",
        "Declaration(DataProperty(:d))",
        "Declaration(DataProperty(:e))",
    )
    maximum = "DataMaxCardinality(1 :d xsd:string)"
    left = pyowl_core.load_snapshot(
        functional(
            *declarations,
            f"SubClassOf(:A {maximum})",
            "SubClassOf(DataMaxCardinality(2 :e xsd:integer) :B)",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            *declarations,
            f"ObjectPropertyDomain(:p {maximum})",
            "DisjointClasses(DataMaxCardinality(2 :e xsd:integer) :A)",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    manifest = _native_slices_manifest(
        *_composite_records(composite, (left, right)),
        logical_fingerprint=composite.logical_fingerprint.digest,
    )

    assert manifest == _expected_manifest(
        composite,
        compiled_roots=4,
        include_object_constraints=True,
        include_generated_data_cardinality_definitions=True,
        include_at_least_data_predicates=True,
    )
    generated = [
        value
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
        if value["generated"]
    ]
    namespace = f":class:{composite.logical_fingerprint.hex}:"
    assert len(generated) == 2
    assert all(namespace in str(value["display"]) for value in generated)
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_recursive_data_maximum_fillers_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(DataProperty(:d))",
            "Declaration(DataProperty(:e))",
            "Declaration(AnnotationProperty(:note))",
            "SubClassOf(:A DataMaxCardinality(1 :d DataIntersectionOf(xsd:string xsd:integer)))",
            'SubClassOf(Annotation(:note "same dependencies") :A '
            "DataMaxCardinality(1 :d "
            "DataIntersectionOf(xsd:string xsd:integer)))",
            "SubClassOf(DataMaxCardinality(2 :e DataUnionOf(xsd:boolean xsd:decimal)) :B)",
            "SubClassOf(:B DataMaxCardinality(0 :d DataIntersectionOf("
            "xsd:string DataUnionOf(xsd:integer xsd:boolean))))",
            "SubClassOf(ObjectComplementOf(DataMaxCardinality(0 :e "
            "DataIntersectionOf(xsd:boolean xsd:integer))) :B)",
            "SubClassOf(:A ObjectComplementOf(DataMaxCardinality(2 :d "
            "DataUnionOf(xsd:string xsd:decimal))))",
            "DataPropertyRange(:e DataUnionOf(xsd:boolean xsd:decimal))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=7,
        include_generated_data_quantifier_definitions=True,
        include_generated_data_cardinality_definitions=True,
        include_at_least_data_predicates=True,
        include_data_ranges=True,
        include_generated_data_definitions=True,
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_recursive_data_maximum_fillers_cover_generated_class_contexts() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(NamedIndividual(:i))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(DataProperty(:d))",
            "Declaration(DataProperty(:e))",
            "ClassAssertion(DataMaxCardinality(1 :d DataUnionOf(xsd:string xsd:integer)) :i)",
            "ObjectPropertyDomain(:p DataMaxCardinality(2 :e "
            "DataIntersectionOf(xsd:boolean xsd:decimal)))",
            "DataPropertyDomain(:d DataMaxCardinality(3 :e DataUnionOf(xsd:decimal xsd:integer)))",
            "HasKey(DataMaxCardinality(1 :d DataIntersectionOf(xsd:string xsd:boolean)) (:p) (:e))",
            "DisjointClasses(DataMaxCardinality(2 :e DataUnionOf(xsd:string xsd:decimal)) :A)",
            "SubClassOf(ObjectIntersectionOf(:B DataMaxCardinality(1 :d "
            "DataIntersectionOf(xsd:boolean xsd:integer))) :A)",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=6,
        include_object_constraints=True,
        include_generated_data_cardinality_definitions=True,
        include_at_least_data_predicates=True,
        include_generated_data_definitions=True,
        include_data_domains=True,
        include_keys=True,
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_recursive_data_maximum_fillers_reuse_global_identity() -> None:
    declarations = (
        "Declaration(Class(:A))",
        "Declaration(Class(:B))",
        "Declaration(ObjectProperty(:p))",
        "Declaration(DataProperty(:d))",
    )
    maximum = (
        "DataMaxCardinality(2 :d "
        "DataIntersectionOf(xsd:string DataUnionOf(xsd:integer xsd:boolean)))"
    )
    left = pyowl_core.load_snapshot(
        functional(
            *declarations,
            f"SubClassOf(:A {maximum})",
            f"SubClassOf({maximum} :B)",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            *declarations,
            f"ObjectPropertyDomain(:p {maximum})",
            f"DisjointClasses({maximum} :A)",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    manifest = _native_slices_manifest(
        *_composite_records(composite, (left, right)),
        logical_fingerprint=composite.logical_fingerprint.digest,
    )

    assert manifest == _expected_manifest(
        composite,
        compiled_roots=4,
        include_object_constraints=True,
        include_generated_data_cardinality_definitions=True,
        include_at_least_data_predicates=True,
        include_generated_data_definitions=True,
    )
    class_namespace = f":class:{composite.logical_fingerprint.hex}:"
    data_namespace = f":data:{composite.logical_fingerprint.hex}:"
    assert (
        sum(
            class_namespace in str(value["display"])
            for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
            if value["generated"]
        )
        == 2
    )
    assert (
        sum(
            data_namespace in str(value["display"])
            for value in cast(list[dict[str, object]], manifest["data_range_symbols"])
            if value["generated"]
        )
        == 4
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_unsupported_data_maximum_inputs_defer_without_symbol_leaks() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(DataProperty(:d))",
            "SubClassOf(:A DataMaxCardinality(4294967295 :d xsd:string))",
            "SubClassOf(:A DataMaxCardinality(4294967296 :d xsd:string))",
            "SubClassOf(:A DataMaxCardinality(2 :undeclared xsd:string))",
            "SubClassOf(ObjectComplementOf(DataMaxCardinality(4294967295 :d xsd:string)) :B)",
            "EquivalentClasses(:A DataMaxCardinality(2 :d "
            "DataIntersectionOf(xsd:string xsd:integer)) "
            'DataHasValue(:undeclared "value"))',
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest["compiled_roots"] == 0
    assert manifest["deferred_roots"] == 5
    assert not any(
        value["generated"]
        or str(value["display"]).startswith(("DataMinCardinality:", "DataMaxCardinality:"))
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
    )
    assert not any(
        value["generated"]
        or str(value["display"]).startswith(("DataIntersectionOf:", "DataUnionOf:"))
        for value in cast(list[dict[str, object]], manifest["data_range_symbols"])
    )
    assert all(
        predicate["kind"]
        not in {
            PredicateKind.AT_LEAST_DATA.value,
            PredicateKind.DATA_ROLE.value,
            PredicateKind.EQUALITY.value,
            PredicateKind.INEQUALITY.value,
        }
        for predicate in cast(list[dict[str, object]], manifest["predicates"])
    )
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_data_exact_cardinality_definitions_match_scalar_normalization() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(DataProperty(:d))",
            "Declaration(DataProperty(:e))",
            "Declaration(AnnotationProperty(:note))",
            "SubClassOf(:A DataExactCardinality(1 :d xsd:string))",
            'SubClassOf(Annotation(:note "same exact") :A DataExactCardinality(1 :d xsd:string))',
            "SubClassOf(DataExactCardinality(2 :e xsd:boolean) :B)",
            'EquivalentClasses(:A DataExactCardinality(2 :e DataOneOf("value")))',
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=4,
        include_generated_data_quantifier_definitions=True,
        include_generated_data_cardinality_definitions=True,
        include_at_least_data_predicates=True,
    )
    assert any(
        predicate["kind"] == PredicateKind.EQUALITY.value
        and predicate["argument_sorts"] == [TermSort.DATA.value, TermSort.DATA.value]
        for predicate in cast(list[dict[str, object]], manifest["predicates"])
    )
    assert any(
        predicate["kind"] == PredicateKind.INEQUALITY.value
        and predicate["argument_sorts"] == [TermSort.DATA.value, TermSort.DATA.value]
        for predicate in cast(list[dict[str, object]], manifest["predicates"])
    )
    assert not any(
        str(value["display"]).startswith("DataExactCardinality:")
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_data_exact_cardinality_boundaries_and_complements_match_scalar() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(DataProperty(:d))",
            "Declaration(DataProperty(:e))",
            "SubClassOf(:A DataExactCardinality(0 :d xsd:string))",
            "SubClassOf(ObjectComplementOf(DataExactCardinality(0 :d xsd:string)) :B)",
            "SubClassOf(:A DataExactCardinality(1 :e xsd:boolean))",
            "SubClassOf(ObjectComplementOf(DataExactCardinality(1 :e xsd:boolean)) :B)",
            'SubClassOf(:A ObjectComplementOf(DataExactCardinality(2 :d DataOneOf("value"))))',
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=5,
        include_generated_data_quantifier_definitions=True,
        include_generated_data_cardinality_definitions=True,
        include_at_least_data_predicates=True,
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_data_exact_cardinality_definitions_cover_generated_class_contexts() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(NamedIndividual(:i))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(DataProperty(:d))",
            "Declaration(DataProperty(:e))",
            "ClassAssertion(DataExactCardinality(1 :d xsd:string) :i)",
            "ObjectPropertyDomain(:p DataExactCardinality(2 :e xsd:boolean))",
            "DataPropertyDomain(:d DataExactCardinality(1 :e xsd:decimal))",
            "HasKey(DataExactCardinality(2 :d xsd:integer) (:p) (:e))",
            'DisjointClasses(DataExactCardinality(1 :e DataOneOf("value")) :A)',
            "SubClassOf(ObjectIntersectionOf(:B DataExactCardinality(2 :d "
            "DataComplementOf(xsd:string))) :A)",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=6,
        include_object_constraints=True,
        include_generated_data_quantifier_definitions=True,
        include_generated_data_cardinality_definitions=True,
        include_at_least_data_predicates=True,
        include_data_domains=True,
        include_keys=True,
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_data_exact_cardinality_definitions_reuse_global_identity() -> None:
    declarations = (
        "Declaration(Class(:A))",
        "Declaration(Class(:B))",
        "Declaration(ObjectProperty(:p))",
        "Declaration(DataProperty(:d))",
        "Declaration(DataProperty(:e))",
    )
    exact = "DataExactCardinality(1 :d xsd:string)"
    left = pyowl_core.load_snapshot(
        functional(
            *declarations,
            f"SubClassOf(:A {exact})",
            "SubClassOf(DataExactCardinality(2 :e xsd:integer) :B)",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            *declarations,
            f"ObjectPropertyDomain(:p {exact})",
            "DisjointClasses(DataExactCardinality(2 :e xsd:integer) :A)",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    manifest = _native_slices_manifest(
        *_composite_records(composite, (left, right)),
        logical_fingerprint=composite.logical_fingerprint.digest,
    )

    assert manifest == _expected_manifest(
        composite,
        compiled_roots=4,
        include_object_constraints=True,
        include_generated_data_quantifier_definitions=True,
        include_generated_data_cardinality_definitions=True,
        include_at_least_data_predicates=True,
    )
    generated = [
        value
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
        if value["generated"]
    ]
    namespace = f":class:{composite.logical_fingerprint.hex}:"
    assert generated
    assert all(namespace in str(value["display"]) for value in generated)
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_recursive_data_exact_cardinality_fillers_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(DataProperty(:d))",
            "Declaration(DataProperty(:e))",
            "Declaration(AnnotationProperty(:note))",
            "SubClassOf(:A DataExactCardinality(1 :d DataIntersectionOf(xsd:string xsd:integer)))",
            'SubClassOf(Annotation(:note "same dependencies") :A '
            "DataExactCardinality(1 :d "
            "DataIntersectionOf(xsd:string xsd:integer)))",
            "SubClassOf(DataExactCardinality(2 :e DataUnionOf(xsd:boolean xsd:decimal)) :B)",
            "SubClassOf(:B DataExactCardinality(0 :d DataIntersectionOf("
            "xsd:string DataUnionOf(xsd:integer xsd:boolean))))",
            "SubClassOf(ObjectComplementOf(DataExactCardinality(0 :e "
            "DataIntersectionOf(xsd:boolean xsd:integer))) :B)",
            "SubClassOf(:A ObjectComplementOf(DataExactCardinality(2 :d "
            "DataUnionOf(xsd:string xsd:decimal))))",
            "DataPropertyRange(:e DataUnionOf(xsd:boolean xsd:decimal))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=7,
        include_generated_data_quantifier_definitions=True,
        include_generated_data_cardinality_definitions=True,
        include_at_least_data_predicates=True,
        include_data_ranges=True,
        include_generated_data_definitions=True,
    )
    assert not any(
        str(value["display"]).startswith("DataExactCardinality:")
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_recursive_data_exact_cardinality_fillers_cover_generated_contexts() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(NamedIndividual(:i))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(DataProperty(:d))",
            "Declaration(DataProperty(:e))",
            "ClassAssertion(DataExactCardinality(1 :d DataUnionOf(xsd:string xsd:integer)) :i)",
            "ObjectPropertyDomain(:p DataExactCardinality(2 :e "
            "DataIntersectionOf(xsd:boolean xsd:decimal)))",
            "DataPropertyDomain(:d DataExactCardinality(3 :e "
            "DataUnionOf(xsd:decimal xsd:integer)))",
            "HasKey(DataExactCardinality(1 :d "
            "DataIntersectionOf(xsd:string xsd:boolean)) (:p) (:e))",
            "DisjointClasses(DataExactCardinality(2 :e DataUnionOf(xsd:string xsd:decimal)) :A)",
            "SubClassOf(ObjectIntersectionOf(:B DataExactCardinality(1 :d "
            "DataIntersectionOf(xsd:boolean xsd:integer))) :A)",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=6,
        include_object_constraints=True,
        include_generated_data_quantifier_definitions=True,
        include_generated_data_cardinality_definitions=True,
        include_at_least_data_predicates=True,
        include_generated_data_definitions=True,
        include_data_domains=True,
        include_keys=True,
    )
    assert not any(
        str(value["display"]).startswith("DataExactCardinality:")
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_recursive_data_exact_fillers_reuse_global_identity() -> None:
    declarations = (
        "Declaration(Class(:A))",
        "Declaration(Class(:B))",
        "Declaration(ObjectProperty(:p))",
        "Declaration(DataProperty(:d))",
    )
    exact = (
        "DataExactCardinality(2 :d "
        "DataIntersectionOf(xsd:string DataUnionOf(xsd:integer xsd:boolean)))"
    )
    left = pyowl_core.load_snapshot(
        functional(
            *declarations,
            f"SubClassOf(:A {exact})",
            f"SubClassOf({exact} :B)",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            *declarations,
            f"ObjectPropertyDomain(:p {exact})",
            f"DisjointClasses({exact} :A)",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    manifest = _native_slices_manifest(
        *_composite_records(composite, (left, right)),
        logical_fingerprint=composite.logical_fingerprint.digest,
    )

    assert manifest == _expected_manifest(
        composite,
        compiled_roots=4,
        include_object_constraints=True,
        include_generated_data_cardinality_definitions=True,
        include_at_least_data_predicates=True,
        include_generated_data_definitions=True,
    )
    class_namespace = f":class:{composite.logical_fingerprint.hex}:"
    data_namespace = f":data:{composite.logical_fingerprint.hex}:"
    assert (
        sum(
            class_namespace in str(value["display"])
            for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
            if value["generated"]
        )
        == 6
    )
    assert (
        sum(
            data_namespace in str(value["display"])
            for value in cast(list[dict[str, object]], manifest["data_range_symbols"])
            if value["generated"]
        )
        == 4
    )
    assert not any(
        str(value["display"]).startswith("DataExactCardinality:")
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_unsupported_data_exact_cardinality_inputs_defer_without_symbol_leaks() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(DataProperty(:d))",
            "SubClassOf(:A DataExactCardinality(4294967295 :d xsd:string))",
            "SubClassOf(:A DataExactCardinality(4294967296 :d xsd:string))",
            "SubClassOf(:A DataExactCardinality(2 :undeclared xsd:string))",
            "SubClassOf(ObjectComplementOf(DataExactCardinality(4294967295 :d xsd:string)) :B)",
            "EquivalentClasses(:A DataExactCardinality(2 :d "
            "DataIntersectionOf(xsd:string xsd:integer)) "
            'DataHasValue(:undeclared "value"))',
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest["compiled_roots"] == 0
    assert manifest["deferred_roots"] == 5
    assert not any(
        value["generated"]
        or str(value["display"]).startswith(
            (
                "DataSomeValuesFrom:",
                "DataAllValuesFrom:",
                "DataMinCardinality:",
                "DataMaxCardinality:",
                "DataExactCardinality:",
            )
        )
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
    )
    assert all(
        predicate["kind"]
        not in {
            PredicateKind.AT_LEAST_DATA.value,
            PredicateKind.DATA_ROLE.value,
            PredicateKind.EQUALITY.value,
            PredicateKind.INEQUALITY.value,
        }
        for predicate in cast(list[dict[str, object]], manifest["predicates"])
    )
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_data_has_value_definitions_match_scalar_singleton_quantifiers() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(DataProperty(:d))",
            "Declaration(DataProperty(:e))",
            "Declaration(AnnotationProperty(:note))",
            'SubClassOf(:A DataHasValue(:d "value"))',
            'SubClassOf(Annotation(:note "same value") :A DataHasValue(:d "value"))',
            'SubClassOf(DataHasValue(:e "other") :B)',
            'EquivalentClasses(:A DataHasValue(:e "value"))',
            'SubClassOf(:B DataSomeValuesFrom(:d DataOneOf("value")))',
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=5,
        include_generated_data_quantifier_definitions=True,
        include_at_least_data_predicates=True,
    )
    singleton_ranges = [
        value
        for value in cast(list[dict[str, object]], manifest["data_range_symbols"])
        if str(value["display"]).startswith("DataOneOf:")
    ]
    assert len(singleton_ranges) == 2
    assert not any(
        str(value["display"]).startswith("DataHasValue:")
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_data_has_value_definitions_cover_complements_and_generated_contexts() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(NamedIndividual(:i))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(DataProperty(:d))",
            "Declaration(DataProperty(:e))",
            'SubClassOf(ObjectComplementOf(DataHasValue(:d "value")) :B)',
            'ClassAssertion(DataHasValue(:d "value") :i)',
            'ObjectPropertyDomain(:p DataHasValue(:e "other"))',
            'DataPropertyDomain(:d ObjectComplementOf(DataHasValue(:e "value")))',
            'HasKey(DataHasValue(:d "other") (:p) (:e))',
            'DisjointClasses(ObjectComplementOf(DataHasValue(:e "other")) :A)',
            'SubClassOf(ObjectIntersectionOf(:B DataHasValue(:d "value")) :A)',
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=7,
        include_object_constraints=True,
        include_generated_data_quantifier_definitions=True,
        include_at_least_data_predicates=True,
        include_data_domains=True,
        include_keys=True,
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_data_has_value_definitions_reuse_global_identity() -> None:
    declarations = (
        "Declaration(Class(:A))",
        "Declaration(Class(:B))",
        "Declaration(ObjectProperty(:p))",
        "Declaration(DataProperty(:d))",
        "Declaration(DataProperty(:e))",
    )
    has_value = 'DataHasValue(:d "value")'
    left = pyowl_core.load_snapshot(
        functional(
            *declarations,
            f"SubClassOf(:A {has_value})",
            'SubClassOf(DataHasValue(:e "other") :B)',
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            *declarations,
            f"ObjectPropertyDomain(:p {has_value})",
            'DisjointClasses(DataHasValue(:e "other") :A)',
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    manifest = _native_slices_manifest(
        *_composite_records(composite, (left, right)),
        logical_fingerprint=composite.logical_fingerprint.digest,
    )

    assert manifest == _expected_manifest(
        composite,
        compiled_roots=4,
        include_object_constraints=True,
        include_generated_data_quantifier_definitions=True,
        include_at_least_data_predicates=True,
    )
    generated = [
        value
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
        if value["generated"]
    ]
    namespace = f":class:{composite.logical_fingerprint.hex}:"
    assert len(generated) == 2
    assert all(namespace in str(value["display"]) for value in generated)
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_partially_unsupported_data_has_value_inputs_defer_without_symbol_leaks() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(DataProperty(:d))",
            "Declaration(DataProperty(owl:bottomDataProperty))",
            'SubClassOf(:A DataHasValue(:undeclared "value"))',
            'SubClassOf(DataHasValue(owl:bottomDataProperty "value") :B)',
            'EquivalentClasses(:A DataHasValue(:d "value") '
            "DataSomeValuesFrom(:d :undeclared xsd:string))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest["compiled_roots"] == 1
    assert manifest["deferred_roots"] == 2
    assert not any(
        value["generated"]
        or str(value["display"]).startswith(
            (
                "DataSomeValuesFrom:",
                "DataAllValuesFrom:",
                "DataOneOf:",
                "DataComplementOf:",
                "DataHasValue:",
            )
        )
        for value in (
            *cast(list[dict[str, object]], manifest["class_expression_symbols"]),
            *cast(list[dict[str, object]], manifest["data_range_symbols"]),
        )
    )
    assert all(
        predicate["kind"]
        not in {
            PredicateKind.AT_LEAST_DATA.value,
            PredicateKind.DATA_ROLE.value,
        }
        for predicate in cast(list[dict[str, object]], manifest["predicates"])
    )
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_partial_object_self_equivalence_defers_without_symbol_leaks() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "EquivalentClasses(:A ObjectHasSelf(:p) ObjectMinCardinality(4294967296 :q :B))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest["compiled_roots"] == 0
    assert manifest["deferred_roots"] == 1
    assert not any(
        value["generated"] or str(value["display"]).startswith("ObjectHasSelf:")
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
    )
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_partial_nested_object_self_root_defers_without_symbol_leaks() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "SubClassOf(:A ObjectIntersectionOf(ObjectHasSelf(:p) "
            "ObjectMinCardinality(4294967296 :q :B)))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest["compiled_roots"] == 0
    assert manifest["deferred_roots"] == 1
    assert not any(
        value["generated"] or str(value["display"]).startswith("ObjectHasSelf:")
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
    )
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_flat_boolean_equivalent_class_definitions_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:C))",
            "Declaration(Class(:D))",
            "Declaration(Class(:E))",
            "Declaration(NamedIndividual(:i))",
            "Declaration(AnnotationProperty(:note))",
            "EquivalentClasses(:A ObjectIntersectionOf(:B :C))",
            'EquivalentClasses(Annotation(:note "same definitions") :A '
            "ObjectIntersectionOf(:B :C))",
            "EquivalentClasses(:D ObjectUnionOf(ObjectComplementOf(:B) :C) "
            "ObjectIntersectionOf(ObjectOneOf(:i) :E))",
            "SubClassOf(:E ObjectIntersectionOf(:B :C))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(snapshot, compiled_roots=4)
    generated = [
        value
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
        if value["generated"]
    ]
    assert len(generated) == 6
    assert {str(value["display"]).split(":")[-2] for value in generated} == {"negative", "positive"}
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_partial_boolean_equivalence_defers_without_generated_symbol_leaks() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:C))",
            "Declaration(ObjectProperty(:p))",
            "EquivalentClasses(:A ObjectIntersectionOf(:B :C) "
            "ObjectMinCardinality(4294967296 :p :B))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest["compiled_roots"] == 0
    assert manifest["deferred_roots"] == 1
    assert not any(
        value["generated"]
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
    )
    assert not any(
        str(value["display"]).startswith("ObjectIntersectionOf:")
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
    )
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_flat_boolean_class_assertion_definitions_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:C))",
            "Declaration(NamedIndividual(:i))",
            "Declaration(AnnotationProperty(:note))",
            "ClassAssertion(ObjectIntersectionOf(:A :B) :i)",
            'ClassAssertion(Annotation(:note "same definition") ObjectIntersectionOf(:A :B) :i)',
            "ClassAssertion(ObjectUnionOf(ObjectComplementOf(:B) ObjectOneOf(:i)) _:anonymous)",
            "SubClassOf(:C ObjectIntersectionOf(:A :B))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(snapshot, compiled_roots=4)
    assert (
        sum(
            bool(value["generated"])
            for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
        )
        == 2
    )
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_flat_boolean_property_constraint_definitions_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:C))",
            "Declaration(Class(:D))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "Declaration(DataProperty(:data))",
            "Declaration(NamedIndividual(:i))",
            "Declaration(AnnotationProperty(:note))",
            "ObjectPropertyDomain(:p ObjectIntersectionOf(:A :B))",
            'ObjectPropertyDomain(Annotation(:note "same definition") :p '
            "ObjectIntersectionOf(:A :B))",
            "ObjectPropertyRange(ObjectInverseOf(:q) ObjectUnionOf(ObjectComplementOf(:B) :C))",
            "DataPropertyDomain(:data ObjectIntersectionOf(ObjectOneOf(:i) :D))",
            "SubClassOf(:C ObjectIntersectionOf(:A :B))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=5,
        include_object_constraints=True,
        include_data_domains=True,
    )
    assert (
        sum(
            bool(value["generated"])
            for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
        )
        == 3
    )
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_flat_boolean_key_definitions_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:C))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "Declaration(DataProperty(:d))",
            "Declaration(DataProperty(:e))",
            "Declaration(NamedIndividual(:i))",
            "Declaration(AnnotationProperty(:note))",
            "HasKey(ObjectIntersectionOf(:A :B) (:p :q) (:d))",
            'HasKey(Annotation(:note "same definition") ObjectIntersectionOf(:A :B) (:p :q) (:d))',
            "HasKey(ObjectUnionOf(ObjectComplementOf(:B) ObjectOneOf(:i)) () (:e))",
            "SubClassOf(ObjectIntersectionOf(:A :B) :C)",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=4,
        include_keys=True,
    )
    assert (
        sum(
            bool(value["generated"])
            for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
        )
        == 2
    )
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_flat_boolean_disjoint_definitions_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:C))",
            "Declaration(Class(:D))",
            "Declaration(NamedIndividual(:i))",
            "Declaration(AnnotationProperty(:note))",
            "DisjointClasses(ObjectIntersectionOf(:A :B) :C)",
            'DisjointClasses(Annotation(:note "same definition") ObjectIntersectionOf(:A :B) :C)',
            "DisjointClasses(:A ObjectUnionOf(ObjectComplementOf(:B) :C) "
            "ObjectIntersectionOf(ObjectOneOf(:i) :D))",
            "SubClassOf(ObjectIntersectionOf(:A :B) :D)",
            "DisjointClasses(ObjectIntersectionOf(:A :D) owl:Nothing)",
            "DisjointClasses(ObjectUnionOf(:A :D) owl:Thing)",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(snapshot, compiled_roots=6)
    assert (
        sum(
            bool(value["generated"])
            for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
        )
        == 5
    )
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_partial_boolean_disjoint_defers_without_generated_symbol_leaks() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:C))",
            "Declaration(ObjectProperty(:p))",
            "DisjointClasses(ObjectIntersectionOf(:A :B) ObjectMinCardinality(4294967296 :p :C))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest["compiled_roots"] == 0
    assert manifest["deferred_roots"] == 1
    assert not any(
        value["generated"]
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
    )
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_generated_class_entity_remapping_matches_scalar_exactly() -> None:
    long_iri = "<urn:test:long:" + ("z" * 240) + ">"
    snapshot = pyowl_core.load_snapshot(
        functional(
            f"Declaration(Class({long_iri}))",
            "Declaration(Class(:B))",
            "Declaration(Class(:C))",
            "Declaration(NamedIndividual(:i))",
            f"ClassAssertion({long_iri} :i)",
            f"SubClassOf({long_iri} ObjectIntersectionOf(:B :C))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(snapshot, compiled_roots=2)
    assert any(
        value["generated"]
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
    )
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_boolean_definitions_use_the_global_logical_namespace() -> None:
    declarations = (
        "Declaration(Class(:A))",
        "Declaration(Class(:B))",
        "Declaration(Class(:C))",
        "Declaration(Class(:D))",
        "Declaration(NamedIndividual(:i))",
    )
    left = pyowl_core.load_snapshot(
        functional(
            *declarations,
            "SubClassOf(:A ObjectIntersectionOf(:B :C))",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            *declarations,
            "EquivalentClasses(ObjectUnionOf(:A :B) :D)",
            "ClassAssertion(ObjectIntersectionOf(:B :C) :i)",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    manifest = _native_slices_manifest(
        *_composite_records(composite, (left, right)),
        logical_fingerprint=composite.logical_fingerprint.digest,
    )

    assert manifest == _expected_manifest(composite, compiled_roots=3)
    namespace = f":class:{composite.logical_fingerprint.hex}:"
    assert all(
        namespace in str(value["display"])
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
        if value["generated"]
    )
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_recursive_class_booleans_reuse_normalized_definitions() -> None:
    declarations = (
        "Declaration(Class(:A))",
        "Declaration(Class(:B))",
        "Declaration(Class(:C))",
        "Declaration(Class(:D))",
        "Declaration(NamedIndividual(:i))",
    )
    left = pyowl_core.load_snapshot(
        functional(
            *declarations,
            "SubClassOf(:A ObjectUnionOf(:B ObjectIntersectionOf(:C :D)))",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            *declarations,
            "ClassAssertion(ObjectComplementOf(ObjectIntersectionOf("
            "ObjectComplementOf(:B) ObjectComplementOf("
            "ObjectIntersectionOf(:C :D)))) :i)",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    manifest = _native_slices_manifest(
        *_composite_records(composite, (left, right)),
        logical_fingerprint=composite.logical_fingerprint.digest,
    )

    assert manifest == _expected_manifest(composite, compiled_roots=2)
    generated = [
        value
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
        if value["generated"]
    ]
    assert len(generated) == 2
    namespace = f":class:{composite.logical_fingerprint.hex}:positive:"
    assert all(namespace in str(value["display"]) for value in generated)
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_boolean_property_constraints_match_scalar_exactly() -> None:
    declarations = (
        "Declaration(Class(:A))",
        "Declaration(Class(:B))",
        "Declaration(Class(:C))",
        "Declaration(Class(:D))",
        "Declaration(ObjectProperty(:p))",
        "Declaration(DataProperty(:data))",
    )
    left = pyowl_core.load_snapshot(
        functional(
            *declarations,
            "ObjectPropertyDomain(:p ObjectIntersectionOf(:A :B))",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            *declarations,
            "DataPropertyDomain(:data ObjectUnionOf(:B :C))",
            "HasKey(ObjectIntersectionOf(:A :B) (:p) (:data))",
            "DisjointClasses(ObjectUnionOf(:A :C) :B)",
            "DisjointUnion(:D :A :C)",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    manifest = _native_slices_manifest(
        *_composite_records(composite, (left, right)),
        logical_fingerprint=composite.logical_fingerprint.digest,
    )

    assert manifest == _expected_manifest(
        composite,
        compiled_roots=5,
        include_object_constraints=True,
        include_data_domains=True,
        include_keys=True,
    )
    namespace = f":class:{composite.logical_fingerprint.hex}:"
    assert all(
        namespace in str(value["display"])
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
        if value["generated"]
    )
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_builtin_restrictions_and_cardinalities_reduce_exactly() -> None:
    string_datatype = "<http://www.w3.org/2001/XMLSchema#string>"
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(DataProperty(:d))",
            f"Declaration(Datatype({string_datatype}))",
            "SubClassOf(ObjectSomeValuesFrom(:p owl:Nothing) :B)",
            "SubClassOf(:A ObjectAllValuesFrom(:p owl:Thing))",
            "SubClassOf(ObjectMinCardinality(0 :p :A) :B)",
            "SubClassOf(ObjectMinCardinality(2 :p owl:Nothing) :B)",
            "SubClassOf(:A ObjectMaxCardinality(2 :p owl:Nothing))",
            "SubClassOf(ObjectExactCardinality(0 :p owl:Nothing) :B)",
            "SubClassOf(ObjectExactCardinality(2 :p owl:Nothing) :B)",
            "SubClassOf(DataSomeValuesFrom(:d DataComplementOf(rdfs:Literal)) :B)",
            "SubClassOf(:A DataAllValuesFrom(:d rdfs:Literal))",
            f"SubClassOf(DataMinCardinality(0 :d {string_datatype}) :B)",
            "SubClassOf(DataMinCardinality(2 :d DataComplementOf(rdfs:Literal)) :B)",
            "SubClassOf(:A DataMaxCardinality(2 :d DataComplementOf(rdfs:Literal)))",
            "SubClassOf(DataExactCardinality(0 :d DataComplementOf(rdfs:Literal)) :B)",
            "SubClassOf(DataExactCardinality(2 :d DataComplementOf(rdfs:Literal)) :B)",
            "SubClassOf(ObjectComplementOf(ObjectSomeValuesFrom(:p owl:Nothing)) :B)",
            "SubClassOf(ObjectComplementOf(DataSomeValuesFrom("
            ":d DataComplementOf(rdfs:Literal))) :B)",
            "SubClassOf(ObjectIntersectionOf(ObjectMinCardinality(0 :p :A) :A) :B)",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(snapshot, compiled_roots=17)
    class_symbols = cast(list[dict[str, object]], manifest["class_expression_symbols"])
    assert not any(
        str(value["display"]).startswith(
            (
                "ObjectSomeValuesFrom:",
                "ObjectAllValuesFrom:",
                "ObjectHasValue:",
                "ObjectMinCardinality:",
                "ObjectMaxCardinality:",
                "ObjectExactCardinality:",
                "DataSomeValuesFrom:",
                "DataAllValuesFrom:",
                "DataMinCardinality:",
                "DataMaxCardinality:",
                "DataExactCardinality:",
            )
        )
        for value in class_symbols
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


@pytest.mark.parametrize("datatype_iri", sorted(SUPPORTED_DATATYPES))
def test_implicit_builtin_datatype_minimum_zero_reduces_exactly(
    datatype_iri: str,
) -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(DataProperty(:d))",
            f"SubClassOf(DataMinCardinality(0 :d <{datatype_iri}>) :B)",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(snapshot, compiled_roots=1)
    assert [
        value["display"] for value in cast(list[dict[str, object]], manifest["data_range_symbols"])
    ] == ["datatype:http://www.w3.org/2000/01/rdf-schema#Literal"]
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_implicit_builtin_datatype_restriction_reductions_match_scalar() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(DataProperty(:d))",
            "SubClassOf(:A DataSomeValuesFrom(:d "
            "DataIntersectionOf(xsd:string DataComplementOf(rdfs:Literal))))",
            "SubClassOf(DataAllValuesFrom(:d DataUnionOf(xsd:string rdfs:Literal)) :B)",
            "SubClassOf(:A DataSomeValuesFrom(owl:bottomDataProperty xsd:string))",
            "SubClassOf(DataAllValuesFrom(owl:bottomDataProperty xsd:string) :B)",
            "SubClassOf(DataMinCardinality(0 :d xsd:string) :B)",
            "SubClassOf(DataMinCardinality(2 owl:bottomDataProperty xsd:string) :B)",
            "SubClassOf(:A DataMaxCardinality(2 owl:bottomDataProperty xsd:string))",
            "SubClassOf(DataExactCardinality(0 owl:bottomDataProperty xsd:string) :B)",
            "SubClassOf(:A DataExactCardinality(2 owl:bottomDataProperty xsd:string))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(snapshot, compiled_roots=9)
    assert [
        value["display"] for value in cast(list[dict[str, object]], manifest["data_range_symbols"])
    ] == ["datatype:http://www.w3.org/2000/01/rdf-schema#Literal"]
    assert not any(
        value["generated"]
        or str(value["display"]).startswith(
            (
                "DataSomeValuesFrom:",
                "DataAllValuesFrom:",
                "DataMinCardinality:",
                "DataMaxCardinality:",
                "DataExactCardinality:",
            )
        )
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_discarded_data_range_values_reduce_without_symbols() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(DataProperty(:d))",
            'SubClassOf(:A DataSomeValuesFrom(owl:bottomDataProperty DataOneOf("discarded")))',
            'SubClassOf(DataAllValuesFrom(owl:bottomDataProperty DataOneOf("discarded")) :B)',
            "SubClassOf(:A DataSomeValuesFrom(owl:bottomDataProperty "
            'DatatypeRestriction(xsd:string xsd:minLength "1"^^xsd:integer)))',
            "SubClassOf(DataAllValuesFrom(owl:bottomDataProperty "
            'DatatypeRestriction(xsd:string xsd:minLength "1"^^xsd:integer)) :B)',
            'SubClassOf(DataMinCardinality(0 :d DataOneOf("discarded")) :B)',
            "SubClassOf(:A ObjectComplementOf(DataMinCardinality(0 :d "
            'DatatypeRestriction(xsd:string xsd:minLength "1"^^xsd:integer))))',
            'SubClassOf(:A DataMaxCardinality(2 owl:bottomDataProperty DataOneOf("discarded")))',
            "SubClassOf(DataExactCardinality(2 owl:bottomDataProperty "
            'DatatypeRestriction(xsd:string xsd:minLength "1"^^xsd:integer)) :B)',
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(snapshot, compiled_roots=8)
    assert manifest["source_literal_symbols"] == []
    assert manifest["data_value_symbols"] == []
    assert [
        value["display"] for value in cast(list[dict[str, object]], manifest["data_range_symbols"])
    ] == ["datatype:http://www.w3.org/2000/01/rdf-schema#Literal"]
    assert not any(
        value["generated"]
        or str(value["display"]).startswith(
            (
                "DataSomeValuesFrom:",
                "DataAllValuesFrom:",
                "DataMinCardinality:",
                "DataMaxCardinality:",
                "DataExactCardinality:",
            )
        )
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_discarded_data_range_value_keeps_shared_live_literal() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            'SubClassOf(:A DataSomeValuesFrom(owl:bottomDataProperty DataOneOf("shared")))',
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:B))",
            "Declaration(DataProperty(:d))",
            'SubClassOf(:B DataHasValue(:d "shared"))',
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))
    records = _composite_records(composite, (left, right))

    forward = _native_slices_manifest(
        *records,
        logical_fingerprint=composite.logical_fingerprint.digest,
    )
    reverse = _native_slices_manifest(
        *reversed(records),
        logical_fingerprint=composite.logical_fingerprint.digest,
    )

    assert (
        forward
        == reverse
        == _expected_manifest(
            composite,
            compiled_roots=2,
            include_generated_data_quantifier_definitions=True,
            include_at_least_data_predicates=True,
        )
    )
    assert len(cast(list[object], forward["source_literal_symbols"])) == 1
    assert len(cast(list[object], forward["data_value_symbols"])) == 1
    assert forward["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_discarded_data_boolean_operands_prune_normalized_symbols() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(DataProperty(:d))",
            "Declaration(Datatype(:T))",
            "Declaration(Datatype(:U))",
            "DatatypeDefinition(:T DataIntersectionOf("
            'DataComplementOf(rdfs:Literal) DataOneOf("discarded-one")))',
            "DatatypeDefinition(:U DataUnionOf(rdfs:Literal "
            "DatatypeRestriction(xsd:string "
            'xsd:minLength "1"^^xsd:integer)))',
            "SubClassOf(:A DataSomeValuesFrom(:d "
            "DataUnionOf(rdfs:Literal DataOneOf("
            '"discarded-two"))))',
            "SubClassOf(:A DataMaxCardinality(2 :d DataIntersectionOf(rdfs:Literal xsd:boolean)))",
            "SubClassOf(:A DataExactCardinality(2 :d "
            "DataIntersectionOf(rdfs:Literal xsd:boolean)))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=5,
        include_generated_data_quantifier_definitions=True,
        include_generated_data_cardinality_definitions=True,
        include_at_least_data_predicates=True,
        include_datatype_definitions=True,
    )
    assert manifest["source_literal_symbols"] == []
    assert manifest["data_value_symbols"] == []
    assert not any(
        value["display"]
        in {
            "datatype:http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral",
            "datatype:http://www.w3.org/2001/XMLSchema#integer",
            "datatype:http://www.w3.org/2001/XMLSchema#string",
        }
        for value in cast(list[dict[str, object]], manifest["data_range_symbols"])
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_discarded_data_boolean_keeps_shared_live_literal() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(Datatype(:T))",
            'DatatypeDefinition(:T DataUnionOf(rdfs:Literal DataOneOf("shared")))',
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:B))",
            "Declaration(DataProperty(:d))",
            'SubClassOf(:B DataHasValue(:d "shared"))',
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))
    records = _composite_records(composite, (left, right))

    forward = _native_slices_manifest(
        *records,
        logical_fingerprint=composite.logical_fingerprint.digest,
    )
    reverse = _native_slices_manifest(
        *reversed(records),
        logical_fingerprint=composite.logical_fingerprint.digest,
    )

    assert (
        forward
        == reverse
        == _expected_manifest(
            composite,
            compiled_roots=2,
            include_generated_data_quantifier_definitions=True,
            include_at_least_data_predicates=True,
            include_datatype_definitions=True,
        )
    )
    assert len(cast(list[object], forward["source_literal_symbols"])) == 1
    assert len(cast(list[object], forward["data_value_symbols"])) == 1
    assert forward["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_complemented_reduced_data_booleans_match_scalar_roots() -> None:
    retained_one_of = 'DataComplementOf(DataIntersectionOf(rdfs:Literal DataOneOf("retained")))'
    retained_restriction = (
        "DataComplementOf(DataUnionOf(DataComplementOf(rdfs:Literal) "
        "DatatypeRestriction(xsd:string "
        'xsd:minLength "1"^^xsd:integer)))'
    )
    discarded_one_of = 'DataComplementOf(DataUnionOf(rdfs:Literal DataOneOf("discarded")))'
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:d))",
            "Declaration(DataProperty(:e))",
            "Declaration(DataProperty(:f))",
            "Declaration(Datatype(:T))",
            "Declaration(Datatype(:U))",
            "Declaration(Datatype(:V))",
            f"DataPropertyRange(:d {retained_one_of})",
            f"DataPropertyRange(:e {retained_restriction})",
            f"DataPropertyRange(:f {discarded_one_of})",
            f"DatatypeDefinition(:T {retained_one_of})",
            f"DatatypeDefinition(:U {retained_restriction})",
            f"DatatypeDefinition(:V {discarded_one_of})",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=6,
        include_data_ranges=True,
        include_datatype_definitions=True,
    )
    assert not any(
        str(value["display"]).startswith(("DataIntersectionOf:", "DataUnionOf:"))
        for value in cast(list[dict[str, object]], manifest["data_range_symbols"])
    )
    assert all(
        "discarded" not in str(value["display"])
        for value in cast(list[dict[str, object]], manifest["source_literal_symbols"])
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_complemented_reduced_atomic_class_booleans_match_scalar_contexts() -> None:
    expressions = (
        "ObjectComplementOf(ObjectIntersectionOf(owl:Thing ObjectOneOf(:i)))",
        "ObjectComplementOf(ObjectUnionOf(owl:Nothing :A))",
    )
    contexts = (
        "SubClassOf({} :Z)",
        "SubClassOf(:Z {})",
        "EquivalentClasses(:Z {})",
        "DisjointClasses(:Z {})",
        "ClassAssertion({} :i)",
        "ObjectPropertyDomain(:p {})",
        "ObjectPropertyRange(:p {})",
        "DataPropertyDomain(:d {})",
        "HasKey({} (:p) (:d))",
    )
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:Z))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(DataProperty(:d))",
            "Declaration(NamedIndividual(:i))",
            *(context.format(expression) for expression in expressions for context in contexts),
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=18,
        include_object_constraints=True,
        include_data_domains=True,
        include_keys=True,
    )
    assert not any(
        str(value["display"]).startswith(("ObjectIntersectionOf:", "ObjectUnionOf:"))
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


@pytest.mark.parametrize(
    ("mode", "expression"),
    (
        (
            "union/direct",
            "ObjectComplementOf(ObjectUnionOf(owl:Thing ObjectHasSelf(:discarded)))",
        ),
        (
            "union/complemented-multi-live",
            "ObjectComplementOf(ObjectUnionOf("
            ":A :B owl:Thing ObjectComplementOf(ObjectHasSelf(:discarded))))",
        ),
        (
            "union/nested",
            "ObjectComplementOf(ObjectUnionOf("
            "owl:Thing ObjectIntersectionOf(:A ObjectHasSelf(:discarded))))",
        ),
        (
            "intersection/direct",
            "ObjectComplementOf(ObjectIntersectionOf(owl:Nothing ObjectHasSelf(:discarded)))",
        ),
        (
            "intersection/complemented-multi-live",
            "ObjectComplementOf(ObjectIntersectionOf("
            ":A :B owl:Nothing ObjectComplementOf(ObjectHasSelf(:discarded))))",
        ),
        (
            "intersection/nested",
            "ObjectComplementOf(ObjectIntersectionOf("
            "owl:Nothing ObjectUnionOf(:A ObjectHasSelf(:discarded))))",
        ),
    ),
)
def test_absorbing_class_booleans_discard_object_self_in_scalar_contexts(
    mode: str,
    expression: str,
) -> None:
    contexts = (
        "SubClassOf({} :Z)",
        "SubClassOf(:Z {})",
        "EquivalentClasses(:Z {})",
        "DisjointClasses(:Z {})",
        "ClassAssertion({} :i)",
        "ObjectPropertyDomain(:p {})",
        "ObjectPropertyRange(:p {})",
        "DataPropertyDomain(:d {})",
        "HasKey({} (:p) (:d))",
    )
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:Z))",
            "Declaration(ObjectProperty(:discarded))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(DataProperty(:d))",
            "Declaration(NamedIndividual(:i))",
            *(context.format(expression) for context in contexts),
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=9,
        include_object_constraints=True,
        include_generated_object_self_definitions=True,
        include_data_domains=True,
        include_keys=True,
    ), mode
    assert not any(
        str(value["display"]).startswith("ObjectHasSelf:")
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


@pytest.mark.parametrize(
    ("mode", "expression"),
    (
        (
            "union/direct",
            "ObjectComplementOf(ObjectUnionOf(owl:Thing ObjectHasValue(:discarded :dead)))",
        ),
        (
            "union/complemented-multi-live",
            "ObjectComplementOf(ObjectUnionOf("
            ":A :B owl:Thing "
            "ObjectComplementOf(ObjectHasValue(:discarded :dead))))",
        ),
        (
            "union/nested",
            "ObjectComplementOf(ObjectUnionOf("
            "owl:Thing ObjectIntersectionOf("
            ":A ObjectHasValue(:discarded :dead))))",
        ),
        (
            "intersection/direct",
            "ObjectComplementOf(ObjectIntersectionOf("
            "owl:Nothing ObjectHasValue(:discarded :dead)))",
        ),
        (
            "intersection/complemented-multi-live",
            "ObjectComplementOf(ObjectIntersectionOf("
            ":A :B owl:Nothing "
            "ObjectComplementOf(ObjectHasValue(:discarded :dead))))",
        ),
        (
            "intersection/nested",
            "ObjectComplementOf(ObjectIntersectionOf("
            "owl:Nothing ObjectUnionOf("
            ":A ObjectHasValue(:discarded :dead))))",
        ),
    ),
)
def test_absorbing_class_booleans_discard_object_values_in_scalar_contexts(
    mode: str,
    expression: str,
) -> None:
    contexts = (
        "SubClassOf({} :Z)",
        "SubClassOf(:Z {})",
        "EquivalentClasses(:Z {})",
        "DisjointClasses(:Z {})",
        "ClassAssertion({} :i)",
        "ObjectPropertyDomain(:p {})",
        "ObjectPropertyRange(:p {})",
        "DataPropertyDomain(:d {})",
        "HasKey({} (:p) (:d))",
    )
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:Z))",
            "Declaration(ObjectProperty(:discarded))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(DataProperty(:d))",
            "Declaration(NamedIndividual(:i))",
            *(context.format(expression) for context in contexts),
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=9,
        include_object_constraints=True,
        include_generated_object_quantifier_definitions=True,
        include_at_least_object_predicates=True,
        include_data_domains=True,
        include_keys=True,
    ), mode
    assert not any(
        str(value["display"]).startswith(
            ("ObjectOneOf:", "ObjectSomeValuesFrom:", "ObjectAllValuesFrom:")
        )
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
    )
    assert all(
        "urn:test:named#dead" not in str(value["display"])
        for value in cast(list[dict[str, object]], manifest["individual_symbols"])
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


@pytest.mark.parametrize(
    ("constructor", "label"),
    (
        ("ObjectSomeValuesFrom", "some"),
        ("ObjectAllValuesFrom", "all"),
    ),
)
def test_absorbing_class_booleans_discard_object_quantifiers_in_scalar_contexts(
    constructor: str,
    label: str,
) -> None:
    direct = f"{constructor}(:discarded :A)"
    complemented = f"ObjectComplementOf({direct})"
    expressions = (
        f"ObjectComplementOf(ObjectUnionOf(owl:Thing {direct}))",
        f"ObjectComplementOf(ObjectUnionOf(:A :B owl:Thing {complemented}))",
        f"ObjectComplementOf(ObjectUnionOf(owl:Thing ObjectIntersectionOf(:A {direct})))",
        f"ObjectComplementOf(ObjectIntersectionOf(owl:Nothing {direct}))",
        f"ObjectComplementOf(ObjectIntersectionOf(:A :B owl:Nothing {complemented}))",
        f"ObjectComplementOf(ObjectIntersectionOf(owl:Nothing ObjectUnionOf(:A {direct})))",
    )
    contexts = (
        "SubClassOf({} :Z)",
        "SubClassOf(:Z {})",
        "EquivalentClasses(:Z {})",
        "DisjointClasses(:Z {})",
        "ClassAssertion({} :i)",
        "ObjectPropertyDomain(:p {})",
        "ObjectPropertyRange(:p {})",
        "DataPropertyDomain(:d {})",
        "HasKey({} (:p) (:d))",
    )
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:Z))",
            "Declaration(ObjectProperty(:discarded))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(DataProperty(:d))",
            "Declaration(NamedIndividual(:i))",
            *(context.format(expression) for expression in expressions for context in contexts),
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=54,
        include_object_constraints=True,
        include_generated_object_quantifier_definitions=True,
        include_at_least_object_predicates=True,
        include_data_domains=True,
        include_keys=True,
    ), label
    assert not any(
        str(value["display"]).startswith(("ObjectSomeValuesFrom:", "ObjectAllValuesFrom:"))
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
    )
    assert all(
        predicate["kind"] != PredicateKind.AT_LEAST_OBJECT.value
        for predicate in cast(list[dict[str, object]], manifest["predicates"])
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


@pytest.mark.parametrize(
    ("constructor", "label"),
    (
        ("ObjectMinCardinality", "minimum"),
        ("ObjectMaxCardinality", "maximum"),
        ("ObjectExactCardinality", "exact"),
    ),
)
def test_absorbing_class_booleans_discard_object_cardinalities_in_scalar_contexts(
    constructor: str,
    label: str,
) -> None:
    direct = f"{constructor}(2 :discarded :A)"
    complemented = f"ObjectComplementOf({direct})"
    expressions = (
        f"ObjectComplementOf(ObjectUnionOf(owl:Thing {direct}))",
        f"ObjectComplementOf(ObjectUnionOf(:A :B owl:Thing {complemented}))",
        f"ObjectComplementOf(ObjectUnionOf(owl:Thing ObjectIntersectionOf(:A {direct})))",
        f"ObjectComplementOf(ObjectIntersectionOf(owl:Nothing {direct}))",
        f"ObjectComplementOf(ObjectIntersectionOf(:A :B owl:Nothing {complemented}))",
        f"ObjectComplementOf(ObjectIntersectionOf(owl:Nothing ObjectUnionOf(:A {direct})))",
    )
    contexts = (
        "SubClassOf({} :Z)",
        "SubClassOf(:Z {})",
        "EquivalentClasses(:Z {})",
        "DisjointClasses(:Z {})",
        "ClassAssertion({} :i)",
        "ObjectPropertyDomain(:p {})",
        "ObjectPropertyRange(:p {})",
        "DataPropertyDomain(:d {})",
        "HasKey({} (:p) (:d))",
    )
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:Z))",
            "Declaration(ObjectProperty(:discarded))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(DataProperty(:d))",
            "Declaration(NamedIndividual(:i))",
            *(context.format(expression) for expression in expressions for context in contexts),
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=54,
        include_object_constraints=True,
        include_generated_object_quantifier_definitions=True,
        include_generated_object_cardinality_definitions=True,
        include_at_least_object_predicates=True,
        include_annotated_equality_predicates=True,
        include_data_domains=True,
        include_keys=True,
    ), label
    assert not any(
        str(value["display"]).startswith(
            (
                "ObjectMinCardinality:",
                "ObjectMaxCardinality:",
                "ObjectSomeValuesFrom:",
                "ObjectAllValuesFrom:",
            )
        )
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
    )
    assert all(
        predicate["kind"]
        not in {
            PredicateKind.AT_LEAST_OBJECT.value,
            PredicateKind.ANNOTATED_EQUALITY.value,
        }
        for predicate in cast(list[dict[str, object]], manifest["predicates"])
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


@pytest.mark.parametrize(
    ("constructor", "label"),
    (
        ("DataSomeValuesFrom", "some"),
        ("DataAllValuesFrom", "all"),
    ),
)
def test_absorbing_class_booleans_discard_data_quantifiers_in_scalar_contexts(
    constructor: str,
    label: str,
) -> None:
    direct = f"{constructor}(:discarded xsd:string)"
    complemented = f"ObjectComplementOf({direct})"
    expressions = (
        f"ObjectComplementOf(ObjectUnionOf(owl:Thing {direct}))",
        f"ObjectComplementOf(ObjectUnionOf(:A :B owl:Thing {complemented}))",
        f"ObjectComplementOf(ObjectUnionOf(owl:Thing ObjectIntersectionOf(:A {direct})))",
        f"ObjectComplementOf(ObjectIntersectionOf(owl:Nothing {direct}))",
        f"ObjectComplementOf(ObjectIntersectionOf(:A :B owl:Nothing {complemented}))",
        f"ObjectComplementOf(ObjectIntersectionOf(owl:Nothing ObjectUnionOf(:A {direct})))",
    )
    contexts = (
        "SubClassOf({} :Z)",
        "SubClassOf(:Z {})",
        "EquivalentClasses(:Z {})",
        "DisjointClasses(:Z {})",
        "ClassAssertion({} :i)",
        "ObjectPropertyDomain(:p {})",
        "ObjectPropertyRange(:p {})",
        "DataPropertyDomain(:d {})",
        "HasKey({} (:p) (:d))",
    )
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:Z))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(DataProperty(:discarded))",
            "Declaration(DataProperty(:d))",
            "Declaration(NamedIndividual(:i))",
            *(context.format(expression) for expression in expressions for context in contexts),
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=54,
        include_object_constraints=True,
        include_generated_data_quantifier_definitions=True,
        include_at_least_data_predicates=True,
        include_data_domains=True,
        include_keys=True,
    ), label
    assert not any(
        str(value["display"]).startswith(("DataSomeValuesFrom:", "DataAllValuesFrom:"))
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
    )
    assert all(
        predicate["kind"] != PredicateKind.AT_LEAST_DATA.value
        for predicate in cast(list[dict[str, object]], manifest["predicates"])
    )
    assert [
        value["display"] for value in cast(list[dict[str, object]], manifest["data_range_symbols"])
    ] == ["datatype:http://www.w3.org/2000/01/rdf-schema#Literal"]
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_absorbing_class_booleans_discard_data_values_in_scalar_contexts() -> None:
    direct = 'DataHasValue(:discarded "discarded")'
    complemented = f"ObjectComplementOf({direct})"
    expressions = (
        f"ObjectComplementOf(ObjectUnionOf(owl:Thing {direct}))",
        f"ObjectComplementOf(ObjectUnionOf(:A :B owl:Thing {complemented}))",
        f"ObjectComplementOf(ObjectUnionOf(owl:Thing ObjectIntersectionOf(:A {direct})))",
        f"ObjectComplementOf(ObjectIntersectionOf(owl:Nothing {direct}))",
        f"ObjectComplementOf(ObjectIntersectionOf(:A :B owl:Nothing {complemented}))",
        f"ObjectComplementOf(ObjectIntersectionOf(owl:Nothing ObjectUnionOf(:A {direct})))",
    )
    contexts = (
        "SubClassOf({} :Z)",
        "SubClassOf(:Z {})",
        "EquivalentClasses(:Z {})",
        "DisjointClasses(:Z {})",
        "ClassAssertion({} :i)",
        "ObjectPropertyDomain(:p {})",
        "ObjectPropertyRange(:p {})",
        "DataPropertyDomain(:d {})",
        "HasKey({} (:p) (:d))",
    )
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:Z))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(DataProperty(:discarded))",
            "Declaration(DataProperty(:d))",
            "Declaration(NamedIndividual(:i))",
            *(context.format(expression) for expression in expressions for context in contexts),
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=54,
        include_object_constraints=True,
        include_generated_data_quantifier_definitions=True,
        include_at_least_data_predicates=True,
        include_data_domains=True,
        include_keys=True,
    )
    assert not any(
        str(value["display"]).startswith(
            ("DataHasValue:", "DataSomeValuesFrom:", "DataAllValuesFrom:")
        )
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
    )
    assert all(
        predicate["kind"] != PredicateKind.AT_LEAST_DATA.value
        for predicate in cast(list[dict[str, object]], manifest["predicates"])
    )
    assert manifest["source_literal_symbols"] == []
    assert manifest["data_value_symbols"] == []
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


@pytest.mark.parametrize(
    ("constructor", "label"),
    (
        ("DataMinCardinality", "minimum"),
        ("DataMaxCardinality", "maximum"),
        ("DataExactCardinality", "exact"),
    ),
)
def test_absorbing_class_booleans_discard_data_cardinalities_in_scalar_contexts(
    constructor: str,
    label: str,
) -> None:
    direct = f"{constructor}(2 :discarded xsd:string)"
    complemented = f"ObjectComplementOf({direct})"
    expressions = (
        f"ObjectComplementOf(ObjectUnionOf(owl:Thing {direct}))",
        f"ObjectComplementOf(ObjectUnionOf(:A :B owl:Thing {complemented}))",
        f"ObjectComplementOf(ObjectUnionOf(owl:Thing ObjectIntersectionOf(:A {direct})))",
        f"ObjectComplementOf(ObjectIntersectionOf(owl:Nothing {direct}))",
        f"ObjectComplementOf(ObjectIntersectionOf(:A :B owl:Nothing {complemented}))",
        f"ObjectComplementOf(ObjectIntersectionOf(owl:Nothing ObjectUnionOf(:A {direct})))",
    )
    contexts = (
        "SubClassOf({} :Z)",
        "SubClassOf(:Z {})",
        "EquivalentClasses(:Z {})",
        "DisjointClasses(:Z {})",
        "ClassAssertion({} :i)",
        "ObjectPropertyDomain(:p {})",
        "ObjectPropertyRange(:p {})",
        "DataPropertyDomain(:d {})",
        "HasKey({} (:p) (:d))",
    )
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:Z))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(DataProperty(:discarded))",
            "Declaration(DataProperty(:d))",
            "Declaration(NamedIndividual(:i))",
            *(context.format(expression) for expression in expressions for context in contexts),
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=54,
        include_object_constraints=True,
        include_generated_data_quantifier_definitions=True,
        include_generated_data_cardinality_definitions=True,
        include_at_least_data_predicates=True,
        include_data_domains=True,
        include_keys=True,
    ), label
    assert not any(
        str(value["display"]).startswith(
            (
                "DataMinCardinality:",
                "DataMaxCardinality:",
                "DataSomeValuesFrom:",
                "DataAllValuesFrom:",
            )
        )
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
    )
    assert all(
        predicate["kind"] != PredicateKind.AT_LEAST_DATA.value
        for predicate in cast(list[dict[str, object]], manifest["predicates"])
    )
    assert [
        value["display"] for value in cast(list[dict[str, object]], manifest["data_range_symbols"])
    ] == ["datatype:http://www.w3.org/2000/01/rdf-schema#Literal"]
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_declared_bottom_property_restrictions_reduce_exactly() -> None:
    string_datatype = "<http://www.w3.org/2001/XMLSchema#string>"
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(ObjectProperty(owl:bottomObjectProperty))",
            "Declaration(DataProperty(owl:bottomDataProperty))",
            f"Declaration(Datatype({string_datatype}))",
            "Declaration(NamedIndividual(:a))",
            "SubClassOf(ObjectSomeValuesFrom(owl:bottomObjectProperty :A) :B)",
            "SubClassOf(:A ObjectAllValuesFrom(owl:bottomObjectProperty :B))",
            "SubClassOf(ObjectHasValue(owl:bottomObjectProperty :a) :B)",
            f"SubClassOf(DataSomeValuesFrom(owl:bottomDataProperty {string_datatype}) :B)",
            f"SubClassOf(:A DataAllValuesFrom(owl:bottomDataProperty {string_datatype}))",
            f"SubClassOf(DataMinCardinality(2 owl:bottomDataProperty {string_datatype}) :B)",
            f"SubClassOf(:A DataMaxCardinality(2 owl:bottomDataProperty {string_datatype}))",
            f"SubClassOf(DataExactCardinality(0 owl:bottomDataProperty {string_datatype}) :B)",
            f"SubClassOf(DataExactCardinality(2 owl:bottomDataProperty {string_datatype}) :B)",
            'SubClassOf(DataHasValue(owl:bottomDataProperty "pruned") :B)',
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(snapshot, compiled_roots=10)
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_implicit_builtin_property_restrictions_reduce_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(NamedIndividual(:a))",
            "SubClassOf(ObjectSomeValuesFrom(owl:bottomObjectProperty :A) :B)",
            "SubClassOf(:A ObjectAllValuesFrom(owl:bottomObjectProperty :B))",
            "SubClassOf(ObjectHasValue(owl:bottomObjectProperty :a) :B)",
            "SubClassOf(ObjectSomeValuesFrom(owl:topObjectProperty owl:Nothing) :B)",
            "SubClassOf(:A ObjectAllValuesFrom(owl:topObjectProperty owl:Thing))",
            "SubClassOf(DataSomeValuesFrom(owl:bottomDataProperty rdfs:Literal) :B)",
            "SubClassOf(:A DataAllValuesFrom(owl:bottomDataProperty rdfs:Literal))",
            "SubClassOf(DataMinCardinality(0 owl:bottomDataProperty rdfs:Literal) :B)",
            "SubClassOf(DataMinCardinality(2 owl:bottomDataProperty rdfs:Literal) :B)",
            "SubClassOf(:A DataMaxCardinality(2 owl:bottomDataProperty rdfs:Literal))",
            "SubClassOf(DataExactCardinality(0 owl:bottomDataProperty rdfs:Literal) :B)",
            "SubClassOf(DataExactCardinality(2 owl:bottomDataProperty rdfs:Literal) :B)",
            'SubClassOf(DataHasValue(owl:bottomDataProperty "pruned") :B)',
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(snapshot, compiled_roots=13)
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_nonreduced_implicit_builtin_properties_remain_retained() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(NamedIndividual(:a))",
            "Declaration(NamedIndividual(:b))",
            "SubClassOf(:A ObjectSomeValuesFrom(owl:topObjectProperty :B))",
            "ObjectPropertyAssertion(owl:bottomObjectProperty :a :b)",
            'DataPropertyAssertion(owl:bottomDataProperty :a "value")',
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=3,
        include_generated_object_quantifier_definitions=True,
        include_at_least_object_predicates=True,
        include_object_assertions=True,
        include_data_assertions=True,
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_implicit_builtin_property_reductions_remap_composite_slices_exactly() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "SubClassOf(ObjectSomeValuesFrom(owl:bottomObjectProperty :A) :B)",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:C))",
            "Declaration(Class(:D))",
            "SubClassOf(:C ObjectSomeValuesFrom(owl:topObjectProperty :D))",
            "SubClassOf(DataMinCardinality(0 owl:bottomDataProperty rdfs:Literal) :D)",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))
    records = _composite_records(composite, (left, right))

    forward = _native_slices_manifest(
        *records,
        logical_fingerprint=composite.logical_fingerprint.digest,
    )
    reverse = _native_slices_manifest(
        *reversed(records),
        logical_fingerprint=composite.logical_fingerprint.digest,
    )

    assert (
        forward
        == reverse
        == _expected_manifest(
            composite,
            compiled_roots=3,
            include_generated_object_quantifier_definitions=True,
            include_at_least_object_predicates=True,
        )
    )
    assert forward["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_bottom_data_has_value_reduces_without_literal_symbols() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(AnnotationProperty(:note))",
            'SubClassOf(Annotation(:note "pruned") '
            'DataHasValue(owl:bottomDataProperty "pruned") :B)',
            'SubClassOf(:A ObjectComplementOf(DataHasValue(owl:bottomDataProperty "pruned")))',
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(snapshot, compiled_roots=2)
    assert manifest["source_literal_symbols"] == []
    assert manifest["data_value_symbols"] == []
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_bottom_data_has_value_keeps_a_shared_live_literal() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(DataProperty(:d))",
            'SubClassOf(DataHasValue(owl:bottomDataProperty "shared") :B)',
            'SubClassOf(:A DataHasValue(:d "shared"))',
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=2,
        include_generated_data_quantifier_definitions=True,
        include_at_least_data_predicates=True,
    )
    assert len(cast(list[object], manifest["source_literal_symbols"])) == 1
    assert len(cast(list[object], manifest["data_value_symbols"])) == 1
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_bottom_data_has_value_reduction_remaps_composite_literals_exactly() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            'SubClassOf(DataHasValue(owl:bottomDataProperty "shared") :B)',
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:C))",
            "Declaration(Class(:D))",
            "Declaration(DataProperty(:d))",
            'SubClassOf(:C DataHasValue(:d "shared"))',
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))
    records = _composite_records(composite, (left, right))

    forward = _native_slices_manifest(
        *records,
        logical_fingerprint=composite.logical_fingerprint.digest,
    )
    reverse = _native_slices_manifest(
        *reversed(records),
        logical_fingerprint=composite.logical_fingerprint.digest,
    )

    assert (
        forward
        == reverse
        == _expected_manifest(
            composite,
            compiled_roots=2,
            include_generated_data_quantifier_definitions=True,
            include_at_least_data_predicates=True,
        )
    )
    assert len(cast(list[object], forward["source_literal_symbols"])) == 1
    assert len(cast(list[object], forward["data_value_symbols"])) == 1
    assert forward["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_bottom_object_has_value_drops_implicit_individual_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "SubClassOf(:A ObjectHasValue(owl:bottomObjectProperty :discarded))",
            "SubClassOf(ObjectComplementOf(ObjectHasValue("
            "owl:bottomObjectProperty :discarded)) :B)",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(snapshot, compiled_roots=2)
    assert manifest["individual_symbols"] == []
    assert manifest["individual_signature"] == []
    assert manifest["named_individuals"] == []
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_bottom_object_has_value_keeps_shared_live_individual() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "SubClassOf(:A ObjectHasValue(owl:bottomObjectProperty :shared))",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:B))",
            "Declaration(ObjectProperty(:p))",
            "SubClassOf(:B ObjectHasValue(:p :shared))",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))
    records = _composite_records(composite, (left, right))

    forward = _native_slices_manifest(
        *records,
        logical_fingerprint=composite.logical_fingerprint.digest,
    )
    reverse = _native_slices_manifest(
        *reversed(records),
        logical_fingerprint=composite.logical_fingerprint.digest,
    )

    assert (
        forward
        == reverse
        == _expected_manifest(
            composite,
            compiled_roots=2,
            include_generated_object_quantifier_definitions=True,
            include_at_least_object_predicates=True,
        )
    )
    assert len(cast(list[object], forward["individual_symbols"])) == 1
    assert cast(list[dict[str, object]], forward["individual_signature"])[0]["declared"] is False
    assert forward["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_reduced_restriction_disjoint_duplicates_force_empty_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(ObjectProperty(:p))",
            "DisjointClasses(ObjectMinCardinality(0 :p :A) ObjectMaxCardinality(2 :p owl:Nothing))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(snapshot, compiled_roots=1)
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_reducible_restrictions_require_retained_nonbuiltin_inputs() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:B))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(NamedIndividual(:a))",
            "SubClassOf(ObjectSomeValuesFrom(owl:bottomObjectProperty :undeclared) :B)",
            "SubClassOf(ObjectHasValue(owl:bottomObjectProperty :a) :B)",
            "SubClassOf(ObjectMinCardinality(0 :p :undeclared) :B)",
            'SubClassOf(DataHasValue(owl:bottomDataProperty "value") :B)',
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest["compiled_roots"] == 2
    assert manifest["deferred_roots"] == 2
    class_symbols = cast(list[dict[str, object]], manifest["class_expression_symbols"])
    assert not any(
        str(value["display"]).startswith(
            (
                "ObjectSomeValuesFrom:",
                "ObjectHasValue:",
                "ObjectMinCardinality:",
                "DataHasValue:",
            )
        )
        for value in class_symbols
    )
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_reducible_restrictions_remap_composite_slices_exactly() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(ObjectProperty(:p))",
            "SubClassOf(ObjectMinCardinality(0 :p :A) :B)",
            "SubClassOf(ObjectSomeValuesFrom(:p owl:Nothing) :B)",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:B))",
            "Declaration(DataProperty(:d))",
            "SubClassOf(DataSomeValuesFrom(:d DataComplementOf(rdfs:Literal)) :B)",
            "SubClassOf(DataExactCardinality(0 :d DataComplementOf(rdfs:Literal)) :B)",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    manifest = _native_slices_manifest(*_composite_records(composite, (left, right)))

    assert manifest == _expected_manifest(composite, compiled_roots=4)
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_reducible_disjoint_unions_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:C))",
            "Declaration(Class(:D))",
            "Declaration(Class(:E))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(AnnotationProperty(:note))",
            'DisjointUnion(Annotation(:note "source") :A :B owl:Nothing)',
            "DisjointUnion(:C :B owl:Thing)",
            "DisjointUnion(:D :B ObjectUnionOf(:B owl:Nothing))",
            "DisjointUnion(:E :B ObjectSomeValuesFrom(:p owl:Nothing))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(snapshot, compiled_roots=4)
    assert not any(
        value["generated"] or str(value["display"]).startswith("ObjectUnionOf:")
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_generated_disjoint_unions_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:C))",
            "Declaration(Class(:D))",
            "Declaration(Class(:U))",
            "Declaration(Class(:V))",
            "Declaration(NamedIndividual(:i))",
            "Declaration(AnnotationProperty(:note))",
            "DisjointUnion(:U :A :B)",
            'DisjointUnion(Annotation(:note "same definition") :U :A :B)',
            "SubClassOf(:C ObjectUnionOf(:A :B))",
            "DisjointUnion(:V ObjectComplementOf(:A) ObjectOneOf(:i) :D)",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(snapshot, compiled_roots=4)
    assert (
        sum(
            bool(value["generated"])
            for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
        )
        == 2
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_recursive_generated_disjoint_unions_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:C))",
            "Declaration(Class(:D))",
            "Declaration(Class(:U))",
            "Declaration(Class(:V))",
            "Declaration(AnnotationProperty(:note))",
            "DisjointUnion(:U ObjectIntersectionOf(:A ObjectUnionOf(:B :C)) :D)",
            'DisjointUnion(Annotation(:note "same recursive definitions") :U '
            "ObjectIntersectionOf(:A ObjectUnionOf(:B :C)) :D)",
            "DisjointUnion(:V ObjectUnionOf(:A :B) :C)",
            "SubClassOf(ObjectIntersectionOf(:A ObjectUnionOf(:B :C)) :D)",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(snapshot, compiled_roots=4)
    assert (
        sum(
            bool(value["generated"])
            for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
        )
        == 7
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_recursive_disjoint_unions_remap_composite_slices_exactly() -> None:
    declarations = (
        "Declaration(Class(:A))",
        "Declaration(Class(:B))",
        "Declaration(Class(:C))",
        "Declaration(Class(:D))",
        "Declaration(Class(:E))",
        "Declaration(Class(:U))",
        "Declaration(Class(:V))",
    )
    left = pyowl_core.load_snapshot(
        functional(
            *declarations,
            "DisjointUnion(:U ObjectIntersectionOf(:A ObjectUnionOf(:B :C)) :D)",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            *declarations,
            "DisjointUnion(:V ObjectIntersectionOf(:A ObjectUnionOf(:B :C)) :E)",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    manifest = _native_slices_manifest(
        *_composite_records(composite, (left, right)),
        logical_fingerprint=composite.logical_fingerprint.digest,
    )

    assert manifest == _expected_manifest(composite, compiled_roots=2)
    generated = [
        value
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
        if value["generated"]
    ]
    assert len(generated) == 6
    namespace = f":class:{composite.logical_fingerprint.hex}:"
    assert all(namespace in str(value["display"]) for value in generated)
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_restriction_bearing_disjoint_unions_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:U))",
            "Declaration(NamedIndividual(:i))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "Declaration(DataProperty(:d))",
            "Declaration(DataProperty(:e))",
            "Declaration(AnnotationProperty(:note))",
            "DisjointUnion(:U "
            "ObjectSomeValuesFrom(:p ObjectIntersectionOf(:A ObjectHasSelf(:q))) "
            "ObjectAllValuesFrom(ObjectInverseOf(:q) ObjectUnionOf(:A :B)) "
            "ObjectMinCardinality(1 :p ObjectOneOf(:i)) "
            "ObjectMaxCardinality(1 :q ObjectComplementOf(:A)) "
            "ObjectExactCardinality(2 :p :B) "
            "ObjectHasValue(:q :i) "
            "DataSomeValuesFrom(:d DataIntersectionOf(xsd:string xsd:integer)) "
            "DataAllValuesFrom(:e DataUnionOf(xsd:boolean xsd:decimal)) "
            "DataMinCardinality(1 :d DataUnionOf(xsd:string xsd:decimal)) "
            "DataMaxCardinality(1 :e "
            "DataIntersectionOf(xsd:boolean xsd:integer)) "
            "DataExactCardinality(1 :d DataUnionOf(xsd:string xsd:integer)) "
            'DataHasValue(:e "value"))',
            'DisjointUnion(Annotation(:note "same restrictions") :U '
            "ObjectSomeValuesFrom(:p ObjectIntersectionOf(:A ObjectHasSelf(:q))) "
            "ObjectAllValuesFrom(ObjectInverseOf(:q) ObjectUnionOf(:A :B)) "
            "ObjectMinCardinality(1 :p ObjectOneOf(:i)) "
            "ObjectMaxCardinality(1 :q ObjectComplementOf(:A)) "
            "ObjectExactCardinality(2 :p :B) "
            "ObjectHasValue(:q :i) "
            "DataSomeValuesFrom(:d DataIntersectionOf(xsd:string xsd:integer)) "
            "DataAllValuesFrom(:e DataUnionOf(xsd:boolean xsd:decimal)) "
            "DataMinCardinality(1 :d DataUnionOf(xsd:string xsd:decimal)) "
            "DataMaxCardinality(1 :e "
            "DataIntersectionOf(xsd:boolean xsd:integer)) "
            "DataExactCardinality(1 :d DataUnionOf(xsd:string xsd:integer)) "
            'DataHasValue(:e "value"))',
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=2,
        include_generated_object_self_definitions=True,
        include_generated_object_quantifier_definitions=True,
        include_generated_object_cardinality_definitions=True,
        include_at_least_object_predicates=True,
        include_annotated_equality_predicates=True,
        include_generated_data_quantifier_definitions=True,
        include_generated_data_cardinality_definitions=True,
        include_at_least_data_predicates=True,
        include_generated_data_definitions=True,
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_complemented_restriction_disjoint_union_members_match_scalar() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:V))",
            "Declaration(NamedIndividual(:i))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "Declaration(DataProperty(:d))",
            "Declaration(DataProperty(:e))",
            "DisjointUnion(:V "
            "ObjectComplementOf(ObjectSomeValuesFrom(:p "
            "ObjectIntersectionOf(:A :B))) "
            "ObjectComplementOf(ObjectMaxCardinality(0 :q ObjectOneOf(:i))) "
            "ObjectComplementOf(ObjectExactCardinality(1 "
            "ObjectInverseOf(:q) ObjectUnionOf(:A :B))) "
            "ObjectComplementOf(ObjectHasValue(:p :i)) "
            "ObjectComplementOf(DataSomeValuesFrom(:d "
            "DataIntersectionOf(xsd:string xsd:integer))) "
            "ObjectComplementOf(DataMaxCardinality(0 :e "
            "DataUnionOf(xsd:boolean xsd:decimal))) "
            "ObjectComplementOf(DataExactCardinality(0 :d "
            "DataIntersectionOf(xsd:string xsd:boolean))) "
            'ObjectComplementOf(DataHasValue(:e "value")) '
            ":A)",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=1,
        include_generated_object_quantifier_definitions=True,
        include_generated_object_cardinality_definitions=True,
        include_at_least_object_predicates=True,
        include_generated_data_quantifier_definitions=True,
        include_at_least_data_predicates=True,
        include_generated_data_definitions=True,
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_restriction_disjoint_unions_reuse_global_identity() -> None:
    declarations = (
        "Declaration(Class(:A))",
        "Declaration(Class(:B))",
        "Declaration(Class(:U))",
        "Declaration(Class(:V))",
        "Declaration(ObjectProperty(:p))",
        "Declaration(ObjectProperty(:q))",
        "Declaration(DataProperty(:d))",
    )
    object_restriction = (
        "ObjectExactCardinality(2 :p ObjectIntersectionOf(:A ObjectSomeValuesFrom(:q :B)))"
    )
    data_restriction = (
        "DataExactCardinality(1 :d "
        "DataIntersectionOf(xsd:string DataUnionOf(xsd:integer xsd:boolean)))"
    )
    left = pyowl_core.load_snapshot(
        functional(
            *declarations,
            f"DisjointUnion(:U {object_restriction} {data_restriction} :A)",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            *declarations,
            f"DisjointUnion(:V {object_restriction} {data_restriction} :B)",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    manifest = _native_slices_manifest(
        *_composite_records(composite, (left, right)),
        logical_fingerprint=composite.logical_fingerprint.digest,
    )

    assert manifest == _expected_manifest(
        composite,
        compiled_roots=2,
        include_generated_object_quantifier_definitions=True,
        include_generated_object_cardinality_definitions=True,
        include_at_least_object_predicates=True,
        include_annotated_equality_predicates=True,
        include_generated_data_quantifier_definitions=True,
        include_generated_data_cardinality_definitions=True,
        include_at_least_data_predicates=True,
        include_generated_data_definitions=True,
    )
    class_namespace = f":class:{composite.logical_fingerprint.hex}:"
    data_namespace = f":data:{composite.logical_fingerprint.hex}:"
    assert all(
        class_namespace in str(value["display"])
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
        if value["generated"]
    )
    assert all(
        data_namespace in str(value["display"])
        for value in cast(list[dict[str, object]], manifest["data_range_symbols"])
        if value["generated"]
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_partial_generated_disjoint_union_defers_without_symbol_leaks() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:U))",
            "Declaration(ObjectProperty(:p))",
            "DisjointUnion(:U ObjectIntersectionOf(:A :B) ObjectMinCardinality(4294967296 :p :B))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest["compiled_roots"] == 0
    assert manifest["deferred_roots"] == 1
    assert not any(
        value["generated"]
        or str(value["display"]).startswith(
            (
                "ObjectIntersectionOf:",
                "ObjectUnionOf:",
                "ObjectMinCardinality:",
            )
        )
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
    )
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_reducible_disjoint_unions_remap_composite_slices_exactly() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "DisjointUnion(:A :B owl:Nothing)",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:B))",
            "Declaration(Class(:C))",
            "DisjointUnion(:C :B ObjectUnionOf(:B owl:Nothing))",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    manifest = _native_slices_manifest(*_composite_records(composite, (left, right)))

    assert manifest == _expected_manifest(composite, compiled_roots=2)
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


@pytest.mark.parametrize(
    "axiom",
    [
        "SubClassOf(ObjectOneOf(:a) ObjectOneOf(:a))",
        "SubClassOf(ObjectOneOf(:a) owl:Thing)",
        "SubClassOf(owl:Nothing ObjectComplementOf(ObjectOneOf(:a)))",
        "DisjointClasses(owl:Nothing ObjectOneOf(:a))",
    ],
)
def test_trivial_nominal_axioms_normalize_without_symbol_leaks(axiom: str) -> None:
    snapshot = pyowl_core.load_snapshot(
        functional("Declaration(NamedIndividual(:a))", axiom),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(snapshot, compiled_roots=1)
    assert all(
        not str(value["display"]).startswith(("ObjectOneOf:", "ObjectComplementOf:"))
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
    )
    assert all(
        predicate["kind"] not in {PredicateKind.NOMINAL.value, PredicateKind.NEGATED_NOMINAL.value}
        for predicate in cast(list[dict[str, object]], manifest["predicates"])
    )
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_atomic_complements_remap_local_class_domains_exactly() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:Z))",
            "Declaration(NamedIndividual(:z))",
            "ClassAssertion(ObjectComplementOf(:Z) :z)",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(NamedIndividual(:a))",
            "ClassAssertion(ObjectComplementOf(:A) :a)",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    manifest = _native_slices_manifest(*_composite_records(composite, (left, right)))

    assert manifest == _expected_manifest(composite, compiled_roots=2)
    assert manifest["deferred_roots"] == 0
    assert (
        sum(
            str(value["display"]).startswith("ObjectComplementOf:")
            for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
        )
        == 2
    )
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_named_nominal_assertions_remap_exactly() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(NamedIndividual(:z1))",
            "Declaration(NamedIndividual(:z2))",
            "Declaration(NamedIndividual(:zc))",
            "ClassAssertion(ObjectOneOf(:z1 :z2) :zc)",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(NamedIndividual(:a1))",
            "Declaration(NamedIndividual(:ac))",
            "ClassAssertion(ObjectComplementOf(ObjectOneOf(:a1)) :ac)",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    manifest = _native_slices_manifest(*_composite_records(composite, (left, right)))

    assert manifest == _expected_manifest(composite, compiled_roots=2)
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_named_nominal_class_axioms_and_constraints_remap_exactly() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:Z))",
            "Declaration(NamedIndividual(:z1))",
            "Declaration(NamedIndividual(:z2))",
            "Declaration(ObjectProperty(:zp))",
            "SubClassOf(ObjectOneOf(:z1 :z2) :Z)",
            "ObjectPropertyDomain(:zp ObjectComplementOf(ObjectOneOf(:z1)))",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(NamedIndividual(:a1))",
            "Declaration(NamedIndividual(:a2))",
            "Declaration(DataProperty(:ad))",
            "EquivalentClasses(:A ObjectOneOf(:a1 :a2))",
            "DataPropertyDomain(:ad ObjectComplementOf(ObjectOneOf(:a2)))",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    manifest = _native_slices_manifest(*_composite_records(composite, (left, right)))

    assert manifest == _expected_manifest(
        composite,
        compiled_roots=4,
        include_object_constraints=True,
        include_data_domains=True,
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_nested_complements_remap_normalized_literals_exactly() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:Z))",
            "Declaration(NamedIndividual(:z))",
            "Declaration(DataProperty(:zd))",
            "SubClassOf(ObjectComplementOf(ObjectComplementOf("
            "ObjectComplementOf(:Z))) ObjectComplementOf("
            "ObjectComplementOf(ObjectOneOf(:z))))",
            "DataPropertyRange(:zd DataComplementOf(DataComplementOf("
            'DataComplementOf(DataOneOf("z")))))',
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(NamedIndividual(:a))",
            "Declaration(ObjectProperty(:ap))",
            "Declaration(Datatype(:A))",
            "ObjectPropertyDomain(:ap ObjectComplementOf(ObjectComplementOf("
            "ObjectComplementOf(ObjectOneOf(:a)))))",
            "DatatypeDefinition(:A DataComplementOf(DataComplementOf("
            "DatatypeRestriction(xsd:integer "
            'xsd:minInclusive "2"^^xsd:integer))))',
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    manifest = _native_slices_manifest(*_composite_records(composite, (left, right)))

    assert manifest == _expected_manifest(
        composite,
        compiled_roots=4,
        include_object_constraints=True,
        include_data_ranges=True,
        include_datatype_definitions=True,
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_reducible_booleans_remap_atomic_literals_exactly() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:Z))",
            "Declaration(Class(:Y))",
            "Declaration(DataProperty(:zd))",
            "SubClassOf(ObjectIntersectionOf(:Z owl:Thing) ObjectUnionOf(:Y owl:Nothing))",
            'DataPropertyRange(:zd DataIntersectionOf(DataOneOf("z") rdfs:Literal))',
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(NamedIndividual(:a))",
            "Declaration(ObjectProperty(:ap))",
            "Declaration(Datatype(:A))",
            "ObjectPropertyDomain(:ap ObjectUnionOf(ObjectOneOf(:a) owl:Nothing))",
            "DatatypeDefinition(:A DataUnionOf("
            "DatatypeRestriction(xsd:integer "
            'xsd:minInclusive "2"^^xsd:integer) '
            "DataComplementOf(rdfs:Literal)))",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    manifest = _native_slices_manifest(*_composite_records(composite, (left, right)))

    assert manifest == _expected_manifest(
        composite,
        compiled_roots=4,
        include_object_constraints=True,
        include_data_ranges=True,
        include_datatype_definitions=True,
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_named_same_individual_facts_and_overlapping_provenance_match_scalar() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(NamedIndividual(:a))",
            "Declaration(NamedIndividual(:b))",
            "Declaration(NamedIndividual(:c))",
            "SameIndividual(:a :b :c)",
            # The (a, b) equality is shared by two source axioms, but each
            # source retains its own provenance entry on the merged fact.
            "SameIndividual(:a :b)",
        ),
        options=OPTIONS,
    )

    assert _native_manifest(snapshot) == _expected_manifest(snapshot, compiled_roots=2)


def test_named_different_individual_facts_and_pairwise_provenance_match_scalar() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(NamedIndividual(:a))",
            "Declaration(NamedIndividual(:b))",
            "Declaration(NamedIndividual(:c))",
            "DifferentIndividuals(:a :b :c)",
            # The (a, b) inequality is shared by two source axioms, while the
            # three-member root expands to every canonical unordered pair.
            "DifferentIndividuals(:a :b)",
        ),
        options=OPTIONS,
    )

    assert _native_manifest(snapshot) == _expected_manifest(snapshot, compiled_roots=2)


def test_double_digit_individual_and_fact_ids_preserve_scalar_order() -> None:
    declarations = [f"Declaration(NamedIndividual(:i{index}))" for index in range(12)]
    assertions = [f"ClassAssertion(owl:Thing :i{index})" for index in range(12)]
    snapshot = pyowl_core.load_snapshot(
        functional(
            *declarations,
            *assertions,
            "SameIndividual(:i8 :i9)",
            "DifferentIndividuals(:i7 :i8 :i9)",
        ),
        options=OPTIONS,
    )

    assert _native_manifest(snapshot) == _expected_manifest(
        snapshot,
        compiled_roots=len(assertions) + 2,
    )


def test_annotated_named_axiom_family_preserves_exact_nested_provenance() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:C))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(AnnotationProperty(:note))",
            "Declaration(AnnotationProperty(:meta))",
            "Declaration(NamedIndividual(:i))",
            "Declaration(NamedIndividual(:j))",
            'SubClassOf(Annotation(Annotation(:meta "nested") :note "source") :A :B)',
            "EquivalentClasses(Annotation(:note <urn:annotation:value>) :A :C)",
            'DisjointClasses(Annotation(:note "bonjour"@fr) :B :C)',
            "ClassAssertion(Annotation(:note _:source) :A :i)",
            'SameIndividual(Annotation(:note "same") :i :j)',
            'DifferentIndividuals(Annotation(:note "different") :i :j)',
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)
    assert manifest == _expected_manifest(snapshot, compiled_roots=6)
    assert manifest["compiled_roots"] == 6
    assert manifest["deferred_roots"] == 0
    assert manifest["named_individuals"] == [0, 1]
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_annotated_named_object_domain_and_range_clauses_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "Declaration(AnnotationProperty(:note))",
            "Declaration(AnnotationProperty(:meta))",
            'ObjectPropertyDomain(Annotation(Annotation(:meta "nested") :note "left") :p :A)',
            'ObjectPropertyDomain(Annotation(:note "right"@en) :p :A)',
            "ObjectPropertyRange(Annotation(:note _:source) ObjectInverseOf(:q) :B)",
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(
        snapshot,
        compiled_roots=3,
        include_object_constraints=True,
    )
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_restriction_bearing_object_property_ranges_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(NamedIndividual(:i))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "Declaration(DataProperty(:d))",
            "Declaration(AnnotationProperty(:note))",
            "ObjectPropertyRange(:p ObjectSomeValuesFrom(:q ObjectIntersectionOf(:A :B)))",
            'ObjectPropertyRange(Annotation(:note "same range") :p '
            "ObjectSomeValuesFrom(:q ObjectIntersectionOf(:A :B)))",
            "ObjectPropertyRange(ObjectInverseOf(:p) "
            "ObjectExactCardinality(2 ObjectInverseOf(:q) ObjectOneOf(:i)))",
            "ObjectPropertyRange(:q DataExactCardinality(1 :d "
            "DataIntersectionOf(xsd:string "
            "DataUnionOf(xsd:integer xsd:boolean))))",
            "ObjectPropertyRange(:p ObjectHasValue(:q :i))",
            'ObjectPropertyRange(:q DataHasValue(:d "value"))',
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=6,
        include_object_constraints=True,
        include_generated_object_quantifier_definitions=True,
        include_generated_object_cardinality_definitions=True,
        include_at_least_object_predicates=True,
        include_annotated_equality_predicates=True,
        include_generated_data_quantifier_definitions=True,
        include_generated_data_cardinality_definitions=True,
        include_at_least_data_predicates=True,
        include_generated_data_definitions=True,
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_complemented_restriction_object_property_ranges_match_scalar() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(NamedIndividual(:i))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "Declaration(DataProperty(:d))",
            "Declaration(DataProperty(:e))",
            "ObjectPropertyRange(ObjectInverseOf(:p) "
            "ObjectComplementOf(ObjectSomeValuesFrom(:q "
            "ObjectIntersectionOf(:A :B))))",
            "ObjectPropertyRange(:p ObjectComplementOf("
            "ObjectMaxCardinality(0 :q ObjectOneOf(:i))))",
            "ObjectPropertyRange(:q ObjectComplementOf(ObjectExactCardinality(1 "
            "ObjectInverseOf(:p) ObjectUnionOf(:A :B))))",
            "ObjectPropertyRange(:p ObjectComplementOf(ObjectHasValue(:q :i)))",
            "ObjectPropertyRange(:q ObjectComplementOf(DataSomeValuesFrom(:d "
            "DataIntersectionOf(xsd:string xsd:integer))))",
            "ObjectPropertyRange(:p ObjectComplementOf(DataMaxCardinality(0 :e "
            "DataUnionOf(xsd:boolean xsd:decimal))))",
            "ObjectPropertyRange(:q ObjectComplementOf(DataExactCardinality(0 :d "
            "DataIntersectionOf(xsd:string xsd:boolean))))",
            'ObjectPropertyRange(:p ObjectComplementOf(DataHasValue(:e "value")))',
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=8,
        include_object_constraints=True,
        include_generated_object_quantifier_definitions=True,
        include_generated_object_cardinality_definitions=True,
        include_at_least_object_predicates=True,
        include_generated_data_quantifier_definitions=True,
        include_at_least_data_predicates=True,
        include_generated_data_definitions=True,
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_restriction_object_ranges_reuse_global_identity() -> None:
    declarations = (
        "Declaration(Class(:A))",
        "Declaration(Class(:B))",
        "Declaration(ObjectProperty(:p))",
        "Declaration(ObjectProperty(:q))",
        "Declaration(DataProperty(:d))",
    )
    object_restriction = (
        "ObjectExactCardinality(2 :p ObjectIntersectionOf(:A ObjectSomeValuesFrom(:q :B)))"
    )
    data_restriction = (
        "DataExactCardinality(1 :d "
        "DataIntersectionOf(xsd:string DataUnionOf(xsd:integer xsd:boolean)))"
    )
    left = pyowl_core.load_snapshot(
        functional(
            *declarations,
            f"ObjectPropertyRange(ObjectInverseOf(:p) {object_restriction})",
            f"ObjectPropertyRange(:q {data_restriction})",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            *declarations,
            f"ObjectPropertyRange(ObjectInverseOf(:q) {object_restriction})",
            f"ObjectPropertyRange(:p {data_restriction})",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    manifest = _native_slices_manifest(
        *_composite_records(composite, (left, right)),
        logical_fingerprint=composite.logical_fingerprint.digest,
    )

    assert manifest == _expected_manifest(
        composite,
        compiled_roots=4,
        include_object_constraints=True,
        include_generated_object_quantifier_definitions=True,
        include_generated_object_cardinality_definitions=True,
        include_at_least_object_predicates=True,
        include_annotated_equality_predicates=True,
        include_generated_data_quantifier_definitions=True,
        include_generated_data_cardinality_definitions=True,
        include_at_least_data_predicates=True,
        include_generated_data_definitions=True,
    )
    class_namespace = f":class:{composite.logical_fingerprint.hex}:"
    data_namespace = f":data:{composite.logical_fingerprint.hex}:"
    assert all(
        class_namespace in str(value["display"])
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
        if value["generated"]
    )
    assert all(
        data_namespace in str(value["display"])
        for value in cast(list[dict[str, object]], manifest["data_range_symbols"])
        if value["generated"]
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_partial_restriction_object_range_defers_without_symbol_leaks() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "ObjectPropertyRange(ObjectInverseOf(:p) ObjectIntersectionOf("
            "ObjectSomeValuesFrom(:q :A) "
            "ObjectMinCardinality(4294967296 :q :B)))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest["compiled_roots"] == 0
    assert manifest["deferred_roots"] == 1
    assert not any(
        value["generated"]
        or str(value["display"]).startswith(
            (
                "ObjectIntersectionOf:",
                "ObjectSomeValuesFrom:",
                "ObjectMinCardinality:",
            )
        )
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
    )
    assert all(
        predicate["kind"]
        not in {
            PredicateKind.AT_LEAST_OBJECT.value,
            PredicateKind.OBJECT_ROLE.value,
        }
        for predicate in cast(list[dict[str, object]], manifest["predicates"])
    )
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_annotated_object_functionality_and_reflexivity_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "Declaration(AnnotationProperty(:note))",
            "Declaration(AnnotationProperty(:meta))",
            "Declaration(NamedIndividual(:i))",
            "Declaration(NamedIndividual(:j))",
            'FunctionalObjectProperty(Annotation(Annotation(:meta "nested") :note "left") :p)',
            'FunctionalObjectProperty(Annotation(:note "right"@en) :p)',
            (
                "InverseFunctionalObjectProperty(Annotation(:note <urn:annotation:value>) "
                "ObjectInverseOf(:q))"
            ),
            "ReflexiveObjectProperty(Annotation(:note _:source) :p)",
            "SameIndividual(:i :j)",
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(
        snapshot,
        compiled_roots=5,
        include_object_characteristics=True,
    )
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_annotated_named_data_property_domains_match_scalar_exactly() -> None:
    long_data_property = (
        "<https://example.test/data-property/this-name-is-deliberately-longer-than-owl-builtins>"
    )
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(DataProperty(:p))",
            f"Declaration(DataProperty({long_data_property}))",
            "Declaration(AnnotationProperty(:note))",
            "Declaration(AnnotationProperty(:meta))",
            'DataPropertyDomain(Annotation(Annotation(:meta "nested") :note "left") :p :A)',
            'DataPropertyDomain(Annotation(:note "right"@en) :p :A)',
            (
                "DataPropertyDomain(Annotation(:note <urn:annotation:value>) "
                f"{long_data_property} :B)"
            ),
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(
        snapshot,
        compiled_roots=3,
        include_data_domains=True,
    )
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_annotated_named_data_property_ranges_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "Declaration(DataProperty(:q))",
            "Declaration(AnnotationProperty(:note))",
            "Declaration(AnnotationProperty(:meta))",
            (
                'DataPropertyRange(Annotation(Annotation(:meta "nested") '
                ':note "left") :p xsd:string)'
            ),
            'DataPropertyRange(Annotation(:note "right"@en) :p xsd:string)',
            "DataPropertyRange(Annotation(:note _:source) :q xsd:integer)",
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(
        snapshot,
        compiled_roots=3,
        include_data_ranges=True,
    )
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_atomic_data_complement_ranges_and_definitions_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "Declaration(DataProperty(:q))",
            "Declaration(Datatype(:D))",
            "Declaration(Datatype(:E))",
            "Declaration(AnnotationProperty(:note))",
            "DataPropertyRange(:p DataComplementOf(xsd:string))",
            'DataPropertyRange(Annotation(:note "duplicate") :p DataComplementOf(xsd:string))',
            "DataPropertyRange(:q DataComplementOf(xsd:integer))",
            "DatatypeDefinition(:D DataComplementOf(xsd:string))",
            "DatatypeDefinition(:E DataComplementOf(xsd:integer))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=5,
        include_data_ranges=True,
        include_datatype_definitions=True,
    )
    assert (
        sum(
            str(value["display"]).startswith("DataComplementOf:")
            for value in cast(list[dict[str, object]], manifest["data_range_symbols"])
        )
        == 2
    )
    assert (
        sum(
            predicate["kind"] == PredicateKind.NEGATED_DATA_RANGE.value
            for predicate in cast(list[dict[str, object]], manifest["predicates"])
        )
        == 2
    )
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_enumerated_and_restricted_data_literals_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "Declaration(DataProperty(:q))",
            "Declaration(Datatype(:D))",
            "Declaration(Datatype(:E))",
            "Declaration(AnnotationProperty(:note))",
            'DataPropertyRange(:p DataOneOf("alpha" "beta"))',
            'DataPropertyRange(Annotation(:note "duplicate") :p DataOneOf("alpha" "beta"))',
            "DataPropertyRange(:q DatatypeRestriction(xsd:integer "
            'xsd:minInclusive "1"^^xsd:integer '
            'xsd:maxInclusive "5"^^xsd:integer))',
            'DatatypeDefinition(:D DataOneOf("alpha" "beta"))',
            "DatatypeDefinition(:E DatatypeRestriction(xsd:integer "
            'xsd:minInclusive "1"^^xsd:integer '
            'xsd:maxInclusive "5"^^xsd:integer))',
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=5,
        include_data_ranges=True,
        include_datatype_definitions=True,
    )
    data_range_symbols = cast(list[dict[str, object]], manifest["data_range_symbols"])
    assert sum(str(value["display"]).startswith("DataOneOf:") for value in data_range_symbols) == 1
    assert (
        sum(
            str(value["display"]).startswith("DatatypeRestriction:") for value in data_range_symbols
        )
        == 1
    )
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_complemented_enumerated_restricted_and_bottom_ranges_match_scalar() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "Declaration(DataProperty(:q))",
            "Declaration(DataProperty(:r))",
            "Declaration(Datatype(:D))",
            "Declaration(Datatype(:E))",
            'DataPropertyRange(:p DataComplementOf(DataOneOf("alpha" "beta")))',
            "DataPropertyRange(:q DataComplementOf(DatatypeRestriction(xsd:integer "
            'xsd:minInclusive "1"^^xsd:integer)))',
            "DataPropertyRange(:r DataComplementOf("
            "<http://www.w3.org/2000/01/rdf-schema#Literal>))",
            'DatatypeDefinition(:D DataComplementOf(DataOneOf("alpha" "beta")))',
            "DatatypeDefinition(:E DataComplementOf(DatatypeRestriction(xsd:integer "
            'xsd:minInclusive "1"^^xsd:integer)))',
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=5,
        include_data_ranges=True,
        include_datatype_definitions=True,
    )
    data_range_symbols = cast(list[dict[str, object]], manifest["data_range_symbols"])
    assert (
        sum(str(value["display"]).startswith("DataComplementOf:") for value in data_range_symbols)
        == 3
    )
    assert (
        sum(
            predicate["kind"] == PredicateKind.NEGATED_DATA_RANGE.value
            for predicate in cast(list[dict[str, object]], manifest["predicates"])
        )
        == 3
    )
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_nested_atomic_data_complements_reduce_by_parity_exactly() -> None:
    double_enumeration = 'DataComplementOf(DataComplementOf(DataOneOf("alpha" "beta")))'
    triple_restriction = (
        "DataComplementOf(DataComplementOf(DataComplementOf("
        "DatatypeRestriction(xsd:integer "
        'xsd:minInclusive "1"^^xsd:integer))))'
    )
    double_string = "DataComplementOf(DataComplementOf(xsd:string))"
    triple_enumeration = 'DataComplementOf(DataComplementOf(DataComplementOf(DataOneOf("value"))))'
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "Declaration(DataProperty(:q))",
            "Declaration(Datatype(:D))",
            "Declaration(Datatype(:E))",
            f"DataPropertyRange(:p {double_enumeration})",
            f"DataPropertyRange(:q {triple_restriction})",
            f"DatatypeDefinition(:D {double_string})",
            f"DatatypeDefinition(:E {triple_enumeration})",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=4,
        include_data_ranges=True,
        include_datatype_definitions=True,
    )
    data_range_symbols = cast(list[dict[str, object]], manifest["data_range_symbols"])
    assert (
        sum(str(value["display"]).startswith("DataComplementOf:") for value in data_range_symbols)
        == 2
    )
    assert (
        sum(
            predicate["kind"] == PredicateKind.NEGATED_DATA_RANGE.value
            for predicate in cast(list[dict[str, object]], manifest["predicates"])
        )
        == 2
    )
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_reducible_data_booleans_collapse_to_atomic_ranges_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "Declaration(DataProperty(:q))",
            "Declaration(DataProperty(:r))",
            "Declaration(DataProperty(:s))",
            "Declaration(Datatype(:D))",
            "Declaration(Datatype(:E))",
            "Declaration(Datatype(:F))",
            "Declaration(Datatype(:G))",
            "DataPropertyRange(:p DataIntersectionOf(xsd:string rdfs:Literal))",
            'DataPropertyRange(:q DataUnionOf(DataOneOf("alpha") DataComplementOf(rdfs:Literal)))',
            "DatatypeDefinition(:D DataIntersectionOf("
            "DatatypeRestriction(xsd:integer "
            'xsd:minInclusive "1"^^xsd:integer) rdfs:Literal))',
            'DatatypeDefinition(:E DataUnionOf(DataComplementOf(DataOneOf("blocked")) '
            "DataComplementOf(rdfs:Literal)))",
            "DataPropertyRange(:r DataUnionOf(xsd:string rdfs:Literal))",
            "DatatypeDefinition(:F DataIntersectionOf(xsd:string DataComplementOf(rdfs:Literal)))",
            "DataPropertyRange(:s DataComplementOf(DataUnionOf("
            "DataComplementOf(xsd:string) DataComplementOf(rdfs:Literal))))",
            "DatatypeDefinition(:G DataIntersectionOf(xsd:string "
            "DataComplementOf(DataComplementOf(xsd:string))))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=8,
        include_data_ranges=True,
        include_datatype_definitions=True,
    )
    data_symbols = cast(list[dict[str, object]], manifest["data_range_symbols"])
    assert not any(
        str(value["display"]).startswith(("DataIntersectionOf:", "DataUnionOf:"))
        for value in data_symbols
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_annotated_named_datatype_definitions_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Datatype(:D))",
            "Declaration(Datatype(:E))",
            "Declaration(Datatype(:F))",
            "Declaration(AnnotationProperty(:note))",
            "Declaration(AnnotationProperty(:meta))",
            (
                'DatatypeDefinition(Annotation(Annotation(:meta "nested") '
                ':note "left") :D xsd:string)'
            ),
            'DatatypeDefinition(Annotation(:note "right"@en) :E xsd:integer)',
            "DatatypeDefinition(Annotation(:note _:source) :F xsd:boolean)",
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(
        snapshot,
        compiled_roots=3,
        include_datatype_definitions=True,
    )
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_annotated_named_keys_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:C))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "Declaration(DataProperty(:d))",
            "Declaration(DataProperty(:e))",
            "Declaration(AnnotationProperty(:note))",
            "Declaration(AnnotationProperty(:meta))",
            (
                'HasKey(Annotation(Annotation(:meta "nested") :note "mixed") '
                ":A (:p ObjectInverseOf(:q)) (:d :e))"
            ),
            'HasKey(Annotation(:note "object"@en) :B (:q) ())',
            "HasKey(Annotation(:note _:source) :C () (:e))",
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(
        snapshot,
        compiled_roots=3,
        include_keys=True,
    )
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_annotated_functional_data_properties_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "Declaration(DataProperty(:q))",
            "Declaration(AnnotationProperty(:note))",
            "Declaration(AnnotationProperty(:meta))",
            "Declaration(NamedIndividual(:i))",
            "Declaration(NamedIndividual(:j))",
            'FunctionalDataProperty(Annotation(Annotation(:meta "nested") :note "left") :p)',
            'FunctionalDataProperty(Annotation(:note "right"@en) :p)',
            "FunctionalDataProperty(Annotation(:note _:source) :q)",
            "SameIndividual(:i :j)",
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(
        snapshot,
        compiled_roots=4,
        include_data_functionalities=True,
    )
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_annotated_string_data_property_assertions_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "Declaration(DataProperty(:q))",
            "Declaration(AnnotationProperty(:note))",
            "Declaration(AnnotationProperty(:meta))",
            "Declaration(NamedIndividual(:i))",
            (
                "DataPropertyAssertion("
                'Annotation(Annotation(:meta "nested") :note "left") :p :i "shared")'
            ),
            'DataPropertyAssertion(Annotation(:note "right"@en) :p :i "shared")',
            (
                "DataPropertyAssertion(Annotation(:note _:source) "
                ':q :i "  token   value  "^^xsd:token)'
            ),
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(
        snapshot,
        compiled_roots=3,
        include_data_assertions=True,
    )
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_string_data_assertions_remap_roles_terms_and_aliases_exactly() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:z))",
            "Declaration(NamedIndividual(:zSource))",
            'DataPropertyAssertion(:z :zSource "  shared  "^^xsd:token)',
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:a))",
            "Declaration(NamedIndividual(:aSource))",
            'DataPropertyAssertion(:a :aSource "shared"^^xsd:string)',
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    actual = _native_slices_manifest(*_composite_records(composite, (left, right)))

    assert actual == _expected_manifest(
        composite,
        compiled_roots=2,
        include_data_assertions=True,
    )
    assert len(cast(list[object], actual["source_literal_symbols"])) == 2
    assert len(cast(list[object], actual["data_value_symbols"])) == 1
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_annotated_negative_string_data_assertions_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "Declaration(DataProperty(:q))",
            "Declaration(AnnotationProperty(:note))",
            "Declaration(AnnotationProperty(:meta))",
            "Declaration(NamedIndividual(:i))",
            (
                "NegativeDataPropertyAssertion("
                'Annotation(Annotation(:meta "nested") :note "left") :p :i "blocked")'
            ),
            'NegativeDataPropertyAssertion(Annotation(:note "right"@en) :p :i "blocked")',
            (
                "NegativeDataPropertyAssertion(Annotation(:note <urn:annotation:value>) "
                ':q :i "  token   value  "^^xsd:token)'
            ),
            'DataPropertyAssertion(:p :i "allowed")',
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(
        snapshot,
        compiled_roots=4,
        include_data_assertions=True,
        include_negative_data_assertions=True,
    )
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_negative_string_data_assertions_remap_aliases_exactly() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:z))",
            "Declaration(NamedIndividual(:zSource))",
            'NegativeDataPropertyAssertion(:z :zSource "  shared  "^^xsd:token)',
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:a))",
            "Declaration(NamedIndividual(:aSource))",
            'NegativeDataPropertyAssertion(:a :aSource "shared"^^xsd:string)',
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    actual = _native_slices_manifest(*_composite_records(composite, (left, right)))

    assert actual == _expected_manifest(
        composite,
        compiled_roots=2,
        include_negative_data_assertions=True,
    )
    assert len(cast(list[object], actual["source_literal_symbols"])) == 2
    assert len(cast(list[object], actual["data_value_symbols"])) == 1
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_boolean_data_assertions_collapse_aliases_and_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "Declaration(DataProperty(:q))",
            "Declaration(NamedIndividual(:i))",
            'DataPropertyAssertion(:p :i "true"^^xsd:boolean)',
            'DataPropertyAssertion(:p :i "1"^^xsd:boolean)',
            'NegativeDataPropertyAssertion(:q :i "false"^^xsd:boolean)',
            'NegativeDataPropertyAssertion(:q :i "0"^^xsd:boolean)',
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(
        snapshot,
        compiled_roots=4,
        include_data_assertions=True,
        include_negative_data_assertions=True,
    )
    assert actual["data_value_symbols"] == _expected_data_value_symbols(snapshot)
    assert len(cast(list[object], actual["source_literal_symbols"])) == 4
    assert len(cast(list[object], actual["data_value_symbols"])) == 2
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_boolean_data_assertions_remap_one_shared_identity_exactly() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:z))",
            "Declaration(NamedIndividual(:zSource))",
            'DataPropertyAssertion(:z :zSource "true"^^xsd:boolean)',
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:a))",
            "Declaration(NamedIndividual(:aSource))",
            'NegativeDataPropertyAssertion(:a :aSource "1"^^xsd:boolean)',
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    actual = _native_slices_manifest(*_composite_records(composite, (left, right)))

    assert actual == _expected_manifest(
        composite,
        compiled_roots=2,
        include_data_assertions=True,
        include_negative_data_assertions=True,
    )
    assert len(cast(list[object], actual["source_literal_symbols"])) == 2
    assert len(cast(list[object], actual["data_value_symbols"])) == 1
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_integer_family_data_assertions_match_scalar_boundaries_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "Declaration(DataProperty(:q))",
            "Declaration(NamedIndividual(:i))",
            'DataPropertyAssertion(:p :i "+0001"^^xsd:integer)',
            'NegativeDataPropertyAssertion(:q :i "0"^^xsd:nonNegativeInteger)',
            'DataPropertyAssertion(:p :i "1"^^xsd:positiveInteger)',
            'NegativeDataPropertyAssertion(:q :i "-0"^^xsd:nonPositiveInteger)',
            'DataPropertyAssertion(:p :i "-1"^^xsd:negativeInteger)',
            'NegativeDataPropertyAssertion(:q :i "-9223372036854775808"^^xsd:long)',
            'DataPropertyAssertion(:p :i "2147483647"^^xsd:int)',
            'NegativeDataPropertyAssertion(:q :i "-32768"^^xsd:short)',
            'DataPropertyAssertion(:p :i "127"^^xsd:byte)',
            ('NegativeDataPropertyAssertion(:q :i "18446744073709551615"^^xsd:unsignedLong)'),
            'DataPropertyAssertion(:p :i "4294967295"^^xsd:unsignedInt)',
            'NegativeDataPropertyAssertion(:q :i "65535"^^xsd:unsignedShort)',
            'DataPropertyAssertion(:p :i "255"^^xsd:unsignedByte)',
            'DataPropertyAssertion(:p :i "999999999999999999999999"^^xsd:integer)',
            'NegativeDataPropertyAssertion(:q :i "-999999999999999999999999"^^xsd:integer)',
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(
        snapshot,
        compiled_roots=15,
        include_data_assertions=True,
        include_negative_data_assertions=True,
    )
    assert actual["data_value_symbols"] == _expected_data_value_symbols(snapshot)
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_integer_aliases_remap_one_shared_identity_exactly() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:z))",
            "Declaration(NamedIndividual(:zSource))",
            'DataPropertyAssertion(:z :zSource "01"^^xsd:integer)',
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:a))",
            "Declaration(NamedIndividual(:aSource))",
            'NegativeDataPropertyAssertion(:a :aSource "+1"^^xsd:positiveInteger)',
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    actual = _native_slices_manifest(*_composite_records(composite, (left, right)))

    assert actual == _expected_manifest(
        composite,
        compiled_roots=2,
        include_data_assertions=True,
        include_negative_data_assertions=True,
    )
    assert len(cast(list[object], actual["source_literal_symbols"])) == 2
    assert len(cast(list[object], actual["data_value_symbols"])) == 1
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_decimal_data_assertions_reduce_aliases_and_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "Declaration(DataProperty(:q))",
            "Declaration(NamedIndividual(:i))",
            'DataPropertyAssertion(:p :i "1.0"^^xsd:decimal)',
            'NegativeDataPropertyAssertion(:q :i "+01.00"^^xsd:decimal)',
            'DataPropertyAssertion(:p :i ".25"^^xsd:decimal)',
            'NegativeDataPropertyAssertion(:q :i "0.2500"^^xsd:decimal)',
            'DataPropertyAssertion(:p :i "-0.00"^^xsd:decimal)',
            'NegativeDataPropertyAssertion(:q :i "12."^^xsd:decimal)',
            ('DataPropertyAssertion(:p :i "999999999999999999999999.5"^^xsd:decimal)'),
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(
        snapshot,
        compiled_roots=7,
        include_data_assertions=True,
        include_negative_data_assertions=True,
    )
    assert actual["data_value_symbols"] == _expected_data_value_symbols(snapshot)
    assert len(cast(list[object], actual["source_literal_symbols"])) == 7
    assert len(cast(list[object], actual["data_value_symbols"])) == 5
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_decimal_and_integer_aliases_share_one_identity_exactly() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:z))",
            "Declaration(NamedIndividual(:zSource))",
            'DataPropertyAssertion(:z :zSource "1.00"^^xsd:decimal)',
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:a))",
            "Declaration(NamedIndividual(:aSource))",
            'NegativeDataPropertyAssertion(:a :aSource "+1"^^xsd:integer)',
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    actual = _native_slices_manifest(*_composite_records(composite, (left, right)))

    assert actual == _expected_manifest(
        composite,
        compiled_roots=2,
        include_data_assertions=True,
        include_negative_data_assertions=True,
    )
    assert len(cast(list[object], actual["source_literal_symbols"])) == 2
    assert len(cast(list[object], actual["data_value_symbols"])) == 1
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_rational_data_assertions_reduce_aliases_and_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "Declaration(DataProperty(:q))",
            "Declaration(NamedIndividual(:i))",
            'DataPropertyAssertion(:p :i "6/8"^^owl:rational)',
            'NegativeDataPropertyAssertion(:q :i "3/4"^^owl:rational)',
            'DataPropertyAssertion(:p :i "-0/7"^^owl:rational)',
            'NegativeDataPropertyAssertion(:q :i "+12/4"^^owl:rational)',
            ('DataPropertyAssertion(:p :i "999999999999999999999999/2"^^owl:rational)'),
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(
        snapshot,
        compiled_roots=5,
        include_data_assertions=True,
        include_negative_data_assertions=True,
    )
    assert actual["data_value_symbols"] == _expected_data_value_symbols(snapshot)
    assert len(cast(list[object], actual["source_literal_symbols"])) == 5
    assert len(cast(list[object], actual["data_value_symbols"])) == 4
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_rational_and_decimal_aliases_share_one_identity_exactly() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:z))",
            "Declaration(NamedIndividual(:zSource))",
            'DataPropertyAssertion(:z :zSource "4/2"^^owl:rational)',
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:a))",
            "Declaration(NamedIndividual(:aSource))",
            'NegativeDataPropertyAssertion(:a :aSource "2.0"^^xsd:decimal)',
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    actual = _native_slices_manifest(*_composite_records(composite, (left, right)))

    assert actual == _expected_manifest(
        composite,
        compiled_roots=2,
        include_data_assertions=True,
        include_negative_data_assertions=True,
    )
    assert len(cast(list[object], actual["source_literal_symbols"])) == 2
    assert len(cast(list[object], actual["data_value_symbols"])) == 1
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_ieee_data_assertions_match_scalar_bits_and_signed_zero_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "Declaration(DataProperty(:q))",
            "Declaration(NamedIndividual(:i))",
            'DataPropertyAssertion(:p :i "0"^^xsd:float)',
            'NegativeDataPropertyAssertion(:q :i "-0"^^xsd:float)',
            'DataPropertyAssertion(:p :i "1.5"^^xsd:float)',
            'NegativeDataPropertyAssertion(:q :i "1.50e0"^^xsd:float)',
            'DataPropertyAssertion(:p :i "NaN"^^xsd:float)',
            'NegativeDataPropertyAssertion(:q :i "INF"^^xsd:float)',
            ('DataPropertyAssertion(:p :i "1.401298464324817e-45"^^xsd:float)'),
            'NegativeDataPropertyAssertion(:q :i "-INF"^^xsd:double)',
            'DataPropertyAssertion(:p :i "1.0"^^xsd:double)',
            'NegativeDataPropertyAssertion(:q :i "1e1000"^^xsd:double)',
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(
        snapshot,
        compiled_roots=10,
        include_data_assertions=True,
        include_negative_data_assertions=True,
    )
    assert actual["data_value_symbols"] == _expected_data_value_symbols(snapshot)
    assert len(cast(list[object], actual["source_literal_symbols"])) == 10
    assert len(cast(list[object], actual["data_value_symbols"])) == 9
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


@pytest.mark.parametrize(
    ("datatype", "lexical"),
    [
        ("float", "1.1754943508222875e-38"),
        ("float", "3.4028234663852886e38"),
        ("float", "1.000000059604644775390625"),
        ("float", "1.000000178813934326171875"),
        ("double", "2.2250738585072014e-308"),
        ("double", "1.7976931348623157e308"),
        ("double", "1.00000000000000011102230246251565404236316680908203125"),
        ("double", "4.9406564584124654e-324"),
    ],
)
def test_ieee_normal_subnormal_and_tie_boundaries_match_scalar_exactly(
    datatype: str,
    lexical: str,
) -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "Declaration(NamedIndividual(:i))",
            f'DataPropertyAssertion(:p :i "{lexical}"^^xsd:{datatype})',
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(
        snapshot,
        compiled_roots=1,
        include_data_assertions=True,
    )
    assert actual["data_value_symbols"] == _expected_data_value_symbols(snapshot)
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_generated_ieee_rounding_matrix_matches_scalar_exactly() -> None:
    rng = random.Random(0x1EEE754)
    assertions = []
    for index in range(96):
        datatype = "float" if index % 2 == 0 else "double"
        sign = "-" if rng.randrange(2) else "+"
        fraction = "".join(str(rng.randrange(10)) for _ in range(18))
        exponent_limit = 50 if datatype == "float" else 350
        exponent = rng.randint(-exponent_limit, exponent_limit)
        constructor = "DataPropertyAssertion" if index % 3 else "NegativeDataPropertyAssertion"
        assertions.append(
            f'{constructor}(:p :i "{sign}{index + 1}.{fraction}e{exponent:+d}"^^xsd:{datatype})'
        )
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "Declaration(NamedIndividual(:i))",
            *assertions,
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(
        snapshot,
        compiled_roots=len(assertions),
        include_data_assertions=True,
        include_negative_data_assertions=True,
    )
    assert actual["data_value_symbols"] == _expected_data_value_symbols(snapshot)
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_ieee_lexical_aliases_share_one_identity_exactly() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:z))",
            "Declaration(NamedIndividual(:zSource))",
            'DataPropertyAssertion(:z :zSource "1.5"^^xsd:double)',
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:a))",
            "Declaration(NamedIndividual(:aSource))",
            'NegativeDataPropertyAssertion(:a :aSource "15e-1"^^xsd:double)',
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    actual = _native_slices_manifest(*_composite_records(composite, (left, right)))

    assert actual == _expected_manifest(
        composite,
        compiled_roots=2,
        include_data_assertions=True,
        include_negative_data_assertions=True,
    )
    assert len(cast(list[object], actual["source_literal_symbols"])) == 2
    assert len(cast(list[object], actual["data_value_symbols"])) == 1
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_binary_data_assertions_decode_aliases_and_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "Declaration(DataProperty(:q))",
            "Declaration(NamedIndividual(:i))",
            'DataPropertyAssertion(:p :i " 0Aff "^^xsd:hexBinary)',
            'NegativeDataPropertyAssertion(:q :i "0aFF"^^xsd:hexBinary)',
            'DataPropertyAssertion(:p :i " C v 8 = "^^xsd:base64Binary)',
            'NegativeDataPropertyAssertion(:q :i "Cv8="^^xsd:base64Binary)',
            'DataPropertyAssertion(:p :i ""^^xsd:hexBinary)',
            'NegativeDataPropertyAssertion(:q :i ""^^xsd:base64Binary)',
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(
        snapshot,
        compiled_roots=6,
        include_data_assertions=True,
        include_negative_data_assertions=True,
    )
    assert actual["data_value_symbols"] == _expected_data_value_symbols(snapshot)
    assert len(cast(list[object], actual["source_literal_symbols"])) == 6
    assert len(cast(list[object], actual["data_value_symbols"])) == 4
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_base64_whitespace_aliases_share_one_identity_exactly() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:z))",
            "Declaration(NamedIndividual(:zSource))",
            'DataPropertyAssertion(:z :zSource " Y W J j "^^xsd:base64Binary)',
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:a))",
            "Declaration(NamedIndividual(:aSource))",
            'NegativeDataPropertyAssertion(:a :aSource "YWJj"^^xsd:base64Binary)',
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    actual = _native_slices_manifest(*_composite_records(composite, (left, right)))

    assert actual == _expected_manifest(
        composite,
        compiled_roots=2,
        include_data_assertions=True,
        include_negative_data_assertions=True,
    )
    assert len(cast(list[object], actual["source_literal_symbols"])) == 2
    assert len(cast(list[object], actual["data_value_symbols"])) == 1
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_uri_data_assertions_preserve_spelling_and_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "Declaration(DataProperty(:q))",
            "Declaration(NamedIndividual(:i))",
            'DataPropertyAssertion(:p :i "urn:example:value"^^xsd:anyURI)',
            'NegativeDataPropertyAssertion(:q :i "URN:example:value"^^xsd:anyURI)',
            'DataPropertyAssertion(:p :i "../café?q=one two"^^xsd:anyURI)',
            'NegativeDataPropertyAssertion(:q :i ""^^xsd:anyURI)',
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(
        snapshot,
        compiled_roots=4,
        include_data_assertions=True,
        include_negative_data_assertions=True,
    )
    assert actual["data_value_symbols"] == _expected_data_value_symbols(snapshot)
    assert len(cast(list[object], actual["source_literal_symbols"])) == 4
    assert len(cast(list[object], actual["data_value_symbols"])) == 4
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_uri_spelling_remaps_one_shared_identity_exactly() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:z))",
            "Declaration(NamedIndividual(:zSource))",
            'DataPropertyAssertion(:z :zSource "relative/path"^^xsd:anyURI)',
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:a))",
            "Declaration(NamedIndividual(:aSource))",
            'NegativeDataPropertyAssertion(:a :aSource "relative/path"^^xsd:anyURI)',
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    actual = _native_slices_manifest(*_composite_records(composite, (left, right)))

    assert actual == _expected_manifest(
        composite,
        compiled_roots=2,
        include_data_assertions=True,
        include_negative_data_assertions=True,
    )
    assert len(cast(list[object], actual["source_literal_symbols"])) == 1
    assert len(cast(list[object], actual["data_value_symbols"])) == 1
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_date_time_data_assertions_normalize_aliases_and_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "Declaration(DataProperty(:q))",
            "Declaration(NamedIndividual(:i))",
            'DataPropertyAssertion(:p :i "1970-01-01T00:00:00Z"^^xsd:dateTime)',
            ('NegativeDataPropertyAssertion(:q :i "1970-01-01T00:00:00+00:00"^^xsd:dateTime)'),
            'DataPropertyAssertion(:p :i "1970-01-01T00:00:00"^^xsd:dateTime)',
            ('NegativeDataPropertyAssertion(:q :i "2000-02-29T24:00:00Z"^^xsd:dateTime)'),
            'DataPropertyAssertion(:p :i "2000-03-01T00:00:00Z"^^xsd:dateTime)',
            (
                'NegativeDataPropertyAssertion(:q :i "-0001-01-01T00:00:00.2500-14:00"'
                "^^xsd:dateTime)"
            ),
            ('DataPropertyAssertion(:p :i "2024-01-01T00:00:00+01:30"^^xsd:dateTimeStamp)'),
            ('NegativeDataPropertyAssertion(:q :i "1970-01-01T00:00:00Z"^^xsd:dateTimeStamp)'),
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(
        snapshot,
        compiled_roots=8,
        include_data_assertions=True,
        include_negative_data_assertions=True,
    )
    assert actual["data_value_symbols"] == _expected_data_value_symbols(snapshot)
    assert len(cast(list[object], actual["source_literal_symbols"])) == 8
    assert len(cast(list[object], actual["data_value_symbols"])) == 5
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_date_time_zone_aliases_share_one_identity_exactly() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:z))",
            "Declaration(NamedIndividual(:zSource))",
            'DataPropertyAssertion(:z :zSource "2024-02-29T12:34:56Z"^^xsd:dateTime)',
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:a))",
            "Declaration(NamedIndividual(:aSource))",
            (
                'NegativeDataPropertyAssertion(:a :aSource "2024-02-29T12:34:56+00:00"'
                "^^xsd:dateTimeStamp)"
            ),
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    actual = _native_slices_manifest(*_composite_records(composite, (left, right)))

    assert actual == _expected_manifest(
        composite,
        compiled_roots=2,
        include_data_assertions=True,
        include_negative_data_assertions=True,
    )
    assert len(cast(list[object], actual["source_literal_symbols"])) == 2
    assert len(cast(list[object], actual["data_value_symbols"])) == 1
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_xml_data_assertions_canonicalize_and_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "Declaration(DataProperty(:q))",
            "Declaration(NamedIndividual(:i))",
            ('DataPropertyAssertion(:p :i "<a y=\\"2\\" x=\\"1\\"/>"^^rdf:XMLLiteral)'),
            ('NegativeDataPropertyAssertion(:q :i "<a x=\\"1\\" y=\\"2\\"></a>"^^rdf:XMLLiteral)'),
            (
                'DataPropertyAssertion(:p :i "<a xmlns:p=\\"urn:x\\"><p:b/><p:c/></a>"'
                "^^rdf:XMLLiteral)"
            ),
            (
                'NegativeDataPropertyAssertion(:q :i "<!--top--><a><![CDATA[x<y&z]]>'
                '</a><?pi data?>"^^rdf:XMLLiteral)'
            ),
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(
        snapshot,
        compiled_roots=4,
        include_data_assertions=True,
        include_negative_data_assertions=True,
    )
    assert actual["data_value_symbols"] == _expected_data_value_symbols(snapshot)
    assert len(cast(list[object], actual["source_literal_symbols"])) == 4
    assert len(cast(list[object], actual["data_value_symbols"])) == 3
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_xml_spelling_remaps_one_canonical_identity_exactly() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:z))",
            "Declaration(NamedIndividual(:zSource))",
            ('DataPropertyAssertion(:z :zSource "<a y=\\"2\\" x=\\"1\\"/>"^^rdf:XMLLiteral)'),
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:a))",
            "Declaration(NamedIndividual(:aSource))",
            (
                'NegativeDataPropertyAssertion(:a :aSource "<a x=\\"1\\" y=\\"2\\"></a>"'
                "^^rdf:XMLLiteral)"
            ),
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    actual = _native_slices_manifest(*_composite_records(composite, (left, right)))

    assert actual == _expected_manifest(
        composite,
        compiled_roots=2,
        include_data_assertions=True,
        include_negative_data_assertions=True,
    )
    assert len(cast(list[object], actual["source_literal_symbols"])) == 2
    assert len(cast(list[object], actual["data_value_symbols"])) == 1
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_annotated_named_object_assertions_and_inverse_roles_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "Declaration(AnnotationProperty(:note))",
            "Declaration(AnnotationProperty(:meta))",
            "Declaration(NamedIndividual(:i))",
            "Declaration(NamedIndividual(:j))",
            'ObjectPropertyAssertion(Annotation(Annotation(:meta "nested") :note "left") :p :i :j)',
            'ObjectPropertyAssertion(Annotation(:note "right"@en) :p :i :j)',
            "ObjectPropertyAssertion(Annotation(:note _:source) ObjectInverseOf(:q) :i :j)",
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(
        snapshot,
        compiled_roots=3,
        include_object_assertions=True,
    )
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_annotated_negative_object_assertions_and_inverse_roles_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "Declaration(AnnotationProperty(:note))",
            "Declaration(AnnotationProperty(:meta))",
            "Declaration(NamedIndividual(:i))",
            "Declaration(NamedIndividual(:j))",
            (
                "NegativeObjectPropertyAssertion("
                'Annotation(Annotation(:meta "nested") :note "left") :p :i :j)'
            ),
            'NegativeObjectPropertyAssertion(Annotation(:note "right"@en) :p :i :j)',
            (
                "NegativeObjectPropertyAssertion(Annotation(:note <urn:annotation:value>) "
                "ObjectInverseOf(:q) :i :j)"
            ),
            "ObjectPropertyAssertion(:p :j :i)",
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(
        snapshot,
        compiled_roots=4,
        include_object_assertions=True,
        include_negative_object_assertions=True,
    )
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_anonymous_object_assertions_group_sources_exactly() -> None:
    source = functional(
        "Declaration(ObjectProperty(:p))",
        "Declaration(ObjectProperty(:q))",
        "Declaration(AnnotationProperty(:note))",
        "Declaration(NamedIndividual(:i))",
        "Declaration(NamedIndividual(:j))",
        "ObjectPropertyAssertion(Annotation(:note _:same) :p :i :j)",
        "ObjectPropertyAssertion(Annotation(:note _:same) ObjectInverseOf(:q) :i :j)",
    )
    left = pyowl_core.load_snapshot(source, options=OPTIONS)
    right = pyowl_core.load_snapshot(source, options=OPTIONS)
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    actual = _native_slices_manifest(*_composite_records(composite, (left, right)))

    assert actual == _expected_manifest(
        composite,
        compiled_roots=4,
        include_object_assertions=True,
    )
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_negative_object_assertion_annotations_group_sources_exactly() -> None:
    def source(annotation: str) -> bytes:
        return functional(
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "Declaration(AnnotationProperty(:note))",
            "Declaration(NamedIndividual(:i))",
            "Declaration(NamedIndividual(:j))",
            f'NegativeObjectPropertyAssertion(Annotation(:note "{annotation}") :p :i :j)',
            (
                f'NegativeObjectPropertyAssertion(Annotation(:note "{annotation}") '
                "ObjectInverseOf(:q) :i :j)"
            ),
        )

    left = pyowl_core.load_snapshot(source("left"), options=OPTIONS)
    right = pyowl_core.load_snapshot(source("right"), options=OPTIONS)
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    actual = _native_slices_manifest(*_composite_records(composite, (left, right)))

    assert actual == _expected_manifest(
        composite,
        compiled_roots=4,
        include_negative_object_assertions=True,
    )
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_object_assertions_remap_local_roles_and_individuals_exactly() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(ObjectProperty(:z))",
            "Declaration(NamedIndividual(:zSource))",
            "Declaration(NamedIndividual(:zTarget))",
            "ObjectPropertyAssertion(:z :zSource :zTarget)",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(ObjectProperty(:a))",
            "Declaration(NamedIndividual(:aSource))",
            "Declaration(NamedIndividual(:aTarget))",
            "ObjectPropertyAssertion(ObjectInverseOf(:a) :aSource :aTarget)",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    actual = _native_slices_manifest(*_composite_records(composite, (left, right)))

    assert actual == _expected_manifest(
        composite,
        compiled_roots=2,
        include_object_assertions=True,
    )
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_negative_object_assertions_remap_local_roles_and_individuals_exactly() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(ObjectProperty(:z))",
            "Declaration(NamedIndividual(:zSource))",
            "Declaration(NamedIndividual(:zTarget))",
            "NegativeObjectPropertyAssertion(:z :zSource :zTarget)",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(ObjectProperty(:a))",
            "Declaration(NamedIndividual(:aSource))",
            "Declaration(NamedIndividual(:aTarget))",
            "NegativeObjectPropertyAssertion(ObjectInverseOf(:a) :aSource :aTarget)",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    actual = _native_slices_manifest(*_composite_records(composite, (left, right)))

    assert actual == _expected_manifest(
        composite,
        compiled_roots=2,
        include_negative_object_assertions=True,
    )
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_anonymous_object_assertion_operands_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(ObjectProperty(:p))",
            "Declaration(NamedIndividual(:i))",
            "ObjectPropertyAssertion(:p :i _:anonymous)",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=1,
        include_object_assertions=True,
    )
    assert manifest["deferred_roots"] == 0
    assert manifest["named_individuals"] == [0]
    assert len(cast(list[object], manifest["individual_symbols"])) == 2
    assert len(cast(list[object], manifest["individual_signature"])) == 1
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_anonymous_class_and_data_assertions_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(ObjectProperty(:link))",
            "Declaration(DataProperty(:p))",
            "Declaration(NamedIndividual(:root))",
            "ObjectPropertyAssertion(:link :root _:anonymous)",
            "ClassAssertion(:A _:anonymous)",
            'DataPropertyAssertion(:p _:anonymous "value")',
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=3,
        include_object_assertions=True,
        include_data_assertions=True,
    )
    assert manifest["deferred_roots"] == 0
    assert manifest["named_individuals"] == [0]
    assert len(cast(list[object], manifest["individual_signature"])) == 1
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_anonymous_assertion_operands_remap_scopes_exactly() -> None:
    source = functional(
        "Declaration(ObjectProperty(:p))",
        "ObjectPropertyAssertion(:p _:source _:target)",
    )
    left = pyowl_core.load_snapshot(source, options=OPTIONS)
    right = pyowl_core.load_snapshot(source, options=OPTIONS)
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    manifest = _native_slices_manifest(*_composite_records(composite, (left, right)))

    assert manifest == _expected_manifest(
        composite,
        compiled_roots=2,
        include_object_assertions=True,
    )
    assert manifest["deferred_roots"] == 0
    assert manifest["named_individuals"] == []
    assert len(cast(list[object], manifest["individual_symbols"])) == 4
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


@pytest.mark.parametrize(
    "axiom",
    [
        "NegativeObjectPropertyAssertion(:p :i _:anonymous)",
        'NegativeDataPropertyAssertion(:d _:anonymous "value")',
    ],
)
def test_forbidden_anonymous_negative_assertions_defer_atomically(axiom: str) -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(ObjectProperty(:p))",
            "Declaration(DataProperty(:d))",
            "Declaration(NamedIndividual(:i))",
            axiom,
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest["compiled_roots"] == 0
    assert manifest["deferred_roots"] == 1
    assert manifest["named_individuals"] == [0]
    assert len(cast(list[object], manifest["individual_symbols"])) == 1
    assert len(cast(list[dict[str, object]], manifest["positive_facts"])) == 2
    assert manifest["negative_facts"] == []
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_anonymous_object_constraints_remap_and_group_sources_exactly() -> None:
    source = functional(
        "Declaration(Class(:A))",
        "Declaration(Class(:B))",
        "Declaration(ObjectProperty(:p))",
        "Declaration(ObjectProperty(:q))",
        "Declaration(AnnotationProperty(:note))",
        "ObjectPropertyDomain(Annotation(:note _:same) :p :A)",
        "ObjectPropertyRange(Annotation(:note _:same) ObjectInverseOf(:q) :B)",
    )
    left = pyowl_core.load_snapshot(source, options=OPTIONS)
    right = pyowl_core.load_snapshot(source, options=OPTIONS)
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    actual = _native_slices_manifest(*_composite_records(composite, (left, right)))

    assert actual == _expected_manifest(
        composite,
        compiled_roots=4,
        include_object_constraints=True,
    )
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_object_constraints_remap_distinct_local_role_domains() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(ObjectProperty(:z))",
            "Declaration(AnnotationProperty(:note))",
            "ObjectPropertyDomain(Annotation(:note _:left) :z :A)",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:B))",
            "Declaration(ObjectProperty(:a))",
            "Declaration(AnnotationProperty(:note))",
            "ObjectPropertyRange(Annotation(:note _:right) ObjectInverseOf(:a) :B)",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    actual = _native_slices_manifest(*_composite_records(composite, (left, right)))

    assert actual == _expected_manifest(
        composite,
        compiled_roots=2,
        include_object_constraints=True,
    )
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_anonymous_object_characteristics_group_sources_exactly() -> None:
    source = functional(
        "Declaration(ObjectProperty(:p))",
        "Declaration(ObjectProperty(:q))",
        "Declaration(AnnotationProperty(:note))",
        "FunctionalObjectProperty(Annotation(:note _:same) :p)",
        "InverseFunctionalObjectProperty(Annotation(:note _:same) ObjectInverseOf(:q))",
        "ReflexiveObjectProperty(Annotation(:note _:same) :p)",
    )
    left = pyowl_core.load_snapshot(source, options=OPTIONS)
    right = pyowl_core.load_snapshot(source, options=OPTIONS)
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    actual = _native_slices_manifest(*_composite_records(composite, (left, right)))

    assert actual == _expected_manifest(
        composite,
        compiled_roots=6,
        include_object_characteristics=True,
    )
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_object_characteristics_remap_distinct_local_role_domains() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(ObjectProperty(:z))",
            "FunctionalObjectProperty(:z)",
            "ReflexiveObjectProperty(:z)",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(ObjectProperty(:a))",
            "InverseFunctionalObjectProperty(ObjectInverseOf(:a))",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    actual = _native_slices_manifest(*_composite_records(composite, (left, right)))

    assert actual == _expected_manifest(
        composite,
        compiled_roots=3,
        include_object_characteristics=True,
    )
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_anonymous_data_domains_group_sources_exactly() -> None:
    source = functional(
        "Declaration(Class(:A))",
        "Declaration(Class(:B))",
        "Declaration(DataProperty(:p))",
        "Declaration(DataProperty(:q))",
        "Declaration(AnnotationProperty(:note))",
        "DataPropertyDomain(Annotation(:note _:same) :p :A)",
        "DataPropertyDomain(Annotation(:note _:same) :q :B)",
    )
    left = pyowl_core.load_snapshot(source, options=OPTIONS)
    right = pyowl_core.load_snapshot(source, options=OPTIONS)
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    actual = _native_slices_manifest(*_composite_records(composite, (left, right)))

    assert actual == _expected_manifest(
        composite,
        compiled_roots=4,
        include_data_domains=True,
    )
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_data_domains_remap_distinct_local_role_and_class_domains() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:Z))",
            "Declaration(DataProperty(:z))",
            "DataPropertyDomain(:z :Z)",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(DataProperty(:a))",
            "DataPropertyDomain(:a :A)",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    actual = _native_slices_manifest(*_composite_records(composite, (left, right)))

    assert actual == _expected_manifest(
        composite,
        compiled_roots=2,
        include_data_domains=True,
    )
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_anonymous_data_ranges_group_sources_exactly() -> None:
    source = functional(
        "Declaration(DataProperty(:p))",
        "Declaration(DataProperty(:q))",
        "Declaration(AnnotationProperty(:note))",
        "DataPropertyRange(Annotation(:note _:same) :p xsd:string)",
        "DataPropertyRange(Annotation(:note _:same) :q xsd:integer)",
    )
    left = pyowl_core.load_snapshot(source, options=OPTIONS)
    right = pyowl_core.load_snapshot(source, options=OPTIONS)
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    actual = _native_slices_manifest(*_composite_records(composite, (left, right)))

    assert actual == _expected_manifest(
        composite,
        compiled_roots=4,
        include_data_ranges=True,
    )
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_data_ranges_remap_distinct_local_role_and_datatype_domains() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:z))",
            "DataPropertyRange(:z xsd:string)",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:a))",
            "DataPropertyRange(:a xsd:integer)",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    actual = _native_slices_manifest(*_composite_records(composite, (left, right)))

    assert actual == _expected_manifest(
        composite,
        compiled_roots=2,
        include_data_ranges=True,
    )
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_generated_data_range_definitions_use_global_namespace() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:z))",
            "DataPropertyRange(:z DataUnionOf(xsd:string "
            "DataIntersectionOf(xsd:integer xsd:boolean)))",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:a))",
            "DataPropertyRange(:a DataUnionOf(xsd:string "
            "DataComplementOf(DataUnionOf(DataComplementOf(xsd:integer) "
            "DataComplementOf(xsd:boolean)))))",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    actual = _native_slices_manifest(
        *_composite_records(composite, (left, right)),
        logical_fingerprint=composite.logical_fingerprint.digest,
    )

    assert actual == _expected_manifest(
        composite,
        compiled_roots=2,
        include_data_ranges=True,
        include_generated_data_definitions=True,
    )
    namespace = f":data:{composite.logical_fingerprint.hex}:"
    assert (
        sum(
            namespace in str(value["display"])
            for value in cast(list[dict[str, object]], actual["data_range_symbols"])
            if value["generated"]
        )
        == 2
    )
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_atomic_data_complements_remap_exactly() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:z))",
            "Declaration(Datatype(:Z))",
            "DataPropertyRange(:z DataComplementOf(xsd:string))",
            "DatatypeDefinition(:Z DataComplementOf(xsd:string))",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:a))",
            "Declaration(Datatype(:A))",
            "DataPropertyRange(:a DataComplementOf(xsd:integer))",
            "DatatypeDefinition(:A DataComplementOf(xsd:integer))",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    actual = _native_slices_manifest(*_composite_records(composite, (left, right)))

    assert actual == _expected_manifest(
        composite,
        compiled_roots=4,
        include_data_ranges=True,
        include_datatype_definitions=True,
    )
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_enumerated_and_restricted_data_literals_remap_exactly() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:z))",
            "Declaration(Datatype(:Z))",
            'DataPropertyRange(:z DataOneOf("z"))',
            "DatatypeDefinition(:Z DataComplementOf("
            "DatatypeRestriction(xsd:integer "
            'xsd:minInclusive "10"^^xsd:integer)))',
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:a))",
            "Declaration(Datatype(:A))",
            'DataPropertyRange(:a DataComplementOf(DataOneOf("a")))',
            "DatatypeDefinition(:A DatatypeRestriction(xsd:integer "
            'xsd:maxInclusive "5"^^xsd:integer))',
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    actual = _native_slices_manifest(*_composite_records(composite, (left, right)))

    assert actual == _expected_manifest(
        composite,
        compiled_roots=4,
        include_data_ranges=True,
        include_datatype_definitions=True,
    )
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_datatype_definitions_remap_distinct_local_domains_exactly() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(Datatype(:Z))",
            "Declaration(AnnotationProperty(:note))",
            "DatatypeDefinition(Annotation(:note _:same) :Z xsd:string)",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(Datatype(:A))",
            "Declaration(AnnotationProperty(:note))",
            "DatatypeDefinition(Annotation(:note _:same) :A xsd:integer)",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    actual = _native_slices_manifest(*_composite_records(composite, (left, right)))

    assert actual == _expected_manifest(
        composite,
        compiled_roots=2,
        include_datatype_definitions=True,
    )
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_boolean_datatype_definitions_remap_exactly() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(Datatype(:Z))",
            "DatatypeDefinition(:Z DataUnionOf(xsd:string xsd:integer))",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(Datatype(:A))",
            "DatatypeDefinition(:A DataUnionOf(xsd:string xsd:integer))",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    actual = _native_slices_manifest(*_composite_records(composite, (left, right)))

    assert actual == _expected_manifest(
        composite,
        compiled_roots=2,
        include_datatype_definitions=True,
    )
    assert not any(
        value["generated"] for value in cast(list[dict[str, object]], actual["data_range_symbols"])
    )
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_anonymous_named_keys_group_sources_exactly() -> None:
    source = functional(
        "Declaration(Class(:A))",
        "Declaration(ObjectProperty(:p))",
        "Declaration(DataProperty(:d))",
        "Declaration(AnnotationProperty(:note))",
        "HasKey(Annotation(:note _:same) :A (:p) (:d))",
    )
    left = pyowl_core.load_snapshot(source, options=OPTIONS)
    right = pyowl_core.load_snapshot(source, options=OPTIONS)
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    actual = _native_slices_manifest(*_composite_records(composite, (left, right)))

    assert actual == _expected_manifest(
        composite,
        compiled_roots=2,
        include_keys=True,
    )
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_named_keys_remap_distinct_local_domains_exactly() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:Z))",
            "Declaration(ObjectProperty(:z))",
            "Declaration(DataProperty(:zd))",
            "HasKey(:Z (:z) (:zd))",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(ObjectProperty(:a))",
            "Declaration(DataProperty(:ad))",
            "HasKey(:A (:a) (:ad))",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    actual = _native_slices_manifest(*_composite_records(composite, (left, right)))

    assert actual == _expected_manifest(
        composite,
        compiled_roots=2,
        include_keys=True,
    )
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_anonymous_functional_data_properties_group_sources_exactly() -> None:
    source = functional(
        "Declaration(DataProperty(:p))",
        "Declaration(DataProperty(:q))",
        "Declaration(AnnotationProperty(:note))",
        "FunctionalDataProperty(Annotation(:note _:same) :p)",
        "FunctionalDataProperty(Annotation(:note _:same) :q)",
    )
    left = pyowl_core.load_snapshot(source, options=OPTIONS)
    right = pyowl_core.load_snapshot(source, options=OPTIONS)
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    actual = _native_slices_manifest(*_composite_records(composite, (left, right)))

    assert actual == _expected_manifest(
        composite,
        compiled_roots=4,
        include_data_functionalities=True,
    )
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_functional_data_properties_remap_distinct_local_role_domains() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:z))",
            "FunctionalDataProperty(:z)",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:a))",
            "FunctionalDataProperty(:a)",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    actual = _native_slices_manifest(*_composite_records(composite, (left, right)))

    assert actual == _expected_manifest(
        composite,
        compiled_roots=2,
        include_data_functionalities=True,
    )
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_unsupported_object_cardinality_domain_defers_the_whole_root() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "Declaration(AnnotationProperty(:note))",
            'ObjectPropertyDomain(Annotation(:note "source") :p '
            "ObjectMinCardinality(4294967296 :q :A))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest["compiled_roots"] == 0
    assert manifest["deferred_roots"] == 1
    assert all(
        predicate["kind"] != "object_role"
        for predicate in cast(list[dict[str, object]], manifest["predicates"])
    )
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_unsupported_object_cardinality_data_domain_defers_the_whole_root() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(ObjectProperty(:q))",
            "Declaration(DataProperty(:p))",
            "DataPropertyDomain(:p ObjectMinCardinality(4294967296 :q :A))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest["compiled_roots"] == 0
    assert manifest["deferred_roots"] == 1
    assert all(
        predicate["kind"] != PredicateKind.DATA_ROLE.value
        for predicate in cast(list[dict[str, object]], manifest["predicates"])
    )
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_generated_data_property_range_definitions_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "Declaration(DataProperty(:q))",
            "Declaration(DataProperty(:r))",
            "Declaration(AnnotationProperty(:note))",
            "DataPropertyRange(:p DataUnionOf(xsd:string xsd:integer))",
            'DataPropertyRange(Annotation(:note "same definition") :p '
            "DataUnionOf(xsd:string xsd:integer))",
            "DataPropertyRange(:q DataIntersectionOf(DataComplementOf(xsd:string) xsd:integer))",
            'DataPropertyRange(:r DataUnionOf(DataOneOf("alpha") '
            "DatatypeRestriction(xsd:integer "
            'xsd:minInclusive "1"^^xsd:integer)))',
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=4,
        include_data_ranges=True,
        include_generated_data_definitions=True,
    )
    assert (
        sum(
            bool(value["generated"])
            for value in cast(list[dict[str, object]], manifest["data_range_symbols"])
        )
        == 3
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_recursive_generated_data_range_definitions_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "Declaration(DataProperty(:q))",
            "Declaration(AnnotationProperty(:note))",
            "DataPropertyRange(:p DataUnionOf(xsd:string "
            "DataComplementOf(DataUnionOf(xsd:integer xsd:boolean))))",
            'DataPropertyRange(Annotation(:note "same definitions") :p '
            "DataUnionOf(xsd:string "
            "DataComplementOf(DataUnionOf(xsd:integer xsd:boolean))))",
            "DataPropertyRange(:q DataUnionOf("
            "DataIntersectionOf(xsd:string xsd:integer) "
            "DataComplementOf(DataUnionOf(xsd:boolean "
            "DataComplementOf(xsd:decimal)))))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=3,
        include_data_ranges=True,
        include_generated_data_definitions=True,
    )
    assert (
        sum(
            bool(value["generated"])
            for value in cast(list[dict[str, object]], manifest["data_range_symbols"])
        )
        == 5
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_nested_homogeneous_data_booleans_flatten_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "Declaration(DataProperty(:q))",
            "Declaration(Datatype(:D))",
            "Declaration(Datatype(:E))",
            "DataPropertyRange(:p DataUnionOf(xsd:string DataUnionOf(xsd:integer xsd:boolean)))",
            "DataPropertyRange(:q DataIntersectionOf(xsd:string "
            "DataComplementOf(DataUnionOf(DataComplementOf(xsd:integer) "
            "DataComplementOf(xsd:boolean)))))",
            "DatatypeDefinition(:D DataUnionOf(xsd:string DataUnionOf(xsd:integer xsd:boolean)))",
            "DatatypeDefinition(:E DataIntersectionOf(xsd:string "
            "DataIntersectionOf(xsd:integer xsd:boolean)))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=4,
        include_data_ranges=True,
        include_generated_data_definitions=True,
        include_datatype_definitions=True,
    )
    assert (
        sum(
            bool(value["generated"])
            for value in cast(list[dict[str, object]], manifest["data_range_symbols"])
        )
        == 2
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_data_boolean_complements_normalize_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "Declaration(DataProperty(:q))",
            "Declaration(Datatype(:D))",
            "Declaration(Datatype(:E))",
            "DataPropertyRange(:p DataComplementOf(DataUnionOf(xsd:string xsd:integer)))",
            "DataPropertyRange(:q DataComplementOf(DataComplementOf(DataComplementOf("
            "DataIntersectionOf(xsd:string xsd:integer)))))",
            "DatatypeDefinition(:D DataComplementOf(DataUnionOf(xsd:string xsd:integer)))",
            "DatatypeDefinition(:E DataComplementOf(DataComplementOf("
            "DataIntersectionOf(xsd:string xsd:integer))))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=4,
        include_data_ranges=True,
        include_generated_data_definitions=True,
        include_datatype_definitions=True,
    )
    assert (
        sum(
            bool(value["generated"])
            for value in cast(list[dict[str, object]], manifest["data_range_symbols"])
        )
        == 2
    )
    assert (
        sum(
            predicate["kind"] == PredicateKind.NEGATED_DATA_RANGE.value
            for predicate in cast(list[dict[str, object]], manifest["predicates"])
        )
        == 2
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_mixed_nested_datatype_definition_matches_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Datatype(:D))",
            "DatatypeDefinition(:D DataComplementOf(DataUnionOf(xsd:string "
            "DataIntersectionOf(xsd:integer xsd:boolean))))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=1,
        include_generated_data_definitions=True,
        include_datatype_definitions=True,
    )
    assert (
        sum(
            value["generated"]
            for value in cast(list[dict[str, object]], manifest["data_range_symbols"])
        )
        == 2
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_deep_mixed_nested_datatype_definition_matches_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Datatype(:D))",
            "DatatypeDefinition(:D DataUnionOf(xsd:string "
            "DataIntersectionOf(xsd:integer "
            "DataUnionOf(xsd:boolean xsd:decimal))))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=1,
        include_generated_data_definitions=True,
        include_datatype_definitions=True,
    )
    assert (
        sum(
            value["generated"]
            for value in cast(list[dict[str, object]], manifest["data_range_symbols"])
        )
        == 4
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_boolean_datatype_definitions_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Datatype(:D))",
            "Declaration(Datatype(:E))",
            "Declaration(Datatype(:F))",
            "DatatypeDefinition(:D DataUnionOf(xsd:string xsd:integer))",
            "DatatypeDefinition(:E DataIntersectionOf(DataComplementOf(xsd:string) xsd:integer))",
            'DatatypeDefinition(:F DataUnionOf(DataOneOf("alpha") '
            "DatatypeRestriction(xsd:integer "
            'xsd:minInclusive "1"^^xsd:integer)))',
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=3,
        include_datatype_definitions=True,
    )
    assert not any(
        value["generated"]
        for value in cast(list[dict[str, object]], manifest["data_range_symbols"])
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_recursive_boolean_datatype_definition_matches_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Datatype(:D))",
            "DatatypeDefinition(:D DataUnionOf(xsd:string "
            "DataComplementOf(DataUnionOf(xsd:integer xsd:boolean))))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=1,
        include_generated_data_definitions=True,
        include_datatype_definitions=True,
    )
    assert (
        sum(
            value["generated"]
            for value in cast(list[dict[str, object]], manifest["data_range_symbols"])
        )
        == 2
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_mixed_nested_datatype_definitions_reuse_polarized_dependencies() -> None:
    mixed = (
        "DataIntersectionOf(DataComplementOf(xsd:string) "
        "DataUnionOf(DataComplementOf(xsd:integer) "
        "DataComplementOf(xsd:boolean)))"
    )
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Datatype(:D))",
            "Declaration(Datatype(:E))",
            "Declaration(Datatype(:F))",
            "Declaration(AnnotationProperty(:note))",
            "DatatypeDefinition(:D DataComplementOf(DataUnionOf(xsd:string "
            "DataIntersectionOf(xsd:integer xsd:boolean))))",
            'DatatypeDefinition(Annotation(:note "same") :E '
            "DataComplementOf(DataUnionOf(xsd:string "
            "DataIntersectionOf(xsd:integer xsd:boolean))))",
            f"DatatypeDefinition(:F {mixed})",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest == _expected_manifest(
        snapshot,
        compiled_roots=3,
        include_generated_data_definitions=True,
        include_datatype_definitions=True,
    )
    assert (
        sum(
            value["generated"]
            for value in cast(list[dict[str, object]], manifest["data_range_symbols"])
        )
        == 2
    )
    assert manifest["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_mixed_nested_datatype_definitions_compose_canonically() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(Datatype(:D))",
            "DatatypeDefinition(:D DataComplementOf(DataUnionOf(xsd:string "
            "DataIntersectionOf(xsd:integer xsd:boolean))))",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(Datatype(:E))",
            "DatatypeDefinition(:E DataIntersectionOf("
            "DataComplementOf(xsd:string) "
            "DataUnionOf(DataComplementOf(xsd:integer) "
            "DataComplementOf(xsd:boolean))))",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))
    records = _composite_records(composite, (left, right))

    forward = _native_slices_manifest(
        *records,
        logical_fingerprint=composite.logical_fingerprint.digest,
    )
    reverse = _native_slices_manifest(
        *reversed(records),
        logical_fingerprint=composite.logical_fingerprint.digest,
    )
    expected = _expected_manifest(
        composite,
        compiled_roots=2,
        include_generated_data_definitions=True,
        include_datatype_definitions=True,
    )

    assert forward == reverse == expected
    assert (
        sum(
            value["generated"]
            for value in cast(list[dict[str, object]], forward["data_range_symbols"])
        )
        == 2
    )
    assert forward["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_partially_unsupported_has_key_defers_without_generated_symbols() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "Declaration(DataProperty(:d))",
            "HasKey(ObjectIntersectionOf(:A ObjectMinCardinality(4294967296 :q :B)) (:p) (:d))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest["compiled_roots"] == 0
    assert manifest["deferred_roots"] == 1
    assert not any(
        value["generated"]
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
    )
    assert all(
        predicate["kind"]
        not in {
            PredicateKind.OBJECT_ROLE.value,
            PredicateKind.DATA_ROLE.value,
            PredicateKind.ORDERING_GUARD.value,
        }
        for predicate in cast(list[dict[str, object]], manifest["predicates"])
    )
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_anonymous_annotations_group_normalized_sources_exactly() -> None:
    source = functional(
        "Declaration(Class(:A))",
        "Declaration(Class(:B))",
        "Declaration(Class(:C))",
        "Declaration(AnnotationProperty(:note))",
        "Declaration(NamedIndividual(:i))",
        "Declaration(NamedIndividual(:j))",
        "SubClassOf(Annotation(:note _:same) :A :B)",
        "EquivalentClasses(Annotation(:note _:same) :B :C)",
        "DisjointClasses(Annotation(:note _:same) :A :C)",
        "ClassAssertion(Annotation(:note _:same) :A :i)",
        'SameIndividual(Annotation(:note "identity") :i :j)',
        'DifferentIndividuals(Annotation(:note "identity") :i :j)',
    )
    left = pyowl_core.load_snapshot(source, options=OPTIONS)
    right = pyowl_core.load_snapshot(source, options=OPTIONS)
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))
    records = _composite_records(composite, (left, right))
    assert any(cast(tuple[object, ...], record[3]) for record in records)

    actual = _native_slices_manifest(*records)

    assert actual == _expected_manifest(composite, compiled_roots=10)
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_identity_annotation_variants_group_sources_exactly() -> None:
    def source(annotation: str) -> bytes:
        return functional(
            "Declaration(AnnotationProperty(:note))",
            "Declaration(NamedIndividual(:i))",
            "Declaration(NamedIndividual(:j))",
            f'SameIndividual(Annotation(:note "{annotation}") :i :j)',
            f'DifferentIndividuals(Annotation(:note "{annotation}") :i :j)',
        )

    left = pyowl_core.load_snapshot(source("left"), options=OPTIONS)
    right = pyowl_core.load_snapshot(source("right"), options=OPTIONS)
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    actual = _native_slices_manifest(*_composite_records(composite, (left, right)))

    assert actual == _expected_manifest(composite, compiled_roots=4)
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_unsupported_annotated_object_cardinality_assertion_defers() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(AnnotationProperty(:note))",
            "Declaration(NamedIndividual(:i))",
            'ClassAssertion(Annotation(:note "source") ObjectMinCardinality(4294967296 :p :A) :i)',
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)
    assert manifest["compiled_roots"] == 0
    assert manifest["deferred_roots"] == 1
    assert manifest["named_individuals"] == [0]
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_unsupported_object_cardinality_assertion_defers_without_partial_symbols() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(NamedIndividual(:i))",
            "ClassAssertion(ObjectMinCardinality(4294967296 :p :A) :i)",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest["compiled_roots"] == 0
    assert manifest["deferred_roots"] == 1
    assert all(
        not str(value["display"]).startswith("ObjectComplementOf:")
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
    )
    assert all(
        predicate["kind"] != PredicateKind.NEGATED_CONCEPT.value
        for predicate in cast(list[dict[str, object]], manifest["predicates"])
    )
    assert manifest["negative_facts"] == []
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_unsupported_nominal_assertions_defer_without_partial_symbols() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(NamedIndividual(:a))",
            "Declaration(NamedIndividual(:b))",
            "ClassAssertion(ObjectOneOf(_:anonymous) :a)",
            "ClassAssertion(ObjectComplementOf("
            "ObjectComplementOf(ObjectMinCardinality(4294967296 :p :A))) :b)",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest["compiled_roots"] == 0
    assert manifest["deferred_roots"] == 2
    assert all(
        not str(value["display"]).startswith(("ObjectOneOf:", "ObjectComplementOf:"))
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
    )
    assert all(
        predicate["kind"] not in {PredicateKind.NOMINAL.value, PredicateKind.NEGATED_NOMINAL.value}
        for predicate in cast(list[dict[str, object]], manifest["predicates"])
    )
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_partial_nominal_class_axioms_defer_without_partial_symbols() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(NamedIndividual(:a))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(DataProperty(:data))",
            "SubClassOf(ObjectOneOf(:a) ObjectMinCardinality(4294967296 :p :A))",
            "EquivalentClasses(ObjectOneOf(:a) ObjectMinCardinality(4294967296 :p :A))",
            "DisjointClasses(ObjectOneOf(:a) ObjectMinCardinality(4294967296 :p :A))",
            "ObjectPropertyDomain(:p ObjectComplementOf("
            "ObjectComplementOf(ObjectMinCardinality(4294967296 :p :A))))",
            "DataPropertyDomain(:data ObjectComplementOf("
            "ObjectComplementOf(ObjectMinCardinality(4294967296 :p :A))))",
            "HasKey(ObjectOneOf(_:anonymous) (:p) (:data))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest["compiled_roots"] == 0
    assert manifest["deferred_roots"] == 6
    assert all(
        not str(value["display"]).startswith(("ObjectOneOf:", "ObjectComplementOf:"))
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
    )
    assert all(
        predicate["kind"] not in {PredicateKind.NOMINAL.value, PredicateKind.NEGATED_NOMINAL.value}
        for predicate in cast(list[dict[str, object]], manifest["predicates"])
    )
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


@pytest.mark.parametrize(
    "axiom",
    [
        "SubClassOf(ObjectComplementOf(:A) ObjectMinCardinality(4294967296 :p :B))",
        "SubClassOf(ObjectMinCardinality(4294967296 :p :A) ObjectComplementOf(:B))",
    ],
)
def test_partial_atomic_complement_subclass_defers_without_leaking_symbols(
    axiom: str,
) -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(ObjectProperty(:p))",
            axiom,
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest["compiled_roots"] == 0
    assert manifest["deferred_roots"] == 1
    assert all(
        not str(value["display"]).startswith("ObjectComplementOf:")
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
    )
    assert all(
        predicate["kind"] != PredicateKind.NEGATED_CONCEPT.value
        for predicate in cast(list[dict[str, object]], manifest["predicates"])
    )
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_partial_atomic_complement_equivalence_defers_without_leaking_symbols() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(ObjectProperty(:p))",
            "EquivalentClasses(ObjectComplementOf(:A) ObjectMinCardinality(4294967296 :p :B))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest["compiled_roots"] == 0
    assert manifest["deferred_roots"] == 1
    assert all(
        not str(value["display"]).startswith("ObjectComplementOf:")
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
    )
    assert all(
        predicate["kind"] != PredicateKind.NEGATED_CONCEPT.value
        for predicate in cast(list[dict[str, object]], manifest["predicates"])
    )
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_partial_atomic_complement_disjoint_defers_without_leaking_symbols() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(ObjectProperty(:p))",
            "DisjointClasses(ObjectComplementOf(:A) ObjectMinCardinality(4294967296 :p :B))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest["compiled_roots"] == 0
    assert manifest["deferred_roots"] == 1
    assert all(
        not str(value["display"]).startswith("ObjectComplementOf:")
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
    )
    assert all(
        predicate["kind"] != PredicateKind.NEGATED_CONCEPT.value
        for predicate in cast(list[dict[str, object]], manifest["predicates"])
    )
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_unsupported_object_cardinality_constraints_defer_without_leaks() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "Declaration(DataProperty(:d))",
            "ObjectPropertyDomain(:p ObjectMinCardinality(4294967296 :q :A))",
            "DataPropertyDomain(:d ObjectMinCardinality(4294967296 :q :A))",
            "HasKey(ObjectMinCardinality(4294967296 :q :A) (:p) (:d))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest["compiled_roots"] == 0
    assert manifest["deferred_roots"] == 3
    assert all(
        not str(value["display"]).startswith("ObjectComplementOf:")
        for value in cast(list[dict[str, object]], manifest["class_expression_symbols"])
    )
    assert all(
        predicate["kind"] != PredicateKind.NEGATED_CONCEPT.value
        for predicate in cast(list[dict[str, object]], manifest["predicates"])
    )
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


@pytest.mark.parametrize(
    ("constructor", "predicate_kind"),
    [
        ("SameIndividual", PredicateKind.EQUALITY),
        ("DifferentIndividuals", PredicateKind.INEQUALITY),
    ],
)
def test_anonymous_identity_axiom_defers_the_whole_root_without_partial_fact(
    constructor: str,
    predicate_kind: PredicateKind,
) -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(NamedIndividual(:i))",
            f"{constructor}(:i _:anonymous)",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)
    assert manifest["compiled_roots"] == 0
    assert manifest["deferred_roots"] == 1
    assert manifest["named_individuals"] == [0]
    predicates = cast(list[dict[str, object]], manifest["predicates"])
    assert all(value["kind"] != predicate_kind.value for value in predicates)
    positive_facts = cast(list[dict[str, object]], manifest["positive_facts"])
    assert len(positive_facts) == 2
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_hostile_class_kind_rolls_back_and_valid_retry_is_byte_exact() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "SubClassOf(:A :B)",
        ),
        options=OPTIONS,
    )
    encoded = produce_encoded_structural_view_v2(snapshot)
    buffers = dict(encoded.buffers)
    buffers["logical_fingerprint"] = memoryview(snapshot.logical_fingerprint.digest)
    baseline = native._encoded_named_class_manifest_v1(**buffers)
    scalar_bytes = bytes(buffers["scalar_bytes"])
    assert b"class" in scalar_bytes
    hostile = dict(encoded.buffers)
    hostile["scalar_bytes"] = memoryview(scalar_bytes.replace(b"class", b"xxxxx", 1))

    with pytest.raises(BackendMismatchError) as caught:
        native._validate_encoded_columns_v1(**hostile)
    assert caught.value.code == "NATIVE_ENCODED_VIEW_INVALID"

    # No partially compiled domain, predicate, clause, or provenance table is
    # retained across the failed transaction.
    assert native._encoded_named_class_manifest_v1(**buffers) == baseline


def test_generated_definition_namespace_rejects_malformed_fingerprints() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:C))",
            "SubClassOf(:A ObjectIntersectionOf(:B :C))",
        ),
        options=OPTIONS,
    )
    buffers = dict(produce_encoded_structural_view_v2(snapshot).buffers)
    valid = {
        **buffers,
        "logical_fingerprint": memoryview(snapshot.logical_fingerprint.digest),
    }
    baseline = native._encoded_named_class_manifest_v1(**valid)

    with pytest.raises(BackendMismatchError) as caught:
        native._encoded_named_class_manifest_v1(
            **buffers,
            logical_fingerprint=memoryview(b"x" * 31),
        )
    assert caught.value.code == "NATIVE_ENCODED_VIEW_INVALID"

    with pytest.raises(BackendMismatchError) as caught:
        native._encoded_named_class_manifest_v1(
            **buffers,
            logical_fingerprint=memoryview(bytearray(32)),
        )
    assert caught.value.code == "NATIVE_ENCODED_VIEW_INVALID"

    assert native._encoded_named_class_manifest_v1(**valid) == baseline


def test_hostile_individual_kind_rolls_back_and_valid_retry_is_byte_exact() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(NamedIndividual(:i))",
            "ClassAssertion(:A :i)",
        ),
        options=OPTIONS,
    )
    encoded = produce_encoded_structural_view_v2(snapshot)
    buffers = dict(encoded.buffers)
    buffers["logical_fingerprint"] = memoryview(snapshot.logical_fingerprint.digest)
    baseline = native._encoded_named_class_manifest_v1(**buffers)
    scalar_bytes = bytes(buffers["scalar_bytes"])
    assert b"named_individual" in scalar_bytes
    hostile = dict(encoded.buffers)
    hostile["scalar_bytes"] = memoryview(
        scalar_bytes.replace(b"named_individual", b"xxxxxxxxxxxxxxxx", 1)
    )

    with pytest.raises(BackendMismatchError) as caught:
        native._validate_encoded_columns_v1(**hostile)
    assert caught.value.code == "NATIVE_ENCODED_VIEW_INVALID"

    assert native._encoded_named_class_manifest_v1(**buffers) == baseline
