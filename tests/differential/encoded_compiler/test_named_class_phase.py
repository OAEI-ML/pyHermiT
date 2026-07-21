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
from pyowl_core.backends.native_views import produce_encoded_structural_view_v1

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
from pyhermit.encoded_input import ENCODED_NATIVE_FEATURE
from pyhermit.exceptions import BackendMismatchError
from pyhermit.inputs import capture_ontology

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
    buffers = produce_encoded_structural_view_v1(snapshot).buffers
    encoded = native._encoded_named_class_manifest_v1(
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


def _native_slices_manifest(*records: tuple[object, ...]) -> dict[str, object]:
    encoded = native._encoded_named_class_slices_manifest_v1(slices=records)
    return cast(dict[str, object], json.loads(encoded))


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
        assert isinstance(argument, Variable)
        arguments.append({"index": argument.index, "sort": argument.sort.value})
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
        assert isinstance(argument, Variable)
        arguments.append(
            {
                "type": "Variable",
                "index": argument.index,
                "sort": argument.sort.value,
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
    include_data_domains: bool = False,
    include_data_ranges: bool = False,
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
    named_data_ranges = [
        value for value in data_range_domain.values if value.display.startswith("datatype:")
    ]
    data_range_remap = {
        value.identifier: identifier for identifier, value in enumerate(named_data_ranges)
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
        PredicateKind.DISJOINT_GUARD,
        PredicateKind.EQUALITY,
        PredicateKind.INEQUALITY,
        PredicateKind.NAMED_INDIVIDUAL,
        PredicateKind.ORDERING_GUARD,
    }
    constraint_provenance_ids: set[int] = set()
    characteristic_provenance_ids: set[int] = set()
    data_domain_provenance_ids: set[int] = set()
    data_range_provenance_ids: set[int] = set()
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
        or include_data_domains
        or include_data_ranges
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
        if predicates_by_id[atom.predicate_id].kind is PredicateKind.DATA_RANGE
    }
    datatype_definition_predicates = {
        atom.predicate_id
        for clause in program.clauses
        if clause.clause_id in datatype_definition_clauses
        for atom in clause.body + clause.head
        if predicates_by_id[atom.predicate_id].kind is PredicateKind.DATA_RANGE
    }
    selected_data_range_predicates = data_range_predicates | datatype_definition_predicates
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
                if value.kind is PredicateKind.DATA_RANGE and value.symbol_id is not None
                else value.symbol_id
            ),
            "role_id": value.role_id,
            "cardinality": value.cardinality,
            "filler_predicate_id": value.filler_predicate_id,
            "annotation": list(value.annotation),
            "internal_key": value.internal_key,
        }
        for identifier, value in enumerate(fragment_predicates)
    ]

    expected_variable = Variable(0, TermSort.OBJECT)
    projected: list[tuple[bytes, DLClause]] = []
    for clause in program.clauses:
        unary_named_clause = bool(clause.body) and not any(
            atom.arguments != (expected_variable,) for atom in clause.body + clause.head
        )
        if (
            not unary_named_clause
            and clause.clause_id not in constraint_clauses
            and clause.clause_id not in characteristic_clauses
            and clause.clause_id not in data_domain_clauses
            and clause.clause_id not in data_range_clauses
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
        ],
        "data_range_symbols": [
            {**_symbol_payload(value), "identifier": identifier}
            for identifier, value in enumerate(named_data_ranges)
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
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


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
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


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
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


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
    buffers = produce_encoded_structural_view_v1(snapshot).buffers
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
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


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
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


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
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


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
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


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
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


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
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


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
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


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
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


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
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


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
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


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
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


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
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


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
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


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
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


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
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


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
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


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
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


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
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


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
            (
                'NegativeDataPropertyAssertion(:q :i "18446744073709551615"'
                "^^xsd:unsignedLong)"
            ),
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
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


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
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


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
            (
                'DataPropertyAssertion(:p :i "999999999999999999999999.5"'
                "^^xsd:decimal)"
            ),
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
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


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
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


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
            (
                'DataPropertyAssertion(:p :i "999999999999999999999999/2"'
                "^^owl:rational)"
            ),
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
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


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
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


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
            (
                'DataPropertyAssertion(:p :i "1.401298464324817e-45"'
                "^^xsd:float)"
            ),
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
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


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
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


def test_generated_ieee_rounding_matrix_matches_scalar_exactly() -> None:
    rng = random.Random(0x1EEE754)
    assertions = []
    for index in range(96):
        datatype = "float" if index % 2 == 0 else "double"
        sign = "-" if rng.randrange(2) else "+"
        fraction = "".join(str(rng.randrange(10)) for _ in range(18))
        exponent_limit = 50 if datatype == "float" else 350
        exponent = rng.randint(-exponent_limit, exponent_limit)
        constructor = (
            "DataPropertyAssertion" if index % 3 else "NegativeDataPropertyAssertion"
        )
        assertions.append(
            f'{constructor}(:p :i "{sign}{index + 1}.{fraction}e{exponent:+d}"'
            f"^^xsd:{datatype})"
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
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


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
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


@pytest.mark.parametrize(
    ("constructor", "predicate_kind"),
    [
        ("DataPropertyAssertion", PredicateKind.DATA_ROLE),
        ("NegativeDataPropertyAssertion", PredicateKind.NEGATED_DATA_ROLE),
    ],
)
def test_binary_data_assertion_defers_without_a_partial_data_fact(
    constructor: str,
    predicate_kind: PredicateKind,
) -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "Declaration(NamedIndividual(:i))",
            f'{constructor}(:p :i "0A"^^xsd:hexBinary)',
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(snapshot)

    assert actual["compiled_roots"] == 0
    assert actual["deferred_roots"] == 1
    assert actual["data_value_symbols"] == []
    assert all(
        predicate["kind"] != predicate_kind.value
        for predicate in cast(list[dict[str, object]], actual["predicates"])
    )
    assert len(cast(list[dict[str, object]], actual["positive_facts"])) == 2
    assert actual["negative_facts"] == []
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


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
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


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
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


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
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


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
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


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
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


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
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


@pytest.mark.parametrize(
    "constructor",
    ["ObjectPropertyAssertion", "NegativeObjectPropertyAssertion"],
)
def test_anonymous_object_assertion_operand_defers_the_whole_root(constructor: str) -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(ObjectProperty(:p))",
            "Declaration(NamedIndividual(:i))",
            f"{constructor}(:p :i _:anonymous)",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest["compiled_roots"] == 0
    assert manifest["deferred_roots"] == 1
    assert manifest["named_individuals"] == [0]
    assert all(
        predicate["kind"] != PredicateKind.OBJECT_ROLE.value
        for predicate in cast(list[dict[str, object]], manifest["predicates"])
    )
    assert len(cast(list[dict[str, object]], manifest["positive_facts"])) == 2
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


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
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


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
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


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
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


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
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


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
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


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
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


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
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


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
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


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
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


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
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


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
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


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
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


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
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


def test_complex_object_domain_and_range_still_defer_whole_roots() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "Declaration(AnnotationProperty(:note))",
            'ObjectPropertyDomain(Annotation(:note "source") :p ObjectSomeValuesFrom(:q :A))',
            "ObjectPropertyRange(:p ObjectUnionOf(:A :B))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest["compiled_roots"] == 0
    assert manifest["deferred_roots"] == 2
    assert all(
        predicate["kind"] != "object_role"
        for predicate in cast(list[dict[str, object]], manifest["predicates"])
    )
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


def test_complex_data_property_domain_still_defers_the_whole_root() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(ObjectProperty(:q))",
            "Declaration(DataProperty(:p))",
            "DataPropertyDomain(:p ObjectSomeValuesFrom(:q :A))",
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
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


def test_complex_data_property_range_still_defers_the_whole_root() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "DataPropertyRange(:p DataUnionOf(xsd:string xsd:integer))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest["compiled_roots"] == 0
    assert manifest["deferred_roots"] == 1
    assert all(
        predicate["kind"]
        not in {
            PredicateKind.DATA_ROLE.value,
            PredicateKind.DATA_RANGE.value,
        }
        for predicate in cast(list[dict[str, object]], manifest["predicates"])
    )
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


def test_complex_datatype_definition_still_defers_the_whole_root() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Datatype(:D))",
            "DatatypeDefinition(:D DataUnionOf(xsd:string xsd:integer))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest["compiled_roots"] == 0
    assert manifest["deferred_roots"] == 1
    assert all(
        predicate["kind"] != PredicateKind.DATA_RANGE.value
        for predicate in cast(list[dict[str, object]], manifest["predicates"])
    )
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


def test_complex_has_key_still_defers_the_whole_root() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(DataProperty(:d))",
            "HasKey(ObjectIntersectionOf(:A :B) (:p) (:d))",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)

    assert manifest["compiled_roots"] == 0
    assert manifest["deferred_roots"] == 1
    assert all(
        predicate["kind"]
        not in {
            PredicateKind.OBJECT_ROLE.value,
            PredicateKind.DATA_ROLE.value,
            PredicateKind.ORDERING_GUARD.value,
        }
        for predicate in cast(list[dict[str, object]], manifest["predicates"])
    )
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


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
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


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
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


def test_complex_named_class_assertion_still_defers_the_whole_root() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(AnnotationProperty(:note))",
            "Declaration(NamedIndividual(:i))",
            'ClassAssertion(Annotation(:note "source") ObjectSomeValuesFrom(:p :A) :i)',
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)
    assert manifest["compiled_roots"] == 0
    assert manifest["deferred_roots"] == 1
    assert manifest["named_individuals"] == [0]
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


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
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


def test_complex_named_class_root_is_deferred_without_breaking_scalar_fallback() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(ObjectProperty(:p))",
            "SubClassOf(ObjectSomeValuesFrom(:p :A) :B)",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)
    assert manifest["compiled_roots"] == 0
    assert manifest["deferred_roots"] == 1
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


def test_hostile_class_kind_rolls_back_and_valid_retry_is_byte_exact() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "SubClassOf(:A :B)",
        ),
        options=OPTIONS,
    )
    encoded = produce_encoded_structural_view_v1(snapshot)
    buffers = dict(encoded.buffers)
    baseline = native._encoded_named_class_manifest_v1(**buffers)
    scalar_bytes = bytes(buffers["scalar_bytes"])
    assert b"class" in scalar_bytes
    hostile = dict(buffers)
    hostile["scalar_bytes"] = memoryview(scalar_bytes.replace(b"class", b"xxxxx", 1))

    with pytest.raises(BackendMismatchError) as caught:
        native._validate_encoded_columns_v1(**hostile)
    assert caught.value.code == "NATIVE_ENCODED_VIEW_INVALID"

    # No partially compiled domain, predicate, clause, or provenance table is
    # retained across the failed transaction.
    assert native._encoded_named_class_manifest_v1(**buffers) == baseline


def test_hostile_individual_kind_rolls_back_and_valid_retry_is_byte_exact() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(NamedIndividual(:i))",
            "ClassAssertion(:A :i)",
        ),
        options=OPTIONS,
    )
    encoded = produce_encoded_structural_view_v1(snapshot)
    buffers = dict(encoded.buffers)
    baseline = native._encoded_named_class_manifest_v1(**buffers)
    scalar_bytes = bytes(buffers["scalar_bytes"])
    assert b"named_individual" in scalar_bytes
    hostile = dict(buffers)
    hostile["scalar_bytes"] = memoryview(
        scalar_bytes.replace(b"named_individual", b"xxxxxxxxxxxxxxxx", 1)
    )

    with pytest.raises(BackendMismatchError) as caught:
        native._validate_encoded_columns_v1(**hostile)
    assert caught.value.code == "NATIVE_ENCODED_VIEW_INVALID"

    assert native._encoded_named_class_manifest_v1(**buffers) == baseline
