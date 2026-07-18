"""Deterministic bulk input codec for the private native backend.

The codec deliberately serializes the concrete private IR rather than OWL syntax,
``pickle`` data, or Python object graphs.  Its output is one immutable, versioned,
little-endian byte string suitable for one owned transfer into Rust.

This module is private.  Public OWL values must never depend on these wire records.

SPDX-License-Identifier: LGPL-3.0-or-later
"""

from __future__ import annotations

import hashlib
import json
import math
import struct
from dataclasses import dataclass
from enum import IntEnum
from typing import Final, cast

from pyhermit.backends.protocol import CompiledOntology
from pyhermit.clauses.model import (
    Atom,
    ClauseProgram,
    CompiledDelta,
    CompiledQuery,
    DataConstant,
    DeltaCompatibility,
    DeltaFactIR,
    DLClause,
    Expressivity,
    GroundAtom,
    GroundDisjunctionIR,
    IndividualTerm,
    Predicate,
    PredicateKind,
    ProvenanceEntry,
    RoleAutomatonIR,
    RoleTransitionIR,
    SymbolDomain,
    SymbolKind,
    SymbolValue,
    TermSort,
    Variable,
)
from pyhermit.config import (
    BackendName,
    BlockingMode,
    ExistentialMode,
    FreshEntityPolicy,
    IndividualGrouping,
    ReasonerConfig,
    UnsupportedDatatypePolicy,
)

SCHEMA_VERSION: Final = 1
MAGIC: Final = b"PYHMINP\x00"
HEADER_SIZE: Final = 72
DIRECTORY_RECORD_SIZE: Final = 32
MAX_WIRE_BYTES: Final = 512 * 1024 * 1024
MAX_SECTIONS: Final = 64
U32_NONE: Final = (1 << 32) - 1


class DocumentKind(IntEnum):
    ONTOLOGY = 1
    CONFIG = 2
    QUERY = 3
    DELTA = 4


class SectionKind(IntEnum):
    METADATA = 1
    STRINGS = 2
    BLOBS = 3
    U32_POOL = 4
    PROGRAM = 5
    DOMAINS = 6
    SYMBOLS = 7
    PREDICATES = 8
    TERMS = 9
    ATOMS = 10
    GROUND_ATOMS = 11
    CLAUSES = 12
    DISJUNCTIONS = 13
    PROVENANCE = 14
    DIGESTS = 15
    ROLE = 16
    ROLE_PAIRS = 17
    ROLE_CHAINS = 18
    AUTOMATA = 19
    TRANSITIONS = 20
    LITERALS = 21
    DATATYPE = 22
    EXPRESSIVITY = 23
    ENTITIES = 24
    NAMED_INDIVIDUALS = 25
    DATATYPE_DEFINITIONS = 26
    CONFIG = 32
    QUERY = 33
    DELTA = 34
    DELTA_FACTS = 35
    STRING_REFS = 36


_SYMBOL_KIND: Final = {value: index for index, value in enumerate(SymbolKind)}
_PREDICATE_KIND: Final = {value: index for index, value in enumerate(PredicateKind)}
_SORT: Final = {TermSort.OBJECT: 0, TermSort.DATA: 1}
_DELTA_COMPATIBILITY: Final = {value: index for index, value in enumerate(DeltaCompatibility)}

_BACKEND: Final = {value: index for index, value in enumerate(BackendName)}
_FRESH: Final = {value: index for index, value in enumerate(FreshEntityPolicy)}
_GROUPING: Final = {value: index for index, value in enumerate(IndividualGrouping)}
_UNSUPPORTED_DATATYPE: Final = {
    value: index for index, value in enumerate(UnsupportedDatatypePolicy)
}
_BLOCKING: Final = {value: index for index, value in enumerate(BlockingMode)}
_EXISTENTIAL: Final = {value: index for index, value in enumerate(ExistentialMode)}

_DOMAIN = struct.Struct("<B3xII")
_SYMBOL = struct.Struct("<IBBHIIII")
_PREDICATE = struct.Struct("<IHH10I")
_TERM = struct.Struct("<BBHII")
_ATOM = struct.Struct("<III")
_GROUND_ATOM = struct.Struct("<IIIII")
_CLAUSE = struct.Struct("<I8I")
_DISJUNCTION = struct.Struct("<I4I")
_PROVENANCE = struct.Struct("<IB3xII")
_ROLE = struct.Struct("<10I")
_ROLE_PAIR = struct.Struct("<B3xII")
_ROLE_CHAIN = struct.Struct("<III")
_AUTOMATON = struct.Struct("<7I")
_TRANSITION = struct.Struct("<III")
_LITERAL = struct.Struct("<6I")
_DATATYPE = struct.Struct("<4I")
_EXPRESSIVITY = struct.Struct("<II")
_ENTITY = struct.Struct("<5I")
_PROGRAM = struct.Struct("<12I")
_DELTA_FACT = struct.Struct("<IIIB3x")
_STRING_REF = struct.Struct("<II")
_CONFIG = struct.Struct("<32sdQIH6B4x")


class NativeInputError(ValueError):
    """The private IR cannot be represented by native input schema v1."""


@dataclass(frozen=True, slots=True)
class _Section:
    kind: SectionKind
    count: int
    payload: bytes
    alignment: int = 8


class _Pool:
    __slots__ = ("_data", "_offsets")

    def __init__(self) -> None:
        self._data = bytearray()
        self._offsets: dict[bytes, tuple[int, int]] = {}

    def add(self, value: bytes) -> tuple[int, int]:
        if not isinstance(value, bytes):
            raise TypeError("wire pool values must be bytes")
        known = self._offsets.get(value)
        if known is not None:
            return known
        offset = len(self._data)
        _u32(offset, "pool offset")
        _u32(len(value), "pool length")
        reference = (offset, len(value))
        self._data.extend(value)
        self._offsets[value] = reference
        return reference

    @property
    def bytes(self) -> bytes:
        return bytes(self._data)


class _U32Pool:
    __slots__ = ("values",)

    def __init__(self) -> None:
        self.values: list[int] = []

    def add(self, values: tuple[int, ...] | list[int]) -> tuple[int, int]:
        first = len(self.values)
        _u32(first, "u32-pool offset")
        for value in values:
            _u32(value, "u32-pool value")
        self.values.extend(values)
        return first, len(values)

    @property
    def bytes(self) -> bytes:
        return b"".join(struct.pack("<I", value) for value in self.values)


class _ProgramEncoder:
    """Flatten one already-validated concrete :class:`ClauseProgram`."""

    def __init__(self, program: ClauseProgram) -> None:
        _exact(program, ClauseProgram, "program")
        self.program = program
        self.strings = _Pool()
        self.blobs = _Pool()
        self.u32s = _U32Pool()
        self.digests: list[bytes] = []
        self.domains = bytearray()
        self.symbols = bytearray()
        self.predicates = bytearray()
        self.terms = bytearray()
        self.atoms = bytearray()
        self.ground_atoms = bytearray()
        self.clauses = bytearray()
        self.disjunctions = bytearray()
        self.provenance = bytearray()
        self.role_pairs = bytearray()
        self.role_chains = bytearray()
        self.automata = bytearray()
        self.transitions = bytearray()
        self.literals = bytearray()
        self.datatype_definitions = bytearray()

    def sections(self) -> list[_Section]:
        self._encode_symbols()
        self._encode_predicates()
        positive_first = self._ground_count()
        for fact in self.program.positive_facts:
            self._encode_ground_atom(fact)
        positive_count = self._ground_count() - positive_first
        negative_first = self._ground_count()
        for fact in self.program.negative_facts:
            self._encode_ground_atom(fact)
        negative_count = self._ground_count() - negative_first
        self._encode_clauses()
        self._encode_disjunctions()
        self._encode_provenance()
        role_payload = self._encode_roles()
        datatype_payload = self._encode_datatypes()
        expressivity_payload = self._encode_expressivity()
        summary = _PROGRAM.pack(
            len(self.program.symbols.domains),
            sum(len(domain.values) for domain in self.program.symbols.domains),
            len(self.program.predicates.predicates),
            len(self.program.clauses),
            positive_first,
            positive_count,
            negative_first,
            negative_count,
            len(self.program.ground_disjunctions),
            len(self.program.provenance.entries),
            self._term_count(),
            self._atom_count(),
        )
        return [
            _Section(SectionKind.STRINGS, len(self.strings.bytes), self.strings.bytes, 1),
            _Section(SectionKind.BLOBS, len(self.blobs.bytes), self.blobs.bytes, 1),
            _Section(SectionKind.U32_POOL, len(self.u32s.values), self.u32s.bytes),
            _Section(SectionKind.PROGRAM, 1, summary),
            _Section(SectionKind.DOMAINS, len(self.program.symbols.domains), bytes(self.domains)),
            _Section(
                SectionKind.SYMBOLS,
                sum(len(domain.values) for domain in self.program.symbols.domains),
                bytes(self.symbols),
            ),
            _Section(
                SectionKind.PREDICATES,
                len(self.program.predicates.predicates),
                bytes(self.predicates),
            ),
            _Section(SectionKind.TERMS, self._term_count(), bytes(self.terms)),
            _Section(SectionKind.ATOMS, self._atom_count(), bytes(self.atoms)),
            _Section(SectionKind.GROUND_ATOMS, self._ground_count(), bytes(self.ground_atoms)),
            _Section(SectionKind.CLAUSES, len(self.program.clauses), bytes(self.clauses)),
            _Section(
                SectionKind.DISJUNCTIONS,
                len(self.program.ground_disjunctions),
                bytes(self.disjunctions),
            ),
            _Section(
                SectionKind.PROVENANCE,
                len(self.program.provenance.entries),
                bytes(self.provenance),
            ),
            _Section(SectionKind.DIGESTS, len(self.digests), b"".join(self.digests)),
            _Section(SectionKind.ROLE, 1, role_payload),
            _Section(
                SectionKind.ROLE_PAIRS,
                len(self.program.role_model.simple_inclusions)
                + len(self.program.role_model.data_inclusions),
                bytes(self.role_pairs),
            ),
            _Section(
                SectionKind.ROLE_CHAINS,
                len(self.program.role_model.complex_inclusions),
                bytes(self.role_chains),
            ),
            _Section(
                SectionKind.AUTOMATA,
                len(self.program.role_model.automata),
                bytes(self.automata),
            ),
            _Section(
                SectionKind.TRANSITIONS,
                len(self.transitions) // _TRANSITION.size,
                bytes(self.transitions),
            ),
            _Section(
                SectionKind.LITERALS,
                len(self.program.datatype_model.literal_identities),
                bytes(self.literals),
            ),
            _Section(SectionKind.DATATYPE, 1, datatype_payload),
            _Section(
                SectionKind.DATATYPE_DEFINITIONS,
                len(self.program.datatype_model.datatype_definitions),
                bytes(self.datatype_definitions),
            ),
            _Section(SectionKind.EXPRESSIVITY, 1, expressivity_payload),
        ]

    def _encode_symbols(self) -> None:
        first = 0
        for domain in self.program.symbols.domains:
            _exact(domain, SymbolDomain, "symbol domain")
            self.domains.extend(_DOMAIN.pack(_SYMBOL_KIND[domain.kind], first, len(domain.values)))
            for value in domain.values:
                _exact(value, SymbolValue, "symbol value")
                key = bytes.fromhex(value.key_hex)
                key_offset, key_length = self.blobs.add(key)
                display_offset, display_length = self.strings.add(_utf8(value.display, "display"))
                flags = int(value.generated) | (int(value.query_local) << 1)
                self.symbols.extend(
                    _SYMBOL.pack(
                        value.identifier,
                        _SYMBOL_KIND[domain.kind],
                        flags,
                        0,
                        key_offset,
                        key_length,
                        display_offset,
                        display_length,
                    )
                )
                first += 1

    def _encode_predicates(self) -> None:
        for predicate in self.program.predicates.predicates:
            _exact(predicate, Predicate, "predicate")
            sorts = self.u32s.add([_SORT[value] for value in predicate.argument_sorts])
            annotation = self.u32s.add(list(predicate.annotation))
            internal = (
                (0, 0)
                if predicate.internal_key is None
                else self.strings.add(_utf8(predicate.internal_key, "predicate internal_key"))
            )
            flags = 0
            optional: list[int] = []
            for bit, value in enumerate(
                (
                    predicate.symbol_id,
                    predicate.role_id,
                    predicate.cardinality,
                    predicate.filler_predicate_id,
                )
            ):
                if value is not None:
                    flags |= 1 << bit
                    optional.append(value)
                else:
                    optional.append(U32_NONE)
            if predicate.internal_key is not None:
                flags |= 1 << 4
            self.predicates.extend(
                _PREDICATE.pack(
                    predicate.predicate_id,
                    _PREDICATE_KIND[predicate.kind],
                    flags,
                    sorts[0],
                    sorts[1],
                    *optional,
                    annotation[0],
                    annotation[1],
                    internal[0],
                    internal[1],
                )
            )

    def _encode_term(self, value: object, *, ground: bool) -> None:
        if type(value) is Variable:
            if ground:
                raise NativeInputError("ground wire atoms cannot contain variables")
            self.terms.extend(_TERM.pack(0, _SORT[value.sort], 0, value.index, U32_NONE))
        elif type(value) is IndividualTerm:
            self.terms.extend(
                _TERM.pack(1, _SORT[TermSort.OBJECT], 0, value.individual_id, U32_NONE)
            )
        elif type(value) is DataConstant:
            self.terms.extend(
                _TERM.pack(
                    2,
                    _SORT[TermSort.DATA],
                    0,
                    value.source_literal_id,
                    value.data_identity_id,
                )
            )
        else:
            raise TypeError("term must be a concrete Variable, IndividualTerm, or DataConstant")

    def _encode_atom(self, atom: Atom) -> None:
        _exact(atom, Atom, "atom")
        first = self._term_count()
        for term in atom.arguments:
            self._encode_term(term, ground=False)
        self.atoms.extend(_ATOM.pack(atom.predicate_id, first, len(atom.arguments)))

    def _encode_ground_atom(self, atom: GroundAtom) -> None:
        _exact(atom, GroundAtom, "ground atom")
        first = self._term_count()
        for term in atom.arguments:
            self._encode_term(term, ground=True)
        provenance = self.u32s.add(list(atom.provenance_ids))
        self.ground_atoms.extend(
            _GROUND_ATOM.pack(
                atom.predicate_id,
                first,
                len(atom.arguments),
                provenance[0],
                provenance[1],
            )
        )

    def _encode_clauses(self) -> None:
        for clause in self.program.clauses:
            _exact(clause, DLClause, "clause")
            body_first = self._atom_count()
            for atom in clause.body:
                self._encode_atom(atom)
            head_first = self._atom_count()
            for atom in clause.head:
                self._encode_atom(atom)
            provenance = self.u32s.add(list(clause.provenance_ids))
            join = self.u32s.add(list(clause.join_order))
            self.clauses.extend(
                _CLAUSE.pack(
                    clause.clause_id,
                    body_first,
                    len(clause.body),
                    head_first,
                    len(clause.head),
                    provenance[0],
                    provenance[1],
                    join[0],
                    join[1],
                )
            )

    def _encode_disjunctions(self) -> None:
        for disjunction in self.program.ground_disjunctions:
            _exact(disjunction, GroundDisjunctionIR, "ground disjunction")
            first = self._ground_count()
            for atom in disjunction.disjuncts:
                self._encode_ground_atom(atom)
            provenance = self.u32s.add(list(disjunction.provenance_ids))
            self.disjunctions.extend(
                _DISJUNCTION.pack(
                    disjunction.disjunction_id,
                    first,
                    len(disjunction.disjuncts),
                    provenance[0],
                    provenance[1],
                )
            )

    def _encode_provenance(self) -> None:
        for entry in self.program.provenance.entries:
            _exact(entry, ProvenanceEntry, "provenance entry")
            first = len(self.digests)
            self.digests.extend(_digest(value, "source_sha256") for value in entry.source_sha256)
            self.provenance.extend(
                _PROVENANCE.pack(
                    entry.provenance_id,
                    int(entry.generated),
                    first,
                    len(entry.source_sha256),
                )
            )

    def _encode_roles(self) -> bytes:
        roles = self.program.role_model
        for sub, sup in roles.simple_inclusions:
            self.role_pairs.extend(_ROLE_PAIR.pack(0, sub, sup))
        for sub, sup in roles.data_inclusions:
            self.role_pairs.extend(_ROLE_PAIR.pack(1, sub, sup))
        for chain, target in roles.complex_inclusions:
            first, count = self.u32s.add(list(chain))
            self.role_chains.extend(_ROLE_CHAIN.pack(target, first, count))
        inverse = self.u32s.add(list(roles.inverse_role_ids))
        non_simple = self.u32s.add(list(roles.non_simple_components))
        transition_first = 0
        for automaton in roles.automata:
            _exact(automaton, RoleAutomatonIR, "role automaton")
            finals = self.u32s.add(list(automaton.final_states))
            for transition in automaton.transitions:
                _exact(transition, RoleTransitionIR, "role transition")
                self.transitions.extend(
                    _TRANSITION.pack(
                        transition.source_state,
                        transition.target_state,
                        U32_NONE if transition.role_id is None else transition.role_id,
                    )
                )
            self.automata.extend(
                _AUTOMATON.pack(
                    automaton.component_id,
                    automaton.state_count,
                    automaton.initial_state,
                    finals[0],
                    finals[1],
                    transition_first,
                    len(automaton.transitions),
                )
            )
            transition_first += len(automaton.transitions)
        return _ROLE.pack(
            roles.object_role_count,
            roles.data_property_count,
            inverse[0],
            inverse[1],
            non_simple[0],
            non_simple[1],
            roles.top_object_role_id,
            roles.bottom_object_role_id,
            roles.top_data_property_id,
            roles.bottom_data_property_id,
        )

    def _encode_datatypes(self) -> bytes:
        datatypes = self.program.datatype_model
        semantic = self.strings.add(
            _canonical_json(datatypes.semantic_payload_json, "datatype model")
        )
        for identity in datatypes.literal_identities:
            comparison = self.strings.add(_utf8(identity.comparison_key, "comparison_key"))
            payload = self.strings.add(
                _canonical_json(identity.semantic_payload_json, "literal semantic payload")
            )
            self.literals.extend(
                _LITERAL.pack(
                    identity.source_literal_id,
                    identity.data_identity_id,
                    comparison[0],
                    comparison[1],
                    payload[0],
                    payload[1],
                )
            )
        for left, right in datatypes.datatype_definitions:
            self.datatype_definitions.extend(struct.pack("<II", left, right))
        unknown = self.u32s.add(list(datatypes.unknown_datatype_ids))
        return _DATATYPE.pack(semantic[0], semantic[1], unknown[0], unknown[1])

    def _encode_expressivity(self) -> bytes:
        value: Expressivity = self.program.expressivity
        flags = 0
        for bit, name in enumerate(
            (
                "inverse_roles",
                "nominals",
                "datatypes",
                "unknown_datatypes",
                "complex_roles",
                "number_restrictions",
                "keys",
                "non_horn",
                "bottom_properties",
                "abox",
            )
        ):
            flags |= int(getattr(value, name)) << bit
        return _EXPRESSIVITY.pack(flags, 0)

    def _term_count(self) -> int:
        return len(self.terms) // _TERM.size

    def _atom_count(self) -> int:
        return len(self.atoms) // _ATOM.size

    def _ground_count(self) -> int:
        return len(self.ground_atoms) // _GROUND_ATOM.size


def encode_ontology(ontology: CompiledOntology) -> bytes:
    """Encode a complete concrete ontology envelope into native input v1."""

    _exact(ontology, CompiledOntology, "ontology")
    program = _program_from_ontology(ontology)
    encoder = _ProgramEncoder(program)
    program_sections = encoder.sections()
    metadata = _ontology_metadata(ontology, program)
    entities = bytearray()
    for entity in ontology.declared_entities:
        kind = encoder.strings.add(_utf8(entity.kind, "entity kind"))
        iri = encoder.strings.add(_utf8(entity.iri, "entity IRI"))
        entities.extend(_ENTITY.pack(kind[0], kind[1], iri[0], iri[1], entity.entity_id))
    # Adding entity strings happened after the program sections captured the old string bytes.
    program_sections = _replace_pool_sections(encoder, program_sections)
    named = b"".join(struct.pack("<I", value) for value in ontology.named_individuals)
    return _document(
        DocumentKind.ONTOLOGY,
        [
            _Section(SectionKind.METADATA, 1, metadata),
            *program_sections,
            _Section(SectionKind.ENTITIES, len(ontology.declared_entities), bytes(entities)),
            _Section(SectionKind.NAMED_INDIVIDUALS, len(ontology.named_individuals), named),
        ],
    )


def encode_config(config: ReasonerConfig) -> bytes:
    """Encode semantic configuration for the paired ``create_session`` call.

    Progress and warning callbacks remain Python-side observability hooks.  They are
    intentionally not serialized or callable while Rust runs without the GIL.
    """

    _exact(config, ReasonerConfig, "config")
    flags = (
        int(config.buffer_changes)
        | (int(config.disjunction_learning) << 1)
        | (int(config.force_quasi_order_classification) << 2)
        | (int(config.deterministic) << 3)
        | (int(config.timeout is not None) << 4)
        | (int(config.max_memory_bytes is not None) << 5)
    )
    timeout = 0.0 if config.timeout is None else config.timeout
    maximum = 0 if config.max_memory_bytes is None else config.max_memory_bytes
    if not math.isfinite(timeout) or timeout < 0:
        raise NativeInputError("config timeout is not wire-representable")
    if config.workers > U32_NONE or maximum > (1 << 64) - 1:
        raise NativeInputError("config resource limit exceeds its wire width")
    payload = _CONFIG.pack(
        bytes(32),
        timeout,
        maximum,
        config.workers,
        flags,
        _BACKEND[config.backend],
        _FRESH[config.fresh_entities],
        _GROUPING[config.individual_grouping],
        _UNSUPPORTED_DATATYPE[config.unsupported_datatypes],
        _BLOCKING[config.blocking],
        _EXISTENTIAL[config.existentials],
    )
    return _document(DocumentKind.CONFIG, [_Section(SectionKind.CONFIG, 1, payload)])


def encode_query(query: CompiledQuery) -> bytes:
    """Encode a concrete query and its complete optional overlay program."""

    _exact(query, CompiledQuery, "query")
    strings = _Pool()
    string_refs = bytearray()
    reason = (0, 0) if query.reason is None else strings.add(_utf8(query.reason, "query reason"))
    interpretation_first = 0
    for value in query.interpretation:
        ref = strings.add(_utf8(value, "query interpretation"))
        string_refs.extend(_STRING_REF.pack(*ref))
    flags = int(query.requires_rebuild) | (int(query.program is not None) << 1) | (
        int(query.reason is not None) << 2
    )
    overlay_digest = bytes(32)
    program_sections: list[_Section] = []
    if query.program is not None:
        _exact(query.program, ClauseProgram, "query program")
        overlay_digest = hashlib.sha256(query.program.canonical_bytes()).digest()
        encoder = _ProgramEncoder(query.program)
        program_sections = encoder.sections()
        # Merge query strings into the program's string pool and shift query references.
        shift = len(encoder.strings.bytes)
        merged = encoder.strings.bytes + strings.bytes
        reason = (reason[0] + shift, reason[1]) if query.reason is not None else reason
        shifted_refs = bytearray()
        for offset in range(0, len(string_refs), _STRING_REF.size):
            old, length = _STRING_REF.unpack_from(string_refs, offset)
            shifted_refs.extend(_STRING_REF.pack(old + shift, length))
        string_refs = shifted_refs
        program_sections = [
            _Section(section.kind, len(merged), merged, 1)
            if section.kind is SectionKind.STRINGS
            else section
            for section in program_sections
        ]
        strings_payload = None
    else:
        strings_payload = strings.bytes
    cutoffs = dict(query.first_local_symbols)
    query_payload = struct.pack(
        "<32s32s32sII12I",
        _digest(query.permanent_program_sha256, "permanent_program_sha256"),
        _digest(query.query_hash, "query_hash"),
        overlay_digest,
        query.first_local_predicate_id,
        flags,
        *(cutoffs[kind.value] for kind in SymbolKind),
        reason[0],
        reason[1],
        interpretation_first,
        len(query.interpretation),
    )
    sections = [
        _Section(SectionKind.QUERY, 1, query_payload),
        *program_sections,
        _Section(SectionKind.STRING_REFS, len(query.interpretation), bytes(string_refs)),
    ]
    if strings_payload is not None:
        sections.append(_Section(SectionKind.STRINGS, len(strings_payload), strings_payload, 1))
    return _document(DocumentKind.QUERY, sections)


def encode_delta(delta: CompiledDelta) -> bytes:
    """Encode one concrete compiled delta without consulting Python during apply."""

    _exact(delta, CompiledDelta, "delta")
    strings = _Pool()
    string_refs = bytearray()
    for reason in delta.reasons:
        string_refs.extend(_STRING_REF.pack(*strings.add(_utf8(reason, "delta reason"))))
    digests = [
        *(_digest(value, "addition_sha256") for value in delta.addition_sha256),
        *(_digest(value, "removal_sha256") for value in delta.removal_sha256),
    ]
    u32s = _U32Pool()
    terms = bytearray()
    facts = bytearray()

    def add_term(value: object) -> None:
        if type(value) is IndividualTerm:
            terms.extend(_TERM.pack(1, 0, 0, value.individual_id, U32_NONE))
        elif type(value) is DataConstant:
            terms.extend(_TERM.pack(2, 1, 0, value.source_literal_id, value.data_identity_id))
        else:
            raise TypeError("delta terms must be concrete IndividualTerm or DataConstant")

    for fact in (*delta.fact_additions, *delta.fact_removals):
        _exact(fact, DeltaFactIR, "delta fact")
        first = len(terms) // _TERM.size
        for term in fact.arguments:
            add_term(term)
        facts.extend(
            _DELTA_FACT.pack(fact.predicate_id, first, len(fact.arguments), int(fact.negative))
        )
    addition_count = len(delta.fact_additions)
    payload = struct.pack(
        "<32s32sB3x10I",
        _digest(delta.base_program_sha256, "base_program_sha256"),
        _digest(delta.result_program_sha256, "result_program_sha256"),
        _DELTA_COMPATIBILITY[delta.compatibility],
        0,
        len(delta.addition_sha256),
        len(delta.addition_sha256),
        len(delta.removal_sha256),
        0,
        addition_count,
        addition_count,
        len(delta.fact_removals),
        0,
        len(delta.reasons),
    )
    return _document(
        DocumentKind.DELTA,
        [
            _Section(SectionKind.DELTA, 1, payload),
            _Section(SectionKind.STRINGS, len(strings.bytes), strings.bytes, 1),
            _Section(SectionKind.U32_POOL, len(u32s.values), u32s.bytes),
            _Section(SectionKind.TERMS, len(terms) // _TERM.size, bytes(terms)),
            _Section(SectionKind.DIGESTS, len(digests), b"".join(digests)),
            _Section(SectionKind.DELTA_FACTS, len(facts) // _DELTA_FACT.size, bytes(facts)),
            _Section(SectionKind.STRING_REFS, len(delta.reasons), bytes(string_refs)),
        ],
    )


def _program_from_ontology(ontology: CompiledOntology) -> ClauseProgram:
    # These exact checks prevent a Protocol implementation from smuggling callbacks,
    # mutable records, or alternate semantics through the native boundary.
    from pyhermit.clauses.model import (
        DatatypeModelIR,
        PredicateRegistry,
        ProvenanceTable,
        RoleModelIR,
        SymbolTable,
    )

    _exact(ontology.symbols, SymbolTable, "ontology symbols")
    symbols = cast(SymbolTable, ontology.symbols)
    if symbols.predicates is None:
        raise NativeInputError("ontology symbol table has no predicate registry")
    _exact(symbols.predicates, PredicateRegistry, "ontology predicates")
    predicates = symbols.predicates
    _exact(ontology.role_model, RoleModelIR, "ontology role_model")
    _exact(ontology.datatype_model, DatatypeModelIR, "ontology datatype_model")
    _exact(ontology.expressivity, Expressivity, "ontology expressivity")
    _exact(ontology.provenance, ProvenanceTable, "ontology provenance")
    for value in ontology.clauses:
        _exact(value, DLClause, "ontology clause")
    for values in (ontology.positive_facts, ontology.negative_facts):
        for value in values:
            _exact(value, GroundAtom, "ontology fact")
    for value in ontology.ground_disjunctions:
        _exact(value, GroundDisjunctionIR, "ontology ground disjunction")
    clauses = cast(tuple[DLClause, ...], ontology.clauses)
    positive_facts = cast(tuple[GroundAtom, ...], ontology.positive_facts)
    negative_facts = cast(tuple[GroundAtom, ...], ontology.negative_facts)
    ground_disjunctions = cast(
        tuple[GroundDisjunctionIR, ...], ontology.ground_disjunctions
    )
    return ClauseProgram(
        symbols=symbols,
        predicates=predicates,
        clauses=clauses,
        positive_facts=positive_facts,
        negative_facts=negative_facts,
        ground_disjunctions=ground_disjunctions,
        role_model=cast(RoleModelIR, ontology.role_model),
        datatype_model=cast(DatatypeModelIR, ontology.datatype_model),
        expressivity=cast(Expressivity, ontology.expressivity),
        provenance=cast(ProvenanceTable, ontology.provenance),
    )


def _ontology_metadata(ontology: CompiledOntology, program: ClauseProgram) -> bytes:
    core_package = _utf8(ontology.core_package_version, "core package version")
    # Metadata owns this one short string directly to keep core provenance independent
    # from program symbol-pool layout.
    prefix = bytearray()
    prefix.extend(_digest(ontology.ontology_fingerprint, "ontology_fingerprint"))
    for name in (
        "source_structural_fingerprint",
        "source_logical_fingerprint",
        "source_signature_fingerprint",
    ):
        fingerprint = getattr(ontology, name)
        if fingerprint.algorithm != "sha256" or len(fingerprint.digest) != 32:
            raise NativeInputError(f"{name} must be a 32-byte SHA-256 fingerprint")
        prefix.extend(fingerprint.digest)
    prefix.extend(hashlib.sha256(program.canonical_bytes()).digest())
    for name in (
        "source_structural_fingerprint",
        "source_logical_fingerprint",
        "source_signature_fingerprint",
    ):
        schema = getattr(ontology, name).schema
        _u32(schema, f"{name} schema")
        prefix.extend(struct.pack("<I", schema))
    prefix.extend(struct.pack("<HH", *ontology.core_api_version))
    prefix.extend(struct.pack("<I", ontology.core_model_schema_version))
    prefix.extend(struct.pack("<HH", *ontology.core_wire_format_version))
    prefix.extend(struct.pack("<I", ontology.core_adapter_protocol_version))
    prefix.extend(struct.pack("<I", len(core_package)))
    prefix.extend(core_package)
    return bytes(prefix)


def _replace_pool_sections(encoder: _ProgramEncoder, sections: list[_Section]) -> list[_Section]:
    return [
        _Section(section.kind, len(encoder.strings.bytes), encoder.strings.bytes, 1)
        if section.kind is SectionKind.STRINGS
        else section
        for section in sections
    ]


def _document(kind: DocumentKind, sections: list[_Section]) -> bytes:
    ordered = sorted(sections, key=lambda value: int(value.kind))
    if len(ordered) > MAX_SECTIONS:
        raise NativeInputError("wire document exceeds the section-count limit")
    kinds = [value.kind for value in ordered]
    if len(kinds) != len(set(kinds)):
        raise NativeInputError("wire document contains duplicate sections")
    directory_end = HEADER_SIZE + len(ordered) * DIRECTORY_RECORD_SIZE
    cursor = directory_end
    entries: list[tuple[_Section, int]] = []
    body = bytearray()
    for section in ordered:
        if section.alignment not in (1, 2, 4, 8, 16, 32, 64):
            raise NativeInputError("invalid section alignment")
        padding = (-cursor) % section.alignment
        body.extend(bytes(padding))
        cursor += padding
        entries.append((section, cursor))
        body.extend(section.payload)
        cursor += len(section.payload)
    if cursor > MAX_WIRE_BYTES:
        raise NativeInputError("wire document exceeds the native size limit")
    directory = bytearray()
    for section, offset in entries:
        _u32(section.count, "section count")
        directory.extend(
            struct.pack(
                "<HHIQQII",
                int(section.kind),
                0,
                0,
                offset,
                len(section.payload),
                section.count,
                section.alignment,
            )
        )
    tail = bytes(directory + body)
    header = struct.pack(
        "<8sHHIQQII32s",
        MAGIC,
        SCHEMA_VERSION,
        int(kind),
        0,
        HEADER_SIZE + len(tail),
        HEADER_SIZE,
        len(ordered),
        0,
        hashlib.sha256(tail).digest(),
    )
    return header + tail


def _exact(value: object, expected: type[object], name: str) -> None:
    if type(value) is not expected:
        raise TypeError(f"{name} must be the concrete {expected.__module__}.{expected.__name__}")


def _u32(value: int, name: str) -> None:
    if isinstance(value, bool) or not isinstance(value, int) or not 0 <= value <= U32_NONE:
        raise NativeInputError(f"{name} does not fit unsigned 32-bit wire storage")


def _digest(value: str, name: str) -> bytes:
    if not isinstance(value, str) or len(value) != 64:
        raise NativeInputError(f"{name} must be a lowercase SHA-256 digest")
    try:
        decoded = bytes.fromhex(value)
    except ValueError as error:
        raise NativeInputError(f"{name} must be a lowercase SHA-256 digest") from error
    if decoded.hex() != value:
        raise NativeInputError(f"{name} must be a lowercase SHA-256 digest")
    return decoded


def _utf8(value: str, name: str) -> bytes:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be str")
    return value.encode("utf-8")


def _canonical_json(value: str, name: str) -> bytes:
    encoded = _utf8(value, name)
    try:
        decoded = json.loads(value)
    except json.JSONDecodeError as error:
        raise NativeInputError(f"{name} must contain valid JSON") from error
    canonical = json.dumps(decoded, ensure_ascii=False, separators=(",", ":"), sort_keys=True)
    if canonical != value:
        raise NativeInputError(f"{name} must contain canonical JSON")
    return encoded


__all__ = [
    "MAGIC",
    "MAX_WIRE_BYTES",
    "SCHEMA_VERSION",
    "DocumentKind",
    "NativeInputError",
    "SectionKind",
    "encode_config",
    "encode_delta",
    "encode_ontology",
    "encode_query",
]
