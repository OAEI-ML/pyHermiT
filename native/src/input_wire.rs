//! Complete, allocation-capped decoder for pyHermiT native input schema v1.
//!
//! This module has no `PyO3` dependency.  It consumes the one owned byte copy supplied by
//! the boundary, validates every directory/count/range/enum/sort/reference, and returns
//! language-neutral owned records.  OWL syntax, Python callbacks, pickle, bincode, and
//! Rust layout never cross this boundary.
// SPDX-License-Identifier: LGPL-3.0-or-later

#![forbid(unsafe_code)]
#![allow(
    clippy::module_name_repetitions,
    clippy::match_same_arms,
    clippy::struct_field_names,
    clippy::too_many_arguments,
    clippy::too_many_lines,
    clippy::struct_excessive_bools
)]

use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fmt::{Display, Formatter};

use serde::Serialize;
use sha2::{Digest, Sha256};

pub const INPUT_SCHEMA_VERSION: u16 = 1;
pub const INPUT_MAGIC: &[u8; 8] = b"PYHMINP\0";
pub const INPUT_HEADER_SIZE: usize = 72;
pub const INPUT_DIRECTORY_RECORD_SIZE: usize = 32;
pub const INPUT_MAX_WIRE_BYTES: usize = 512 * 1024 * 1024;
pub const INPUT_MAX_SECTIONS: u32 = 64;
const U32_NONE: u32 = u32::MAX;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InputWireError {
    pub code: &'static str,
    pub message: String,
}

impl InputWireError {
    fn wire(message: impl Into<String>) -> Self {
        Self {
            code: "NATIVE_INPUT_WIRE",
            message: message.into(),
        }
    }

    fn version(message: impl Into<String>) -> Self {
        Self {
            code: "NATIVE_INPUT_VERSION",
            message: message.into(),
        }
    }

    fn resource(message: impl Into<String>) -> Self {
        Self {
            code: "NATIVE_INPUT_RESOURCE_LIMIT",
            message: message.into(),
        }
    }
}

impl Display for InputWireError {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> std::fmt::Result {
        write!(formatter, "{}: {}", self.code, self.message)
    }
}

impl Error for InputWireError {}

pub type InputResult<T> = Result<T, InputWireError>;

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct DecodeLimits {
    pub max_wire_bytes: usize,
    pub max_sections: u32,
    pub max_records_per_section: u32,
    pub max_string_bytes: usize,
}

impl Default for DecodeLimits {
    fn default() -> Self {
        Self {
            max_wire_bytes: INPUT_MAX_WIRE_BYTES,
            max_sections: INPUT_MAX_SECTIONS,
            max_records_per_section: 16_000_000,
            max_string_bytes: 256 * 1024 * 1024,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(u16)]
enum DocumentKind {
    Ontology = 1,
    Config = 2,
    Query = 3,
    Delta = 4,
}

impl DocumentKind {
    fn parse(value: u16) -> InputResult<Self> {
        match value {
            1 => Ok(Self::Ontology),
            2 => Ok(Self::Config),
            3 => Ok(Self::Query),
            4 => Ok(Self::Delta),
            _ => Err(InputWireError::version(format!(
                "input document kind {value} is unsupported"
            ))),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
#[repr(u16)]
enum SectionKind {
    Metadata = 1,
    Strings = 2,
    Blobs = 3,
    U32Pool = 4,
    Program = 5,
    Domains = 6,
    Symbols = 7,
    Predicates = 8,
    Terms = 9,
    Atoms = 10,
    GroundAtoms = 11,
    Clauses = 12,
    Disjunctions = 13,
    Provenance = 14,
    Digests = 15,
    Role = 16,
    RolePairs = 17,
    RoleChains = 18,
    Automata = 19,
    Transitions = 20,
    Literals = 21,
    Datatype = 22,
    Expressivity = 23,
    Entities = 24,
    NamedIndividuals = 25,
    DatatypeDefinitions = 26,
    Config = 32,
    Query = 33,
    Delta = 34,
    DeltaFacts = 35,
    StringRefs = 36,
}

impl SectionKind {
    const fn parse(value: u16) -> Option<Self> {
        match value {
            1 => Some(Self::Metadata),
            2 => Some(Self::Strings),
            3 => Some(Self::Blobs),
            4 => Some(Self::U32Pool),
            5 => Some(Self::Program),
            6 => Some(Self::Domains),
            7 => Some(Self::Symbols),
            8 => Some(Self::Predicates),
            9 => Some(Self::Terms),
            10 => Some(Self::Atoms),
            11 => Some(Self::GroundAtoms),
            12 => Some(Self::Clauses),
            13 => Some(Self::Disjunctions),
            14 => Some(Self::Provenance),
            15 => Some(Self::Digests),
            16 => Some(Self::Role),
            17 => Some(Self::RolePairs),
            18 => Some(Self::RoleChains),
            19 => Some(Self::Automata),
            20 => Some(Self::Transitions),
            21 => Some(Self::Literals),
            22 => Some(Self::Datatype),
            23 => Some(Self::Expressivity),
            24 => Some(Self::Entities),
            25 => Some(Self::NamedIndividuals),
            26 => Some(Self::DatatypeDefinitions),
            32 => Some(Self::Config),
            33 => Some(Self::Query),
            34 => Some(Self::Delta),
            35 => Some(Self::DeltaFacts),
            36 => Some(Self::StringRefs),
            _ => None,
        }
    }

    const fn record_size(self) -> Option<usize> {
        match self {
            Self::Metadata => None,
            Self::Strings | Self::Blobs => Some(1),
            Self::U32Pool | Self::NamedIndividuals => Some(4),
            Self::Program => Some(48),
            Self::Domains => Some(12),
            Self::Symbols => Some(24),
            Self::Predicates => Some(48),
            Self::Terms => Some(12),
            Self::Atoms => Some(12),
            Self::GroundAtoms => Some(20),
            Self::Clauses => Some(36),
            Self::Disjunctions => Some(20),
            Self::Provenance => Some(16),
            Self::Digests => Some(32),
            Self::Role => Some(40),
            Self::RolePairs => Some(12),
            Self::RoleChains => Some(12),
            Self::Automata => Some(28),
            Self::Transitions => Some(12),
            Self::Literals => Some(24),
            Self::Datatype => Some(16),
            Self::Expressivity => Some(8),
            Self::Entities => Some(20),
            Self::DatatypeDefinitions | Self::StringRefs => Some(8),
            Self::Config => Some(64),
            Self::Query => Some(152),
            Self::Delta => Some(108),
            Self::DeltaFacts => Some(16),
        }
    }
}

#[derive(Clone, Copy, Debug)]
struct Section {
    offset: usize,
    length: usize,
    count: u32,
}

#[derive(Debug)]
struct Document {
    bytes: Vec<u8>,
    kind: DocumentKind,
    sections: BTreeMap<SectionKind, Section>,
}

impl Document {
    fn parse(bytes: Vec<u8>, expected: DocumentKind, limits: &DecodeLimits) -> InputResult<Self> {
        if bytes.len() > limits.max_wire_bytes || bytes.len() > INPUT_MAX_WIRE_BYTES {
            return Err(InputWireError::resource(
                "input document exceeds the configured byte limit",
            ));
        }
        let header = bytes
            .get(..INPUT_HEADER_SIZE)
            .ok_or_else(|| InputWireError::wire("input header is truncated"))?;
        if header.get(..8) != Some(INPUT_MAGIC.as_slice()) {
            return Err(InputWireError::wire("input magic is invalid"));
        }
        let schema = read_u16(header, 8)?;
        if schema != INPUT_SCHEMA_VERSION {
            return Err(InputWireError::version(format!(
                "input schema {schema} is incompatible with {INPUT_SCHEMA_VERSION}"
            )));
        }
        let kind = DocumentKind::parse(read_u16(header, 10)?)?;
        if kind != expected {
            return Err(InputWireError::wire(
                "input document kind does not match the operation",
            ));
        }
        if read_u32(header, 12)? != 0 || read_u32(header, 36)? != 0 {
            return Err(InputWireError::version(
                "input header flags or reserved bits are nonzero",
            ));
        }
        if u64_to_usize(read_u64(header, 16)?, "total length")? != bytes.len() {
            return Err(InputWireError::wire(
                "input total length does not match its buffer",
            ));
        }
        if u64_to_usize(read_u64(header, 24)?, "directory offset")? != INPUT_HEADER_SIZE {
            return Err(InputWireError::wire(
                "input directory offset is noncanonical",
            ));
        }
        let section_count = read_u32(header, 32)?;
        if section_count > limits.max_sections || section_count > INPUT_MAX_SECTIONS {
            return Err(InputWireError::resource(
                "input section count exceeds the configured limit",
            ));
        }
        let directory_length = usize::try_from(section_count)
            .ok()
            .and_then(|count| count.checked_mul(INPUT_DIRECTORY_RECORD_SIZE))
            .ok_or_else(|| InputWireError::wire("input directory length overflows"))?;
        let directory_end = INPUT_HEADER_SIZE
            .checked_add(directory_length)
            .ok_or_else(|| InputWireError::wire("input directory end overflows"))?;
        if directory_end > bytes.len() {
            return Err(InputWireError::wire(
                "input directory lies outside the buffer",
            ));
        }
        let expected_hash = header
            .get(40..72)
            .ok_or_else(|| InputWireError::wire("input content hash is truncated"))?;
        if Sha256::digest(&bytes[INPUT_HEADER_SIZE..]).as_slice() != expected_hash {
            return Err(InputWireError::wire("input content hash does not match"));
        }

        let mut sections = BTreeMap::new();
        let mut coverage = Vec::new();
        coverage
            .try_reserve_exact(usize::try_from(section_count).unwrap_or(0))
            .map_err(|_| InputWireError::resource("input directory allocation failed"))?;
        for index in 0..section_count {
            let start = INPUT_HEADER_SIZE
                .checked_add(
                    usize::try_from(index)
                        .ok()
                        .and_then(|value| value.checked_mul(INPUT_DIRECTORY_RECORD_SIZE))
                        .ok_or_else(|| InputWireError::wire("directory index overflows"))?,
                )
                .ok_or_else(|| InputWireError::wire("directory record offset overflows"))?;
            let record = bytes
                .get(start..start + INPUT_DIRECTORY_RECORD_SIZE)
                .ok_or_else(|| InputWireError::wire("directory record is truncated"))?;
            let raw_kind = read_u16(record, 0)?;
            let flags = read_u16(record, 2)?;
            let kind = SectionKind::parse(raw_kind);
            if flags & !1 != 0 || read_u32(record, 4)? != 0 {
                return Err(InputWireError::version(
                    "input section flags or reserved bits are nonzero",
                ));
            }
            if kind.is_none() && flags & 1 == 0 {
                return Err(InputWireError::version(format!(
                    "required input section {raw_kind} is unknown"
                )));
            }
            if kind.is_some() && flags != 0 {
                return Err(InputWireError::version(
                    "known input section cannot be marked optional",
                ));
            }
            let offset = u64_to_usize(read_u64(record, 8)?, "section offset")?;
            let length = u64_to_usize(read_u64(record, 16)?, "section length")?;
            let count = read_u32(record, 24)?;
            if !matches!(kind, Some(SectionKind::Strings | SectionKind::Blobs))
                && count > limits.max_records_per_section
            {
                return Err(InputWireError::resource(format!(
                    "input {kind:?} record count exceeds the configured limit"
                )));
            }
            let alignment = read_u32(record, 28)?;
            if alignment == 0 || !alignment.is_power_of_two() || alignment > 64 {
                return Err(InputWireError::wire("input section alignment is invalid"));
            }
            if offset % usize::try_from(alignment).unwrap_or(usize::MAX) != 0 {
                return Err(InputWireError::wire("input section offset is misaligned"));
            }
            let end = offset
                .checked_add(length)
                .ok_or_else(|| InputWireError::wire("input section end overflows"))?;
            if offset < directory_end || end > bytes.len() {
                return Err(InputWireError::wire(
                    "input section lies outside the payload",
                ));
            }
            if let Some(record_size) = kind.and_then(SectionKind::record_size) {
                let expected_length = usize::try_from(count)
                    .ok()
                    .and_then(|value| value.checked_mul(record_size))
                    .ok_or_else(|| InputWireError::wire("input record byte count overflows"))?;
                if expected_length != length {
                    return Err(InputWireError::wire(format!(
                        "input {kind:?} count does not match its byte length"
                    )));
                }
            } else if kind == Some(SectionKind::Metadata) && count != 1 {
                return Err(InputWireError::wire(
                    "variable metadata section must declare one record",
                ));
            }
            if kind == Some(SectionKind::Strings) && length > limits.max_string_bytes {
                return Err(InputWireError::resource(
                    "input string pool exceeds the configured limit",
                ));
            }
            if let Some(kind) = kind {
                if sections
                    .insert(
                        kind,
                        Section {
                            offset,
                            length,
                            count,
                        },
                    )
                    .is_some()
                {
                    return Err(InputWireError::wire("input section kind is duplicated"));
                }
            }
            coverage.push((offset, end));
        }
        coverage.sort_unstable();
        let mut cursor = directory_end;
        for (start, end) in coverage {
            if start < cursor {
                return Err(InputWireError::wire("input sections overlap"));
            }
            if bytes[cursor..start].iter().any(|value| *value != 0) {
                return Err(InputWireError::wire("input alignment padding is nonzero"));
            }
            cursor = end;
        }
        if cursor != bytes.len() {
            return Err(InputWireError::wire(
                "input document has unreferenced trailing bytes",
            ));
        }
        Ok(Self {
            bytes,
            kind,
            sections,
        })
    }

    fn require(&self, kind: SectionKind) -> InputResult<&[u8]> {
        let section = self
            .sections
            .get(&kind)
            .ok_or_else(|| InputWireError::wire(format!("input section {kind:?} is missing")))?;
        self.bytes
            .get(section.offset..section.offset + section.length)
            .ok_or_else(|| InputWireError::wire("validated input section became unavailable"))
    }

    fn count(&self, kind: SectionKind) -> InputResult<u32> {
        self.sections
            .get(&kind)
            .map(|section| section.count)
            .ok_or_else(|| InputWireError::wire(format!("input section {kind:?} is missing")))
    }

    fn reject_unexpected(&self, allowed: &[SectionKind]) -> InputResult<()> {
        if self.sections.keys().any(|kind| !allowed.contains(kind)) {
            return Err(InputWireError::version(format!(
                "input {:?} document contains a section not valid for that document",
                self.kind
            )));
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize)]
#[repr(u8)]
pub enum SymbolKind {
    Entity = 0,
    ClassExpression = 1,
    DataRange = 2,
    ObjectRole = 3,
    DataProperty = 4,
    Individual = 5,
    SourceLiteral = 6,
    DataValue = 7,
}

impl SymbolKind {
    fn parse(value: u8) -> InputResult<Self> {
        match value {
            0 => Ok(Self::Entity),
            1 => Ok(Self::ClassExpression),
            2 => Ok(Self::DataRange),
            3 => Ok(Self::ObjectRole),
            4 => Ok(Self::DataProperty),
            5 => Ok(Self::Individual),
            6 => Ok(Self::SourceLiteral),
            7 => Ok(Self::DataValue),
            _ => Err(InputWireError::wire("symbol kind discriminant is invalid")),
        }
    }

    const fn index(self) -> usize {
        self as usize
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize)]
#[repr(u8)]
pub enum TermSort {
    Object = 0,
    Data = 1,
}

impl TermSort {
    fn parse(value: u8) -> InputResult<Self> {
        match value {
            0 => Ok(Self::Object),
            1 => Ok(Self::Data),
            _ => Err(InputWireError::wire("term sort discriminant is invalid")),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[repr(u16)]
pub enum PredicateKind {
    Concept = 0,
    NegatedConcept = 1,
    Nominal = 2,
    NegatedNominal = 3,
    ObjectRole = 4,
    NegatedObjectRole = 5,
    DataRole = 6,
    NegatedDataRole = 7,
    DataRange = 8,
    NegatedDataRange = 9,
    Equality = 10,
    Inequality = 11,
    AtLeastObject = 12,
    AtLeastData = 13,
    AnnotatedEquality = 14,
    AutomatonState = 15,
    DisjointGuard = 16,
    OrderingGuard = 17,
    NamedIndividual = 18,
}

impl PredicateKind {
    fn parse(value: u16) -> InputResult<Self> {
        match value {
            0 => Ok(Self::Concept),
            1 => Ok(Self::NegatedConcept),
            2 => Ok(Self::Nominal),
            3 => Ok(Self::NegatedNominal),
            4 => Ok(Self::ObjectRole),
            5 => Ok(Self::NegatedObjectRole),
            6 => Ok(Self::DataRole),
            7 => Ok(Self::NegatedDataRole),
            8 => Ok(Self::DataRange),
            9 => Ok(Self::NegatedDataRange),
            10 => Ok(Self::Equality),
            11 => Ok(Self::Inequality),
            12 => Ok(Self::AtLeastObject),
            13 => Ok(Self::AtLeastData),
            14 => Ok(Self::AnnotatedEquality),
            15 => Ok(Self::AutomatonState),
            16 => Ok(Self::DisjointGuard),
            17 => Ok(Self::OrderingGuard),
            18 => Ok(Self::NamedIndividual),
            _ => Err(InputWireError::wire(
                "predicate kind discriminant is invalid",
            )),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DecodedFingerprint {
    pub schema: u32,
    pub digest: [u8; 32],
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct OntologyMetadata {
    pub ontology_fingerprint: [u8; 32],
    pub structural_fingerprint: DecodedFingerprint,
    pub logical_fingerprint: DecodedFingerprint,
    pub signature_fingerprint: DecodedFingerprint,
    pub program_sha256: [u8; 32],
    pub core_package_version: String,
    pub core_api_version: (u16, u16),
    pub core_model_schema_version: u32,
    pub core_wire_format_version: (u16, u16),
    pub core_adapter_protocol_version: u32,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct DecodedSymbolValue {
    pub identifier: u32,
    pub key: Vec<u8>,
    pub display: String,
    pub generated: bool,
    pub query_local: bool,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct DecodedSymbolDomain {
    pub kind: SymbolKind,
    pub values: Vec<DecodedSymbolValue>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct DecodedPredicate {
    pub predicate_id: u32,
    pub kind: PredicateKind,
    pub argument_sorts: Vec<TermSort>,
    pub symbol_id: Option<u32>,
    pub role_id: Option<u32>,
    pub cardinality: Option<u32>,
    pub filler_predicate_id: Option<u32>,
    pub annotation: Vec<u32>,
    pub internal_key: Option<String>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub enum DecodedTerm {
    Variable {
        index: u32,
        sort: TermSort,
    },
    Individual {
        individual_id: u32,
    },
    Data {
        source_literal_id: u32,
        data_identity_id: u32,
    },
}

impl DecodedTerm {
    const fn sort(&self) -> TermSort {
        match self {
            Self::Variable { sort, .. } => *sort,
            Self::Individual { .. } => TermSort::Object,
            Self::Data { .. } => TermSort::Data,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct DecodedAtom {
    pub predicate_id: u32,
    pub arguments: Vec<DecodedTerm>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct DecodedGroundAtom {
    pub predicate_id: u32,
    pub arguments: Vec<DecodedTerm>,
    pub provenance_ids: Vec<u32>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct DecodedClause {
    pub clause_id: u32,
    pub body: Vec<DecodedAtom>,
    pub head: Vec<DecodedAtom>,
    pub provenance_ids: Vec<u32>,
    pub join_order: Vec<u32>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct DecodedGroundDisjunction {
    pub disjunction_id: u32,
    pub disjuncts: Vec<DecodedGroundAtom>,
    pub provenance_ids: Vec<u32>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct DecodedProvenanceEntry {
    pub provenance_id: u32,
    pub source_sha256: Vec<[u8; 32]>,
    pub generated: bool,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct DecodedRoleAutomaton {
    pub component_id: u32,
    pub state_count: u32,
    pub initial_state: u32,
    pub final_states: Vec<u32>,
    pub transitions: Vec<DecodedRoleTransition>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct DecodedRoleTransition {
    pub source_state: u32,
    pub target_state: u32,
    pub role_id: Option<u32>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct DecodedRoleModel {
    pub object_role_count: u32,
    pub data_property_count: u32,
    pub inverse_role_ids: Vec<u32>,
    pub simple_inclusions: Vec<(u32, u32)>,
    pub data_inclusions: Vec<(u32, u32)>,
    pub complex_inclusions: Vec<(Vec<u32>, u32)>,
    pub non_simple_components: Vec<u32>,
    pub automata: Vec<DecodedRoleAutomaton>,
    pub top_object_role_id: u32,
    pub bottom_object_role_id: u32,
    pub top_data_property_id: u32,
    pub bottom_data_property_id: u32,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct DecodedLiteralIdentity {
    pub source_literal_id: u32,
    pub data_identity_id: u32,
    pub comparison_key: String,
    pub semantic_payload_json: String,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct DecodedDatatypeModel {
    pub literal_identities: Vec<DecodedLiteralIdentity>,
    pub datatype_definitions: Vec<(u32, u32)>,
    pub unknown_datatype_ids: Vec<u32>,
    pub semantic_payload_json: String,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
pub struct DecodedExpressivity {
    pub inverse_roles: bool,
    pub nominals: bool,
    pub datatypes: bool,
    pub unknown_datatypes: bool,
    pub complex_roles: bool,
    pub number_restrictions: bool,
    pub keys: bool,
    pub non_horn: bool,
    pub bottom_properties: bool,
    pub abox: bool,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct DecodedProgram {
    pub symbol_domains: Vec<DecodedSymbolDomain>,
    pub predicates: Vec<DecodedPredicate>,
    pub clauses: Vec<DecodedClause>,
    pub positive_facts: Vec<DecodedGroundAtom>,
    pub negative_facts: Vec<DecodedGroundAtom>,
    pub ground_disjunctions: Vec<DecodedGroundDisjunction>,
    pub role_model: DecodedRoleModel,
    pub datatype_model: DecodedDatatypeModel,
    pub expressivity: DecodedExpressivity,
    pub provenance: Vec<DecodedProvenanceEntry>,
}

impl DecodedProgram {
    #[must_use]
    pub fn domain(&self, kind: SymbolKind) -> Option<&DecodedSymbolDomain> {
        self.symbol_domains
            .iter()
            .find(|domain| domain.kind == kind)
    }
}

/// Validate an already-owned decoded program with the same cross-reference
/// contract used by the binary decoder.
///
/// Direct structural compilation never passes through the private input wire,
/// so all producers converge here before a program may become session-owned.
pub(crate) fn validate_decoded_program(program: &DecodedProgram) -> InputResult<()> {
    let expected_domains = [
        SymbolKind::ClassExpression,
        SymbolKind::DataProperty,
        SymbolKind::DataRange,
        SymbolKind::DataValue,
        SymbolKind::Entity,
        SymbolKind::Individual,
        SymbolKind::ObjectRole,
        SymbolKind::SourceLiteral,
    ];
    if program
        .symbol_domains
        .iter()
        .map(|domain| domain.kind)
        .ne(expected_domains)
    {
        return Err(InputWireError::wire(
            "program symbol domains are not complete and canonical",
        ));
    }
    let mut domain_counts = [0_u32; 8];
    for domain in &program.symbol_domains {
        domain_counts[domain.kind.index()] = u32::try_from(domain.values.len())
            .map_err(|_| InputWireError::resource("symbol domain exceeds u32"))?;
        for (identifier, value) in domain.values.iter().enumerate() {
            if usize::try_from(value.identifier).ok() != Some(identifier)
                || value.key.is_empty()
                || value.display.is_empty()
            {
                return Err(InputWireError::wire(
                    "program symbol values are not dense or contain empty identities",
                ));
            }
        }
    }
    for (identifier, predicate) in program.predicates.iter().enumerate() {
        if usize::try_from(predicate.predicate_id).ok() != Some(identifier) {
            return Err(InputWireError::wire("predicate IDs are not dense"));
        }
        validate_predicate_arity(predicate.kind, &predicate.argument_sorts)?;
        validate_predicate_shape(predicate, &domain_counts)?;
        if let Some(filler) = predicate.filler_predicate_id {
            if filler == predicate.predicate_id
                || usize_from_u32(filler, "filler predicate")? >= program.predicates.len()
            {
                return Err(InputWireError::wire(
                    "cardinality filler predicate ID is dangling or self-referential",
                ));
            }
        }
    }
    validate_role_model_value(&program.role_model, &domain_counts)?;
    validate_datatype_model_value(&program.datatype_model, &domain_counts)?;
    validate_predicate_cross_references(
        &program.predicates,
        &program.role_model,
        &program.datatype_model,
        &domain_counts,
    )?;
    for (identifier, entry) in program.provenance.iter().enumerate() {
        if usize::try_from(entry.provenance_id).ok() != Some(identifier)
            || entry.source_sha256.is_empty()
        {
            return Err(InputWireError::wire(
                "program provenance IDs or digest ranges are invalid",
            ));
        }
        validate_sorted_unique(&entry.source_sha256, "provenance digests")?;
        if identifier > 0 {
            let previous = &program.provenance[identifier - 1];
            if (previous.source_sha256.as_slice(), previous.generated)
                >= (entry.source_sha256.as_slice(), entry.generated)
            {
                return Err(InputWireError::wire(
                    "program provenance entries are not canonical",
                ));
            }
        }
    }
    let individual_count = domain_counts[SymbolKind::Individual.index()];
    let literal_count = domain_counts[SymbolKind::SourceLiteral.index()];
    let data_value_count = domain_counts[SymbolKind::DataValue.index()];
    let provenance_count = u32::try_from(program.provenance.len())
        .map_err(|_| InputWireError::resource("provenance count exceeds u32"))?;
    for (identifier, clause) in program.clauses.iter().enumerate() {
        if usize::try_from(clause.clause_id).ok() != Some(identifier)
            || (clause.body.is_empty() && clause.head.is_empty())
        {
            return Err(InputWireError::wire(
                "clause IDs are not dense or contain an empty rule",
            ));
        }
        validate_owned_provenance(&clause.provenance_ids, provenance_count, "clause")?;
        for atom in clause.body.iter().chain(&clause.head) {
            validate_owned_atom(
                atom,
                &program.predicates,
                individual_count,
                literal_count,
                data_value_count,
                false,
            )?;
        }
        if clause.body.iter().any(|atom| clause.head.contains(atom)) {
            return Err(InputWireError::wire(
                "program contains a tautological clause",
            ));
        }
        if clause.join_order.len() != clause.body.len() {
            return Err(InputWireError::wire(
                "clause join order length does not match its body",
            ));
        }
        for (position, value) in clause.join_order.iter().enumerate() {
            if usize::try_from(*value)
                .ok()
                .is_none_or(|index| index >= clause.body.len())
                || clause.join_order[..position].contains(value)
            {
                return Err(InputWireError::wire(
                    "clause join order is not a body permutation",
                ));
            }
        }
    }
    for (facts, negative) in [
        (&program.positive_facts, false),
        (&program.negative_facts, true),
    ] {
        for fact in facts {
            validate_owned_ground_atom(
                fact,
                &program.predicates,
                individual_count,
                literal_count,
                data_value_count,
                provenance_count,
            )?;
            let kind = program.predicates
                [usize_from_u32(fact.predicate_id, "ground fact predicate")?]
            .kind;
            if is_negative_fact_kind(kind) != negative {
                return Err(InputWireError::wire(
                    "ground fact is stored in the wrong polarity partition",
                ));
            }
        }
    }
    for (identifier, disjunction) in program.ground_disjunctions.iter().enumerate() {
        if usize::try_from(disjunction.disjunction_id).ok() != Some(identifier)
            || disjunction.disjuncts.len() < 2
        {
            return Err(InputWireError::wire(
                "ground disjunction IDs or arity are invalid",
            ));
        }
        validate_owned_provenance(
            &disjunction.provenance_ids,
            provenance_count,
            "ground disjunction",
        )?;
        for disjunct in &disjunction.disjuncts {
            validate_owned_ground_atom(
                disjunct,
                &program.predicates,
                individual_count,
                literal_count,
                data_value_count,
                provenance_count,
            )?;
            if disjunct.provenance_ids != disjunction.provenance_ids {
                return Err(InputWireError::wire(
                    "ground disjunct provenance differs from its disjunction",
                ));
            }
        }
    }
    validate_expressivity_value(program)?;
    Ok(())
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DecodedEntity {
    pub kind: String,
    pub iri: String,
    pub entity_id: u32,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DecodedOntology {
    pub metadata: OntologyMetadata,
    pub program: DecodedProgram,
    pub declared_entities: Vec<DecodedEntity>,
    pub named_individuals: Vec<u32>,
}

/// Validate the session-owned entity sets shared by wire decoding and direct
/// encoded-program publication.
pub(crate) fn validate_decoded_session_domains(
    program: &DecodedProgram,
    declared_entities: &[DecodedEntity],
    named_individuals: &[u32],
) -> InputResult<()> {
    if declared_entities.windows(2).any(|pair| {
        (pair[0].kind.as_str(), pair[0].iri.as_str())
            >= (pair[1].kind.as_str(), pair[1].iri.as_str())
    }) {
        return Err(InputWireError::wire(
            "declared entities are not uniquely canonically ordered",
        ));
    }
    let entity_domain = program
        .domain(SymbolKind::Entity)
        .ok_or_else(|| InputWireError::wire("program entity domain is missing"))?;
    for entity in declared_entities {
        if entity.kind.is_empty() || entity.iri.is_empty() {
            return Err(InputWireError::wire(
                "declared entity kind and IRI must be nonempty",
            ));
        }
        let value = entity_domain
            .values
            .get(usize_from_u32(entity.entity_id, "declared entity")?)
            .ok_or_else(|| InputWireError::wire("declared entity ID is dangling"))?;
        let display = value
            .display
            .strip_prefix(entity.kind.as_str())
            .and_then(|suffix| suffix.strip_prefix(':'));
        if display != Some(entity.iri.as_str()) {
            return Err(InputWireError::wire(
                "declared entity identity disagrees with its symbol",
            ));
        }
    }
    validate_sorted_unique(named_individuals, "named individuals")?;
    let individual_domain = program
        .domain(SymbolKind::Individual)
        .ok_or_else(|| InputWireError::wire("program individual domain is missing"))?;
    for identifier in named_individuals {
        individual_domain
            .values
            .get(usize_from_u32(*identifier, "named individual")?)
            .ok_or_else(|| InputWireError::wire("named individual ID is dangling"))?;
    }
    Ok(())
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(u8)]
pub enum BackendChoice {
    Auto = 0,
    Python = 1,
    Native = 2,
    Verify = 3,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(u8)]
pub enum FreshEntityChoice {
    Disallow = 0,
    Allow = 1,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(u8)]
pub enum IndividualGroupingChoice {
    BySameAs = 0,
    ByName = 1,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(u8)]
pub enum UnsupportedDatatypeChoice {
    Error = 0,
    IgnoreWithWarning = 1,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(u8)]
pub enum BlockingChoice {
    Auto = 0,
    Anywhere = 1,
    ValidatedAnywhere = 2,
    Ancestor = 3,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(u8)]
pub enum ExistentialChoice {
    Auto = 0,
    CreationOrder = 1,
    IndividualReuse = 2,
}

#[derive(Clone, Debug, PartialEq)]
pub struct DecodedConfig {
    pub backend: BackendChoice,
    pub timeout_seconds: Option<f64>,
    pub buffer_changes: bool,
    pub fresh_entities: FreshEntityChoice,
    pub individual_grouping: IndividualGroupingChoice,
    pub unsupported_datatypes: UnsupportedDatatypeChoice,
    pub blocking: BlockingChoice,
    pub existentials: ExistentialChoice,
    pub disjunction_learning: bool,
    pub force_quasi_order_classification: bool,
    pub workers: u32,
    pub max_memory_bytes: Option<u64>,
    pub deterministic: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DecodedQuery {
    pub permanent_program_sha256: [u8; 32],
    pub query_hash: [u8; 32],
    pub overlay_program_sha256: Option<[u8; 32]>,
    pub first_local_predicate_id: u32,
    pub first_local_symbols: [u32; 8],
    pub requires_rebuild: bool,
    pub program: Option<DecodedProgram>,
    pub reason: Option<String>,
    pub interpretation: Vec<String>,
}

impl DecodedQuery {
    /// Bind query-local prefix boundaries and the permanent digest to one session ontology.
    pub fn validate_against(&self, ontology: &DecodedOntology) -> InputResult<()> {
        if self.permanent_program_sha256 != ontology.metadata.program_sha256 {
            return Err(InputWireError::wire(
                "query permanent-program digest does not match the session",
            ));
        }
        if usize_from_u32(self.first_local_predicate_id, "query predicate boundary")?
            != ontology.program.predicates.len()
        {
            return Err(InputWireError::wire(
                "query predicate prefix boundary does not match the session",
            ));
        }
        for domain in &ontology.program.symbol_domains {
            if usize_from_u32(
                self.first_local_symbols[domain.kind.index()],
                "query symbol boundary",
            )? != domain.values.len()
            {
                return Err(InputWireError::wire(
                    "query symbol prefix boundary does not match the session",
                ));
            }
        }
        if let Some(overlay) = &self.program {
            if overlay.predicates[..ontology.program.predicates.len()]
                != ontology.program.predicates
            {
                return Err(InputWireError::wire(
                    "query predicate prefix differs from the permanent program",
                ));
            }
            for permanent_domain in &ontology.program.symbol_domains {
                let overlay_domain = overlay
                    .domain(permanent_domain.kind)
                    .ok_or_else(|| InputWireError::wire("query symbol domain is missing"))?;
                if overlay_domain.values[..permanent_domain.values.len()] != permanent_domain.values
                {
                    return Err(InputWireError::wire(
                        "query symbol prefix differs from the permanent program",
                    ));
                }
            }
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(u8)]
pub enum DeltaCompatibility {
    AssertionOnly = 0,
    DeclarationOnly = 1,
    RebuildRequired = 2,
    Rejected = 3,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct DecodedDeltaFact {
    pub predicate_id: u32,
    pub arguments: Vec<DecodedTerm>,
    pub negative: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DecodedDelta {
    pub base_program_sha256: [u8; 32],
    pub result_program_sha256: [u8; 32],
    pub compatibility: DeltaCompatibility,
    pub addition_sha256: Vec<[u8; 32]>,
    pub removal_sha256: Vec<[u8; 32]>,
    pub fact_additions: Vec<DecodedDeltaFact>,
    pub fact_removals: Vec<DecodedDeltaFact>,
    pub reasons: Vec<String>,
}

impl DecodedDelta {
    /// Validate revision-local predicate and term IDs once the bound permanent program exists.
    pub fn validate_against(&self, program: &DecodedProgram) -> InputResult<()> {
        let individual_count = domain_len(program, SymbolKind::Individual)?;
        let literal_count = domain_len(program, SymbolKind::SourceLiteral)?;
        let data_value_count = domain_len(program, SymbolKind::DataValue)?;
        for fact in self.fact_additions.iter().chain(&self.fact_removals) {
            let predicate = program
                .predicates
                .get(usize_from_u32(fact.predicate_id, "delta predicate ID")?)
                .ok_or_else(|| InputWireError::wire("delta predicate ID is dangling"))?;
            validate_argument_list(
                &fact.arguments,
                predicate,
                individual_count,
                literal_count,
                data_value_count,
                true,
            )?;
            let expected_negative = matches!(
                predicate.kind,
                PredicateKind::NegatedConcept
                    | PredicateKind::NegatedNominal
                    | PredicateKind::NegatedObjectRole
                    | PredicateKind::NegatedDataRole
                    | PredicateKind::NegatedDataRange
            );
            if fact.negative != expected_negative {
                return Err(InputWireError::wire(
                    "delta fact polarity disagrees with its predicate kind",
                ));
            }
        }
        Ok(())
    }

    /// Bind the base digest and then validate all fact references against a session ontology.
    pub fn validate_revision(&self, ontology: &DecodedOntology) -> InputResult<()> {
        if self.base_program_sha256 != ontology.metadata.program_sha256 {
            return Err(InputWireError::wire(
                "delta base-program digest does not match the session",
            ));
        }
        self.validate_against(&ontology.program)
    }
}

const PROGRAM_SECTIONS: &[SectionKind] = &[
    SectionKind::Strings,
    SectionKind::Blobs,
    SectionKind::U32Pool,
    SectionKind::Program,
    SectionKind::Domains,
    SectionKind::Symbols,
    SectionKind::Predicates,
    SectionKind::Terms,
    SectionKind::Atoms,
    SectionKind::GroundAtoms,
    SectionKind::Clauses,
    SectionKind::Disjunctions,
    SectionKind::Provenance,
    SectionKind::Digests,
    SectionKind::Role,
    SectionKind::RolePairs,
    SectionKind::RoleChains,
    SectionKind::Automata,
    SectionKind::Transitions,
    SectionKind::Literals,
    SectionKind::Datatype,
    SectionKind::Expressivity,
    SectionKind::DatatypeDefinitions,
];

/// Decode and fully validate an owned ontology input document.
pub fn decode_ontology(bytes: Vec<u8>, limits: &DecodeLimits) -> InputResult<DecodedOntology> {
    let document = Document::parse(bytes, DocumentKind::Ontology, limits)?;
    let mut allowed = PROGRAM_SECTIONS.to_vec();
    allowed.extend([
        SectionKind::Metadata,
        SectionKind::Entities,
        SectionKind::NamedIndividuals,
    ]);
    document.reject_unexpected(&allowed)?;
    let metadata = decode_ontology_metadata(document.require(SectionKind::Metadata)?)?;
    let program = decode_program(&document)?;
    let strings = document.require(SectionKind::Strings)?;
    let mut declared_entities = Vec::new();
    reserve_count(
        &mut declared_entities,
        document.count(SectionKind::Entities)?,
        "declared entities",
    )?;
    for record in records(document.require(SectionKind::Entities)?, 20)? {
        let kind = read_string(strings, read_u32(record, 0)?, read_u32(record, 4)?, false)?;
        let iri = read_string(strings, read_u32(record, 8)?, read_u32(record, 12)?, false)?;
        declared_entities.push(DecodedEntity {
            kind,
            iri,
            entity_id: read_u32(record, 16)?,
        });
    }
    let named_individuals = decode_u32_records(
        document.require(SectionKind::NamedIndividuals)?,
        "named individuals",
    )?;
    validate_decoded_session_domains(&program, &declared_entities, &named_individuals)?;
    Ok(DecodedOntology {
        metadata,
        program,
        declared_entities,
        named_individuals,
    })
}

/// Decode and validate one semantic configuration input document.
pub fn decode_config(bytes: Vec<u8>, limits: &DecodeLimits) -> InputResult<DecodedConfig> {
    let document = Document::parse(bytes, DocumentKind::Config, limits)?;
    document.reject_unexpected(&[SectionKind::Config])?;
    let record = document.require(SectionKind::Config)?;
    if record[..32].iter().any(|value| *value != 0) {
        return Err(InputWireError::version(
            "config reserved binding bytes are nonzero",
        ));
    }
    let timeout = read_f64(record, 32)?;
    let maximum = read_u64(record, 40)?;
    let workers = read_u32(record, 48)?;
    let flags = read_u16(record, 52)?;
    if flags & !0b11_1111 != 0 || record[60..64].iter().any(|value| *value != 0) {
        return Err(InputWireError::version(
            "config flags or reserved bytes are nonzero",
        ));
    }
    let has_timeout = flags & (1 << 4) != 0;
    let has_maximum = flags & (1 << 5) != 0;
    if (has_timeout && (!timeout.is_finite() || timeout <= 0.0)) || (!has_timeout && timeout != 0.0)
    {
        return Err(InputWireError::wire("config timeout encoding is invalid"));
    }
    if (has_maximum && maximum == 0) || (!has_maximum && maximum != 0) {
        return Err(InputWireError::wire(
            "config maximum-memory encoding is invalid",
        ));
    }
    Ok(DecodedConfig {
        backend: parse_backend(record[54])?,
        timeout_seconds: has_timeout.then_some(timeout),
        buffer_changes: flags & 1 != 0,
        fresh_entities: parse_fresh(record[55])?,
        individual_grouping: parse_grouping(record[56])?,
        unsupported_datatypes: parse_unsupported_datatype(record[57])?,
        blocking: parse_blocking(record[58])?,
        existentials: parse_existential(record[59])?,
        disjunction_learning: flags & (1 << 1) != 0,
        force_quasi_order_classification: flags & (1 << 2) != 0,
        workers,
        max_memory_bytes: has_maximum.then_some(maximum),
        deterministic: flags & (1 << 3) != 0,
    })
}

/// Decode and validate one query document, including its optional complete overlay program.
pub fn decode_query(bytes: Vec<u8>, limits: &DecodeLimits) -> InputResult<DecodedQuery> {
    let document = Document::parse(bytes, DocumentKind::Query, limits)?;
    let record = document.require(SectionKind::Query)?;
    let flags = read_u32(record, 100)?;
    if flags & !0b111 != 0 {
        return Err(InputWireError::version("query flags are invalid"));
    }
    let requires_rebuild = flags & 1 != 0;
    let has_program = flags & 2 != 0;
    let has_reason = flags & 4 != 0;
    if requires_rebuild == has_program {
        return Err(InputWireError::wire(
            "query rebuild/program flags are contradictory",
        ));
    }
    let mut allowed = vec![
        SectionKind::Query,
        SectionKind::Strings,
        SectionKind::StringRefs,
    ];
    if has_program {
        allowed.extend(PROGRAM_SECTIONS.iter().copied());
    }
    document.reject_unexpected(&allowed)?;
    let strings = document.require(SectionKind::Strings)?;
    let reason_offset = read_u32(record, 136)?;
    let reason_length = read_u32(record, 140)?;
    let reason = if has_reason {
        Some(read_string(strings, reason_offset, reason_length, false)?)
    } else {
        if reason_offset != 0 || reason_length != 0 {
            return Err(InputWireError::wire(
                "absent query reason has a nonzero reference",
            ));
        }
        None
    };
    let interpretation = decode_string_ref_range(
        document.require(SectionKind::StringRefs)?,
        strings,
        read_u32(record, 144)?,
        read_u32(record, 148)?,
        false,
    )?;
    let mut first_local_symbols = [0_u32; 8];
    for (index, cutoff) in first_local_symbols.iter_mut().enumerate() {
        *cutoff = read_u32(record, 104 + index * 4)?;
    }
    let first_local_predicate_id = read_u32(record, 96)?;
    let program = if has_program {
        let value = decode_program(&document)?;
        validate_query_prefix(&value, first_local_predicate_id, &first_local_symbols)?;
        Some(value)
    } else {
        None
    };
    let overlay_digest = read_array_32(record, 64)?;
    if has_program == overlay_digest.iter().all(|value| *value == 0) {
        return Err(InputWireError::wire(
            "query overlay digest presence does not match its program",
        ));
    }
    Ok(DecodedQuery {
        permanent_program_sha256: read_array_32(record, 0)?,
        query_hash: read_array_32(record, 32)?,
        overlay_program_sha256: has_program.then_some(overlay_digest),
        first_local_predicate_id,
        first_local_symbols,
        requires_rebuild,
        program,
        reason,
        interpretation,
    })
}

/// Decode one delta. Call [`DecodedDelta::validate_against`] after revision binding.
pub fn decode_delta(bytes: Vec<u8>, limits: &DecodeLimits) -> InputResult<DecodedDelta> {
    let document = Document::parse(bytes, DocumentKind::Delta, limits)?;
    document.reject_unexpected(&[
        SectionKind::Delta,
        SectionKind::Strings,
        SectionKind::U32Pool,
        SectionKind::Terms,
        SectionKind::Digests,
        SectionKind::DeltaFacts,
        SectionKind::StringRefs,
    ])?;
    let record = document.require(SectionKind::Delta)?;
    if record[65..68].iter().any(|value| *value != 0) {
        return Err(InputWireError::version("delta reserved bytes are nonzero"));
    }
    let compatibility = match record[64] {
        0 => DeltaCompatibility::AssertionOnly,
        1 => DeltaCompatibility::DeclarationOnly,
        2 => DeltaCompatibility::RebuildRequired,
        3 => DeltaCompatibility::Rejected,
        _ => return Err(InputWireError::wire("delta compatibility enum is invalid")),
    };
    let digests = decode_digest_records(document.require(SectionKind::Digests)?)?;
    let addition_sha256 = clone_range(
        &digests,
        read_u32(record, 68)?,
        read_u32(record, 72)?,
        "delta addition digests",
    )?;
    let removal_sha256 = clone_range(
        &digests,
        read_u32(record, 76)?,
        read_u32(record, 80)?,
        "delta removal digests",
    )?;
    validate_sorted_unique(&addition_sha256, "delta addition digests")?;
    validate_sorted_unique(&removal_sha256, "delta removal digests")?;
    let terms = decode_terms(document.require(SectionKind::Terms)?)?;
    let facts = decode_delta_facts(document.require(SectionKind::DeltaFacts)?, &terms)?;
    let fact_additions = clone_range(
        &facts,
        read_u32(record, 84)?,
        read_u32(record, 88)?,
        "delta fact additions",
    )?;
    let fact_removals = clone_range(
        &facts,
        read_u32(record, 92)?,
        read_u32(record, 96)?,
        "delta fact removals",
    )?;
    let mut seen_facts = BTreeSet::new();
    for fact in fact_additions.iter().chain(&fact_removals) {
        if !seen_facts.insert(fact) {
            return Err(InputWireError::wire(
                "delta fact rows are duplicated across additions/removals",
            ));
        }
    }
    if compatibility != DeltaCompatibility::AssertionOnly
        && (!fact_additions.is_empty() || !fact_removals.is_empty())
    {
        return Err(InputWireError::wire(
            "non-assertion delta carries applicable fact rows",
        ));
    }
    let strings = document.require(SectionKind::Strings)?;
    let reasons = decode_string_ref_range(
        document.require(SectionKind::StringRefs)?,
        strings,
        read_u32(record, 100)?,
        read_u32(record, 104)?,
        false,
    )?;
    validate_sorted_unique(&reasons, "delta reasons")?;
    Ok(DecodedDelta {
        base_program_sha256: read_array_32(record, 0)?,
        result_program_sha256: read_array_32(record, 32)?,
        compatibility,
        addition_sha256,
        removal_sha256,
        fact_additions,
        fact_removals,
        reasons,
    })
}

pub(crate) fn decode_ontology_metadata(bytes: &[u8]) -> InputResult<OntologyMetadata> {
    if bytes.len() < 193 {
        return Err(InputWireError::wire("ontology metadata is truncated"));
    }
    let structural_schema = read_u32(bytes, 160)?;
    let logical_schema = read_u32(bytes, 164)?;
    let signature_schema = read_u32(bytes, 168)?;
    if structural_schema == 0 || logical_schema == 0 || signature_schema == 0 {
        return Err(InputWireError::wire(
            "source fingerprint schema must be positive",
        ));
    }
    let package_length = usize_from_u32(read_u32(bytes, 188)?, "core package length")?;
    if bytes.len() != 192_usize.saturating_add(package_length) {
        return Err(InputWireError::wire(
            "core package length does not cover ontology metadata",
        ));
    }
    let core_package_version = std::str::from_utf8(&bytes[192..])
        .map_err(|_| InputWireError::wire("core package version is not UTF-8"))?
        .to_owned();
    if core_package_version.is_empty() {
        return Err(InputWireError::wire("core package version is empty"));
    }
    let core_model_schema_version = read_u32(bytes, 176)?;
    let core_adapter_protocol_version = read_u32(bytes, 184)?;
    if core_model_schema_version == 0 || core_adapter_protocol_version == 0 {
        return Err(InputWireError::wire(
            "core model/adapter schema versions must be positive",
        ));
    }
    Ok(OntologyMetadata {
        ontology_fingerprint: read_array_32(bytes, 0)?,
        structural_fingerprint: DecodedFingerprint {
            schema: structural_schema,
            digest: read_array_32(bytes, 32)?,
        },
        logical_fingerprint: DecodedFingerprint {
            schema: logical_schema,
            digest: read_array_32(bytes, 64)?,
        },
        signature_fingerprint: DecodedFingerprint {
            schema: signature_schema,
            digest: read_array_32(bytes, 96)?,
        },
        program_sha256: read_array_32(bytes, 128)?,
        core_package_version,
        core_api_version: (read_u16(bytes, 172)?, read_u16(bytes, 174)?),
        core_model_schema_version,
        core_wire_format_version: (read_u16(bytes, 180)?, read_u16(bytes, 182)?),
        core_adapter_protocol_version,
    })
}

#[derive(Clone, Copy)]
struct ProgramSummary {
    domain_count: u32,
    symbol_count: u32,
    predicate_count: u32,
    clause_count: u32,
    positive_first: u32,
    positive_count: u32,
    negative_first: u32,
    negative_count: u32,
    disjunction_count: u32,
    provenance_count: u32,
    term_count: u32,
    atom_count: u32,
}

fn decode_program(document: &Document) -> InputResult<DecodedProgram> {
    for kind in PROGRAM_SECTIONS {
        document.require(*kind)?;
    }
    let summary_record = document.require(SectionKind::Program)?;
    let summary = ProgramSummary {
        domain_count: read_u32(summary_record, 0)?,
        symbol_count: read_u32(summary_record, 4)?,
        predicate_count: read_u32(summary_record, 8)?,
        clause_count: read_u32(summary_record, 12)?,
        positive_first: read_u32(summary_record, 16)?,
        positive_count: read_u32(summary_record, 20)?,
        negative_first: read_u32(summary_record, 24)?,
        negative_count: read_u32(summary_record, 28)?,
        disjunction_count: read_u32(summary_record, 32)?,
        provenance_count: read_u32(summary_record, 36)?,
        term_count: read_u32(summary_record, 40)?,
        atom_count: read_u32(summary_record, 44)?,
    };
    for (kind, expected) in [
        (SectionKind::Domains, summary.domain_count),
        (SectionKind::Symbols, summary.symbol_count),
        (SectionKind::Predicates, summary.predicate_count),
        (SectionKind::Clauses, summary.clause_count),
        (SectionKind::Disjunctions, summary.disjunction_count),
        (SectionKind::Provenance, summary.provenance_count),
        (SectionKind::Terms, summary.term_count),
        (SectionKind::Atoms, summary.atom_count),
    ] {
        if document.count(kind)? != expected {
            return Err(InputWireError::wire(format!(
                "program summary count does not match {kind:?} section"
            )));
        }
    }
    if summary.domain_count != 8 {
        return Err(InputWireError::wire(
            "program must contain exactly every symbol domain",
        ));
    }

    let strings = document.require(SectionKind::Strings)?;
    std::str::from_utf8(strings)
        .map_err(|_| InputWireError::wire("program string pool is not UTF-8"))?;
    let blobs = document.require(SectionKind::Blobs)?;
    let u32s = document.require(SectionKind::U32Pool)?;
    let (symbol_domains, domain_counts) = decode_symbol_domains(
        document.require(SectionKind::Domains)?,
        document.require(SectionKind::Symbols)?,
        strings,
        blobs,
    )?;
    let predicates = decode_predicates(
        document.require(SectionKind::Predicates)?,
        strings,
        u32s,
        &domain_counts,
    )?;
    let terms = decode_terms(document.require(SectionKind::Terms)?)?;
    let individual_count = domain_counts[SymbolKind::Individual.index()];
    let literal_count = domain_counts[SymbolKind::SourceLiteral.index()];
    let data_value_count = domain_counts[SymbolKind::DataValue.index()];
    let atoms = decode_atoms(
        document.require(SectionKind::Atoms)?,
        &terms,
        &predicates,
        individual_count,
        literal_count,
        data_value_count,
        false,
    )?;
    let ground_atoms = decode_ground_atoms(
        document.require(SectionKind::GroundAtoms)?,
        &terms,
        u32s,
        &predicates,
        individual_count,
        literal_count,
        data_value_count,
        summary.provenance_count,
    )?;
    let clauses = decode_clauses(
        document.require(SectionKind::Clauses)?,
        &atoms,
        u32s,
        summary.provenance_count,
    )?;
    let positive_facts = clone_range(
        &ground_atoms,
        summary.positive_first,
        summary.positive_count,
        "positive facts",
    )?;
    if summary.positive_first != 0 {
        return Err(InputWireError::wire(
            "positive fact range must begin at zero",
        ));
    }
    let expected_negative_first = summary
        .positive_first
        .checked_add(summary.positive_count)
        .ok_or_else(|| InputWireError::wire("positive fact range overflows"))?;
    if summary.negative_first != expected_negative_first {
        return Err(InputWireError::wire(
            "negative facts do not immediately follow positive facts",
        ));
    }
    let negative_facts = clone_range(
        &ground_atoms,
        summary.negative_first,
        summary.negative_count,
        "negative facts",
    )?;
    let first_disjunct = summary
        .negative_first
        .checked_add(summary.negative_count)
        .ok_or_else(|| InputWireError::wire("negative fact range overflows"))?;
    let ground_disjunctions = decode_disjunctions(
        document.require(SectionKind::Disjunctions)?,
        &ground_atoms,
        u32s,
        summary.provenance_count,
        first_disjunct,
    )?;
    let provenance = decode_provenance(
        document.require(SectionKind::Provenance)?,
        document.require(SectionKind::Digests)?,
    )?;
    let role_model = decode_role_model(document, u32s)?;
    let datatype_model = decode_datatype_model(
        document,
        strings,
        u32s,
        literal_count,
        data_value_count,
        domain_counts[SymbolKind::DataRange.index()],
    )?;
    let expressivity = decode_expressivity(document.require(SectionKind::Expressivity)?)?;
    let program = DecodedProgram {
        symbol_domains,
        predicates,
        clauses,
        positive_facts,
        negative_facts,
        ground_disjunctions,
        role_model,
        datatype_model,
        expressivity,
        provenance,
    };
    validate_decoded_program(&program)?;
    Ok(program)
}

fn decode_symbol_domains(
    domain_bytes: &[u8],
    symbol_bytes: &[u8],
    strings: &[u8],
    blobs: &[u8],
) -> InputResult<(Vec<DecodedSymbolDomain>, [u32; 8])> {
    let symbol_records = records(symbol_bytes, 24)?;
    let mut domains = Vec::new();
    let mut counts = [0_u32; 8];
    let mut seen = [false; 8];
    let mut expected_first = 0_u32;
    reserve_count(
        &mut domains,
        u32::try_from(domain_bytes.len() / 12).unwrap_or(u32::MAX),
        "symbol domains",
    )?;
    for record in records(domain_bytes, 12)? {
        let kind = SymbolKind::parse(record[0])?;
        if record[1..4].iter().any(|value| *value != 0) || seen[kind.index()] {
            return Err(InputWireError::wire(
                "symbol domain has reserved bytes or duplicate kind",
            ));
        }
        seen[kind.index()] = true;
        let first = read_u32(record, 4)?;
        let count = read_u32(record, 8)?;
        if first != expected_first {
            return Err(InputWireError::wire(
                "symbol domains are not contiguous in canonical order",
            ));
        }
        let records_for_domain =
            slice_range(&symbol_records, first, count, "symbol domain records")?;
        let mut values = Vec::new();
        reserve_count(&mut values, count, "symbol values")?;
        for (identifier, symbol) in records_for_domain.iter().enumerate() {
            if read_u32(symbol, 0)? != u32::try_from(identifier).unwrap_or(u32::MAX)
                || symbol[4] != kind as u8
                || read_u16(symbol, 6)? != 0
                || symbol[5] & !0b11 != 0
            {
                return Err(InputWireError::wire(
                    "symbol ID/kind/flags are noncanonical",
                ));
            }
            let key = read_bytes(blobs, read_u32(symbol, 8)?, read_u32(symbol, 12)?)?;
            if key.is_empty() {
                return Err(InputWireError::wire("symbol key is empty"));
            }
            let display =
                read_string(strings, read_u32(symbol, 16)?, read_u32(symbol, 20)?, false)?;
            values.push(DecodedSymbolValue {
                identifier: u32::try_from(identifier).unwrap_or(u32::MAX),
                key,
                display,
                generated: symbol[5] & 1 != 0,
                query_local: symbol[5] & 2 != 0,
            });
        }
        counts[kind.index()] = count;
        expected_first = expected_first
            .checked_add(count)
            .ok_or_else(|| InputWireError::wire("symbol domain end overflows"))?;
        domains.push(DecodedSymbolDomain { kind, values });
    }
    if seen.iter().any(|value| !*value)
        || usize_from_u32(expected_first, "symbol count")? != symbol_records.len()
    {
        return Err(InputWireError::wire(
            "symbol domains do not exactly partition symbol records",
        ));
    }
    // Python's canonical SymbolTable order is lexicographic by enum text.
    let expected_order = [
        SymbolKind::ClassExpression,
        SymbolKind::DataProperty,
        SymbolKind::DataRange,
        SymbolKind::DataValue,
        SymbolKind::Entity,
        SymbolKind::Individual,
        SymbolKind::ObjectRole,
        SymbolKind::SourceLiteral,
    ];
    if domains.iter().map(|value| value.kind).ne(expected_order) {
        return Err(InputWireError::wire(
            "symbol domains are not in canonical lexical order",
        ));
    }
    Ok((domains, counts))
}

fn decode_predicates(
    bytes: &[u8],
    strings: &[u8],
    u32s: &[u8],
    domain_counts: &[u32; 8],
) -> InputResult<Vec<DecodedPredicate>> {
    let mut values = Vec::new();
    reserve_count(
        &mut values,
        u32::try_from(bytes.len() / 48).unwrap_or(u32::MAX),
        "predicates",
    )?;
    for (identifier, record) in records(bytes, 48)?.iter().enumerate() {
        let predicate_id = read_u32(record, 0)?;
        if predicate_id != u32::try_from(identifier).unwrap_or(u32::MAX) {
            return Err(InputWireError::wire("predicate IDs are not dense"));
        }
        let kind = PredicateKind::parse(read_u16(record, 4)?)?;
        let flags = read_u16(record, 6)?;
        if flags & !0b1_1111 != 0 {
            return Err(InputWireError::version("predicate flags are invalid"));
        }
        let sort_ids = read_u32_range(u32s, read_u32(record, 8)?, read_u32(record, 12)?)?;
        let mut argument_sorts = Vec::new();
        reserve_count(
            &mut argument_sorts,
            u32::try_from(sort_ids.len()).unwrap_or(u32::MAX),
            "predicate sorts",
        )?;
        for value in sort_ids {
            argument_sorts.push(TermSort::parse(u8::try_from(value).unwrap_or(u8::MAX))?);
        }
        validate_predicate_arity(kind, &argument_sorts)?;
        let symbol_id = optional_u32(flags, 0, read_u32(record, 16)?, "symbol_id")?;
        let role_id = optional_u32(flags, 1, read_u32(record, 20)?, "role_id")?;
        let cardinality = optional_u32(flags, 2, read_u32(record, 24)?, "cardinality")?;
        let filler_predicate_id =
            optional_u32(flags, 3, read_u32(record, 28)?, "filler_predicate_id")?;
        let annotation = read_u32_range(u32s, read_u32(record, 32)?, read_u32(record, 36)?)?;
        let internal_key = if flags & (1 << 4) != 0 {
            Some(read_string(
                strings,
                read_u32(record, 40)?,
                read_u32(record, 44)?,
                false,
            )?)
        } else {
            if read_u32(record, 40)? != 0 || read_u32(record, 44)? != 0 {
                return Err(InputWireError::wire(
                    "absent predicate internal key has a nonzero reference",
                ));
            }
            None
        };
        let predicate = DecodedPredicate {
            predicate_id,
            kind,
            argument_sorts,
            symbol_id,
            role_id,
            cardinality,
            filler_predicate_id,
            annotation,
            internal_key,
        };
        validate_predicate_shape(&predicate, domain_counts)?;
        values.push(predicate);
    }
    for predicate in &values {
        if let Some(filler) = predicate.filler_predicate_id {
            if filler == predicate.predicate_id
                || usize_from_u32(filler, "filler predicate")? >= values.len()
            {
                return Err(InputWireError::wire(
                    "cardinality filler predicate ID is dangling or self-referential",
                ));
            }
        }
    }
    Ok(values)
}

fn decode_terms(bytes: &[u8]) -> InputResult<Vec<DecodedTerm>> {
    let mut terms = Vec::new();
    reserve_count(
        &mut terms,
        u32::try_from(bytes.len() / 12).unwrap_or(u32::MAX),
        "terms",
    )?;
    for record in records(bytes, 12)? {
        let sort = TermSort::parse(record[1])?;
        if read_u16(record, 2)? != 0 {
            return Err(InputWireError::version("term reserved bits are nonzero"));
        }
        let first = read_u32(record, 4)?;
        let second = read_u32(record, 8)?;
        let term = match record[0] {
            0 if second == U32_NONE => DecodedTerm::Variable { index: first, sort },
            1 if sort == TermSort::Object && second == U32_NONE => DecodedTerm::Individual {
                individual_id: first,
            },
            2 if sort == TermSort::Data && second != U32_NONE => DecodedTerm::Data {
                source_literal_id: first,
                data_identity_id: second,
            },
            _ => return Err(InputWireError::wire("term tag/sort/sentinel is invalid")),
        };
        terms.push(term);
    }
    Ok(terms)
}

fn decode_atoms(
    bytes: &[u8],
    terms: &[DecodedTerm],
    predicates: &[DecodedPredicate],
    individual_count: u32,
    literal_count: u32,
    data_value_count: u32,
    ground: bool,
) -> InputResult<Vec<DecodedAtom>> {
    let mut atoms = Vec::new();
    reserve_count(
        &mut atoms,
        u32::try_from(bytes.len() / 12).unwrap_or(u32::MAX),
        "atoms",
    )?;
    for record in records(bytes, 12)? {
        let predicate_id = read_u32(record, 0)?;
        let first = read_u32(record, 4)?;
        let count = read_u32(record, 8)?;
        let arguments = clone_range(terms, first, count, "atom terms")?;
        let predicate = predicates
            .get(usize_from_u32(predicate_id, "atom predicate ID")?)
            .ok_or_else(|| InputWireError::wire("atom predicate ID is dangling"))?;
        validate_argument_list(
            &arguments,
            predicate,
            individual_count,
            literal_count,
            data_value_count,
            ground,
        )?;
        atoms.push(DecodedAtom {
            predicate_id,
            arguments,
        });
    }
    Ok(atoms)
}

fn decode_ground_atoms(
    bytes: &[u8],
    terms: &[DecodedTerm],
    u32s: &[u8],
    predicates: &[DecodedPredicate],
    individual_count: u32,
    literal_count: u32,
    data_value_count: u32,
    provenance_count: u32,
) -> InputResult<Vec<DecodedGroundAtom>> {
    let mut atoms = Vec::new();
    reserve_count(
        &mut atoms,
        u32::try_from(bytes.len() / 20).unwrap_or(u32::MAX),
        "ground atoms",
    )?;
    for record in records(bytes, 20)? {
        let predicate_id = read_u32(record, 0)?;
        let arguments = clone_range(
            terms,
            read_u32(record, 4)?,
            read_u32(record, 8)?,
            "ground atom terms",
        )?;
        let predicate = predicates
            .get(usize_from_u32(predicate_id, "ground atom predicate ID")?)
            .ok_or_else(|| InputWireError::wire("ground atom predicate ID is dangling"))?;
        validate_argument_list(
            &arguments,
            predicate,
            individual_count,
            literal_count,
            data_value_count,
            true,
        )?;
        let provenance_ids = read_u32_range(u32s, read_u32(record, 12)?, read_u32(record, 16)?)?;
        if provenance_ids.is_empty()
            || provenance_ids
                .iter()
                .any(|value| *value >= provenance_count)
        {
            return Err(InputWireError::wire(
                "ground atom provenance is empty or dangling",
            ));
        }
        validate_sorted_unique(&provenance_ids, "ground atom provenance")?;
        atoms.push(DecodedGroundAtom {
            predicate_id,
            arguments,
            provenance_ids,
        });
    }
    Ok(atoms)
}

fn decode_clauses(
    bytes: &[u8],
    atoms: &[DecodedAtom],
    u32s: &[u8],
    provenance_count: u32,
) -> InputResult<Vec<DecodedClause>> {
    let mut clauses = Vec::new();
    reserve_count(
        &mut clauses,
        u32::try_from(bytes.len() / 36).unwrap_or(u32::MAX),
        "clauses",
    )?;
    let mut expected_atom = 0_u32;
    for (identifier, record) in records(bytes, 36)?.iter().enumerate() {
        let clause_id = read_u32(record, 0)?;
        if clause_id != u32::try_from(identifier).unwrap_or(u32::MAX) {
            return Err(InputWireError::wire("clause IDs are not dense"));
        }
        let body_first = read_u32(record, 4)?;
        let body_count = read_u32(record, 8)?;
        let head_first = read_u32(record, 12)?;
        let head_count = read_u32(record, 16)?;
        if body_first != expected_atom
            || head_first
                != body_first
                    .checked_add(body_count)
                    .ok_or_else(|| InputWireError::wire("clause body range overflows"))?
        {
            return Err(InputWireError::wire(
                "clause atom ranges are not contiguous and canonical",
            ));
        }
        if body_count == 0 && head_count == 0 {
            return Err(InputWireError::wire("clause body and head are both empty"));
        }
        let body = clone_range(atoms, body_first, body_count, "clause body")?;
        let head = clone_range(atoms, head_first, head_count, "clause head")?;
        let provenance_ids = read_u32_range(u32s, read_u32(record, 20)?, read_u32(record, 24)?)?;
        if provenance_ids.is_empty()
            || provenance_ids
                .iter()
                .any(|value| *value >= provenance_count)
        {
            return Err(InputWireError::wire(
                "clause provenance is empty or dangling",
            ));
        }
        validate_sorted_unique(&provenance_ids, "clause provenance")?;
        let join_order = read_u32_range(u32s, read_u32(record, 28)?, read_u32(record, 32)?)?;
        if usize_from_u32(body_count, "clause body count")? != join_order.len() {
            return Err(InputWireError::wire(
                "clause join order length does not match its body",
            ));
        }
        let mut sorted_join = join_order.clone();
        sorted_join.sort_unstable();
        if sorted_join
            .iter()
            .enumerate()
            .any(|(index, value)| *value != u32::try_from(index).unwrap_or(u32::MAX))
        {
            return Err(InputWireError::wire(
                "clause join order is not a body permutation",
            ));
        }
        expected_atom = head_first
            .checked_add(head_count)
            .ok_or_else(|| InputWireError::wire("clause head range overflows"))?;
        clauses.push(DecodedClause {
            clause_id,
            body,
            head,
            provenance_ids,
            join_order,
        });
    }
    if usize_from_u32(expected_atom, "clause atom count")? != atoms.len() {
        return Err(InputWireError::wire(
            "clauses do not exactly partition the atom section",
        ));
    }
    Ok(clauses)
}

fn decode_disjunctions(
    bytes: &[u8],
    ground_atoms: &[DecodedGroundAtom],
    u32s: &[u8],
    provenance_count: u32,
    mut expected_fact: u32,
) -> InputResult<Vec<DecodedGroundDisjunction>> {
    let mut values = Vec::new();
    reserve_count(
        &mut values,
        u32::try_from(bytes.len() / 20).unwrap_or(u32::MAX),
        "ground disjunctions",
    )?;
    for (identifier, record) in records(bytes, 20)?.iter().enumerate() {
        let disjunction_id = read_u32(record, 0)?;
        if disjunction_id != u32::try_from(identifier).unwrap_or(u32::MAX) {
            return Err(InputWireError::wire("ground disjunction IDs are not dense"));
        }
        let first = read_u32(record, 4)?;
        let count = read_u32(record, 8)?;
        if first != expected_fact || count < 2 {
            return Err(InputWireError::wire(
                "ground disjunction range is noncanonical or too short",
            ));
        }
        let disjuncts = clone_range(ground_atoms, first, count, "ground disjuncts")?;
        let provenance_ids = read_u32_range(u32s, read_u32(record, 12)?, read_u32(record, 16)?)?;
        if provenance_ids.is_empty()
            || provenance_ids
                .iter()
                .any(|value| *value >= provenance_count)
            || disjuncts
                .iter()
                .any(|atom| atom.provenance_ids != provenance_ids)
        {
            return Err(InputWireError::wire(
                "ground disjunction provenance is empty, dangling, or inconsistent",
            ));
        }
        validate_sorted_unique(&provenance_ids, "ground disjunction provenance")?;
        expected_fact = expected_fact
            .checked_add(count)
            .ok_or_else(|| InputWireError::wire("ground disjunction range overflows"))?;
        values.push(DecodedGroundDisjunction {
            disjunction_id,
            disjuncts,
            provenance_ids,
        });
    }
    if usize_from_u32(expected_fact, "ground atom count")? != ground_atoms.len() {
        return Err(InputWireError::wire(
            "facts and disjunctions do not partition ground atoms",
        ));
    }
    Ok(values)
}

fn decode_provenance(
    bytes: &[u8],
    digest_bytes: &[u8],
) -> InputResult<Vec<DecodedProvenanceEntry>> {
    let digests = decode_digest_records(digest_bytes)?;
    let mut values = Vec::new();
    reserve_count(
        &mut values,
        u32::try_from(bytes.len() / 16).unwrap_or(u32::MAX),
        "provenance entries",
    )?;
    let mut expected_digest = 0_u32;
    for (identifier, record) in records(bytes, 16)?.iter().enumerate() {
        let provenance_id = read_u32(record, 0)?;
        if provenance_id != u32::try_from(identifier).unwrap_or(u32::MAX)
            || record[4] > 1
            || record[5..8].iter().any(|value| *value != 0)
        {
            return Err(InputWireError::wire(
                "provenance ID/flags/reserved bytes are invalid",
            ));
        }
        let first = read_u32(record, 8)?;
        let count = read_u32(record, 12)?;
        if first != expected_digest || count == 0 {
            return Err(InputWireError::wire(
                "provenance digest range is empty or noncanonical",
            ));
        }
        let source_sha256 = clone_range(&digests, first, count, "provenance digests")?;
        validate_sorted_unique(&source_sha256, "provenance digests")?;
        expected_digest = expected_digest
            .checked_add(count)
            .ok_or_else(|| InputWireError::wire("provenance digest range overflows"))?;
        values.push(DecodedProvenanceEntry {
            provenance_id,
            source_sha256,
            generated: record[4] != 0,
        });
    }
    if usize_from_u32(expected_digest, "provenance digest count")? != digests.len() {
        return Err(InputWireError::wire(
            "provenance entries do not partition digest records",
        ));
    }
    Ok(values)
}

fn decode_role_model(document: &Document, u32s: &[u8]) -> InputResult<DecodedRoleModel> {
    let record = document.require(SectionKind::Role)?;
    let object_role_count = read_u32(record, 0)?;
    let data_property_count = read_u32(record, 4)?;
    if object_role_count == 0 || data_property_count == 0 {
        return Err(InputWireError::wire(
            "role model must retain object/data built-ins",
        ));
    }
    let inverse_role_ids = read_u32_range(u32s, read_u32(record, 8)?, read_u32(record, 12)?)?;
    if inverse_role_ids.len() != usize_from_u32(object_role_count, "object role count")?
        || inverse_role_ids
            .iter()
            .any(|value| *value >= object_role_count)
    {
        return Err(InputWireError::wire(
            "inverse role map is incomplete or dangling",
        ));
    }
    for (index, inverse) in inverse_role_ids.iter().enumerate() {
        let inverse_index = usize_from_u32(*inverse, "inverse role ID")?;
        if inverse_role_ids.get(inverse_index).copied()
            != Some(u32::try_from(index).unwrap_or(u32::MAX))
        {
            return Err(InputWireError::wire(
                "inverse role map is not an involution",
            ));
        }
    }
    let non_simple_components = read_u32_range(u32s, read_u32(record, 16)?, read_u32(record, 20)?)?;
    validate_sorted_unique(&non_simple_components, "non-simple role components")?;
    if non_simple_components
        .iter()
        .any(|value| *value >= object_role_count)
    {
        return Err(InputWireError::wire(
            "non-simple role component ID is dangling",
        ));
    }
    let top_object_role_id = read_u32(record, 24)?;
    let bottom_object_role_id = read_u32(record, 28)?;
    let top_data_property_id = read_u32(record, 32)?;
    let bottom_data_property_id = read_u32(record, 36)?;
    if top_object_role_id >= object_role_count
        || bottom_object_role_id >= object_role_count
        || top_data_property_id >= data_property_count
        || bottom_data_property_id >= data_property_count
    {
        return Err(InputWireError::wire("role-model built-in ID is dangling"));
    }
    let mut simple_inclusions = Vec::new();
    let mut data_inclusions = Vec::new();
    let mut seen_data = false;
    for pair in records(document.require(SectionKind::RolePairs)?, 12)? {
        if pair[1..4].iter().any(|value| *value != 0) {
            return Err(InputWireError::version(
                "role inclusion reserved bytes are nonzero",
            ));
        }
        let left = read_u32(pair, 4)?;
        let right = read_u32(pair, 8)?;
        match pair[0] {
            0 if !seen_data && left < object_role_count && right < object_role_count => {
                simple_inclusions.push((left, right));
            }
            1 if left < data_property_count && right < data_property_count => {
                seen_data = true;
                data_inclusions.push((left, right));
            }
            _ => {
                return Err(InputWireError::wire(
                    "role inclusion kind/order/reference is invalid",
                ));
            }
        }
    }
    validate_sorted_unique(&simple_inclusions, "object role inclusions")?;
    validate_sorted_unique(&data_inclusions, "data role inclusions")?;
    let mut complex_inclusions = Vec::new();
    for chain_record in records(document.require(SectionKind::RoleChains)?, 12)? {
        let target = read_u32(chain_record, 0)?;
        let chain = read_u32_range(u32s, read_u32(chain_record, 4)?, read_u32(chain_record, 8)?)?;
        if target >= object_role_count
            || chain.len() < 2
            || chain.iter().any(|value| *value >= object_role_count)
        {
            return Err(InputWireError::wire(
                "complex role inclusion is malformed or dangling",
            ));
        }
        complex_inclusions.push((chain, target));
    }
    validate_sorted_unique(&complex_inclusions, "complex role inclusions")?;
    let transition_records = records(document.require(SectionKind::Transitions)?, 12)?;
    let mut automata = Vec::new();
    let mut expected_transition = 0_u32;
    for automaton_record in records(document.require(SectionKind::Automata)?, 28)? {
        let component_id = read_u32(automaton_record, 0)?;
        let state_count = read_u32(automaton_record, 4)?;
        let initial_state = read_u32(automaton_record, 8)?;
        if component_id >= object_role_count || state_count == 0 || initial_state >= state_count {
            return Err(InputWireError::wire("role automaton header is invalid"));
        }
        let final_states = read_u32_range(
            u32s,
            read_u32(automaton_record, 12)?,
            read_u32(automaton_record, 16)?,
        )?;
        validate_sorted_unique(&final_states, "role automaton final states")?;
        if final_states.is_empty() || final_states.iter().any(|value| *value >= state_count) {
            return Err(InputWireError::wire(
                "role automaton final state is empty or dangling",
            ));
        }
        let transition_first = read_u32(automaton_record, 20)?;
        let transition_count = read_u32(automaton_record, 24)?;
        if transition_first != expected_transition {
            return Err(InputWireError::wire(
                "role automaton transition ranges are noncanonical",
            ));
        }
        let selected = slice_range(
            &transition_records,
            transition_first,
            transition_count,
            "role automaton transitions",
        )?;
        let mut transitions = Vec::new();
        reserve_count(&mut transitions, transition_count, "role transitions")?;
        for transition in selected {
            let source_state = read_u32(transition, 0)?;
            let target_state = read_u32(transition, 4)?;
            let raw_role = read_u32(transition, 8)?;
            if source_state >= state_count
                || target_state >= state_count
                || (raw_role != U32_NONE && raw_role >= object_role_count)
            {
                return Err(InputWireError::wire(
                    "role automaton transition is dangling",
                ));
            }
            transitions.push(DecodedRoleTransition {
                source_state,
                target_state,
                role_id: (raw_role != U32_NONE).then_some(raw_role),
            });
        }
        if transitions
            .windows(2)
            .any(|pair| transition_key(&pair[0]) >= transition_key(&pair[1]))
        {
            return Err(InputWireError::wire(
                "role automaton transitions are not canonically unique",
            ));
        }
        expected_transition = expected_transition
            .checked_add(transition_count)
            .ok_or_else(|| InputWireError::wire("role transition range overflows"))?;
        automata.push(DecodedRoleAutomaton {
            component_id,
            state_count,
            initial_state,
            final_states,
            transitions,
        });
    }
    if usize_from_u32(expected_transition, "role transition count")? != transition_records.len()
        || automata
            .windows(2)
            .any(|pair| pair[0].component_id >= pair[1].component_id)
    {
        return Err(InputWireError::wire(
            "role automata do not canonically partition transitions",
        ));
    }
    Ok(DecodedRoleModel {
        object_role_count,
        data_property_count,
        inverse_role_ids,
        simple_inclusions,
        data_inclusions,
        complex_inclusions,
        non_simple_components,
        automata,
        top_object_role_id,
        bottom_object_role_id,
        top_data_property_id,
        bottom_data_property_id,
    })
}

fn transition_key(value: &DecodedRoleTransition) -> (u32, u32, u32) {
    (
        value.source_state,
        value.role_id.unwrap_or(U32_NONE),
        value.target_state,
    )
}

fn decode_datatype_model(
    document: &Document,
    strings: &[u8],
    u32s: &[u8],
    literal_count: u32,
    data_value_count: u32,
    data_range_count: u32,
) -> InputResult<DecodedDatatypeModel> {
    let record = document.require(SectionKind::Datatype)?;
    let semantic_payload_json = read_canonical_json(
        strings,
        read_u32(record, 0)?,
        read_u32(record, 4)?,
        "datatype semantic payload",
    )?;
    let unknown_datatype_ids = read_u32_range(u32s, read_u32(record, 8)?, read_u32(record, 12)?)?;
    validate_sorted_unique(&unknown_datatype_ids, "unknown datatype IDs")?;
    if unknown_datatype_ids
        .iter()
        .any(|value| *value >= data_range_count)
    {
        return Err(InputWireError::wire("unknown datatype ID is dangling"));
    }
    let mut literal_identities = Vec::new();
    reserve_count(
        &mut literal_identities,
        document.count(SectionKind::Literals)?,
        "literal identities",
    )?;
    for (identifier, literal) in records(document.require(SectionKind::Literals)?, 24)?
        .iter()
        .enumerate()
    {
        let source_literal_id = read_u32(literal, 0)?;
        let data_identity_id = read_u32(literal, 4)?;
        if source_literal_id != u32::try_from(identifier).unwrap_or(u32::MAX)
            || data_identity_id >= data_value_count
        {
            return Err(InputWireError::wire(
                "literal identity source/data ID is not dense or is dangling",
            ));
        }
        literal_identities.push(DecodedLiteralIdentity {
            source_literal_id,
            data_identity_id,
            comparison_key: read_string(
                strings,
                read_u32(literal, 8)?,
                read_u32(literal, 12)?,
                false,
            )?,
            semantic_payload_json: read_canonical_json(
                strings,
                read_u32(literal, 16)?,
                read_u32(literal, 20)?,
                "literal semantic payload",
            )?,
        });
    }
    if literal_identities.len() != usize_from_u32(literal_count, "literal count")? {
        return Err(InputWireError::wire(
            "datatype identities do not cover source literals densely",
        ));
    }
    let mut datatype_definitions = Vec::new();
    reserve_count(
        &mut datatype_definitions,
        document.count(SectionKind::DatatypeDefinitions)?,
        "datatype definitions",
    )?;
    for definition in records(document.require(SectionKind::DatatypeDefinitions)?, 8)? {
        let left = read_u32(definition, 0)?;
        let right = read_u32(definition, 4)?;
        if left >= data_range_count || right >= data_range_count {
            return Err(InputWireError::wire("datatype definition ID is dangling"));
        }
        datatype_definitions.push((left, right));
    }
    validate_sorted_unique(&datatype_definitions, "datatype definitions")?;
    Ok(DecodedDatatypeModel {
        literal_identities,
        datatype_definitions,
        unknown_datatype_ids,
        semantic_payload_json,
    })
}

fn decode_expressivity(bytes: &[u8]) -> InputResult<DecodedExpressivity> {
    let flags = read_u32(bytes, 0)?;
    if flags & !0b11_1111_1111 != 0 || read_u32(bytes, 4)? != 0 {
        return Err(InputWireError::version(
            "expressivity flags or reserved bits are invalid",
        ));
    }
    Ok(DecodedExpressivity {
        inverse_roles: flags & 1 != 0,
        nominals: flags & (1 << 1) != 0,
        datatypes: flags & (1 << 2) != 0,
        unknown_datatypes: flags & (1 << 3) != 0,
        complex_roles: flags & (1 << 4) != 0,
        number_restrictions: flags & (1 << 5) != 0,
        keys: flags & (1 << 6) != 0,
        non_horn: flags & (1 << 7) != 0,
        bottom_properties: flags & (1 << 8) != 0,
        abox: flags & (1 << 9) != 0,
    })
}

fn validate_predicate_arity(kind: PredicateKind, sorts: &[TermSort]) -> InputResult<()> {
    let valid = match kind {
        PredicateKind::Concept
        | PredicateKind::NegatedConcept
        | PredicateKind::Nominal
        | PredicateKind::NegatedNominal
        | PredicateKind::AtLeastObject
        | PredicateKind::AtLeastData
        | PredicateKind::AutomatonState
        | PredicateKind::DisjointGuard
        | PredicateKind::NamedIndividual => sorts.len() == 1,
        PredicateKind::ObjectRole
        | PredicateKind::NegatedObjectRole
        | PredicateKind::DataRole
        | PredicateKind::NegatedDataRole
        | PredicateKind::Equality
        | PredicateKind::Inequality
        | PredicateKind::OrderingGuard => sorts.len() == 2,
        PredicateKind::DataRange | PredicateKind::NegatedDataRange => !sorts.is_empty(),
        PredicateKind::AnnotatedEquality => sorts.len() == 3,
    };
    if !valid {
        return Err(InputWireError::wire(
            "predicate arity does not match its kind",
        ));
    }
    Ok(())
}

fn validate_predicate_shape(
    predicate: &DecodedPredicate,
    domain_counts: &[u32; 8],
) -> InputResult<()> {
    let object_unary = matches!(
        predicate.kind,
        PredicateKind::Concept
            | PredicateKind::NegatedConcept
            | PredicateKind::Nominal
            | PredicateKind::NegatedNominal
            | PredicateKind::AtLeastObject
            | PredicateKind::AtLeastData
            | PredicateKind::AutomatonState
            | PredicateKind::DisjointGuard
            | PredicateKind::NamedIndividual
    );
    if object_unary && predicate.argument_sorts != [TermSort::Object] {
        return Err(InputWireError::wire(
            "object-unary predicate has an invalid sort",
        ));
    }
    if matches!(
        predicate.kind,
        PredicateKind::DataRange | PredicateKind::NegatedDataRange
    ) && predicate
        .argument_sorts
        .iter()
        .any(|sort| *sort != TermSort::Data)
    {
        return Err(InputWireError::wire(
            "data-range predicate has an object sort",
        ));
    }
    match predicate.kind {
        PredicateKind::ObjectRole | PredicateKind::NegatedObjectRole
            if predicate.argument_sorts != [TermSort::Object, TermSort::Object] =>
        {
            return Err(InputWireError::wire(
                "object-role predicate sorts are invalid",
            ));
        }
        PredicateKind::DataRole | PredicateKind::NegatedDataRole
            if predicate.argument_sorts != [TermSort::Object, TermSort::Data] =>
        {
            return Err(InputWireError::wire(
                "data-role predicate sorts are invalid",
            ));
        }
        PredicateKind::Equality | PredicateKind::Inequality | PredicateKind::OrderingGuard
            if predicate.argument_sorts[0] != predicate.argument_sorts[1] =>
        {
            return Err(InputWireError::wire(
                "equality/ordering predicate mixes term sorts",
            ));
        }
        PredicateKind::AnnotatedEquality if predicate.argument_sorts != [TermSort::Object; 3] => {
            return Err(InputWireError::wire(
                "annotated-equality predicate sorts are invalid",
            ));
        }
        _ => {}
    }
    let cardinality_kind = matches!(
        predicate.kind,
        PredicateKind::AtLeastObject
            | PredicateKind::AtLeastData
            | PredicateKind::AnnotatedEquality
    );
    if cardinality_kind {
        if predicate.cardinality == Some(0)
            || predicate.cardinality.is_none()
            || predicate.role_id.is_none()
            || predicate.filler_predicate_id.is_none()
        {
            return Err(InputWireError::wire(
                "cardinality predicate fields are incomplete",
            ));
        }
    } else if predicate.cardinality.is_some() || predicate.filler_predicate_id.is_some() {
        return Err(InputWireError::wire(
            "non-cardinality predicate carries cardinality fields",
        ));
    }
    let role_kind = matches!(
        predicate.kind,
        PredicateKind::ObjectRole
            | PredicateKind::NegatedObjectRole
            | PredicateKind::DataRole
            | PredicateKind::NegatedDataRole
    );
    if role_kind && predicate.role_id.is_none() {
        return Err(InputWireError::wire("role predicate has no role ID"));
    }
    if !role_kind && !cardinality_kind && predicate.role_id.is_some() {
        return Err(InputWireError::wire(
            "predicate kind cannot carry a role ID",
        ));
    }
    let concept_kind = matches!(
        predicate.kind,
        PredicateKind::Concept
            | PredicateKind::NegatedConcept
            | PredicateKind::Nominal
            | PredicateKind::NegatedNominal
    );
    let data_range_kind = matches!(
        predicate.kind,
        PredicateKind::DataRange | PredicateKind::NegatedDataRange
    );
    if concept_kind {
        if predicate
            .symbol_id
            .is_none_or(|value| value >= domain_counts[SymbolKind::ClassExpression.index()])
        {
            return Err(InputWireError::wire(
                "concept predicate symbol ID is absent or dangling",
            ));
        }
    } else if data_range_kind {
        if predicate
            .symbol_id
            .is_none_or(|value| value >= domain_counts[SymbolKind::DataRange.index()])
        {
            return Err(InputWireError::wire(
                "data-range predicate symbol ID is absent or dangling",
            ));
        }
    } else if predicate.symbol_id.is_some() {
        return Err(InputWireError::wire(
            "predicate kind cannot carry a symbol ID",
        ));
    }
    let annotation_kind = matches!(
        predicate.kind,
        PredicateKind::Nominal
            | PredicateKind::NegatedNominal
            | PredicateKind::AtLeastData
            | PredicateKind::AutomatonState
            | PredicateKind::DisjointGuard
    );
    if !annotation_kind && !predicate.annotation.is_empty() {
        return Err(InputWireError::wire(
            "predicate kind cannot carry annotations",
        ));
    }
    if matches!(
        predicate.kind,
        PredicateKind::Nominal | PredicateKind::NegatedNominal
    ) {
        if predicate.annotation.is_empty() {
            return Err(InputWireError::wire("nominal annotation is empty"));
        }
        validate_sorted_unique(&predicate.annotation, "nominal annotation")?;
        if predicate
            .annotation
            .iter()
            .any(|value| *value >= domain_counts[SymbolKind::Individual.index()])
        {
            return Err(InputWireError::wire("nominal individual ID is dangling"));
        }
    }
    if predicate.kind == PredicateKind::AtLeastData
        && (predicate.annotation.is_empty()
            || predicate.annotation.first().copied() != predicate.role_id)
    {
        return Err(InputWireError::wire(
            "data at-least annotation does not begin with its role",
        ));
    }
    if predicate.kind == PredicateKind::AutomatonState && predicate.annotation.len() != 2 {
        return Err(InputWireError::wire(
            "automaton-state annotation must have component/state IDs",
        ));
    }
    if predicate.kind == PredicateKind::DisjointGuard && predicate.annotation.len() != 1 {
        return Err(InputWireError::wire(
            "disjoint-guard annotation must have one ID",
        ));
    }
    let internal_kind = matches!(
        predicate.kind,
        PredicateKind::AutomatonState
            | PredicateKind::DisjointGuard
            | PredicateKind::OrderingGuard
            | PredicateKind::NamedIndividual
    );
    if internal_kind != predicate.internal_key.is_some() {
        return Err(InputWireError::wire(
            "predicate internal-key presence does not match its kind",
        ));
    }
    if predicate.kind == PredicateKind::OrderingGuard {
        let expected = match predicate.argument_sorts[0] {
            TermSort::Object => "canonical-object-order",
            TermSort::Data => "canonical-data-order",
        };
        if predicate.internal_key.as_deref() != Some(expected) {
            return Err(InputWireError::wire(
                "ordering-guard internal key is noncanonical",
            ));
        }
    }
    Ok(())
}

fn validate_predicate_cross_references(
    predicates: &[DecodedPredicate],
    roles: &DecodedRoleModel,
    datatypes: &DecodedDatatypeModel,
    domain_counts: &[u32; 8],
) -> InputResult<()> {
    let automata: BTreeMap<u32, &DecodedRoleAutomaton> = roles
        .automata
        .iter()
        .map(|value| (value.component_id, value))
        .collect();
    for predicate in predicates {
        if let Some(role_id) = predicate.role_id {
            let limit = if matches!(
                predicate.kind,
                PredicateKind::DataRole
                    | PredicateKind::NegatedDataRole
                    | PredicateKind::AtLeastData
            ) {
                roles.data_property_count
            } else {
                roles.object_role_count
            };
            if role_id >= limit {
                return Err(InputWireError::wire("predicate role ID is dangling"));
            }
        }
        if predicate.kind == PredicateKind::AtLeastData
            && predicate
                .annotation
                .iter()
                .any(|value| *value >= roles.data_property_count)
        {
            return Err(InputWireError::wire("data at-least role tuple is dangling"));
        }
        if predicate.kind == PredicateKind::AutomatonState {
            let component = predicate.annotation[0];
            let state = predicate.annotation[1];
            if automata
                .get(&component)
                .is_none_or(|automaton| state >= automaton.state_count)
            {
                return Err(InputWireError::wire(
                    "automaton-state predicate is dangling",
                ));
            }
        }
        if let Some(filler_id) = predicate.filler_predicate_id {
            let filler = &predicates[usize_from_u32(filler_id, "filler predicate")?];
            if matches!(
                predicate.kind,
                PredicateKind::AtLeastObject | PredicateKind::AnnotatedEquality
            ) && !matches!(
                filler.kind,
                PredicateKind::Concept
                    | PredicateKind::NegatedConcept
                    | PredicateKind::Nominal
                    | PredicateKind::NegatedNominal
            ) {
                return Err(InputWireError::wire(
                    "object-cardinality filler is not an object concept",
                ));
            }
            if predicate.kind == PredicateKind::AtLeastData
                && (!matches!(
                    filler.kind,
                    PredicateKind::DataRange | PredicateKind::NegatedDataRange
                ) || filler.argument_sorts.len() != predicate.annotation.len())
            {
                return Err(InputWireError::wire(
                    "data-cardinality filler shape is invalid",
                ));
            }
        }
    }
    if datatypes.literal_identities.len()
        != usize_from_u32(
            domain_counts[SymbolKind::SourceLiteral.index()],
            "literal count",
        )?
    {
        return Err(InputWireError::wire(
            "datatype literal identity coverage is inconsistent",
        ));
    }
    Ok(())
}

#[allow(clippy::suspicious_operation_groupings)]
fn validate_role_model_value(
    roles: &DecodedRoleModel,
    _domain_counts: &[u32; 8],
) -> InputResult<()> {
    // Role IDs include the built-ins and may therefore outnumber the named-role
    // symbol domains. Predicate references below are checked against these
    // authoritative role-model counts instead of assuming the two namespaces
    // have equal cardinality.
    if roles.object_role_count == 0 || roles.data_property_count == 0 {
        return Err(InputWireError::wire(
            "role-model counts omit required built-ins",
        ));
    }
    if roles.inverse_role_ids.len() != usize_from_u32(roles.object_role_count, "object role count")?
        || roles
            .inverse_role_ids
            .iter()
            .any(|value| *value >= roles.object_role_count)
    {
        return Err(InputWireError::wire(
            "inverse role map is incomplete or dangling",
        ));
    }
    for (identifier, inverse) in roles.inverse_role_ids.iter().enumerate() {
        let inverse_index = usize_from_u32(*inverse, "inverse role ID")?;
        if roles.inverse_role_ids.get(inverse_index).copied()
            != Some(u32::try_from(identifier).unwrap_or(u32::MAX))
        {
            return Err(InputWireError::wire(
                "inverse role map is not an involution",
            ));
        }
    }
    validate_sorted_unique(&roles.simple_inclusions, "object role inclusions")?;
    validate_sorted_unique(&roles.data_inclusions, "data role inclusions")?;
    validate_sorted_unique(&roles.complex_inclusions, "complex role inclusions")?;
    validate_sorted_unique(&roles.non_simple_components, "non-simple role components")?;
    if roles
        .simple_inclusions
        .iter()
        .any(|(left, right)| *left >= roles.object_role_count || *right >= roles.object_role_count)
        || roles.data_inclusions.iter().any(|(left, right)| {
            *left >= roles.data_property_count || *right >= roles.data_property_count
        })
        || roles.complex_inclusions.iter().any(|(chain, target)| {
            chain.len() < 2
                || *target >= roles.object_role_count
                || chain
                    .iter()
                    .any(|identifier| *identifier >= roles.object_role_count)
        })
        || roles
            .non_simple_components
            .iter()
            .any(|identifier| *identifier >= roles.object_role_count)
    {
        return Err(InputWireError::wire(
            "role-model inclusion or component reference is dangling",
        ));
    }
    if roles.top_object_role_id >= roles.object_role_count
        || roles.bottom_object_role_id >= roles.object_role_count
        || roles.top_data_property_id >= roles.data_property_count
        || roles.bottom_data_property_id >= roles.data_property_count
    {
        return Err(InputWireError::wire("role-model built-in ID is dangling"));
    }
    for (index, automaton) in roles.automata.iter().enumerate() {
        if (automaton.component_id >= roles.object_role_count)
            || (automaton.state_count == 0)
            || (automaton.initial_state >= automaton.state_count)
            || automaton.final_states.is_empty()
            || automaton
                .final_states
                .iter()
                .any(|state| *state >= automaton.state_count)
        {
            return Err(InputWireError::wire("role automaton header is invalid"));
        }
        validate_sorted_unique(&automaton.final_states, "role automaton final states")?;
        if index > 0 && roles.automata[index - 1].component_id >= automaton.component_id {
            return Err(InputWireError::wire(
                "role automata are not canonically ordered",
            ));
        }
        if automaton
            .transitions
            .windows(2)
            .any(|pair| transition_key(&pair[0]) >= transition_key(&pair[1]))
            || automaton.transitions.iter().any(|transition| {
                transition.source_state >= automaton.state_count
                    || transition.target_state >= automaton.state_count
                    || transition
                        .role_id
                        .is_some_and(|role| role >= roles.object_role_count)
            })
        {
            return Err(InputWireError::wire(
                "role automaton transitions are dangling or noncanonical",
            ));
        }
    }
    Ok(())
}

fn validate_datatype_model_value(
    datatypes: &DecodedDatatypeModel,
    domain_counts: &[u32; 8],
) -> InputResult<()> {
    let literal_count = domain_counts[SymbolKind::SourceLiteral.index()];
    let data_value_count = domain_counts[SymbolKind::DataValue.index()];
    let data_range_count = domain_counts[SymbolKind::DataRange.index()];
    if datatypes.literal_identities.len() != usize_from_u32(literal_count, "literal count")? {
        return Err(InputWireError::wire(
            "datatype identities do not cover source literals densely",
        ));
    }
    for (identifier, literal) in datatypes.literal_identities.iter().enumerate() {
        if usize::try_from(literal.source_literal_id).ok() != Some(identifier)
            || literal.data_identity_id >= data_value_count
            || literal.comparison_key.is_empty()
        {
            return Err(InputWireError::wire(
                "literal identity source/data ID is not dense or is dangling",
            ));
        }
        validate_canonical_json_text(&literal.semantic_payload_json, "literal semantic payload")?;
    }
    validate_sorted_unique(&datatypes.datatype_definitions, "datatype definitions")?;
    if datatypes
        .datatype_definitions
        .iter()
        .any(|(left, right)| *left >= data_range_count || *right >= data_range_count)
    {
        return Err(InputWireError::wire("datatype definition ID is dangling"));
    }
    validate_sorted_unique(&datatypes.unknown_datatype_ids, "unknown datatype IDs")?;
    if datatypes
        .unknown_datatype_ids
        .iter()
        .any(|value| *value >= data_range_count)
    {
        return Err(InputWireError::wire("unknown datatype ID is dangling"));
    }
    let semantic = validate_canonical_json_text(
        &datatypes.semantic_payload_json,
        "datatype semantic payload",
    )?;
    let semantic_count = semantic
        .as_object()
        .and_then(|value| value.get("data_ranges"))
        .and_then(serde_json::Value::as_array)
        .map(Vec::len)
        .ok_or_else(|| {
            InputWireError::wire("datatype semantic payload has no data_ranges collection")
        })?;
    if semantic_count != usize_from_u32(data_range_count, "data range count")? {
        return Err(InputWireError::wire(
            "datatype semantic payload does not cover the data-range domain",
        ));
    }
    Ok(())
}

fn validate_canonical_json_text(value: &str, name: &str) -> InputResult<serde_json::Value> {
    let parsed: serde_json::Value = serde_json::from_str(value)
        .map_err(|_| InputWireError::wire(format!("{name} is not valid JSON")))?;
    let canonical = serde_json::to_string(&parsed)
        .map_err(|_| InputWireError::wire(format!("{name} cannot be canonicalized")))?;
    if canonical != value {
        return Err(InputWireError::wire(format!(
            "{name} is not canonical JSON"
        )));
    }
    Ok(parsed)
}

fn validate_owned_atom(
    atom: &DecodedAtom,
    predicates: &[DecodedPredicate],
    individual_count: u32,
    literal_count: u32,
    data_value_count: u32,
    ground: bool,
) -> InputResult<()> {
    let predicate = predicates
        .get(usize_from_u32(atom.predicate_id, "atom predicate ID")?)
        .ok_or_else(|| InputWireError::wire("atom predicate ID is dangling"))?;
    validate_argument_list(
        &atom.arguments,
        predicate,
        individual_count,
        literal_count,
        data_value_count,
        ground,
    )
}

fn validate_owned_ground_atom(
    atom: &DecodedGroundAtom,
    predicates: &[DecodedPredicate],
    individual_count: u32,
    literal_count: u32,
    data_value_count: u32,
    provenance_count: u32,
) -> InputResult<()> {
    let predicate = predicates
        .get(usize_from_u32(
            atom.predicate_id,
            "ground atom predicate ID",
        )?)
        .ok_or_else(|| InputWireError::wire("ground atom predicate ID is dangling"))?;
    validate_argument_list(
        &atom.arguments,
        predicate,
        individual_count,
        literal_count,
        data_value_count,
        true,
    )?;
    validate_owned_provenance(&atom.provenance_ids, provenance_count, "ground atom")
}

fn validate_owned_provenance(values: &[u32], count: u32, name: &str) -> InputResult<()> {
    if values.is_empty() || values.iter().any(|value| *value >= count) {
        return Err(InputWireError::wire(format!(
            "{name} provenance is empty or dangling"
        )));
    }
    validate_sorted_unique(values, &format!("{name} provenance"))
}

fn validate_expressivity_value(program: &DecodedProgram) -> InputResult<()> {
    let observed_non_horn = !program.ground_disjunctions.is_empty()
        || program.clauses.iter().any(|clause| clause.head.len() > 1);
    let observed_nominals = program.predicates.iter().any(|predicate| {
        matches!(
            predicate.kind,
            PredicateKind::Nominal | PredicateKind::NegatedNominal
        )
    });
    let observed_datatypes = !program.datatype_model.literal_identities.is_empty()
        || !program.datatype_model.datatype_definitions.is_empty()
        || !program.datatype_model.unknown_datatype_ids.is_empty()
        || program.predicates.iter().any(|predicate| {
            matches!(
                predicate.kind,
                PredicateKind::DataRange
                    | PredicateKind::NegatedDataRange
                    | PredicateKind::AtLeastData
            ) || (matches!(
                predicate.kind,
                PredicateKind::DataRole | PredicateKind::NegatedDataRole
            ) && predicate.role_id != Some(program.role_model.bottom_data_property_id))
        });
    let observed_complex_roles = !program.role_model.complex_inclusions.is_empty()
        || !program.role_model.automata.is_empty();
    let observed_cardinality = program.predicates.iter().any(|predicate| {
        matches!(
            predicate.kind,
            PredicateKind::AtLeastObject
                | PredicateKind::AtLeastData
                | PredicateKind::AnnotatedEquality
        )
    });
    let observed_keys = program.clauses.iter().any(|clause| {
        clause.body.iter().any(|atom| {
            program.predicates[usize::try_from(atom.predicate_id).unwrap_or(usize::MAX)].kind
                == PredicateKind::NamedIndividual
        }) && clause.body.iter().any(|atom| {
            program.predicates[usize::try_from(atom.predicate_id).unwrap_or(usize::MAX)].kind
                == PredicateKind::OrderingGuard
        }) && clause.head.iter().any(|atom| {
            program.predicates[usize::try_from(atom.predicate_id).unwrap_or(usize::MAX)].kind
                == PredicateKind::Equality
        })
    });
    if observed_non_horn && !program.expressivity.non_horn {
        return Err(InputWireError::wire(
            "expressivity incorrectly marks a non-Horn program as Horn",
        ));
    }
    if observed_nominals && !program.expressivity.nominals {
        return Err(InputWireError::wire("expressivity omits compiled nominals"));
    }
    if observed_datatypes && !program.expressivity.datatypes {
        return Err(InputWireError::wire(
            "expressivity omits compiled datatype constraints",
        ));
    }
    if !program.datatype_model.unknown_datatype_ids.is_empty()
        && !program.expressivity.unknown_datatypes
    {
        return Err(InputWireError::wire(
            "expressivity omits unknown datatype restrictions",
        ));
    }
    if observed_complex_roles && !program.expressivity.complex_roles {
        return Err(InputWireError::wire(
            "expressivity omits complex role clauses or automata",
        ));
    }
    if observed_cardinality && !program.expressivity.number_restrictions {
        return Err(InputWireError::wire(
            "expressivity omits compiled number restrictions",
        ));
    }
    if observed_keys && !program.expressivity.keys {
        return Err(InputWireError::wire("expressivity omits compiled keys"));
    }
    Ok(())
}

const fn is_negative_fact_kind(kind: PredicateKind) -> bool {
    matches!(
        kind,
        PredicateKind::NegatedConcept
            | PredicateKind::NegatedNominal
            | PredicateKind::NegatedObjectRole
            | PredicateKind::NegatedDataRole
            | PredicateKind::NegatedDataRange
    )
}

fn validate_argument_list(
    arguments: &[DecodedTerm],
    predicate: &DecodedPredicate,
    individual_count: u32,
    literal_count: u32,
    data_value_count: u32,
    ground: bool,
) -> InputResult<()> {
    if arguments.len() != predicate.argument_sorts.len() {
        return Err(InputWireError::wire(
            "atom arity does not match its predicate",
        ));
    }
    for (argument, expected_sort) in arguments.iter().zip(&predicate.argument_sorts) {
        if argument.sort() != *expected_sort {
            return Err(InputWireError::wire(
                "atom argument sort does not match its predicate",
            ));
        }
        match argument {
            DecodedTerm::Variable { .. } if ground => {
                return Err(InputWireError::wire("ground atom contains a variable"));
            }
            DecodedTerm::Individual { individual_id } if *individual_id >= individual_count => {
                return Err(InputWireError::wire("atom individual ID is dangling"));
            }
            DecodedTerm::Data {
                source_literal_id,
                data_identity_id,
            } if *source_literal_id >= literal_count || *data_identity_id >= data_value_count => {
                return Err(InputWireError::wire(
                    "atom literal/data identity ID is dangling",
                ));
            }
            _ => {}
        }
    }
    Ok(())
}

fn validate_query_prefix(
    program: &DecodedProgram,
    first_local_predicate_id: u32,
    first_local_symbols: &[u32; 8],
) -> InputResult<()> {
    if usize_from_u32(first_local_predicate_id, "query predicate boundary")?
        > program.predicates.len()
    {
        return Err(InputWireError::wire(
            "query predicate prefix boundary is outside the overlay",
        ));
    }
    for domain in &program.symbol_domains {
        let cutoff = first_local_symbols[domain.kind.index()];
        let cutoff_index = usize_from_u32(cutoff, "query symbol boundary")?;
        if cutoff_index > domain.values.len()
            || domain.values[..cutoff_index]
                .iter()
                .any(|value| value.query_local)
            || domain.values[cutoff_index..]
                .iter()
                .any(|value| !value.query_local)
        {
            return Err(InputWireError::wire(
                "query-local symbol flags disagree with their prefix boundary",
            ));
        }
    }
    Ok(())
}

fn decode_delta_facts(bytes: &[u8], terms: &[DecodedTerm]) -> InputResult<Vec<DecodedDeltaFact>> {
    let mut values = Vec::new();
    reserve_count(
        &mut values,
        u32::try_from(bytes.len() / 16).unwrap_or(u32::MAX),
        "delta facts",
    )?;
    for record in records(bytes, 16)? {
        if record[12] > 1 || record[13..16].iter().any(|value| *value != 0) {
            return Err(InputWireError::wire(
                "delta fact flags or reserved bytes are invalid",
            ));
        }
        let arguments = clone_range(
            terms,
            read_u32(record, 4)?,
            read_u32(record, 8)?,
            "delta fact terms",
        )?;
        if arguments
            .iter()
            .any(|value| matches!(value, DecodedTerm::Variable { .. }))
        {
            return Err(InputWireError::wire("delta fact contains a variable"));
        }
        values.push(DecodedDeltaFact {
            predicate_id: read_u32(record, 0)?,
            arguments,
            negative: record[12] != 0,
        });
    }
    Ok(values)
}

fn parse_backend(value: u8) -> InputResult<BackendChoice> {
    match value {
        0 => Ok(BackendChoice::Auto),
        1 => Ok(BackendChoice::Python),
        2 => Ok(BackendChoice::Native),
        3 => Ok(BackendChoice::Verify),
        _ => Err(InputWireError::wire("config backend enum is invalid")),
    }
}

fn parse_fresh(value: u8) -> InputResult<FreshEntityChoice> {
    match value {
        0 => Ok(FreshEntityChoice::Disallow),
        1 => Ok(FreshEntityChoice::Allow),
        _ => Err(InputWireError::wire("config fresh-entity enum is invalid")),
    }
}

fn parse_grouping(value: u8) -> InputResult<IndividualGroupingChoice> {
    match value {
        0 => Ok(IndividualGroupingChoice::BySameAs),
        1 => Ok(IndividualGroupingChoice::ByName),
        _ => Err(InputWireError::wire(
            "config individual-grouping enum is invalid",
        )),
    }
}

fn parse_unsupported_datatype(value: u8) -> InputResult<UnsupportedDatatypeChoice> {
    match value {
        0 => Ok(UnsupportedDatatypeChoice::Error),
        1 => Ok(UnsupportedDatatypeChoice::IgnoreWithWarning),
        _ => Err(InputWireError::wire(
            "config unsupported-datatype enum is invalid",
        )),
    }
}

fn parse_blocking(value: u8) -> InputResult<BlockingChoice> {
    match value {
        0 => Ok(BlockingChoice::Auto),
        1 => Ok(BlockingChoice::Anywhere),
        2 => Ok(BlockingChoice::ValidatedAnywhere),
        3 => Ok(BlockingChoice::Ancestor),
        _ => Err(InputWireError::wire("config blocking enum is invalid")),
    }
}

fn parse_existential(value: u8) -> InputResult<ExistentialChoice> {
    match value {
        0 => Ok(ExistentialChoice::Auto),
        1 => Ok(ExistentialChoice::CreationOrder),
        2 => Ok(ExistentialChoice::IndividualReuse),
        _ => Err(InputWireError::wire("config existential enum is invalid")),
    }
}

fn optional_u32(flags: u16, bit: u8, value: u32, name: &str) -> InputResult<Option<u32>> {
    if flags & (1_u16 << bit) != 0 {
        if value == U32_NONE {
            return Err(InputWireError::wire(format!(
                "present predicate {name} uses the absent sentinel"
            )));
        }
        Ok(Some(value))
    } else if value == U32_NONE {
        Ok(None)
    } else {
        Err(InputWireError::wire(format!(
            "absent predicate {name} has a concrete value"
        )))
    }
}

fn read_canonical_json(
    strings: &[u8],
    offset: u32,
    length: u32,
    name: &str,
) -> InputResult<String> {
    let value = read_string(strings, offset, length, false)?;
    let parsed: serde_json::Value = serde_json::from_str(&value)
        .map_err(|_| InputWireError::wire(format!("{name} is not valid JSON")))?;
    let canonical = serde_json::to_string(&parsed)
        .map_err(|_| InputWireError::wire(format!("{name} cannot be canonicalized")))?;
    if canonical != value {
        return Err(InputWireError::wire(format!(
            "{name} is not canonical JSON"
        )));
    }
    Ok(value)
}

fn decode_string_ref_range(
    records_bytes: &[u8],
    strings: &[u8],
    first: u32,
    count: u32,
    allow_empty: bool,
) -> InputResult<Vec<String>> {
    let all_records = records(records_bytes, 8)?;
    let selected = slice_range(&all_records, first, count, "string references")?;
    let mut values = Vec::new();
    reserve_count(&mut values, count, "string references")?;
    for record in selected {
        values.push(read_string(
            strings,
            read_u32(record, 0)?,
            read_u32(record, 4)?,
            allow_empty,
        )?);
    }
    Ok(values)
}

fn decode_digest_records(bytes: &[u8]) -> InputResult<Vec<[u8; 32]>> {
    let mut values = Vec::new();
    reserve_count(
        &mut values,
        u32::try_from(bytes.len() / 32).unwrap_or(u32::MAX),
        "digests",
    )?;
    for record in records(bytes, 32)? {
        values.push(
            record
                .try_into()
                .map_err(|_| InputWireError::wire("digest record length is invalid"))?,
        );
    }
    Ok(values)
}

fn decode_u32_records(bytes: &[u8], name: &str) -> InputResult<Vec<u32>> {
    if bytes.len() % 4 != 0 {
        return Err(InputWireError::wire(format!(
            "{name} byte length is not divisible by four"
        )));
    }
    let mut values = Vec::new();
    reserve_count(
        &mut values,
        u32::try_from(bytes.len() / 4).unwrap_or(u32::MAX),
        name,
    )?;
    for offset in (0..bytes.len()).step_by(4) {
        values.push(read_u32(bytes, offset)?);
    }
    Ok(values)
}

fn read_u32_range(bytes: &[u8], first: u32, count: u32) -> InputResult<Vec<u32>> {
    let byte_first = usize_from_u32(first, "u32-pool offset")?
        .checked_mul(4)
        .ok_or_else(|| InputWireError::wire("u32-pool byte offset overflows"))?;
    let byte_count = usize_from_u32(count, "u32-pool count")?
        .checked_mul(4)
        .ok_or_else(|| InputWireError::wire("u32-pool byte count overflows"))?;
    let end = byte_first
        .checked_add(byte_count)
        .ok_or_else(|| InputWireError::wire("u32-pool range overflows"))?;
    let selected = bytes
        .get(byte_first..end)
        .ok_or_else(|| InputWireError::wire("u32-pool reference is outside the section"))?;
    decode_u32_records(selected, "u32-pool range")
}

fn read_string(strings: &[u8], offset: u32, length: u32, allow_empty: bool) -> InputResult<String> {
    let bytes = read_bytes_slice(strings, offset, length)?;
    if !allow_empty && bytes.is_empty() {
        return Err(InputWireError::wire("referenced string is empty"));
    }
    std::str::from_utf8(bytes)
        .map(str::to_owned)
        .map_err(|_| InputWireError::wire("referenced string is not UTF-8"))
}

fn read_bytes(bytes: &[u8], offset: u32, length: u32) -> InputResult<Vec<u8>> {
    Ok(read_bytes_slice(bytes, offset, length)?.to_vec())
}

fn read_bytes_slice(bytes: &[u8], offset: u32, length: u32) -> InputResult<&[u8]> {
    let start = usize_from_u32(offset, "byte-pool offset")?;
    let end = start
        .checked_add(usize_from_u32(length, "byte-pool length")?)
        .ok_or_else(|| InputWireError::wire("byte-pool reference overflows"))?;
    bytes
        .get(start..end)
        .ok_or_else(|| InputWireError::wire("byte-pool reference is outside the section"))
}

fn records(bytes: &[u8], size: usize) -> InputResult<Vec<&[u8]>> {
    if size == 0 || bytes.len() % size != 0 {
        return Err(InputWireError::wire(
            "fixed-record section has a partial record",
        ));
    }
    Ok(bytes.chunks_exact(size).collect())
}

fn slice_range<'a, T>(values: &'a [T], first: u32, count: u32, name: &str) -> InputResult<&'a [T]> {
    let start = usize_from_u32(first, name)?;
    let end = start
        .checked_add(usize_from_u32(count, name)?)
        .ok_or_else(|| InputWireError::wire(format!("{name} range overflows")))?;
    values
        .get(start..end)
        .ok_or_else(|| InputWireError::wire(format!("{name} range is dangling")))
}

fn clone_range<T: Clone>(values: &[T], first: u32, count: u32, name: &str) -> InputResult<Vec<T>> {
    Ok(slice_range(values, first, count, name)?.to_vec())
}

fn reserve_count<T>(values: &mut Vec<T>, count: u32, name: &str) -> InputResult<()> {
    values
        .try_reserve_exact(usize_from_u32(count, name)?)
        .map_err(|_| InputWireError::resource(format!("{name} allocation failed")))
}

fn validate_sorted_unique<T: Ord>(values: &[T], name: &str) -> InputResult<()> {
    if values.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err(InputWireError::wire(format!(
            "{name} is not sorted and unique"
        )));
    }
    Ok(())
}

fn domain_len(program: &DecodedProgram, kind: SymbolKind) -> InputResult<u32> {
    let count = program
        .domain(kind)
        .ok_or_else(|| InputWireError::wire("program symbol domain is missing"))?
        .values
        .len();
    u32::try_from(count).map_err(|_| InputWireError::resource("symbol domain exceeds u32"))
}

fn read_array_32(bytes: &[u8], offset: usize) -> InputResult<[u8; 32]> {
    bytes
        .get(offset..offset + 32)
        .ok_or_else(|| InputWireError::wire("32-byte field is truncated"))?
        .try_into()
        .map_err(|_| InputWireError::wire("32-byte field length is invalid"))
}

fn read_u16(bytes: &[u8], offset: usize) -> InputResult<u16> {
    let value: [u8; 2] = bytes
        .get(offset..offset + 2)
        .ok_or_else(|| InputWireError::wire("u16 field is truncated"))?
        .try_into()
        .map_err(|_| InputWireError::wire("u16 field length is invalid"))?;
    Ok(u16::from_le_bytes(value))
}

fn read_u32(bytes: &[u8], offset: usize) -> InputResult<u32> {
    let value: [u8; 4] = bytes
        .get(offset..offset + 4)
        .ok_or_else(|| InputWireError::wire("u32 field is truncated"))?
        .try_into()
        .map_err(|_| InputWireError::wire("u32 field length is invalid"))?;
    Ok(u32::from_le_bytes(value))
}

fn read_u64(bytes: &[u8], offset: usize) -> InputResult<u64> {
    let value: [u8; 8] = bytes
        .get(offset..offset + 8)
        .ok_or_else(|| InputWireError::wire("u64 field is truncated"))?
        .try_into()
        .map_err(|_| InputWireError::wire("u64 field length is invalid"))?;
    Ok(u64::from_le_bytes(value))
}

fn read_f64(bytes: &[u8], offset: usize) -> InputResult<f64> {
    let value: [u8; 8] = bytes
        .get(offset..offset + 8)
        .ok_or_else(|| InputWireError::wire("f64 field is truncated"))?
        .try_into()
        .map_err(|_| InputWireError::wire("f64 field length is invalid"))?;
    Ok(f64::from_le_bytes(value))
}

fn usize_from_u32(value: u32, name: &str) -> InputResult<usize> {
    usize::try_from(value).map_err(|_| InputWireError::wire(format!("{name} does not fit usize")))
}

fn u64_to_usize(value: u64, name: &str) -> InputResult<usize> {
    usize::try_from(value).map_err(|_| InputWireError::wire(format!("{name} does not fit usize")))
}
