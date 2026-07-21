//! Transactional named-class, named-individual, and axiom compilation.
//!
//! This phase owns a scalar-compatible `class_expression` symbol domain and
//! a scalar-compatible named-and-anonymous `individual` domain and the exact
//! semantic `source_literal` domain plus scalar-compatible string, Boolean, and
//! exact numeric `data_value` identities needed by later datatype/ABox phases. It compiles
//! `SubClassOf`, `EquivalentClasses`, `DisjointClasses`, `ClassAssertion`,
//! `SameIndividual`, `DifferentIndividuals`, named object-property domains,
//! ranges, assertions, functionality, inverse functionality, and reflexivity,
//! plus named data-property domains, ranges, functionality, string/Boolean/exact-numeric
//! positive and negative assertions, named datatype definitions, and named-class keys
//! into the existing native predicate, clause, fact, and provenance records. Exact
//! nested annotations participate in source provenance, with segmented anonymous
//! scopes remapped before hashing.
//! Predicate and clause identifiers are dense within this fragment and must be
//! remapped when a later phase assembles the complete program; no fragment is
//! publishable on its own.
// SPDX-License-Identifier: LGPL-3.0-or-later

#![forbid(unsafe_code)]

use std::cmp::Ordering;
use std::mem::size_of;

use num_bigint::{BigInt, BigUint, Sign};
use num_integer::Integer;
use num_traits::{ToPrimitive, Zero};
use serde::Serialize;
use sha2::{Digest, Sha256};

use super::canonical::{
    self, annotation_stripped_axiom_digest, source_axiom_digest, AnonymousScopeMap, CanonicalBudget,
};
use super::data_roles::DataRolePhase;
use super::model::{ComponentKind, ComponentValue, NodeId, NodeRef, ScalarRef, ValidatedModel};
use super::object_roles::ObjectRolePhase;
use super::symbols::{RootHandler, SymbolPhase};
use super::{ByteSource, EncodedResult, EncodedValidationError};
use crate::input_wire::{
    DecodedAtom, DecodedClause, DecodedGroundAtom, DecodedPredicate, DecodedProvenanceEntry,
    DecodedSymbolDomain, DecodedSymbolValue, DecodedTerm, PredicateKind, SymbolKind, TermSort,
};

const NAMED_CLASS_PHASE_SCHEMA_VERSION: u16 = 1;
const ENTITY_TAG: u16 = 2;
const ANONYMOUS_INDIVIDUAL_TAG: u16 = 3;
const LITERAL_TAG: u16 = 4;
const DATA_COMPLEMENT_OF_TAG: u16 = 23;
const DATA_ONE_OF_TAG: u16 = 24;
const DATATYPE_RESTRICTION_TAG: u16 = 25;
const OBJECT_ONE_OF_TAG: u16 = 33;
const OBJECT_COMPLEMENT_OF_TAG: u16 = 32;
const SUBCLASS_TAG: u16 = 61;
const EQUIVALENT_CLASSES_TAG: u16 = 62;
const DISJOINT_CLASSES_TAG: u16 = 63;
const OBJECT_PROPERTY_DOMAIN_TAG: u16 = 74;
const OBJECT_PROPERTY_RANGE_TAG: u16 = 75;
const FUNCTIONAL_OBJECT_PROPERTY_TAG: u16 = 76;
const INVERSE_FUNCTIONAL_OBJECT_PROPERTY_TAG: u16 = 77;
const REFLEXIVE_OBJECT_PROPERTY_TAG: u16 = 78;
const DATA_PROPERTY_DOMAIN_TAG: u16 = 93;
const DATA_PROPERTY_RANGE_TAG: u16 = 94;
const FUNCTIONAL_DATA_PROPERTY_TAG: u16 = 95;
const DATATYPE_DEFINITION_TAG: u16 = 100;
const HAS_KEY_TAG: u16 = 101;
const OBJECT_INVERSE_OF_TAG: u16 = 10;
const SAME_INDIVIDUAL_TAG: u16 = 110;
const DIFFERENT_INDIVIDUALS_TAG: u16 = 111;
const CLASS_ASSERTION_TAG: u16 = 112;
const OBJECT_PROPERTY_ASSERTION_TAG: u16 = 113;
const NEGATIVE_OBJECT_PROPERTY_ASSERTION_TAG: u16 = 114;
const DATA_PROPERTY_ASSERTION_TAG: u16 = 115;
const NEGATIVE_DATA_PROPERTY_ASSERTION_TAG: u16 = 116;
const BUILTIN_PROVENANCE_INPUT: &[u8] = b"pyhermit:clausification:builtins:v1";
const DISJOINT_GUARD_DOMAIN: &[u8] = b"pyhermit:linear-disjoint-classes:v1\0";
const THING_DISPLAY: &str = "class:http://www.w3.org/2002/07/owl#Thing";
const NOTHING_DISPLAY: &str = "class:http://www.w3.org/2002/07/owl#Nothing";
const RDFS_LITERAL_DISPLAY: &str = "datatype:http://www.w3.org/2000/01/rdf-schema#Literal";
const NAMED_INDIVIDUAL_PREFIX: &str = "named_individual:";
const ANONYMOUS_INDIVIDUAL_PREFIX: &str = "anonymous:";
const OBJECT_PROPERTY_PREFIX: &str = "object_property:";
const DATA_PROPERTY_PREFIX: &str = "data_property:";
const DATA_IDENTITY_PREFIX: &[u8] = b"pyhermit:data-identity:v1\0";
const ANY_URI_IDENTITY_PREFIX: &str = "[\"any-uri-v1\",";
const HEX_DIGITS: &[u8; 16] = b"0123456789abcdef";
const RDF_PLAIN_LITERAL_IRI: &str = "http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral";
const OWL_RATIONAL_IRI: &str = "http://www.w3.org/2002/07/owl#rational";
const XSD_NAMESPACE: &str = "http://www.w3.org/2001/XMLSchema#";
const XSD_BOOLEAN_IRI: &str = "http://www.w3.org/2001/XMLSchema#boolean";
const XSD_DECIMAL_IRI: &str = "http://www.w3.org/2001/XMLSchema#decimal";
const XSD_FLOAT_IRI: &str = "http://www.w3.org/2001/XMLSchema#float";
const XSD_DOUBLE_IRI: &str = "http://www.w3.org/2001/XMLSchema#double";
const XSD_HEX_BINARY_IRI: &str = "http://www.w3.org/2001/XMLSchema#hexBinary";
const XSD_BASE64_BINARY_IRI: &str = "http://www.w3.org/2001/XMLSchema#base64Binary";
const XSD_ANY_URI_IRI: &str = "http://www.w3.org/2001/XMLSchema#anyURI";
const XSD_DATE_TIME_IRI: &str = "http://www.w3.org/2001/XMLSchema#dateTime";
const XSD_DATE_TIME_STAMP_IRI: &str = "http://www.w3.org/2001/XMLSchema#dateTimeStamp";
const RDF_XML_LITERAL_IRI: &str = "http://www.w3.org/1999/02/22-rdf-syntax-ns#XMLLiteral";
const TOP_OBJECT_IRI: &str = "http://www.w3.org/2002/07/owl#topObjectProperty";
const BOTTOM_OBJECT_IRI: &str = "http://www.w3.org/2002/07/owl#bottomObjectProperty";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct NamedClassPhaseLimits {
    pub max_slices: usize,
    pub max_entity_symbols: usize,
    pub max_class_symbols: usize,
    pub max_data_range_symbols: usize,
    pub max_individual_symbols: usize,
    pub max_source_literal_symbols: usize,
    pub max_data_value_symbols: usize,
    pub max_literal_characters: usize,
    pub max_numeric_digits: usize,
    pub max_decimal_exponent: usize,
    pub max_binary_bytes: usize,
    pub max_xml_depth: usize,
    pub max_xml_nodes: usize,
    pub max_compiled_roots: usize,
    pub max_predicates: usize,
    pub max_clauses: usize,
    pub max_facts: usize,
    pub max_provenance: usize,
    pub max_owned_bytes: usize,
    pub max_work: u64,
    pub max_manifest_bytes: usize,
    pub max_canonical_depth: usize,
    pub max_scope_maps: usize,
}

impl Default for NamedClassPhaseLimits {
    fn default() -> Self {
        Self {
            max_slices: 32_769,
            max_entity_symbols: 16_000_000,
            max_class_symbols: 16_000_000,
            max_data_range_symbols: 16_000_000,
            max_individual_symbols: 16_000_000,
            max_source_literal_symbols: 16_000_000,
            max_data_value_symbols: 16_000_000,
            max_literal_characters: 1_000_000,
            max_numeric_digits: 100_000,
            max_decimal_exponent: 100_000,
            max_binary_bytes: 1_000_000,
            max_xml_depth: 256,
            max_xml_nodes: 100_000,
            max_compiled_roots: 100_000_000,
            max_predicates: 100_000_000,
            max_clauses: 100_000_000,
            max_facts: 100_000_000,
            max_provenance: 100_000_000,
            max_owned_bytes: 512 * 1024 * 1024,
            max_work: 2_000_000_000,
            max_manifest_bytes: 512 * 1024 * 1024,
            max_canonical_depth: 512,
            max_scope_maps: 32,
        }
    }
}

/// Stable declaration/signature bridge between entity and class domains.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ClassSignatureBinding {
    pub class_expression_id: u32,
    pub entity_id: u32,
    pub declared: bool,
}

/// Stable declaration/signature bridge between entity and individual domains.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct IndividualSignatureBinding {
    pub individual_id: u32,
    pub entity_id: u32,
    pub declared: bool,
}

/// Owned output of the named-class compiler transaction.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NamedClassPhase {
    pub class_domain: DecodedSymbolDomain,
    pub class_signature: Vec<ClassSignatureBinding>,
    pub data_range_domain: DecodedSymbolDomain,
    pub individual_domain: DecodedSymbolDomain,
    pub source_literal_domain: DecodedSymbolDomain,
    pub data_value_domain: DecodedSymbolDomain,
    pub individual_signature: Vec<IndividualSignatureBinding>,
    pub named_individuals: Vec<u32>,
    pub predicates: Vec<DecodedPredicate>,
    pub clauses: Vec<DecodedClause>,
    pub positive_facts: Vec<DecodedGroundAtom>,
    pub negative_facts: Vec<DecodedGroundAtom>,
    pub provenance: Vec<DecodedProvenanceEntry>,
    pub compiled_roots: usize,
    pub deferred_roots: usize,
    pub work: u64,
    pub owned_bytes: usize,
    compiled_root_digests: Vec<[u8; 32]>,
    nominal_bindings: Vec<NominalBinding>,
    normalized_edges: Vec<NormalizedEdge>,
    normalized_disjoints: Vec<NormalizedDisjoint>,
    normalized_object_constraints: Vec<NormalizedObjectConstraint>,
    normalized_object_characteristics: Vec<NormalizedObjectCharacteristic>,
    normalized_data_domains: Vec<NormalizedDataDomain>,
    normalized_data_ranges: Vec<NormalizedDataRange>,
    normalized_datatype_definitions: Vec<NormalizedDatatypeDefinition>,
    normalized_keys: Vec<NormalizedKey>,
    normalized_data_functionalities: Vec<NormalizedDataFunctionality>,
    normalized_facts: Vec<NormalizedFact>,
    normalized_object_facts: Vec<NormalizedObjectFact>,
    normalized_negative_object_facts: Vec<NormalizedObjectFact>,
    normalized_data_facts: Vec<NormalizedDataFact>,
    normalized_negative_data_facts: Vec<NormalizedDataFact>,
    normalized_equalities: Vec<NormalizedEqualityFact>,
    normalized_inequalities: Vec<NormalizedInequalityFact>,
    source_data_identity_ids: Vec<Option<u32>>,
    manifest_limit: usize,
}

impl NamedClassPhase {
    /// Canonical private manifest used for exact scalar differential checks.
    pub fn canonical_manifest_json(&self) -> EncodedResult<Vec<u8>> {
        let class_expression_symbols = self
            .class_domain
            .values
            .iter()
            .map(symbol_manifest)
            .collect();
        let class_signature = self
            .class_signature
            .iter()
            .map(|binding| ClassSignatureManifest {
                class_expression_id: binding.class_expression_id,
                entity_id: binding.entity_id,
                declared: binding.declared,
            })
            .collect();
        let data_range_symbols = self
            .data_range_domain
            .values
            .iter()
            .map(symbol_manifest)
            .collect();
        let individual_symbols = self
            .individual_domain
            .values
            .iter()
            .map(symbol_manifest)
            .collect();
        let source_literal_symbols = self
            .source_literal_domain
            .values
            .iter()
            .map(symbol_manifest)
            .collect();
        let data_value_symbols = self
            .data_value_domain
            .values
            .iter()
            .map(symbol_manifest)
            .collect();
        let individual_signature = self
            .individual_signature
            .iter()
            .map(|binding| IndividualSignatureManifest {
                individual_id: binding.individual_id,
                entity_id: binding.entity_id,
                declared: binding.declared,
            })
            .collect();
        let predicates = self
            .predicates
            .iter()
            .map(|predicate| PredicateManifest {
                predicate_id: predicate.predicate_id,
                kind: predicate_kind_name(predicate.kind),
                argument_sorts: predicate
                    .argument_sorts
                    .iter()
                    .copied()
                    .map(term_sort_name)
                    .collect(),
                symbol_id: predicate.symbol_id,
                role_id: predicate.role_id,
                cardinality: predicate.cardinality,
                filler_predicate_id: predicate.filler_predicate_id,
                annotation: &predicate.annotation,
                internal_key: predicate.internal_key.as_deref(),
            })
            .collect();
        let clauses = self
            .clauses
            .iter()
            .map(|clause| ClauseManifest {
                clause_id: clause.clause_id,
                body: clause.body.iter().map(atom_manifest).collect(),
                head: clause.head.iter().map(atom_manifest).collect(),
                provenance_ids: &clause.provenance_ids,
                join_order: &clause.join_order,
            })
            .collect();
        let positive_facts = self
            .positive_facts
            .iter()
            .map(ground_atom_manifest)
            .collect();
        let negative_facts = self
            .negative_facts
            .iter()
            .map(ground_atom_manifest)
            .collect();
        let provenance = self
            .provenance
            .iter()
            .map(|entry| ProvenanceManifest {
                provenance_id: entry.provenance_id,
                source_sha256: entry
                    .source_sha256
                    .iter()
                    .map(|digest| crate::model::hex(digest))
                    .collect(),
                generated: entry.generated,
            })
            .collect();
        let encoded = serde_json::to_vec(&NamedClassManifest {
            schema_version: NAMED_CLASS_PHASE_SCHEMA_VERSION,
            family: "named_class_axioms",
            compiled_roots: self.compiled_roots,
            deferred_roots: self.deferred_roots,
            class_expression_symbols,
            class_signature,
            data_range_symbols,
            individual_symbols,
            source_literal_symbols,
            data_value_symbols,
            individual_signature,
            named_individuals: &self.named_individuals,
            predicates,
            clauses,
            positive_facts,
            negative_facts,
            provenance,
        })
        .map_err(|_| {
            EncodedValidationError::invariant("named-class manifest serialization failed")
        })?;
        if encoded.len() > self.manifest_limit {
            return Err(EncodedValidationError::resource(
                "named-class manifest exceeds its byte limit",
            ));
        }
        Ok(encoded)
    }
}

#[derive(Serialize)]
struct NamedClassManifest<'a> {
    schema_version: u16,
    family: &'static str,
    compiled_roots: usize,
    deferred_roots: usize,
    class_expression_symbols: Vec<SymbolManifest<'a>>,
    class_signature: Vec<ClassSignatureManifest>,
    data_range_symbols: Vec<SymbolManifest<'a>>,
    individual_symbols: Vec<SymbolManifest<'a>>,
    source_literal_symbols: Vec<SymbolManifest<'a>>,
    data_value_symbols: Vec<SymbolManifest<'a>>,
    individual_signature: Vec<IndividualSignatureManifest>,
    named_individuals: &'a [u32],
    predicates: Vec<PredicateManifest<'a>>,
    clauses: Vec<ClauseManifest<'a>>,
    positive_facts: Vec<GroundAtomManifest<'a>>,
    negative_facts: Vec<GroundAtomManifest<'a>>,
    provenance: Vec<ProvenanceManifest>,
}

#[derive(Serialize)]
struct SymbolManifest<'a> {
    identifier: u32,
    key_hex: String,
    display: &'a str,
    generated: bool,
    query_local: bool,
}

fn symbol_manifest(value: &DecodedSymbolValue) -> SymbolManifest<'_> {
    SymbolManifest {
        identifier: value.identifier,
        key_hex: crate::model::hex(&value.key),
        display: &value.display,
        generated: value.generated,
        query_local: value.query_local,
    }
}

#[derive(Serialize)]
struct ClassSignatureManifest {
    class_expression_id: u32,
    entity_id: u32,
    declared: bool,
}

#[derive(Serialize)]
struct IndividualSignatureManifest {
    individual_id: u32,
    entity_id: u32,
    declared: bool,
}

#[derive(Serialize)]
struct PredicateManifest<'a> {
    predicate_id: u32,
    kind: &'static str,
    argument_sorts: Vec<&'static str>,
    symbol_id: Option<u32>,
    role_id: Option<u32>,
    cardinality: Option<u32>,
    filler_predicate_id: Option<u32>,
    annotation: &'a [u32],
    internal_key: Option<&'a str>,
}

#[derive(Serialize)]
struct ClauseManifest<'a> {
    clause_id: u32,
    body: Vec<AtomManifest>,
    head: Vec<AtomManifest>,
    provenance_ids: &'a [u32],
    join_order: &'a [u32],
}

#[derive(Serialize)]
struct GroundAtomManifest<'a> {
    predicate_id: u32,
    arguments: Vec<TermManifest>,
    provenance_ids: &'a [u32],
}

#[derive(Serialize)]
struct AtomManifest {
    predicate_id: u32,
    arguments: Vec<TermManifest>,
}

#[derive(Serialize)]
#[serde(untagged)]
enum TermManifest {
    Variable {
        index: u32,
        sort: &'static str,
    },
    Individual {
        individual_id: u32,
    },
    Data {
        source_literal_id: u32,
        data_identity_id: u32,
    },
}

fn atom_manifest(atom: &DecodedAtom) -> AtomManifest {
    AtomManifest {
        predicate_id: atom.predicate_id,
        arguments: atom.arguments.iter().map(term_manifest).collect(),
    }
}

fn ground_atom_manifest(atom: &DecodedGroundAtom) -> GroundAtomManifest<'_> {
    GroundAtomManifest {
        predicate_id: atom.predicate_id,
        arguments: atom.arguments.iter().map(term_manifest).collect(),
        provenance_ids: &atom.provenance_ids,
    }
}

const fn term_manifest(term: &DecodedTerm) -> TermManifest {
    match term {
        DecodedTerm::Variable { index, sort } => TermManifest::Variable {
            index: *index,
            sort: term_sort_name(*sort),
        },
        DecodedTerm::Individual { individual_id } => TermManifest::Individual {
            individual_id: *individual_id,
        },
        DecodedTerm::Data {
            source_literal_id,
            data_identity_id,
        } => TermManifest::Data {
            source_literal_id: *source_literal_id,
            data_identity_id: *data_identity_id,
        },
    }
}

#[derive(Serialize)]
struct ProvenanceManifest {
    provenance_id: u32,
    source_sha256: Vec<String>,
    generated: bool,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct RawEdge {
    sub_class: u32,
    sub_negative: bool,
    super_class: u32,
    super_negative: bool,
    provenance: [u8; 32],
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct NormalizedEdge {
    sub_class: u32,
    sub_negative: bool,
    super_class: u32,
    super_negative: bool,
    provenance: Vec<[u8; 32]>,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ClassLiteral {
    class_id: u32,
    negative: bool,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct NominalBinding {
    class_id: u32,
    individual_ids: Vec<u32>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum NominalUsage {
    None,
    Positive,
    Negative,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum AtomicClassSource {
    Entity(u32),
    Nominal(NodeId),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct AtomicClassSelection {
    source: AtomicClassSource,
    expression: NodeId,
    negative: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct RawDisjoint {
    classes: Vec<ClassLiteral>,
    guard_digest: [u8; 32],
    provenance: [u8; 32],
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct NormalizedDisjoint {
    classes: Vec<ClassLiteral>,
    provenance: Vec<[u8; 32]>,
    guard_digest: [u8; 32],
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum ObjectConstraintKind {
    Domain,
    Range,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct RawObjectConstraint {
    kind: ObjectConstraintKind,
    role_id: u32,
    class: ClassLiteral,
    provenance: [u8; 32],
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct NormalizedObjectConstraint {
    kind: ObjectConstraintKind,
    role_id: u32,
    class: ClassLiteral,
    provenance: Vec<[u8; 32]>,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum ObjectCharacteristicKind {
    Functional,
    InverseFunctional,
    Reflexive,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct RawObjectCharacteristic {
    kind: ObjectCharacteristicKind,
    role_id: u32,
    provenance: [u8; 32],
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct NormalizedObjectCharacteristic {
    kind: ObjectCharacteristicKind,
    role_id: u32,
    provenance: Vec<[u8; 32]>,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct RawDataDomain {
    role_id: u32,
    class: ClassLiteral,
    provenance: [u8; 32],
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct NormalizedDataDomain {
    role_id: u32,
    class: ClassLiteral,
    provenance: Vec<[u8; 32]>,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct DataRangeLiteral {
    range_id: u32,
    negative: bool,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct RawDataRange {
    role_id: u32,
    range: DataRangeLiteral,
    provenance: [u8; 32],
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct NormalizedDataRange {
    role_id: u32,
    range: DataRangeLiteral,
    provenance: Vec<[u8; 32]>,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct RawDatatypeDefinition {
    left_range: DataRangeLiteral,
    right_range: DataRangeLiteral,
    provenance: [u8; 32],
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct NormalizedDatatypeDefinition {
    left_range: DataRangeLiteral,
    right_range: DataRangeLiteral,
    provenance: Vec<[u8; 32]>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct RawKey {
    class: ClassLiteral,
    object_role_ids: Vec<u32>,
    data_role_ids: Vec<u32>,
    provenance: [u8; 32],
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct NormalizedKey {
    class: ClassLiteral,
    object_role_ids: Vec<u32>,
    data_role_ids: Vec<u32>,
    provenance: Vec<[u8; 32]>,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct RawDataFunctionality {
    role_id: u32,
    provenance: [u8; 32],
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct NormalizedDataFunctionality {
    role_id: u32,
    provenance: Vec<[u8; 32]>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct RawFact {
    class_id: u32,
    individual_id: u32,
    negative: bool,
    provenance: [u8; 32],
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct NormalizedFact {
    class_id: u32,
    individual_id: u32,
    negative: bool,
    provenance: Vec<[u8; 32]>,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct RawObjectFact {
    role_id: u32,
    source_individual: u32,
    target_individual: u32,
    provenance: [u8; 32],
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct NormalizedObjectFact {
    role_id: u32,
    source_individual: u32,
    target_individual: u32,
    provenance: Vec<[u8; 32]>,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct RawDataFact {
    role_id: u32,
    source_individual: u32,
    source_literal_id: u32,
    data_identity_id: u32,
    provenance: [u8; 32],
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct NormalizedDataFact {
    role_id: u32,
    source_individual: u32,
    source_literal_id: u32,
    data_identity_id: u32,
    provenance: Vec<[u8; 32]>,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct RawEqualityFact {
    left_individual: u32,
    right_individual: u32,
    statement_sha256: [u8; 32],
    provenance: [u8; 32],
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct RawInequalityFact {
    left_individual: u32,
    right_individual: u32,
    statement_sha256: [u8; 32],
    provenance: [u8; 32],
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct NormalizedEqualityFact {
    left_individual: u32,
    right_individual: u32,
    statement_sha256: [u8; 32],
    provenance: Vec<[u8; 32]>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct NormalizedInequalityFact {
    left_individual: u32,
    right_individual: u32,
    statement_sha256: [u8; 32],
    provenance: Vec<[u8; 32]>,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum GroundArguments {
    Unary(u32),
    Binary(u32, u32),
    DataBinary(u32, u32, u32),
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct NamedDisjointOutput {
    edges: Vec<RawEdge>,
    disjoint: Option<RawDisjoint>,
    provenance: [u8; 32],
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct PendingIndividualSymbol {
    value: DecodedSymbolValue,
    entity: Option<(u32, bool)>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct PendingClassSymbol {
    value: DecodedSymbolValue,
    entity: Option<(u32, bool)>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ProvenanceKey {
    source_sha256: Vec<[u8; 32]>,
    generated: bool,
}

pub(super) struct PhaseBudget {
    limits: NamedClassPhaseLimits,
    work: u64,
    owned_bytes: usize,
}

impl PhaseBudget {
    pub(super) const fn new(limits: NamedClassPhaseLimits) -> Self {
        Self {
            limits,
            work: 0,
            owned_bytes: 0,
        }
    }

    pub(super) fn claim_work(&mut self, amount: usize) -> EncodedResult<()> {
        let amount = u64::try_from(amount)
            .map_err(|_| EncodedValidationError::resource("named-class work exceeds u64"))?;
        let following = self
            .work
            .checked_add(amount)
            .ok_or_else(|| EncodedValidationError::resource("named-class work overflowed"))?;
        if following > self.limits.max_work {
            return Err(EncodedValidationError::resource(
                "named-class compilation exceeds its work limit",
            ));
        }
        self.work = following;
        Ok(())
    }

    pub(super) fn claim_owned(&mut self, amount: usize) -> EncodedResult<()> {
        let following = self.owned_bytes.checked_add(amount).ok_or_else(|| {
            EncodedValidationError::resource("named-class owned-byte count overflowed")
        })?;
        if following > self.limits.max_owned_bytes {
            return Err(EncodedValidationError::resource(
                "named-class compilation exceeds its owned-byte limit",
            ));
        }
        self.owned_bytes = following;
        Ok(())
    }

    fn count(observed: usize, allowed: usize, name: &'static str) -> EncodedResult<()> {
        if observed > allowed {
            Err(EncodedValidationError::resource(format!(
                "named-class {name} exceeds its limit"
            )))
        } else {
            Ok(())
        }
    }

    pub(super) const fn max_xml_depth(&self) -> usize {
        self.limits.max_xml_depth
    }

    pub(super) const fn max_xml_nodes(&self) -> usize {
        self.limits.max_xml_nodes
    }
}

impl CanonicalBudget for PhaseBudget {
    fn canonical_max_depth(&self) -> usize {
        self.limits.max_canonical_depth
    }

    fn canonical_max_scope_maps(&self) -> usize {
        self.limits.max_scope_maps
    }

    fn claim_canonical_work(&mut self, amount: usize) -> EncodedResult<()> {
        self.claim_work(amount)
    }

    fn claim_canonical_owned(&mut self, amount: usize) -> EncodedResult<()> {
        self.claim_owned(amount)
    }
}

/// Compile the bounded named class and named `ABox` fragment without publishing a session.
pub fn compile_named_class_phase<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    limits: NamedClassPhaseLimits,
) -> EncodedResult<NamedClassPhase> {
    compile_named_class_phase_impl(model, symbols, None, None, &[], limits)
}

/// Compile the named fragment with an inner-to-outer anonymous-scope map
/// chain applied only to exact source provenance.
pub fn compile_named_class_phase_scoped<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    scope_maps: &[AnonymousScopeMap],
    limits: NamedClassPhaseLimits,
) -> EncodedResult<NamedClassPhase> {
    compile_named_class_phase_impl(model, symbols, None, None, scope_maps, limits)
}

/// Compile the named fragment with the source-local object-role domain needed
/// for exact named object-property domain/range clauses.
pub fn compile_named_class_phase_with_object_roles_scoped<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    object_roles: &ObjectRolePhase,
    scope_maps: &[AnonymousScopeMap],
    limits: NamedClassPhaseLimits,
) -> EncodedResult<NamedClassPhase> {
    compile_named_class_phase_impl(model, symbols, Some(object_roles), None, scope_maps, limits)
}

/// Compile the named fragment with source-local object- and data-role domains.
pub fn compile_named_class_phase_with_role_domains_scoped<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    object_roles: &ObjectRolePhase,
    data_roles: &DataRolePhase,
    scope_maps: &[AnonymousScopeMap],
    limits: NamedClassPhaseLimits,
) -> EncodedResult<NamedClassPhase> {
    compile_named_class_phase_impl(
        model,
        symbols,
        Some(object_roles),
        Some(data_roles),
        scope_maps,
        limits,
    )
}

fn compile_named_class_phase_impl<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    object_roles: Option<&ObjectRolePhase>,
    data_roles: Option<&DataRolePhase>,
    scope_maps: &[AnonymousScopeMap],
    limits: NamedClassPhaseLimits,
) -> EncodedResult<NamedClassPhase> {
    let mut budget = PhaseBudget::new(limits);
    canonical::validate_scope_maps(scope_maps, &mut budget)?;
    let declared_class_ids = declared_class_ids(symbols, &mut budget)?;
    let (class_domain, class_signature) = class_signature(
        model,
        symbols,
        &declared_class_ids,
        object_roles.is_some(),
        data_roles.is_some(),
        scope_maps,
        &mut budget,
    )?;
    let data_range_domain = named_data_range_domain(
        model,
        symbols,
        data_roles.is_some(),
        scope_maps,
        &mut budget,
    )?;
    let declared_individual_ids = declared_individual_ids(symbols, &mut budget)?;
    let (individual_domain, individual_signature) = individual_signature(
        model,
        symbols,
        &declared_individual_ids,
        object_roles.is_some(),
        data_roles.is_some(),
        scope_maps,
        &mut budget,
    )?;
    let nominal_bindings = nominal_bindings(
        model,
        symbols,
        &class_domain,
        &individual_signature,
        scope_maps,
        &mut budget,
    )?;
    let (source_literal_domain, data_value_domain, source_data_identity_ids) =
        literal_symbol_domains(model, symbols, &mut budget)?;
    let mut named_individuals = Vec::new();
    budget.claim_owned(
        individual_signature
            .len()
            .checked_mul(size_of::<u32>())
            .ok_or_else(|| {
                EncodedValidationError::resource("named-individual ID output overflowed")
            })?,
    )?;
    named_individuals
        .try_reserve_exact(individual_signature.len())
        .map_err(|_| {
            EncodedValidationError::resource("named-individual ID output allocation failed")
        })?;
    named_individuals.extend(
        individual_signature
            .iter()
            .map(|binding| binding.individual_id),
    );
    let thing = class_id_by_display(&class_domain, THING_DISPLAY)?;
    let nothing = class_id_by_display(&class_domain, NOTHING_DISPLAY)?;
    let top_data_range = data_range_id_by_display(&data_range_domain, RDFS_LITERAL_DISPLAY)?;
    let scalar_object_role_count = object_roles.map_or_else(
        || scalar_object_role_count(&symbols.entity_domain),
        |roles| Ok(roles.object_role_domain.values.len()),
    )?;
    let (scalar_data_role_count, scalar_bottom_data_role_id) = data_roles.map_or_else(
        || scalar_data_role_summary(&symbols.entity_domain),
        |roles| {
            Ok((
                roles.data_property_domain.values.len(),
                roles.bottom_data_property_id,
            ))
        },
    )?;

    let mut raw_edges = Vec::<RawEdge>::new();
    let mut raw_disjoints = Vec::<RawDisjoint>::new();
    let mut raw_object_constraints = Vec::<RawObjectConstraint>::new();
    let mut raw_object_characteristics = Vec::<RawObjectCharacteristic>::new();
    let mut raw_data_domains = Vec::<RawDataDomain>::new();
    let mut raw_data_ranges = Vec::<RawDataRange>::new();
    let mut raw_datatype_definitions = Vec::<RawDatatypeDefinition>::new();
    let mut raw_keys = Vec::<RawKey>::new();
    let mut raw_data_functionalities = Vec::<RawDataFunctionality>::new();
    let mut raw_facts = Vec::<RawFact>::new();
    let mut raw_object_facts = Vec::<RawObjectFact>::new();
    let mut raw_negative_object_facts = Vec::<RawObjectFact>::new();
    let mut raw_data_facts = Vec::<RawDataFact>::new();
    let mut raw_negative_data_facts = Vec::<RawDataFact>::new();
    let mut raw_equalities = Vec::<RawEqualityFact>::new();
    let mut raw_inequalities = Vec::<RawInequalityFact>::new();
    let mut compiled_root_digests = Vec::<[u8; 32]>::new();
    let mut compiled_roots = 0_usize;
    let mut deferred_roots = 0_usize;
    for root in &symbols.roots {
        budget.claim_work(1)?;
        match root.handler {
            RootHandler::Declaration
            | RootHandler::OntologyAnnotation
            | RootHandler::AnnotationAssertion
            | RootHandler::SubAnnotationPropertyOf
            | RootHandler::AnnotationPropertyDomain
            | RootHandler::AnnotationPropertyRange => {}
            RootHandler::SubClassOf => {
                match named_subclass(
                    model,
                    symbols,
                    &class_domain,
                    &class_signature,
                    root.node,
                    scope_maps,
                    &mut budget,
                )? {
                    Some(edge) => {
                        retain_compiled_root(
                            &mut compiled_root_digests,
                            &mut compiled_roots,
                            edge.provenance,
                            &mut budget,
                        )?;
                        retain_edge(&mut raw_edges, edge, thing, nothing, &mut budget)?;
                    }
                    None => {
                        deferred_roots = deferred_roots.checked_add(1).ok_or_else(|| {
                            EncodedValidationError::resource(
                                "named-class deferred-root count overflowed",
                            )
                        })?;
                    }
                }
            }
            RootHandler::EquivalentClasses => {
                match named_equivalent_classes(
                    model,
                    symbols,
                    &class_domain,
                    &class_signature,
                    root.node,
                    scope_maps,
                    &mut budget,
                )? {
                    Some(edges) => {
                        let provenance =
                            edges.first().map(|edge| edge.provenance).ok_or_else(|| {
                                EncodedValidationError::invariant(
                                    "named equivalent-classes root emitted no edges",
                                )
                            })?;
                        retain_compiled_root(
                            &mut compiled_root_digests,
                            &mut compiled_roots,
                            provenance,
                            &mut budget,
                        )?;
                        for edge in edges {
                            retain_edge(&mut raw_edges, edge, thing, nothing, &mut budget)?;
                        }
                    }
                    None => {
                        deferred_roots = deferred_roots.checked_add(1).ok_or_else(|| {
                            EncodedValidationError::resource(
                                "named-class deferred-root count overflowed",
                            )
                        })?;
                    }
                }
            }
            RootHandler::DisjointClasses => {
                match named_disjoint_classes(
                    model,
                    symbols,
                    &class_domain,
                    &class_signature,
                    root.node,
                    thing,
                    nothing,
                    scope_maps,
                    &mut budget,
                )? {
                    Some(output) => {
                        retain_compiled_root(
                            &mut compiled_root_digests,
                            &mut compiled_roots,
                            output.provenance,
                            &mut budget,
                        )?;
                        for edge in output.edges {
                            retain_edge(&mut raw_edges, edge, thing, nothing, &mut budget)?;
                        }
                        if let Some(disjoint) = output.disjoint {
                            budget.claim_owned(size_of::<RawDisjoint>())?;
                            raw_disjoints.try_reserve(1).map_err(|_| {
                                EncodedValidationError::resource(
                                    "named disjoint-classes allocation failed",
                                )
                            })?;
                            raw_disjoints.push(disjoint);
                        }
                    }
                    None => {
                        deferred_roots = deferred_roots.checked_add(1).ok_or_else(|| {
                            EncodedValidationError::resource(
                                "named-class deferred-root count overflowed",
                            )
                        })?;
                    }
                }
            }
            RootHandler::ObjectPropertyDomain | RootHandler::ObjectPropertyRange => {
                let Some(object_roles) = object_roles else {
                    deferred_roots = deferred_roots.checked_add(1).ok_or_else(|| {
                        EncodedValidationError::resource(
                            "named-class deferred-root count overflowed",
                        )
                    })?;
                    continue;
                };
                match named_object_constraint(
                    model,
                    symbols,
                    object_roles,
                    &class_domain,
                    &class_signature,
                    root.handler,
                    root.node,
                    scope_maps,
                    &mut budget,
                )? {
                    Some(constraint) => {
                        retain_compiled_root(
                            &mut compiled_root_digests,
                            &mut compiled_roots,
                            constraint.provenance,
                            &mut budget,
                        )?;
                        budget.claim_owned(size_of::<RawObjectConstraint>())?;
                        raw_object_constraints.try_reserve(1).map_err(|_| {
                            EncodedValidationError::resource(
                                "named object-property constraint allocation failed",
                            )
                        })?;
                        raw_object_constraints.push(constraint);
                    }
                    None => {
                        deferred_roots = deferred_roots.checked_add(1).ok_or_else(|| {
                            EncodedValidationError::resource(
                                "named-class deferred-root count overflowed",
                            )
                        })?;
                    }
                }
            }
            RootHandler::FunctionalObjectProperty
            | RootHandler::InverseFunctionalObjectProperty
            | RootHandler::ReflexiveObjectProperty => {
                let Some(object_roles) = object_roles else {
                    deferred_roots = deferred_roots.checked_add(1).ok_or_else(|| {
                        EncodedValidationError::resource(
                            "named-class deferred-root count overflowed",
                        )
                    })?;
                    continue;
                };
                let characteristic = named_object_characteristic(
                    model,
                    symbols,
                    object_roles,
                    root.handler,
                    root.node,
                    scope_maps,
                    &mut budget,
                )?;
                retain_compiled_root(
                    &mut compiled_root_digests,
                    &mut compiled_roots,
                    characteristic.provenance,
                    &mut budget,
                )?;
                budget.claim_owned(size_of::<RawObjectCharacteristic>())?;
                raw_object_characteristics.try_reserve(1).map_err(|_| {
                    EncodedValidationError::resource(
                        "named object-property characteristic allocation failed",
                    )
                })?;
                raw_object_characteristics.push(characteristic);
            }
            RootHandler::DataPropertyDomain => {
                let Some(data_roles) = data_roles else {
                    deferred_roots = deferred_roots.checked_add(1).ok_or_else(|| {
                        EncodedValidationError::resource(
                            "named-class deferred-root count overflowed",
                        )
                    })?;
                    continue;
                };
                match named_data_domain(
                    model,
                    symbols,
                    data_roles,
                    &class_domain,
                    &class_signature,
                    root.node,
                    scope_maps,
                    &mut budget,
                )? {
                    Some(domain) => {
                        retain_compiled_root(
                            &mut compiled_root_digests,
                            &mut compiled_roots,
                            domain.provenance,
                            &mut budget,
                        )?;
                        budget.claim_owned(size_of::<RawDataDomain>())?;
                        raw_data_domains.try_reserve(1).map_err(|_| {
                            EncodedValidationError::resource(
                                "named data-property domain allocation failed",
                            )
                        })?;
                        raw_data_domains.push(domain);
                    }
                    None => {
                        deferred_roots = deferred_roots.checked_add(1).ok_or_else(|| {
                            EncodedValidationError::resource(
                                "named-class deferred-root count overflowed",
                            )
                        })?;
                    }
                }
            }
            RootHandler::DataPropertyRange => {
                let Some(data_roles) = data_roles else {
                    deferred_roots = deferred_roots.checked_add(1).ok_or_else(|| {
                        EncodedValidationError::resource(
                            "named-class deferred-root count overflowed",
                        )
                    })?;
                    continue;
                };
                match named_data_range(
                    model,
                    symbols,
                    data_roles,
                    &data_range_domain,
                    root.node,
                    scope_maps,
                    &mut budget,
                )? {
                    Some(range) => {
                        retain_compiled_root(
                            &mut compiled_root_digests,
                            &mut compiled_roots,
                            range.provenance,
                            &mut budget,
                        )?;
                        budget.claim_owned(size_of::<RawDataRange>())?;
                        raw_data_ranges.try_reserve(1).map_err(|_| {
                            EncodedValidationError::resource(
                                "named data-property range allocation failed",
                            )
                        })?;
                        raw_data_ranges.push(range);
                    }
                    None => {
                        deferred_roots = deferred_roots.checked_add(1).ok_or_else(|| {
                            EncodedValidationError::resource(
                                "named-class deferred-root count overflowed",
                            )
                        })?;
                    }
                }
            }
            RootHandler::DatatypeDefinition => {
                match named_datatype_definition(
                    model,
                    symbols,
                    &data_range_domain,
                    root.node,
                    scope_maps,
                    &mut budget,
                )? {
                    Some(definition) => {
                        retain_compiled_root(
                            &mut compiled_root_digests,
                            &mut compiled_roots,
                            definition.provenance,
                            &mut budget,
                        )?;
                        budget.claim_owned(size_of::<RawDatatypeDefinition>())?;
                        raw_datatype_definitions.try_reserve(1).map_err(|_| {
                            EncodedValidationError::resource(
                                "named datatype-definition allocation failed",
                            )
                        })?;
                        raw_datatype_definitions.push(definition);
                    }
                    None => {
                        deferred_roots = deferred_roots.checked_add(1).ok_or_else(|| {
                            EncodedValidationError::resource(
                                "named-class deferred-root count overflowed",
                            )
                        })?;
                    }
                }
            }
            RootHandler::HasKey => {
                match named_key(
                    model,
                    symbols,
                    object_roles,
                    data_roles,
                    &class_domain,
                    &class_signature,
                    root.node,
                    scope_maps,
                    &mut budget,
                )? {
                    Some(key) => {
                        retain_compiled_root(
                            &mut compiled_root_digests,
                            &mut compiled_roots,
                            key.provenance,
                            &mut budget,
                        )?;
                        budget.claim_owned(size_of::<RawKey>())?;
                        raw_keys.try_reserve(1).map_err(|_| {
                            EncodedValidationError::resource("named key allocation failed")
                        })?;
                        raw_keys.push(key);
                    }
                    None => {
                        deferred_roots = deferred_roots.checked_add(1).ok_or_else(|| {
                            EncodedValidationError::resource(
                                "named-class deferred-root count overflowed",
                            )
                        })?;
                    }
                }
            }
            RootHandler::FunctionalDataProperty => {
                let Some(data_roles) = data_roles else {
                    deferred_roots = deferred_roots.checked_add(1).ok_or_else(|| {
                        EncodedValidationError::resource(
                            "named-class deferred-root count overflowed",
                        )
                    })?;
                    continue;
                };
                let functionality = named_data_functionality(
                    model,
                    symbols,
                    data_roles,
                    root.node,
                    scope_maps,
                    &mut budget,
                )?;
                retain_compiled_root(
                    &mut compiled_root_digests,
                    &mut compiled_roots,
                    functionality.provenance,
                    &mut budget,
                )?;
                budget.claim_owned(size_of::<RawDataFunctionality>())?;
                raw_data_functionalities.try_reserve(1).map_err(|_| {
                    EncodedValidationError::resource(
                        "named functional data-property allocation failed",
                    )
                })?;
                raw_data_functionalities.push(functionality);
            }
            RootHandler::SameIndividual => {
                match named_same_individuals(
                    model,
                    symbols,
                    &individual_signature,
                    root.node,
                    scope_maps,
                    &mut budget,
                )? {
                    Some(equalities) => {
                        let provenance = equalities
                            .first()
                            .map(|equality| equality.provenance)
                            .ok_or_else(|| {
                                EncodedValidationError::invariant(
                                    "named same-individual root emitted no facts",
                                )
                            })?;
                        retain_compiled_root(
                            &mut compiled_root_digests,
                            &mut compiled_roots,
                            provenance,
                            &mut budget,
                        )?;
                        budget.claim_owned(
                            equalities
                                .len()
                                .checked_mul(size_of::<RawEqualityFact>())
                                .ok_or_else(|| {
                                    EncodedValidationError::resource(
                                        "named same-individual allocation overflowed",
                                    )
                                })?,
                        )?;
                        raw_equalities.try_reserve(equalities.len()).map_err(|_| {
                            EncodedValidationError::resource(
                                "named same-individual allocation failed",
                            )
                        })?;
                        raw_equalities.extend(equalities);
                    }
                    None => {
                        deferred_roots = deferred_roots.checked_add(1).ok_or_else(|| {
                            EncodedValidationError::resource(
                                "named-class deferred-root count overflowed",
                            )
                        })?;
                    }
                }
            }
            RootHandler::DifferentIndividuals => {
                match named_different_individuals(
                    model,
                    symbols,
                    &individual_signature,
                    root.node,
                    scope_maps,
                    &mut budget,
                )? {
                    Some(inequalities) => {
                        let provenance = inequalities
                            .first()
                            .map(|inequality| inequality.provenance)
                            .ok_or_else(|| {
                                EncodedValidationError::invariant(
                                    "named different-individuals root emitted no facts",
                                )
                            })?;
                        retain_compiled_root(
                            &mut compiled_root_digests,
                            &mut compiled_roots,
                            provenance,
                            &mut budget,
                        )?;
                        budget.claim_owned(
                            inequalities
                                .len()
                                .checked_mul(size_of::<RawInequalityFact>())
                                .ok_or_else(|| {
                                    EncodedValidationError::resource(
                                        "named different-individuals allocation overflowed",
                                    )
                                })?,
                        )?;
                        raw_inequalities
                            .try_reserve(inequalities.len())
                            .map_err(|_| {
                                EncodedValidationError::resource(
                                    "named different-individuals allocation failed",
                                )
                            })?;
                        raw_inequalities.extend(inequalities);
                    }
                    None => {
                        deferred_roots = deferred_roots.checked_add(1).ok_or_else(|| {
                            EncodedValidationError::resource(
                                "named-class deferred-root count overflowed",
                            )
                        })?;
                    }
                }
            }
            RootHandler::ClassAssertion => {
                match named_class_assertion(
                    model,
                    symbols,
                    &class_domain,
                    &class_signature,
                    &individual_domain,
                    &individual_signature,
                    root.node,
                    scope_maps,
                    &mut budget,
                )? {
                    Some(fact) => {
                        retain_compiled_root(
                            &mut compiled_root_digests,
                            &mut compiled_roots,
                            fact.provenance,
                            &mut budget,
                        )?;
                        budget.claim_owned(size_of::<RawFact>())?;
                        raw_facts.try_reserve(1).map_err(|_| {
                            EncodedValidationError::resource(
                                "named class-assertion allocation failed",
                            )
                        })?;
                        raw_facts.push(fact);
                    }
                    None => {
                        deferred_roots = deferred_roots.checked_add(1).ok_or_else(|| {
                            EncodedValidationError::resource(
                                "named-class deferred-root count overflowed",
                            )
                        })?;
                    }
                }
            }
            RootHandler::ObjectPropertyAssertion => {
                let Some(object_roles) = object_roles else {
                    deferred_roots = deferred_roots.checked_add(1).ok_or_else(|| {
                        EncodedValidationError::resource(
                            "named-class deferred-root count overflowed",
                        )
                    })?;
                    continue;
                };
                match named_object_assertion(
                    model,
                    symbols,
                    object_roles,
                    &individual_domain,
                    &individual_signature,
                    root.node,
                    OBJECT_PROPERTY_ASSERTION_TAG,
                    scope_maps,
                    &mut budget,
                )? {
                    Some(fact) => {
                        retain_compiled_root(
                            &mut compiled_root_digests,
                            &mut compiled_roots,
                            fact.provenance,
                            &mut budget,
                        )?;
                        budget.claim_owned(size_of::<RawObjectFact>())?;
                        raw_object_facts.try_reserve(1).map_err(|_| {
                            EncodedValidationError::resource(
                                "named object-property assertion allocation failed",
                            )
                        })?;
                        raw_object_facts.push(fact);
                    }
                    None => {
                        deferred_roots = deferred_roots.checked_add(1).ok_or_else(|| {
                            EncodedValidationError::resource(
                                "named-class deferred-root count overflowed",
                            )
                        })?;
                    }
                }
            }
            RootHandler::NegativeObjectPropertyAssertion => {
                let Some(object_roles) = object_roles else {
                    deferred_roots = deferred_roots.checked_add(1).ok_or_else(|| {
                        EncodedValidationError::resource(
                            "named-class deferred-root count overflowed",
                        )
                    })?;
                    continue;
                };
                match named_object_assertion(
                    model,
                    symbols,
                    object_roles,
                    &individual_domain,
                    &individual_signature,
                    root.node,
                    NEGATIVE_OBJECT_PROPERTY_ASSERTION_TAG,
                    scope_maps,
                    &mut budget,
                )? {
                    Some(fact) => {
                        retain_compiled_root(
                            &mut compiled_root_digests,
                            &mut compiled_roots,
                            fact.provenance,
                            &mut budget,
                        )?;
                        budget.claim_owned(size_of::<RawObjectFact>())?;
                        raw_negative_object_facts.try_reserve(1).map_err(|_| {
                            EncodedValidationError::resource(
                                "named negative object-property assertion allocation failed",
                            )
                        })?;
                        raw_negative_object_facts.push(fact);
                    }
                    None => {
                        deferred_roots = deferred_roots.checked_add(1).ok_or_else(|| {
                            EncodedValidationError::resource(
                                "named-class deferred-root count overflowed",
                            )
                        })?;
                    }
                }
            }
            RootHandler::DataPropertyAssertion => {
                let Some(data_roles) = data_roles else {
                    deferred_roots = deferred_roots.checked_add(1).ok_or_else(|| {
                        EncodedValidationError::resource(
                            "named-class deferred-root count overflowed",
                        )
                    })?;
                    continue;
                };
                match named_data_assertion(
                    model,
                    symbols,
                    data_roles,
                    &individual_domain,
                    &individual_signature,
                    &source_literal_domain,
                    &source_data_identity_ids,
                    root.node,
                    DATA_PROPERTY_ASSERTION_TAG,
                    scope_maps,
                    &mut budget,
                )? {
                    Some(fact) => {
                        retain_compiled_root(
                            &mut compiled_root_digests,
                            &mut compiled_roots,
                            fact.provenance,
                            &mut budget,
                        )?;
                        budget.claim_owned(size_of::<RawDataFact>())?;
                        raw_data_facts.try_reserve(1).map_err(|_| {
                            EncodedValidationError::resource(
                                "named data-property assertion allocation failed",
                            )
                        })?;
                        raw_data_facts.push(fact);
                    }
                    None => {
                        deferred_roots = deferred_roots.checked_add(1).ok_or_else(|| {
                            EncodedValidationError::resource(
                                "named-class deferred-root count overflowed",
                            )
                        })?;
                    }
                }
            }
            RootHandler::NegativeDataPropertyAssertion => {
                let Some(data_roles) = data_roles else {
                    deferred_roots = deferred_roots.checked_add(1).ok_or_else(|| {
                        EncodedValidationError::resource(
                            "named-class deferred-root count overflowed",
                        )
                    })?;
                    continue;
                };
                match named_data_assertion(
                    model,
                    symbols,
                    data_roles,
                    &individual_domain,
                    &individual_signature,
                    &source_literal_domain,
                    &source_data_identity_ids,
                    root.node,
                    NEGATIVE_DATA_PROPERTY_ASSERTION_TAG,
                    scope_maps,
                    &mut budget,
                )? {
                    Some(fact) => {
                        retain_compiled_root(
                            &mut compiled_root_digests,
                            &mut compiled_roots,
                            fact.provenance,
                            &mut budget,
                        )?;
                        budget.claim_owned(size_of::<RawDataFact>())?;
                        raw_negative_data_facts.try_reserve(1).map_err(|_| {
                            EncodedValidationError::resource(
                                "named negative data-property assertion allocation failed",
                            )
                        })?;
                        raw_negative_data_facts.push(fact);
                    }
                    None => {
                        deferred_roots = deferred_roots.checked_add(1).ok_or_else(|| {
                            EncodedValidationError::resource(
                                "named-class deferred-root count overflowed",
                            )
                        })?;
                    }
                }
            }
            _ => {
                deferred_roots = deferred_roots.checked_add(1).ok_or_else(|| {
                    EncodedValidationError::resource("named-class deferred-root count overflowed")
                })?;
            }
        }
        PhaseBudget::count(
            compiled_roots,
            limits.max_compiled_roots,
            "compiled root count",
        )?;
    }
    budget.claim_work(sort_work(compiled_root_digests.len()))?;
    compiled_root_digests.sort_unstable();
    compiled_root_digests.dedup();
    if compiled_root_digests.len() != compiled_roots {
        return Err(EncodedValidationError::invariant(
            "named-class source roots have duplicate semantic identities",
        ));
    }

    let edges = normalize_edges(raw_edges, &mut budget)?;
    let disjoints = normalize_disjoints(raw_disjoints, &mut budget)?;
    let object_constraints = normalize_object_constraints(raw_object_constraints, &mut budget)?;
    let object_characteristics =
        normalize_object_characteristics(raw_object_characteristics, &mut budget)?;
    let data_domains = normalize_data_domains(raw_data_domains, &mut budget)?;
    let data_ranges = normalize_data_ranges(raw_data_ranges, &mut budget)?;
    let datatype_definitions =
        normalize_datatype_definitions(raw_datatype_definitions, &mut budget)?;
    let keys = normalize_keys(raw_keys, &mut budget)?;
    let data_functionalities =
        normalize_data_functionalities(raw_data_functionalities, &mut budget)?;
    let facts = normalize_facts(raw_facts, &mut budget)?;
    let object_facts = normalize_object_facts(raw_object_facts, &mut budget)?;
    let negative_object_facts = normalize_object_facts(raw_negative_object_facts, &mut budget)?;
    let data_facts = normalize_data_facts(raw_data_facts, &mut budget)?;
    let negative_data_facts = normalize_data_facts(raw_negative_data_facts, &mut budget)?;
    let equalities = normalize_equalities(raw_equalities, &mut budget)?;
    let inequalities = normalize_inequalities(raw_inequalities, &mut budget)?;
    let (provenance, provenance_keys) = freeze_provenance(
        &edges,
        &disjoints,
        &object_constraints,
        &object_characteristics,
        &data_domains,
        &data_ranges,
        &datatype_definitions,
        &keys,
        &data_functionalities,
        &facts,
        &object_facts,
        &negative_object_facts,
        &data_facts,
        &negative_data_facts,
        &equalities,
        &inequalities,
        &mut budget,
    )?;
    let (
        predicates,
        predicate_by_class,
        predicate_by_negative_class,
        predicate_by_object_role,
        predicate_by_negative_object_role,
        predicate_by_data_role,
        predicate_by_negative_data_role,
        predicate_by_data_range,
        predicate_by_negative_data_range,
        guard_predicates,
        named_predicate,
        equality_predicate,
        data_equality_predicate,
        inequality_predicate,
        data_inequality_predicate,
        ordering_predicate,
    ) = freeze_predicates(
        &nominal_bindings,
        &edges,
        &disjoints,
        &object_constraints,
        &object_characteristics,
        &data_domains,
        &data_ranges,
        &datatype_definitions,
        &keys,
        &data_functionalities,
        &facts,
        &object_facts,
        &negative_object_facts,
        &data_facts,
        &negative_data_facts,
        &equalities,
        &inequalities,
        thing,
        nothing,
        top_data_range,
        !individual_domain.values.is_empty(),
        !named_individuals.is_empty(),
        &mut budget,
    )?;
    let scalar_predicate_ids = scalar_predicate_ids(
        &predicates,
        scalar_object_role_count,
        scalar_data_role_count,
        scalar_bottom_data_role_id,
        &mut budget,
    )?;
    let clauses = freeze_clauses(
        &nominal_bindings,
        &edges,
        &disjoints,
        &object_constraints,
        &object_characteristics,
        &data_domains,
        &data_ranges,
        &datatype_definitions,
        &keys,
        &data_functionalities,
        &facts,
        thing,
        nothing,
        top_data_range,
        &predicate_by_class,
        &predicate_by_negative_class,
        &predicate_by_object_role,
        &predicate_by_data_role,
        &predicate_by_data_range,
        &predicate_by_negative_data_range,
        equality_predicate,
        inequality_predicate,
        data_equality_predicate,
        data_inequality_predicate,
        ordering_predicate,
        named_predicate,
        &guard_predicates,
        &scalar_predicate_ids,
        &provenance_keys,
        &mut budget,
    )?;
    let positive_facts = freeze_positive_facts(
        &facts,
        &object_facts,
        &data_facts,
        &equalities,
        &inequalities,
        &individual_domain,
        thing,
        &predicate_by_class,
        &predicate_by_object_role,
        &predicate_by_data_role,
        &source_literal_domain,
        &data_value_domain,
        &source_data_identity_ids,
        &named_individuals,
        named_predicate,
        equality_predicate,
        nominal_usage(
            &nominal_bindings,
            &edges,
            &disjoints,
            &object_constraints,
            &data_domains,
            &keys,
            &facts,
        ),
        object_characteristics
            .iter()
            .any(|value| value.kind != ObjectCharacteristicKind::Reflexive),
        !keys.is_empty(),
        inequality_predicate,
        &provenance_keys,
        &scalar_predicate_ids,
        &mut budget,
    )?;
    let negative_facts = freeze_negative_facts(
        &facts,
        &negative_object_facts,
        &negative_data_facts,
        &individual_domain,
        &predicate_by_negative_class,
        &predicate_by_negative_object_role,
        &predicate_by_negative_data_role,
        &source_literal_domain,
        &data_value_domain,
        &source_data_identity_ids,
        &provenance_keys,
        &scalar_predicate_ids,
        positive_facts.len(),
        &mut budget,
    )?;
    Ok(NamedClassPhase {
        class_domain,
        class_signature,
        data_range_domain,
        individual_domain,
        source_literal_domain,
        data_value_domain,
        individual_signature,
        named_individuals,
        predicates,
        clauses,
        positive_facts,
        negative_facts,
        provenance,
        compiled_roots,
        deferred_roots,
        work: budget.work,
        owned_bytes: budget.owned_bytes,
        compiled_root_digests,
        nominal_bindings,
        normalized_edges: edges,
        normalized_disjoints: disjoints,
        normalized_object_constraints: object_constraints,
        normalized_object_characteristics: object_characteristics,
        normalized_data_domains: data_domains,
        normalized_data_ranges: data_ranges,
        normalized_datatype_definitions: datatype_definitions,
        normalized_keys: keys,
        normalized_data_functionalities: data_functionalities,
        normalized_facts: facts,
        normalized_object_facts: object_facts,
        normalized_negative_object_facts: negative_object_facts,
        normalized_data_facts: data_facts,
        normalized_negative_data_facts: negative_data_facts,
        normalized_equalities: equalities,
        normalized_inequalities: inequalities,
        source_data_identity_ids,
        manifest_limit: limits.max_manifest_bytes,
    })
}

fn declared_class_ids(symbols: &SymbolPhase, budget: &mut PhaseBudget) -> EncodedResult<Vec<u32>> {
    let mut identifiers = Vec::new();
    for entity in &symbols.declared_entities {
        budget.claim_work(1)?;
        if entity.kind != "class" {
            continue;
        }
        budget.claim_owned(size_of::<u32>())?;
        identifiers.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("declared-class signature allocation failed")
        })?;
        identifiers.push(entity.entity_id);
    }
    budget.claim_work(sort_work(identifiers.len()))?;
    identifiers.sort_unstable();
    identifiers.dedup();
    Ok(identifiers)
}

fn class_signature<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    declared_class_ids: &[u32],
    has_object_roles: bool,
    has_data_roles: bool,
    scope_maps: &[AnonymousScopeMap],
    budget: &mut PhaseBudget,
) -> EncodedResult<(DecodedSymbolDomain, Vec<ClassSignatureBinding>)> {
    let mut pending = Vec::<PendingClassSymbol>::new();
    for entity in &symbols.entity_domain.values {
        budget.claim_work(1)?;
        if !entity.display.starts_with("class:") {
            continue;
        }
        let following = pending.len().checked_add(1).ok_or_else(|| {
            EncodedValidationError::resource("named-class symbol count overflowed")
        })?;
        PhaseBudget::count(following, budget.limits.max_class_symbols, "symbol count")?;
        budget.claim_owned(size_of::<PendingClassSymbol>())?;
        budget.claim_owned(size_of::<DecodedSymbolValue>())?;
        budget.claim_owned(entity.key.len())?;
        budget.claim_owned(entity.display.len())?;
        pending.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("named-class symbol allocation failed")
        })?;
        pending.push(PendingClassSymbol {
            value: DecodedSymbolValue {
                identifier: 0,
                key: entity.key.clone(),
                display: entity.display.clone(),
                generated: entity.generated,
                query_local: entity.query_local,
            },
            entity: Some((
                entity.identifier,
                declared_class_ids.binary_search(&entity.identifier).is_ok(),
            )),
        });
    }

    let mut selected_expressions = Vec::<NodeId>::new();
    'root_selection: for root in &symbols.roots {
        budget.claim_work(1)?;
        let root_node = model.node(root.node)?;
        match root.handler {
            RootHandler::ClassAssertion => {
                let expression = node_field(
                    model,
                    root_node,
                    0,
                    "class-assertion class-expression operand",
                )?;
                if let Some(selection) = atomic_class_selection(model, symbols, expression, budget)?
                {
                    push_atomic_class_selection(&mut selected_expressions, selection, budget)?;
                }
            }
            RootHandler::SubClassOf => {
                let sub_class = node_field(model, root_node, 0, "subclass antecedent")?;
                let super_class = node_field(model, root_node, 1, "subclass consequent")?;
                let Some(sub_selection) =
                    atomic_class_selection(model, symbols, sub_class, budget)?
                else {
                    continue;
                };
                let Some(super_selection) =
                    atomic_class_selection(model, symbols, super_class, budget)?
                else {
                    continue;
                };
                if atomic_class_selection_is_trivial(
                    model,
                    symbols,
                    sub_selection,
                    super_selection,
                    scope_maps,
                    budget,
                )? {
                    continue;
                }
                push_atomic_class_selection(&mut selected_expressions, sub_selection, budget)?;
                push_atomic_class_selection(&mut selected_expressions, super_selection, budget)?;
            }
            RootHandler::EquivalentClasses => {
                let expressions_component = required_component(
                    model.field(root_node.fields().start)?,
                    "equivalent-classes expressions",
                )?;
                let ComponentValue::Collection(expressions) =
                    model.resolve(expressions_component)?
                else {
                    return Err(EncodedValidationError::invariant(
                        "equivalent-classes expressions did not resolve to a collection",
                    ));
                };
                for item_index in expressions.items() {
                    budget.claim_work(1)?;
                    let item =
                        required_component(model.item(item_index)?, "equivalent-classes member")?;
                    let ComponentValue::Node(identifier) = model.resolve(item)? else {
                        return Err(EncodedValidationError::invariant(
                            "equivalent-classes member did not resolve to a node",
                        ));
                    };
                    if atomic_class_selection(model, symbols, identifier, budget)?.is_none() {
                        continue 'root_selection;
                    }
                }
                for item_index in expressions.items() {
                    budget.claim_work(1)?;
                    let item =
                        required_component(model.item(item_index)?, "equivalent-classes member")?;
                    let ComponentValue::Node(identifier) = model.resolve(item)? else {
                        return Err(EncodedValidationError::invariant(
                            "equivalent-classes member did not resolve to a node",
                        ));
                    };
                    if let Some(selection) =
                        atomic_class_selection(model, symbols, identifier, budget)?
                    {
                        push_atomic_class_selection(&mut selected_expressions, selection, budget)?;
                    }
                }
            }
            RootHandler::DisjointClasses => {
                let expressions_component = required_component(
                    model.field(root_node.fields().start)?,
                    "disjoint-classes expressions",
                )?;
                let ComponentValue::Collection(expressions) =
                    model.resolve(expressions_component)?
                else {
                    return Err(EncodedValidationError::invariant(
                        "disjoint-classes expressions did not resolve to a collection",
                    ));
                };
                let mut live_count = 0_usize;
                for item_index in expressions.items() {
                    budget.claim_work(1)?;
                    let item =
                        required_component(model.item(item_index)?, "disjoint-classes member")?;
                    let ComponentValue::Node(identifier) = model.resolve(item)? else {
                        return Err(EncodedValidationError::invariant(
                            "disjoint-classes member did not resolve to a node",
                        ));
                    };
                    let Some(selection) =
                        atomic_class_selection(model, symbols, identifier, budget)?
                    else {
                        continue 'root_selection;
                    };
                    if matches!(selection.source, AtomicClassSource::Entity(entity_id)
                        if !selection.negative
                            && class_entity_display(symbols, entity_id)? == NOTHING_DISPLAY)
                    {
                        continue;
                    }
                    live_count = live_count.checked_add(1).ok_or_else(|| {
                        EncodedValidationError::resource(
                            "disjoint-class live-member count overflowed",
                        )
                    })?;
                }
                if live_count < 2 {
                    continue;
                }
                for item_index in expressions.items() {
                    budget.claim_work(1)?;
                    let item =
                        required_component(model.item(item_index)?, "disjoint-classes member")?;
                    let ComponentValue::Node(identifier) = model.resolve(item)? else {
                        return Err(EncodedValidationError::invariant(
                            "disjoint-classes member did not resolve to a node",
                        ));
                    };
                    if let Some(selection) =
                        atomic_class_selection(model, symbols, identifier, budget)?
                    {
                        push_atomic_class_selection(&mut selected_expressions, selection, budget)?;
                    }
                }
            }
            RootHandler::ObjectPropertyDomain | RootHandler::ObjectPropertyRange
                if has_object_roles =>
            {
                let expression = node_field(
                    model,
                    root_node,
                    1,
                    "object-property constraint class expression",
                )?;
                if let Some(selection) = atomic_class_selection(model, symbols, expression, budget)?
                {
                    push_atomic_class_selection(&mut selected_expressions, selection, budget)?;
                }
            }
            RootHandler::DataPropertyDomain if has_data_roles => {
                let expression =
                    node_field(model, root_node, 1, "data-property domain class expression")?;
                if let Some(selection) = atomic_class_selection(model, symbols, expression, budget)?
                {
                    push_atomic_class_selection(&mut selected_expressions, selection, budget)?;
                }
            }
            RootHandler::HasKey => {
                let object_component = required_component(
                    model.field(root_node.fields().start + 1)?,
                    "has-key object properties",
                )?;
                let ComponentValue::Collection(object_properties) =
                    model.resolve(object_component)?
                else {
                    return Err(EncodedValidationError::invariant(
                        "has-key object properties did not resolve to a collection",
                    ));
                };
                let data_component = required_component(
                    model.field(root_node.fields().start + 2)?,
                    "has-key data properties",
                )?;
                let ComponentValue::Collection(data_properties) = model.resolve(data_component)?
                else {
                    return Err(EncodedValidationError::invariant(
                        "has-key data properties did not resolve to a collection",
                    ));
                };
                if (!object_properties.is_empty() && !has_object_roles)
                    || (!data_properties.is_empty() && !has_data_roles)
                {
                    continue;
                }
                let expression = node_field(model, root_node, 0, "has-key class expression")?;
                if let Some(selection) = atomic_class_selection(model, symbols, expression, budget)?
                {
                    push_atomic_class_selection(&mut selected_expressions, selection, budget)?;
                }
            }
            _ => {}
        }
    }
    budget.claim_work(sort_work(selected_expressions.len()))?;
    selected_expressions.sort_unstable();
    selected_expressions.dedup();
    for identifier in selected_expressions {
        let following = pending.len().checked_add(1).ok_or_else(|| {
            EncodedValidationError::resource("class-expression symbol count overflowed")
        })?;
        PhaseBudget::count(
            following,
            budget.limits.max_class_symbols,
            "class-expression",
        )?;
        let key = canonical::canonical_node_key(model, identifier, scope_maps, budget)?;
        budget.claim_work(key.len())?;
        let digest = crate::model::hex(&Sha256::digest(&key));
        let prefix = class_expression_prefix(model.node(identifier)?.tag())?;
        let display_len = prefix.len().checked_add(digest.len()).ok_or_else(|| {
            EncodedValidationError::resource("class-expression display length overflowed")
        })?;
        budget.claim_owned(display_len)?;
        let mut display = String::new();
        display.try_reserve_exact(display_len).map_err(|_| {
            EncodedValidationError::resource("class-expression display allocation failed")
        })?;
        display.push_str(prefix);
        display.push_str(&digest);
        budget.claim_owned(size_of::<PendingClassSymbol>())?;
        budget.claim_owned(size_of::<DecodedSymbolValue>())?;
        pending.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("class-expression symbol allocation failed")
        })?;
        pending.push(PendingClassSymbol {
            value: DecodedSymbolValue {
                identifier: 0,
                key,
                display,
                generated: false,
                query_local: false,
            },
            entity: None,
        });
    }

    budget.claim_work(sort_work(pending.len()))?;
    pending.sort_by(|left, right| left.value.key.cmp(&right.value.key));
    let mut values = Vec::<DecodedSymbolValue>::new();
    let mut bindings = Vec::<ClassSignatureBinding>::new();
    values.try_reserve_exact(pending.len()).map_err(|_| {
        EncodedValidationError::resource("class-expression symbol result allocation failed")
    })?;
    bindings
        .try_reserve_exact(pending.len())
        .map_err(|_| EncodedValidationError::resource("class signature allocation failed"))?;
    for mut candidate in pending {
        if let Some(previous) = values.last() {
            if previous.key == candidate.value.key {
                if previous.display != candidate.value.display
                    || previous.generated != candidate.value.generated
                    || previous.query_local != candidate.value.query_local
                    || candidate.entity.is_some()
                {
                    return Err(EncodedValidationError::invariant(
                        "class-expression symbol key has conflicting metadata",
                    ));
                }
                continue;
            }
        }
        let class_expression_id = u32::try_from(values.len()).map_err(|_| {
            EncodedValidationError::resource("class-expression symbol ID exceeds u32")
        })?;
        candidate.value.identifier = class_expression_id;
        if let Some((entity_id, declared)) = candidate.entity {
            budget.claim_owned(size_of::<ClassSignatureBinding>())?;
            bindings.push(ClassSignatureBinding {
                class_expression_id,
                entity_id,
                declared,
            });
        }
        values.push(candidate.value);
    }
    Ok((
        DecodedSymbolDomain {
            kind: SymbolKind::ClassExpression,
            values,
        },
        bindings,
    ))
}

fn class_expression_prefix(tag: u16) -> EncodedResult<&'static str> {
    match tag {
        OBJECT_ONE_OF_TAG => Ok("ObjectOneOf:"),
        OBJECT_COMPLEMENT_OF_TAG => Ok("ObjectComplementOf:"),
        _ => Err(EncodedValidationError::invariant(
            "selected class expression has an unsupported constructor",
        )),
    }
}

fn push_class_expression_selection(
    expressions: &mut Vec<NodeId>,
    identifier: NodeId,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    budget.claim_owned(size_of::<NodeId>())?;
    expressions.try_reserve(1).map_err(|_| {
        EncodedValidationError::resource("class-expression selection allocation failed")
    })?;
    expressions.push(identifier);
    Ok(())
}

fn is_named_nominal<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    identifier: NodeId,
    budget: &mut PhaseBudget,
) -> EncodedResult<bool> {
    let node = model.node(identifier)?;
    if node.tag() != OBJECT_ONE_OF_TAG {
        return Ok(false);
    }
    if node.field_count() != 1 {
        return Err(EncodedValidationError::invariant(
            "object nominal no longer has schema-1 shape",
        ));
    }
    let component = required_component(
        model.field(node.fields().start)?,
        "object nominal individuals",
    )?;
    let ComponentValue::Collection(individuals) = model.resolve(component)? else {
        return Err(EncodedValidationError::invariant(
            "object nominal individuals did not resolve to a collection",
        ));
    };
    for item_index in individuals.items() {
        budget.claim_work(1)?;
        let item = required_component(model.item(item_index)?, "object nominal individual")?;
        let ComponentValue::Node(individual) = model.resolve(item)? else {
            return Err(EncodedValidationError::invariant(
                "object nominal member did not resolve to an individual node",
            ));
        };
        if model.node(individual)?.tag() != ENTITY_TAG {
            return Ok(false);
        }
        let entity_id = symbols.entity_symbol_for_node(individual).ok_or_else(|| {
            EncodedValidationError::invariant(
                "object nominal member is absent from the reachable entity mapping",
            )
        })?;
        let entity = symbols
            .entity_domain
            .values
            .get(usize::try_from(entity_id).unwrap_or(usize::MAX))
            .ok_or_else(|| {
                EncodedValidationError::invariant("object nominal entity ID is dangling")
            })?;
        if !entity.display.starts_with(NAMED_INDIVIDUAL_PREFIX) {
            return Ok(false);
        }
    }
    Ok(true)
}

fn atomic_named_nominal<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    identifier: NodeId,
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<(NodeId, bool)>> {
    if is_named_nominal(model, symbols, identifier, budget)? {
        return Ok(Some((identifier, false)));
    }
    let node = model.node(identifier)?;
    if node.tag() != OBJECT_COMPLEMENT_OF_TAG {
        return Ok(None);
    }
    if node.field_count() != 1 {
        return Err(EncodedValidationError::invariant(
            "class complement no longer has schema-1 shape",
        ));
    }
    let operand = node_field(model, node, 0, "nominal-complement operand")?;
    Ok(is_named_nominal(model, symbols, operand, budget)?.then_some((operand, true)))
}

fn atomic_class_selection<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    identifier: NodeId,
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<AtomicClassSelection>> {
    if let Some((entity_id, negative)) = atomic_class_entity(model, symbols, identifier)? {
        return Ok(Some(AtomicClassSelection {
            source: AtomicClassSource::Entity(entity_id),
            expression: identifier,
            negative,
        }));
    }
    Ok(
        atomic_named_nominal(model, symbols, identifier, budget)?.map(|(base, negative)| {
            AtomicClassSelection {
                source: AtomicClassSource::Nominal(base),
                expression: identifier,
                negative,
            }
        }),
    )
}

fn push_atomic_class_selection(
    expressions: &mut Vec<NodeId>,
    selection: AtomicClassSelection,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    if let AtomicClassSource::Nominal(base) = selection.source {
        push_class_expression_selection(expressions, base, budget)?;
    }
    if selection.negative {
        push_class_expression_selection(expressions, selection.expression, budget)?;
    }
    Ok(())
}

fn atomic_class_selection_is_trivial<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    sub: AtomicClassSelection,
    super_class: AtomicClassSelection,
    scope_maps: &[AnonymousScopeMap],
    budget: &mut PhaseBudget,
) -> EncodedResult<bool> {
    let same_base = match (sub.source, super_class.source) {
        (AtomicClassSource::Entity(left), AtomicClassSource::Entity(right)) => left == right,
        (AtomicClassSource::Nominal(left), AtomicClassSource::Nominal(right)) => {
            if left == right {
                true
            } else {
                canonical::canonical_node_key(model, left, scope_maps, budget)?
                    == canonical::canonical_node_key(model, right, scope_maps, budget)?
            }
        }
        _ => false,
    };
    if sub.negative == super_class.negative && same_base {
        return Ok(true);
    }
    let sub_is_bottom = match sub.source {
        AtomicClassSource::Entity(entity_id) if !sub.negative => {
            class_entity_display(symbols, entity_id)? == NOTHING_DISPLAY
        }
        _ => false,
    };
    let super_is_top = match super_class.source {
        AtomicClassSource::Entity(entity_id) if !super_class.negative => {
            class_entity_display(symbols, entity_id)? == THING_DISPLAY
        }
        _ => false,
    };
    Ok(sub_is_bottom || super_is_top)
}

#[allow(clippy::too_many_arguments)]
fn nominal_bindings<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    class_domain: &DecodedSymbolDomain,
    individual_signature: &[IndividualSignatureBinding],
    scope_maps: &[AnonymousScopeMap],
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<NominalBinding>> {
    let mut bindings = Vec::new();
    for index in 0..model.summary().node_count {
        budget.claim_work(1)?;
        let node = model.node_at(index)?.ok_or_else(|| {
            EncodedValidationError::invariant("object nominal node disappeared during traversal")
        })?;
        if node.tag() != OBJECT_ONE_OF_TAG {
            continue;
        }
        let key = canonical::canonical_node_key(model, node.id(), scope_maps, budget)?;
        budget.claim_work(binary_search_work(class_domain.values.len()))?;
        let Ok(class_index) = class_domain
            .values
            .binary_search_by(|candidate| candidate.key.cmp(&key))
        else {
            continue;
        };
        if !is_named_nominal(model, symbols, node.id(), budget)? {
            return Err(EncodedValidationError::invariant(
                "selected object nominal contains a non-named individual",
            ));
        }
        let component = required_component(
            model.field(node.fields().start)?,
            "selected object nominal individuals",
        )?;
        let ComponentValue::Collection(individuals) = model.resolve(component)? else {
            return Err(EncodedValidationError::invariant(
                "selected object nominal individuals changed shape",
            ));
        };
        let mut individual_ids = Vec::new();
        budget.claim_owned(individuals.len().checked_mul(size_of::<u32>()).ok_or_else(
            || EncodedValidationError::resource("object nominal individual IDs overflowed"),
        )?)?;
        individual_ids
            .try_reserve_exact(individuals.len())
            .map_err(|_| {
                EncodedValidationError::resource("object nominal individual ID allocation failed")
            })?;
        for item_index in individuals.items() {
            budget.claim_work(1)?;
            let item =
                required_component(model.item(item_index)?, "selected object nominal member")?;
            let ComponentValue::Node(individual) = model.resolve(item)? else {
                return Err(EncodedValidationError::invariant(
                    "selected object nominal member changed shape",
                ));
            };
            individual_ids.push(
                named_individual_id(model, symbols, individual_signature, individual)?.ok_or_else(
                    || {
                        EncodedValidationError::invariant(
                            "selected object nominal member is not a named individual",
                        )
                    },
                )?,
            );
        }
        if !individual_ids.windows(2).all(|pair| pair[0] < pair[1]) {
            return Err(EncodedValidationError::invariant(
                "object nominal individual IDs are not canonical",
            ));
        }
        budget.claim_owned(size_of::<NominalBinding>())?;
        bindings.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("object nominal binding allocation failed")
        })?;
        bindings.push(NominalBinding {
            class_id: u32::try_from(class_index).map_err(|_| {
                EncodedValidationError::resource("object nominal class ID exceeds u32")
            })?,
            individual_ids,
        });
    }
    budget.claim_work(sort_work(bindings.len()))?;
    bindings.sort();
    if bindings.windows(2).any(|pair| pair[0] == pair[1]) {
        bindings.dedup();
    }
    if bindings
        .windows(2)
        .any(|pair| pair[0].class_id == pair[1].class_id)
    {
        return Err(EncodedValidationError::invariant(
            "object nominal class ID has conflicting individual members",
        ));
    }
    Ok(bindings)
}

fn atomic_class_entity<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    identifier: NodeId,
) -> EncodedResult<Option<(u32, bool)>> {
    if model.node(identifier)?.tag() == ENTITY_TAG {
        let entity_id = symbols.entity_symbol_for_node(identifier).ok_or_else(|| {
            EncodedValidationError::invariant(
                "atomic class is absent from the reachable entity mapping",
            )
        })?;
        let entity = symbols
            .entity_domain
            .values
            .get(usize::try_from(entity_id).unwrap_or(usize::MAX))
            .ok_or_else(|| {
                EncodedValidationError::invariant("atomic class entity ID is dangling")
            })?;
        return Ok(entity
            .display
            .starts_with("class:")
            .then_some((entity_id, false)));
    }
    let Some(entity_id) = atomic_complement_operand(model, symbols, identifier)? else {
        return Ok(None);
    };
    match class_entity_display(symbols, entity_id)? {
        THING_DISPLAY => Ok(Some((
            class_id_by_display(&symbols.entity_domain, NOTHING_DISPLAY)?,
            false,
        ))),
        NOTHING_DISPLAY => Ok(Some((
            class_id_by_display(&symbols.entity_domain, THING_DISPLAY)?,
            false,
        ))),
        _ => Ok(Some((entity_id, true))),
    }
}

fn class_entity_display(symbols: &SymbolPhase, entity_id: u32) -> EncodedResult<&str> {
    symbols
        .entity_domain
        .values
        .get(usize::try_from(entity_id).unwrap_or(usize::MAX))
        .map(|entity| entity.display.as_str())
        .ok_or_else(|| EncodedValidationError::invariant("atomic class entity ID is dangling"))
}

fn atomic_complement_operand<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    identifier: NodeId,
) -> EncodedResult<Option<u32>> {
    let node = model.node(identifier)?;
    if node.tag() != OBJECT_COMPLEMENT_OF_TAG || node.field_count() != 1 {
        return Ok(None);
    }
    let operand = node_field(model, node, 0, "class-complement operand")?;
    if model.node(operand)?.tag() != ENTITY_TAG {
        return Ok(None);
    }
    let entity_id = symbols.entity_symbol_for_node(operand).ok_or_else(|| {
        EncodedValidationError::invariant(
            "class-complement operand is absent from the reachable entity mapping",
        )
    })?;
    let entity = symbols
        .entity_domain
        .values
        .get(usize::try_from(entity_id).unwrap_or(usize::MAX))
        .ok_or_else(|| {
            EncodedValidationError::invariant("class-complement operand entity ID is dangling")
        })?;
    Ok(entity.display.starts_with("class:").then_some(entity_id))
}

fn named_data_range_domain<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    has_data_roles: bool,
    scope_maps: &[AnonymousScopeMap],
    budget: &mut PhaseBudget,
) -> EncodedResult<DecodedSymbolDomain> {
    let mut pending = Vec::new();
    for entity in &symbols.entity_domain.values {
        budget.claim_work(1)?;
        if !entity.display.starts_with("datatype:") {
            continue;
        }
        let following = pending.len().checked_add(1).ok_or_else(|| {
            EncodedValidationError::resource("named data-range symbol count overflowed")
        })?;
        PhaseBudget::count(
            following,
            budget.limits.max_data_range_symbols,
            "data-range symbol count",
        )?;
        budget.claim_owned(size_of::<DecodedSymbolValue>())?;
        budget.claim_owned(entity.key.len())?;
        budget.claim_owned(entity.display.len())?;
        pending.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("named data-range symbol allocation failed")
        })?;
        pending.push(DecodedSymbolValue {
            identifier: 0,
            key: entity.key.clone(),
            display: entity.display.clone(),
            generated: entity.generated,
            query_local: entity.query_local,
        });
    }

    let mut expressions = Vec::new();
    for root in &symbols.roots {
        budget.claim_work(1)?;
        let range = match root.handler {
            RootHandler::DataPropertyRange if has_data_roles => node_field(
                model,
                model.node(root.node)?,
                1,
                "data-property range value",
            )?,
            RootHandler::DatatypeDefinition => {
                node_field(model, model.node(root.node)?, 1, "datatype defining range")?
            }
            _ => continue,
        };
        let Some((base, negative)) = atomic_data_range_base(model, symbols, range)? else {
            continue;
        };
        if model.node(base)?.tag() != ENTITY_TAG {
            budget.claim_owned(size_of::<NodeId>())?;
            expressions.try_reserve(1).map_err(|_| {
                EncodedValidationError::resource("data-range selection allocation failed")
            })?;
            expressions.push(base);
        }
        if negative {
            budget.claim_owned(size_of::<NodeId>())?;
            expressions.try_reserve(1).map_err(|_| {
                EncodedValidationError::resource("data-range selection allocation failed")
            })?;
            expressions.push(range);
        }
    }
    budget.claim_work(sort_work(expressions.len()))?;
    expressions.sort_unstable();
    expressions.dedup();
    for identifier in expressions {
        let following = pending.len().checked_add(1).ok_or_else(|| {
            EncodedValidationError::resource("data-range symbol count overflowed")
        })?;
        PhaseBudget::count(
            following,
            budget.limits.max_data_range_symbols,
            "data-range symbol count",
        )?;
        let key = canonical::canonical_node_key(model, identifier, scope_maps, budget)?;
        budget.claim_work(key.len())?;
        let digest = crate::model::hex(&Sha256::digest(&key));
        let prefix = data_range_expression_prefix(model.node(identifier)?.tag())?;
        let display_len = prefix.len().checked_add(digest.len()).ok_or_else(|| {
            EncodedValidationError::resource("data-range display length overflowed")
        })?;
        budget.claim_owned(size_of::<DecodedSymbolValue>())?;
        budget.claim_owned(display_len)?;
        let mut display = String::new();
        display.try_reserve_exact(display_len).map_err(|_| {
            EncodedValidationError::resource("data-range display allocation failed")
        })?;
        display.push_str(prefix);
        display.push_str(&digest);
        pending
            .try_reserve(1)
            .map_err(|_| EncodedValidationError::resource("data-range symbol allocation failed"))?;
        pending.push(DecodedSymbolValue {
            identifier: 0,
            key,
            display,
            generated: false,
            query_local: false,
        });
    }

    budget.claim_work(sort_work(pending.len()))?;
    pending.sort_by(|left, right| left.key.cmp(&right.key));
    let mut values = Vec::<DecodedSymbolValue>::new();
    values.try_reserve_exact(pending.len()).map_err(|_| {
        EncodedValidationError::resource("data-range symbol result allocation failed")
    })?;
    for mut candidate in pending {
        if let Some(previous) = values.last() {
            if previous.key == candidate.key {
                if previous.display != candidate.display
                    || previous.generated != candidate.generated
                    || previous.query_local != candidate.query_local
                {
                    return Err(EncodedValidationError::invariant(
                        "data-range symbol key has conflicting metadata",
                    ));
                }
                continue;
            }
        }
        candidate.identifier = u32::try_from(values.len())
            .map_err(|_| EncodedValidationError::resource("data-range symbol ID exceeds u32"))?;
        values.push(candidate);
    }
    Ok(DecodedSymbolDomain {
        kind: SymbolKind::DataRange,
        values,
    })
}

fn data_range_expression_prefix(tag: u16) -> EncodedResult<&'static str> {
    match tag {
        DATA_COMPLEMENT_OF_TAG => Ok("DataComplementOf:"),
        DATA_ONE_OF_TAG => Ok("DataOneOf:"),
        DATATYPE_RESTRICTION_TAG => Ok("DatatypeRestriction:"),
        _ => Err(EncodedValidationError::invariant(
            "selected data-range expression has an unsupported constructor",
        )),
    }
}

fn atomic_data_range_base<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    identifier: NodeId,
) -> EncodedResult<Option<(NodeId, bool)>> {
    let node = model.node(identifier)?;
    let (base, negative) = if node.tag() == DATA_COMPLEMENT_OF_TAG {
        if node.field_count() != 1 {
            return Err(EncodedValidationError::invariant(
                "data complement no longer has schema-1 shape",
            ));
        }
        (node_field(model, node, 0, "data-complement operand")?, true)
    } else {
        (identifier, false)
    };
    let base_node = model.node(base)?;
    match base_node.tag() {
        ENTITY_TAG => {
            let entity_id = symbols.entity_symbol_for_node(base).ok_or_else(|| {
                EncodedValidationError::invariant(
                    "atomic data-range entity is absent from the reachable entity mapping",
                )
            })?;
            let entity = symbols
                .entity_domain
                .values
                .get(usize::try_from(entity_id).unwrap_or(usize::MAX))
                .ok_or_else(|| {
                    EncodedValidationError::invariant("atomic data-range entity ID is dangling")
                })?;
            Ok(entity
                .display
                .starts_with("datatype:")
                .then_some((base, negative)))
        }
        DATA_ONE_OF_TAG if base_node.field_count() == 1 => Ok(Some((base, negative))),
        DATATYPE_RESTRICTION_TAG if base_node.field_count() == 2 => Ok(Some((base, negative))),
        DATA_ONE_OF_TAG | DATATYPE_RESTRICTION_TAG => Err(EncodedValidationError::invariant(
            "atomic data-range expression no longer has schema-1 shape",
        )),
        _ => Ok(None),
    }
}

#[derive(Debug, Eq, PartialEq)]
struct RawLiteralSymbol {
    key: Vec<u8>,
    display: String,
    data_identity_key: Option<Vec<u8>>,
}

#[derive(Debug, Eq, PartialEq)]
struct ExtractedLiteral {
    display: String,
    data_identity_key: Option<Vec<u8>>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum StringDatatypeKind {
    PlainLiteral,
    String,
    NormalizedString,
    Token,
    Language,
    Name,
    NcName,
    NmToken,
}

fn literal_symbol_domains<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    budget: &mut PhaseBudget,
) -> EncodedResult<(DecodedSymbolDomain, DecodedSymbolDomain, Vec<Option<u32>>)> {
    let mut candidates = Vec::<RawLiteralSymbol>::new();
    for node_index in 0..model.summary().node_count {
        budget.claim_work(1)?;
        let node = model.node_at(node_index)?.ok_or_else(|| {
            EncodedValidationError::invariant("validated literal node disappeared")
        })?;
        if node.tag() != LITERAL_TAG || !symbols.semantic_node_is_reachable(node.id()) {
            continue;
        }
        let following = candidates.len().checked_add(1).ok_or_else(|| {
            EncodedValidationError::resource("source-literal symbol count overflowed")
        })?;
        PhaseBudget::count(
            following,
            budget.limits.max_source_literal_symbols,
            "source-literal symbol count",
        )?;
        let key = canonical::canonical_node_key(model, node.id(), &[], budget)?;
        let extracted = extract_literal(model, symbols, node, budget)?;
        budget.claim_owned(size_of::<RawLiteralSymbol>())?;
        candidates.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("source-literal candidate allocation failed")
        })?;
        candidates.push(RawLiteralSymbol {
            key,
            display: extracted.display,
            data_identity_key: extracted.data_identity_key,
        });
    }
    budget.claim_work(sort_work(candidates.len()))?;
    candidates.sort_by(|left, right| left.key.cmp(&right.key));
    let mut unique = Vec::<RawLiteralSymbol>::new();
    unique.try_reserve_exact(candidates.len()).map_err(|_| {
        EncodedValidationError::resource("source-literal deduplication allocation failed")
    })?;
    for candidate in candidates {
        if let Some(previous) = unique.last() {
            if previous.key == candidate.key {
                if previous.display != candidate.display
                    || previous.data_identity_key != candidate.data_identity_key
                {
                    return Err(EncodedValidationError::invariant(
                        "source-literal key has conflicting metadata",
                    ));
                }
                continue;
            }
        }
        unique.push(candidate);
    }

    let mut data_keys = Vec::<Vec<u8>>::new();
    for candidate in &unique {
        let Some(key) = &candidate.data_identity_key else {
            continue;
        };
        budget.claim_owned(key.len().saturating_add(size_of::<Vec<u8>>()))?;
        data_keys
            .try_reserve(1)
            .map_err(|_| EncodedValidationError::resource("data-value key allocation failed"))?;
        data_keys.push(key.clone());
    }
    budget.claim_work(sort_work(data_keys.len()))?;
    data_keys.sort_unstable();
    data_keys.dedup();
    PhaseBudget::count(
        data_keys.len(),
        budget.limits.max_data_value_symbols,
        "data-value symbol count",
    )?;

    let mut data_values = Vec::<DecodedSymbolValue>::new();
    budget.claim_owned(
        data_keys
            .len()
            .checked_mul(size_of::<DecodedSymbolValue>())
            .ok_or_else(|| {
                EncodedValidationError::resource("data-value symbol output overflowed")
            })?,
    )?;
    data_values
        .try_reserve_exact(data_keys.len())
        .map_err(|_| {
            EncodedValidationError::resource("data-value symbol output allocation failed")
        })?;
    for key in data_keys {
        let identifier = u32::try_from(data_values.len())
            .map_err(|_| EncodedValidationError::resource("data-value symbol ID exceeds u32"))?;
        let display = data_value_display(&key, budget)?;
        data_values.push(DecodedSymbolValue {
            identifier,
            key,
            display,
            generated: false,
            query_local: false,
        });
    }

    let mut source_values = Vec::<DecodedSymbolValue>::new();
    let mut source_data_identity_ids = Vec::<Option<u32>>::new();
    budget.claim_owned(
        unique
            .len()
            .checked_mul(size_of::<DecodedSymbolValue>() + size_of::<Option<u32>>())
            .ok_or_else(|| {
                EncodedValidationError::resource("source-literal symbol output overflowed")
            })?,
    )?;
    source_values.try_reserve_exact(unique.len()).map_err(|_| {
        EncodedValidationError::resource("source-literal symbol output allocation failed")
    })?;
    source_data_identity_ids
        .try_reserve_exact(unique.len())
        .map_err(|_| {
            EncodedValidationError::resource("source data-identity mapping allocation failed")
        })?;
    for candidate in unique {
        let identifier = u32::try_from(source_values.len()).map_err(|_| {
            EncodedValidationError::resource("source-literal symbol ID exceeds u32")
        })?;
        let data_identity_id = candidate
            .data_identity_key
            .as_ref()
            .map(|key| {
                budget.claim_work(binary_search_work(data_values.len()))?;
                let index = data_values
                    .binary_search_by(|value| value.key.cmp(key))
                    .map_err(|_| {
                        EncodedValidationError::invariant(
                            "source literal data identity disappeared",
                        )
                    })?;
                u32::try_from(index).map_err(|_| {
                    EncodedValidationError::resource("data-value symbol ID exceeds u32")
                })
            })
            .transpose()?;
        source_values.push(DecodedSymbolValue {
            identifier,
            key: candidate.key,
            display: candidate.display,
            generated: false,
            query_local: false,
        });
        source_data_identity_ids.push(data_identity_id);
    }
    Ok((
        DecodedSymbolDomain {
            kind: SymbolKind::SourceLiteral,
            values: source_values,
        },
        DecodedSymbolDomain {
            kind: SymbolKind::DataValue,
            values: data_values,
        },
        source_data_identity_ids,
    ))
}

fn extract_literal<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    literal: NodeRef,
    budget: &mut PhaseBudget,
) -> EncodedResult<ExtractedLiteral> {
    if literal.tag() != LITERAL_TAG || literal.field_count() != 3 {
        return Err(EncodedValidationError::invariant(
            "literal node no longer has schema-1 shape",
        ));
    }
    let fields = literal.fields();
    let lexical = text_field(model, fields.start, "literal lexical form", budget)?;
    let datatype_index = fields.start.checked_add(1).ok_or_else(|| {
        EncodedValidationError::invariant("literal datatype field index overflowed")
    })?;
    let datatype_component = required_component(model.field(datatype_index)?, "literal datatype")?;
    let ComponentValue::Node(datatype_node) = model.resolve(datatype_component)? else {
        return Err(EncodedValidationError::invariant(
            "literal datatype field is not a node",
        ));
    };
    let datatype_symbol_id = symbols
        .entity_symbol_for_node(datatype_node)
        .ok_or_else(|| EncodedValidationError::invariant("literal datatype is not reachable"))?;
    let datatype = symbols
        .entity_domain
        .values
        .get(usize::try_from(datatype_symbol_id).map_err(|_| {
            EncodedValidationError::invariant("literal datatype symbol ID exceeds usize")
        })?)
        .ok_or_else(|| EncodedValidationError::invariant("literal datatype symbol is dangling"))?;
    let datatype_iri = datatype.display.strip_prefix("datatype:").ok_or_else(|| {
        EncodedValidationError::invariant("literal datatype symbol changed entity kind")
    })?;
    let language_index = fields.start.checked_add(2).ok_or_else(|| {
        EncodedValidationError::invariant("literal language field index overflowed")
    })?;
    let language_component = required_component(model.field(language_index)?, "literal language")?;
    let language = match model.resolve(language_component)? {
        ComponentValue::None => None,
        ComponentValue::Scalar(value) => Some(text_scalar(value, "literal language", budget)?),
        ComponentValue::Node(_) | ComponentValue::Collection(_) => {
            return Err(EncodedValidationError::invariant(
                "literal language field is not optional text",
            ));
        }
    };
    let lexical_repr = python_string_repr(&lexical, budget)?;
    let language_len = language
        .as_ref()
        .map_or(0, |value| value.len().saturating_add(1));
    let display_len = "literal:"
        .len()
        .checked_add(lexical_repr.len())
        .and_then(|value| value.checked_add("^^".len()))
        .and_then(|value| value.checked_add(datatype_iri.len()))
        .and_then(|value| value.checked_add(language_len))
        .ok_or_else(|| EncodedValidationError::resource("literal display length overflowed"))?;
    budget.claim_owned(display_len)?;
    let mut display = String::new();
    display
        .try_reserve_exact(display_len)
        .map_err(|_| EncodedValidationError::resource("literal display allocation failed"))?;
    display.push_str("literal:");
    display.push_str(&lexical_repr);
    display.push_str("^^");
    display.push_str(datatype_iri);
    if let Some(language) = &language {
        display.push('@');
        display.push_str(language.as_str());
    }
    let data_identity_key =
        literal_data_identity_key(&lexical, datatype_iri, language.as_deref(), budget)?;
    Ok(ExtractedLiteral {
        display,
        data_identity_key,
    })
}

fn literal_data_identity_key(
    lexical: &str,
    datatype_iri: &str,
    language: Option<&str>,
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<Vec<u8>>> {
    if datatype_iri == XSD_BOOLEAN_IRI {
        return boolean_data_identity_key(lexical, budget).map(Some);
    }
    if let Some(bounds) = integer_datatype_bounds(datatype_iri) {
        return integer_data_identity_key(lexical, bounds, budget).map(Some);
    }
    if datatype_iri == XSD_DECIMAL_IRI {
        return decimal_data_identity_key(lexical, budget).map(Some);
    }
    if datatype_iri == OWL_RATIONAL_IRI {
        return rational_literal_data_identity_key(lexical, budget).map(Some);
    }
    let ieee_width = match datatype_iri {
        XSD_FLOAT_IRI => Some(IEEEWidth::Float32),
        XSD_DOUBLE_IRI => Some(IEEEWidth::Float64),
        _ => None,
    };
    if let Some(width) = ieee_width {
        return ieee_data_identity_key(lexical, width, budget).map(Some);
    }
    let binary_kind = match datatype_iri {
        XSD_HEX_BINARY_IRI => Some(EncodedBinaryKind::Hex),
        XSD_BASE64_BINARY_IRI => Some(EncodedBinaryKind::Base64),
        _ => None,
    };
    if let Some(kind) = binary_kind {
        return binary_data_identity_key(lexical, kind, budget).map(Some);
    }
    if datatype_iri == XSD_ANY_URI_IRI {
        return uri_data_identity_key(lexical, budget).map(Some);
    }
    let require_timezone = match datatype_iri {
        XSD_DATE_TIME_IRI => Some(false),
        XSD_DATE_TIME_STAMP_IRI => Some(true),
        _ => None,
    };
    if let Some(require_timezone) = require_timezone {
        return date_time_data_identity_key(lexical, require_timezone, budget).map(Some);
    }
    if datatype_iri == RDF_XML_LITERAL_IRI {
        return xml_literal_data_identity_key(lexical, budget).map(Some);
    }
    string_data_identity_key(lexical, datatype_iri, language, budget)
}

fn xml_literal_data_identity_key(
    lexical: &str,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<u8>> {
    let character_count = lexical.chars().count();
    PhaseBudget::count(
        character_count,
        budget.limits.max_literal_characters,
        "literal character count",
    )?;
    let canonical = super::xml_literal::canonicalize(lexical, budget)?;
    let payload = serde_json::to_vec(&("xml-literal-c14n-v1", canonical.as_str()))
        .map_err(|_| EncodedValidationError::invariant("XML literal identity encoding failed"))?;
    prefixed_data_identity_key(&payload, budget)
}

fn boolean_data_identity_key(lexical: &str, budget: &mut PhaseBudget) -> EncodedResult<Vec<u8>> {
    let character_count = lexical.chars().count();
    PhaseBudget::count(
        character_count,
        budget.limits.max_literal_characters,
        "literal character count",
    )?;
    budget.claim_work(character_count)?;
    let payload = match lexical {
        "true" | "1" => b"[\"boolean\",true]".as_slice(),
        "false" | "0" => b"[\"boolean\",false]".as_slice(),
        _ => {
            return Err(EncodedValidationError::invariant(
                "Boolean literal is outside its datatype lexical space",
            ));
        }
    };
    prefixed_data_identity_key(payload, budget)
}

type IntegerBounds = (Option<i128>, Option<i128>);

fn integer_datatype_bounds(datatype_iri: &str) -> Option<IntegerBounds> {
    let local = datatype_iri.strip_prefix(XSD_NAMESPACE)?;
    match local {
        "integer" => Some((None, None)),
        "nonNegativeInteger" => Some((Some(0), None)),
        "positiveInteger" => Some((Some(1), None)),
        "nonPositiveInteger" => Some((None, Some(0))),
        "negativeInteger" => Some((None, Some(-1))),
        "long" => Some((
            Some(-9_223_372_036_854_775_808),
            Some(9_223_372_036_854_775_807),
        )),
        "int" => Some((Some(-2_147_483_648), Some(2_147_483_647))),
        "short" => Some((Some(-32_768), Some(32_767))),
        "byte" => Some((Some(-128), Some(127))),
        "unsignedLong" => Some((Some(0), Some(18_446_744_073_709_551_615))),
        "unsignedInt" => Some((Some(0), Some(4_294_967_295))),
        "unsignedShort" => Some((Some(0), Some(65_535))),
        "unsignedByte" => Some((Some(0), Some(255))),
        _ => None,
    }
}

fn integer_data_identity_key(
    lexical: &str,
    (lower, upper): IntegerBounds,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<u8>> {
    let character_count = lexical.chars().count();
    PhaseBudget::count(
        character_count,
        budget.limits.max_literal_characters,
        "literal character count",
    )?;
    let bytes = lexical.as_bytes();
    let (negative, digits) = match bytes.first() {
        Some(b'-') => (true, &bytes[1..]),
        Some(b'+') => (false, &bytes[1..]),
        Some(_) | None => (false, bytes),
    };
    PhaseBudget::count(
        digits.len(),
        budget.limits.max_numeric_digits,
        "numeric digit count",
    )?;
    budget.claim_work(bytes.len())?;
    if digits.is_empty() || !digits.iter().all(u8::is_ascii_digit) {
        return Err(EncodedValidationError::invariant(
            "integer literal is outside its datatype lexical space",
        ));
    }
    let temporary_bytes = digits
        .len()
        .checked_mul(2)
        .and_then(|value| value.checked_add(1))
        .ok_or_else(|| EncodedValidationError::resource("integer temporary size overflowed"))?;
    budget.claim_owned(temporary_bytes)?;
    let magnitude = BigInt::parse_bytes(digits, 10).ok_or_else(|| {
        EncodedValidationError::invariant("integer literal magnitude could not be decoded")
    })?;
    let value = if negative { -magnitude } else { magnitude };
    if lower.is_some_and(|bound| value < BigInt::from(bound))
        || upper.is_some_and(|bound| value > BigInt::from(bound))
    {
        return Err(EncodedValidationError::invariant(
            "integer literal is outside its datatype value space",
        ));
    }
    rational_bigint_data_identity_key(value, BigInt::from(1_u8), budget)
}

fn decimal_data_identity_key(lexical: &str, budget: &mut PhaseBudget) -> EncodedResult<Vec<u8>> {
    let character_count = lexical.chars().count();
    PhaseBudget::count(
        character_count,
        budget.limits.max_literal_characters,
        "literal character count",
    )?;
    let bytes = lexical.as_bytes();
    let (negative, unsigned) = match bytes.first() {
        Some(b'-') => (true, &bytes[1..]),
        Some(b'+') => (false, &bytes[1..]),
        Some(_) | None => (false, bytes),
    };
    budget.claim_work(bytes.len())?;
    let mut point = None;
    for (index, byte) in unsigned.iter().copied().enumerate() {
        if byte == b'.' {
            if point.replace(index).is_some() {
                return Err(EncodedValidationError::invariant(
                    "decimal literal is outside its datatype lexical space",
                ));
            }
        } else if !byte.is_ascii_digit() {
            return Err(EncodedValidationError::invariant(
                "decimal literal is outside its datatype lexical space",
            ));
        }
    }
    let (whole, fraction) = point.map_or((unsigned, &b""[..]), |index| {
        (&unsigned[..index], &unsigned[index + 1..])
    });
    if whole.is_empty() && fraction.is_empty() {
        return Err(EncodedValidationError::invariant(
            "decimal literal is outside its datatype lexical space",
        ));
    }
    let inserted_zero = usize::from(whole.is_empty());
    let digit_count = whole
        .len()
        .checked_add(fraction.len())
        .and_then(|value| value.checked_add(inserted_zero))
        .ok_or_else(|| EncodedValidationError::resource("decimal digit count overflowed"))?;
    PhaseBudget::count(
        digit_count,
        budget.limits.max_numeric_digits,
        "numeric digit count",
    )?;
    PhaseBudget::count(
        fraction.len(),
        budget.limits.max_decimal_exponent,
        "decimal scale",
    )?;
    let temporary_bytes = digit_count
        .checked_add(fraction.len())
        .and_then(|value| value.checked_mul(4))
        .and_then(|value| value.checked_add(2))
        .ok_or_else(|| EncodedValidationError::resource("decimal temporary size overflowed"))?;
    budget.claim_owned(temporary_bytes)?;
    budget.claim_work(fraction.len())?;
    let mut digits = Vec::new();
    digits
        .try_reserve_exact(digit_count)
        .map_err(|_| EncodedValidationError::resource("decimal digit allocation failed"))?;
    if whole.is_empty() {
        digits.push(b'0');
    } else {
        digits.extend_from_slice(whole);
    }
    digits.extend_from_slice(fraction);
    let magnitude = BigInt::parse_bytes(&digits, 10).ok_or_else(|| {
        EncodedValidationError::invariant("decimal literal magnitude could not be decoded")
    })?;
    let numerator = if negative { -magnitude } else { magnitude };
    let exponent = u32::try_from(fraction.len())
        .map_err(|_| EncodedValidationError::resource("decimal scale exceeds u32"))?;
    let denominator = BigInt::from(10_u8).pow(exponent);
    rational_bigint_data_identity_key(numerator, denominator, budget)
}

fn rational_literal_data_identity_key(
    lexical: &str,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<u8>> {
    let character_count = lexical.chars().count();
    PhaseBudget::count(
        character_count,
        budget.limits.max_literal_characters,
        "literal character count",
    )?;
    let bytes = lexical.as_bytes();
    let (negative, unsigned) = match bytes.first() {
        Some(b'-') => (true, &bytes[1..]),
        Some(b'+') => (false, &bytes[1..]),
        Some(_) | None => (false, bytes),
    };
    budget.claim_work(bytes.len())?;
    let Some(slash) = unsigned.iter().position(|byte| *byte == b'/') else {
        return Err(EncodedValidationError::invariant(
            "rational literal is outside its datatype lexical space",
        ));
    };
    let numerator_digits = &unsigned[..slash];
    let denominator_digits = &unsigned[slash + 1..];
    if numerator_digits.is_empty()
        || denominator_digits.is_empty()
        || !numerator_digits.iter().all(u8::is_ascii_digit)
        || !denominator_digits.iter().all(u8::is_ascii_digit)
    {
        return Err(EncodedValidationError::invariant(
            "rational literal is outside its datatype lexical space",
        ));
    }
    PhaseBudget::count(
        numerator_digits.len(),
        budget.limits.max_numeric_digits,
        "numeric numerator digit count",
    )?;
    PhaseBudget::count(
        denominator_digits.len(),
        budget.limits.max_numeric_digits,
        "numeric denominator digit count",
    )?;
    let temporary_bytes = numerator_digits
        .len()
        .checked_add(denominator_digits.len())
        .and_then(|value| value.checked_mul(4))
        .and_then(|value| value.checked_add(2))
        .ok_or_else(|| EncodedValidationError::resource("rational temporary size overflowed"))?;
    budget.claim_owned(temporary_bytes)?;
    let numerator_magnitude = BigInt::parse_bytes(numerator_digits, 10).ok_or_else(|| {
        EncodedValidationError::invariant("rational numerator could not be decoded")
    })?;
    let denominator = BigInt::parse_bytes(denominator_digits, 10).ok_or_else(|| {
        EncodedValidationError::invariant("rational denominator could not be decoded")
    })?;
    if denominator.sign() != Sign::Plus {
        return Err(EncodedValidationError::invariant(
            "rational literal is outside its datatype lexical space",
        ));
    }
    let numerator = if negative {
        -numerator_magnitude
    } else {
        numerator_magnitude
    };
    rational_bigint_data_identity_key(numerator, denominator, budget)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum IEEEWidth {
    Float32,
    Float64,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct IEEELayout {
    width: u32,
    exponent_bits: u32,
    fraction_bits: u32,
    bias: i64,
}

impl IEEEWidth {
    const fn layout(self) -> IEEELayout {
        match self {
            Self::Float32 => IEEELayout {
                width: 32,
                exponent_bits: 8,
                fraction_bits: 23,
                bias: 127,
            },
            Self::Float64 => IEEELayout {
                width: 64,
                exponent_bits: 11,
                fraction_bits: 52,
                bias: 1023,
            },
        }
    }

    const fn name(self) -> &'static str {
        match self {
            Self::Float32 => "float32",
            Self::Float64 => "float64",
        }
    }
}

impl IEEELayout {
    const fn precision(self) -> u32 {
        self.fraction_bits + 1
    }

    const fn minimum_normal_exponent(self) -> i64 {
        1 - self.bias
    }

    const fn maximum_normal_exponent(self) -> i64 {
        self.bias
    }

    const fn minimum_subnormal_exponent(self) -> i64 {
        self.minimum_normal_exponent() - self.fraction_bits as i64
    }

    const fn exponent_mask(self) -> u64 {
        (1_u64 << self.exponent_bits) - 1
    }

    const fn sign_bit(self) -> u64 {
        1_u64 << (self.width - 1)
    }
}

fn ieee_data_identity_key(
    lexical: &str,
    width: IEEEWidth,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<u8>> {
    let character_count = lexical.chars().count();
    PhaseBudget::count(
        character_count,
        budget.limits.max_literal_characters,
        "literal character count",
    )?;
    let layout = width.layout();
    let bits = match lexical {
        "INF" | "+INF" => layout.exponent_mask() << layout.fraction_bits,
        "-INF" => layout.sign_bit() | (layout.exponent_mask() << layout.fraction_bits),
        "NaN" => {
            (layout.exponent_mask() << layout.fraction_bits) | (1_u64 << (layout.fraction_bits - 1))
        }
        _ => {
            let (negative, numerator, denominator) = ieee_decimal_ratio(lexical, budget)?;
            ieee_ratio_to_bits(&numerator, &denominator, negative, layout)?
        }
    };
    let digits = usize::try_from(layout.width / 4)
        .map_err(|_| EncodedValidationError::resource("IEEE hexadecimal width exceeds usize"))?;
    let payload = format!(
        "[\"ieee-identity-v1\",\"{}\",\"{bits:0digits$x}\"]",
        width.name()
    );
    prefixed_data_identity_key(payload.as_bytes(), budget)
}

fn ieee_decimal_ratio(
    lexical: &str,
    budget: &mut PhaseBudget,
) -> EncodedResult<(bool, BigUint, BigUint)> {
    let bytes = lexical.as_bytes();
    let (negative, unsigned) = match bytes.first() {
        Some(b'-') => (true, &bytes[1..]),
        Some(b'+') => (false, &bytes[1..]),
        Some(_) | None => (false, bytes),
    };
    budget.claim_work(bytes.len())?;
    let mut exponent_marker = None;
    for (index, byte) in unsigned.iter().copied().enumerate() {
        if matches!(byte, b'e' | b'E') && exponent_marker.replace(index).is_some() {
            return Err(EncodedValidationError::invariant(
                "floating-point literal is outside its datatype lexical space",
            ));
        }
    }
    let (mantissa, exponent_text) = exponent_marker.map_or((unsigned, None), |index| {
        (&unsigned[..index], Some(&unsigned[index + 1..]))
    });
    let exponent = if let Some(value) = exponent_text {
        let (exponent_negative, digits) = match value.first() {
            Some(b'-') => (true, &value[1..]),
            Some(b'+') => (false, &value[1..]),
            Some(_) | None => (false, value),
        };
        if digits.is_empty() || !digits.iter().all(u8::is_ascii_digit) {
            return Err(EncodedValidationError::invariant(
                "floating-point literal is outside its datatype lexical space",
            ));
        }
        PhaseBudget::count(
            digits.len(),
            budget.limits.max_numeric_digits,
            "floating-point exponent digit count",
        )?;
        let magnitude = BigUint::parse_bytes(digits, 10).ok_or_else(|| {
            EncodedValidationError::invariant("floating-point exponent could not be decoded")
        })?;
        let maximum = BigUint::from(budget.limits.max_decimal_exponent);
        if magnitude > maximum {
            return Err(EncodedValidationError::resource(
                "named-class floating-point exponent exceeds its limit",
            ));
        }
        let magnitude = magnitude.to_i64().ok_or_else(|| {
            EncodedValidationError::resource("floating-point exponent exceeds i64")
        })?;
        if exponent_negative {
            -magnitude
        } else {
            magnitude
        }
    } else {
        0
    };
    let mut point = None;
    for (index, byte) in mantissa.iter().copied().enumerate() {
        if byte == b'.' {
            if point.replace(index).is_some() {
                return Err(EncodedValidationError::invariant(
                    "floating-point literal is outside its datatype lexical space",
                ));
            }
        } else if !byte.is_ascii_digit() {
            return Err(EncodedValidationError::invariant(
                "floating-point literal is outside its datatype lexical space",
            ));
        }
    }
    let (whole, fraction) = point.map_or((mantissa, &b""[..]), |index| {
        (&mantissa[..index], &mantissa[index + 1..])
    });
    if whole.is_empty() && fraction.is_empty() {
        return Err(EncodedValidationError::invariant(
            "floating-point literal is outside its datatype lexical space",
        ));
    }
    let inserted_zero = usize::from(whole.is_empty());
    let digit_count = whole
        .len()
        .checked_add(fraction.len())
        .and_then(|value| value.checked_add(inserted_zero))
        .ok_or_else(|| EncodedValidationError::resource("floating-point digit count overflowed"))?;
    PhaseBudget::count(
        digit_count,
        budget.limits.max_numeric_digits,
        "numeric digit count",
    )?;
    let fraction_length = i64::try_from(fraction.len())
        .map_err(|_| EncodedValidationError::resource("floating-point scale exceeds i64"))?;
    let scale = fraction_length.checked_sub(exponent).ok_or_else(|| {
        EncodedValidationError::resource("floating-point decimal scale overflowed")
    })?;
    let absolute_scale = scale.unsigned_abs();
    let maximum_scale = u64::try_from(budget.limits.max_decimal_exponent)
        .map_err(|_| EncodedValidationError::resource("decimal scale limit exceeds u64"))?;
    if absolute_scale > maximum_scale {
        return Err(EncodedValidationError::resource(
            "named-class floating-point decimal scale exceeds its limit",
        ));
    }
    let scale_size = usize::try_from(absolute_scale)
        .map_err(|_| EncodedValidationError::resource("decimal scale exceeds usize"))?;
    let temporary_bytes = digit_count
        .checked_add(scale_size)
        .and_then(|value| value.checked_mul(4))
        .and_then(|value| value.checked_add(2))
        .ok_or_else(|| {
            EncodedValidationError::resource("floating-point temporary size overflowed")
        })?;
    budget.claim_owned(temporary_bytes)?;
    budget.claim_work(scale_size)?;
    let mut digits = Vec::new();
    digits
        .try_reserve_exact(digit_count)
        .map_err(|_| EncodedValidationError::resource("floating-point digit allocation failed"))?;
    if whole.is_empty() {
        digits.push(b'0');
    } else {
        digits.extend_from_slice(whole);
    }
    digits.extend_from_slice(fraction);
    let mut numerator = BigUint::parse_bytes(&digits, 10).ok_or_else(|| {
        EncodedValidationError::invariant("floating-point magnitude could not be decoded")
    })?;
    let exponent = u32::try_from(scale_size)
        .map_err(|_| EncodedValidationError::resource("decimal scale exceeds u32"))?;
    let denominator = if scale > 0 {
        BigUint::from(10_u8).pow(exponent)
    } else {
        if scale < 0 {
            numerator *= BigUint::from(10_u8).pow(exponent);
        }
        BigUint::from(1_u8)
    };
    Ok((negative, numerator, denominator))
}

fn ieee_ratio_to_bits(
    numerator: &BigUint,
    denominator: &BigUint,
    negative: bool,
    layout: IEEELayout,
) -> EncodedResult<u64> {
    if numerator.is_zero() {
        return Ok(if negative { layout.sign_bit() } else { 0 });
    }
    let mut exponent = floor_log2_ratio(numerator, denominator)?;
    let bits = if exponent < layout.minimum_normal_exponent() {
        let shift = -layout.minimum_subnormal_exponent();
        let significand = round_scaled_ratio(numerator, denominator, shift)?;
        if significand.is_zero() {
            return Ok(if negative { layout.sign_bit() } else { 0 });
        }
        let normal_boundary = BigUint::from(1_u8) << layout.fraction_bits;
        if significand < normal_boundary {
            significand
                .to_u64()
                .ok_or_else(|| EncodedValidationError::resource("IEEE significand exceeds u64"))?
        } else {
            1_u64 << layout.fraction_bits
        }
    } else {
        let shift = i64::from(layout.fraction_bits) - exponent;
        let mut significand = round_scaled_ratio(numerator, denominator, shift)?;
        let precision_boundary = BigUint::from(1_u8) << layout.precision();
        if significand == precision_boundary {
            significand >>= 1_u32;
            exponent = exponent
                .checked_add(1)
                .ok_or_else(|| EncodedValidationError::resource("IEEE exponent overflowed"))?;
        }
        if exponent > layout.maximum_normal_exponent() {
            layout.exponent_mask() << layout.fraction_bits
        } else {
            let exponent_field = u64::try_from(exponent + layout.bias)
                .map_err(|_| EncodedValidationError::resource("IEEE exponent is negative"))?;
            let hidden_bit = BigUint::from(1_u8) << layout.fraction_bits;
            let fraction = (significand - hidden_bit)
                .to_u64()
                .ok_or_else(|| EncodedValidationError::resource("IEEE fraction exceeds u64"))?;
            (exponent_field << layout.fraction_bits) | fraction
        }
    };
    Ok(bits | if negative { layout.sign_bit() } else { 0 })
}

fn floor_log2_ratio(numerator: &BigUint, denominator: &BigUint) -> EncodedResult<i64> {
    let numerator_bits = i64::try_from(numerator.bits())
        .map_err(|_| EncodedValidationError::resource("numeric bit length exceeds i64"))?;
    let denominator_bits = i64::try_from(denominator.bits())
        .map_err(|_| EncodedValidationError::resource("numeric bit length exceeds i64"))?;
    let estimate = numerator_bits
        .checked_sub(denominator_bits)
        .ok_or_else(|| EncodedValidationError::resource("numeric exponent overflowed"))?;
    if estimate >= 0 {
        let shift = usize::try_from(estimate)
            .map_err(|_| EncodedValidationError::resource("numeric shift exceeds usize"))?;
        Ok(if numerator < &(denominator << shift) {
            estimate - 1
        } else {
            estimate
        })
    } else {
        let shift = usize::try_from(-estimate)
            .map_err(|_| EncodedValidationError::resource("numeric shift exceeds usize"))?;
        Ok(if &(numerator << shift) < denominator {
            estimate - 1
        } else {
            estimate
        })
    }
}

fn round_scaled_ratio(
    numerator: &BigUint,
    denominator: &BigUint,
    shift: i64,
) -> EncodedResult<BigUint> {
    let (scaled_numerator, scaled_denominator) = if shift >= 0 {
        let amount = usize::try_from(shift)
            .map_err(|_| EncodedValidationError::resource("numeric shift exceeds usize"))?;
        (numerator << amount, denominator.clone())
    } else {
        let amount = usize::try_from(-shift)
            .map_err(|_| EncodedValidationError::resource("numeric shift exceeds usize"))?;
        (numerator.clone(), denominator << amount)
    };
    let (mut quotient, remainder) = scaled_numerator.div_rem(&scaled_denominator);
    let doubled = &remainder << 1_u32;
    if doubled > scaled_denominator || (doubled == scaled_denominator && quotient.bit(0)) {
        quotient += BigUint::from(1_u8);
    }
    Ok(quotient)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum EncodedBinaryKind {
    Hex,
    Base64,
}

impl EncodedBinaryKind {
    const fn name(self) -> &'static str {
        match self {
            Self::Hex => "hexBinary",
            Self::Base64 => "base64Binary",
        }
    }
}

fn binary_data_identity_key(
    lexical: &str,
    kind: EncodedBinaryKind,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<u8>> {
    let character_count = lexical.chars().count();
    PhaseBudget::count(
        character_count,
        budget.limits.max_literal_characters,
        "literal character count",
    )?;
    budget.claim_work(character_count)?;
    let normalized = collapse_xml_whitespace(lexical, budget)?;
    let octets = match kind {
        EncodedBinaryKind::Hex => decode_hex_binary(&normalized, budget)?,
        EncodedBinaryKind::Base64 => decode_base64_binary(&normalized, budget)?,
    };
    let hex_len = octets
        .len()
        .checked_mul(2)
        .ok_or_else(|| EncodedValidationError::resource("binary hexadecimal size overflowed"))?;
    budget.claim_owned(hex_len)?;
    let mut hex = String::new();
    hex.try_reserve_exact(hex_len)
        .map_err(|_| EncodedValidationError::resource("binary hexadecimal allocation failed"))?;
    for byte in octets {
        hex.push(char::from(HEX_DIGITS[usize::from(byte >> 4)]));
        hex.push(char::from(HEX_DIGITS[usize::from(byte & 0x0f)]));
    }
    let payload = format!("[\"binary-identity-v1\",\"{}\",\"{hex}\"]", kind.name());
    prefixed_data_identity_key(payload.as_bytes(), budget)
}

fn collapse_xml_whitespace(value: &str, budget: &mut PhaseBudget) -> EncodedResult<String> {
    budget.claim_owned(value.len())?;
    let mut normalized = String::new();
    normalized
        .try_reserve_exact(value.len())
        .map_err(|_| EncodedValidationError::resource("binary normalization allocation failed"))?;
    let mut pending_space = false;
    for character in value.chars() {
        if matches!(character, '\t' | '\n' | '\r' | ' ') {
            pending_space = !normalized.is_empty();
        } else {
            if pending_space {
                normalized.push(' ');
                pending_space = false;
            }
            normalized.push(character);
        }
    }
    Ok(normalized)
}

fn decode_hex_binary(value: &str, budget: &mut PhaseBudget) -> EncodedResult<Vec<u8>> {
    let bytes = value.as_bytes();
    if bytes.contains(&b' ') || bytes.len() % 2 != 0 {
        return Err(EncodedValidationError::invariant(
            "hexBinary literal is outside its datatype lexical space",
        ));
    }
    let byte_count = bytes.len() / 2;
    PhaseBudget::count(
        byte_count,
        budget.limits.max_binary_bytes,
        "decoded binary byte count",
    )?;
    budget.claim_owned(byte_count)?;
    budget.claim_work(byte_count)?;
    let mut output = Vec::new();
    output
        .try_reserve_exact(byte_count)
        .map_err(|_| EncodedValidationError::resource("hexBinary allocation failed"))?;
    for pair in bytes.chunks_exact(2) {
        let Some(high) = hex_value(pair[0]) else {
            return Err(EncodedValidationError::invariant(
                "hexBinary literal is outside its datatype lexical space",
            ));
        };
        let Some(low) = hex_value(pair[1]) else {
            return Err(EncodedValidationError::invariant(
                "hexBinary literal is outside its datatype lexical space",
            ));
        };
        output.push((high << 4) | low);
    }
    Ok(output)
}

const fn hex_value(value: u8) -> Option<u8> {
    match value {
        b'0'..=b'9' => Some(value - b'0'),
        b'A'..=b'F' => Some(value - b'A' + 10),
        b'a'..=b'f' => Some(value - b'a' + 10),
        _ => None,
    }
}

fn decode_base64_binary(value: &str, budget: &mut PhaseBudget) -> EncodedResult<Vec<u8>> {
    if !value.is_ascii() {
        return Err(EncodedValidationError::invariant(
            "base64Binary literal is outside its datatype lexical space",
        ));
    }
    budget.claim_owned(value.len())?;
    let mut compact = Vec::new();
    compact
        .try_reserve_exact(value.len())
        .map_err(|_| EncodedValidationError::resource("base64Binary compaction failed"))?;
    compact.extend(value.bytes().filter(|byte| *byte != b' '));
    if compact.len() % 4 != 0 {
        return Err(EncodedValidationError::invariant(
            "base64Binary literal is outside its datatype lexical space",
        ));
    }
    let padding = compact
        .iter()
        .rev()
        .take_while(|byte| **byte == b'=')
        .count();
    if padding > 2 || compact[..compact.len().saturating_sub(padding)].contains(&b'=') {
        return Err(EncodedValidationError::invariant(
            "base64Binary literal is outside its datatype lexical space",
        ));
    }
    let byte_count = compact
        .len()
        .checked_div(4)
        .and_then(|value| value.checked_mul(3))
        .and_then(|value| value.checked_sub(padding))
        .ok_or_else(|| EncodedValidationError::resource("base64Binary size overflowed"))?;
    PhaseBudget::count(
        byte_count,
        budget.limits.max_binary_bytes,
        "decoded binary byte count",
    )?;
    budget.claim_owned(byte_count)?;
    budget.claim_work(compact.len())?;
    let mut output = Vec::new();
    output
        .try_reserve_exact(byte_count)
        .map_err(|_| EncodedValidationError::resource("base64Binary allocation failed"))?;
    for (index, quartet) in compact.chunks_exact(4).enumerate() {
        let last = index + 1 == compact.len() / 4;
        let Some(first) = base64_value(quartet[0]) else {
            return invalid_base64();
        };
        let Some(second) = base64_value(quartet[1]) else {
            return invalid_base64();
        };
        let third = if quartet[2] == b'=' {
            if !last || padding != 2 || second & 0x0f != 0 {
                return invalid_base64();
            }
            0
        } else {
            let Some(value) = base64_value(quartet[2]) else {
                return invalid_base64();
            };
            value
        };
        let fourth = if quartet[3] == b'=' {
            if !last || padding == 0 || (padding == 1 && third & 0x03 != 0) {
                return invalid_base64();
            }
            0
        } else {
            let Some(value) = base64_value(quartet[3]) else {
                return invalid_base64();
            };
            value
        };
        output.push((first << 2) | (second >> 4));
        if quartet[2] != b'=' {
            output.push((second << 4) | (third >> 2));
        }
        if quartet[3] != b'=' {
            output.push((third << 6) | fourth);
        }
    }
    Ok(output)
}

const fn base64_value(value: u8) -> Option<u8> {
    match value {
        b'A'..=b'Z' => Some(value - b'A'),
        b'a'..=b'z' => Some(value - b'a' + 26),
        b'0'..=b'9' => Some(value - b'0' + 52),
        b'+' => Some(62),
        b'/' => Some(63),
        _ => None,
    }
}

fn invalid_base64<T>() -> EncodedResult<T> {
    Err(EncodedValidationError::invariant(
        "base64Binary literal is outside its datatype lexical space",
    ))
}

fn uri_data_identity_key(lexical: &str, budget: &mut PhaseBudget) -> EncodedResult<Vec<u8>> {
    let character_count = lexical.chars().count();
    PhaseBudget::count(
        character_count,
        budget.limits.max_literal_characters,
        "literal character count",
    )?;
    budget.claim_work(character_count)?;
    if !lexical.chars().all(is_xml_character) {
        return Err(EncodedValidationError::invariant(
            "anyURI literal is outside its datatype lexical space",
        ));
    }
    let content_len = json_string_content_len(lexical)?;
    let payload_len = ANY_URI_IDENTITY_PREFIX
        .len()
        .checked_add(content_len)
        .and_then(|value| value.checked_add(3))
        .ok_or_else(|| EncodedValidationError::resource("anyURI identity length overflowed"))?;
    budget.claim_owned(payload_len)?;
    let payload = serde_json::to_vec(&("any-uri-v1", lexical))
        .map_err(|_| EncodedValidationError::invariant("anyURI identity encoding failed"))?;
    if payload.len() != payload_len {
        return Err(EncodedValidationError::invariant(
            "anyURI identity length disagrees with canonical JSON",
        ));
    }
    prefixed_data_identity_key(&payload, budget)
}

fn date_time_data_identity_key(
    lexical: &str,
    require_timezone: bool,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<u8>> {
    let character_count = lexical.chars().count();
    PhaseBudget::count(
        character_count,
        budget.limits.max_literal_characters,
        "literal character count",
    )?;
    budget.claim_work(character_count)?;
    let selected = collapse_xml_whitespace(lexical, budget)?;
    let Some((date, time_and_zone)) = selected.split_once('T') else {
        return invalid_date_time();
    };
    if time_and_zone.contains('T') {
        return invalid_date_time();
    }
    let mut date_parts = date.rsplitn(3, '-');
    let Some(day_text) = date_parts.next() else {
        return invalid_date_time();
    };
    let Some(month_text) = date_parts.next() else {
        return invalid_date_time();
    };
    let Some(year_text) = date_parts.next() else {
        return invalid_date_time();
    };
    let year = parse_date_time_year(year_text, budget)?;
    let Some(month) = fixed_decimal_u8(month_text) else {
        return invalid_date_time();
    };
    let Some(day) = fixed_decimal_u8(day_text) else {
        return invalid_date_time();
    };
    if !(1..=12).contains(&month) || day == 0 || day > days_in_month(&year, month) {
        return invalid_date_time();
    }
    let (time, offset) = parse_date_time_zone(time_and_zone, require_timezone)?;
    let mut time_parts = time.split(':');
    let Some(hour_text) = time_parts.next() else {
        return invalid_date_time();
    };
    let Some(minute_text) = time_parts.next() else {
        return invalid_date_time();
    };
    let Some(second_and_fraction) = time_parts.next() else {
        return invalid_date_time();
    };
    if time_parts.next().is_some() {
        return invalid_date_time();
    }
    let Some(hour) = fixed_decimal_u8(hour_text) else {
        return invalid_date_time();
    };
    let Some(minute) = fixed_decimal_u8(minute_text) else {
        return invalid_date_time();
    };
    let (second_text, fraction_text) = second_and_fraction
        .split_once('.')
        .map_or((second_and_fraction, None), |(second, fraction)| {
            (second, Some(fraction))
        });
    if fraction_text.is_some_and(|fraction| fraction.is_empty() || fraction.contains('.')) {
        return invalid_date_time();
    }
    let Some(second) = fixed_decimal_u8(second_text) else {
        return invalid_date_time();
    };
    if minute > 59
        || second > 59
        || hour > 24
        || (hour == 24
            && (minute != 0
                || second != 0
                || fraction_text.is_some_and(|value| !value.bytes().all(|byte| byte == b'0'))))
    {
        return invalid_date_time();
    }
    let (fraction_numerator, fraction_denominator) = if let Some(fraction) = fraction_text {
        if !fraction.bytes().all(|byte| byte.is_ascii_digit()) {
            return invalid_date_time();
        }
        PhaseBudget::count(
            fraction.len(),
            budget.limits.max_numeric_digits,
            "date/time fraction digit count",
        )?;
        let temporary_bytes = fraction.len().checked_mul(4).ok_or_else(|| {
            EncodedValidationError::resource("date/time fraction size overflowed")
        })?;
        budget.claim_owned(temporary_bytes)?;
        let numerator = BigInt::parse_bytes(fraction.as_bytes(), 10).ok_or_else(|| {
            EncodedValidationError::invariant("date/time fraction could not be decoded")
        })?;
        let exponent = u32::try_from(fraction.len())
            .map_err(|_| EncodedValidationError::resource("date/time fraction exceeds u32"))?;
        (numerator, BigInt::from(10_u8).pow(exponent))
    } else {
        (BigInt::from(0_u8), BigInt::from(1_u8))
    };
    let days = days_before_year(&year) + days_before_month(&year, month) + BigInt::from(day - 1);
    let whole_seconds = days * BigInt::from(86_400_u32)
        + BigInt::from(hour) * BigInt::from(3_600_u16)
        + BigInt::from(minute) * BigInt::from(60_u8)
        + BigInt::from(second);
    let local_numerator = whole_seconds * &fraction_denominator + fraction_numerator;
    date_time_identity_key(local_numerator, fraction_denominator, offset, budget)
}

fn parse_date_time_year(value: &str, budget: &mut PhaseBudget) -> EncodedResult<BigInt> {
    let (negative, digits) = value
        .strip_prefix('-')
        .map_or((false, value), |digits| (true, digits));
    if digits.len() < 4
        || !digits.bytes().all(|byte| byte.is_ascii_digit())
        || (digits.starts_with('0') && digits.len() != 4)
    {
        return invalid_date_time();
    }
    PhaseBudget::count(
        digits.len(),
        budget.limits.max_numeric_digits,
        "date/time year digit count",
    )?;
    let temporary_bytes = digits
        .len()
        .checked_mul(4)
        .and_then(|length| length.checked_add(1))
        .ok_or_else(|| EncodedValidationError::resource("date/time year size overflowed"))?;
    budget.claim_owned(temporary_bytes)?;
    let magnitude = BigInt::parse_bytes(digits.as_bytes(), 10)
        .ok_or_else(|| EncodedValidationError::invariant("date/time year could not be decoded"))?;
    if negative && magnitude.sign() == Sign::NoSign {
        return invalid_date_time();
    }
    Ok(if negative { -magnitude } else { magnitude })
}

fn parse_date_time_zone(value: &str, require_timezone: bool) -> EncodedResult<(&str, Option<i16>)> {
    if let Some(time) = value.strip_suffix('Z') {
        return Ok((time, Some(0)));
    }
    if value.len() >= 6 {
        let split = value.len() - 6;
        let zone = &value.as_bytes()[split..];
        if value.is_char_boundary(split) && matches!(zone[0], b'+' | b'-') && zone[3] == b':' {
            let Some(hour) = fixed_decimal_u8_bytes(&zone[1..3]) else {
                return invalid_date_time();
            };
            let Some(minute) = fixed_decimal_u8_bytes(&zone[4..6]) else {
                return invalid_date_time();
            };
            if hour > 14 || minute > 59 || (hour == 14 && minute != 0) {
                return invalid_date_time();
            }
            let magnitude = i16::from(hour) * 60 + i16::from(minute);
            let offset = if zone[0] == b'-' {
                -magnitude
            } else {
                magnitude
            };
            return Ok((&value[..split], Some(offset)));
        }
    }
    if require_timezone {
        invalid_date_time()
    } else {
        Ok((value, None))
    }
}

fn fixed_decimal_u8(value: &str) -> Option<u8> {
    fixed_decimal_u8_bytes(value.as_bytes())
}

fn fixed_decimal_u8_bytes(value: &[u8]) -> Option<u8> {
    if value.len() != 2 || !value.iter().all(u8::is_ascii_digit) {
        return None;
    }
    Some((value[0] - b'0') * 10 + value[1] - b'0')
}

fn days_before_year(year: &BigInt) -> BigInt {
    let prior = year - BigInt::from(1_u8);
    BigInt::from(365_u16) * &prior + prior.div_floor(&BigInt::from(4_u8))
        - prior.div_floor(&BigInt::from(100_u8))
        + prior.div_floor(&BigInt::from(400_u16))
}

fn days_before_month(year: &BigInt, month: u8) -> BigInt {
    (1..month)
        .map(|selected| BigInt::from(days_in_month(year, selected)))
        .sum()
}

fn days_in_month(year: &BigInt, month: u8) -> u8 {
    if month == 2 {
        if year.mod_floor(&BigInt::from(4_u8)).is_zero()
            && (!year.mod_floor(&BigInt::from(100_u8)).is_zero()
                || year.mod_floor(&BigInt::from(400_u16)).is_zero())
        {
            29
        } else {
            28
        }
    } else if matches!(month, 4 | 6 | 9 | 11) {
        30
    } else {
        31
    }
}

fn date_time_identity_key(
    numerator: BigInt,
    denominator: BigInt,
    offset: Option<i16>,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<u8>> {
    let divisor = numerator.gcd(&denominator);
    let reduced_numerator = numerator / &divisor;
    let reduced_denominator = denominator / divisor;
    let numerator_token = bigint_token(&reduced_numerator, budget)?;
    let denominator_token = bigint_token(&reduced_denominator, budget)?;
    let payload = serde_json::to_vec(&(
        "date-time-identity-v1",
        numerator_token.as_str(),
        denominator_token.as_str(),
        offset,
        false,
    ))
    .map_err(|_| EncodedValidationError::invariant("date/time identity encoding failed"))?;
    budget.claim_owned(payload.len())?;
    prefixed_data_identity_key(&payload, budget)
}

fn invalid_date_time<T>() -> EncodedResult<T> {
    Err(EncodedValidationError::invariant(
        "date/time literal is outside its datatype lexical space",
    ))
}

fn rational_bigint_data_identity_key(
    numerator: BigInt,
    denominator: BigInt,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<u8>> {
    if denominator.sign() != Sign::Plus {
        return Err(EncodedValidationError::invariant(
            "numeric identity denominator must be positive",
        ));
    }
    let divisor = numerator.gcd(&denominator);
    let reduced_numerator = numerator / &divisor;
    let reduced_denominator = denominator / divisor;
    let numerator_token = bigint_token(&reduced_numerator, budget)?;
    let denominator_token = bigint_token(&reduced_denominator, budget)?;
    rational_data_identity_key(&numerator_token, &denominator_token, budget)
}

fn bigint_token(value: &BigInt, budget: &mut PhaseBudget) -> EncodedResult<String> {
    let sign = if value.sign() == Sign::Minus {
        '-'
    } else {
        '+'
    };
    let magnitude = value.magnitude().to_str_radix(16);
    let token_len = magnitude
        .len()
        .checked_add(1)
        .ok_or_else(|| EncodedValidationError::resource("integer token length overflowed"))?;
    budget.claim_owned(token_len)?;
    let mut token = String::new();
    token
        .try_reserve_exact(token_len)
        .map_err(|_| EncodedValidationError::resource("integer token allocation failed"))?;
    token.push(sign);
    token.push_str(&magnitude);
    Ok(token)
}

fn rational_data_identity_key(
    numerator: &str,
    denominator: &str,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<u8>> {
    const PREFIX: &[u8] = b"[\"numeric-rational-hex-v1\",\"";
    const SEPARATOR: &[u8] = b"\",\"";
    const SUFFIX: &[u8] = b"\"]";
    let payload_len = PREFIX
        .len()
        .checked_add(numerator.len())
        .and_then(|value| value.checked_add(SEPARATOR.len()))
        .and_then(|value| value.checked_add(denominator.len()))
        .and_then(|value| value.checked_add(SUFFIX.len()))
        .ok_or_else(|| EncodedValidationError::resource("numeric identity length overflowed"))?;
    let key_len = DATA_IDENTITY_PREFIX
        .len()
        .checked_add(payload_len)
        .ok_or_else(|| EncodedValidationError::resource("data identity key length overflowed"))?;
    budget.claim_work(payload_len)?;
    budget.claim_owned(key_len)?;
    let mut key = Vec::new();
    key.try_reserve_exact(key_len)
        .map_err(|_| EncodedValidationError::resource("data identity key allocation failed"))?;
    key.extend_from_slice(DATA_IDENTITY_PREFIX);
    key.extend_from_slice(PREFIX);
    key.extend_from_slice(numerator.as_bytes());
    key.extend_from_slice(SEPARATOR);
    key.extend_from_slice(denominator.as_bytes());
    key.extend_from_slice(SUFFIX);
    Ok(key)
}

fn string_data_identity_key(
    lexical: &str,
    datatype_iri: &str,
    language: Option<&str>,
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<Vec<u8>>> {
    let kind = if datatype_iri == RDF_PLAIN_LITERAL_IRI {
        StringDatatypeKind::PlainLiteral
    } else if let Some(local) = datatype_iri.strip_prefix(XSD_NAMESPACE) {
        match local {
            "string" => StringDatatypeKind::String,
            "normalizedString" => StringDatatypeKind::NormalizedString,
            "token" => StringDatatypeKind::Token,
            "language" => StringDatatypeKind::Language,
            "Name" => StringDatatypeKind::Name,
            "NCName" => StringDatatypeKind::NcName,
            "NMTOKEN" => StringDatatypeKind::NmToken,
            _ => return Ok(None),
        }
    } else {
        return Ok(None);
    };
    let character_count = lexical.chars().count();
    PhaseBudget::count(
        character_count,
        budget.limits.max_literal_characters,
        "literal character count",
    )?;
    budget.claim_work(character_count)?;
    let transformed = transform_string_literal(lexical, kind, budget)?;
    if !transformed.chars().all(is_xml_character) || !valid_string_lexical(&transformed, kind) {
        return Err(EncodedValidationError::invariant(
            "string literal is outside its datatype lexical space",
        ));
    }
    let identity_language = if kind == StringDatatypeKind::PlainLiteral {
        language
    } else {
        None
    };
    let payload_len = string_identity_payload_len(&transformed, identity_language)?;
    budget.claim_owned(payload_len)?;
    let payload = serde_json::to_vec(&("plain-string-v1", transformed.as_str(), identity_language))
        .map_err(|_| EncodedValidationError::invariant("string data identity encoding failed"))?;
    if payload.len() != payload_len {
        return Err(EncodedValidationError::invariant(
            "string data identity length disagrees with canonical JSON",
        ));
    }
    prefixed_data_identity_key(&payload, budget).map(Some)
}

fn prefixed_data_identity_key(payload: &[u8], budget: &mut PhaseBudget) -> EncodedResult<Vec<u8>> {
    let key_len = DATA_IDENTITY_PREFIX
        .len()
        .checked_add(payload.len())
        .ok_or_else(|| EncodedValidationError::resource("data identity key length overflowed"))?;
    budget.claim_work(payload.len())?;
    budget.claim_owned(key_len)?;
    let mut key = Vec::new();
    key.try_reserve_exact(key_len)
        .map_err(|_| EncodedValidationError::resource("data identity key allocation failed"))?;
    key.extend_from_slice(DATA_IDENTITY_PREFIX);
    key.extend_from_slice(payload);
    Ok(key)
}

fn string_identity_payload_len(text: &str, language: Option<&str>) -> EncodedResult<usize> {
    const PREFIX: &str = "[\"plain-string-v1\",";
    let text_len = json_string_content_len(text)?;
    let language_len = language.map_or(Ok(4_usize), |value| {
        json_string_content_len(value).and_then(|length| {
            length
                .checked_add(2)
                .ok_or_else(|| EncodedValidationError::resource("language JSON length overflowed"))
        })
    })?;
    PREFIX
        .len()
        .checked_add(2)
        .and_then(|value| value.checked_add(text_len))
        .and_then(|value| value.checked_add(1))
        .and_then(|value| value.checked_add(language_len))
        .and_then(|value| value.checked_add(1))
        .ok_or_else(|| EncodedValidationError::resource("string identity JSON length overflowed"))
}

fn json_string_content_len(value: &str) -> EncodedResult<usize> {
    value.chars().try_fold(0_usize, |length, character| {
        let encoded = match character {
            '"' | '\\' | '\u{0008}' | '\t' | '\n' | '\u{000c}' | '\r' => 2,
            value if u32::from(value) <= 0x1f => 6,
            value => value.len_utf8(),
        };
        length.checked_add(encoded).ok_or_else(|| {
            EncodedValidationError::resource("JSON string content length overflowed")
        })
    })
}

fn transform_string_literal(
    lexical: &str,
    kind: StringDatatypeKind,
    budget: &mut PhaseBudget,
) -> EncodedResult<String> {
    budget.claim_owned(lexical.len())?;
    let mut transformed = String::new();
    transformed.try_reserve_exact(lexical.len()).map_err(|_| {
        EncodedValidationError::resource("string literal transformation allocation failed")
    })?;
    match kind {
        StringDatatypeKind::PlainLiteral | StringDatatypeKind::String => {
            transformed.push_str(lexical);
        }
        StringDatatypeKind::NormalizedString => {
            for character in lexical.chars() {
                transformed.push(if matches!(character, '\t' | '\n' | '\r') {
                    ' '
                } else {
                    character
                });
            }
        }
        StringDatatypeKind::Token
        | StringDatatypeKind::Language
        | StringDatatypeKind::Name
        | StringDatatypeKind::NcName
        | StringDatatypeKind::NmToken => {
            let mut pending_space = false;
            for character in lexical.chars() {
                if matches!(character, ' ' | '\t' | '\n' | '\r') {
                    pending_space = !transformed.is_empty();
                } else {
                    if pending_space {
                        transformed.push(' ');
                        pending_space = false;
                    }
                    transformed.push(character);
                }
            }
        }
    }
    Ok(transformed)
}

fn valid_string_lexical(value: &str, kind: StringDatatypeKind) -> bool {
    match kind {
        StringDatatypeKind::PlainLiteral
        | StringDatatypeKind::String
        | StringDatatypeKind::NormalizedString
        | StringDatatypeKind::Token => true,
        StringDatatypeKind::Language => valid_language_lexical(value),
        StringDatatypeKind::Name => {
            let mut characters = value.chars();
            characters
                .next()
                .is_some_and(|first| is_name_start(first, true))
                && characters.all(|character| is_name_character(character, true))
        }
        StringDatatypeKind::NcName => {
            let mut characters = value.chars();
            characters
                .next()
                .is_some_and(|first| is_name_start(first, false))
                && characters.all(|character| is_name_character(character, false))
        }
        StringDatatypeKind::NmToken => {
            !value.is_empty()
                && value
                    .chars()
                    .all(|character| is_name_character(character, true))
        }
    }
}

fn valid_language_lexical(value: &str) -> bool {
    let mut parts = value.split('-');
    let Some(first) = parts.next() else {
        return false;
    };
    (1..=8).contains(&first.len())
        && first.bytes().all(|byte| byte.is_ascii_alphabetic())
        && parts.all(|part| {
            (1..=8).contains(&part.len()) && part.bytes().all(|byte| byte.is_ascii_alphanumeric())
        })
}

const fn is_xml_character(value: char) -> bool {
    let codepoint = value as u32;
    matches!(codepoint, 0x9 | 0xa | 0xd)
        || (codepoint >= 0x20 && codepoint <= 0xd7ff)
        || (codepoint >= 0xe000 && codepoint <= 0xfffd)
        || (codepoint >= 0x1_0000 && codepoint <= 0x10_ffff)
}

const fn is_name_start(value: char, allow_colon: bool) -> bool {
    let codepoint = value as u32;
    (allow_colon && value == ':')
        || value == '_'
        || (codepoint >= 0x41 && codepoint <= 0x5a)
        || (codepoint >= 0x61 && codepoint <= 0x7a)
        || (codepoint >= 0xc0 && codepoint <= 0xd6)
        || (codepoint >= 0xd8 && codepoint <= 0xf6)
        || (codepoint >= 0xf8 && codepoint <= 0x2ff)
        || (codepoint >= 0x370 && codepoint <= 0x37d)
        || (codepoint >= 0x37f && codepoint <= 0x1fff)
        || (codepoint >= 0x200c && codepoint <= 0x200d)
        || (codepoint >= 0x2070 && codepoint <= 0x218f)
        || (codepoint >= 0x2c00 && codepoint <= 0x2fef)
        || (codepoint >= 0x3001 && codepoint <= 0xd7ff)
        || (codepoint >= 0xf900 && codepoint <= 0xfdcf)
        || (codepoint >= 0xfdf0 && codepoint <= 0xfffd)
        || (codepoint >= 0x1_0000 && codepoint <= 0xe_ffff)
}

const fn is_name_character(value: char, allow_colon: bool) -> bool {
    let codepoint = value as u32;
    is_name_start(value, allow_colon)
        || matches!(value, '-' | '.')
        || (codepoint >= 0x30 && codepoint <= 0x39)
        || codepoint == 0xb7
        || (codepoint >= 0x300 && codepoint <= 0x36f)
        || (codepoint >= 0x203f && codepoint <= 0x2040)
}

fn data_value_display(key: &[u8], budget: &mut PhaseBudget) -> EncodedResult<String> {
    const DIGEST_HEX_BYTES: usize = 64;
    budget.claim_work(key.len())?;
    budget.claim_owned(DIGEST_HEX_BYTES)?;
    let digest = crate::model::hex(&Sha256::digest(key));
    let display_len = "data-value:"
        .len()
        .checked_add(digest.len())
        .ok_or_else(|| EncodedValidationError::resource("data-value display length overflowed"))?;
    budget.claim_owned(display_len)?;
    let mut display = String::new();
    display
        .try_reserve_exact(display_len)
        .map_err(|_| EncodedValidationError::resource("data-value display allocation failed"))?;
    display.push_str("data-value:");
    display.push_str(&digest);
    Ok(display)
}

fn text_field<B: ByteSource>(
    model: &ValidatedModel<B>,
    index: usize,
    name: &'static str,
    budget: &mut PhaseBudget,
) -> EncodedResult<String> {
    let component = required_component(model.field(index)?, name)?;
    let ComponentValue::Scalar(value) = model.resolve(component)? else {
        return Err(EncodedValidationError::invariant(format!(
            "{name} is not a scalar"
        )));
    };
    text_scalar(value, name, budget)
}

fn text_scalar<B: ByteSource>(
    value: ScalarRef<B>,
    name: &'static str,
    budget: &mut PhaseBudget,
) -> EncodedResult<String> {
    if value.kind() != ComponentKind::Text {
        return Err(EncodedValidationError::invariant(format!(
            "{name} is not text"
        )));
    }
    budget.claim_work(value.len())?;
    budget.claim_owned(value.len())?;
    let mut bytes = Vec::new();
    bytes
        .try_reserve_exact(value.len())
        .map_err(|_| EncodedValidationError::resource(format!("{name} allocation failed")))?;
    for index in 0..value.len() {
        bytes.push(value.byte(index).ok_or_else(|| {
            EncodedValidationError::invariant(format!("{name} byte disappeared"))
        })?);
    }
    String::from_utf8(bytes)
        .map_err(|_| EncodedValidationError::invariant(format!("{name} is no longer UTF-8")))
}

fn python_string_repr(value: &str, budget: &mut PhaseBudget) -> EncodedResult<String> {
    let quote = if value.contains('\'') && !value.contains('"') {
        '"'
    } else {
        '\''
    };
    let encoded_len = value.chars().try_fold(2_usize, |length, character| {
        length
            .checked_add(python_repr_character_len(character, quote))
            .ok_or_else(|| EncodedValidationError::resource("literal repr length overflowed"))
    })?;
    budget.claim_owned(encoded_len)?;
    let mut encoded = String::new();
    encoded
        .try_reserve_exact(encoded_len)
        .map_err(|_| EncodedValidationError::resource("literal repr allocation failed"))?;
    encoded.push(quote);
    for character in value.chars() {
        push_python_repr_character(&mut encoded, character, quote);
    }
    encoded.push(quote);
    Ok(encoded)
}

fn python_repr_character_len(value: char, quote: char) -> usize {
    match value {
        '\\' | '\n' | '\r' | '\t' => 2,
        character if character == quote => 2,
        '\'' | '"' => 1,
        character if debug_keeps_character(character) => character.len_utf8(),
        character if u32::from(character) <= 0xff => 4,
        character if u32::from(character) <= 0xffff => 6,
        _ => 10,
    }
}

fn debug_keeps_character(value: char) -> bool {
    let mut escaped = value.escape_debug();
    escaped.next() == Some(value) && escaped.next().is_none()
}

fn push_python_repr_character(target: &mut String, value: char, quote: char) {
    match value {
        '\\' => target.push_str("\\\\"),
        '\n' => target.push_str("\\n"),
        '\r' => target.push_str("\\r"),
        '\t' => target.push_str("\\t"),
        character if character == quote => {
            target.push('\\');
            target.push(character);
        }
        character @ ('\'' | '"') => target.push(character),
        character if debug_keeps_character(character) => target.push(character),
        character => push_python_hex_escape(target, u32::from(character)),
    }
}

fn push_python_hex_escape(target: &mut String, value: u32) {
    let (prefix, digits) = if value <= 0xff {
        ("\\x", 2)
    } else if value <= 0xffff {
        ("\\u", 4)
    } else {
        ("\\U", 8)
    };
    target.push_str(prefix);
    for shift in (0..digits).rev() {
        let nibble = u8::try_from((value >> (shift * 4)) & 0x0f).unwrap_or(0);
        target.push(char::from(if nibble < 10 {
            b'0' + nibble
        } else {
            b'a' + nibble - 10
        }));
    }
}

fn declared_individual_ids(
    symbols: &SymbolPhase,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<u32>> {
    let mut identifiers = Vec::new();
    for entity in &symbols.declared_entities {
        budget.claim_work(1)?;
        if entity.kind != "named_individual" {
            continue;
        }
        budget.claim_owned(size_of::<u32>())?;
        identifiers.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("declared-individual signature allocation failed")
        })?;
        identifiers.push(entity.entity_id);
    }
    budget.claim_work(sort_work(identifiers.len()))?;
    identifiers.sort_unstable();
    identifiers.dedup();
    Ok(identifiers)
}

fn individual_signature<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    declared_individual_ids: &[u32],
    include_object_assertions: bool,
    include_data_assertions: bool,
    scope_maps: &[AnonymousScopeMap],
    budget: &mut PhaseBudget,
) -> EncodedResult<(DecodedSymbolDomain, Vec<IndividualSignatureBinding>)> {
    let mut pending = Vec::<PendingIndividualSymbol>::new();
    for entity in &symbols.entity_domain.values {
        budget.claim_work(1)?;
        if !entity.display.starts_with(NAMED_INDIVIDUAL_PREFIX) {
            continue;
        }
        let following = pending.len().checked_add(1).ok_or_else(|| {
            EncodedValidationError::resource("individual symbol count overflowed")
        })?;
        PhaseBudget::count(
            following,
            budget.limits.max_individual_symbols,
            "individual symbol count",
        )?;
        budget.claim_owned(size_of::<PendingIndividualSymbol>())?;
        budget.claim_owned(size_of::<DecodedSymbolValue>())?;
        budget.claim_owned(entity.key.len())?;
        budget.claim_owned(entity.display.len())?;
        pending
            .try_reserve(1)
            .map_err(|_| EncodedValidationError::resource("individual symbol allocation failed"))?;
        pending.push(PendingIndividualSymbol {
            value: DecodedSymbolValue {
                identifier: 0,
                key: entity.key.clone(),
                display: entity.display.clone(),
                generated: entity.generated,
                query_local: entity.query_local,
            },
            entity: Some((
                entity.identifier,
                declared_individual_ids
                    .binary_search(&entity.identifier)
                    .is_ok(),
            )),
        });
    }

    let mut anonymous_nodes = Vec::<NodeId>::new();
    for root in &symbols.roots {
        budget.claim_work(1)?;
        let positions: &[usize] = match root.handler {
            RootHandler::ClassAssertion => &[1],
            RootHandler::ObjectPropertyAssertion if include_object_assertions => &[1, 2],
            RootHandler::DataPropertyAssertion if include_data_assertions => &[1],
            _ => continue,
        };
        let root_node = model.node(root.node)?;
        for position in positions {
            let individual = node_field(
                model,
                root_node,
                *position,
                "anonymous-individual assertion operand",
            )?;
            if model.node(individual)?.tag() != ANONYMOUS_INDIVIDUAL_TAG {
                continue;
            }
            budget.claim_owned(size_of::<NodeId>())?;
            anonymous_nodes.try_reserve(1).map_err(|_| {
                EncodedValidationError::resource(
                    "anonymous-individual node selection allocation failed",
                )
            })?;
            anonymous_nodes.push(individual);
        }
    }
    budget.claim_work(sort_work(anonymous_nodes.len()))?;
    anonymous_nodes.sort_unstable();
    anonymous_nodes.dedup();
    for identifier in anonymous_nodes {
        budget.claim_work(1)?;
        if !symbols.semantic_node_is_reachable(identifier) {
            continue;
        }
        let following = pending.len().checked_add(1).ok_or_else(|| {
            EncodedValidationError::resource("individual symbol count overflowed")
        })?;
        PhaseBudget::count(
            following,
            budget.limits.max_individual_symbols,
            "individual symbol count",
        )?;
        let node = model.node(identifier)?;
        let key = canonical::canonical_node_key(model, identifier, scope_maps, budget)?;
        let display = anonymous_individual_display(model, node, scope_maps, budget)?;
        budget.claim_owned(size_of::<PendingIndividualSymbol>())?;
        budget.claim_owned(size_of::<DecodedSymbolValue>())?;
        pending
            .try_reserve(1)
            .map_err(|_| EncodedValidationError::resource("individual symbol allocation failed"))?;
        pending.push(PendingIndividualSymbol {
            value: DecodedSymbolValue {
                identifier: 0,
                key,
                display,
                generated: false,
                query_local: false,
            },
            entity: None,
        });
    }

    budget.claim_work(sort_work(pending.len()))?;
    pending.sort_by(|left, right| left.value.key.cmp(&right.value.key));
    let mut values = Vec::<DecodedSymbolValue>::new();
    let mut bindings = Vec::new();
    values.try_reserve_exact(pending.len()).map_err(|_| {
        EncodedValidationError::resource("individual symbol result allocation failed")
    })?;
    bindings
        .try_reserve_exact(pending.len())
        .map_err(|_| EncodedValidationError::resource("individual signature allocation failed"))?;
    for mut candidate in pending {
        if let Some(previous) = values.last() {
            if previous.key == candidate.value.key {
                if previous.display != candidate.value.display
                    || previous.generated != candidate.value.generated
                    || previous.query_local != candidate.value.query_local
                    || candidate.entity.is_some()
                {
                    return Err(EncodedValidationError::invariant(
                        "individual symbol key has conflicting metadata",
                    ));
                }
                continue;
            }
        }
        let individual_id = u32::try_from(values.len())
            .map_err(|_| EncodedValidationError::resource("individual symbol ID exceeds u32"))?;
        candidate.value.identifier = individual_id;
        if let Some((entity_id, declared)) = candidate.entity {
            budget.claim_owned(size_of::<IndividualSignatureBinding>())?;
            bindings.push(IndividualSignatureBinding {
                individual_id,
                entity_id,
                declared,
            });
        }
        values.push(candidate.value);
    }
    Ok((
        DecodedSymbolDomain {
            kind: SymbolKind::Individual,
            values,
        },
        bindings,
    ))
}

fn anonymous_individual_display<B: ByteSource>(
    model: &ValidatedModel<B>,
    node: NodeRef,
    scope_maps: &[AnonymousScopeMap],
    budget: &mut PhaseBudget,
) -> EncodedResult<String> {
    const SCOPE_BYTES: usize = 32;
    if node.tag() != ANONYMOUS_INDIVIDUAL_TAG || node.field_count() != 2 {
        return Err(EncodedValidationError::invariant(
            "anonymous individual no longer has schema-1 shape",
        ));
    }
    let scope_component = required_component(
        model.field(node.fields().start)?,
        "anonymous-individual scope",
    )?;
    let ComponentValue::Scalar(scope) = model.resolve(scope_component)? else {
        return Err(EncodedValidationError::invariant(
            "anonymous-individual scope is not scalar",
        ));
    };
    if scope.kind() != ComponentKind::Bytes || scope.len() != SCOPE_BYTES {
        return Err(EncodedValidationError::invariant(
            "anonymous-individual scope no longer has bytes32 shape",
        ));
    }
    let local_field = node.fields().start.checked_add(1).ok_or_else(|| {
        EncodedValidationError::invariant("anonymous-individual local-key field overflowed")
    })?;
    let local_component =
        required_component(model.field(local_field)?, "anonymous-individual local key")?;
    let ComponentValue::Scalar(local) = model.resolve(local_component)? else {
        return Err(EncodedValidationError::invariant(
            "anonymous-individual local key is not scalar",
        ));
    };
    if local.kind() != ComponentKind::Bytes || local.is_empty() {
        return Err(EncodedValidationError::invariant(
            "anonymous-individual local key no longer has nonempty bytes shape",
        ));
    }
    let mut source_scope = [0_u8; SCOPE_BYTES];
    for (index, byte) in source_scope.iter_mut().enumerate() {
        *byte = scope.byte(index).ok_or_else(|| {
            EncodedValidationError::invariant("anonymous-individual scope byte disappeared")
        })?;
    }
    let mapped_scope = canonical::remap_anonymous_scope(source_scope, scope_maps, budget)?;
    let display_len = ANONYMOUS_INDIVIDUAL_PREFIX
        .len()
        .checked_add(SCOPE_BYTES * 2)
        .and_then(|value| value.checked_add(1))
        .and_then(|value| value.checked_add(local.len().checked_mul(2)?))
        .ok_or_else(|| {
            EncodedValidationError::resource("anonymous-individual display length overflowed")
        })?;
    budget.claim_work(SCOPE_BYTES.checked_add(local.len()).ok_or_else(|| {
        EncodedValidationError::resource("anonymous-individual display work overflowed")
    })?)?;
    budget.claim_owned(display_len)?;
    let mut display = String::new();
    display.try_reserve_exact(display_len).map_err(|_| {
        EncodedValidationError::resource("anonymous-individual display allocation failed")
    })?;
    display.push_str(ANONYMOUS_INDIVIDUAL_PREFIX);
    append_hex_bytes(&mut display, &mapped_scope);
    display.push(':');
    append_hex_scalar(&mut display, local)?;
    Ok(display)
}

fn append_hex_bytes(target: &mut String, bytes: &[u8]) {
    for byte in bytes {
        target.push(char::from(HEX_DIGITS[usize::from(byte >> 4)]));
        target.push(char::from(HEX_DIGITS[usize::from(byte & 0x0f)]));
    }
}

fn append_hex_scalar<B: ByteSource>(
    target: &mut String,
    scalar: ScalarRef<B>,
) -> EncodedResult<()> {
    for index in 0..scalar.len() {
        let byte = scalar.byte(index).ok_or_else(|| {
            EncodedValidationError::invariant("anonymous-individual local-key byte disappeared")
        })?;
        target.push(char::from(HEX_DIGITS[usize::from(byte >> 4)]));
        target.push(char::from(HEX_DIGITS[usize::from(byte & 0x0f)]));
    }
    Ok(())
}

fn class_id_by_display(domain: &DecodedSymbolDomain, display: &str) -> EncodedResult<u32> {
    domain
        .values
        .iter()
        .find(|value| value.display == display)
        .map(|value| value.identifier)
        .ok_or_else(|| {
            EncodedValidationError::invariant(
                "named-class signature is missing a required built-in class",
            )
        })
}

fn data_range_id_by_display(domain: &DecodedSymbolDomain, display: &str) -> EncodedResult<u32> {
    domain
        .values
        .iter()
        .find(|value| value.display == display)
        .map(|value| value.identifier)
        .ok_or_else(|| {
            EncodedValidationError::invariant(
                "data-range signature is missing the universal data range",
            )
        })
}

fn named_subclass<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    class_domain: &DecodedSymbolDomain,
    signature: &[ClassSignatureBinding],
    root: NodeId,
    scope_maps: &[AnonymousScopeMap],
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<RawEdge>> {
    let node = model.node(root)?;
    if node.tag() != SUBCLASS_TAG || node.field_count() != 3 {
        return Err(EncodedValidationError::invariant(
            "subclass root no longer has schema-1 shape",
        ));
    }
    let sub_class_node = node_field(model, node, 0, "subclass antecedent")?;
    let Some(sub_selection) = atomic_class_selection(model, symbols, sub_class_node, budget)?
    else {
        return Ok(None);
    };
    let super_class_node = node_field(model, node, 1, "subclass consequent")?;
    let Some(super_selection) = atomic_class_selection(model, symbols, super_class_node, budget)?
    else {
        return Ok(None);
    };
    if atomic_class_selection_is_trivial(
        model,
        symbols,
        sub_selection,
        super_selection,
        scope_maps,
        budget,
    )? {
        return Ok(Some(RawEdge {
            sub_class: class_id_by_display(class_domain, NOTHING_DISPLAY)?,
            sub_negative: false,
            super_class: class_id_by_display(class_domain, THING_DISPLAY)?,
            super_negative: false,
            provenance: source_axiom_digest(model, root, scope_maps, budget)?,
        }));
    }
    let Some((sub_class, sub_negative)) = atomic_class_expression_literal(
        model,
        symbols,
        class_domain,
        signature,
        sub_class_node,
        scope_maps,
        budget,
    )?
    else {
        return Ok(None);
    };
    let Some((super_class, super_negative)) = atomic_class_expression_literal(
        model,
        symbols,
        class_domain,
        signature,
        super_class_node,
        scope_maps,
        budget,
    )?
    else {
        return Ok(None);
    };
    let provenance = source_axiom_digest(model, root, scope_maps, budget)?;
    Ok(Some(RawEdge {
        sub_class,
        sub_negative,
        super_class,
        super_negative,
        provenance,
    }))
}

fn named_equivalent_classes<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    class_domain: &DecodedSymbolDomain,
    signature: &[ClassSignatureBinding],
    root: NodeId,
    scope_maps: &[AnonymousScopeMap],
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<Vec<RawEdge>>> {
    let node = model.node(root)?;
    if node.tag() != EQUIVALENT_CLASSES_TAG || node.field_count() != 2 {
        return Err(EncodedValidationError::invariant(
            "equivalent-classes root no longer has schema-1 shape",
        ));
    }
    let expressions_component = required_component(
        model.field(node.fields().start)?,
        "equivalent-classes expressions",
    )?;
    let ComponentValue::Collection(expressions) = model.resolve(expressions_component)? else {
        return Err(EncodedValidationError::invariant(
            "equivalent-classes expressions did not resolve to a collection",
        ));
    };
    for item_index in expressions.items() {
        budget.claim_work(1)?;
        let item = required_component(model.item(item_index)?, "equivalent-classes member")?;
        let ComponentValue::Node(identifier) = model.resolve(item)? else {
            return Err(EncodedValidationError::invariant(
                "equivalent-classes member did not resolve to a node",
            ));
        };
        if atomic_class_selection(model, symbols, identifier, budget)?.is_none() {
            return Ok(None);
        }
    }
    let mut classes = Vec::new();
    budget.claim_owned(
        expressions
            .len()
            .checked_mul(size_of::<(u32, bool)>())
            .ok_or_else(|| {
                EncodedValidationError::resource("equivalent-classes member allocation overflowed")
            })?,
    )?;
    classes.try_reserve_exact(expressions.len()).map_err(|_| {
        EncodedValidationError::resource("equivalent-classes member allocation failed")
    })?;
    for item_index in expressions.items() {
        budget.claim_work(1)?;
        let item = required_component(model.item(item_index)?, "equivalent-classes member")?;
        let ComponentValue::Node(identifier) = model.resolve(item)? else {
            return Err(EncodedValidationError::invariant(
                "equivalent-classes member did not resolve to a node",
            ));
        };
        let Some(class_literal) = atomic_class_expression_literal(
            model,
            symbols,
            class_domain,
            signature,
            identifier,
            scope_maps,
            budget,
        )?
        else {
            return Ok(None);
        };
        classes.push(class_literal);
    }
    if classes.len() < 2 {
        return Err(EncodedValidationError::invariant(
            "equivalent-classes root has fewer than two members",
        ));
    }
    let provenance = source_axiom_digest(model, root, scope_maps, budget)?;
    let mut edges = Vec::new();
    budget.claim_owned(
        classes
            .len()
            .checked_mul(size_of::<RawEdge>())
            .ok_or_else(|| {
                EncodedValidationError::resource("equivalent-classes edge allocation overflowed")
            })?,
    )?;
    edges.try_reserve_exact(classes.len()).map_err(|_| {
        EncodedValidationError::resource("equivalent-classes edge allocation failed")
    })?;
    for (index, (sub_class, sub_negative)) in classes.iter().copied().enumerate() {
        let following = index.checked_add(1).ok_or_else(|| {
            EncodedValidationError::resource("equivalent-classes edge index overflowed")
        })?;
        let (super_class, super_negative) = classes[following % classes.len()];
        edges.push(RawEdge {
            sub_class,
            sub_negative,
            super_class,
            super_negative,
            provenance,
        });
    }
    Ok(Some(edges))
}

#[allow(clippy::too_many_arguments)]
fn named_disjoint_classes<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    class_domain: &DecodedSymbolDomain,
    signature: &[ClassSignatureBinding],
    root: NodeId,
    thing: u32,
    nothing: u32,
    scope_maps: &[AnonymousScopeMap],
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<NamedDisjointOutput>> {
    let node = model.node(root)?;
    if node.tag() != DISJOINT_CLASSES_TAG || node.field_count() != 2 {
        return Err(EncodedValidationError::invariant(
            "disjoint-classes root no longer has schema-1 shape",
        ));
    }
    let expressions_component = required_component(
        model.field(node.fields().start)?,
        "disjoint-classes expressions",
    )?;
    let ComponentValue::Collection(expressions) = model.resolve(expressions_component)? else {
        return Err(EncodedValidationError::invariant(
            "disjoint-classes expressions did not resolve to a collection",
        ));
    };
    let mut live_count = 0_usize;
    for item_index in expressions.items() {
        budget.claim_work(1)?;
        let item = required_component(model.item(item_index)?, "disjoint-classes member")?;
        let ComponentValue::Node(identifier) = model.resolve(item)? else {
            return Err(EncodedValidationError::invariant(
                "disjoint-classes member did not resolve to a node",
            ));
        };
        let Some(selection) = atomic_class_selection(model, symbols, identifier, budget)? else {
            return Ok(None);
        };
        if matches!(selection.source, AtomicClassSource::Entity(entity_id)
            if !selection.negative
                && class_entity_display(symbols, entity_id)? == NOTHING_DISPLAY)
        {
            continue;
        }
        live_count = live_count.checked_add(1).ok_or_else(|| {
            EncodedValidationError::resource("disjoint-class live-member count overflowed")
        })?;
    }
    if live_count < 2 {
        return Ok(Some(NamedDisjointOutput {
            edges: Vec::new(),
            disjoint: None,
            provenance: source_axiom_digest(model, root, scope_maps, budget)?,
        }));
    }
    let mut classes = Vec::new();
    budget.claim_owned(
        expressions
            .len()
            .checked_mul(size_of::<(ClassLiteral, NodeId)>())
            .ok_or_else(|| {
                EncodedValidationError::resource("disjoint-classes member allocation overflowed")
            })?,
    )?;
    classes.try_reserve_exact(expressions.len()).map_err(|_| {
        EncodedValidationError::resource("disjoint-classes member allocation failed")
    })?;
    for item_index in expressions.items() {
        budget.claim_work(1)?;
        let item = required_component(model.item(item_index)?, "disjoint-classes member")?;
        let ComponentValue::Node(identifier) = model.resolve(item)? else {
            return Err(EncodedValidationError::invariant(
                "disjoint-classes member did not resolve to a node",
            ));
        };
        let Some((class_id, negative)) = atomic_class_expression_literal(
            model,
            symbols,
            class_domain,
            signature,
            identifier,
            scope_maps,
            budget,
        )?
        else {
            return Ok(None);
        };
        classes.push((ClassLiteral { class_id, negative }, identifier));
    }
    if classes.len() < 2 {
        return Err(EncodedValidationError::invariant(
            "disjoint-classes root has fewer than two members",
        ));
    }
    let provenance = source_axiom_digest(model, root, scope_maps, budget)?;
    let mut live = Vec::new();
    budget.claim_owned(
        classes
            .len()
            .checked_mul(size_of::<(ClassLiteral, NodeId)>())
            .ok_or_else(|| {
                EncodedValidationError::resource("live disjoint-class allocation overflowed")
            })?,
    )?;
    live.try_reserve_exact(classes.len())
        .map_err(|_| EncodedValidationError::resource("live disjoint-class allocation failed"))?;
    live.extend(
        classes
            .into_iter()
            .filter(|(literal, _)| literal.negative || literal.class_id != nothing),
    );

    if live
        .iter()
        .any(|(literal, _)| !literal.negative && literal.class_id == thing)
    {
        let mut edges = Vec::new();
        let edge_count = live.len().saturating_sub(1);
        budget.claim_owned(
            edge_count
                .checked_mul(size_of::<RawEdge>())
                .ok_or_else(|| {
                    EncodedValidationError::resource(
                        "top disjoint-class edge allocation overflowed",
                    )
                })?,
        )?;
        edges.try_reserve_exact(edge_count).map_err(|_| {
            EncodedValidationError::resource("top disjoint-class edge allocation failed")
        })?;
        for (literal, _) in live {
            if literal.negative || literal.class_id != thing {
                edges.push(RawEdge {
                    sub_class: literal.class_id,
                    sub_negative: literal.negative,
                    super_class: nothing,
                    super_negative: false,
                    provenance,
                });
            }
        }
        return Ok(Some(NamedDisjointOutput {
            edges,
            disjoint: None,
            provenance,
        }));
    }

    let disjoint = if live.len() >= 2 {
        let guard_digest = disjoint_guard_digest_nodes(model, &live, scope_maps, budget)?;
        let mut literals = Vec::new();
        budget.claim_owned(
            live.len()
                .checked_mul(size_of::<ClassLiteral>())
                .ok_or_else(|| {
                    EncodedValidationError::resource("disjoint-class literal allocation overflowed")
                })?,
        )?;
        literals.try_reserve_exact(live.len()).map_err(|_| {
            EncodedValidationError::resource("disjoint-class literal allocation failed")
        })?;
        literals.extend(live.into_iter().map(|(literal, _)| literal));
        Some(RawDisjoint {
            classes: literals,
            guard_digest,
            provenance,
        })
    } else {
        None
    };
    Ok(Some(NamedDisjointOutput {
        edges: Vec::new(),
        disjoint,
        provenance,
    }))
}

#[allow(clippy::too_many_arguments)]
fn named_object_constraint<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    object_roles: &ObjectRolePhase,
    class_domain: &DecodedSymbolDomain,
    class_signature: &[ClassSignatureBinding],
    handler: RootHandler,
    root: NodeId,
    scope_maps: &[AnonymousScopeMap],
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<RawObjectConstraint>> {
    let (tag, kind, name) = match handler {
        RootHandler::ObjectPropertyDomain => (
            OBJECT_PROPERTY_DOMAIN_TAG,
            ObjectConstraintKind::Domain,
            "object-property domain",
        ),
        RootHandler::ObjectPropertyRange => (
            OBJECT_PROPERTY_RANGE_TAG,
            ObjectConstraintKind::Range,
            "object-property range",
        ),
        _ => {
            return Err(EncodedValidationError::invariant(
                "named object constraint received a different root handler",
            ));
        }
    };
    let node = model.node(root)?;
    if node.tag() != tag || node.field_count() != 3 {
        return Err(EncodedValidationError::invariant(format!(
            "{name} root no longer has schema-1 shape"
        )));
    }
    let property = node_field(model, node, 0, "object-property constraint role")?;
    let role_id = named_object_role_id(model, symbols, object_roles, property, budget)?;
    let Some(class) = atomic_class_field(
        model,
        symbols,
        class_domain,
        class_signature,
        node,
        1,
        scope_maps,
        budget,
    )?
    else {
        return Ok(None);
    };
    let provenance = source_axiom_digest(model, root, scope_maps, budget)?;
    Ok(Some(RawObjectConstraint {
        kind,
        role_id,
        class,
        provenance,
    }))
}

#[allow(clippy::too_many_arguments)]
fn named_object_characteristic<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    object_roles: &ObjectRolePhase,
    handler: RootHandler,
    root: NodeId,
    scope_maps: &[AnonymousScopeMap],
    budget: &mut PhaseBudget,
) -> EncodedResult<RawObjectCharacteristic> {
    let (tag, kind, name) = match handler {
        RootHandler::FunctionalObjectProperty => (
            FUNCTIONAL_OBJECT_PROPERTY_TAG,
            ObjectCharacteristicKind::Functional,
            "functional-object-property",
        ),
        RootHandler::InverseFunctionalObjectProperty => (
            INVERSE_FUNCTIONAL_OBJECT_PROPERTY_TAG,
            ObjectCharacteristicKind::InverseFunctional,
            "inverse-functional-object-property",
        ),
        RootHandler::ReflexiveObjectProperty => (
            REFLEXIVE_OBJECT_PROPERTY_TAG,
            ObjectCharacteristicKind::Reflexive,
            "reflexive-object-property",
        ),
        _ => {
            return Err(EncodedValidationError::invariant(
                "named object characteristic received a different root handler",
            ));
        }
    };
    let node = model.node(root)?;
    if node.tag() != tag || node.field_count() != 2 {
        return Err(EncodedValidationError::invariant(format!(
            "{name} root no longer has schema-1 shape"
        )));
    }
    let property = node_field(model, node, 0, "object-property characteristic role")?;
    let role_id = named_object_role_id(model, symbols, object_roles, property, budget)?;
    let provenance = source_axiom_digest(model, root, scope_maps, budget)?;
    Ok(RawObjectCharacteristic {
        kind,
        role_id,
        provenance,
    })
}

#[allow(clippy::too_many_arguments)]
fn named_data_domain<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    data_roles: &DataRolePhase,
    class_domain: &DecodedSymbolDomain,
    class_signature: &[ClassSignatureBinding],
    root: NodeId,
    scope_maps: &[AnonymousScopeMap],
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<RawDataDomain>> {
    let node = model.node(root)?;
    if node.tag() != DATA_PROPERTY_DOMAIN_TAG || node.field_count() != 3 {
        return Err(EncodedValidationError::invariant(
            "data-property domain root no longer has schema-1 shape",
        ));
    }
    let property = node_field(model, node, 0, "data-property domain role")?;
    let role_id = named_data_role_id(model, symbols, data_roles, property, budget)?;
    let Some(class) = atomic_class_field(
        model,
        symbols,
        class_domain,
        class_signature,
        node,
        1,
        scope_maps,
        budget,
    )?
    else {
        return Ok(None);
    };
    let provenance = source_axiom_digest(model, root, scope_maps, budget)?;
    Ok(Some(RawDataDomain {
        role_id,
        class,
        provenance,
    }))
}

#[allow(clippy::too_many_arguments)]
fn named_data_range<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    data_roles: &DataRolePhase,
    data_range_domain: &DecodedSymbolDomain,
    root: NodeId,
    scope_maps: &[AnonymousScopeMap],
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<RawDataRange>> {
    let node = model.node(root)?;
    if node.tag() != DATA_PROPERTY_RANGE_TAG || node.field_count() != 3 {
        return Err(EncodedValidationError::invariant(
            "data-property range root no longer has schema-1 shape",
        ));
    }
    let property = node_field(model, node, 0, "data-property range role")?;
    let role_id = named_data_role_id(model, symbols, data_roles, property, budget)?;
    let range_node = node_field(model, node, 1, "data-property range value")?;
    let Some(range) = atomic_data_range_literal(
        model,
        symbols,
        data_range_domain,
        range_node,
        scope_maps,
        budget,
    )?
    else {
        return Ok(None);
    };
    let provenance = source_axiom_digest(model, root, scope_maps, budget)?;
    Ok(Some(RawDataRange {
        role_id,
        range,
        provenance,
    }))
}

fn atomic_data_range_literal<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    data_range_domain: &DecodedSymbolDomain,
    range: NodeId,
    scope_maps: &[AnonymousScopeMap],
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<DataRangeLiteral>> {
    let Some((base, negative)) = atomic_data_range_base(model, symbols, range)? else {
        return Ok(None);
    };
    let range_id = if model.node(base)?.tag() == ENTITY_TAG {
        named_data_range_id(model, symbols, data_range_domain, base, budget)?.ok_or_else(|| {
            EncodedValidationError::invariant(
                "atomic datatype is absent from the named data-range domain",
            )
        })?
    } else {
        let key = canonical::canonical_node_key(model, base, scope_maps, budget)?;
        budget.claim_work(binary_search_work(data_range_domain.values.len()))?;
        let index = data_range_domain
            .values
            .binary_search_by(|value| value.key.cmp(&key))
            .map_err(|_| {
                EncodedValidationError::invariant(
                    "atomic expression is absent from the data-range domain",
                )
            })?;
        u32::try_from(index).map_err(|_| {
            EncodedValidationError::resource("atomic data-range symbol ID exceeds u32")
        })?
    };
    Ok(Some(DataRangeLiteral { range_id, negative }))
}

fn named_data_range_id<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    data_range_domain: &DecodedSymbolDomain,
    range: NodeId,
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<u32>> {
    let range_node = model.node(range)?;
    if range_node.tag() != ENTITY_TAG {
        return Ok(None);
    }
    let entity_id = symbols.entity_symbol_for_node(range).ok_or_else(|| {
        EncodedValidationError::invariant(
            "data-property range datatype is absent from the entity seed",
        )
    })?;
    let entity = symbols
        .entity_domain
        .values
        .get(usize::try_from(entity_id).map_err(|_| {
            EncodedValidationError::invariant("data-property range entity ID exceeds usize")
        })?)
        .ok_or_else(|| {
            EncodedValidationError::invariant("data-property range entity ID is dangling")
        })?;
    if !entity.display.starts_with("datatype:") {
        return Err(EncodedValidationError::invariant(
            "data-property range entity is not a datatype",
        ));
    }
    budget.claim_work(binary_search_work(data_range_domain.values.len()))?;
    let range_id = data_range_domain
        .values
        .binary_search_by(|value| value.key.cmp(&entity.key))
        .map_err(|_| {
            EncodedValidationError::invariant(
                "data-property range datatype is absent from the data-range domain",
            )
        })?;
    let range_id = u32::try_from(range_id).map_err(|_| {
        EncodedValidationError::resource("data-property range symbol ID exceeds u32")
    })?;
    Ok(Some(range_id))
}

#[allow(clippy::too_many_arguments)]
fn named_datatype_definition<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    data_range_domain: &DecodedSymbolDomain,
    root: NodeId,
    scope_maps: &[AnonymousScopeMap],
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<RawDatatypeDefinition>> {
    let node = model.node(root)?;
    if node.tag() != DATATYPE_DEFINITION_TAG || node.field_count() != 3 {
        return Err(EncodedValidationError::invariant(
            "datatype-definition root no longer has schema-1 shape",
        ));
    }
    let datatype = node_field(model, node, 0, "defined datatype")?;
    let left_range_id = named_data_range_id(model, symbols, data_range_domain, datatype, budget)?
        .ok_or_else(|| {
        EncodedValidationError::invariant("datatype-definition subject is not a named datatype")
    })?;
    let left_range = DataRangeLiteral {
        range_id: left_range_id,
        negative: false,
    };
    let data_range = node_field(model, node, 1, "datatype defining range")?;
    let Some(right_range) = atomic_data_range_literal(
        model,
        symbols,
        data_range_domain,
        data_range,
        scope_maps,
        budget,
    )?
    else {
        return Ok(None);
    };
    let (left_range, right_range) = if left_range <= right_range {
        (left_range, right_range)
    } else {
        (right_range, left_range)
    };
    let provenance = source_axiom_digest(model, root, scope_maps, budget)?;
    Ok(Some(RawDatatypeDefinition {
        left_range,
        right_range,
        provenance,
    }))
}

#[allow(clippy::too_many_arguments)]
fn named_key<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    object_roles: Option<&ObjectRolePhase>,
    data_roles: Option<&DataRolePhase>,
    class_domain: &DecodedSymbolDomain,
    class_signature: &[ClassSignatureBinding],
    root: NodeId,
    scope_maps: &[AnonymousScopeMap],
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<RawKey>> {
    let node = model.node(root)?;
    if node.tag() != HAS_KEY_TAG || node.field_count() != 4 {
        return Err(EncodedValidationError::invariant(
            "has-key root no longer has schema-1 shape",
        ));
    }
    let Some(class) = atomic_class_field(
        model,
        symbols,
        class_domain,
        class_signature,
        node,
        0,
        scope_maps,
        budget,
    )?
    else {
        return Ok(None);
    };
    let object_component = required_component(
        model.field(node.fields().start + 1)?,
        "has-key object properties",
    )?;
    let ComponentValue::Collection(object_properties) = model.resolve(object_component)? else {
        return Err(EncodedValidationError::invariant(
            "has-key object properties did not resolve to a collection",
        ));
    };
    let data_component = required_component(
        model.field(node.fields().start + 2)?,
        "has-key data properties",
    )?;
    let ComponentValue::Collection(data_properties) = model.resolve(data_component)? else {
        return Err(EncodedValidationError::invariant(
            "has-key data properties did not resolve to a collection",
        ));
    };
    if object_properties.is_empty() && data_properties.is_empty() {
        return Err(EncodedValidationError::invariant(
            "has-key root no longer contains a property",
        ));
    }
    if !object_properties.is_empty() && object_roles.is_none() {
        return Ok(None);
    }
    if !data_properties.is_empty() && data_roles.is_none() {
        return Ok(None);
    }

    let role_count = object_properties
        .len()
        .checked_add(data_properties.len())
        .ok_or_else(|| EncodedValidationError::resource("has-key role count overflowed"))?;
    budget.claim_owned(
        role_count.checked_mul(size_of::<u32>()).ok_or_else(|| {
            EncodedValidationError::resource("has-key role allocation overflowed")
        })?,
    )?;
    let mut object_role_ids = Vec::new();
    object_role_ids
        .try_reserve_exact(object_properties.len())
        .map_err(|_| EncodedValidationError::resource("has-key object-role allocation failed"))?;
    for item_index in object_properties.items() {
        budget.claim_work(1)?;
        let item = required_component(model.item(item_index)?, "has-key object property")?;
        let ComponentValue::Node(identifier) = model.resolve(item)? else {
            return Err(EncodedValidationError::invariant(
                "has-key object property did not resolve to a node",
            ));
        };
        let roles = object_roles.ok_or_else(|| {
            EncodedValidationError::invariant("has-key object role domain disappeared")
        })?;
        object_role_ids.push(named_object_role_id(
            model, symbols, roles, identifier, budget,
        )?);
    }
    let mut data_role_ids = Vec::new();
    data_role_ids
        .try_reserve_exact(data_properties.len())
        .map_err(|_| EncodedValidationError::resource("has-key data-role allocation failed"))?;
    for item_index in data_properties.items() {
        budget.claim_work(1)?;
        let item = required_component(model.item(item_index)?, "has-key data property")?;
        let ComponentValue::Node(identifier) = model.resolve(item)? else {
            return Err(EncodedValidationError::invariant(
                "has-key data property did not resolve to a node",
            ));
        };
        let roles = data_roles.ok_or_else(|| {
            EncodedValidationError::invariant("has-key data role domain disappeared")
        })?;
        data_role_ids.push(named_data_role_id(
            model, symbols, roles, identifier, budget,
        )?);
    }
    budget.claim_work(
        sort_work(object_role_ids.len()).saturating_add(sort_work(data_role_ids.len())),
    )?;
    object_role_ids.sort_unstable();
    object_role_ids.dedup();
    data_role_ids.sort_unstable();
    data_role_ids.dedup();
    let provenance = source_axiom_digest(model, root, scope_maps, budget)?;
    Ok(Some(RawKey {
        class,
        object_role_ids,
        data_role_ids,
        provenance,
    }))
}

fn named_data_functionality<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    data_roles: &DataRolePhase,
    root: NodeId,
    scope_maps: &[AnonymousScopeMap],
    budget: &mut PhaseBudget,
) -> EncodedResult<RawDataFunctionality> {
    let node = model.node(root)?;
    if node.tag() != FUNCTIONAL_DATA_PROPERTY_TAG || node.field_count() != 2 {
        return Err(EncodedValidationError::invariant(
            "functional-data-property root no longer has schema-1 shape",
        ));
    }
    let property = node_field(model, node, 0, "functional data-property role")?;
    let role_id = named_data_role_id(model, symbols, data_roles, property, budget)?;
    let provenance = source_axiom_digest(model, root, scope_maps, budget)?;
    Ok(RawDataFunctionality {
        role_id,
        provenance,
    })
}

fn named_data_role_id<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    data_roles: &DataRolePhase,
    identifier: NodeId,
    budget: &mut PhaseBudget,
) -> EncodedResult<u32> {
    let node = model.node(identifier)?;
    if node.tag() != ENTITY_TAG {
        return Err(EncodedValidationError::invariant(
            "data-property domain has an unsupported role expression",
        ));
    }
    let entity_id = symbols.entity_symbol_for_node(identifier).ok_or_else(|| {
        EncodedValidationError::invariant(
            "data-property domain role is absent from the entity seed",
        )
    })?;
    let entity = symbols
        .entity_domain
        .values
        .get(usize::try_from(entity_id).map_err(|_| {
            EncodedValidationError::invariant("data-property entity ID exceeds usize")
        })?)
        .ok_or_else(|| EncodedValidationError::invariant("data-property entity ID is dangling"))?;
    if !entity.display.starts_with(DATA_PROPERTY_PREFIX) {
        return Err(EncodedValidationError::invariant(
            "data-property domain resolved to a different entity kind",
        ));
    }
    data_role_id_by_key(&data_roles.data_property_domain, &entity.key, budget)
}

fn named_object_role_id<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    object_roles: &ObjectRolePhase,
    identifier: NodeId,
    budget: &mut PhaseBudget,
) -> EncodedResult<u32> {
    let node = model.node(identifier)?;
    if node.tag() == ENTITY_TAG {
        let entity_id = symbols.entity_symbol_for_node(identifier).ok_or_else(|| {
            EncodedValidationError::invariant(
                "object-property constraint role is absent from the entity seed",
            )
        })?;
        let entity = symbols
            .entity_domain
            .values
            .get(usize::try_from(entity_id).map_err(|_| {
                EncodedValidationError::invariant("object-property entity ID exceeds usize")
            })?)
            .ok_or_else(|| {
                EncodedValidationError::invariant("object-property entity ID is dangling")
            })?;
        if !entity.display.starts_with(OBJECT_PROPERTY_PREFIX) {
            return Err(EncodedValidationError::invariant(
                "object-property constraint resolved to a different entity kind",
            ));
        }
        return role_id_by_key(&object_roles.object_role_domain, &entity.key, budget);
    }
    if node.tag() != OBJECT_INVERSE_OF_TAG || node.field_count() != 1 {
        return Err(EncodedValidationError::invariant(
            "object-property constraint has an unsupported role expression",
        ));
    }
    let property = node_field(model, node, 0, "inverse object-property constraint role")?;
    let forward = named_object_role_id(model, symbols, object_roles, property, budget)?;
    object_roles
        .inverse_role_ids
        .get(usize::try_from(forward).map_err(|_| {
            EncodedValidationError::invariant("object-property role ID exceeds usize")
        })?)
        .copied()
        .ok_or_else(|| EncodedValidationError::invariant("object-property role ID is dangling"))
}

fn node_field<B: ByteSource>(
    model: &ValidatedModel<B>,
    node: NodeRef,
    offset: usize,
    name: &'static str,
) -> EncodedResult<NodeId> {
    let field_index = node
        .fields()
        .start
        .checked_add(offset)
        .ok_or_else(|| EncodedValidationError::invariant(format!("{name} index overflowed")))?;
    let component = required_component(model.field(field_index)?, name)?;
    let ComponentValue::Node(identifier) = model.resolve(component)? else {
        return Err(EncodedValidationError::invariant(format!(
            "{name} is not a node"
        )));
    };
    Ok(identifier)
}

fn role_id_by_key(
    domain: &DecodedSymbolDomain,
    key: &[u8],
    budget: &mut PhaseBudget,
) -> EncodedResult<u32> {
    if domain.kind != SymbolKind::ObjectRole {
        return Err(EncodedValidationError::invariant(
            "object-property constraint received a non-role domain",
        ));
    }
    budget.claim_work(binary_search_work(domain.values.len()))?;
    let index = domain
        .values
        .binary_search_by(|candidate| candidate.key.as_slice().cmp(key))
        .map_err(|_| EncodedValidationError::invariant("object-property role key is absent"))?;
    u32::try_from(index)
        .map_err(|_| EncodedValidationError::resource("object-property role ID exceeds u32"))
}

fn data_role_id_by_key(
    domain: &DecodedSymbolDomain,
    key: &[u8],
    budget: &mut PhaseBudget,
) -> EncodedResult<u32> {
    if domain.kind != SymbolKind::DataProperty {
        return Err(EncodedValidationError::invariant(
            "data-property domain received a non-data-property domain",
        ));
    }
    budget.claim_work(binary_search_work(domain.values.len()))?;
    let index = domain
        .values
        .binary_search_by(|candidate| candidate.key.as_slice().cmp(key))
        .map_err(|_| EncodedValidationError::invariant("data-property role key is absent"))?;
    u32::try_from(index)
        .map_err(|_| EncodedValidationError::resource("data-property role ID exceeds u32"))
}

fn named_same_individuals<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    signature: &[IndividualSignatureBinding],
    root: NodeId,
    scope_maps: &[AnonymousScopeMap],
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<Vec<RawEqualityFact>>> {
    let node = model.node(root)?;
    if node.tag() != SAME_INDIVIDUAL_TAG || node.field_count() != 2 {
        return Err(EncodedValidationError::invariant(
            "same-individual root no longer has schema-1 shape",
        ));
    }
    let individuals_component = required_component(
        model.field(node.fields().start)?,
        "same-individual individuals",
    )?;
    let ComponentValue::Collection(individuals_view) = model.resolve(individuals_component)? else {
        return Err(EncodedValidationError::invariant(
            "same-individual members did not resolve to a collection",
        ));
    };
    let mut individuals = Vec::new();
    budget.claim_owned(
        individuals_view
            .len()
            .checked_mul(size_of::<u32>())
            .ok_or_else(|| {
                EncodedValidationError::resource("same-individual member allocation overflowed")
            })?,
    )?;
    individuals
        .try_reserve_exact(individuals_view.len())
        .map_err(|_| {
            EncodedValidationError::resource("same-individual member allocation failed")
        })?;
    for item_index in individuals_view.items() {
        budget.claim_work(1)?;
        let item = required_component(model.item(item_index)?, "same-individual member")?;
        let ComponentValue::Node(identifier) = model.resolve(item)? else {
            return Err(EncodedValidationError::invariant(
                "same-individual member did not resolve to a node",
            ));
        };
        let Some(individual_id) = named_individual_id(model, symbols, signature, identifier)?
        else {
            return Ok(None);
        };
        individuals.push(individual_id);
    }
    if individuals.len() < 2 {
        return Err(EncodedValidationError::invariant(
            "same-individual root has fewer than two members",
        ));
    }
    if !individuals.windows(2).all(|pair| pair[0] < pair[1]) {
        return Err(EncodedValidationError::invariant(
            "same-individual members are not in canonical set order",
        ));
    }
    let statement_sha256 = annotation_stripped_axiom_digest(model, root, budget)?;
    let provenance = source_axiom_digest(model, root, scope_maps, budget)?;
    let equality_count = individuals.len().checked_sub(1).ok_or_else(|| {
        EncodedValidationError::invariant("same-individual equality count underflowed")
    })?;
    let mut equalities = Vec::new();
    budget.claim_owned(
        equality_count
            .checked_mul(size_of::<RawEqualityFact>())
            .ok_or_else(|| {
                EncodedValidationError::resource("same-individual fact allocation overflowed")
            })?,
    )?;
    equalities
        .try_reserve_exact(equality_count)
        .map_err(|_| EncodedValidationError::resource("same-individual fact allocation failed"))?;
    let first = individuals[0];
    for individual in individuals.into_iter().skip(1) {
        equalities.push(RawEqualityFact {
            left_individual: first,
            right_individual: individual,
            statement_sha256,
            provenance,
        });
    }
    Ok(Some(equalities))
}

fn named_different_individuals<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    signature: &[IndividualSignatureBinding],
    root: NodeId,
    scope_maps: &[AnonymousScopeMap],
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<Vec<RawInequalityFact>>> {
    let node = model.node(root)?;
    if node.tag() != DIFFERENT_INDIVIDUALS_TAG || node.field_count() != 2 {
        return Err(EncodedValidationError::invariant(
            "different-individuals root no longer has schema-1 shape",
        ));
    }
    let individuals_component = required_component(
        model.field(node.fields().start)?,
        "different-individuals individuals",
    )?;
    let ComponentValue::Collection(individuals_view) = model.resolve(individuals_component)? else {
        return Err(EncodedValidationError::invariant(
            "different-individuals members did not resolve to a collection",
        ));
    };
    let mut individuals = Vec::new();
    budget.claim_owned(
        individuals_view
            .len()
            .checked_mul(size_of::<u32>())
            .ok_or_else(|| {
                EncodedValidationError::resource(
                    "different-individuals member allocation overflowed",
                )
            })?,
    )?;
    individuals
        .try_reserve_exact(individuals_view.len())
        .map_err(|_| {
            EncodedValidationError::resource("different-individuals member allocation failed")
        })?;
    for item_index in individuals_view.items() {
        budget.claim_work(1)?;
        let item = required_component(model.item(item_index)?, "different-individuals member")?;
        let ComponentValue::Node(identifier) = model.resolve(item)? else {
            return Err(EncodedValidationError::invariant(
                "different-individuals member did not resolve to a node",
            ));
        };
        let Some(individual_id) = named_individual_id(model, symbols, signature, identifier)?
        else {
            return Ok(None);
        };
        individuals.push(individual_id);
    }
    if individuals.len() < 2 {
        return Err(EncodedValidationError::invariant(
            "different-individuals root has fewer than two members",
        ));
    }
    if !individuals.windows(2).all(|pair| pair[0] < pair[1]) {
        return Err(EncodedValidationError::invariant(
            "different-individuals members are not in canonical set order",
        ));
    }
    let statement_sha256 = annotation_stripped_axiom_digest(model, root, budget)?;
    let provenance = source_axiom_digest(model, root, scope_maps, budget)?;
    let lesser = individuals.len().checked_sub(1).ok_or_else(|| {
        EncodedValidationError::invariant("different-individuals pair count underflowed")
    })?;
    let (left_factor, right_factor) = if individuals.len() % 2 == 0 {
        (individuals.len() / 2, lesser)
    } else {
        (individuals.len(), lesser / 2)
    };
    let pair_count = left_factor.checked_mul(right_factor).ok_or_else(|| {
        EncodedValidationError::resource("different-individuals pair count overflowed")
    })?;
    PhaseBudget::count(
        pair_count,
        budget.limits.max_facts,
        "different-individual fact count",
    )?;
    budget.claim_work(pair_count)?;
    budget.claim_owned(
        pair_count
            .checked_mul(size_of::<RawInequalityFact>())
            .ok_or_else(|| {
                EncodedValidationError::resource("different-individuals fact allocation overflowed")
            })?,
    )?;
    let mut inequalities = Vec::new();
    inequalities.try_reserve_exact(pair_count).map_err(|_| {
        EncodedValidationError::resource("different-individuals fact allocation failed")
    })?;
    for left_index in 0..lesser {
        let left_individual = individuals[left_index];
        for right_individual in individuals.iter().copied().skip(left_index + 1) {
            inequalities.push(RawInequalityFact {
                left_individual,
                right_individual,
                statement_sha256,
                provenance,
            });
        }
    }
    if inequalities.len() != pair_count {
        return Err(EncodedValidationError::invariant(
            "different-individuals expansion disagrees with its exact pair bound",
        ));
    }
    Ok(Some(inequalities))
}

#[allow(clippy::too_many_arguments)]
fn named_class_assertion<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    class_domain: &DecodedSymbolDomain,
    class_signature: &[ClassSignatureBinding],
    individual_domain: &DecodedSymbolDomain,
    individual_signature: &[IndividualSignatureBinding],
    root: NodeId,
    scope_maps: &[AnonymousScopeMap],
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<RawFact>> {
    let node = model.node(root)?;
    if node.tag() != CLASS_ASSERTION_TAG || node.field_count() != 3 {
        return Err(EncodedValidationError::invariant(
            "class-assertion root no longer has schema-1 shape",
        ));
    }
    let Some((class_id, negative)) = class_assertion_literal(
        model,
        symbols,
        class_domain,
        class_signature,
        node,
        scope_maps,
        budget,
    )?
    else {
        return Ok(None);
    };
    let Some(individual_id) = individual_field(
        model,
        symbols,
        individual_domain,
        individual_signature,
        node,
        1,
        true,
        scope_maps,
        budget,
    )?
    else {
        return Ok(None);
    };
    let provenance = source_axiom_digest(model, root, scope_maps, budget)?;
    Ok(Some(RawFact {
        class_id,
        individual_id,
        negative,
        provenance,
    }))
}

fn class_assertion_literal<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    class_domain: &DecodedSymbolDomain,
    signature: &[ClassSignatureBinding],
    assertion: NodeRef,
    scope_maps: &[AnonymousScopeMap],
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<(u32, bool)>> {
    let identifier = node_field(
        model,
        assertion,
        0,
        "class-assertion class-expression operand",
    )?;
    atomic_class_expression_literal(
        model,
        symbols,
        class_domain,
        signature,
        identifier,
        scope_maps,
        budget,
    )
}

#[allow(clippy::too_many_arguments)]
fn atomic_class_expression_literal<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    class_domain: &DecodedSymbolDomain,
    signature: &[ClassSignatureBinding],
    identifier: NodeId,
    scope_maps: &[AnonymousScopeMap],
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<(u32, bool)>> {
    let Some(selection) = atomic_class_selection(model, symbols, identifier, budget)? else {
        return Ok(None);
    };
    let class_id = match selection.source {
        AtomicClassSource::Entity(entity_id) => signature
            .binary_search_by_key(&entity_id, |binding| binding.entity_id)
            .ok()
            .map(|index| signature[index].class_expression_id)
            .ok_or_else(|| {
                EncodedValidationError::invariant(
                    "atomic class operand is absent from the class signature",
                )
            })?,
        AtomicClassSource::Nominal(base) => {
            let key = canonical::canonical_node_key(model, base, scope_maps, budget)?;
            budget.claim_work(binary_search_work(class_domain.values.len()))?;
            let class_index = class_domain
                .values
                .binary_search_by(|candidate| candidate.key.cmp(&key))
                .map_err(|_| {
                    EncodedValidationError::invariant(
                        "object nominal is absent from the class-expression domain",
                    )
                })?;
            u32::try_from(class_index)
                .map_err(|_| EncodedValidationError::resource("object nominal ID exceeds u32"))?
        }
    };
    Ok(Some((class_id, selection.negative)))
}

#[allow(clippy::too_many_arguments)]
fn named_object_assertion<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    object_roles: &ObjectRolePhase,
    individual_domain: &DecodedSymbolDomain,
    individual_signature: &[IndividualSignatureBinding],
    root: NodeId,
    expected_tag: u16,
    scope_maps: &[AnonymousScopeMap],
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<RawObjectFact>> {
    let node = model.node(root)?;
    if node.tag() != expected_tag || node.field_count() != 4 {
        return Err(EncodedValidationError::invariant(
            "object-property assertion root no longer has schema-1 shape",
        ));
    }
    let property = node_field(model, node, 0, "object-property assertion role")?;
    let (role_id, inverted) = named_assertion_role(model, symbols, object_roles, property, budget)?;
    let Some(mut source_individual) = individual_field(
        model,
        symbols,
        individual_domain,
        individual_signature,
        node,
        1,
        expected_tag == OBJECT_PROPERTY_ASSERTION_TAG,
        scope_maps,
        budget,
    )?
    else {
        return Ok(None);
    };
    let Some(mut target_individual) = individual_field(
        model,
        symbols,
        individual_domain,
        individual_signature,
        node,
        2,
        expected_tag == OBJECT_PROPERTY_ASSERTION_TAG,
        scope_maps,
        budget,
    )?
    else {
        return Ok(None);
    };
    if inverted {
        std::mem::swap(&mut source_individual, &mut target_individual);
    }
    let provenance = source_axiom_digest(model, root, scope_maps, budget)?;
    Ok(Some(RawObjectFact {
        role_id,
        source_individual,
        target_individual,
        provenance,
    }))
}

#[allow(clippy::too_many_arguments)]
fn named_data_assertion<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    data_roles: &DataRolePhase,
    individual_domain: &DecodedSymbolDomain,
    individual_signature: &[IndividualSignatureBinding],
    source_literal_domain: &DecodedSymbolDomain,
    source_data_identity_ids: &[Option<u32>],
    root: NodeId,
    expected_tag: u16,
    scope_maps: &[AnonymousScopeMap],
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<RawDataFact>> {
    let node = model.node(root)?;
    if node.tag() != expected_tag || node.field_count() != 4 {
        return Err(EncodedValidationError::invariant(
            "data-property assertion root no longer has schema-1 shape",
        ));
    }
    let property = node_field(model, node, 0, "data-property assertion role")?;
    let role_id = named_data_role_id(model, symbols, data_roles, property, budget)?;
    let Some(source_individual) = individual_field(
        model,
        symbols,
        individual_domain,
        individual_signature,
        node,
        1,
        expected_tag == DATA_PROPERTY_ASSERTION_TAG,
        scope_maps,
        budget,
    )?
    else {
        return Ok(None);
    };
    let literal = node_field(model, node, 2, "data-property assertion literal")?;
    let Some((source_literal_id, data_identity_id)) = source_data_ids(
        model,
        source_literal_domain,
        source_data_identity_ids,
        literal,
        budget,
    )?
    else {
        return Ok(None);
    };
    let provenance = source_axiom_digest(model, root, scope_maps, budget)?;
    Ok(Some(RawDataFact {
        role_id,
        source_individual,
        source_literal_id,
        data_identity_id,
        provenance,
    }))
}

fn source_data_ids<B: ByteSource>(
    model: &ValidatedModel<B>,
    source_literal_domain: &DecodedSymbolDomain,
    source_data_identity_ids: &[Option<u32>],
    literal: NodeId,
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<(u32, u32)>> {
    if source_literal_domain.kind != SymbolKind::SourceLiteral
        || source_data_identity_ids.len() != source_literal_domain.values.len()
    {
        return Err(EncodedValidationError::invariant(
            "source literal domain and data-identity mapping disagree",
        ));
    }
    if model.node(literal)?.tag() != LITERAL_TAG {
        return Err(EncodedValidationError::invariant(
            "data-property assertion value is not a literal",
        ));
    }
    let key = canonical::canonical_node_key(model, literal, &[], budget)?;
    budget.claim_work(binary_search_work(source_literal_domain.values.len()))?;
    let source_index = source_literal_domain
        .values
        .binary_search_by(|candidate| candidate.key.cmp(&key))
        .map_err(|_| {
            EncodedValidationError::invariant(
                "data-property assertion literal is absent from its source domain",
            )
        })?;
    let Some(data_identity_id) = source_data_identity_ids[source_index] else {
        return Ok(None);
    };
    let source_literal_id = u32::try_from(source_index)
        .map_err(|_| EncodedValidationError::resource("source-literal ID exceeds u32"))?;
    Ok(Some((source_literal_id, data_identity_id)))
}

fn named_assertion_role<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    object_roles: &ObjectRolePhase,
    identifier: NodeId,
    budget: &mut PhaseBudget,
) -> EncodedResult<(u32, bool)> {
    let node = model.node(identifier)?;
    if node.tag() == ENTITY_TAG {
        return named_object_role_id(model, symbols, object_roles, identifier, budget)
            .map(|role_id| (role_id, false));
    }
    if node.tag() != OBJECT_INVERSE_OF_TAG || node.field_count() != 1 {
        return Err(EncodedValidationError::invariant(
            "object-property assertion has an unsupported role expression",
        ));
    }
    let property = node_field(model, node, 0, "inverse object-property assertion role")?;
    let (role_id, inverted) = named_assertion_role(model, symbols, object_roles, property, budget)?;
    Ok((role_id, !inverted))
}

#[allow(clippy::too_many_arguments)]
fn atomic_class_field<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    class_domain: &DecodedSymbolDomain,
    signature: &[ClassSignatureBinding],
    node: NodeRef,
    relative_field: usize,
    scope_maps: &[AnonymousScopeMap],
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<ClassLiteral>> {
    let field_index = node
        .fields()
        .start
        .checked_add(relative_field)
        .ok_or_else(|| EncodedValidationError::invariant("class field index overflowed"))?;
    let component = required_component(model.field(field_index)?, "named-class field")?;
    let ComponentValue::Node(identifier) = model.resolve(component)? else {
        return Err(EncodedValidationError::invariant(
            "class-expression field did not resolve to a node",
        ));
    };
    Ok(atomic_class_expression_literal(
        model,
        symbols,
        class_domain,
        signature,
        identifier,
        scope_maps,
        budget,
    )?
    .map(|(class_id, negative)| ClassLiteral { class_id, negative }))
}

#[allow(clippy::too_many_arguments)]
fn individual_field<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    domain: &DecodedSymbolDomain,
    signature: &[IndividualSignatureBinding],
    node: NodeRef,
    relative_field: usize,
    allow_anonymous: bool,
    scope_maps: &[AnonymousScopeMap],
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<u32>> {
    let field_index = node
        .fields()
        .start
        .checked_add(relative_field)
        .ok_or_else(|| EncodedValidationError::invariant("individual field index overflowed"))?;
    let component = required_component(model.field(field_index)?, "individual field")?;
    let ComponentValue::Node(identifier) = model.resolve(component)? else {
        return Err(EncodedValidationError::invariant(
            "individual field did not resolve to a node",
        ));
    };
    if !allow_anonymous {
        return named_individual_id(model, symbols, signature, identifier);
    }
    individual_id(
        model, symbols, domain, signature, identifier, scope_maps, budget,
    )
}

fn individual_id<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    domain: &DecodedSymbolDomain,
    signature: &[IndividualSignatureBinding],
    identifier: NodeId,
    scope_maps: &[AnonymousScopeMap],
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<u32>> {
    let tag = model.node(identifier)?.tag();
    if tag == ENTITY_TAG {
        return named_individual_id(model, symbols, signature, identifier);
    }
    if tag != ANONYMOUS_INDIVIDUAL_TAG {
        return Ok(None);
    }
    if domain.kind != SymbolKind::Individual {
        return Err(EncodedValidationError::invariant(
            "individual lookup domain changed kind",
        ));
    }
    let key = canonical::canonical_node_key(model, identifier, scope_maps, budget)?;
    budget.claim_work(binary_search_work(domain.values.len()))?;
    let index = domain
        .values
        .binary_search_by(|candidate| candidate.key.cmp(&key))
        .map_err(|_| {
            EncodedValidationError::invariant(
                "anonymous individual is absent from its semantic symbol domain",
            )
        })?;
    Ok(Some(u32::try_from(index).map_err(|_| {
        EncodedValidationError::resource("individual symbol ID exceeds u32")
    })?))
}

fn named_individual_id<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    signature: &[IndividualSignatureBinding],
    identifier: NodeId,
) -> EncodedResult<Option<u32>> {
    if model.node(identifier)?.tag() != ENTITY_TAG {
        return Ok(None);
    }
    let entity_id = symbols.entity_symbol_for_node(identifier).ok_or_else(|| {
        EncodedValidationError::invariant(
            "named individual is absent from the reachable entity-node mapping",
        )
    })?;
    Ok(signature
        .binary_search_by_key(&entity_id, |binding| binding.entity_id)
        .ok()
        .map(|index| signature[index].individual_id))
}

fn retain_compiled_root(
    digests: &mut Vec<[u8; 32]>,
    compiled_roots: &mut usize,
    digest: [u8; 32],
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    *compiled_roots = compiled_roots.checked_add(1).ok_or_else(|| {
        EncodedValidationError::resource("named-class compiled-root count overflowed")
    })?;
    budget.claim_owned(size_of::<[u8; 32]>())?;
    digests.try_reserve(1).map_err(|_| {
        EncodedValidationError::resource("named-class compiled-root identity allocation failed")
    })?;
    digests.push(digest);
    Ok(())
}

fn retain_edge(
    edges: &mut Vec<RawEdge>,
    edge: RawEdge,
    thing: u32,
    nothing: u32,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    if (!edge.sub_negative && edge.sub_class == nothing)
        || (!edge.super_negative && edge.super_class == thing)
        || (edge.sub_class == edge.super_class && edge.sub_negative == edge.super_negative)
    {
        return Ok(());
    }
    budget.claim_owned(size_of::<RawEdge>())?;
    edges
        .try_reserve(1)
        .map_err(|_| EncodedValidationError::resource("named-class edge allocation failed"))?;
    edges.push(edge);
    Ok(())
}

fn normalize_edges(
    mut raw: Vec<RawEdge>,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<NormalizedEdge>> {
    budget.claim_work(sort_work(raw.len()))?;
    raw.sort_by_key(|edge| {
        (
            edge.sub_class,
            edge.sub_negative,
            edge.super_class,
            edge.super_negative,
            edge.provenance,
        )
    });
    let mut normalized = Vec::<NormalizedEdge>::new();
    for edge in raw {
        budget.claim_work(1)?;
        if let Some(previous) = normalized.last_mut() {
            if previous.sub_class == edge.sub_class
                && previous.sub_negative == edge.sub_negative
                && previous.super_class == edge.super_class
                && previous.super_negative == edge.super_negative
            {
                if previous.provenance.last() != Some(&edge.provenance) {
                    budget.claim_owned(size_of::<[u8; 32]>())?;
                    previous.provenance.try_reserve(1).map_err(|_| {
                        EncodedValidationError::resource(
                            "named-class edge provenance allocation failed",
                        )
                    })?;
                    previous.provenance.push(edge.provenance);
                }
                continue;
            }
        }
        budget.claim_owned(size_of::<NormalizedEdge>() + size_of::<[u8; 32]>())?;
        normalized.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("normalized named-class edge allocation failed")
        })?;
        let mut provenance = Vec::new();
        provenance.try_reserve_exact(1).map_err(|_| {
            EncodedValidationError::resource("named-class edge provenance allocation failed")
        })?;
        provenance.push(edge.provenance);
        normalized.push(NormalizedEdge {
            sub_class: edge.sub_class,
            sub_negative: edge.sub_negative,
            super_class: edge.super_class,
            super_negative: edge.super_negative,
            provenance,
        });
    }
    Ok(normalized)
}

fn normalize_disjoints(
    mut raw: Vec<RawDisjoint>,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<NormalizedDisjoint>> {
    budget.claim_work(sort_work(raw.len()))?;
    raw.sort_by(|left, right| {
        left.classes
            .cmp(&right.classes)
            .then_with(|| left.provenance.cmp(&right.provenance))
    });
    let mut normalized = Vec::<NormalizedDisjoint>::new();
    for value in raw {
        budget.claim_work(1)?;
        if let Some(previous) = normalized.last_mut() {
            if previous.classes == value.classes {
                if previous.guard_digest != value.guard_digest {
                    return Err(EncodedValidationError::invariant(
                        "equivalent disjoint classes disagree on their guard identity",
                    ));
                }
                if previous.provenance.last() != Some(&value.provenance) {
                    budget.claim_owned(size_of::<[u8; 32]>())?;
                    previous.provenance.try_reserve(1).map_err(|_| {
                        EncodedValidationError::resource(
                            "disjoint-class provenance allocation failed",
                        )
                    })?;
                    previous.provenance.push(value.provenance);
                }
                continue;
            }
        }
        budget.claim_owned(size_of::<NormalizedDisjoint>() + size_of::<[u8; 32]>())?;
        normalized.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("normalized disjoint-class allocation failed")
        })?;
        let mut provenance = Vec::new();
        provenance.try_reserve_exact(1).map_err(|_| {
            EncodedValidationError::resource("disjoint-class provenance allocation failed")
        })?;
        provenance.push(value.provenance);
        normalized.push(NormalizedDisjoint {
            classes: value.classes,
            provenance,
            guard_digest: value.guard_digest,
        });
    }
    Ok(normalized)
}

fn normalize_facts(
    mut raw: Vec<RawFact>,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<NormalizedFact>> {
    budget.claim_work(sort_work(raw.len()))?;
    raw.sort_by_key(|fact| {
        (
            fact.class_id,
            fact.individual_id,
            fact.negative,
            fact.provenance,
        )
    });
    let mut normalized = Vec::<NormalizedFact>::new();
    for fact in raw {
        budget.claim_work(1)?;
        if let Some(previous) = normalized.last_mut() {
            if previous.class_id == fact.class_id
                && previous.individual_id == fact.individual_id
                && previous.negative == fact.negative
            {
                if previous.provenance.last() != Some(&fact.provenance) {
                    budget.claim_owned(size_of::<[u8; 32]>())?;
                    previous.provenance.try_reserve(1).map_err(|_| {
                        EncodedValidationError::resource(
                            "named class-assertion provenance allocation failed",
                        )
                    })?;
                    previous.provenance.push(fact.provenance);
                }
                continue;
            }
        }
        budget.claim_owned(size_of::<NormalizedFact>() + size_of::<[u8; 32]>())?;
        normalized.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("normalized class-assertion allocation failed")
        })?;
        let mut provenance = Vec::new();
        provenance.try_reserve_exact(1).map_err(|_| {
            EncodedValidationError::resource("named class-assertion provenance allocation failed")
        })?;
        provenance.push(fact.provenance);
        normalized.push(NormalizedFact {
            class_id: fact.class_id,
            individual_id: fact.individual_id,
            negative: fact.negative,
            provenance,
        });
    }
    Ok(normalized)
}

fn normalize_object_constraints(
    mut raw: Vec<RawObjectConstraint>,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<NormalizedObjectConstraint>> {
    budget.claim_work(sort_work(raw.len()))?;
    raw.sort_unstable();
    let mut normalized = Vec::<NormalizedObjectConstraint>::new();
    for constraint in raw {
        budget.claim_work(1)?;
        if let Some(previous) = normalized.last_mut() {
            if previous.kind == constraint.kind
                && previous.role_id == constraint.role_id
                && previous.class == constraint.class
            {
                if previous.provenance.last() != Some(&constraint.provenance) {
                    budget.claim_owned(size_of::<[u8; 32]>())?;
                    previous.provenance.try_reserve(1).map_err(|_| {
                        EncodedValidationError::resource(
                            "object-property constraint provenance allocation failed",
                        )
                    })?;
                    previous.provenance.push(constraint.provenance);
                }
                continue;
            }
        }
        budget.claim_owned(size_of::<NormalizedObjectConstraint>() + size_of::<[u8; 32]>())?;
        normalized.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource(
                "normalized object-property constraint allocation failed",
            )
        })?;
        let mut provenance = Vec::new();
        provenance.try_reserve_exact(1).map_err(|_| {
            EncodedValidationError::resource(
                "object-property constraint provenance allocation failed",
            )
        })?;
        provenance.push(constraint.provenance);
        normalized.push(NormalizedObjectConstraint {
            kind: constraint.kind,
            role_id: constraint.role_id,
            class: constraint.class,
            provenance,
        });
    }
    Ok(normalized)
}

fn normalize_object_characteristics(
    mut raw: Vec<RawObjectCharacteristic>,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<NormalizedObjectCharacteristic>> {
    budget.claim_work(sort_work(raw.len()))?;
    raw.sort_unstable();
    let mut normalized = Vec::<NormalizedObjectCharacteristic>::new();
    for characteristic in raw {
        budget.claim_work(1)?;
        if let Some(previous) = normalized.last_mut() {
            if previous.kind == characteristic.kind && previous.role_id == characteristic.role_id {
                if previous.provenance.last() != Some(&characteristic.provenance) {
                    budget.claim_owned(size_of::<[u8; 32]>())?;
                    previous.provenance.try_reserve(1).map_err(|_| {
                        EncodedValidationError::resource(
                            "object-property characteristic provenance allocation failed",
                        )
                    })?;
                    previous.provenance.push(characteristic.provenance);
                }
                continue;
            }
        }
        budget.claim_owned(size_of::<NormalizedObjectCharacteristic>() + size_of::<[u8; 32]>())?;
        normalized.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource(
                "normalized object-property characteristic allocation failed",
            )
        })?;
        let mut provenance = Vec::new();
        provenance.try_reserve_exact(1).map_err(|_| {
            EncodedValidationError::resource(
                "object-property characteristic provenance allocation failed",
            )
        })?;
        provenance.push(characteristic.provenance);
        normalized.push(NormalizedObjectCharacteristic {
            kind: characteristic.kind,
            role_id: characteristic.role_id,
            provenance,
        });
    }
    Ok(normalized)
}

fn normalize_data_domains(
    mut raw: Vec<RawDataDomain>,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<NormalizedDataDomain>> {
    budget.claim_work(sort_work(raw.len()))?;
    raw.sort_unstable();
    let mut normalized = Vec::<NormalizedDataDomain>::new();
    for domain in raw {
        budget.claim_work(1)?;
        if let Some(previous) = normalized.last_mut() {
            if previous.role_id == domain.role_id && previous.class == domain.class {
                if previous.provenance.last() != Some(&domain.provenance) {
                    budget.claim_owned(size_of::<[u8; 32]>())?;
                    previous.provenance.try_reserve(1).map_err(|_| {
                        EncodedValidationError::resource(
                            "data-property domain provenance allocation failed",
                        )
                    })?;
                    previous.provenance.push(domain.provenance);
                }
                continue;
            }
        }
        budget.claim_owned(size_of::<NormalizedDataDomain>() + size_of::<[u8; 32]>())?;
        normalized.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("normalized data-property domain allocation failed")
        })?;
        let mut provenance = Vec::new();
        provenance.try_reserve_exact(1).map_err(|_| {
            EncodedValidationError::resource("data-property domain provenance allocation failed")
        })?;
        provenance.push(domain.provenance);
        normalized.push(NormalizedDataDomain {
            role_id: domain.role_id,
            class: domain.class,
            provenance,
        });
    }
    Ok(normalized)
}

fn normalize_data_ranges(
    mut raw: Vec<RawDataRange>,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<NormalizedDataRange>> {
    budget.claim_work(sort_work(raw.len()))?;
    raw.sort_unstable();
    let mut normalized = Vec::<NormalizedDataRange>::new();
    for range in raw {
        budget.claim_work(1)?;
        if let Some(previous) = normalized.last_mut() {
            if previous.role_id == range.role_id && previous.range == range.range {
                if previous.provenance.last() != Some(&range.provenance) {
                    budget.claim_owned(size_of::<[u8; 32]>())?;
                    previous.provenance.try_reserve(1).map_err(|_| {
                        EncodedValidationError::resource(
                            "data-property range provenance allocation failed",
                        )
                    })?;
                    previous.provenance.push(range.provenance);
                }
                continue;
            }
        }
        budget.claim_owned(size_of::<NormalizedDataRange>() + size_of::<[u8; 32]>())?;
        normalized.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("normalized data-property range allocation failed")
        })?;
        let mut provenance = Vec::new();
        provenance.try_reserve_exact(1).map_err(|_| {
            EncodedValidationError::resource("data-property range provenance allocation failed")
        })?;
        provenance.push(range.provenance);
        normalized.push(NormalizedDataRange {
            role_id: range.role_id,
            range: range.range,
            provenance,
        });
    }
    Ok(normalized)
}

fn normalize_datatype_definitions(
    mut raw: Vec<RawDatatypeDefinition>,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<NormalizedDatatypeDefinition>> {
    budget.claim_work(sort_work(raw.len()))?;
    raw.sort_unstable();
    let mut normalized = Vec::<NormalizedDatatypeDefinition>::new();
    for definition in raw {
        budget.claim_work(1)?;
        if let Some(previous) = normalized.last_mut() {
            if previous.left_range == definition.left_range
                && previous.right_range == definition.right_range
            {
                if previous.provenance.last() != Some(&definition.provenance) {
                    budget.claim_owned(size_of::<[u8; 32]>())?;
                    previous.provenance.try_reserve(1).map_err(|_| {
                        EncodedValidationError::resource(
                            "datatype-definition provenance allocation failed",
                        )
                    })?;
                    previous.provenance.push(definition.provenance);
                }
                continue;
            }
        }
        budget.claim_owned(size_of::<NormalizedDatatypeDefinition>() + size_of::<[u8; 32]>())?;
        normalized.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("normalized datatype-definition allocation failed")
        })?;
        let mut provenance = Vec::new();
        provenance.try_reserve_exact(1).map_err(|_| {
            EncodedValidationError::resource("datatype-definition provenance allocation failed")
        })?;
        provenance.push(definition.provenance);
        normalized.push(NormalizedDatatypeDefinition {
            left_range: definition.left_range,
            right_range: definition.right_range,
            provenance,
        });
    }
    Ok(normalized)
}

fn normalize_keys(
    mut raw: Vec<RawKey>,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<NormalizedKey>> {
    budget.claim_work(sort_work(raw.len()))?;
    raw.sort_unstable();
    let mut normalized = Vec::<NormalizedKey>::new();
    for key in raw {
        budget.claim_work(1)?;
        if let Some(previous) = normalized.last_mut() {
            if previous.class == key.class
                && previous.object_role_ids == key.object_role_ids
                && previous.data_role_ids == key.data_role_ids
            {
                if previous.provenance.last() != Some(&key.provenance) {
                    budget.claim_owned(size_of::<[u8; 32]>())?;
                    previous.provenance.try_reserve(1).map_err(|_| {
                        EncodedValidationError::resource("has-key provenance allocation failed")
                    })?;
                    previous.provenance.push(key.provenance);
                }
                continue;
            }
        }
        budget.claim_owned(size_of::<NormalizedKey>() + size_of::<[u8; 32]>())?;
        normalized.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("normalized has-key allocation failed")
        })?;
        let mut provenance = Vec::new();
        provenance.try_reserve_exact(1).map_err(|_| {
            EncodedValidationError::resource("has-key provenance allocation failed")
        })?;
        provenance.push(key.provenance);
        normalized.push(NormalizedKey {
            class: key.class,
            object_role_ids: key.object_role_ids,
            data_role_ids: key.data_role_ids,
            provenance,
        });
    }
    Ok(normalized)
}

fn normalize_data_functionalities(
    mut raw: Vec<RawDataFunctionality>,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<NormalizedDataFunctionality>> {
    budget.claim_work(sort_work(raw.len()))?;
    raw.sort_unstable();
    let mut normalized = Vec::<NormalizedDataFunctionality>::new();
    for functionality in raw {
        budget.claim_work(1)?;
        if let Some(previous) = normalized.last_mut() {
            if previous.role_id == functionality.role_id {
                if previous.provenance.last() != Some(&functionality.provenance) {
                    budget.claim_owned(size_of::<[u8; 32]>())?;
                    previous.provenance.try_reserve(1).map_err(|_| {
                        EncodedValidationError::resource(
                            "functional data-property provenance allocation failed",
                        )
                    })?;
                    previous.provenance.push(functionality.provenance);
                }
                continue;
            }
        }
        budget.claim_owned(size_of::<NormalizedDataFunctionality>() + size_of::<[u8; 32]>())?;
        normalized.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource(
                "normalized functional data-property allocation failed",
            )
        })?;
        let mut provenance = Vec::new();
        provenance.try_reserve_exact(1).map_err(|_| {
            EncodedValidationError::resource(
                "functional data-property provenance allocation failed",
            )
        })?;
        provenance.push(functionality.provenance);
        normalized.push(NormalizedDataFunctionality {
            role_id: functionality.role_id,
            provenance,
        });
    }
    Ok(normalized)
}

fn normalize_object_facts(
    mut raw: Vec<RawObjectFact>,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<NormalizedObjectFact>> {
    budget.claim_work(sort_work(raw.len()))?;
    raw.sort_unstable();
    let mut normalized = Vec::<NormalizedObjectFact>::new();
    for fact in raw {
        budget.claim_work(1)?;
        if let Some(previous) = normalized.last_mut() {
            if previous.role_id == fact.role_id
                && previous.source_individual == fact.source_individual
                && previous.target_individual == fact.target_individual
            {
                if previous.provenance.last() != Some(&fact.provenance) {
                    budget.claim_owned(size_of::<[u8; 32]>())?;
                    previous.provenance.try_reserve(1).map_err(|_| {
                        EncodedValidationError::resource(
                            "object-property assertion provenance allocation failed",
                        )
                    })?;
                    previous.provenance.push(fact.provenance);
                }
                continue;
            }
        }
        budget.claim_owned(size_of::<NormalizedObjectFact>() + size_of::<[u8; 32]>())?;
        normalized.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource(
                "normalized object-property assertion allocation failed",
            )
        })?;
        let mut provenance = Vec::new();
        provenance.try_reserve_exact(1).map_err(|_| {
            EncodedValidationError::resource(
                "object-property assertion provenance allocation failed",
            )
        })?;
        provenance.push(fact.provenance);
        normalized.push(NormalizedObjectFact {
            role_id: fact.role_id,
            source_individual: fact.source_individual,
            target_individual: fact.target_individual,
            provenance,
        });
    }
    Ok(normalized)
}

fn normalize_data_facts(
    mut raw: Vec<RawDataFact>,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<NormalizedDataFact>> {
    budget.claim_work(sort_work(raw.len()))?;
    raw.sort_unstable();
    let mut normalized = Vec::<NormalizedDataFact>::new();
    for fact in raw {
        budget.claim_work(1)?;
        if let Some(previous) = normalized.last_mut() {
            if previous.role_id == fact.role_id
                && previous.source_individual == fact.source_individual
                && previous.source_literal_id == fact.source_literal_id
                && previous.data_identity_id == fact.data_identity_id
            {
                if previous.provenance.last() != Some(&fact.provenance) {
                    budget.claim_owned(size_of::<[u8; 32]>())?;
                    previous.provenance.try_reserve(1).map_err(|_| {
                        EncodedValidationError::resource(
                            "data-property assertion provenance allocation failed",
                        )
                    })?;
                    previous.provenance.push(fact.provenance);
                }
                continue;
            }
        }
        budget.claim_owned(size_of::<NormalizedDataFact>() + size_of::<[u8; 32]>())?;
        normalized.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("normalized data-property assertion allocation failed")
        })?;
        let mut provenance = Vec::new();
        provenance.try_reserve_exact(1).map_err(|_| {
            EncodedValidationError::resource("data-property assertion provenance allocation failed")
        })?;
        provenance.push(fact.provenance);
        normalized.push(NormalizedDataFact {
            role_id: fact.role_id,
            source_individual: fact.source_individual,
            source_literal_id: fact.source_literal_id,
            data_identity_id: fact.data_identity_id,
            provenance,
        });
    }
    Ok(normalized)
}

fn normalize_equalities(
    mut raw: Vec<RawEqualityFact>,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<NormalizedEqualityFact>> {
    budget.claim_work(sort_work(raw.len()))?;
    raw.sort_unstable();
    let mut normalized = Vec::<NormalizedEqualityFact>::new();
    for fact in raw {
        budget.claim_work(1)?;
        if let Some(previous) = normalized.last_mut() {
            if previous.left_individual == fact.left_individual
                && previous.right_individual == fact.right_individual
                && previous.statement_sha256 == fact.statement_sha256
            {
                if previous.provenance.last() != Some(&fact.provenance) {
                    budget.claim_owned(size_of::<[u8; 32]>())?;
                    previous.provenance.try_reserve(1).map_err(|_| {
                        EncodedValidationError::resource(
                            "same-individual provenance allocation failed",
                        )
                    })?;
                    previous.provenance.push(fact.provenance);
                }
                continue;
            }
        }
        budget.claim_owned(size_of::<NormalizedEqualityFact>() + size_of::<[u8; 32]>())?;
        normalized.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("normalized same-individual allocation failed")
        })?;
        let mut provenance = Vec::new();
        provenance.try_reserve_exact(1).map_err(|_| {
            EncodedValidationError::resource("same-individual provenance allocation failed")
        })?;
        provenance.push(fact.provenance);
        normalized.push(NormalizedEqualityFact {
            left_individual: fact.left_individual,
            right_individual: fact.right_individual,
            statement_sha256: fact.statement_sha256,
            provenance,
        });
    }
    Ok(normalized)
}

fn normalize_inequalities(
    mut raw: Vec<RawInequalityFact>,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<NormalizedInequalityFact>> {
    budget.claim_work(sort_work(raw.len()))?;
    raw.sort_unstable();
    let mut normalized = Vec::<NormalizedInequalityFact>::new();
    for fact in raw {
        budget.claim_work(1)?;
        if let Some(previous) = normalized.last_mut() {
            if previous.left_individual == fact.left_individual
                && previous.right_individual == fact.right_individual
                && previous.statement_sha256 == fact.statement_sha256
            {
                if previous.provenance.last() != Some(&fact.provenance) {
                    budget.claim_owned(size_of::<[u8; 32]>())?;
                    previous.provenance.try_reserve(1).map_err(|_| {
                        EncodedValidationError::resource(
                            "different-individual provenance allocation failed",
                        )
                    })?;
                    previous.provenance.push(fact.provenance);
                }
                continue;
            }
        }
        budget.claim_owned(size_of::<NormalizedInequalityFact>() + size_of::<[u8; 32]>())?;
        normalized.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("normalized different-individual allocation failed")
        })?;
        let mut provenance = Vec::new();
        provenance.try_reserve_exact(1).map_err(|_| {
            EncodedValidationError::resource("different-individual provenance allocation failed")
        })?;
        provenance.push(fact.provenance);
        normalized.push(NormalizedInequalityFact {
            left_individual: fact.left_individual,
            right_individual: fact.right_individual,
            statement_sha256: fact.statement_sha256,
            provenance,
        });
    }
    Ok(normalized)
}

#[allow(clippy::too_many_arguments)]
fn freeze_provenance(
    edges: &[NormalizedEdge],
    disjoints: &[NormalizedDisjoint],
    object_constraints: &[NormalizedObjectConstraint],
    object_characteristics: &[NormalizedObjectCharacteristic],
    data_domains: &[NormalizedDataDomain],
    data_ranges: &[NormalizedDataRange],
    datatype_definitions: &[NormalizedDatatypeDefinition],
    normalized_keys: &[NormalizedKey],
    data_functionalities: &[NormalizedDataFunctionality],
    facts: &[NormalizedFact],
    object_facts: &[NormalizedObjectFact],
    negative_object_facts: &[NormalizedObjectFact],
    data_facts: &[NormalizedDataFact],
    negative_data_facts: &[NormalizedDataFact],
    equalities: &[NormalizedEqualityFact],
    inequalities: &[NormalizedInequalityFact],
    budget: &mut PhaseBudget,
) -> EncodedResult<(Vec<DecodedProvenanceEntry>, Vec<ProvenanceKey>)> {
    let builtin: [u8; 32] = Sha256::digest(BUILTIN_PROVENANCE_INPUT).into();
    let mut keys = Vec::new();
    push_provenance_key(
        &mut keys,
        ProvenanceKey {
            source_sha256: vec![builtin],
            generated: true,
        },
        budget,
    )?;
    for edge in edges {
        push_provenance_key(
            &mut keys,
            ProvenanceKey {
                source_sha256: edge.provenance.clone(),
                generated: false,
            },
            budget,
        )?;
    }
    for disjoint in disjoints {
        push_provenance_key(
            &mut keys,
            ProvenanceKey {
                source_sha256: disjoint.provenance.clone(),
                generated: false,
            },
            budget,
        )?;
    }
    for constraint in object_constraints {
        push_provenance_key(
            &mut keys,
            ProvenanceKey {
                source_sha256: constraint.provenance.clone(),
                generated: false,
            },
            budget,
        )?;
    }
    for characteristic in object_characteristics {
        push_provenance_key(
            &mut keys,
            ProvenanceKey {
                source_sha256: characteristic.provenance.clone(),
                generated: false,
            },
            budget,
        )?;
    }
    for domain in data_domains {
        push_provenance_key(
            &mut keys,
            ProvenanceKey {
                source_sha256: domain.provenance.clone(),
                generated: false,
            },
            budget,
        )?;
    }
    for range in data_ranges {
        push_provenance_key(
            &mut keys,
            ProvenanceKey {
                source_sha256: range.provenance.clone(),
                generated: false,
            },
            budget,
        )?;
    }
    for definition in datatype_definitions {
        push_provenance_key(
            &mut keys,
            ProvenanceKey {
                source_sha256: definition.provenance.clone(),
                generated: false,
            },
            budget,
        )?;
    }
    for key in normalized_keys {
        push_provenance_key(
            &mut keys,
            ProvenanceKey {
                source_sha256: key.provenance.clone(),
                generated: false,
            },
            budget,
        )?;
    }
    for functionality in data_functionalities {
        push_provenance_key(
            &mut keys,
            ProvenanceKey {
                source_sha256: functionality.provenance.clone(),
                generated: false,
            },
            budget,
        )?;
    }
    for fact in facts {
        push_provenance_key(
            &mut keys,
            ProvenanceKey {
                source_sha256: fact.provenance.clone(),
                generated: false,
            },
            budget,
        )?;
    }
    for fact in object_facts {
        push_provenance_key(
            &mut keys,
            ProvenanceKey {
                source_sha256: fact.provenance.clone(),
                generated: false,
            },
            budget,
        )?;
    }
    for fact in negative_object_facts {
        push_provenance_key(
            &mut keys,
            ProvenanceKey {
                source_sha256: fact.provenance.clone(),
                generated: false,
            },
            budget,
        )?;
    }
    for fact in data_facts {
        push_provenance_key(
            &mut keys,
            ProvenanceKey {
                source_sha256: fact.provenance.clone(),
                generated: false,
            },
            budget,
        )?;
    }
    for fact in negative_data_facts {
        push_provenance_key(
            &mut keys,
            ProvenanceKey {
                source_sha256: fact.provenance.clone(),
                generated: false,
            },
            budget,
        )?;
    }
    budget.claim_work(equalities.len())?;
    for equality in equalities {
        push_provenance_key(
            &mut keys,
            ProvenanceKey {
                source_sha256: equality.provenance.clone(),
                generated: false,
            },
            budget,
        )?;
    }
    budget.claim_work(inequalities.len())?;
    for inequality in inequalities {
        push_provenance_key(
            &mut keys,
            ProvenanceKey {
                source_sha256: inequality.provenance.clone(),
                generated: false,
            },
            budget,
        )?;
    }
    budget.claim_work(sort_work(keys.len()))?;
    keys.sort();
    keys.dedup();
    PhaseBudget::count(keys.len(), budget.limits.max_provenance, "provenance count")?;

    let mut entries = Vec::new();
    budget.claim_owned(
        keys.len()
            .checked_mul(size_of::<DecodedProvenanceEntry>())
            .ok_or_else(|| {
                EncodedValidationError::resource("named-class provenance output overflowed")
            })?,
    )?;
    entries.try_reserve_exact(keys.len()).map_err(|_| {
        EncodedValidationError::resource("named-class provenance output allocation failed")
    })?;
    for (identifier, key) in keys.iter().enumerate() {
        budget.claim_owned(
            key.source_sha256
                .len()
                .checked_mul(size_of::<[u8; 32]>())
                .ok_or_else(|| {
                    EncodedValidationError::resource(
                        "named-class provenance digest output overflowed",
                    )
                })?,
        )?;
        entries.push(DecodedProvenanceEntry {
            provenance_id: u32::try_from(identifier).map_err(|_| {
                EncodedValidationError::resource("named-class provenance ID exceeds u32")
            })?,
            source_sha256: key.source_sha256.clone(),
            generated: key.generated,
        });
    }
    Ok((entries, keys))
}

fn push_provenance_key(
    keys: &mut Vec<ProvenanceKey>,
    key: ProvenanceKey,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    budget.claim_owned(size_of::<ProvenanceKey>())?;
    budget.claim_owned(
        key.source_sha256
            .len()
            .checked_mul(size_of::<[u8; 32]>())
            .ok_or_else(|| {
                EncodedValidationError::resource("named-class provenance key overflowed")
            })?,
    )?;
    keys.try_reserve(1).map_err(|_| {
        EncodedValidationError::resource("named-class provenance-key allocation failed")
    })?;
    keys.push(key);
    Ok(())
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum PredicateOwner {
    Concept(u32),
    NegatedConcept(u32),
    Nominal {
        class_id: u32,
        individual_ids: Vec<u32>,
    },
    NegatedNominal {
        class_id: u32,
        individual_ids: Vec<u32>,
    },
    ObjectRole(u32),
    NegatedObjectRole(u32),
    DataRole(u32),
    NegatedDataRole(u32),
    DataRange(u32),
    NegatedDataRange(u32),
    Equality(TermSort),
    Inequality(TermSort),
    OrderingGuard,
    NamedIndividual,
    DisjointGuard {
        digest: [u8; 32],
        sequence: u32,
        internal_key: String,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct PendingPredicate {
    key: Vec<u8>,
    owner: PredicateOwner,
}

type PredicateIndex = Vec<(u32, u32)>;
type ObjectPredicateIndex = Vec<(u32, u32)>;
type GuardPredicateIndex = Vec<([u8; 32], u32, u32)>;

fn nominal_binding(bindings: &[NominalBinding], class_id: u32) -> Option<&NominalBinding> {
    bindings
        .binary_search_by_key(&class_id, |binding| binding.class_id)
        .ok()
        .map(|index| &bindings[index])
}

#[allow(clippy::too_many_arguments)]
fn nominal_usage(
    bindings: &[NominalBinding],
    edges: &[NormalizedEdge],
    disjoints: &[NormalizedDisjoint],
    object_constraints: &[NormalizedObjectConstraint],
    data_domains: &[NormalizedDataDomain],
    keys: &[NormalizedKey],
    facts: &[NormalizedFact],
) -> NominalUsage {
    if bindings.is_empty() {
        NominalUsage::None
    } else if edges.iter().any(|edge| {
        (edge.sub_negative && nominal_binding(bindings, edge.sub_class).is_some())
            || (edge.super_negative && nominal_binding(bindings, edge.super_class).is_some())
    }) || disjoints.iter().any(|disjoint| {
        disjoint.classes.iter().any(|literal| {
            literal.negative && nominal_binding(bindings, literal.class_id).is_some()
        })
    }) || object_constraints.iter().any(|constraint| {
        constraint.class.negative && nominal_binding(bindings, constraint.class.class_id).is_some()
    }) || data_domains.iter().any(|domain| {
        domain.class.negative && nominal_binding(bindings, domain.class.class_id).is_some()
    }) || keys
        .iter()
        .any(|key| key.class.negative && nominal_binding(bindings, key.class.class_id).is_some())
        || facts
            .iter()
            .any(|fact| fact.negative && nominal_binding(bindings, fact.class_id).is_some())
    {
        NominalUsage::Negative
    } else {
        NominalUsage::Positive
    }
}

type FrozenPredicates = (
    Vec<DecodedPredicate>,
    PredicateIndex,
    PredicateIndex,
    ObjectPredicateIndex,
    ObjectPredicateIndex,
    ObjectPredicateIndex,
    ObjectPredicateIndex,
    PredicateIndex,
    PredicateIndex,
    GuardPredicateIndex,
    Option<u32>,
    Option<u32>,
    Option<u32>,
    Option<u32>,
    Option<u32>,
    Option<u32>,
);

#[allow(clippy::too_many_arguments)]
fn freeze_predicates(
    nominal_bindings: &[NominalBinding],
    edges: &[NormalizedEdge],
    disjoints: &[NormalizedDisjoint],
    object_constraints: &[NormalizedObjectConstraint],
    object_characteristics: &[NormalizedObjectCharacteristic],
    data_domains: &[NormalizedDataDomain],
    data_ranges: &[NormalizedDataRange],
    datatype_definitions: &[NormalizedDatatypeDefinition],
    keys: &[NormalizedKey],
    data_functionalities: &[NormalizedDataFunctionality],
    facts: &[NormalizedFact],
    object_facts: &[NormalizedObjectFact],
    negative_object_facts: &[NormalizedObjectFact],
    data_facts: &[NormalizedDataFact],
    negative_data_facts: &[NormalizedDataFact],
    equalities: &[NormalizedEqualityFact],
    inequalities: &[NormalizedInequalityFact],
    thing: u32,
    nothing: u32,
    top_data_range: u32,
    has_individuals: bool,
    has_named_individuals: bool,
    budget: &mut PhaseBudget,
) -> EncodedResult<FrozenPredicates> {
    if !nominal_bindings
        .windows(2)
        .all(|pair| pair[0].class_id < pair[1].class_id)
        || nominal_bindings.iter().any(|binding| {
            binding.individual_ids.is_empty()
                || !binding
                    .individual_ids
                    .windows(2)
                    .all(|pair| pair[0] < pair[1])
        })
    {
        return Err(EncodedValidationError::invariant(
            "object nominal bindings are not canonical",
        ));
    }
    let mut class_ids = Vec::new();
    let mut negative_class_ids = Vec::new();
    push_u32(&mut class_ids, nothing, "predicate class", budget)?;
    if has_individuals
        || object_characteristics
            .iter()
            .any(|value| value.kind == ObjectCharacteristicKind::Reflexive)
    {
        push_u32(&mut class_ids, thing, "predicate class", budget)?;
    }
    for edge in edges {
        push_u32(&mut class_ids, edge.sub_class, "predicate class", budget)?;
        push_u32(&mut class_ids, edge.super_class, "predicate class", budget)?;
        if edge.sub_negative {
            push_u32(
                &mut negative_class_ids,
                edge.sub_class,
                "negated predicate class",
                budget,
            )?;
        }
        if edge.super_negative {
            push_u32(
                &mut negative_class_ids,
                edge.super_class,
                "negated predicate class",
                budget,
            )?;
        }
    }
    for disjoint in disjoints {
        for literal in &disjoint.classes {
            push_u32(&mut class_ids, literal.class_id, "predicate class", budget)?;
            if literal.negative {
                push_u32(
                    &mut negative_class_ids,
                    literal.class_id,
                    "negated predicate class",
                    budget,
                )?;
            }
        }
    }
    for constraint in object_constraints {
        push_u32(
            &mut class_ids,
            constraint.class.class_id,
            "predicate class",
            budget,
        )?;
        if constraint.class.negative {
            push_u32(
                &mut negative_class_ids,
                constraint.class.class_id,
                "negated predicate class",
                budget,
            )?;
        }
    }
    for domain in data_domains {
        push_u32(
            &mut class_ids,
            domain.class.class_id,
            "predicate class",
            budget,
        )?;
        if domain.class.negative {
            push_u32(
                &mut negative_class_ids,
                domain.class.class_id,
                "negated predicate class",
                budget,
            )?;
        }
    }
    for key in keys {
        push_u32(
            &mut class_ids,
            key.class.class_id,
            "predicate key class",
            budget,
        )?;
        if key.class.negative {
            push_u32(
                &mut negative_class_ids,
                key.class.class_id,
                "negated predicate key class",
                budget,
            )?;
        }
    }
    for fact in facts {
        push_u32(&mut class_ids, fact.class_id, "predicate class", budget)?;
        if fact.negative {
            push_u32(
                &mut negative_class_ids,
                fact.class_id,
                "negated predicate class",
                budget,
            )?;
        }
    }
    if !negative_class_ids.is_empty() {
        push_u32(&mut class_ids, thing, "predicate class", budget)?;
    }
    budget.claim_work(sort_work(class_ids.len()))?;
    class_ids.sort_unstable();
    class_ids.dedup();
    budget.claim_work(sort_work(negative_class_ids.len()))?;
    negative_class_ids.sort_unstable();
    negative_class_ids.dedup();
    let has_negative_nominals = negative_class_ids
        .iter()
        .any(|class_id| nominal_binding(nominal_bindings, *class_id).is_some());

    let mut ordered = Vec::<PendingPredicate>::new();
    if !equalities.is_empty()
        || !nominal_bindings.is_empty()
        || !keys.is_empty()
        || object_characteristics
            .iter()
            .any(|value| value.kind != ObjectCharacteristicKind::Reflexive)
    {
        let key = equality_predicate_key(TermSort::Object);
        budget.claim_owned(size_of::<PendingPredicate>())?;
        budget.claim_owned(key.len())?;
        ordered.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("equality predicate allocation failed")
        })?;
        ordered.push(PendingPredicate {
            key,
            owner: PredicateOwner::Equality(TermSort::Object),
        });
    }
    if !data_functionalities.is_empty() {
        let key = equality_predicate_key(TermSort::Data);
        budget.claim_owned(size_of::<PendingPredicate>())?;
        budget.claim_owned(key.len())?;
        ordered.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("data equality predicate allocation failed")
        })?;
        ordered.push(PendingPredicate {
            key,
            owner: PredicateOwner::Equality(TermSort::Data),
        });
    }
    if !inequalities.is_empty() || has_negative_nominals {
        let key = inequality_predicate_key(TermSort::Object);
        budget.claim_owned(size_of::<PendingPredicate>())?;
        budget.claim_owned(key.len())?;
        ordered.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("inequality predicate allocation failed")
        })?;
        ordered.push(PendingPredicate {
            key,
            owner: PredicateOwner::Inequality(TermSort::Object),
        });
    }
    if !negative_data_facts.is_empty() || keys.iter().any(|key| !key.data_role_ids.is_empty()) {
        let key = inequality_predicate_key(TermSort::Data);
        budget.claim_owned(size_of::<PendingPredicate>())?;
        budget.claim_owned(key.len())?;
        ordered.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("data inequality predicate allocation failed")
        })?;
        ordered.push(PendingPredicate {
            key,
            owner: PredicateOwner::Inequality(TermSort::Data),
        });
    }
    if !keys.is_empty() {
        let key = ordering_predicate_key();
        budget.claim_owned(size_of::<PendingPredicate>())?;
        budget.claim_owned(key.len())?;
        ordered.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("ordering-guard predicate allocation failed")
        })?;
        ordered.push(PendingPredicate {
            key,
            owner: PredicateOwner::OrderingGuard,
        });
    }
    if has_named_individuals || !keys.is_empty() {
        let key = named_individual_predicate_key();
        budget.claim_owned(size_of::<PendingPredicate>())?;
        budget.claim_owned(key.len())?;
        ordered.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("named-individual predicate allocation failed")
        })?;
        ordered.push(PendingPredicate {
            key,
            owner: PredicateOwner::NamedIndividual,
        });
    }
    for class_id in class_ids {
        let nominal = nominal_binding(nominal_bindings, class_id);
        let key = nominal.map_or_else(
            || concept_predicate_key(class_id),
            |binding| nominal_predicate_key(class_id, &binding.individual_ids, false),
        );
        budget.claim_owned(size_of::<PendingPredicate>())?;
        budget.claim_owned(key.len())?;
        if let Some(binding) = nominal {
            budget.claim_owned(
                binding
                    .individual_ids
                    .len()
                    .checked_mul(size_of::<u32>())
                    .ok_or_else(|| {
                        EncodedValidationError::resource("nominal predicate annotation overflowed")
                    })?,
            )?;
        }
        ordered.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("named-class predicate ordering allocation failed")
        })?;
        ordered.push(PendingPredicate {
            key,
            owner: nominal.map_or(PredicateOwner::Concept(class_id), |binding| {
                PredicateOwner::Nominal {
                    class_id,
                    individual_ids: binding.individual_ids.clone(),
                }
            }),
        });
    }
    for class_id in negative_class_ids.iter().copied() {
        let nominal = nominal_binding(nominal_bindings, class_id);
        let key = nominal.map_or_else(
            || negated_concept_predicate_key(class_id),
            |binding| nominal_predicate_key(class_id, &binding.individual_ids, true),
        );
        budget.claim_owned(size_of::<PendingPredicate>())?;
        budget.claim_owned(key.len())?;
        if let Some(binding) = nominal {
            budget.claim_owned(
                binding
                    .individual_ids
                    .len()
                    .checked_mul(size_of::<u32>())
                    .ok_or_else(|| {
                        EncodedValidationError::resource(
                            "negated nominal predicate annotation overflowed",
                        )
                    })?,
            )?;
        }
        ordered.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource(
                "negated named-class predicate ordering allocation failed",
            )
        })?;
        ordered.push(PendingPredicate {
            key,
            owner: nominal.map_or(PredicateOwner::NegatedConcept(class_id), |binding| {
                PredicateOwner::NegatedNominal {
                    class_id,
                    individual_ids: binding.individual_ids.clone(),
                }
            }),
        });
    }
    let mut object_role_ids = Vec::new();
    for constraint in object_constraints {
        push_u32(
            &mut object_role_ids,
            constraint.role_id,
            "predicate object role",
            budget,
        )?;
    }
    for characteristic in object_characteristics {
        push_u32(
            &mut object_role_ids,
            characteristic.role_id,
            "predicate object role",
            budget,
        )?;
    }
    for key in keys {
        for role_id in &key.object_role_ids {
            push_u32(
                &mut object_role_ids,
                *role_id,
                "predicate key object role",
                budget,
            )?;
        }
    }
    for fact in object_facts {
        push_u32(
            &mut object_role_ids,
            fact.role_id,
            "predicate object role",
            budget,
        )?;
    }
    budget.claim_work(sort_work(object_role_ids.len()))?;
    object_role_ids.sort_unstable();
    object_role_ids.dedup();
    for role_id in object_role_ids {
        let key = role_predicate_key(PredicateKind::ObjectRole, role_id);
        budget.claim_owned(size_of::<PendingPredicate>())?;
        budget.claim_owned(key.len())?;
        ordered.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("object-role predicate allocation failed")
        })?;
        ordered.push(PendingPredicate {
            key,
            owner: PredicateOwner::ObjectRole(role_id),
        });
    }
    let mut negative_object_role_ids = Vec::new();
    for fact in negative_object_facts {
        push_u32(
            &mut negative_object_role_ids,
            fact.role_id,
            "predicate negative object role",
            budget,
        )?;
    }
    budget.claim_work(sort_work(negative_object_role_ids.len()))?;
    negative_object_role_ids.sort_unstable();
    negative_object_role_ids.dedup();
    for role_id in negative_object_role_ids {
        let key = role_predicate_key(PredicateKind::NegatedObjectRole, role_id);
        budget.claim_owned(size_of::<PendingPredicate>())?;
        budget.claim_owned(key.len())?;
        ordered.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("negated object-role predicate allocation failed")
        })?;
        ordered.push(PendingPredicate {
            key,
            owner: PredicateOwner::NegatedObjectRole(role_id),
        });
    }
    let mut data_role_ids = Vec::new();
    for domain in data_domains {
        push_u32(
            &mut data_role_ids,
            domain.role_id,
            "predicate data role",
            budget,
        )?;
    }
    for range in data_ranges {
        push_u32(
            &mut data_role_ids,
            range.role_id,
            "predicate data role",
            budget,
        )?;
    }
    for functionality in data_functionalities {
        push_u32(
            &mut data_role_ids,
            functionality.role_id,
            "predicate data role",
            budget,
        )?;
    }
    for key in keys {
        for role_id in &key.data_role_ids {
            push_u32(
                &mut data_role_ids,
                *role_id,
                "predicate key data role",
                budget,
            )?;
        }
    }
    for fact in data_facts {
        push_u32(
            &mut data_role_ids,
            fact.role_id,
            "predicate data role",
            budget,
        )?;
    }
    budget.claim_work(sort_work(data_role_ids.len()))?;
    data_role_ids.sort_unstable();
    data_role_ids.dedup();
    for role_id in data_role_ids {
        let key = role_predicate_key(PredicateKind::DataRole, role_id);
        budget.claim_owned(size_of::<PendingPredicate>())?;
        budget.claim_owned(key.len())?;
        ordered.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("data-role predicate allocation failed")
        })?;
        ordered.push(PendingPredicate {
            key,
            owner: PredicateOwner::DataRole(role_id),
        });
    }
    let mut negative_data_role_ids = Vec::new();
    for fact in negative_data_facts {
        push_u32(
            &mut negative_data_role_ids,
            fact.role_id,
            "predicate negative data role",
            budget,
        )?;
    }
    budget.claim_work(sort_work(negative_data_role_ids.len()))?;
    negative_data_role_ids.sort_unstable();
    negative_data_role_ids.dedup();
    for role_id in negative_data_role_ids {
        let key = role_predicate_key(PredicateKind::NegatedDataRole, role_id);
        budget.claim_owned(size_of::<PendingPredicate>())?;
        budget.claim_owned(key.len())?;
        ordered.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("negated data-role predicate allocation failed")
        })?;
        ordered.push(PendingPredicate {
            key,
            owner: PredicateOwner::NegatedDataRole(role_id),
        });
    }
    let mut data_range_ids = Vec::new();
    let mut negative_data_range_ids = Vec::new();
    for range in data_ranges {
        push_u32(
            &mut data_range_ids,
            range.range.range_id,
            "predicate data range",
            budget,
        )?;
        if range.range.negative {
            push_u32(
                &mut negative_data_range_ids,
                range.range.range_id,
                "negated predicate data range",
                budget,
            )?;
        }
    }
    for definition in datatype_definitions {
        push_u32(
            &mut data_range_ids,
            definition.left_range.range_id,
            "predicate defined datatype",
            budget,
        )?;
        push_u32(
            &mut data_range_ids,
            definition.right_range.range_id,
            "predicate datatype defining range",
            budget,
        )?;
        for range in [definition.left_range, definition.right_range]
            .into_iter()
            .filter(|range| range.negative)
        {
            push_u32(
                &mut negative_data_range_ids,
                range.range_id,
                "negated predicate data range",
                budget,
            )?;
        }
    }
    if !negative_data_range_ids.is_empty() {
        push_u32(
            &mut data_range_ids,
            top_data_range,
            "predicate universal data range",
            budget,
        )?;
    }
    budget.claim_work(sort_work(data_range_ids.len()))?;
    data_range_ids.sort_unstable();
    data_range_ids.dedup();
    for range_id in data_range_ids {
        let key = data_range_predicate_key(range_id);
        budget.claim_owned(size_of::<PendingPredicate>())?;
        budget.claim_owned(key.len())?;
        ordered.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("data-range predicate allocation failed")
        })?;
        ordered.push(PendingPredicate {
            key,
            owner: PredicateOwner::DataRange(range_id),
        });
    }
    budget.claim_work(sort_work(negative_data_range_ids.len()))?;
    negative_data_range_ids.sort_unstable();
    negative_data_range_ids.dedup();
    for range_id in negative_data_range_ids {
        let key = negated_data_range_predicate_key(range_id);
        budget.claim_owned(size_of::<PendingPredicate>())?;
        budget.claim_owned(key.len())?;
        ordered.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("negated data-range predicate allocation failed")
        })?;
        ordered.push(PendingPredicate {
            key,
            owner: PredicateOwner::NegatedDataRange(range_id),
        });
    }
    for disjoint in disjoints {
        let internal_key = crate::model::hex(&disjoint.guard_digest);
        budget.claim_owned(internal_key.len())?;
        for index in 0..disjoint.classes.len() {
            let sequence = u32::try_from(index).map_err(|_| {
                EncodedValidationError::resource("disjoint-guard sequence exceeds u32")
            })?;
            let key = disjoint_guard_predicate_key(sequence, &internal_key);
            budget.claim_owned(size_of::<PendingPredicate>())?;
            budget.claim_owned(key.len())?;
            budget.claim_owned(internal_key.len())?;
            ordered.try_reserve(1).map_err(|_| {
                EncodedValidationError::resource(
                    "disjoint-guard predicate ordering allocation failed",
                )
            })?;
            ordered.push(PendingPredicate {
                key,
                owner: PredicateOwner::DisjointGuard {
                    digest: disjoint.guard_digest,
                    sequence,
                    internal_key: internal_key.clone(),
                },
            });
        }
    }
    budget.claim_work(sort_work(ordered.len()))?;
    ordered.sort_by(|left, right| left.key.cmp(&right.key));
    PhaseBudget::count(
        ordered.len(),
        budget.limits.max_predicates,
        "predicate count",
    )?;

    let mut predicates = Vec::new();
    let mut predicate_by_class = Vec::new();
    let mut predicate_by_negative_class = Vec::new();
    let mut predicate_by_object_role = Vec::new();
    let mut predicate_by_negative_object_role = Vec::new();
    let mut predicate_by_data_role = Vec::new();
    let mut predicate_by_negative_data_role = Vec::new();
    let mut predicate_by_data_range = Vec::new();
    let mut predicate_by_negative_data_range = Vec::new();
    let mut guard_predicates = Vec::new();
    let mut named_predicate = None;
    let mut equality_predicate = None;
    let mut data_equality_predicate = None;
    let mut inequality_predicate = None;
    let mut data_inequality_predicate = None;
    let mut ordering_predicate = None;
    budget.claim_owned(
        ordered
            .len()
            .checked_mul(
                size_of::<DecodedPredicate>()
                    + 7 * size_of::<(u32, u32)>()
                    + size_of::<([u8; 32], u32, u32)>()
                    + size_of::<TermSort>(),
            )
            .ok_or_else(|| {
                EncodedValidationError::resource("named-class predicate output overflowed")
            })?,
    )?;
    predicates.try_reserve_exact(ordered.len()).map_err(|_| {
        EncodedValidationError::resource("named-class predicate output allocation failed")
    })?;
    predicate_by_class
        .try_reserve_exact(ordered.len())
        .map_err(|_| {
            EncodedValidationError::resource("named-class predicate index allocation failed")
        })?;
    predicate_by_negative_class
        .try_reserve_exact(ordered.len())
        .map_err(|_| {
            EncodedValidationError::resource(
                "negated named-class predicate index allocation failed",
            )
        })?;
    predicate_by_object_role
        .try_reserve_exact(ordered.len())
        .map_err(|_| {
            EncodedValidationError::resource("object-role predicate index allocation failed")
        })?;
    predicate_by_negative_object_role
        .try_reserve_exact(ordered.len())
        .map_err(|_| {
            EncodedValidationError::resource(
                "negated object-role predicate index allocation failed",
            )
        })?;
    predicate_by_data_role
        .try_reserve_exact(ordered.len())
        .map_err(|_| {
            EncodedValidationError::resource("data-role predicate index allocation failed")
        })?;
    predicate_by_negative_data_role
        .try_reserve_exact(ordered.len())
        .map_err(|_| {
            EncodedValidationError::resource("negated data-role predicate index allocation failed")
        })?;
    predicate_by_data_range
        .try_reserve_exact(ordered.len())
        .map_err(|_| {
            EncodedValidationError::resource("data-range predicate index allocation failed")
        })?;
    guard_predicates
        .try_reserve_exact(ordered.len())
        .map_err(|_| {
            EncodedValidationError::resource("disjoint-guard predicate index allocation failed")
        })?;
    for (identifier, pending) in ordered.into_iter().enumerate() {
        let predicate_id = u32::try_from(identifier).map_err(|_| {
            EncodedValidationError::resource("named-class predicate ID exceeds u32")
        })?;
        match pending.owner {
            PredicateOwner::Concept(class_id) => {
                predicates.push(DecodedPredicate {
                    predicate_id,
                    kind: PredicateKind::Concept,
                    argument_sorts: vec![TermSort::Object],
                    symbol_id: Some(class_id),
                    role_id: None,
                    cardinality: None,
                    filler_predicate_id: None,
                    annotation: Vec::new(),
                    internal_key: None,
                });
                predicate_by_class.push((class_id, predicate_id));
            }
            PredicateOwner::NegatedConcept(class_id) => {
                predicates.push(DecodedPredicate {
                    predicate_id,
                    kind: PredicateKind::NegatedConcept,
                    argument_sorts: vec![TermSort::Object],
                    symbol_id: Some(class_id),
                    role_id: None,
                    cardinality: None,
                    filler_predicate_id: None,
                    annotation: Vec::new(),
                    internal_key: None,
                });
                predicate_by_negative_class.push((class_id, predicate_id));
            }
            PredicateOwner::Nominal {
                class_id,
                individual_ids,
            } => {
                predicates.push(DecodedPredicate {
                    predicate_id,
                    kind: PredicateKind::Nominal,
                    argument_sorts: vec![TermSort::Object],
                    symbol_id: Some(class_id),
                    role_id: None,
                    cardinality: None,
                    filler_predicate_id: None,
                    annotation: individual_ids,
                    internal_key: None,
                });
                predicate_by_class.push((class_id, predicate_id));
            }
            PredicateOwner::NegatedNominal {
                class_id,
                individual_ids,
            } => {
                predicates.push(DecodedPredicate {
                    predicate_id,
                    kind: PredicateKind::NegatedNominal,
                    argument_sorts: vec![TermSort::Object],
                    symbol_id: Some(class_id),
                    role_id: None,
                    cardinality: None,
                    filler_predicate_id: None,
                    annotation: individual_ids,
                    internal_key: None,
                });
                predicate_by_negative_class.push((class_id, predicate_id));
            }
            PredicateOwner::ObjectRole(role_id) => {
                budget.claim_owned(size_of::<TermSort>())?;
                predicates.push(DecodedPredicate {
                    predicate_id,
                    kind: PredicateKind::ObjectRole,
                    argument_sorts: vec![TermSort::Object, TermSort::Object],
                    symbol_id: None,
                    role_id: Some(role_id),
                    cardinality: None,
                    filler_predicate_id: None,
                    annotation: Vec::new(),
                    internal_key: None,
                });
                predicate_by_object_role.push((role_id, predicate_id));
            }
            PredicateOwner::NegatedObjectRole(role_id) => {
                budget.claim_owned(size_of::<TermSort>())?;
                predicates.push(DecodedPredicate {
                    predicate_id,
                    kind: PredicateKind::NegatedObjectRole,
                    argument_sorts: vec![TermSort::Object, TermSort::Object],
                    symbol_id: None,
                    role_id: Some(role_id),
                    cardinality: None,
                    filler_predicate_id: None,
                    annotation: Vec::new(),
                    internal_key: None,
                });
                predicate_by_negative_object_role.push((role_id, predicate_id));
            }
            PredicateOwner::DataRole(role_id) => {
                budget.claim_owned(size_of::<TermSort>())?;
                predicates.push(DecodedPredicate {
                    predicate_id,
                    kind: PredicateKind::DataRole,
                    argument_sorts: vec![TermSort::Object, TermSort::Data],
                    symbol_id: None,
                    role_id: Some(role_id),
                    cardinality: None,
                    filler_predicate_id: None,
                    annotation: Vec::new(),
                    internal_key: None,
                });
                predicate_by_data_role.push((role_id, predicate_id));
            }
            PredicateOwner::NegatedDataRole(role_id) => {
                budget.claim_owned(size_of::<TermSort>())?;
                predicates.push(DecodedPredicate {
                    predicate_id,
                    kind: PredicateKind::NegatedDataRole,
                    argument_sorts: vec![TermSort::Object, TermSort::Data],
                    symbol_id: None,
                    role_id: Some(role_id),
                    cardinality: None,
                    filler_predicate_id: None,
                    annotation: Vec::new(),
                    internal_key: None,
                });
                predicate_by_negative_data_role.push((role_id, predicate_id));
            }
            PredicateOwner::DataRange(range_id) => {
                predicates.push(DecodedPredicate {
                    predicate_id,
                    kind: PredicateKind::DataRange,
                    argument_sorts: vec![TermSort::Data],
                    symbol_id: Some(range_id),
                    role_id: None,
                    cardinality: None,
                    filler_predicate_id: None,
                    annotation: Vec::new(),
                    internal_key: None,
                });
                predicate_by_data_range.push((range_id, predicate_id));
            }
            PredicateOwner::NegatedDataRange(range_id) => {
                predicates.push(DecodedPredicate {
                    predicate_id,
                    kind: PredicateKind::NegatedDataRange,
                    argument_sorts: vec![TermSort::Data],
                    symbol_id: Some(range_id),
                    role_id: None,
                    cardinality: None,
                    filler_predicate_id: None,
                    annotation: Vec::new(),
                    internal_key: None,
                });
                predicate_by_negative_data_range.push((range_id, predicate_id));
            }
            PredicateOwner::Equality(sort) => {
                budget.claim_owned(size_of::<TermSort>())?;
                predicates.push(DecodedPredicate {
                    predicate_id,
                    kind: PredicateKind::Equality,
                    argument_sorts: vec![sort, sort],
                    symbol_id: None,
                    role_id: None,
                    cardinality: None,
                    filler_predicate_id: None,
                    annotation: Vec::new(),
                    internal_key: None,
                });
                match sort {
                    TermSort::Object => equality_predicate = Some(predicate_id),
                    TermSort::Data => data_equality_predicate = Some(predicate_id),
                }
            }
            PredicateOwner::Inequality(sort) => {
                budget.claim_owned(size_of::<TermSort>())?;
                predicates.push(DecodedPredicate {
                    predicate_id,
                    kind: PredicateKind::Inequality,
                    argument_sorts: vec![sort, sort],
                    symbol_id: None,
                    role_id: None,
                    cardinality: None,
                    filler_predicate_id: None,
                    annotation: Vec::new(),
                    internal_key: None,
                });
                match sort {
                    TermSort::Object => inequality_predicate = Some(predicate_id),
                    TermSort::Data => data_inequality_predicate = Some(predicate_id),
                }
            }
            PredicateOwner::OrderingGuard => {
                budget.claim_owned(size_of::<TermSort>() + "canonical-object-order".len())?;
                predicates.push(DecodedPredicate {
                    predicate_id,
                    kind: PredicateKind::OrderingGuard,
                    argument_sorts: vec![TermSort::Object, TermSort::Object],
                    symbol_id: None,
                    role_id: None,
                    cardinality: None,
                    filler_predicate_id: None,
                    annotation: Vec::new(),
                    internal_key: Some("canonical-object-order".to_owned()),
                });
                ordering_predicate = Some(predicate_id);
            }
            PredicateOwner::NamedIndividual => {
                budget.claim_owned("named-individual".len())?;
                predicates.push(DecodedPredicate {
                    predicate_id,
                    kind: PredicateKind::NamedIndividual,
                    argument_sorts: vec![TermSort::Object],
                    symbol_id: None,
                    role_id: None,
                    cardinality: None,
                    filler_predicate_id: None,
                    annotation: Vec::new(),
                    internal_key: Some("named-individual".to_owned()),
                });
                named_predicate = Some(predicate_id);
            }
            PredicateOwner::DisjointGuard {
                digest,
                sequence,
                internal_key,
            } => {
                budget.claim_owned(size_of::<u32>())?;
                predicates.push(DecodedPredicate {
                    predicate_id,
                    kind: PredicateKind::DisjointGuard,
                    argument_sorts: vec![TermSort::Object],
                    symbol_id: None,
                    role_id: None,
                    cardinality: None,
                    filler_predicate_id: None,
                    annotation: vec![sequence],
                    internal_key: Some(internal_key),
                });
                guard_predicates.push((digest, sequence, predicate_id));
            }
        }
    }
    predicate_by_class.sort_unstable_by_key(|(class_id, _)| *class_id);
    predicate_by_negative_class.sort_unstable_by_key(|(class_id, _)| *class_id);
    predicate_by_object_role.sort_unstable_by_key(|(role_id, _)| *role_id);
    predicate_by_negative_object_role.sort_unstable_by_key(|(role_id, _)| *role_id);
    predicate_by_data_role.sort_unstable_by_key(|(role_id, _)| *role_id);
    predicate_by_negative_data_role.sort_unstable_by_key(|(role_id, _)| *role_id);
    predicate_by_data_range.sort_unstable_by_key(|(range_id, _)| *range_id);
    predicate_by_negative_data_range.sort_unstable_by_key(|(range_id, _)| *range_id);
    guard_predicates.sort_unstable_by_key(|(digest, sequence, _)| (*digest, *sequence));
    Ok((
        predicates,
        predicate_by_class,
        predicate_by_negative_class,
        predicate_by_object_role,
        predicate_by_negative_object_role,
        predicate_by_data_role,
        predicate_by_negative_data_role,
        predicate_by_data_range,
        predicate_by_negative_data_range,
        guard_predicates,
        named_predicate,
        equality_predicate,
        data_equality_predicate,
        inequality_predicate,
        data_inequality_predicate,
        ordering_predicate,
    ))
}

#[allow(clippy::too_many_arguments)]
fn freeze_clauses(
    nominal_bindings: &[NominalBinding],
    edges: &[NormalizedEdge],
    disjoints: &[NormalizedDisjoint],
    object_constraints: &[NormalizedObjectConstraint],
    object_characteristics: &[NormalizedObjectCharacteristic],
    data_domains: &[NormalizedDataDomain],
    data_ranges: &[NormalizedDataRange],
    datatype_definitions: &[NormalizedDatatypeDefinition],
    keys: &[NormalizedKey],
    data_functionalities: &[NormalizedDataFunctionality],
    facts: &[NormalizedFact],
    thing: u32,
    nothing: u32,
    top_data_range: u32,
    predicate_by_class: &[(u32, u32)],
    predicate_by_negative_class: &[(u32, u32)],
    predicate_by_object_role: &[(u32, u32)],
    predicate_by_data_role: &[(u32, u32)],
    predicate_by_data_range: &[(u32, u32)],
    predicate_by_negative_data_range: &[(u32, u32)],
    equality_predicate: Option<u32>,
    inequality_predicate: Option<u32>,
    data_equality_predicate: Option<u32>,
    data_inequality_predicate: Option<u32>,
    ordering_predicate: Option<u32>,
    named_predicate: Option<u32>,
    guard_predicates: &[([u8; 32], u32, u32)],
    scalar_predicate_ids: &[u32],
    provenance_keys: &[ProvenanceKey],
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<DecodedClause>> {
    let mut negative_class_ids = Vec::new();
    for edge in edges {
        if edge.sub_negative {
            push_u32(
                &mut negative_class_ids,
                edge.sub_class,
                "complement clause class",
                budget,
            )?;
        }
        if edge.super_negative {
            push_u32(
                &mut negative_class_ids,
                edge.super_class,
                "complement clause class",
                budget,
            )?;
        }
    }
    for disjoint in disjoints {
        for literal in disjoint.classes.iter().filter(|literal| literal.negative) {
            push_u32(
                &mut negative_class_ids,
                literal.class_id,
                "complement clause class",
                budget,
            )?;
        }
    }
    for constraint in object_constraints
        .iter()
        .filter(|constraint| constraint.class.negative)
    {
        push_u32(
            &mut negative_class_ids,
            constraint.class.class_id,
            "complement clause class",
            budget,
        )?;
    }
    for domain in data_domains.iter().filter(|domain| domain.class.negative) {
        push_u32(
            &mut negative_class_ids,
            domain.class.class_id,
            "complement clause class",
            budget,
        )?;
    }
    for key in keys.iter().filter(|key| key.class.negative) {
        push_u32(
            &mut negative_class_ids,
            key.class.class_id,
            "complement clause class",
            budget,
        )?;
    }
    for fact in facts.iter().filter(|fact| fact.negative) {
        push_u32(
            &mut negative_class_ids,
            fact.class_id,
            "complement clause class",
            budget,
        )?;
    }
    budget.claim_work(sort_work(negative_class_ids.len()))?;
    negative_class_ids.sort_unstable();
    negative_class_ids.dedup();
    let mut negative_data_range_ids = Vec::new();
    for range in data_ranges.iter().filter(|range| range.range.negative) {
        push_u32(
            &mut negative_data_range_ids,
            range.range.range_id,
            "complement clause data range",
            budget,
        )?;
    }
    for definition in datatype_definitions {
        for range in [definition.left_range, definition.right_range]
            .into_iter()
            .filter(|range| range.negative)
        {
            push_u32(
                &mut negative_data_range_ids,
                range.range_id,
                "complement clause data range",
                budget,
            )?;
        }
    }
    budget.claim_work(sort_work(negative_data_range_ids.len()))?;
    negative_data_range_ids.sort_unstable();
    negative_data_range_ids.dedup();
    let nominal_clause_count = nominal_bindings
        .iter()
        .try_fold(0_usize, |count, binding| {
            let positive = binding.individual_ids.len().checked_add(1).ok_or_else(|| {
                EncodedValidationError::resource("object nominal clause count overflowed")
            })?;
            let negative = if negative_class_ids.binary_search(&binding.class_id).is_ok() {
                binding.individual_ids.len()
            } else {
                0
            };
            count
                .checked_add(positive)
                .and_then(|value| value.checked_add(negative))
                .ok_or_else(|| {
                    EncodedValidationError::resource("object nominal clause count overflowed")
                })
        })?;
    let datatype_definition_clauses =
        datatype_definitions
            .iter()
            .try_fold(0_usize, |count, definition| {
                count
                    .checked_add(usize::from(definition.left_range != definition.right_range) * 2)
                    .ok_or_else(|| {
                        EncodedValidationError::resource(
                            "datatype-definition clause count overflowed",
                        )
                    })
            })?;
    let mut following = edges
        .len()
        .checked_add(1)
        .and_then(|value| value.checked_add(object_constraints.len()))
        .and_then(|value| value.checked_add(object_characteristics.len()))
        .and_then(|value| value.checked_add(data_domains.len()))
        .and_then(|value| value.checked_add(data_ranges.len()))
        .and_then(|value| value.checked_add(datatype_definition_clauses))
        .and_then(|value| value.checked_add(keys.len()))
        .and_then(|value| value.checked_add(data_functionalities.len()))
        .and_then(|value| value.checked_add(nominal_clause_count))
        .and_then(|value| value.checked_add(negative_class_ids.len().checked_mul(2)?))
        .and_then(|value| value.checked_add(negative_data_range_ids.len().checked_mul(2)?))
        .ok_or_else(|| EncodedValidationError::resource("named-class clause count overflowed"))?;
    for disjoint in disjoints {
        let count = disjoint
            .classes
            .len()
            .checked_mul(3)
            .and_then(|value| value.checked_sub(2))
            .ok_or_else(|| {
                EncodedValidationError::resource("disjoint-class clause count overflowed")
            })?;
        following = following.checked_add(count).ok_or_else(|| {
            EncodedValidationError::resource("named-class clause count overflowed")
        })?;
    }
    PhaseBudget::count(following, budget.limits.max_clauses, "clause count")?;
    let builtin: [u8; 32] = Sha256::digest(BUILTIN_PROVENANCE_INPUT).into();
    let mut ordered = Vec::<(Vec<u8>, DecodedClause)>::new();
    let bottom_predicate = predicate_id(predicate_by_class, nothing)?;
    let bottom_provenance = provenance_id(provenance_keys, &[builtin], true)?;
    push_clause(
        &mut ordered,
        &[bottom_predicate],
        &[],
        bottom_provenance,
        scalar_predicate_ids,
        budget,
    )?;
    if !negative_class_ids.is_empty() {
        let thing_predicate = predicate_id(predicate_by_class, thing)?;
        for class_id in negative_class_ids.iter().copied() {
            let positive = predicate_id(predicate_by_class, class_id)?;
            let negative = predicate_id(predicate_by_negative_class, class_id)?;
            push_clause(
                &mut ordered,
                &[positive, negative],
                &[],
                bottom_provenance,
                scalar_predicate_ids,
                budget,
            )?;
            push_clause(
                &mut ordered,
                &[thing_predicate],
                &[positive, negative],
                bottom_provenance,
                scalar_predicate_ids,
                budget,
            )?;
        }
    }
    if !nominal_bindings.is_empty() {
        let equality = equality_predicate.ok_or_else(|| {
            EncodedValidationError::invariant("object nominal lost the equality predicate")
        })?;
        for binding in nominal_bindings {
            let positive = predicate_id(predicate_by_class, binding.class_id)?;
            let negative = if negative_class_ids.binary_search(&binding.class_id).is_ok() {
                Some(predicate_id(predicate_by_negative_class, binding.class_id)?)
            } else {
                None
            };
            push_nominal_clauses(
                &mut ordered,
                positive,
                negative,
                equality,
                inequality_predicate,
                &binding.individual_ids,
                bottom_provenance,
                scalar_predicate_ids,
                budget,
            )?;
        }
    }
    if !negative_data_range_ids.is_empty() {
        let universal = predicate_id(predicate_by_data_range, top_data_range)?;
        for range_id in negative_data_range_ids {
            let positive = predicate_id(predicate_by_data_range, range_id)?;
            let negative = predicate_id(predicate_by_negative_data_range, range_id)?;
            push_typed_clause(
                &mut ordered,
                &[positive, negative],
                &[],
                TermSort::Data,
                bottom_provenance,
                scalar_predicate_ids,
                budget,
            )?;
            push_typed_clause(
                &mut ordered,
                &[universal],
                &[positive, negative],
                TermSort::Data,
                bottom_provenance,
                scalar_predicate_ids,
                budget,
            )?;
        }
    }
    for edge in edges {
        let body = class_literal_predicate_id(
            predicate_by_class,
            predicate_by_negative_class,
            edge.sub_class,
            edge.sub_negative,
        )?;
        let head = class_literal_predicate_id(
            predicate_by_class,
            predicate_by_negative_class,
            edge.super_class,
            edge.super_negative,
        )?;
        let provenance = provenance_id(provenance_keys, &edge.provenance, false)?;
        push_clause(
            &mut ordered,
            &[body],
            &[head],
            provenance,
            scalar_predicate_ids,
            budget,
        )?;
    }
    for constraint in object_constraints {
        let role = object_predicate_id(predicate_by_object_role, constraint.role_id)?;
        let class = class_literal_predicate_id(
            predicate_by_class,
            predicate_by_negative_class,
            constraint.class.class_id,
            constraint.class.negative,
        )?;
        let provenance = provenance_id(provenance_keys, &constraint.provenance, false)?;
        push_object_constraint_clause(
            &mut ordered,
            role,
            class,
            constraint.kind,
            provenance,
            budget,
        )?;
    }
    for characteristic in object_characteristics {
        let role = object_predicate_id(predicate_by_object_role, characteristic.role_id)?;
        let provenance = provenance_id(provenance_keys, &characteristic.provenance, false)?;
        let thing_predicate = if characteristic.kind == ObjectCharacteristicKind::Reflexive {
            Some(predicate_id(predicate_by_class, thing)?)
        } else {
            None
        };
        push_object_characteristic_clause(
            &mut ordered,
            role,
            equality_predicate,
            thing_predicate,
            characteristic.kind,
            provenance,
            budget,
        )?;
    }
    for domain in data_domains {
        let role = data_predicate_id(predicate_by_data_role, domain.role_id)?;
        let class = class_literal_predicate_id(
            predicate_by_class,
            predicate_by_negative_class,
            domain.class.class_id,
            domain.class.negative,
        )?;
        let provenance = provenance_id(provenance_keys, &domain.provenance, false)?;
        push_data_domain_clause(&mut ordered, role, class, provenance, budget)?;
    }
    for range in data_ranges {
        let role = data_predicate_id(predicate_by_data_role, range.role_id)?;
        let data_range = data_range_literal_predicate_id(
            predicate_by_data_range,
            predicate_by_negative_data_range,
            range.range,
        )?;
        let provenance = provenance_id(provenance_keys, &range.provenance, false)?;
        push_data_range_clause(&mut ordered, role, data_range, provenance, budget)?;
    }
    for definition in datatype_definitions {
        let left = data_range_literal_predicate_id(
            predicate_by_data_range,
            predicate_by_negative_data_range,
            definition.left_range,
        )?;
        let right = data_range_literal_predicate_id(
            predicate_by_data_range,
            predicate_by_negative_data_range,
            definition.right_range,
        )?;
        let provenance = provenance_id(provenance_keys, &definition.provenance, false)?;
        push_datatype_definition_clause(&mut ordered, left, right, provenance, budget)?;
        push_datatype_definition_clause(&mut ordered, right, left, provenance, budget)?;
    }
    for key in keys {
        let class = class_literal_predicate_id(
            predicate_by_class,
            predicate_by_negative_class,
            key.class.class_id,
            key.class.negative,
        )?;
        let mut object_roles = Vec::new();
        budget.claim_owned(
            key.object_role_ids
                .len()
                .checked_mul(size_of::<u32>())
                .ok_or_else(|| {
                    EncodedValidationError::resource("has-key object predicate IDs overflowed")
                })?,
        )?;
        object_roles
            .try_reserve_exact(key.object_role_ids.len())
            .map_err(|_| {
                EncodedValidationError::resource("has-key object predicate allocation failed")
            })?;
        for role_id in &key.object_role_ids {
            object_roles.push(object_predicate_id(predicate_by_object_role, *role_id)?);
        }
        let mut data_roles = Vec::new();
        budget.claim_owned(
            key.data_role_ids
                .len()
                .checked_mul(size_of::<u32>())
                .ok_or_else(|| {
                    EncodedValidationError::resource("has-key data predicate IDs overflowed")
                })?,
        )?;
        data_roles
            .try_reserve_exact(key.data_role_ids.len())
            .map_err(|_| {
                EncodedValidationError::resource("has-key data predicate allocation failed")
            })?;
        for role_id in &key.data_role_ids {
            data_roles.push(data_predicate_id(predicate_by_data_role, *role_id)?);
        }
        let provenance = provenance_id(provenance_keys, &key.provenance, false)?;
        push_key_clause(
            &mut ordered,
            class,
            &object_roles,
            &data_roles,
            equality_predicate,
            data_inequality_predicate,
            ordering_predicate,
            named_predicate,
            provenance,
            scalar_predicate_ids,
            budget,
        )?;
    }
    for functionality in data_functionalities {
        let role = data_predicate_id(predicate_by_data_role, functionality.role_id)?;
        let equality = data_equality_predicate.ok_or_else(|| {
            EncodedValidationError::invariant(
                "functional data-property clause lost the data equality predicate",
            )
        })?;
        let provenance = provenance_id(provenance_keys, &functionality.provenance, false)?;
        push_data_functionality_clause(&mut ordered, role, equality, provenance, budget)?;
    }
    for disjoint in disjoints {
        let provenance = provenance_id(provenance_keys, &disjoint.provenance, false)?;
        let mut previous = None;
        for (index, literal) in disjoint.classes.iter().copied().enumerate() {
            let sequence = u32::try_from(index).map_err(|_| {
                EncodedValidationError::resource("disjoint-guard sequence exceeds u32")
            })?;
            let current = guard_predicate_id(guard_predicates, disjoint.guard_digest, sequence)?;
            let member = class_literal_predicate_id(
                predicate_by_class,
                predicate_by_negative_class,
                literal.class_id,
                literal.negative,
            )?;
            if let Some(previous_id) = previous {
                push_clause(
                    &mut ordered,
                    &[previous_id, member],
                    &[],
                    provenance,
                    scalar_predicate_ids,
                    budget,
                )?;
                push_clause(
                    &mut ordered,
                    &[previous_id],
                    &[current],
                    provenance,
                    scalar_predicate_ids,
                    budget,
                )?;
            }
            push_clause(
                &mut ordered,
                &[member],
                &[current],
                provenance,
                scalar_predicate_ids,
                budget,
            )?;
            previous = Some(current);
        }
    }
    budget.claim_work(sort_work(ordered.len()))?;
    ordered.sort_by(|left, right| left.0.cmp(&right.0));
    let mut clauses = Vec::new();
    budget.claim_owned(
        ordered
            .len()
            .checked_mul(size_of::<DecodedClause>())
            .ok_or_else(|| {
                EncodedValidationError::resource("named-class clause output overflowed")
            })?,
    )?;
    clauses.try_reserve_exact(ordered.len()).map_err(|_| {
        EncodedValidationError::resource("named-class clause output allocation failed")
    })?;
    for (identifier, (_, mut clause)) in ordered.into_iter().enumerate() {
        clause.clause_id = u32::try_from(identifier)
            .map_err(|_| EncodedValidationError::resource("named-class clause ID exceeds u32"))?;
        clauses.push(clause);
    }
    Ok(clauses)
}

#[allow(clippy::too_many_arguments)]
fn freeze_positive_facts(
    facts: &[NormalizedFact],
    object_facts: &[NormalizedObjectFact],
    data_facts: &[NormalizedDataFact],
    equalities: &[NormalizedEqualityFact],
    inequalities: &[NormalizedInequalityFact],
    individual_domain: &DecodedSymbolDomain,
    thing: u32,
    predicate_by_class: &[(u32, u32)],
    predicate_by_object_role: &[(u32, u32)],
    predicate_by_data_role: &[(u32, u32)],
    source_literal_domain: &DecodedSymbolDomain,
    data_value_domain: &DecodedSymbolDomain,
    source_data_identity_ids: &[Option<u32>],
    named_individuals: &[u32],
    named_predicate: Option<u32>,
    equality_predicate: Option<u32>,
    nominal_usage: NominalUsage,
    has_object_functionality: bool,
    has_keys: bool,
    inequality_predicate: Option<u32>,
    provenance_keys: &[ProvenanceKey],
    scalar_predicate_ids: &[u32],
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<DecodedGroundAtom>> {
    if source_literal_domain.kind != SymbolKind::SourceLiteral
        || data_value_domain.kind != SymbolKind::DataValue
        || source_data_identity_ids.len() != source_literal_domain.values.len()
    {
        return Err(EncodedValidationError::invariant(
            "positive data-fact symbol domains are inconsistent",
        ));
    }
    let builtin: [u8; 32] = Sha256::digest(BUILTIN_PROVENANCE_INPUT).into();
    let builtin_provenance = provenance_id(provenance_keys, &[builtin], true)?;
    let thing_predicate = if individual_domain.values.is_empty() {
        None
    } else {
        Some(predicate_id(predicate_by_class, thing)?)
    };
    if !named_individuals.windows(2).all(|pair| pair[0] < pair[1])
        || named_individuals.iter().any(|identifier| {
            usize::try_from(*identifier).ok().is_none_or(|index| {
                individual_domain
                    .values
                    .get(index)
                    .is_none_or(|value| !value.display.starts_with(NAMED_INDIVIDUAL_PREFIX))
            })
        })
    {
        return Err(EncodedValidationError::invariant(
            "named-individual IDs are not a canonical subset of their domain",
        ));
    }
    let named_predicate = match (named_individuals.is_empty(), has_keys, named_predicate) {
        (true, false, None) | (true, true, Some(_)) => None,
        (false, _, Some(identifier)) => Some(identifier),
        _ => {
            return Err(EncodedValidationError::invariant(
                "named-individual predicate presence disagrees with its signature",
            ));
        }
    };
    let equality_predicate = match (
        equalities.is_empty()
            && nominal_usage == NominalUsage::None
            && !has_object_functionality
            && !has_keys,
        equality_predicate,
    ) {
        (true, None) => None,
        (false, Some(identifier)) => Some(identifier),
        _ => {
            return Err(EncodedValidationError::invariant(
                "equality predicate presence disagrees with equality facts",
            ));
        }
    };
    let inequality_predicate = match (
        inequalities.is_empty() && nominal_usage != NominalUsage::Negative,
        inequality_predicate,
    ) {
        (true, None) => None,
        (false, Some(identifier)) => Some(identifier),
        _ => {
            return Err(EncodedValidationError::invariant(
                "inequality predicate presence disagrees with inequality facts",
            ));
        }
    };
    let positive_class_facts = facts.iter().filter(|fact| !fact.negative).count();
    let expected = individual_domain
        .values
        .len()
        .checked_add(named_individuals.len())
        .and_then(|value| value.checked_add(positive_class_facts))
        .and_then(|value| value.checked_add(object_facts.len()))
        .and_then(|value| value.checked_add(data_facts.len()))
        .and_then(|value| value.checked_add(equalities.len()))
        .and_then(|value| value.checked_add(inequalities.len()))
        .ok_or_else(|| EncodedValidationError::resource("positive-fact count overflowed"))?;
    budget.claim_work(
        positive_class_facts
            .checked_add(object_facts.len())
            .and_then(|value| value.checked_add(data_facts.len()))
            .and_then(|value| value.checked_add(equalities.len()))
            .and_then(|value| value.checked_add(inequalities.len()))
            .ok_or_else(|| EncodedValidationError::resource("positive-fact work overflowed"))?,
    )?;
    let top_fact_count = facts
        .iter()
        .filter(|fact| !fact.negative && fact.class_id == thing)
        .count();
    let class_fact_count = positive_class_facts
        .checked_sub(top_fact_count)
        .ok_or_else(|| {
            EncodedValidationError::invariant("positive class-fact merge count underflowed")
        })?;
    let equality_fact_count = equalities
        .iter()
        .enumerate()
        .filter(|(index, equality)| {
            *index == 0
                || equalities[*index - 1].left_individual != equality.left_individual
                || equalities[*index - 1].right_individual != equality.right_individual
        })
        .count();
    let inequality_fact_count = inequalities
        .iter()
        .enumerate()
        .filter(|(index, inequality)| {
            *index == 0
                || inequalities[*index - 1].left_individual != inequality.left_individual
                || inequalities[*index - 1].right_individual != inequality.right_individual
        })
        .count();
    let merged_count = individual_domain
        .values
        .len()
        .checked_add(named_individuals.len())
        .and_then(|value| value.checked_add(class_fact_count))
        .and_then(|value| value.checked_add(object_facts.len()))
        .and_then(|value| value.checked_add(data_facts.len()))
        .and_then(|value| value.checked_add(equality_fact_count))
        .and_then(|value| value.checked_add(inequality_fact_count))
        .ok_or_else(|| EncodedValidationError::resource("positive-fact merge count overflowed"))?;
    PhaseBudget::count(merged_count, budget.limits.max_facts, "positive fact count")?;
    let mut pending = Vec::<(u32, GroundArguments, u32)>::new();
    budget.claim_owned(
        expected
            .checked_mul(size_of::<(u32, GroundArguments, u32)>())
            .ok_or_else(|| EncodedValidationError::resource("positive-fact input overflowed"))?,
    )?;
    pending
        .try_reserve_exact(expected)
        .map_err(|_| EncodedValidationError::resource("positive-fact input allocation failed"))?;
    for individual in &individual_domain.values {
        budget.claim_work(1)?;
        let top = thing_predicate.ok_or_else(|| {
            EncodedValidationError::invariant("top concept predicate index is incomplete")
        })?;
        pending.push((
            top,
            GroundArguments::Unary(individual.identifier),
            builtin_provenance,
        ));
    }
    if let Some(named) = named_predicate {
        for individual_id in named_individuals {
            budget.claim_work(1)?;
            pending.push((
                named,
                GroundArguments::Unary(*individual_id),
                builtin_provenance,
            ));
        }
    }
    for fact in facts {
        if fact.negative {
            continue;
        }
        budget.claim_work(1)?;
        if usize::try_from(fact.individual_id)
            .ok()
            .is_none_or(|identifier| identifier >= individual_domain.values.len())
        {
            return Err(EncodedValidationError::invariant(
                "named class-assertion individual ID is dangling",
            ));
        }
        pending.push((
            predicate_id(predicate_by_class, fact.class_id)?,
            GroundArguments::Unary(fact.individual_id),
            provenance_id(provenance_keys, &fact.provenance, false)?,
        ));
    }
    for fact in object_facts {
        budget.claim_work(1)?;
        if [fact.source_individual, fact.target_individual]
            .into_iter()
            .any(|individual_id| {
                usize::try_from(individual_id)
                    .ok()
                    .is_none_or(|identifier| identifier >= individual_domain.values.len())
            })
        {
            return Err(EncodedValidationError::invariant(
                "named object-property assertion has a dangling individual ID",
            ));
        }
        pending.push((
            object_predicate_id(predicate_by_object_role, fact.role_id)?,
            GroundArguments::Binary(fact.source_individual, fact.target_individual),
            provenance_id(provenance_keys, &fact.provenance, false)?,
        ));
    }
    for fact in data_facts {
        budget.claim_work(1)?;
        if usize::try_from(fact.source_individual)
            .ok()
            .is_none_or(|identifier| identifier >= individual_domain.values.len())
        {
            return Err(EncodedValidationError::invariant(
                "named data-property assertion has a dangling individual ID",
            ));
        }
        let source_index = usize::try_from(fact.source_literal_id).map_err(|_| {
            EncodedValidationError::invariant(
                "named data-property assertion source-literal ID exceeds usize",
            )
        })?;
        if source_index >= source_literal_domain.values.len() {
            return Err(EncodedValidationError::invariant(
                "named data-property assertion has a dangling source-literal ID",
            ));
        }
        if usize::try_from(fact.data_identity_id)
            .ok()
            .is_none_or(|identifier| identifier >= data_value_domain.values.len())
        {
            return Err(EncodedValidationError::invariant(
                "named data-property assertion has a dangling data-identity ID",
            ));
        }
        if source_data_identity_ids[source_index] != Some(fact.data_identity_id) {
            return Err(EncodedValidationError::invariant(
                "named data-property assertion source and data identity disagree",
            ));
        }
        pending.push((
            data_predicate_id(predicate_by_data_role, fact.role_id)?,
            GroundArguments::DataBinary(
                fact.source_individual,
                fact.source_literal_id,
                fact.data_identity_id,
            ),
            provenance_id(provenance_keys, &fact.provenance, false)?,
        ));
    }
    for equality in equalities {
        budget.claim_work(1)?;
        if equality.left_individual >= equality.right_individual {
            return Err(EncodedValidationError::invariant(
                "named same-individual fact is not canonically oriented",
            ));
        }
        if [equality.left_individual, equality.right_individual]
            .into_iter()
            .any(|individual_id| {
                usize::try_from(individual_id)
                    .ok()
                    .is_none_or(|identifier| identifier >= individual_domain.values.len())
            })
        {
            return Err(EncodedValidationError::invariant(
                "named same-individual fact has a dangling individual ID",
            ));
        }
        let predicate = equality_predicate.ok_or_else(|| {
            EncodedValidationError::invariant("equality predicate index is incomplete")
        })?;
        pending.push((
            predicate,
            GroundArguments::Binary(equality.left_individual, equality.right_individual),
            provenance_id(provenance_keys, &equality.provenance, false)?,
        ));
    }
    for inequality in inequalities {
        budget.claim_work(1)?;
        if inequality.left_individual >= inequality.right_individual {
            return Err(EncodedValidationError::invariant(
                "named different-individual fact is not canonically oriented",
            ));
        }
        if [inequality.left_individual, inequality.right_individual]
            .into_iter()
            .any(|individual_id| {
                usize::try_from(individual_id)
                    .ok()
                    .is_none_or(|identifier| identifier >= individual_domain.values.len())
            })
        {
            return Err(EncodedValidationError::invariant(
                "named different-individual fact has a dangling individual ID",
            ));
        }
        let predicate = inequality_predicate.ok_or_else(|| {
            EncodedValidationError::invariant("inequality predicate index is incomplete")
        })?;
        pending.push((
            predicate,
            GroundArguments::Binary(inequality.left_individual, inequality.right_individual),
            provenance_id(provenance_keys, &inequality.provenance, false)?,
        ));
    }
    budget.claim_work(sort_work(pending.len()))?;
    pending.sort_unstable();

    let mut merged = Vec::<(u32, GroundArguments, Vec<u32>)>::new();
    for (predicate, arguments, provenance) in pending {
        budget.claim_work(1)?;
        if let Some(previous) = merged.last_mut() {
            if previous.0 == predicate && previous.1 == arguments {
                if previous.2.last() != Some(&provenance) {
                    budget.claim_owned(size_of::<u32>())?;
                    previous.2.try_reserve(1).map_err(|_| {
                        EncodedValidationError::resource(
                            "positive-fact provenance allocation failed",
                        )
                    })?;
                    previous.2.push(provenance);
                }
                continue;
            }
        }
        budget.claim_owned(size_of::<(u32, GroundArguments, Vec<u32>)>() + size_of::<u32>())?;
        merged.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("positive-fact merge allocation failed")
        })?;
        let mut provenance_ids = Vec::new();
        provenance_ids.try_reserve_exact(1).map_err(|_| {
            EncodedValidationError::resource("positive-fact provenance allocation failed")
        })?;
        provenance_ids.push(provenance);
        merged.push((predicate, arguments, provenance_ids));
    }
    PhaseBudget::count(merged.len(), budget.limits.max_facts, "positive fact count")?;
    if merged.len() != merged_count {
        return Err(EncodedValidationError::invariant(
            "positive-fact merge count disagrees with its exact bound",
        ));
    }

    let mut ordered = Vec::<(Vec<u8>, DecodedGroundAtom)>::new();
    let binary_fact_count = merged
        .iter()
        .filter(|(_, arguments, _)| {
            matches!(
                arguments,
                GroundArguments::Binary(_, _) | GroundArguments::DataBinary(_, _, _)
            )
        })
        .count();
    let expected_binary_fact_count = equality_fact_count
        .checked_add(inequality_fact_count)
        .and_then(|value| value.checked_add(object_facts.len()))
        .and_then(|value| value.checked_add(data_facts.len()))
        .ok_or_else(|| EncodedValidationError::resource("binary-fact count overflowed"))?;
    if binary_fact_count != expected_binary_fact_count {
        return Err(EncodedValidationError::invariant(
            "binary-fact merge count disagrees with its exact bound",
        ));
    }
    let term_count = merged
        .len()
        .checked_add(binary_fact_count)
        .ok_or_else(|| EncodedValidationError::resource("positive-fact term count overflowed"))?;
    budget.claim_owned(
        merged
            .len()
            .checked_mul(size_of::<(Vec<u8>, DecodedGroundAtom)>())
            .and_then(|value| {
                term_count
                    .checked_mul(size_of::<DecodedTerm>())
                    .and_then(|term_bytes| value.checked_add(term_bytes))
            })
            .ok_or_else(|| EncodedValidationError::resource("positive-fact output overflowed"))?,
    )?;
    ordered
        .try_reserve_exact(merged.len())
        .map_err(|_| EncodedValidationError::resource("positive-fact output allocation failed"))?;
    for (predicate_id, arguments, provenance_ids) in merged {
        budget.claim_owned(
            provenance_ids
                .len()
                .checked_mul(size_of::<u32>())
                .ok_or_else(|| {
                    EncodedValidationError::resource("positive-fact provenance output overflowed")
                })?,
        )?;
        let scalar_predicate_id = scalar_predicate_ids
            .get(usize::try_from(predicate_id).map_err(|_| {
                EncodedValidationError::invariant("fact predicate ID exceeds usize")
            })?)
            .copied()
            .ok_or_else(|| {
                EncodedValidationError::invariant("scalar fact predicate mapping is incomplete")
            })?;
        let key = ground_fact_key(scalar_predicate_id, arguments, &provenance_ids);
        budget.claim_owned(key.len())?;
        let arguments = match arguments {
            GroundArguments::Unary(individual_id) => {
                vec![DecodedTerm::Individual { individual_id }]
            }
            GroundArguments::Binary(left_individual, right_individual) => vec![
                DecodedTerm::Individual {
                    individual_id: left_individual,
                },
                DecodedTerm::Individual {
                    individual_id: right_individual,
                },
            ],
            GroundArguments::DataBinary(source_individual, source_literal_id, data_identity_id) => {
                vec![
                    DecodedTerm::Individual {
                        individual_id: source_individual,
                    },
                    DecodedTerm::Data {
                        source_literal_id,
                        data_identity_id,
                    },
                ]
            }
        };
        ordered.push((
            key,
            DecodedGroundAtom {
                predicate_id,
                arguments,
                provenance_ids,
            },
        ));
    }
    budget.claim_work(sort_work(ordered.len()))?;
    ordered.sort_by(|left, right| left.0.cmp(&right.0));
    let mut output = Vec::new();
    budget.claim_owned(
        ordered
            .len()
            .checked_mul(size_of::<DecodedGroundAtom>())
            .ok_or_else(|| EncodedValidationError::resource("positive-fact result overflowed"))?,
    )?;
    output
        .try_reserve_exact(ordered.len())
        .map_err(|_| EncodedValidationError::resource("positive-fact result allocation failed"))?;
    output.extend(ordered.into_iter().map(|(_, fact)| fact));
    Ok(output)
}

#[allow(clippy::too_many_arguments)]
fn freeze_negative_facts(
    facts: &[NormalizedFact],
    object_facts: &[NormalizedObjectFact],
    data_facts: &[NormalizedDataFact],
    individual_domain: &DecodedSymbolDomain,
    predicate_by_negative_class: &[(u32, u32)],
    predicate_by_negative_object_role: &[(u32, u32)],
    predicate_by_negative_data_role: &[(u32, u32)],
    source_literal_domain: &DecodedSymbolDomain,
    data_value_domain: &DecodedSymbolDomain,
    source_data_identity_ids: &[Option<u32>],
    provenance_keys: &[ProvenanceKey],
    scalar_predicate_ids: &[u32],
    positive_fact_count: usize,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<DecodedGroundAtom>> {
    if source_literal_domain.kind != SymbolKind::SourceLiteral
        || data_value_domain.kind != SymbolKind::DataValue
        || source_data_identity_ids.len() != source_literal_domain.values.len()
    {
        return Err(EncodedValidationError::invariant(
            "negative data-fact symbol domains are inconsistent",
        ));
    }
    let negative_class_fact_count = facts.iter().filter(|fact| fact.negative).count();
    let negative_fact_count = negative_class_fact_count
        .checked_add(object_facts.len())
        .and_then(|value| value.checked_add(data_facts.len()))
        .ok_or_else(|| EncodedValidationError::resource("negative-fact count overflowed"))?;
    let total_fact_count = positive_fact_count
        .checked_add(negative_fact_count)
        .ok_or_else(|| EncodedValidationError::resource("ground-fact count overflowed"))?;
    PhaseBudget::count(
        total_fact_count,
        budget.limits.max_facts,
        "ground fact count",
    )?;
    budget.claim_work(
        negative_fact_count
            .checked_add(sort_work(negative_fact_count))
            .ok_or_else(|| EncodedValidationError::resource("negative-fact work overflowed"))?,
    )?;
    budget.claim_owned(
        negative_fact_count
            .checked_mul(size_of::<(Vec<u8>, DecodedGroundAtom)>())
            .ok_or_else(|| EncodedValidationError::resource("negative-fact input overflowed"))?,
    )?;
    let mut ordered = Vec::<(Vec<u8>, DecodedGroundAtom)>::new();
    ordered
        .try_reserve_exact(negative_fact_count)
        .map_err(|_| EncodedValidationError::resource("negative-fact input allocation failed"))?;
    for fact in facts.iter().filter(|fact| fact.negative) {
        if usize::try_from(fact.individual_id)
            .ok()
            .is_none_or(|identifier| identifier >= individual_domain.values.len())
        {
            return Err(EncodedValidationError::invariant(
                "negated class-assertion individual ID is dangling",
            ));
        }
        let predicate_id = predicate_id(predicate_by_negative_class, fact.class_id)?;
        let scalar_predicate_id = scalar_predicate_ids
            .get(usize::try_from(predicate_id).map_err(|_| {
                EncodedValidationError::invariant("negated class-fact predicate ID exceeds usize")
            })?)
            .copied()
            .ok_or_else(|| {
                EncodedValidationError::invariant(
                    "scalar negated class-fact predicate mapping is incomplete",
                )
            })?;
        let provenance_id = provenance_id(provenance_keys, &fact.provenance, false)?;
        let provenance_ids = vec![provenance_id];
        let arguments = GroundArguments::Unary(fact.individual_id);
        let key = ground_fact_key(scalar_predicate_id, arguments, &provenance_ids);
        budget.claim_owned(
            key.len()
                .checked_add(size_of::<u32>())
                .and_then(|value| value.checked_add(size_of::<DecodedTerm>()))
                .ok_or_else(|| {
                    EncodedValidationError::resource("negated class-fact payload overflowed")
                })?,
        )?;
        ordered.push((
            key,
            DecodedGroundAtom {
                predicate_id,
                arguments: vec![DecodedTerm::Individual {
                    individual_id: fact.individual_id,
                }],
                provenance_ids,
            },
        ));
    }
    for fact in object_facts {
        if [fact.source_individual, fact.target_individual]
            .into_iter()
            .any(|individual_id| {
                usize::try_from(individual_id)
                    .ok()
                    .is_none_or(|identifier| identifier >= individual_domain.values.len())
            })
        {
            return Err(EncodedValidationError::invariant(
                "named negative object-property assertion has a dangling individual ID",
            ));
        }
        let predicate_id = object_predicate_id(predicate_by_negative_object_role, fact.role_id)?;
        let scalar_predicate_id = scalar_predicate_ids
            .get(usize::try_from(predicate_id).map_err(|_| {
                EncodedValidationError::invariant("negative-fact predicate ID exceeds usize")
            })?)
            .copied()
            .ok_or_else(|| {
                EncodedValidationError::invariant(
                    "scalar negative-fact predicate mapping is incomplete",
                )
            })?;
        let provenance_id = provenance_id(provenance_keys, &fact.provenance, false)?;
        let provenance_ids = vec![provenance_id];
        let arguments = GroundArguments::Binary(fact.source_individual, fact.target_individual);
        let key = ground_fact_key(scalar_predicate_id, arguments, &provenance_ids);
        budget.claim_owned(
            key.len()
                .checked_add(size_of::<u32>())
                .and_then(|value| value.checked_add(2 * size_of::<DecodedTerm>()))
                .ok_or_else(|| {
                    EncodedValidationError::resource("negative-fact payload overflowed")
                })?,
        )?;
        ordered.push((
            key,
            DecodedGroundAtom {
                predicate_id,
                arguments: vec![
                    DecodedTerm::Individual {
                        individual_id: fact.source_individual,
                    },
                    DecodedTerm::Individual {
                        individual_id: fact.target_individual,
                    },
                ],
                provenance_ids,
            },
        ));
    }
    for fact in data_facts {
        if usize::try_from(fact.source_individual)
            .ok()
            .is_none_or(|identifier| identifier >= individual_domain.values.len())
        {
            return Err(EncodedValidationError::invariant(
                "named negative data-property assertion has a dangling individual ID",
            ));
        }
        let source_index = usize::try_from(fact.source_literal_id).map_err(|_| {
            EncodedValidationError::invariant(
                "named negative data-property assertion source-literal ID exceeds usize",
            )
        })?;
        if source_index >= source_literal_domain.values.len() {
            return Err(EncodedValidationError::invariant(
                "named negative data-property assertion has a dangling source-literal ID",
            ));
        }
        if usize::try_from(fact.data_identity_id)
            .ok()
            .is_none_or(|identifier| identifier >= data_value_domain.values.len())
        {
            return Err(EncodedValidationError::invariant(
                "named negative data-property assertion has a dangling data-identity ID",
            ));
        }
        if source_data_identity_ids[source_index] != Some(fact.data_identity_id) {
            return Err(EncodedValidationError::invariant(
                "named negative data-property assertion source and data identity disagree",
            ));
        }
        let predicate_id = data_predicate_id(predicate_by_negative_data_role, fact.role_id)?;
        let scalar_predicate_id = scalar_predicate_ids
            .get(usize::try_from(predicate_id).map_err(|_| {
                EncodedValidationError::invariant("negative data-fact predicate ID exceeds usize")
            })?)
            .copied()
            .ok_or_else(|| {
                EncodedValidationError::invariant(
                    "scalar negative data-fact predicate mapping is incomplete",
                )
            })?;
        let provenance_id = provenance_id(provenance_keys, &fact.provenance, false)?;
        let provenance_ids = vec![provenance_id];
        let arguments = GroundArguments::DataBinary(
            fact.source_individual,
            fact.source_literal_id,
            fact.data_identity_id,
        );
        let key = ground_fact_key(scalar_predicate_id, arguments, &provenance_ids);
        budget.claim_owned(
            key.len()
                .checked_add(size_of::<u32>())
                .and_then(|value| value.checked_add(2 * size_of::<DecodedTerm>()))
                .ok_or_else(|| {
                    EncodedValidationError::resource("negative data-fact payload overflowed")
                })?,
        )?;
        ordered.push((
            key,
            DecodedGroundAtom {
                predicate_id,
                arguments: vec![
                    DecodedTerm::Individual {
                        individual_id: fact.source_individual,
                    },
                    DecodedTerm::Data {
                        source_literal_id: fact.source_literal_id,
                        data_identity_id: fact.data_identity_id,
                    },
                ],
                provenance_ids,
            },
        ));
    }
    ordered.sort_by(|left, right| left.0.cmp(&right.0));
    if ordered.windows(2).any(|pair| pair[0].0 >= pair[1].0) {
        return Err(EncodedValidationError::invariant(
            "negative facts contain duplicate identities",
        ));
    }
    let mut output = Vec::new();
    budget.claim_owned(
        ordered
            .len()
            .checked_mul(size_of::<DecodedGroundAtom>())
            .ok_or_else(|| EncodedValidationError::resource("negative-fact result overflowed"))?,
    )?;
    output
        .try_reserve_exact(ordered.len())
        .map_err(|_| EncodedValidationError::resource("negative-fact result allocation failed"))?;
    output.extend(ordered.into_iter().map(|(_, fact)| fact));
    Ok(output)
}

fn push_clause(
    clauses: &mut Vec<(Vec<u8>, DecodedClause)>,
    body_predicates: &[u32],
    head_predicates: &[u32],
    provenance_id: u32,
    scalar_predicate_ids: &[u32],
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    push_typed_clause(
        clauses,
        body_predicates,
        head_predicates,
        TermSort::Object,
        provenance_id,
        scalar_predicate_ids,
        budget,
    )
}

#[allow(clippy::too_many_arguments)]
fn push_nominal_clauses(
    clauses: &mut Vec<(Vec<u8>, DecodedClause)>,
    nominal_predicate: u32,
    negated_nominal_predicate: Option<u32>,
    equality_predicate: u32,
    inequality_predicate: Option<u32>,
    individual_ids: &[u32],
    provenance_id: u32,
    scalar_predicate_ids: &[u32],
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    let variable = DecodedTerm::Variable {
        index: 0,
        sort: TermSort::Object,
    };
    let nominal_atom = DecodedAtom {
        predicate_id: nominal_predicate,
        arguments: vec![variable.clone()],
    };
    let equality_atoms = individual_ids
        .iter()
        .copied()
        .map(|individual_id| DecodedAtom {
            predicate_id: equality_predicate,
            arguments: vec![variable.clone(), DecodedTerm::Individual { individual_id }],
        })
        .collect::<Vec<_>>();
    push_mixed_clause(
        clauses,
        vec![nominal_atom.clone()],
        equality_atoms.clone(),
        provenance_id,
        scalar_predicate_ids,
        budget,
    )?;
    for equality_atom in equality_atoms {
        push_mixed_clause(
            clauses,
            vec![equality_atom],
            vec![nominal_atom.clone()],
            provenance_id,
            scalar_predicate_ids,
            budget,
        )?;
    }
    if let Some(negative) = negated_nominal_predicate {
        let inequality = inequality_predicate.ok_or_else(|| {
            EncodedValidationError::invariant(
                "negated object nominal lost the inequality predicate",
            )
        })?;
        let negative_atom = DecodedAtom {
            predicate_id: negative,
            arguments: vec![variable.clone()],
        };
        for individual_id in individual_ids {
            push_mixed_clause(
                clauses,
                vec![negative_atom.clone()],
                vec![DecodedAtom {
                    predicate_id: inequality,
                    arguments: vec![
                        variable.clone(),
                        DecodedTerm::Individual {
                            individual_id: *individual_id,
                        },
                    ],
                }],
                provenance_id,
                scalar_predicate_ids,
                budget,
            )?;
        }
    }
    Ok(())
}

fn push_mixed_clause(
    clauses: &mut Vec<(Vec<u8>, DecodedClause)>,
    body: Vec<DecodedAtom>,
    head: Vec<DecodedAtom>,
    provenance_id: u32,
    scalar_predicate_ids: &[u32],
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    let mut body = ordered_scalar_atoms(body, scalar_predicate_ids)?;
    let mut head = ordered_scalar_atoms(head, scalar_predicate_ids)?;
    body.dedup_by(|left, right| left.0 == right.0);
    head.dedup_by(|left, right| left.0 == right.0);
    if body
        .iter()
        .any(|body_atom| head.iter().any(|head_atom| body_atom.0 == head_atom.0))
    {
        return Ok(());
    }
    let body_json = body
        .iter()
        .map(|(key, _)| key.as_str())
        .collect::<Vec<_>>()
        .join(",");
    let head_json = head
        .iter()
        .map(|(key, _)| key.as_str())
        .collect::<Vec<_>>()
        .join(",");
    let key = format!("{{\"body\":[{body_json}],\"head\":[{head_json}]}}").into_bytes();
    let body_count = body.len();
    let atom_count = body
        .len()
        .checked_add(head.len())
        .ok_or_else(|| EncodedValidationError::resource("mixed nominal atom count overflowed"))?;
    let term_count = body
        .iter()
        .chain(&head)
        .try_fold(0_usize, |count, (_, atom)| {
            count.checked_add(atom.arguments.len()).ok_or_else(|| {
                EncodedValidationError::resource("mixed nominal term count overflowed")
            })
        })?;
    budget.claim_owned(size_of::<(Vec<u8>, DecodedClause)>())?;
    budget.claim_owned(key.len())?;
    budget.claim_owned(
        atom_count
            .checked_mul(size_of::<DecodedAtom>())
            .and_then(|value| value.checked_add(term_count.checked_mul(size_of::<DecodedTerm>())?))
            .and_then(|value| {
                value.checked_add(body_count.checked_add(1)?.checked_mul(size_of::<u32>())?)
            })
            .ok_or_else(|| {
                EncodedValidationError::resource("mixed nominal clause payload overflowed")
            })?,
    )?;
    clauses
        .try_reserve(1)
        .map_err(|_| EncodedValidationError::resource("mixed nominal clause allocation failed"))?;
    clauses.push((
        key,
        DecodedClause {
            clause_id: 0,
            body: body.into_iter().map(|(_, atom)| atom).collect(),
            head: head.into_iter().map(|(_, atom)| atom).collect(),
            provenance_ids: vec![provenance_id],
            join_order: (0..u32::try_from(body_count).map_err(|_| {
                EncodedValidationError::resource("mixed nominal join order exceeds u32")
            })?)
                .collect(),
        },
    ));
    Ok(())
}

fn ordered_scalar_atoms(
    atoms: Vec<DecodedAtom>,
    scalar_predicate_ids: &[u32],
) -> EncodedResult<Vec<(String, DecodedAtom)>> {
    let mut ordered = Vec::new();
    ordered.try_reserve_exact(atoms.len()).map_err(|_| {
        EncodedValidationError::resource("mixed nominal atom ordering allocation failed")
    })?;
    for atom in atoms {
        let scalar_predicate_id = scalar_predicate_ids
            .get(usize::try_from(atom.predicate_id).unwrap_or(usize::MAX))
            .copied()
            .ok_or_else(|| {
                EncodedValidationError::invariant(
                    "mixed nominal scalar predicate mapping is incomplete",
                )
            })?;
        let arguments = atom
            .arguments
            .iter()
            .map(decoded_term_json)
            .collect::<Vec<_>>()
            .join(",");
        let key = format!(
            "{{\"arguments\":[{arguments}],\"predicate_id\":{scalar_predicate_id},\"schema_version\":1,\"type\":\"Atom\"}}"
        );
        ordered.push((key, atom));
    }
    ordered.sort_by(|left, right| left.0.cmp(&right.0));
    Ok(ordered)
}

fn decoded_term_json(term: &DecodedTerm) -> String {
    match term {
        DecodedTerm::Variable { index, sort } => variable_json(*index, *sort),
        DecodedTerm::Individual { individual_id } => format!(
            "{{\"individual_id\":{individual_id},\"schema_version\":1,\"type\":\"IndividualTerm\"}}"
        ),
        DecodedTerm::Data {
            source_literal_id,
            data_identity_id,
        } => format!(
            "{{\"data_identity_id\":{data_identity_id},\"schema_version\":1,\"source_literal_id\":{source_literal_id},\"type\":\"DataConstant\"}}"
        ),
    }
}

fn push_typed_clause(
    clauses: &mut Vec<(Vec<u8>, DecodedClause)>,
    body_predicates: &[u32],
    head_predicates: &[u32],
    sort: TermSort,
    provenance_id: u32,
    scalar_predicate_ids: &[u32],
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    let mut body_ids = body_predicates.to_vec();
    let mut head_ids = head_predicates.to_vec();
    budget.claim_owned(
        body_ids
            .len()
            .checked_add(head_ids.len())
            .and_then(|value| value.checked_mul(size_of::<u32>()))
            .ok_or_else(|| {
                EncodedValidationError::resource("named-class clause ID payload overflowed")
            })?,
    )?;
    if body_ids.iter().chain(&head_ids).any(|predicate_id| {
        usize::try_from(*predicate_id)
            .ok()
            .is_none_or(|index| index >= scalar_predicate_ids.len())
    }) {
        return Err(EncodedValidationError::invariant(
            "clause scalar predicate mapping is incomplete",
        ));
    }
    let scalar_id = |predicate_id: &u32| {
        scalar_predicate_ids
            .get(usize::try_from(*predicate_id).unwrap_or(usize::MAX))
            .copied()
            .unwrap_or(u32::MAX)
    };
    body_ids.sort_unstable_by(|left, right| decimal_lexical_cmp(scalar_id(left), scalar_id(right)));
    body_ids.dedup();
    head_ids.sort_unstable_by(|left, right| decimal_lexical_cmp(scalar_id(left), scalar_id(right)));
    head_ids.dedup();
    if body_ids.iter().any(|value| head_ids.contains(value)) {
        return Ok(());
    }
    let body_count = body_ids.len();
    let key = unary_rule_key(&body_ids, &head_ids, sort);
    budget.claim_owned(size_of::<(Vec<u8>, DecodedClause)>())?;
    budget.claim_owned(key.len())?;
    let atom_count = body_ids
        .len()
        .checked_add(head_ids.len())
        .ok_or_else(|| EncodedValidationError::resource("named-class atom count overflowed"))?;
    budget.claim_owned(
        atom_count
            .checked_mul(size_of::<DecodedAtom>() + size_of::<DecodedTerm>())
            .and_then(|value| {
                value.checked_add(
                    body_ids
                        .len()
                        .checked_add(1)?
                        .checked_mul(size_of::<u32>())?,
                )
            })
            .ok_or_else(|| {
                EncodedValidationError::resource("named-class clause payload size overflowed")
            })?,
    )?;
    clauses
        .try_reserve(1)
        .map_err(|_| EncodedValidationError::resource("named-class clause allocation failed"))?;
    clauses.push((
        key,
        DecodedClause {
            clause_id: 0,
            body: body_ids
                .into_iter()
                .map(|predicate_id| variable_atom_at(predicate_id, 0, sort))
                .collect(),
            head: head_ids
                .into_iter()
                .map(|predicate_id| variable_atom_at(predicate_id, 0, sort))
                .collect(),
            provenance_ids: vec![provenance_id],
            join_order: (0..u32::try_from(body_count).map_err(|_| {
                EncodedValidationError::resource("named-class join order exceeds u32")
            })?)
                .collect(),
        },
    ));
    Ok(())
}

fn decimal_lexical_cmp(left: u32, right: u32) -> Ordering {
    let mut left_digits = [0_u8; 10];
    let mut right_digits = [0_u8; 10];
    let left_start = write_decimal_digits(left, &mut left_digits);
    let right_start = write_decimal_digits(right, &mut right_digits);
    left_digits[left_start..].cmp(&right_digits[right_start..])
}

fn write_decimal_digits(mut value: u32, digits: &mut [u8; 10]) -> usize {
    let mut index = digits.len();
    loop {
        index -= 1;
        digits[index] = b'0' + u8::try_from(value % 10).unwrap_or(0);
        value /= 10;
        if value == 0 {
            return index;
        }
    }
}

fn push_object_constraint_clause(
    clauses: &mut Vec<(Vec<u8>, DecodedClause)>,
    role_predicate_id: u32,
    class_predicate_id: u32,
    kind: ObjectConstraintKind,
    provenance_id: u32,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    let class_variable = match kind {
        ObjectConstraintKind::Domain => 0,
        ObjectConstraintKind::Range => 1,
    };
    let body = object_variable_atom(role_predicate_id, 0, 1);
    let head = variable_atom_at(class_predicate_id, class_variable, TermSort::Object);
    let key = object_constraint_rule_key(role_predicate_id, class_predicate_id, class_variable);
    budget.claim_owned(size_of::<(Vec<u8>, DecodedClause)>() + key.len())?;
    budget.claim_owned(
        2_usize
            .checked_mul(size_of::<DecodedAtom>())
            .and_then(|value| value.checked_add(3 * size_of::<DecodedTerm>()))
            .and_then(|value| value.checked_add(2 * size_of::<u32>()))
            .ok_or_else(|| {
                EncodedValidationError::resource(
                    "object-property constraint clause payload overflowed",
                )
            })?,
    )?;
    clauses.try_reserve(1).map_err(|_| {
        EncodedValidationError::resource("object-property constraint clause allocation failed")
    })?;
    clauses.push((
        key,
        DecodedClause {
            clause_id: 0,
            body: vec![body],
            head: vec![head],
            provenance_ids: vec![provenance_id],
            join_order: vec![0],
        },
    ));
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn push_object_characteristic_clause(
    clauses: &mut Vec<(Vec<u8>, DecodedClause)>,
    role_predicate_id: u32,
    equality_predicate_id: Option<u32>,
    thing_predicate_id: Option<u32>,
    kind: ObjectCharacteristicKind,
    provenance_id: u32,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    let (body, head) = match kind {
        ObjectCharacteristicKind::Functional => {
            let equality = equality_predicate_id.ok_or_else(|| {
                EncodedValidationError::invariant(
                    "functional object-property clause lost the equality predicate",
                )
            })?;
            (
                vec![
                    object_variable_atom(role_predicate_id, 0, 1),
                    object_variable_atom(role_predicate_id, 0, 2),
                ],
                vec![object_variable_atom(equality, 1, 2)],
            )
        }
        ObjectCharacteristicKind::InverseFunctional => {
            let equality = equality_predicate_id.ok_or_else(|| {
                EncodedValidationError::invariant(
                    "inverse-functional object-property clause lost the equality predicate",
                )
            })?;
            (
                vec![
                    object_variable_atom(role_predicate_id, 0, 1),
                    object_variable_atom(role_predicate_id, 2, 1),
                ],
                vec![object_variable_atom(equality, 0, 2)],
            )
        }
        ObjectCharacteristicKind::Reflexive => {
            let thing = thing_predicate_id.ok_or_else(|| {
                EncodedValidationError::invariant(
                    "reflexive object-property clause lost the top concept predicate",
                )
            })?;
            (
                vec![variable_atom_at(thing, 0, TermSort::Object)],
                vec![object_variable_atom(role_predicate_id, 0, 0)],
            )
        }
    };
    let key = object_characteristic_rule_key(
        role_predicate_id,
        equality_predicate_id,
        thing_predicate_id,
        kind,
    )?;
    let atom_count = body.len().checked_add(head.len()).ok_or_else(|| {
        EncodedValidationError::resource("object-property characteristic atom count overflowed")
    })?;
    let term_count = body.iter().chain(&head).try_fold(0_usize, |count, atom| {
        count.checked_add(atom.arguments.len()).ok_or_else(|| {
            EncodedValidationError::resource("object-property characteristic term count overflowed")
        })
    })?;
    let body_count = body.len();
    budget.claim_owned(size_of::<(Vec<u8>, DecodedClause)>() + key.len())?;
    budget.claim_owned(
        atom_count
            .checked_mul(size_of::<DecodedAtom>())
            .and_then(|value| value.checked_add(term_count.checked_mul(size_of::<DecodedTerm>())?))
            .and_then(|value| value.checked_add((body_count + 1) * size_of::<u32>()))
            .ok_or_else(|| {
                EncodedValidationError::resource(
                    "object-property characteristic clause payload overflowed",
                )
            })?,
    )?;
    clauses.try_reserve(1).map_err(|_| {
        EncodedValidationError::resource("object-property characteristic clause allocation failed")
    })?;
    clauses.push((
        key,
        DecodedClause {
            clause_id: 0,
            body,
            head,
            provenance_ids: vec![provenance_id],
            join_order: (0..u32::try_from(body_count).map_err(|_| {
                EncodedValidationError::resource(
                    "object-property characteristic join order exceeds u32",
                )
            })?)
                .collect(),
        },
    ));
    Ok(())
}

fn push_data_domain_clause(
    clauses: &mut Vec<(Vec<u8>, DecodedClause)>,
    role_predicate_id: u32,
    class_predicate_id: u32,
    provenance_id: u32,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    let body = data_variable_atom(role_predicate_id, 0, 1);
    let head = variable_atom_at(class_predicate_id, 0, TermSort::Object);
    let key = data_domain_rule_key(role_predicate_id, class_predicate_id);
    budget.claim_owned(size_of::<(Vec<u8>, DecodedClause)>() + key.len())?;
    budget.claim_owned(
        2_usize
            .checked_mul(size_of::<DecodedAtom>())
            .and_then(|value| value.checked_add(3 * size_of::<DecodedTerm>()))
            .and_then(|value| value.checked_add(2 * size_of::<u32>()))
            .ok_or_else(|| {
                EncodedValidationError::resource("data-property domain clause payload overflowed")
            })?,
    )?;
    clauses.try_reserve(1).map_err(|_| {
        EncodedValidationError::resource("data-property domain clause allocation failed")
    })?;
    clauses.push((
        key,
        DecodedClause {
            clause_id: 0,
            body: vec![body],
            head: vec![head],
            provenance_ids: vec![provenance_id],
            join_order: vec![0],
        },
    ));
    Ok(())
}

fn push_data_range_clause(
    clauses: &mut Vec<(Vec<u8>, DecodedClause)>,
    role_predicate_id: u32,
    range_predicate_id: u32,
    provenance_id: u32,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    let body = data_variable_atom(role_predicate_id, 0, 1);
    let head = variable_atom_at(range_predicate_id, 1, TermSort::Data);
    let key = data_range_rule_key(role_predicate_id, range_predicate_id);
    budget.claim_owned(size_of::<(Vec<u8>, DecodedClause)>() + key.len())?;
    budget.claim_owned(
        2_usize
            .checked_mul(size_of::<DecodedAtom>())
            .and_then(|value| value.checked_add(3 * size_of::<DecodedTerm>()))
            .and_then(|value| value.checked_add(2 * size_of::<u32>()))
            .ok_or_else(|| {
                EncodedValidationError::resource("data-property range clause payload overflowed")
            })?,
    )?;
    clauses.try_reserve(1).map_err(|_| {
        EncodedValidationError::resource("data-property range clause allocation failed")
    })?;
    clauses.push((
        key,
        DecodedClause {
            clause_id: 0,
            body: vec![body],
            head: vec![head],
            provenance_ids: vec![provenance_id],
            join_order: vec![0],
        },
    ));
    Ok(())
}

fn push_datatype_definition_clause(
    clauses: &mut Vec<(Vec<u8>, DecodedClause)>,
    sub_range_predicate_id: u32,
    super_range_predicate_id: u32,
    provenance_id: u32,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    if sub_range_predicate_id == super_range_predicate_id {
        return Ok(());
    }
    let body = variable_atom_at(sub_range_predicate_id, 0, TermSort::Data);
    let head = variable_atom_at(super_range_predicate_id, 0, TermSort::Data);
    let key = datatype_definition_rule_key(sub_range_predicate_id, super_range_predicate_id);
    budget.claim_owned(size_of::<(Vec<u8>, DecodedClause)>() + key.len())?;
    budget.claim_owned(
        2_usize
            .checked_mul(size_of::<DecodedAtom>())
            .and_then(|value| value.checked_add(2 * size_of::<DecodedTerm>()))
            .and_then(|value| value.checked_add(2 * size_of::<u32>()))
            .ok_or_else(|| {
                EncodedValidationError::resource("datatype-definition clause payload overflowed")
            })?,
    )?;
    clauses.try_reserve(1).map_err(|_| {
        EncodedValidationError::resource("datatype-definition clause allocation failed")
    })?;
    clauses.push((
        key,
        DecodedClause {
            clause_id: 0,
            body: vec![body],
            head: vec![head],
            provenance_ids: vec![provenance_id],
            join_order: vec![0],
        },
    ));
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn push_key_clause(
    clauses: &mut Vec<(Vec<u8>, DecodedClause)>,
    class_predicate_id: u32,
    object_role_predicate_ids: &[u32],
    data_role_predicate_ids: &[u32],
    equality_predicate_id: Option<u32>,
    data_inequality_predicate_id: Option<u32>,
    ordering_predicate_id: Option<u32>,
    named_predicate_id: Option<u32>,
    provenance_id: u32,
    scalar_predicate_ids: &[u32],
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    let equality = equality_predicate_id
        .ok_or_else(|| EncodedValidationError::invariant("has-key clause lost object equality"))?;
    let ordering = ordering_predicate_id.ok_or_else(|| {
        EncodedValidationError::invariant("has-key clause lost its ordering guard")
    })?;
    let named = named_predicate_id.ok_or_else(|| {
        EncodedValidationError::invariant("has-key clause lost its named-individual predicate")
    })?;
    let data_inequality = if data_role_predicate_ids.is_empty() {
        None
    } else {
        Some(data_inequality_predicate_id.ok_or_else(|| {
            EncodedValidationError::invariant("has-key clause lost data inequality")
        })?)
    };
    let body_count = 5_usize
        .checked_add(
            object_role_predicate_ids
                .len()
                .checked_mul(3)
                .ok_or_else(|| {
                    EncodedValidationError::resource("has-key body atom count overflowed")
                })?,
        )
        .and_then(|value| value.checked_add(data_role_predicate_ids.len().checked_mul(2)?))
        .ok_or_else(|| EncodedValidationError::resource("has-key body atom count overflowed"))?;
    let head_count = 1_usize
        .checked_add(data_role_predicate_ids.len())
        .ok_or_else(|| EncodedValidationError::resource("has-key head atom count overflowed"))?;
    let mut body = Vec::new();
    let mut head = Vec::new();
    budget.claim_owned(
        body_count
            .checked_add(head_count)
            .and_then(|value| value.checked_mul(size_of::<DecodedAtom>()))
            .ok_or_else(|| {
                EncodedValidationError::resource("has-key atom allocation overflowed")
            })?,
    )?;
    body.try_reserve_exact(body_count)
        .map_err(|_| EncodedValidationError::resource("has-key body allocation failed"))?;
    head.try_reserve_exact(head_count)
        .map_err(|_| EncodedValidationError::resource("has-key head allocation failed"))?;

    let left = 0_u32;
    let right = 1_u32;
    head.push(object_variable_atom(equality, left, right));
    body.push(variable_atom_at(class_predicate_id, left, TermSort::Object));
    body.push(variable_atom_at(
        class_predicate_id,
        right,
        TermSort::Object,
    ));
    body.push(variable_atom_at(named, left, TermSort::Object));
    body.push(variable_atom_at(named, right, TermSort::Object));
    body.push(object_variable_atom(ordering, left, right));
    let mut next_index = 2_u32;
    for role in object_role_predicate_ids {
        let target = next_index;
        next_index = next_index.checked_add(1).ok_or_else(|| {
            EncodedValidationError::resource("has-key variable count exceeds u32")
        })?;
        body.push(object_variable_atom(*role, left, target));
        body.push(object_variable_atom(*role, right, target));
        body.push(variable_atom_at(named, target, TermSort::Object));
    }
    for role in data_role_predicate_ids {
        let left_target = next_index;
        let right_target = next_index.checked_add(1).ok_or_else(|| {
            EncodedValidationError::resource("has-key variable count exceeds u32")
        })?;
        next_index = next_index.checked_add(2).ok_or_else(|| {
            EncodedValidationError::resource("has-key variable count exceeds u32")
        })?;
        body.push(data_variable_atom(*role, left, left_target));
        body.push(data_variable_atom(*role, right, right_target));
        head.push(data_equality_variable_atom(
            data_inequality.ok_or_else(|| {
                EncodedValidationError::invariant("has-key data inequality disappeared")
            })?,
            left_target,
            right_target,
        ));
    }
    let mut symmetric_predicates = vec![equality, ordering];
    if let Some(predicate) = data_inequality {
        symmetric_predicates.push(predicate);
    }
    let (body, head) = canonicalize_variable_rule(
        body,
        head,
        &symmetric_predicates,
        scalar_predicate_ids,
        budget,
    )?;
    let join_order = plan_key_join(&body, ordering, scalar_predicate_ids, budget)?;
    let key = variable_rule_key(&body, &head)?;
    budget.claim_owned(size_of::<(Vec<u8>, DecodedClause)>() + key.len())?;
    budget.claim_owned(
        body.len()
            .checked_add(1)
            .and_then(|value| value.checked_mul(size_of::<u32>()))
            .ok_or_else(|| EncodedValidationError::resource("has-key clause IDs overflowed"))?,
    )?;
    clauses
        .try_reserve(1)
        .map_err(|_| EncodedValidationError::resource("has-key clause allocation failed"))?;
    clauses.push((
        key,
        DecodedClause {
            clause_id: 0,
            body,
            head,
            provenance_ids: vec![provenance_id],
            join_order,
        },
    ));
    Ok(())
}

fn canonicalize_variable_rule(
    mut body: Vec<DecodedAtom>,
    mut head: Vec<DecodedAtom>,
    symmetric_predicates: &[u32],
    scalar_predicate_ids: &[u32],
    budget: &mut PhaseBudget,
) -> EncodedResult<(Vec<DecodedAtom>, Vec<DecodedAtom>)> {
    for atom in body.iter_mut().chain(&mut head) {
        canonicalize_symmetric_variable_atom(atom, symmetric_predicates)?;
    }
    body = sort_atoms_by_alpha_skeleton(body, scalar_predicate_ids, budget)?;
    head = sort_atoms_by_alpha_skeleton(head, scalar_predicate_ids, budget)?;
    let mut variables = Vec::<(u32, TermSort)>::new();
    for atom in body.iter().chain(&head) {
        for argument in &atom.arguments {
            let DecodedTerm::Variable { index, sort } = argument else {
                return Err(EncodedValidationError::invariant(
                    "has-key rule contains a non-variable term",
                ));
            };
            variables.push((*index, *sort));
        }
    }
    budget.claim_work(sort_work(variables.len()))?;
    variables.sort_unstable();
    variables.dedup();
    let maximum_passes = variables.len().checked_add(2).ok_or_else(|| {
        EncodedValidationError::resource("has-key alpha-canonical pass count overflowed")
    })?;
    for _ in 0..maximum_passes {
        budget.claim_work(body.len().saturating_add(head.len()))?;
        let mut mapping = Vec::<((u32, TermSort), u32)>::new();
        budget.claim_owned(
            variables
                .len()
                .checked_mul(size_of::<((u32, TermSort), u32)>())
                .ok_or_else(|| {
                    EncodedValidationError::resource("has-key variable mapping overflowed")
                })?,
        )?;
        mapping.try_reserve_exact(variables.len()).map_err(|_| {
            EncodedValidationError::resource("has-key variable mapping allocation failed")
        })?;
        for atom in body.iter().chain(&head) {
            for argument in &atom.arguments {
                let DecodedTerm::Variable { index, sort } = argument else {
                    return Err(EncodedValidationError::invariant(
                        "has-key rule contains a non-variable term",
                    ));
                };
                if mapping.iter().all(|(source, _)| *source != (*index, *sort)) {
                    let mapped = u32::try_from(mapping.len()).map_err(|_| {
                        EncodedValidationError::resource("has-key variable ID exceeds u32")
                    })?;
                    mapping.push(((*index, *sort), mapped));
                }
            }
        }
        let renamed_body = rename_variable_atoms(
            &body,
            &mapping,
            symmetric_predicates,
            scalar_predicate_ids,
            budget,
        )?;
        let renamed_head = rename_variable_atoms(
            &head,
            &mapping,
            symmetric_predicates,
            scalar_predicate_ids,
            budget,
        )?;
        let mut first_occurrence = Vec::new();
        for atom in renamed_body.iter().chain(&renamed_head) {
            for argument in &atom.arguments {
                let DecodedTerm::Variable { index, .. } = argument else {
                    return Err(EncodedValidationError::invariant(
                        "has-key rule contains a non-variable term",
                    ));
                };
                if !first_occurrence.contains(index) {
                    first_occurrence.push(*index);
                }
            }
        }
        let dense = first_occurrence
            .iter()
            .enumerate()
            .all(|(index, value)| usize::try_from(*value).ok() == Some(index));
        if renamed_body == body && renamed_head == head && dense {
            return Ok((renamed_body, renamed_head));
        }
        body = renamed_body;
        head = renamed_head;
    }
    Err(EncodedValidationError::invariant(
        "has-key alpha-canonical ordering did not converge",
    ))
}

fn rename_variable_atoms(
    atoms: &[DecodedAtom],
    mapping: &[((u32, TermSort), u32)],
    symmetric_predicates: &[u32],
    scalar_predicate_ids: &[u32],
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<DecodedAtom>> {
    let mut renamed = Vec::new();
    budget.claim_owned(
        atoms
            .len()
            .checked_mul(size_of::<DecodedAtom>())
            .ok_or_else(|| EncodedValidationError::resource("has-key atom rename overflowed"))?,
    )?;
    renamed
        .try_reserve_exact(atoms.len())
        .map_err(|_| EncodedValidationError::resource("has-key atom rename allocation failed"))?;
    for atom in atoms {
        let mut arguments = Vec::new();
        budget.claim_owned(
            atom.arguments
                .len()
                .checked_mul(size_of::<DecodedTerm>())
                .ok_or_else(|| {
                    EncodedValidationError::resource("has-key term rename overflowed")
                })?,
        )?;
        arguments
            .try_reserve_exact(atom.arguments.len())
            .map_err(|_| EncodedValidationError::resource("has-key term allocation failed"))?;
        for argument in &atom.arguments {
            let DecodedTerm::Variable { index, sort } = argument else {
                return Err(EncodedValidationError::invariant(
                    "has-key rule contains a non-variable term",
                ));
            };
            let mapped = mapping
                .iter()
                .find(|(source, _)| *source == (*index, *sort))
                .map(|(_, target)| *target)
                .ok_or_else(|| {
                    EncodedValidationError::invariant("has-key variable mapping is incomplete")
                })?;
            arguments.push(DecodedTerm::Variable {
                index: mapped,
                sort: *sort,
            });
        }
        let mut value = DecodedAtom {
            predicate_id: atom.predicate_id,
            arguments,
        };
        canonicalize_symmetric_variable_atom(&mut value, symmetric_predicates)?;
        renamed.push(value);
    }
    sort_atoms_by_canonical_key(renamed, scalar_predicate_ids, budget)
}

fn canonicalize_symmetric_variable_atom(
    atom: &mut DecodedAtom,
    symmetric_predicates: &[u32],
) -> EncodedResult<()> {
    if !symmetric_predicates.contains(&atom.predicate_id) {
        return Ok(());
    }
    let [left, right] = atom.arguments.as_mut_slice() else {
        return Err(EncodedValidationError::invariant(
            "symmetric has-key atom is not binary",
        ));
    };
    let DecodedTerm::Variable {
        index: left_index,
        sort: left_sort,
    } = left
    else {
        return Err(EncodedValidationError::invariant(
            "symmetric has-key atom contains a non-variable term",
        ));
    };
    let DecodedTerm::Variable {
        index: right_index,
        sort: right_sort,
    } = right
    else {
        return Err(EncodedValidationError::invariant(
            "symmetric has-key atom contains a non-variable term",
        ));
    };
    if left_sort != right_sort {
        return Err(EncodedValidationError::invariant(
            "symmetric has-key atom mixes term sorts",
        ));
    }
    if right_index < left_index {
        std::mem::swap(left, right);
    }
    Ok(())
}

fn sort_atoms_by_alpha_skeleton(
    atoms: Vec<DecodedAtom>,
    scalar_predicate_ids: &[u32],
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<DecodedAtom>> {
    budget.claim_work(sort_work(atoms.len()))?;
    let mut ordered = Vec::new();
    ordered
        .try_reserve_exact(atoms.len())
        .map_err(|_| EncodedValidationError::resource("has-key alpha sort allocation failed"))?;
    for atom in &atoms {
        if atom
            .arguments
            .iter()
            .any(|argument| !matches!(argument, DecodedTerm::Variable { .. }))
        {
            return Err(EncodedValidationError::invariant(
                "has-key alpha skeleton contains a non-variable term",
            ));
        }
    }
    for atom in atoms {
        ordered.push((
            scalar_predicate_id(scalar_predicate_ids, atom.predicate_id)?,
            atom,
        ));
    }
    ordered.sort_by(|(left_predicate, left), (right_predicate, right)| {
        left_predicate.cmp(right_predicate).then_with(|| {
            left.arguments
                .iter()
                .zip(&right.arguments)
                .find_map(|(left_term, right_term)| {
                    let DecodedTerm::Variable {
                        index: left_index,
                        sort: left_sort,
                    } = left_term
                    else {
                        return None;
                    };
                    let DecodedTerm::Variable {
                        index: right_index,
                        sort: right_sort,
                    } = right_term
                    else {
                        return None;
                    };
                    let left_key = (alpha_sort_rank(*left_sort), *left_index);
                    let right_key = (alpha_sort_rank(*right_sort), *right_index);
                    (left_key != right_key).then(|| left_key.cmp(&right_key))
                })
                .unwrap_or_else(|| left.arguments.len().cmp(&right.arguments.len()))
        })
    });
    ordered.dedup_by(|left, right| left.1 == right.1);
    Ok(ordered.into_iter().map(|(_, atom)| atom).collect())
}

const fn alpha_sort_rank(sort: TermSort) -> u8 {
    match sort {
        TermSort::Data => 0,
        TermSort::Object => 1,
    }
}

fn sort_atoms_by_canonical_key(
    atoms: Vec<DecodedAtom>,
    scalar_predicate_ids: &[u32],
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<DecodedAtom>> {
    let mut ordered = Vec::new();
    budget.claim_owned(
        atoms
            .len()
            .checked_mul(size_of::<(Vec<u8>, DecodedAtom)>())
            .ok_or_else(|| EncodedValidationError::resource("has-key atom sort overflowed"))?,
    )?;
    ordered
        .try_reserve_exact(atoms.len())
        .map_err(|_| EncodedValidationError::resource("has-key atom sort allocation failed"))?;
    for atom in atoms {
        let scalar_id = scalar_predicate_id(scalar_predicate_ids, atom.predicate_id)?;
        let key = variable_atom_key_with_predicate(&atom, scalar_id)?;
        budget.claim_owned(key.len())?;
        ordered.push((key, atom));
    }
    budget.claim_work(sort_work(ordered.len()))?;
    ordered.sort_by(|left, right| left.0.cmp(&right.0));
    ordered.dedup_by(|left, right| left.0 == right.0);
    Ok(ordered.into_iter().map(|(_, atom)| atom).collect())
}

fn variable_atom_key(atom: &DecodedAtom) -> EncodedResult<Vec<u8>> {
    variable_atom_key_with_predicate(atom, atom.predicate_id)
}

fn variable_atom_key_with_predicate(
    atom: &DecodedAtom,
    predicate_id: u32,
) -> EncodedResult<Vec<u8>> {
    let mut arguments = Vec::new();
    arguments
        .try_reserve_exact(atom.arguments.len())
        .map_err(|_| EncodedValidationError::resource("has-key atom key allocation failed"))?;
    for argument in &atom.arguments {
        let DecodedTerm::Variable { index, sort } = argument else {
            return Err(EncodedValidationError::invariant(
                "has-key atom key contains a non-variable term",
            ));
        };
        arguments.push(variable_json(*index, *sort));
    }
    Ok(format!(
        "{{\"arguments\":[{}],\"predicate_id\":{},\"schema_version\":1,\"type\":\"Atom\"}}",
        arguments.join(","),
        predicate_id,
    )
    .into_bytes())
}

fn scalar_predicate_id(scalar_predicate_ids: &[u32], local_id: u32) -> EncodedResult<u32> {
    scalar_predicate_ids
        .get(usize::try_from(local_id).map_err(|_| {
            EncodedValidationError::invariant("has-key local predicate ID exceeds usize")
        })?)
        .copied()
        .ok_or_else(|| {
            EncodedValidationError::invariant("has-key scalar predicate mapping is incomplete")
        })
}

fn variable_rule_key(body: &[DecodedAtom], head: &[DecodedAtom]) -> EncodedResult<Vec<u8>> {
    let body = body
        .iter()
        .map(variable_atom_key)
        .collect::<EncodedResult<Vec<_>>>()?
        .into_iter()
        .map(|value| {
            String::from_utf8(value)
                .map_err(|_| EncodedValidationError::invariant("has-key body key is not UTF-8"))
        })
        .collect::<EncodedResult<Vec<_>>>()?
        .join(",");
    let head = head
        .iter()
        .map(variable_atom_key)
        .collect::<EncodedResult<Vec<_>>>()?
        .into_iter()
        .map(|value| {
            String::from_utf8(value)
                .map_err(|_| EncodedValidationError::invariant("has-key head key is not UTF-8"))
        })
        .collect::<EncodedResult<Vec<_>>>()?
        .join(",");
    Ok(format!("{{\"body\":[{body}],\"head\":[{head}]}}").into_bytes())
}

fn plan_key_join(
    body: &[DecodedAtom],
    ordering_predicate_id: u32,
    scalar_predicate_ids: &[u32],
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<u32>> {
    let mut remaining = (0..body.len()).collect::<Vec<_>>();
    let mut bound = Vec::<(u32, TermSort)>::new();
    let mut result = Vec::new();
    let mut atom_keys = Vec::new();
    atom_keys
        .try_reserve_exact(body.len())
        .map_err(|_| EncodedValidationError::resource("has-key join key allocation failed"))?;
    for atom in body {
        let scalar_id = scalar_predicate_id(scalar_predicate_ids, atom.predicate_id)?;
        let key = variable_atom_key_with_predicate(atom, scalar_id)?;
        budget.claim_owned(key.len())?;
        atom_keys.push(key);
    }
    budget.claim_owned(
        body.len()
            .checked_mul(3)
            .and_then(|value| value.checked_mul(size_of::<usize>()))
            .ok_or_else(|| {
                EncodedValidationError::resource("has-key join allocation overflowed")
            })?,
    )?;
    result
        .try_reserve_exact(body.len())
        .map_err(|_| EncodedValidationError::resource("has-key join allocation failed"))?;
    while !remaining.is_empty() {
        budget.claim_work(remaining.len())?;
        let mut selected = None::<(usize, (u8, u8, usize, usize, &Vec<u8>))>;
        for (position, index) in remaining.iter().copied().enumerate() {
            let mut variables = Vec::new();
            for argument in &body[index].arguments {
                let DecodedTerm::Variable {
                    index: variable,
                    sort,
                } = argument
                else {
                    return Err(EncodedValidationError::invariant(
                        "has-key join contains a non-variable term",
                    ));
                };
                if !variables.contains(&(*variable, *sort)) {
                    variables.push((*variable, *sort));
                }
            }
            let shared = variables
                .iter()
                .filter(|value| bound.contains(value))
                .count();
            let new = variables.len().saturating_sub(shared);
            let rank = (
                u8::from(body[index].predicate_id == ordering_predicate_id && new > 0),
                u8::from(shared == 0),
                new,
                body[index].arguments.len(),
                &atom_keys[index],
            );
            if selected
                .as_ref()
                .is_none_or(|(_, previous)| rank < *previous)
            {
                selected = Some((position, rank));
            }
        }
        let (position, _) = selected.ok_or_else(|| {
            EncodedValidationError::invariant("has-key join planner lost its candidates")
        })?;
        let index = remaining.remove(position);
        result.push(
            u32::try_from(index)
                .map_err(|_| EncodedValidationError::resource("has-key join index exceeds u32"))?,
        );
        for argument in &body[index].arguments {
            let DecodedTerm::Variable { index, sort } = argument else {
                return Err(EncodedValidationError::invariant(
                    "has-key join contains a non-variable term",
                ));
            };
            if !bound.contains(&(*index, *sort)) {
                bound.push((*index, *sort));
            }
        }
    }
    Ok(result)
}

fn push_data_functionality_clause(
    clauses: &mut Vec<(Vec<u8>, DecodedClause)>,
    role_predicate_id: u32,
    equality_predicate_id: u32,
    provenance_id: u32,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    let first = data_variable_atom(role_predicate_id, 0, 1);
    let second = data_variable_atom(role_predicate_id, 0, 2);
    let head = data_equality_variable_atom(equality_predicate_id, 1, 2);
    let key = data_functionality_rule_key(role_predicate_id, equality_predicate_id);
    budget.claim_owned(size_of::<(Vec<u8>, DecodedClause)>() + key.len())?;
    budget.claim_owned(
        3_usize
            .checked_mul(size_of::<DecodedAtom>())
            .and_then(|value| value.checked_add(6 * size_of::<DecodedTerm>()))
            .and_then(|value| value.checked_add(3 * size_of::<u32>()))
            .ok_or_else(|| {
                EncodedValidationError::resource(
                    "functional data-property clause payload overflowed",
                )
            })?,
    )?;
    clauses.try_reserve(1).map_err(|_| {
        EncodedValidationError::resource("functional data-property clause allocation failed")
    })?;
    clauses.push((
        key,
        DecodedClause {
            clause_id: 0,
            body: vec![first, second],
            head: vec![head],
            provenance_ids: vec![provenance_id],
            join_order: vec![0, 1],
        },
    ));
    Ok(())
}

fn variable_atom_at(predicate_id: u32, index: u32, sort: TermSort) -> DecodedAtom {
    DecodedAtom {
        predicate_id,
        arguments: vec![DecodedTerm::Variable { index, sort }],
    }
}

fn object_variable_atom(predicate_id: u32, left: u32, right: u32) -> DecodedAtom {
    DecodedAtom {
        predicate_id,
        arguments: vec![
            DecodedTerm::Variable {
                index: left,
                sort: TermSort::Object,
            },
            DecodedTerm::Variable {
                index: right,
                sort: TermSort::Object,
            },
        ],
    }
}

fn data_variable_atom(predicate_id: u32, left: u32, right: u32) -> DecodedAtom {
    DecodedAtom {
        predicate_id,
        arguments: vec![
            DecodedTerm::Variable {
                index: left,
                sort: TermSort::Object,
            },
            DecodedTerm::Variable {
                index: right,
                sort: TermSort::Data,
            },
        ],
    }
}

fn data_equality_variable_atom(predicate_id: u32, left: u32, right: u32) -> DecodedAtom {
    DecodedAtom {
        predicate_id,
        arguments: vec![
            DecodedTerm::Variable {
                index: left,
                sort: TermSort::Data,
            },
            DecodedTerm::Variable {
                index: right,
                sort: TermSort::Data,
            },
        ],
    }
}

fn class_literal_predicate_id(
    positive_index: &[(u32, u32)],
    negative_index: &[(u32, u32)],
    class_id: u32,
    negative: bool,
) -> EncodedResult<u32> {
    predicate_id(
        if negative {
            negative_index
        } else {
            positive_index
        },
        class_id,
    )
}

fn data_range_literal_predicate_id(
    positive_index: &[(u32, u32)],
    negative_index: &[(u32, u32)],
    range: DataRangeLiteral,
) -> EncodedResult<u32> {
    predicate_id(
        if range.negative {
            negative_index
        } else {
            positive_index
        },
        range.range_id,
    )
}

fn predicate_id(index: &[(u32, u32)], class_id: u32) -> EncodedResult<u32> {
    index
        .binary_search_by_key(&class_id, |(candidate, _)| *candidate)
        .ok()
        .map(|position| index[position].1)
        .ok_or_else(|| {
            EncodedValidationError::invariant("named-class predicate index is incomplete")
        })
}

fn object_predicate_id(index: &[(u32, u32)], role_id: u32) -> EncodedResult<u32> {
    index
        .binary_search_by_key(&role_id, |(candidate, _)| *candidate)
        .ok()
        .map(|position| index[position].1)
        .ok_or_else(|| {
            EncodedValidationError::invariant("object-role predicate index is incomplete")
        })
}

fn data_predicate_id(index: &[(u32, u32)], role_id: u32) -> EncodedResult<u32> {
    index
        .binary_search_by_key(&role_id, |(candidate, _)| *candidate)
        .ok()
        .map(|position| index[position].1)
        .ok_or_else(|| EncodedValidationError::invariant("data-role predicate index is incomplete"))
}

fn guard_predicate_id(
    index: &[([u8; 32], u32, u32)],
    digest: [u8; 32],
    sequence: u32,
) -> EncodedResult<u32> {
    index
        .binary_search_by_key(&(digest, sequence), |(candidate, position, _)| {
            (*candidate, *position)
        })
        .ok()
        .map(|position| index[position].2)
        .ok_or_else(|| {
            EncodedValidationError::invariant("disjoint-guard predicate index is incomplete")
        })
}

fn provenance_id(
    keys: &[ProvenanceKey],
    source_sha256: &[[u8; 32]],
    generated: bool,
) -> EncodedResult<u32> {
    let identifier = keys
        .binary_search_by(|candidate| {
            (candidate.source_sha256.as_slice(), candidate.generated)
                .cmp(&(source_sha256, generated))
        })
        .map_err(|_| {
            EncodedValidationError::invariant("named-class provenance index is incomplete")
        })?;
    u32::try_from(identifier)
        .map_err(|_| EncodedValidationError::resource("named-class provenance ID exceeds u32"))
}

fn push_u32(
    target: &mut Vec<u32>,
    value: u32,
    name: &'static str,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    budget.claim_owned(size_of::<u32>())?;
    target.try_reserve(1).map_err(|_| {
        EncodedValidationError::resource(format!("named-class {name} allocation failed"))
    })?;
    target.push(value);
    Ok(())
}

fn disjoint_guard_digest_nodes<B: ByteSource>(
    model: &ValidatedModel<B>,
    classes: &[(ClassLiteral, NodeId)],
    scope_maps: &[AnonymousScopeMap],
    budget: &mut PhaseBudget,
) -> EncodedResult<[u8; 32]> {
    let mut digest = Sha256::new();
    digest.update(DISJOINT_GUARD_DOMAIN);
    budget.claim_work(DISJOINT_GUARD_DOMAIN.len())?;
    for (_, identifier) in classes {
        let key = canonical::canonical_node_key(model, *identifier, scope_maps, budget)?;
        budget.claim_work(key.len())?;
        digest.update(&key);
    }
    Ok(digest.finalize().into())
}

fn scalar_object_role_count(entity_domain: &DecodedSymbolDomain) -> EncodedResult<usize> {
    if entity_domain.kind != SymbolKind::Entity {
        return Err(EncodedValidationError::invariant(
            "scalar object-role count received a non-entity domain",
        ));
    }
    let named = entity_domain
        .values
        .iter()
        .filter_map(|value| value.display.strip_prefix(OBJECT_PROPERTY_PREFIX))
        .filter(|iri| *iri != TOP_OBJECT_IRI && *iri != BOTTOM_OBJECT_IRI)
        .count();
    named
        .checked_mul(2)
        .and_then(|value| value.checked_add(2))
        .ok_or_else(|| EncodedValidationError::resource("scalar object-role count overflowed"))
}

fn scalar_data_role_summary(entity_domain: &DecodedSymbolDomain) -> EncodedResult<(usize, u32)> {
    if entity_domain.kind != SymbolKind::Entity {
        return Err(EncodedValidationError::invariant(
            "scalar data-role summary received a non-entity domain",
        ));
    }
    let named = entity_domain
        .values
        .iter()
        .filter(|value| value.display.starts_with(DATA_PROPERTY_PREFIX))
        .count();
    let count = named
        .checked_add(2)
        .ok_or_else(|| EncodedValidationError::resource("scalar data-role count overflowed"))?;
    let bottom = named
        .checked_add(1)
        .and_then(|value| u32::try_from(value).ok())
        .ok_or_else(|| {
            EncodedValidationError::resource("scalar bottom data-role ID exceeds u32")
        })?;
    Ok((count, bottom))
}

fn scalar_predicate_ids(
    predicates: &[DecodedPredicate],
    object_role_count: usize,
    data_role_count: usize,
    bottom_data_role_id: u32,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<u32>> {
    let candidate_capacity = predicates
        .len()
        .checked_add(object_role_count)
        .and_then(|value| value.checked_add(1))
        .ok_or_else(|| EncodedValidationError::resource("scalar predicate count overflowed"))?;
    budget.claim_owned(
        object_role_count
            .checked_add(data_role_count)
            .and_then(|value| value.checked_mul(size_of::<Option<u32>>()))
            .ok_or_else(|| EncodedValidationError::resource("scalar role mapping overflowed"))?,
    )?;
    let mut local_object_predicates = Vec::new();
    local_object_predicates
        .try_reserve_exact(object_role_count)
        .map_err(|_| {
            EncodedValidationError::resource("scalar object-role mapping allocation failed")
        })?;
    local_object_predicates.resize(object_role_count, None);
    let mut local_data_predicates = Vec::new();
    local_data_predicates
        .try_reserve_exact(data_role_count)
        .map_err(|_| {
            EncodedValidationError::resource("scalar data-role mapping allocation failed")
        })?;
    local_data_predicates.resize(data_role_count, None);
    for predicate in predicates {
        let (expected_sorts, slots, name) = match predicate.kind {
            PredicateKind::ObjectRole => (
                [TermSort::Object, TermSort::Object],
                &mut local_object_predicates,
                "object-role",
            ),
            PredicateKind::DataRole => (
                [TermSort::Object, TermSort::Data],
                &mut local_data_predicates,
                "data-role",
            ),
            _ => continue,
        };
        if predicate.argument_sorts != expected_sorts
            || predicate.symbol_id.is_some()
            || predicate.cardinality.is_some()
            || predicate.filler_predicate_id.is_some()
            || !predicate.annotation.is_empty()
            || predicate.internal_key.is_some()
        {
            return Err(EncodedValidationError::invariant(format!(
                "named {name} predicate has invalid metadata"
            )));
        }
        let role_id = predicate.role_id.ok_or_else(|| {
            EncodedValidationError::invariant(format!("named {name} predicate lost its role ID"))
        })?;
        let slot = slots
            .get_mut(usize::try_from(role_id).map_err(|_| {
                EncodedValidationError::invariant(format!("named {name} ID exceeds usize"))
            })?)
            .ok_or_else(|| {
                EncodedValidationError::invariant(format!("named {name} ID is outside its domain"))
            })?;
        if slot.replace(predicate.predicate_id).is_some() {
            return Err(EncodedValidationError::invariant(format!(
                "named {name} predicate ID is duplicated"
            )));
        }
    }
    let mut candidates = Vec::<(Vec<u8>, Option<u32>)>::new();
    candidates
        .try_reserve_exact(candidate_capacity)
        .map_err(|_| {
            EncodedValidationError::resource("scalar predicate ordering allocation failed")
        })?;
    let bottom_data_index = usize::try_from(bottom_data_role_id).map_err(|_| {
        EncodedValidationError::invariant("scalar bottom data-role ID exceeds usize")
    })?;
    let bottom_data_predicate = local_data_predicates
        .get(bottom_data_index)
        .copied()
        .ok_or_else(|| {
            EncodedValidationError::invariant("scalar bottom data-role ID is outside its domain")
        })?;
    let data_key = role_predicate_key(PredicateKind::DataRole, bottom_data_role_id);
    budget.claim_owned(size_of::<(Vec<u8>, Option<u32>)>().saturating_add(data_key.len()))?;
    candidates.push((data_key, bottom_data_predicate));
    for (role_index, local_predicate_id) in local_data_predicates.iter().copied().enumerate() {
        let role_id = u32::try_from(role_index)
            .map_err(|_| EncodedValidationError::resource("scalar data-role ID exceeds u32"))?;
        if role_id == bottom_data_role_id {
            continue;
        }
        let Some(local_predicate_id) = local_predicate_id else {
            continue;
        };
        let key = role_predicate_key(PredicateKind::DataRole, role_id);
        budget.claim_owned(size_of::<(Vec<u8>, Option<u32>)>().saturating_add(key.len()))?;
        candidates.push((key, Some(local_predicate_id)));
    }
    for (role_index, local_predicate_id) in local_object_predicates.iter().copied().enumerate() {
        let role_id = u32::try_from(role_index)
            .map_err(|_| EncodedValidationError::resource("scalar object-role ID exceeds u32"))?;
        let key = role_predicate_key(PredicateKind::ObjectRole, role_id);
        budget.claim_owned(size_of::<(Vec<u8>, Option<u32>)>().saturating_add(key.len()))?;
        candidates.push((key, local_predicate_id));
    }
    for predicate in predicates {
        if matches!(
            predicate.kind,
            PredicateKind::ObjectRole | PredicateKind::DataRole
        ) {
            continue;
        }
        let key = named_predicate_key(predicate)?;
        budget.claim_owned(size_of::<(Vec<u8>, Option<u32>)>().saturating_add(key.len()))?;
        candidates.push((key, Some(predicate.predicate_id)));
    }
    budget.claim_work(sort_work(candidates.len()))?;
    candidates.sort_by(|left, right| left.0.cmp(&right.0));
    if candidates.windows(2).any(|pair| pair[0].0 >= pair[1].0) {
        return Err(EncodedValidationError::invariant(
            "scalar predicate ordering contains duplicate identities",
        ));
    }
    budget.claim_owned(
        predicates
            .len()
            .checked_mul(size_of::<u32>())
            .ok_or_else(|| {
                EncodedValidationError::resource("scalar predicate mapping overflowed")
            })?,
    )?;
    let mut mapping = Vec::new();
    mapping.try_reserve_exact(predicates.len()).map_err(|_| {
        EncodedValidationError::resource("scalar predicate mapping allocation failed")
    })?;
    mapping.resize(predicates.len(), u32::MAX);
    for (scalar_id, (_, local_id)) in candidates.into_iter().enumerate() {
        let Some(local_id) = local_id else {
            continue;
        };
        let local_index = usize::try_from(local_id)
            .map_err(|_| EncodedValidationError::invariant("local predicate ID exceeds usize"))?;
        let slot = mapping
            .get_mut(local_index)
            .ok_or_else(|| EncodedValidationError::invariant("local predicate ID is dangling"))?;
        *slot = u32::try_from(scalar_id)
            .map_err(|_| EncodedValidationError::resource("scalar predicate ID exceeds u32"))?;
    }
    if mapping.contains(&u32::MAX) {
        return Err(EncodedValidationError::invariant(
            "scalar predicate mapping is incomplete",
        ));
    }
    Ok(mapping)
}

fn role_predicate_key(kind: PredicateKind, role_id: u32) -> Vec<u8> {
    let (sorts, name) = match kind {
        PredicateKind::ObjectRole => ("\"object\",\"object\"", "object_role"),
        PredicateKind::NegatedObjectRole => ("\"object\",\"object\"", "negated_object_role"),
        PredicateKind::DataRole => ("\"object\",\"data\"", "data_role"),
        PredicateKind::NegatedDataRole => ("\"object\",\"data\"", "negated_data_role"),
        _ => ("", "invalid"),
    };
    format!(
        "{{\"annotation\":[],\"argument_sorts\":[{sorts}],\"cardinality\":null,\"filler\":null,\"internal_key\":null,\"kind\":\"{name}\",\"role_id\":{role_id},\"symbol_id\":null}}"
    )
    .into_bytes()
}

fn named_predicate_key(predicate: &DecodedPredicate) -> EncodedResult<Vec<u8>> {
    let unary_object = predicate.argument_sorts == [TermSort::Object];
    let unary_data = predicate.argument_sorts == [TermSort::Data];
    let binary_object = predicate.argument_sorts == [TermSort::Object, TermSort::Object];
    let binary_data = predicate.argument_sorts == [TermSort::Object, TermSort::Data];
    let equality_sort = match predicate.argument_sorts.as_slice() {
        [left, right] if left == right => Some(*left),
        _ => None,
    };
    if predicate.kind == PredicateKind::NegatedObjectRole
        && binary_object
        && predicate.symbol_id.is_none()
        && predicate.cardinality.is_none()
        && predicate.filler_predicate_id.is_none()
        && predicate.annotation.is_empty()
        && predicate.internal_key.is_none()
    {
        return predicate
            .role_id
            .map(|role_id| role_predicate_key(PredicateKind::NegatedObjectRole, role_id))
            .ok_or_else(|| {
                EncodedValidationError::invariant("negated object-role predicate lost its role ID")
            });
    }
    if predicate.kind == PredicateKind::NegatedDataRole
        && binary_data
        && predicate.symbol_id.is_none()
        && predicate.cardinality.is_none()
        && predicate.filler_predicate_id.is_none()
        && predicate.annotation.is_empty()
        && predicate.internal_key.is_none()
    {
        return predicate
            .role_id
            .map(|role_id| role_predicate_key(PredicateKind::NegatedDataRole, role_id))
            .ok_or_else(|| {
                EncodedValidationError::invariant("negated data-role predicate lost its role ID")
            });
    }
    if predicate.role_id.is_some()
        || predicate.cardinality.is_some()
        || predicate.filler_predicate_id.is_some()
    {
        return Err(EncodedValidationError::invariant(
            "named-class predicate has a foreign cross-reference",
        ));
    }
    match predicate.kind {
        PredicateKind::Concept
            if unary_object
                && predicate.annotation.is_empty()
                && predicate.internal_key.is_none() =>
        {
            predicate
                .symbol_id
                .map(concept_predicate_key)
                .ok_or_else(|| {
                    EncodedValidationError::invariant("concept predicate lost its class symbol")
                })
        }
        PredicateKind::NegatedConcept
            if unary_object
                && predicate.annotation.is_empty()
                && predicate.internal_key.is_none() =>
        {
            predicate
                .symbol_id
                .map(negated_concept_predicate_key)
                .ok_or_else(|| {
                    EncodedValidationError::invariant(
                        "negated concept predicate lost its class symbol",
                    )
                })
        }
        PredicateKind::Nominal if unary_object && predicate.internal_key.is_none() => predicate
            .symbol_id
            .map(|symbol_id| nominal_predicate_key(symbol_id, &predicate.annotation, false))
            .ok_or_else(|| {
                EncodedValidationError::invariant("nominal predicate lost its class symbol")
            }),
        PredicateKind::NegatedNominal if unary_object && predicate.internal_key.is_none() => {
            predicate
                .symbol_id
                .map(|symbol_id| nominal_predicate_key(symbol_id, &predicate.annotation, true))
                .ok_or_else(|| {
                    EncodedValidationError::invariant(
                        "negated nominal predicate lost its class symbol",
                    )
                })
        }
        PredicateKind::DataRange
            if unary_data
                && predicate.annotation.is_empty()
                && predicate.internal_key.is_none() =>
        {
            predicate
                .symbol_id
                .map(data_range_predicate_key)
                .ok_or_else(|| {
                    EncodedValidationError::invariant("data-range predicate lost its range symbol")
                })
        }
        PredicateKind::NegatedDataRange
            if unary_data
                && predicate.annotation.is_empty()
                && predicate.internal_key.is_none() =>
        {
            predicate
                .symbol_id
                .map(negated_data_range_predicate_key)
                .ok_or_else(|| {
                    EncodedValidationError::invariant(
                        "negated data-range predicate lost its range symbol",
                    )
                })
        }
        PredicateKind::Equality
            if equality_sort.is_some()
                && predicate.symbol_id.is_none()
                && predicate.annotation.is_empty()
                && predicate.internal_key.is_none() =>
        {
            Ok(equality_predicate_key(equality_sort.ok_or_else(|| {
                EncodedValidationError::invariant("equality predicate lost its term sort")
            })?))
        }
        PredicateKind::Inequality
            if equality_sort.is_some()
                && predicate.symbol_id.is_none()
                && predicate.annotation.is_empty()
                && predicate.internal_key.is_none() =>
        {
            Ok(inequality_predicate_key(equality_sort.ok_or_else(
                || EncodedValidationError::invariant("inequality predicate lost its term sort"),
            )?))
        }
        PredicateKind::OrderingGuard
            if binary_object
                && predicate.symbol_id.is_none()
                && predicate.annotation.is_empty()
                && predicate.internal_key.as_deref() == Some("canonical-object-order") =>
        {
            Ok(ordering_predicate_key())
        }
        PredicateKind::NamedIndividual
            if unary_object
                && predicate.symbol_id.is_none()
                && predicate.annotation.is_empty()
                && predicate.internal_key.as_deref() == Some("named-individual") =>
        {
            Ok(named_individual_predicate_key())
        }
        PredicateKind::DisjointGuard
            if unary_object
                && predicate.symbol_id.is_none()
                && predicate.annotation.len() == 1
                && predicate.internal_key.is_some() =>
        {
            Ok(disjoint_guard_predicate_key(
                predicate.annotation[0],
                predicate.internal_key.as_deref().unwrap_or_default(),
            ))
        }
        _ => Err(EncodedValidationError::invariant(
            "phase contains a predicate outside the named-class fragment",
        )),
    }
}

fn concept_predicate_key(class_id: u32) -> Vec<u8> {
    format!(
        "{{\"annotation\":[],\"argument_sorts\":[\"object\"],\"cardinality\":null,\"filler\":null,\"internal_key\":null,\"kind\":\"concept\",\"role_id\":null,\"symbol_id\":{class_id}}}"
    )
    .into_bytes()
}

fn negated_concept_predicate_key(class_id: u32) -> Vec<u8> {
    format!(
        "{{\"annotation\":[],\"argument_sorts\":[\"object\"],\"cardinality\":null,\"filler\":null,\"internal_key\":null,\"kind\":\"negated_concept\",\"role_id\":null,\"symbol_id\":{class_id}}}"
    )
    .into_bytes()
}

fn nominal_predicate_key(class_id: u32, individual_ids: &[u32], negative: bool) -> Vec<u8> {
    let annotation = individual_ids
        .iter()
        .map(u32::to_string)
        .collect::<Vec<_>>()
        .join(",");
    let kind = if negative {
        "negated_nominal"
    } else {
        "nominal"
    };
    format!(
        "{{\"annotation\":[{annotation}],\"argument_sorts\":[\"object\"],\"cardinality\":null,\"filler\":null,\"internal_key\":null,\"kind\":\"{kind}\",\"role_id\":null,\"symbol_id\":{class_id}}}"
    )
    .into_bytes()
}

fn data_range_predicate_key(range_id: u32) -> Vec<u8> {
    format!(
        "{{\"annotation\":[],\"argument_sorts\":[\"data\"],\"cardinality\":null,\"filler\":null,\"internal_key\":null,\"kind\":\"data_range\",\"role_id\":null,\"symbol_id\":{range_id}}}"
    )
    .into_bytes()
}

fn negated_data_range_predicate_key(range_id: u32) -> Vec<u8> {
    format!(
        "{{\"annotation\":[],\"argument_sorts\":[\"data\"],\"cardinality\":null,\"filler\":null,\"internal_key\":null,\"kind\":\"negated_data_range\",\"role_id\":null,\"symbol_id\":{range_id}}}"
    )
    .into_bytes()
}

fn named_individual_predicate_key() -> Vec<u8> {
    b"{\"annotation\":[],\"argument_sorts\":[\"object\"],\"cardinality\":null,\"filler\":null,\"internal_key\":\"named-individual\",\"kind\":\"named_individual\",\"role_id\":null,\"symbol_id\":null}"
        .to_vec()
}

fn equality_predicate_key(sort: TermSort) -> Vec<u8> {
    let sort = term_sort_name(sort);
    format!(
        "{{\"annotation\":[],\"argument_sorts\":[\"{sort}\",\"{sort}\"],\"cardinality\":null,\"filler\":null,\"internal_key\":null,\"kind\":\"equality\",\"role_id\":null,\"symbol_id\":null}}"
    )
    .into_bytes()
}

fn inequality_predicate_key(sort: TermSort) -> Vec<u8> {
    let sort = term_sort_name(sort);
    format!(
        "{{\"annotation\":[],\"argument_sorts\":[\"{sort}\",\"{sort}\"],\"cardinality\":null,\"filler\":null,\"internal_key\":null,\"kind\":\"inequality\",\"role_id\":null,\"symbol_id\":null}}"
    )
    .into_bytes()
}

fn ordering_predicate_key() -> Vec<u8> {
    b"{\"annotation\":[],\"argument_sorts\":[\"object\",\"object\"],\"cardinality\":null,\"filler\":null,\"internal_key\":\"canonical-object-order\",\"kind\":\"ordering_guard\",\"role_id\":null,\"symbol_id\":null}"
        .to_vec()
}

fn disjoint_guard_predicate_key(sequence: u32, internal_key: &str) -> Vec<u8> {
    format!(
        "{{\"annotation\":[{sequence}],\"argument_sorts\":[\"object\"],\"cardinality\":null,\"filler\":null,\"internal_key\":\"{internal_key}\",\"kind\":\"disjoint_guard\",\"role_id\":null,\"symbol_id\":null}}"
    )
    .into_bytes()
}

fn unary_rule_key(body_predicates: &[u32], head_predicates: &[u32], sort: TermSort) -> Vec<u8> {
    let body = body_predicates
        .iter()
        .copied()
        .map(|predicate_id| unary_atom_json(predicate_id, sort))
        .collect::<Vec<_>>()
        .join(",");
    let head = head_predicates
        .iter()
        .copied()
        .map(|predicate_id| unary_atom_json(predicate_id, sort))
        .collect::<Vec<_>>()
        .join(",");
    format!("{{\"body\":[{body}],\"head\":[{head}]}}").into_bytes()
}

fn object_constraint_rule_key(
    role_predicate_id: u32,
    class_predicate_id: u32,
    class_variable: u32,
) -> Vec<u8> {
    let body = format!(
        "{{\"arguments\":[{},{}],\"predicate_id\":{role_predicate_id},\"schema_version\":1,\"type\":\"Atom\"}}",
        variable_json(0, TermSort::Object),
        variable_json(1, TermSort::Object),
    );
    let head = format!(
        "{{\"arguments\":[{}],\"predicate_id\":{class_predicate_id},\"schema_version\":1,\"type\":\"Atom\"}}",
        variable_json(class_variable, TermSort::Object),
    );
    format!("{{\"body\":[{body}],\"head\":[{head}]}}").into_bytes()
}

fn object_characteristic_rule_key(
    role_predicate_id: u32,
    equality_predicate_id: Option<u32>,
    thing_predicate_id: Option<u32>,
    kind: ObjectCharacteristicKind,
) -> EncodedResult<Vec<u8>> {
    let object_atom = |predicate_id: u32, left: u32, right: u32| {
        format!(
            "{{\"arguments\":[{},{}],\"predicate_id\":{predicate_id},\"schema_version\":1,\"type\":\"Atom\"}}",
            variable_json(left, TermSort::Object),
            variable_json(right, TermSort::Object),
        )
    };
    let (body, head) = match kind {
        ObjectCharacteristicKind::Functional => {
            let equality = equality_predicate_id.ok_or_else(|| {
                EncodedValidationError::invariant(
                    "functional object-property key lost the equality predicate",
                )
            })?;
            (
                format!(
                    "{},{}",
                    object_atom(role_predicate_id, 0, 1),
                    object_atom(role_predicate_id, 0, 2),
                ),
                object_atom(equality, 1, 2),
            )
        }
        ObjectCharacteristicKind::InverseFunctional => {
            let equality = equality_predicate_id.ok_or_else(|| {
                EncodedValidationError::invariant(
                    "inverse-functional object-property key lost the equality predicate",
                )
            })?;
            (
                format!(
                    "{},{}",
                    object_atom(role_predicate_id, 0, 1),
                    object_atom(role_predicate_id, 2, 1),
                ),
                object_atom(equality, 0, 2),
            )
        }
        ObjectCharacteristicKind::Reflexive => {
            let thing = thing_predicate_id.ok_or_else(|| {
                EncodedValidationError::invariant(
                    "reflexive object-property key lost the top concept predicate",
                )
            })?;
            (
                format!(
                    "{{\"arguments\":[{}],\"predicate_id\":{thing},\"schema_version\":1,\"type\":\"Atom\"}}",
                    variable_json(0, TermSort::Object),
                ),
                object_atom(role_predicate_id, 0, 0),
            )
        }
    };
    Ok(format!("{{\"body\":[{body}],\"head\":[{head}]}}").into_bytes())
}

fn data_domain_rule_key(role_predicate_id: u32, class_predicate_id: u32) -> Vec<u8> {
    let body = format!(
        "{{\"arguments\":[{},{}],\"predicate_id\":{role_predicate_id},\"schema_version\":1,\"type\":\"Atom\"}}",
        variable_json(0, TermSort::Object),
        variable_json(1, TermSort::Data),
    );
    let head = format!(
        "{{\"arguments\":[{}],\"predicate_id\":{class_predicate_id},\"schema_version\":1,\"type\":\"Atom\"}}",
        variable_json(0, TermSort::Object),
    );
    format!("{{\"body\":[{body}],\"head\":[{head}]}}").into_bytes()
}

fn data_range_rule_key(role_predicate_id: u32, range_predicate_id: u32) -> Vec<u8> {
    let body = format!(
        "{{\"arguments\":[{},{}],\"predicate_id\":{role_predicate_id},\"schema_version\":1,\"type\":\"Atom\"}}",
        variable_json(0, TermSort::Object),
        variable_json(1, TermSort::Data),
    );
    let head = format!(
        "{{\"arguments\":[{}],\"predicate_id\":{range_predicate_id},\"schema_version\":1,\"type\":\"Atom\"}}",
        variable_json(1, TermSort::Data),
    );
    format!("{{\"body\":[{body}],\"head\":[{head}]}}").into_bytes()
}

fn datatype_definition_rule_key(
    sub_range_predicate_id: u32,
    super_range_predicate_id: u32,
) -> Vec<u8> {
    let body = format!(
        "{{\"arguments\":[{}],\"predicate_id\":{sub_range_predicate_id},\"schema_version\":1,\"type\":\"Atom\"}}",
        variable_json(0, TermSort::Data),
    );
    let head = format!(
        "{{\"arguments\":[{}],\"predicate_id\":{super_range_predicate_id},\"schema_version\":1,\"type\":\"Atom\"}}",
        variable_json(0, TermSort::Data),
    );
    format!("{{\"body\":[{body}],\"head\":[{head}]}}").into_bytes()
}

fn data_functionality_rule_key(role_predicate_id: u32, equality_predicate_id: u32) -> Vec<u8> {
    let role_atom = |value: u32| {
        format!(
            "{{\"arguments\":[{},{}],\"predicate_id\":{role_predicate_id},\"schema_version\":1,\"type\":\"Atom\"}}",
            variable_json(0, TermSort::Object),
            variable_json(value, TermSort::Data),
        )
    };
    let body = format!("{},{}", role_atom(1), role_atom(2));
    let head = format!(
        "{{\"arguments\":[{},{}],\"predicate_id\":{equality_predicate_id},\"schema_version\":1,\"type\":\"Atom\"}}",
        variable_json(1, TermSort::Data),
        variable_json(2, TermSort::Data),
    );
    format!("{{\"body\":[{body}],\"head\":[{head}]}}").into_bytes()
}

fn variable_json(index: u32, sort: TermSort) -> String {
    let sort = match sort {
        TermSort::Object => "object",
        TermSort::Data => "data",
    };
    format!("{{\"index\":{index},\"schema_version\":1,\"sort\":\"{sort}\",\"type\":\"Variable\"}}")
}

fn unary_atom_json(predicate_id: u32, sort: TermSort) -> String {
    format!(
        "{{\"arguments\":[{}],\"predicate_id\":{predicate_id},\"schema_version\":1,\"type\":\"Atom\"}}",
        variable_json(0, sort),
    )
}

fn ground_fact_key(
    predicate_id: u32,
    arguments: GroundArguments,
    provenance_ids: &[u32],
) -> Vec<u8> {
    let provenance = provenance_ids
        .iter()
        .map(u32::to_string)
        .collect::<Vec<_>>()
        .join(",");
    let arguments = match arguments {
        GroundArguments::Unary(individual_id) => format!(
            "{{\"individual_id\":{individual_id},\"schema_version\":1,\"type\":\"IndividualTerm\"}}"
        ),
        GroundArguments::Binary(left_individual, right_individual) => format!(
            "{{\"individual_id\":{left_individual},\"schema_version\":1,\"type\":\"IndividualTerm\"}},{{\"individual_id\":{right_individual},\"schema_version\":1,\"type\":\"IndividualTerm\"}}"
        ),
        GroundArguments::DataBinary(source_individual, source_literal_id, data_identity_id) => {
            format!(
                "{{\"individual_id\":{source_individual},\"schema_version\":1,\"type\":\"IndividualTerm\"}},{{\"data_identity_id\":{data_identity_id},\"schema_version\":1,\"source_literal_id\":{source_literal_id},\"type\":\"DataConstant\"}}"
            )
        }
    };
    format!(
        "{{\"arguments\":[{arguments}],\"predicate_id\":{predicate_id},\"provenance_ids\":[{provenance}],\"schema_version\":1,\"type\":\"GroundAtom\"}}"
    )
    .into_bytes()
}

fn required_component<T>(value: Option<T>, name: &'static str) -> EncodedResult<T> {
    value.ok_or_else(|| {
        EncodedValidationError::invariant(format!("validated {name} component disappeared"))
    })
}

const fn predicate_kind_name(kind: PredicateKind) -> &'static str {
    match kind {
        PredicateKind::Concept => "concept",
        PredicateKind::NegatedConcept => "negated_concept",
        PredicateKind::Nominal => "nominal",
        PredicateKind::NegatedNominal => "negated_nominal",
        PredicateKind::ObjectRole => "object_role",
        PredicateKind::NegatedObjectRole => "negated_object_role",
        PredicateKind::DataRole => "data_role",
        PredicateKind::NegatedDataRole => "negated_data_role",
        PredicateKind::DataRange => "data_range",
        PredicateKind::NegatedDataRange => "negated_data_range",
        PredicateKind::Equality => "equality",
        PredicateKind::Inequality => "inequality",
        PredicateKind::AtLeastObject => "at_least_object",
        PredicateKind::AtLeastData => "at_least_data",
        PredicateKind::AnnotatedEquality => "annotated_equality",
        PredicateKind::AutomatonState => "automaton_state",
        PredicateKind::DisjointGuard => "disjoint_guard",
        PredicateKind::OrderingGuard => "ordering_guard",
        PredicateKind::NamedIndividual => "named_individual",
    }
}

const fn term_sort_name(sort: TermSort) -> &'static str {
    match sort {
        TermSort::Object => "object",
        TermSort::Data => "data",
    }
}

/// Canonically merge independently owned source-local compiler transactions.
///
/// Every source identifier is remapped through its stable symbol key before
/// predicates, clauses, facts, and provenance are deduplicated.  The returned
/// phase therefore has the same dense-ID invariants as a single-source phase;
/// no borrowed encoded column or Python owner survives this transaction.
pub fn merge_named_class_phases(
    phases: &[(SymbolPhase, NamedClassPhase)],
    limits: NamedClassPhaseLimits,
) -> EncodedResult<NamedClassPhase> {
    merge_named_class_phases_impl(phases, None, None, None, None, limits)
}

/// Merge named fragments while remapping source-local object roles into the
/// globally frozen role domain used by object-property domain/range clauses.
pub fn merge_named_class_phases_with_object_roles(
    phases: &[(SymbolPhase, NamedClassPhase)],
    source_object_roles: &[ObjectRolePhase],
    merged_object_roles: &ObjectRolePhase,
    limits: NamedClassPhaseLimits,
) -> EncodedResult<NamedClassPhase> {
    if source_object_roles.len() != phases.len() {
        return Err(EncodedValidationError::invariant(
            "named-class source role phases do not align with their slices",
        ));
    }
    merge_named_class_phases_impl(
        phases,
        Some(source_object_roles),
        Some(merged_object_roles),
        None,
        None,
        limits,
    )
}

/// Merge named fragments while remapping source-local object and data roles
/// into the globally frozen role domains used by property-domain clauses.
pub fn merge_named_class_phases_with_role_domains(
    phases: &[(SymbolPhase, NamedClassPhase)],
    source_object_roles: &[ObjectRolePhase],
    merged_object_roles: &ObjectRolePhase,
    source_data_roles: &[DataRolePhase],
    merged_data_roles: &DataRolePhase,
    limits: NamedClassPhaseLimits,
) -> EncodedResult<NamedClassPhase> {
    if source_object_roles.len() != phases.len() || source_data_roles.len() != phases.len() {
        return Err(EncodedValidationError::invariant(
            "named-class source role phases do not align with their slices",
        ));
    }
    merge_named_class_phases_impl(
        phases,
        Some(source_object_roles),
        Some(merged_object_roles),
        Some(source_data_roles),
        Some(merged_data_roles),
        limits,
    )
}

fn merge_named_class_phases_impl(
    phases: &[(SymbolPhase, NamedClassPhase)],
    source_object_roles: Option<&[ObjectRolePhase]>,
    merged_object_roles: Option<&ObjectRolePhase>,
    source_data_roles: Option<&[DataRolePhase]>,
    merged_data_roles: Option<&DataRolePhase>,
    limits: NamedClassPhaseLimits,
) -> EncodedResult<NamedClassPhase> {
    if phases.is_empty() {
        return Err(EncodedValidationError::protocol(
            "encoded program merge requires at least one slice",
        ));
    }
    PhaseBudget::count(phases.len(), limits.max_slices, "slice count")?;
    let mut budget = PhaseBudget::new(limits);
    for (symbols, phase) in phases {
        budget.claim_work(
            usize::try_from(symbols.work)
                .unwrap_or(usize::MAX)
                .saturating_add(usize::try_from(phase.work).unwrap_or(usize::MAX)),
        )?;
        budget.claim_owned(
            symbols
                .owned_bytes
                .checked_add(phase.owned_bytes)
                .ok_or_else(|| {
                    EncodedValidationError::resource(
                        "encoded slice source ownership overflowed during merge",
                    )
                })?,
        )?;
    }

    let entity_domains = phases
        .iter()
        .map(|(symbols, _)| &symbols.entity_domain)
        .collect::<Vec<_>>();
    let class_domains = phases
        .iter()
        .map(|(_, phase)| &phase.class_domain)
        .collect::<Vec<_>>();
    let data_range_domains = phases
        .iter()
        .map(|(_, phase)| &phase.data_range_domain)
        .collect::<Vec<_>>();
    let individual_domains = phases
        .iter()
        .map(|(_, phase)| &phase.individual_domain)
        .collect::<Vec<_>>();
    let source_literal_domains = phases
        .iter()
        .map(|(_, phase)| &phase.source_literal_domain)
        .collect::<Vec<_>>();
    let data_value_domains = phases
        .iter()
        .map(|(_, phase)| &phase.data_value_domain)
        .collect::<Vec<_>>();
    let (entity_domain, entity_maps) = merge_symbol_domains(
        &entity_domains,
        SymbolKind::Entity,
        limits.max_entity_symbols,
        "entity",
        &mut budget,
    )?;
    let (class_domain, class_maps) = merge_symbol_domains(
        &class_domains,
        SymbolKind::ClassExpression,
        limits.max_class_symbols,
        "class-expression",
        &mut budget,
    )?;
    let (data_range_domain, data_range_maps) = merge_symbol_domains(
        &data_range_domains,
        SymbolKind::DataRange,
        limits.max_data_range_symbols,
        "data-range",
        &mut budget,
    )?;
    let (individual_domain, individual_maps) = merge_symbol_domains(
        &individual_domains,
        SymbolKind::Individual,
        limits.max_individual_symbols,
        "individual",
        &mut budget,
    )?;
    let (source_literal_domain, source_literal_maps) = merge_symbol_domains(
        &source_literal_domains,
        SymbolKind::SourceLiteral,
        limits.max_source_literal_symbols,
        "source-literal",
        &mut budget,
    )?;
    let (data_value_domain, data_value_maps) = merge_symbol_domains(
        &data_value_domains,
        SymbolKind::DataValue,
        limits.max_data_value_symbols,
        "data-value",
        &mut budget,
    )?;
    let source_data_identity_ids = merge_source_data_identity_ids(
        phases,
        &source_literal_maps,
        &data_value_maps,
        source_literal_domain.values.len(),
        &mut budget,
    )?;
    let class_signature = merge_class_signatures(
        phases,
        &entity_maps,
        &class_maps,
        &class_domain,
        &mut budget,
    )?;
    let individual_signature = merge_individual_signatures(
        phases,
        &entity_maps,
        &individual_maps,
        &individual_domain,
        &mut budget,
    )?;
    let nominal_bindings =
        merge_nominal_bindings(phases, &class_maps, &individual_maps, &mut budget)?;
    budget.claim_owned(
        individual_signature
            .len()
            .checked_mul(size_of::<u32>())
            .ok_or_else(|| {
                EncodedValidationError::resource("merged named-individual IDs overflowed")
            })?,
    )?;
    let mut named_individuals = Vec::<u32>::new();
    named_individuals
        .try_reserve_exact(individual_signature.len())
        .map_err(|_| {
            EncodedValidationError::resource("merged named-individual ID allocation failed")
        })?;
    named_individuals.extend(
        individual_signature
            .iter()
            .map(|binding| binding.individual_id),
    );
    let scalar_object_role_count = merged_object_roles.map_or_else(
        || scalar_object_role_count(&entity_domain),
        |roles| Ok(roles.object_role_domain.values.len()),
    )?;
    let (scalar_data_role_count, scalar_bottom_data_role_id) = merged_data_roles.map_or_else(
        || scalar_data_role_summary(&entity_domain),
        |roles| {
            Ok((
                roles.data_property_domain.values.len(),
                roles.bottom_data_property_id,
            ))
        },
    )?;
    drop(entity_domain);

    let (
        edges,
        disjoints,
        object_constraints,
        object_characteristics,
        data_domains,
        data_ranges,
        datatype_definitions,
        keys,
        data_functionalities,
        facts,
        object_facts,
        negative_object_facts,
        data_facts,
        negative_data_facts,
        equalities,
        inequalities,
    ) = merge_normalized_sources(
        phases,
        &class_maps,
        &data_range_maps,
        &individual_maps,
        &source_literal_maps,
        &data_value_maps,
        source_object_roles,
        merged_object_roles,
        source_data_roles,
        merged_data_roles,
        &mut budget,
    )?;
    let thing = class_id_by_display(&class_domain, THING_DISPLAY)?;
    let nothing = class_id_by_display(&class_domain, NOTHING_DISPLAY)?;
    let top_data_range = data_range_id_by_display(&data_range_domain, RDFS_LITERAL_DISPLAY)?;
    let (provenance, provenance_keys) = freeze_provenance(
        &edges,
        &disjoints,
        &object_constraints,
        &object_characteristics,
        &data_domains,
        &data_ranges,
        &datatype_definitions,
        &keys,
        &data_functionalities,
        &facts,
        &object_facts,
        &negative_object_facts,
        &data_facts,
        &negative_data_facts,
        &equalities,
        &inequalities,
        &mut budget,
    )?;
    let (
        predicates,
        predicate_by_class,
        predicate_by_negative_class,
        predicate_by_object_role,
        predicate_by_negative_object_role,
        predicate_by_data_role,
        predicate_by_negative_data_role,
        predicate_by_data_range,
        predicate_by_negative_data_range,
        guard_predicates,
        named_predicate,
        equality_predicate,
        data_equality_predicate,
        inequality_predicate,
        data_inequality_predicate,
        ordering_predicate,
    ) = freeze_predicates(
        &nominal_bindings,
        &edges,
        &disjoints,
        &object_constraints,
        &object_characteristics,
        &data_domains,
        &data_ranges,
        &datatype_definitions,
        &keys,
        &data_functionalities,
        &facts,
        &object_facts,
        &negative_object_facts,
        &data_facts,
        &negative_data_facts,
        &equalities,
        &inequalities,
        thing,
        nothing,
        top_data_range,
        !individual_domain.values.is_empty(),
        !named_individuals.is_empty(),
        &mut budget,
    )?;
    let scalar_predicate_ids = scalar_predicate_ids(
        &predicates,
        scalar_object_role_count,
        scalar_data_role_count,
        scalar_bottom_data_role_id,
        &mut budget,
    )?;
    let clauses = freeze_clauses(
        &nominal_bindings,
        &edges,
        &disjoints,
        &object_constraints,
        &object_characteristics,
        &data_domains,
        &data_ranges,
        &datatype_definitions,
        &keys,
        &data_functionalities,
        &facts,
        thing,
        nothing,
        top_data_range,
        &predicate_by_class,
        &predicate_by_negative_class,
        &predicate_by_object_role,
        &predicate_by_data_role,
        &predicate_by_data_range,
        &predicate_by_negative_data_range,
        equality_predicate,
        inequality_predicate,
        data_equality_predicate,
        data_inequality_predicate,
        ordering_predicate,
        named_predicate,
        &guard_predicates,
        &scalar_predicate_ids,
        &provenance_keys,
        &mut budget,
    )?;
    let positive_facts = freeze_positive_facts(
        &facts,
        &object_facts,
        &data_facts,
        &equalities,
        &inequalities,
        &individual_domain,
        thing,
        &predicate_by_class,
        &predicate_by_object_role,
        &predicate_by_data_role,
        &source_literal_domain,
        &data_value_domain,
        &source_data_identity_ids,
        &named_individuals,
        named_predicate,
        equality_predicate,
        nominal_usage(
            &nominal_bindings,
            &edges,
            &disjoints,
            &object_constraints,
            &data_domains,
            &keys,
            &facts,
        ),
        object_characteristics
            .iter()
            .any(|value| value.kind != ObjectCharacteristicKind::Reflexive),
        !keys.is_empty(),
        inequality_predicate,
        &provenance_keys,
        &scalar_predicate_ids,
        &mut budget,
    )?;
    let negative_facts = freeze_negative_facts(
        &facts,
        &negative_object_facts,
        &negative_data_facts,
        &individual_domain,
        &predicate_by_negative_class,
        &predicate_by_negative_object_role,
        &predicate_by_negative_data_role,
        &source_literal_domain,
        &data_value_domain,
        &source_data_identity_ids,
        &provenance_keys,
        &scalar_predicate_ids,
        positive_facts.len(),
        &mut budget,
    )?;
    let compiled_source_count = phases.iter().try_fold(0_usize, |total, (_, phase)| {
        if phase.compiled_root_digests.len() != phase.compiled_roots {
            return Err(EncodedValidationError::invariant(
                "merged source compiled-root identities are incomplete",
            ));
        }
        total.checked_add(phase.compiled_roots).ok_or_else(|| {
            EncodedValidationError::resource("merged compiled-root count overflowed")
        })
    })?;
    let mut compiled_root_digests = Vec::new();
    budget.claim_owned(
        compiled_source_count
            .checked_mul(size_of::<[u8; 32]>())
            .ok_or_else(|| {
                EncodedValidationError::resource("merged compiled-root identities overflowed")
            })?,
    )?;
    compiled_root_digests
        .try_reserve_exact(compiled_source_count)
        .map_err(|_| {
            EncodedValidationError::resource("merged compiled-root identity allocation failed")
        })?;
    for (_, phase) in phases {
        compiled_root_digests.extend_from_slice(&phase.compiled_root_digests);
    }
    budget.claim_work(sort_work(compiled_root_digests.len()))?;
    compiled_root_digests.sort_unstable();
    compiled_root_digests.dedup();
    let compiled_roots = compiled_root_digests.len();
    let deferred_roots = phases.iter().try_fold(0_usize, |total, (_, phase)| {
        total.checked_add(phase.deferred_roots).ok_or_else(|| {
            EncodedValidationError::resource("merged deferred-root count overflowed")
        })
    })?;
    PhaseBudget::count(
        compiled_roots,
        limits.max_compiled_roots,
        "compiled root count",
    )?;
    Ok(NamedClassPhase {
        class_domain,
        class_signature,
        data_range_domain,
        individual_domain,
        source_literal_domain,
        data_value_domain,
        individual_signature,
        named_individuals,
        predicates,
        clauses,
        positive_facts,
        negative_facts,
        provenance,
        compiled_roots,
        deferred_roots,
        work: budget.work,
        owned_bytes: budget.owned_bytes,
        compiled_root_digests,
        nominal_bindings,
        normalized_edges: edges,
        normalized_disjoints: disjoints,
        normalized_object_constraints: object_constraints,
        normalized_object_characteristics: object_characteristics,
        normalized_data_domains: data_domains,
        normalized_data_ranges: data_ranges,
        normalized_datatype_definitions: datatype_definitions,
        normalized_keys: keys,
        normalized_data_functionalities: data_functionalities,
        normalized_facts: facts,
        normalized_object_facts: object_facts,
        normalized_negative_object_facts: negative_object_facts,
        normalized_data_facts: data_facts,
        normalized_negative_data_facts: negative_data_facts,
        normalized_equalities: equalities,
        normalized_inequalities: inequalities,
        source_data_identity_ids,
        manifest_limit: limits.max_manifest_bytes,
    })
}

fn merge_symbol_domains(
    domains: &[&DecodedSymbolDomain],
    kind: SymbolKind,
    limit: usize,
    name: &'static str,
    budget: &mut PhaseBudget,
) -> EncodedResult<(DecodedSymbolDomain, Vec<Vec<u32>>)> {
    let total = domains.iter().try_fold(0_usize, |count, domain| {
        if domain.kind != kind {
            return Err(EncodedValidationError::invariant(format!(
                "merged {name} domain changed kind"
            )));
        }
        validate_dense_symbols(domain, name)?;
        count.checked_add(domain.values.len()).ok_or_else(|| {
            EncodedValidationError::resource(format!("merged {name} count overflowed"))
        })
    })?;
    PhaseBudget::count(total, limit, name)?;
    let mut candidates = Vec::new();
    candidates.try_reserve_exact(total).map_err(|_| {
        EncodedValidationError::resource(format!("merged {name} symbols allocation failed"))
    })?;
    for domain in domains {
        for value in &domain.values {
            budget.claim_work(1)?;
            budget.claim_owned(size_of::<DecodedSymbolValue>())?;
            budget.claim_owned(value.key.len().saturating_add(value.display.len()))?;
            candidates.push(value.clone());
        }
    }
    budget.claim_work(sort_work(candidates.len()))?;
    candidates.sort_by(|left, right| left.key.cmp(&right.key));
    let mut values: Vec<DecodedSymbolValue> = Vec::new();
    values.try_reserve_exact(candidates.len()).map_err(|_| {
        EncodedValidationError::resource(format!("merged {name} result allocation failed"))
    })?;
    for mut candidate in candidates {
        if let Some(previous) = values.last() {
            if previous.key == candidate.key {
                if previous.display != candidate.display
                    || previous.generated != candidate.generated
                    || previous.query_local != candidate.query_local
                {
                    return Err(EncodedValidationError::invariant(format!(
                        "merged {name} symbol key has conflicting metadata"
                    )));
                }
                continue;
            }
        }
        candidate.identifier = u32::try_from(values.len()).map_err(|_| {
            EncodedValidationError::resource(format!("merged {name} symbol ID exceeds u32"))
        })?;
        values.push(candidate);
    }
    let mut mappings = Vec::new();
    mappings.try_reserve_exact(domains.len()).map_err(|_| {
        EncodedValidationError::resource(format!("merged {name} mapping allocation failed"))
    })?;
    for domain in domains {
        let mut mapping = Vec::new();
        budget.claim_owned(
            domain
                .values
                .len()
                .checked_mul(size_of::<u32>())
                .ok_or_else(|| {
                    EncodedValidationError::resource(format!("merged {name} mapping overflowed"))
                })?,
        )?;
        mapping
            .try_reserve_exact(domain.values.len())
            .map_err(|_| {
                EncodedValidationError::resource(format!("merged {name} mapping allocation failed"))
            })?;
        for value in &domain.values {
            budget.claim_work(binary_search_work(values.len()))?;
            let index = values
                .binary_search_by(|candidate| candidate.key.cmp(&value.key))
                .map_err(|_| {
                    EncodedValidationError::invariant(format!("merged {name} symbol disappeared"))
                })?;
            mapping.push(u32::try_from(index).map_err(|_| {
                EncodedValidationError::resource(format!("merged {name} mapping exceeds u32"))
            })?);
        }
        mappings.push(mapping);
    }
    Ok((DecodedSymbolDomain { kind, values }, mappings))
}

fn validate_dense_symbols(domain: &DecodedSymbolDomain, name: &'static str) -> EncodedResult<()> {
    for (index, value) in domain.values.iter().enumerate() {
        if usize::try_from(value.identifier).ok() != Some(index) {
            return Err(EncodedValidationError::invariant(format!(
                "merged {name} source IDs are not dense"
            )));
        }
        if index > 0 && domain.values[index - 1].key >= value.key {
            return Err(EncodedValidationError::invariant(format!(
                "merged {name} source keys are not canonical"
            )));
        }
    }
    Ok(())
}

fn merge_source_data_identity_ids(
    phases: &[(SymbolPhase, NamedClassPhase)],
    source_literal_maps: &[Vec<u32>],
    data_value_maps: &[Vec<u32>],
    source_literal_count: usize,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<Option<u32>>> {
    if source_literal_maps.len() != phases.len() || data_value_maps.len() != phases.len() {
        return Err(EncodedValidationError::invariant(
            "literal symbol mappings do not align with their slices",
        ));
    }
    budget.claim_owned(
        source_literal_count
            .checked_mul(size_of::<Option<Option<u32>>>())
            .ok_or_else(|| {
                EncodedValidationError::resource("merged source data-identity mapping overflowed")
            })?,
    )?;
    let mut merged = vec![None::<Option<u32>>; source_literal_count];
    for (phase_index, (_, phase)) in phases.iter().enumerate() {
        if phase.source_data_identity_ids.len() != phase.source_literal_domain.values.len() {
            return Err(EncodedValidationError::invariant(
                "source data-identity mapping no longer covers its literal domain",
            ));
        }
        for (source_index, data_identity_id) in
            phase.source_data_identity_ids.iter().copied().enumerate()
        {
            budget.claim_work(1)?;
            let global_source = mapped_id(
                &source_literal_maps[phase_index],
                u32::try_from(source_index).map_err(|_| {
                    EncodedValidationError::resource("source-literal ID exceeds u32")
                })?,
                "source literal",
            )?;
            let global_data = data_identity_id
                .map(|identifier| {
                    mapped_id(
                        &data_value_maps[phase_index],
                        identifier,
                        "source data identity",
                    )
                })
                .transpose()?;
            let slot = merged
                .get_mut(usize::try_from(global_source).unwrap_or(usize::MAX))
                .ok_or_else(|| {
                    EncodedValidationError::invariant("merged source-literal mapping is dangling")
                })?;
            match slot {
                Some(existing) if *existing != global_data => {
                    return Err(EncodedValidationError::invariant(
                        "merged source literal has conflicting data identities",
                    ));
                }
                Some(_) => {}
                None => *slot = Some(global_data),
            }
        }
    }
    merged
        .into_iter()
        .map(|value| {
            value.ok_or_else(|| {
                EncodedValidationError::invariant(
                    "merged source data-identity mapping is incomplete",
                )
            })
        })
        .collect()
}

fn mapped_id(mapping: &[u32], identifier: u32, name: &'static str) -> EncodedResult<u32> {
    mapping
        .get(usize::try_from(identifier).map_err(|_| {
            EncodedValidationError::invariant(format!("merged {name} source ID exceeds usize"))
        })?)
        .copied()
        .ok_or_else(|| {
            EncodedValidationError::invariant(format!("merged {name} source ID is dangling"))
        })
}

fn remap_object_role(
    source: &ObjectRolePhase,
    merged: &ObjectRolePhase,
    identifier: u32,
    budget: &mut PhaseBudget,
) -> EncodedResult<u32> {
    let key = source
        .object_role_domain
        .values
        .get(usize::try_from(identifier).map_err(|_| {
            EncodedValidationError::invariant("source object-role ID exceeds usize")
        })?)
        .map(|value| value.key.as_slice())
        .ok_or_else(|| EncodedValidationError::invariant("source object-role ID is dangling"))?;
    role_id_by_key(&merged.object_role_domain, key, budget)
}

fn remap_data_role(
    source: &DataRolePhase,
    merged: &DataRolePhase,
    identifier: u32,
    budget: &mut PhaseBudget,
) -> EncodedResult<u32> {
    let key =
        source
            .data_property_domain
            .values
            .get(usize::try_from(identifier).map_err(|_| {
                EncodedValidationError::invariant("source data-role ID exceeds usize")
            })?)
            .map(|value| value.key.as_slice())
            .ok_or_else(|| EncodedValidationError::invariant("source data-role ID is dangling"))?;
    data_role_id_by_key(&merged.data_property_domain, key, budget)
}

fn merge_class_signatures(
    phases: &[(SymbolPhase, NamedClassPhase)],
    entity_maps: &[Vec<u32>],
    class_maps: &[Vec<u32>],
    class_domain: &DecodedSymbolDomain,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<ClassSignatureBinding>> {
    if class_domain.kind != SymbolKind::ClassExpression {
        return Err(EncodedValidationError::invariant(
            "merged class signature domain changed kind",
        ));
    }
    let class_count = class_domain.values.len();
    let mut merged = vec![None::<(u32, bool)>; class_count];
    budget.claim_owned(
        class_count
            .checked_mul(size_of::<Option<(u32, bool)>>())
            .ok_or_else(|| EncodedValidationError::resource("merged class signature overflowed"))?,
    )?;
    for (phase_index, (symbols, phase)) in phases.iter().enumerate() {
        let named_count = symbols
            .entity_domain
            .values
            .iter()
            .filter(|value| value.display.starts_with("class:"))
            .count();
        if phase.class_signature.len() != named_count {
            return Err(EncodedValidationError::invariant(
                "merged class signature no longer covers its entity domain",
            ));
        }
        for binding in &phase.class_signature {
            budget.claim_work(1)?;
            let local_value = phase
                .class_domain
                .values
                .get(usize::try_from(binding.class_expression_id).unwrap_or(usize::MAX))
                .ok_or_else(|| {
                    EncodedValidationError::invariant(
                        "merged class signature has a dangling local ID",
                    )
                })?;
            let entity = symbols
                .entity_domain
                .values
                .get(usize::try_from(binding.entity_id).unwrap_or(usize::MAX))
                .ok_or_else(|| {
                    EncodedValidationError::invariant(
                        "merged class signature has a dangling entity ID",
                    )
                })?;
            if !entity.display.starts_with("class:") || local_value.key != entity.key {
                return Err(EncodedValidationError::invariant(
                    "merged class signature binds a non-entity expression",
                ));
            }
            let class_id = mapped_id(
                &class_maps[phase_index],
                binding.class_expression_id,
                "class",
            )?;
            let entity_id = mapped_id(&entity_maps[phase_index], binding.entity_id, "entity")?;
            let slot = merged
                .get_mut(usize::try_from(class_id).unwrap_or(usize::MAX))
                .ok_or_else(|| EncodedValidationError::invariant("merged class ID is dangling"))?;
            match slot {
                Some((existing, declared)) if *existing == entity_id => {
                    *declared |= binding.declared;
                }
                Some(_) => {
                    return Err(EncodedValidationError::invariant(
                        "merged class symbol maps to conflicting entities",
                    ));
                }
                None => *slot = Some((entity_id, binding.declared)),
            }
        }
    }
    merged
        .into_iter()
        .enumerate()
        .filter_map(|(index, value)| {
            value.map(|(entity_id, declared)| {
                u32::try_from(index)
                    .map(|class_expression_id| ClassSignatureBinding {
                        class_expression_id,
                        entity_id,
                        declared,
                    })
                    .map_err(|_| {
                        EncodedValidationError::resource("merged class signature ID exceeds u32")
                    })
            })
        })
        .collect()
}

fn merge_individual_signatures(
    phases: &[(SymbolPhase, NamedClassPhase)],
    entity_maps: &[Vec<u32>],
    individual_maps: &[Vec<u32>],
    individual_domain: &DecodedSymbolDomain,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<IndividualSignatureBinding>> {
    if individual_domain.kind != SymbolKind::Individual {
        return Err(EncodedValidationError::invariant(
            "merged individual signature domain changed kind",
        ));
    }
    let individual_count = individual_domain.values.len();
    let mut merged = vec![None::<(u32, bool)>; individual_count];
    budget.claim_owned(
        individual_count
            .checked_mul(size_of::<Option<(u32, bool)>>())
            .ok_or_else(|| {
                EncodedValidationError::resource("merged individual signature overflowed")
            })?,
    )?;
    for (phase_index, (_, phase)) in phases.iter().enumerate() {
        let named_count = phase
            .individual_domain
            .values
            .iter()
            .filter(|value| value.display.starts_with(NAMED_INDIVIDUAL_PREFIX))
            .count();
        if phase.individual_signature.len() != named_count {
            return Err(EncodedValidationError::invariant(
                "merged individual signature no longer covers its named domain",
            ));
        }
        for binding in &phase.individual_signature {
            budget.claim_work(1)?;
            let local_value = phase
                .individual_domain
                .values
                .get(usize::try_from(binding.individual_id).unwrap_or(usize::MAX))
                .ok_or_else(|| {
                    EncodedValidationError::invariant(
                        "merged individual signature has a dangling local ID",
                    )
                })?;
            if !local_value.display.starts_with(NAMED_INDIVIDUAL_PREFIX) {
                return Err(EncodedValidationError::invariant(
                    "merged individual signature binds an anonymous symbol",
                ));
            }
            let individual_id = mapped_id(
                &individual_maps[phase_index],
                binding.individual_id,
                "individual",
            )?;
            let entity_id = mapped_id(&entity_maps[phase_index], binding.entity_id, "entity")?;
            let slot = merged
                .get_mut(usize::try_from(individual_id).unwrap_or(usize::MAX))
                .ok_or_else(|| {
                    EncodedValidationError::invariant("merged individual ID is dangling")
                })?;
            match slot {
                Some((existing, declared)) if *existing == entity_id => {
                    *declared |= binding.declared;
                }
                Some(_) => {
                    return Err(EncodedValidationError::invariant(
                        "merged individual symbol maps to conflicting entities",
                    ));
                }
                None => *slot = Some((entity_id, binding.declared)),
            }
        }
    }
    merged
        .into_iter()
        .enumerate()
        .filter_map(|(index, value)| {
            let is_named = individual_domain.values[index]
                .display
                .starts_with(NAMED_INDIVIDUAL_PREFIX);
            match (is_named, value) {
                (false, None) => None,
                (true, Some((entity_id, declared))) => Some(
                    u32::try_from(index)
                        .map(|individual_id| IndividualSignatureBinding {
                            individual_id,
                            entity_id,
                            declared,
                        })
                        .map_err(|_| {
                            EncodedValidationError::resource(
                                "merged individual signature ID exceeds u32",
                            )
                        }),
                ),
                (true, None) => Some(Err(EncodedValidationError::invariant(
                    "merged individual signature is incomplete",
                ))),
                (false, Some(_)) => Some(Err(EncodedValidationError::invariant(
                    "merged individual signature binds an anonymous symbol",
                ))),
            }
        })
        .collect()
}

fn merge_nominal_bindings(
    phases: &[(SymbolPhase, NamedClassPhase)],
    class_maps: &[Vec<u32>],
    individual_maps: &[Vec<u32>],
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<NominalBinding>> {
    if class_maps.len() != phases.len() || individual_maps.len() != phases.len() {
        return Err(EncodedValidationError::invariant(
            "object nominal mappings do not align with their slices",
        ));
    }
    let mut merged = Vec::new();
    for (phase_index, (_, phase)) in phases.iter().enumerate() {
        for binding in &phase.nominal_bindings {
            budget.claim_work(1)?;
            let class_value = phase
                .class_domain
                .values
                .get(usize::try_from(binding.class_id).unwrap_or(usize::MAX))
                .ok_or_else(|| {
                    EncodedValidationError::invariant(
                        "source object nominal has a dangling class ID",
                    )
                })?;
            if !class_value.display.starts_with("ObjectOneOf:") || binding.individual_ids.is_empty()
            {
                return Err(EncodedValidationError::invariant(
                    "source object nominal binding changed shape",
                ));
            }
            let class_id = mapped_id(
                &class_maps[phase_index],
                binding.class_id,
                "object nominal class",
            )?;
            let mut individual_ids = Vec::new();
            budget.claim_owned(
                binding
                    .individual_ids
                    .len()
                    .checked_mul(size_of::<u32>())
                    .ok_or_else(|| {
                        EncodedValidationError::resource(
                            "merged object nominal individual IDs overflowed",
                        )
                    })?,
            )?;
            individual_ids
                .try_reserve_exact(binding.individual_ids.len())
                .map_err(|_| {
                    EncodedValidationError::resource(
                        "merged object nominal individual allocation failed",
                    )
                })?;
            for individual_id in &binding.individual_ids {
                individual_ids.push(mapped_id(
                    &individual_maps[phase_index],
                    *individual_id,
                    "object nominal individual",
                )?);
            }
            individual_ids.sort_unstable();
            individual_ids.dedup();
            if individual_ids.is_empty() {
                return Err(EncodedValidationError::invariant(
                    "merged object nominal lost all individuals",
                ));
            }
            budget.claim_owned(size_of::<NominalBinding>())?;
            merged.try_reserve(1).map_err(|_| {
                EncodedValidationError::resource("merged object nominal allocation failed")
            })?;
            merged.push(NominalBinding {
                class_id,
                individual_ids,
            });
        }
    }
    budget.claim_work(sort_work(merged.len()))?;
    merged.sort();
    merged.dedup();
    if merged
        .windows(2)
        .any(|pair| pair[0].class_id == pair[1].class_id)
    {
        return Err(EncodedValidationError::invariant(
            "merged object nominal has conflicting individual members",
        ));
    }
    Ok(merged)
}

type NormalizedSources = (
    Vec<NormalizedEdge>,
    Vec<NormalizedDisjoint>,
    Vec<NormalizedObjectConstraint>,
    Vec<NormalizedObjectCharacteristic>,
    Vec<NormalizedDataDomain>,
    Vec<NormalizedDataRange>,
    Vec<NormalizedDatatypeDefinition>,
    Vec<NormalizedKey>,
    Vec<NormalizedDataFunctionality>,
    Vec<NormalizedFact>,
    Vec<NormalizedObjectFact>,
    Vec<NormalizedObjectFact>,
    Vec<NormalizedDataFact>,
    Vec<NormalizedDataFact>,
    Vec<NormalizedEqualityFact>,
    Vec<NormalizedInequalityFact>,
);

#[allow(clippy::too_many_arguments)]
fn merge_normalized_sources(
    phases: &[(SymbolPhase, NamedClassPhase)],
    class_maps: &[Vec<u32>],
    data_range_maps: &[Vec<u32>],
    individual_maps: &[Vec<u32>],
    source_literal_maps: &[Vec<u32>],
    data_value_maps: &[Vec<u32>],
    source_object_roles: Option<&[ObjectRolePhase]>,
    merged_object_roles: Option<&ObjectRolePhase>,
    source_data_roles: Option<&[DataRolePhase]>,
    merged_data_roles: Option<&DataRolePhase>,
    budget: &mut PhaseBudget,
) -> EncodedResult<NormalizedSources> {
    let mut raw_edges = Vec::new();
    let mut raw_disjoints = Vec::new();
    let mut raw_object_constraints = Vec::new();
    let mut raw_object_characteristics = Vec::new();
    let mut raw_data_domains = Vec::new();
    let mut raw_data_ranges = Vec::new();
    let mut raw_datatype_definitions = Vec::new();
    let mut raw_keys = Vec::new();
    let mut raw_data_functionalities = Vec::new();
    let mut raw_facts = Vec::new();
    let mut raw_object_facts = Vec::new();
    let mut raw_negative_object_facts = Vec::new();
    let mut raw_data_facts = Vec::new();
    let mut raw_negative_data_facts = Vec::new();
    let mut raw_equalities = Vec::new();
    let mut raw_inequalities = Vec::new();
    for (phase_index, (_, phase)) in phases.iter().enumerate() {
        let class_map = class_maps
            .get(phase_index)
            .ok_or_else(|| EncodedValidationError::invariant("merged class mapping disappeared"))?;
        let data_range_map = data_range_maps.get(phase_index).ok_or_else(|| {
            EncodedValidationError::invariant("merged data-range mapping disappeared")
        })?;
        let individual_map = individual_maps.get(phase_index).ok_or_else(|| {
            EncodedValidationError::invariant("merged individual mapping disappeared")
        })?;
        let source_literal_map = source_literal_maps.get(phase_index).ok_or_else(|| {
            EncodedValidationError::invariant("merged source-literal mapping disappeared")
        })?;
        let data_value_map = data_value_maps.get(phase_index).ok_or_else(|| {
            EncodedValidationError::invariant("merged data-value mapping disappeared")
        })?;
        for edge in &phase.normalized_edges {
            if edge.provenance.is_empty() {
                return Err(EncodedValidationError::invariant(
                    "merged named-class edge lost provenance",
                ));
            }
            let sub_class = mapped_id(class_map, edge.sub_class, "edge subclass")?;
            let super_class = mapped_id(class_map, edge.super_class, "edge superclass")?;
            for provenance in &edge.provenance {
                budget.claim_work(1)?;
                budget.claim_owned(size_of::<RawEdge>())?;
                raw_edges.try_reserve(1).map_err(|_| {
                    EncodedValidationError::resource("merged named-class edge allocation failed")
                })?;
                raw_edges.push(RawEdge {
                    sub_class,
                    sub_negative: edge.sub_negative,
                    super_class,
                    super_negative: edge.super_negative,
                    provenance: *provenance,
                });
            }
        }
        for disjoint in &phase.normalized_disjoints {
            if disjoint.provenance.is_empty() {
                return Err(EncodedValidationError::invariant(
                    "merged disjoint-class source lost provenance",
                ));
            }
            for provenance in &disjoint.provenance {
                budget.claim_work(disjoint.classes.len().saturating_add(1))?;
                let class_bytes = disjoint
                    .classes
                    .len()
                    .checked_mul(size_of::<ClassLiteral>())
                    .ok_or_else(|| {
                        EncodedValidationError::resource(
                            "merged disjoint-class member allocation overflowed",
                        )
                    })?;
                budget.claim_owned(size_of::<RawDisjoint>().saturating_add(class_bytes))?;
                let mut classes = Vec::new();
                classes
                    .try_reserve_exact(disjoint.classes.len())
                    .map_err(|_| {
                        EncodedValidationError::resource(
                            "merged disjoint-class member allocation failed",
                        )
                    })?;
                for literal in &disjoint.classes {
                    classes.push(ClassLiteral {
                        class_id: mapped_id(class_map, literal.class_id, "disjoint class")?,
                        negative: literal.negative,
                    });
                }
                raw_disjoints.try_reserve(1).map_err(|_| {
                    EncodedValidationError::resource(
                        "merged disjoint-class source allocation failed",
                    )
                })?;
                raw_disjoints.push(RawDisjoint {
                    classes,
                    guard_digest: disjoint.guard_digest,
                    provenance: *provenance,
                });
            }
        }
        if !phase.normalized_object_constraints.is_empty() {
            let source_roles = source_object_roles
                .and_then(|roles| roles.get(phase_index))
                .ok_or_else(|| {
                    EncodedValidationError::invariant(
                        "merged object-property constraints lost their source role domain",
                    )
                })?;
            let merged_roles = merged_object_roles.ok_or_else(|| {
                EncodedValidationError::invariant(
                    "merged object-property constraints lost their global role domain",
                )
            })?;
            for constraint in &phase.normalized_object_constraints {
                if constraint.provenance.is_empty() {
                    return Err(EncodedValidationError::invariant(
                        "merged object-property constraint lost provenance",
                    ));
                }
                let role_id =
                    remap_object_role(source_roles, merged_roles, constraint.role_id, budget)?;
                let class = ClassLiteral {
                    class_id: mapped_id(
                        class_map,
                        constraint.class.class_id,
                        "object-property constraint class",
                    )?,
                    negative: constraint.class.negative,
                };
                for provenance in &constraint.provenance {
                    budget.claim_work(1)?;
                    budget.claim_owned(size_of::<RawObjectConstraint>())?;
                    raw_object_constraints.try_reserve(1).map_err(|_| {
                        EncodedValidationError::resource(
                            "merged object-property constraint allocation failed",
                        )
                    })?;
                    raw_object_constraints.push(RawObjectConstraint {
                        kind: constraint.kind,
                        role_id,
                        class,
                        provenance: *provenance,
                    });
                }
            }
        }
        if !phase.normalized_object_characteristics.is_empty() {
            let source_roles = source_object_roles
                .and_then(|roles| roles.get(phase_index))
                .ok_or_else(|| {
                    EncodedValidationError::invariant(
                        "merged object-property characteristics lost their source role domain",
                    )
                })?;
            let merged_roles = merged_object_roles.ok_or_else(|| {
                EncodedValidationError::invariant(
                    "merged object-property characteristics lost their global role domain",
                )
            })?;
            for characteristic in &phase.normalized_object_characteristics {
                if characteristic.provenance.is_empty() {
                    return Err(EncodedValidationError::invariant(
                        "merged object-property characteristic lost provenance",
                    ));
                }
                let role_id =
                    remap_object_role(source_roles, merged_roles, characteristic.role_id, budget)?;
                for provenance in &characteristic.provenance {
                    budget.claim_work(1)?;
                    budget.claim_owned(size_of::<RawObjectCharacteristic>())?;
                    raw_object_characteristics.try_reserve(1).map_err(|_| {
                        EncodedValidationError::resource(
                            "merged object-property characteristic allocation failed",
                        )
                    })?;
                    raw_object_characteristics.push(RawObjectCharacteristic {
                        kind: characteristic.kind,
                        role_id,
                        provenance: *provenance,
                    });
                }
            }
        }
        if !phase.normalized_data_domains.is_empty() {
            let source_roles = source_data_roles
                .and_then(|roles| roles.get(phase_index))
                .ok_or_else(|| {
                    EncodedValidationError::invariant(
                        "merged data-property domains lost their source role domain",
                    )
                })?;
            let merged_roles = merged_data_roles.ok_or_else(|| {
                EncodedValidationError::invariant(
                    "merged data-property domains lost their global role domain",
                )
            })?;
            for domain in &phase.normalized_data_domains {
                if domain.provenance.is_empty() {
                    return Err(EncodedValidationError::invariant(
                        "merged data-property domain lost provenance",
                    ));
                }
                let role_id = remap_data_role(source_roles, merged_roles, domain.role_id, budget)?;
                let class = ClassLiteral {
                    class_id: mapped_id(
                        class_map,
                        domain.class.class_id,
                        "data-property domain class",
                    )?,
                    negative: domain.class.negative,
                };
                for provenance in &domain.provenance {
                    budget.claim_work(1)?;
                    budget.claim_owned(size_of::<RawDataDomain>())?;
                    raw_data_domains.try_reserve(1).map_err(|_| {
                        EncodedValidationError::resource(
                            "merged data-property domain allocation failed",
                        )
                    })?;
                    raw_data_domains.push(RawDataDomain {
                        role_id,
                        class,
                        provenance: *provenance,
                    });
                }
            }
        }
        if !phase.normalized_data_ranges.is_empty() {
            let source_roles = source_data_roles
                .and_then(|roles| roles.get(phase_index))
                .ok_or_else(|| {
                    EncodedValidationError::invariant(
                        "merged data-property ranges lost their source role domain",
                    )
                })?;
            let merged_roles = merged_data_roles.ok_or_else(|| {
                EncodedValidationError::invariant(
                    "merged data-property ranges lost their global role domain",
                )
            })?;
            for range in &phase.normalized_data_ranges {
                if range.provenance.is_empty() {
                    return Err(EncodedValidationError::invariant(
                        "merged data-property range lost provenance",
                    ));
                }
                let role_id = remap_data_role(source_roles, merged_roles, range.role_id, budget)?;
                let mapped_range = DataRangeLiteral {
                    range_id: mapped_id(
                        data_range_map,
                        range.range.range_id,
                        "data-property range datatype",
                    )?,
                    negative: range.range.negative,
                };
                for provenance in &range.provenance {
                    budget.claim_work(1)?;
                    budget.claim_owned(size_of::<RawDataRange>())?;
                    raw_data_ranges.try_reserve(1).map_err(|_| {
                        EncodedValidationError::resource(
                            "merged data-property range allocation failed",
                        )
                    })?;
                    raw_data_ranges.push(RawDataRange {
                        role_id,
                        range: mapped_range,
                        provenance: *provenance,
                    });
                }
            }
        }
        for definition in &phase.normalized_datatype_definitions {
            if definition.provenance.is_empty() {
                return Err(EncodedValidationError::invariant(
                    "merged datatype definition lost provenance",
                ));
            }
            let left_range = DataRangeLiteral {
                range_id: mapped_id(
                    data_range_map,
                    definition.left_range.range_id,
                    "defined datatype",
                )?,
                negative: definition.left_range.negative,
            };
            let right_range = DataRangeLiteral {
                range_id: mapped_id(
                    data_range_map,
                    definition.right_range.range_id,
                    "datatype defining range",
                )?,
                negative: definition.right_range.negative,
            };
            let (left_range, right_range) = if left_range <= right_range {
                (left_range, right_range)
            } else {
                (right_range, left_range)
            };
            for provenance in &definition.provenance {
                budget.claim_work(1)?;
                budget.claim_owned(size_of::<RawDatatypeDefinition>())?;
                raw_datatype_definitions.try_reserve(1).map_err(|_| {
                    EncodedValidationError::resource("merged datatype-definition allocation failed")
                })?;
                raw_datatype_definitions.push(RawDatatypeDefinition {
                    left_range,
                    right_range,
                    provenance: *provenance,
                });
            }
        }
        for key in &phase.normalized_keys {
            if key.provenance.is_empty() {
                return Err(EncodedValidationError::invariant(
                    "merged has-key source lost provenance",
                ));
            }
            let class = ClassLiteral {
                class_id: mapped_id(class_map, key.class.class_id, "has-key class")?,
                negative: key.class.negative,
            };
            budget.claim_owned(
                key.object_role_ids
                    .len()
                    .checked_add(key.data_role_ids.len())
                    .and_then(|value| value.checked_mul(size_of::<u32>()))
                    .ok_or_else(|| {
                        EncodedValidationError::resource(
                            "merged has-key role mapping allocation overflowed",
                        )
                    })?,
            )?;
            let mut object_role_ids = Vec::new();
            let mut data_role_ids = Vec::new();
            if !key.object_role_ids.is_empty() {
                let source_roles = source_object_roles
                    .and_then(|roles| roles.get(phase_index))
                    .ok_or_else(|| {
                        EncodedValidationError::invariant(
                            "merged has-key source lost its object-role domain",
                        )
                    })?;
                let merged_roles = merged_object_roles.ok_or_else(|| {
                    EncodedValidationError::invariant(
                        "merged has-key source lost its global object-role domain",
                    )
                })?;
                object_role_ids
                    .try_reserve_exact(key.object_role_ids.len())
                    .map_err(|_| {
                        EncodedValidationError::resource(
                            "merged has-key object-role allocation failed",
                        )
                    })?;
                for role_id in &key.object_role_ids {
                    object_role_ids.push(remap_object_role(
                        source_roles,
                        merged_roles,
                        *role_id,
                        budget,
                    )?);
                }
                budget.claim_work(sort_work(object_role_ids.len()))?;
                object_role_ids.sort_unstable();
                object_role_ids.dedup();
            }
            if !key.data_role_ids.is_empty() {
                let source_roles = source_data_roles
                    .and_then(|roles| roles.get(phase_index))
                    .ok_or_else(|| {
                        EncodedValidationError::invariant(
                            "merged has-key source lost its data-role domain",
                        )
                    })?;
                let merged_roles = merged_data_roles.ok_or_else(|| {
                    EncodedValidationError::invariant(
                        "merged has-key source lost its global data-role domain",
                    )
                })?;
                data_role_ids
                    .try_reserve_exact(key.data_role_ids.len())
                    .map_err(|_| {
                        EncodedValidationError::resource(
                            "merged has-key data-role allocation failed",
                        )
                    })?;
                for role_id in &key.data_role_ids {
                    data_role_ids.push(remap_data_role(
                        source_roles,
                        merged_roles,
                        *role_id,
                        budget,
                    )?);
                }
                budget.claim_work(sort_work(data_role_ids.len()))?;
                data_role_ids.sort_unstable();
                data_role_ids.dedup();
            }
            let role_bytes = object_role_ids
                .len()
                .checked_add(data_role_ids.len())
                .and_then(|value| value.checked_mul(size_of::<u32>()))
                .ok_or_else(|| {
                    EncodedValidationError::resource("merged has-key role allocation overflowed")
                })?;
            for provenance in &key.provenance {
                budget.claim_work(1)?;
                budget.claim_owned(size_of::<RawKey>().saturating_add(role_bytes))?;
                raw_keys.try_reserve(1).map_err(|_| {
                    EncodedValidationError::resource("merged has-key allocation failed")
                })?;
                raw_keys.push(RawKey {
                    class,
                    object_role_ids: object_role_ids.clone(),
                    data_role_ids: data_role_ids.clone(),
                    provenance: *provenance,
                });
            }
        }
        if !phase.normalized_data_functionalities.is_empty() {
            let source_roles = source_data_roles
                .and_then(|roles| roles.get(phase_index))
                .ok_or_else(|| {
                    EncodedValidationError::invariant(
                        "merged functional data properties lost their source role domain",
                    )
                })?;
            let merged_roles = merged_data_roles.ok_or_else(|| {
                EncodedValidationError::invariant(
                    "merged functional data properties lost their global role domain",
                )
            })?;
            for functionality in &phase.normalized_data_functionalities {
                if functionality.provenance.is_empty() {
                    return Err(EncodedValidationError::invariant(
                        "merged functional data property lost provenance",
                    ));
                }
                let role_id =
                    remap_data_role(source_roles, merged_roles, functionality.role_id, budget)?;
                for provenance in &functionality.provenance {
                    budget.claim_work(1)?;
                    budget.claim_owned(size_of::<RawDataFunctionality>())?;
                    raw_data_functionalities.try_reserve(1).map_err(|_| {
                        EncodedValidationError::resource(
                            "merged functional data-property allocation failed",
                        )
                    })?;
                    raw_data_functionalities.push(RawDataFunctionality {
                        role_id,
                        provenance: *provenance,
                    });
                }
            }
        }
        for fact in &phase.normalized_facts {
            if fact.provenance.is_empty() {
                return Err(EncodedValidationError::invariant(
                    "merged class-assertion source lost provenance",
                ));
            }
            let class_id = mapped_id(class_map, fact.class_id, "asserted class")?;
            let individual_id = mapped_id(
                individual_map,
                fact.individual_id,
                "class-assertion individual",
            )?;
            for provenance in &fact.provenance {
                budget.claim_work(1)?;
                budget.claim_owned(size_of::<RawFact>())?;
                raw_facts.try_reserve(1).map_err(|_| {
                    EncodedValidationError::resource(
                        "merged class-assertion source allocation failed",
                    )
                })?;
                raw_facts.push(RawFact {
                    class_id,
                    individual_id,
                    negative: fact.negative,
                    provenance: *provenance,
                });
            }
        }
        if !phase.normalized_object_facts.is_empty() {
            let source_roles = source_object_roles
                .and_then(|roles| roles.get(phase_index))
                .ok_or_else(|| {
                    EncodedValidationError::invariant(
                        "merged object-property assertions lost their source role domain",
                    )
                })?;
            let merged_roles = merged_object_roles.ok_or_else(|| {
                EncodedValidationError::invariant(
                    "merged object-property assertions lost their global role domain",
                )
            })?;
            for fact in &phase.normalized_object_facts {
                if fact.provenance.is_empty() {
                    return Err(EncodedValidationError::invariant(
                        "merged object-property assertion lost provenance",
                    ));
                }
                let role_id = remap_object_role(source_roles, merged_roles, fact.role_id, budget)?;
                let source_individual = mapped_id(
                    individual_map,
                    fact.source_individual,
                    "object-property assertion source individual",
                )?;
                let target_individual = mapped_id(
                    individual_map,
                    fact.target_individual,
                    "object-property assertion target individual",
                )?;
                for provenance in &fact.provenance {
                    budget.claim_work(1)?;
                    budget.claim_owned(size_of::<RawObjectFact>())?;
                    raw_object_facts.try_reserve(1).map_err(|_| {
                        EncodedValidationError::resource(
                            "merged object-property assertion allocation failed",
                        )
                    })?;
                    raw_object_facts.push(RawObjectFact {
                        role_id,
                        source_individual,
                        target_individual,
                        provenance: *provenance,
                    });
                }
            }
        }
        if !phase.normalized_data_facts.is_empty() {
            let source_roles = source_data_roles
                .and_then(|roles| roles.get(phase_index))
                .ok_or_else(|| {
                    EncodedValidationError::invariant(
                        "merged data-property assertions lost their source role domain",
                    )
                })?;
            let merged_roles = merged_data_roles.ok_or_else(|| {
                EncodedValidationError::invariant(
                    "merged data-property assertions lost their global role domain",
                )
            })?;
            for fact in &phase.normalized_data_facts {
                if fact.provenance.is_empty() {
                    return Err(EncodedValidationError::invariant(
                        "merged data-property assertion lost provenance",
                    ));
                }
                let role_id = remap_data_role(source_roles, merged_roles, fact.role_id, budget)?;
                let source_individual = mapped_id(
                    individual_map,
                    fact.source_individual,
                    "data-property assertion source individual",
                )?;
                let source_literal_id = mapped_id(
                    source_literal_map,
                    fact.source_literal_id,
                    "data-property assertion source literal",
                )?;
                let data_identity_id = mapped_id(
                    data_value_map,
                    fact.data_identity_id,
                    "data-property assertion data identity",
                )?;
                for provenance in &fact.provenance {
                    budget.claim_work(1)?;
                    budget.claim_owned(size_of::<RawDataFact>())?;
                    raw_data_facts.try_reserve(1).map_err(|_| {
                        EncodedValidationError::resource(
                            "merged data-property assertion allocation failed",
                        )
                    })?;
                    raw_data_facts.push(RawDataFact {
                        role_id,
                        source_individual,
                        source_literal_id,
                        data_identity_id,
                        provenance: *provenance,
                    });
                }
            }
        }
        if !phase.normalized_negative_data_facts.is_empty() {
            let source_roles = source_data_roles
                .and_then(|roles| roles.get(phase_index))
                .ok_or_else(|| {
                    EncodedValidationError::invariant(
                        "merged negative data-property assertions lost their source role domain",
                    )
                })?;
            let merged_roles = merged_data_roles.ok_or_else(|| {
                EncodedValidationError::invariant(
                    "merged negative data-property assertions lost their global role domain",
                )
            })?;
            for fact in &phase.normalized_negative_data_facts {
                if fact.provenance.is_empty() {
                    return Err(EncodedValidationError::invariant(
                        "merged negative data-property assertion lost provenance",
                    ));
                }
                let role_id = remap_data_role(source_roles, merged_roles, fact.role_id, budget)?;
                let source_individual = mapped_id(
                    individual_map,
                    fact.source_individual,
                    "negative data-property assertion source individual",
                )?;
                let source_literal_id = mapped_id(
                    source_literal_map,
                    fact.source_literal_id,
                    "negative data-property assertion source literal",
                )?;
                let data_identity_id = mapped_id(
                    data_value_map,
                    fact.data_identity_id,
                    "negative data-property assertion data identity",
                )?;
                for provenance in &fact.provenance {
                    budget.claim_work(1)?;
                    budget.claim_owned(size_of::<RawDataFact>())?;
                    raw_negative_data_facts.try_reserve(1).map_err(|_| {
                        EncodedValidationError::resource(
                            "merged negative data-property assertion allocation failed",
                        )
                    })?;
                    raw_negative_data_facts.push(RawDataFact {
                        role_id,
                        source_individual,
                        source_literal_id,
                        data_identity_id,
                        provenance: *provenance,
                    });
                }
            }
        }
        if !phase.normalized_negative_object_facts.is_empty() {
            let source_roles = source_object_roles
                .and_then(|roles| roles.get(phase_index))
                .ok_or_else(|| {
                    EncodedValidationError::invariant(
                        "merged negative object-property assertions lost their source role domain",
                    )
                })?;
            let merged_roles = merged_object_roles.ok_or_else(|| {
                EncodedValidationError::invariant(
                    "merged negative object-property assertions lost their global role domain",
                )
            })?;
            for fact in &phase.normalized_negative_object_facts {
                if fact.provenance.is_empty() {
                    return Err(EncodedValidationError::invariant(
                        "merged negative object-property assertion lost provenance",
                    ));
                }
                let role_id = remap_object_role(source_roles, merged_roles, fact.role_id, budget)?;
                let source_individual = mapped_id(
                    individual_map,
                    fact.source_individual,
                    "negative object-property assertion source individual",
                )?;
                let target_individual = mapped_id(
                    individual_map,
                    fact.target_individual,
                    "negative object-property assertion target individual",
                )?;
                for provenance in &fact.provenance {
                    budget.claim_work(1)?;
                    budget.claim_owned(size_of::<RawObjectFact>())?;
                    raw_negative_object_facts.try_reserve(1).map_err(|_| {
                        EncodedValidationError::resource(
                            "merged negative object-property assertion allocation failed",
                        )
                    })?;
                    raw_negative_object_facts.push(RawObjectFact {
                        role_id,
                        source_individual,
                        target_individual,
                        provenance: *provenance,
                    });
                }
            }
        }
        for equality in &phase.normalized_equalities {
            if equality.provenance.is_empty() {
                return Err(EncodedValidationError::invariant(
                    "merged same-individual source lost provenance",
                ));
            }
            let left_individual = mapped_id(
                individual_map,
                equality.left_individual,
                "same-individual left member",
            )?;
            let right_individual = mapped_id(
                individual_map,
                equality.right_individual,
                "same-individual right member",
            )?;
            for provenance in &equality.provenance {
                budget.claim_work(1)?;
                budget.claim_owned(size_of::<RawEqualityFact>())?;
                raw_equalities.try_reserve(1).map_err(|_| {
                    EncodedValidationError::resource(
                        "merged same-individual source allocation failed",
                    )
                })?;
                raw_equalities.push(RawEqualityFact {
                    left_individual,
                    right_individual,
                    statement_sha256: equality.statement_sha256,
                    provenance: *provenance,
                });
            }
        }
        for inequality in &phase.normalized_inequalities {
            if inequality.provenance.is_empty() {
                return Err(EncodedValidationError::invariant(
                    "merged different-individual source lost provenance",
                ));
            }
            let left_individual = mapped_id(
                individual_map,
                inequality.left_individual,
                "different-individual left member",
            )?;
            let right_individual = mapped_id(
                individual_map,
                inequality.right_individual,
                "different-individual right member",
            )?;
            for provenance in &inequality.provenance {
                budget.claim_work(1)?;
                budget.claim_owned(size_of::<RawInequalityFact>())?;
                raw_inequalities.try_reserve(1).map_err(|_| {
                    EncodedValidationError::resource(
                        "merged different-individual source allocation failed",
                    )
                })?;
                raw_inequalities.push(RawInequalityFact {
                    left_individual,
                    right_individual,
                    statement_sha256: inequality.statement_sha256,
                    provenance: *provenance,
                });
            }
        }
    }
    Ok((
        normalize_edges(raw_edges, budget)?,
        normalize_disjoints(raw_disjoints, budget)?,
        normalize_object_constraints(raw_object_constraints, budget)?,
        normalize_object_characteristics(raw_object_characteristics, budget)?,
        normalize_data_domains(raw_data_domains, budget)?,
        normalize_data_ranges(raw_data_ranges, budget)?,
        normalize_datatype_definitions(raw_datatype_definitions, budget)?,
        normalize_keys(raw_keys, budget)?,
        normalize_data_functionalities(raw_data_functionalities, budget)?,
        normalize_facts(raw_facts, budget)?,
        normalize_object_facts(raw_object_facts, budget)?,
        normalize_object_facts(raw_negative_object_facts, budget)?,
        normalize_data_facts(raw_data_facts, budget)?,
        normalize_data_facts(raw_negative_data_facts, budget)?,
        normalize_equalities(raw_equalities, budget)?,
        normalize_inequalities(raw_inequalities, budget)?,
    ))
}

fn binary_search_work(count: usize) -> usize {
    if count < 2 {
        1
    } else {
        usize::try_from(usize::BITS - (count - 1).leading_zeros())
            .unwrap_or(usize::MAX)
            .saturating_add(1)
    }
}

fn sort_work(count: usize) -> usize {
    if count < 2 {
        return count;
    }
    let comparisons = usize::BITS - (count - 1).leading_zeros();
    count.saturating_mul(usize::try_from(comparisons).unwrap_or(usize::MAX))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::encoded::model::ValidatedModel;
    use crate::encoded::symbols::{compile_symbol_phase, SymbolPhaseLimits};
    use crate::encoded::{EncodedColumns, EncodedLimits};

    #[derive(Clone, Debug)]
    struct OwnedColumns {
        root_kinds: Vec<u8>,
        root_ids: Vec<u8>,
        node_tags: Vec<u8>,
        node_field_offsets: Vec<u8>,
        field_kinds: Vec<u8>,
        field_values: Vec<u8>,
        field_lengths: Vec<u8>,
        item_kinds: Vec<u8>,
        item_values: Vec<u8>,
        item_lengths: Vec<u8>,
        scalar_bytes: Vec<u8>,
    }

    impl OwnedColumns {
        fn borrowed(&self) -> EncodedColumns<&[u8]> {
            EncodedColumns {
                root_kinds: &self.root_kinds,
                root_ids: &self.root_ids,
                node_tags: &self.node_tags,
                node_field_offsets: &self.node_field_offsets,
                field_kinds: &self.field_kinds,
                field_values: &self.field_values,
                field_lengths: &self.field_lengths,
                item_kinds: &self.item_kinds,
                item_values: &self.item_values,
                item_lengths: &self.item_lengths,
                scalar_bytes: &self.scalar_bytes,
            }
        }
    }

    fn le16(values: &[u16]) -> Vec<u8> {
        values
            .iter()
            .flat_map(|value| value.to_le_bytes())
            .collect()
    }

    fn le32(values: &[u32]) -> Vec<u8> {
        values
            .iter()
            .flat_map(|value| value.to_le_bytes())
            .collect()
    }

    fn le64(values: &[u64]) -> Vec<u8> {
        values
            .iter()
            .flat_map(|value| value.to_le_bytes())
            .collect()
    }

    #[test]
    fn projected_clause_atoms_preserve_scalar_lexical_predicate_order() {
        let mut identifiers = [2, 10, 1, 11, 100, 0, u32::MAX];
        identifiers.sort_by(|left, right| decimal_lexical_cmp(*left, *right));
        assert_eq!(identifiers, [0, 1, 10, 100, 11, 2, u32::MAX]);
    }

    #[test]
    fn integer_identities_are_exact_bounded_and_resource_limited() -> EncodedResult<()> {
        let mut budget = PhaseBudget::new(NamedClassPhaseLimits::default());
        assert_eq!(
            integer_data_identity_key("+0001", (None, None), &mut budget)?,
            b"pyhermit:data-identity:v1\0[\"numeric-rational-hex-v1\",\"+1\",\"+1\"]"
        );
        assert_eq!(
            integer_data_identity_key("-0", (None, None), &mut budget)?,
            b"pyhermit:data-identity:v1\0[\"numeric-rational-hex-v1\",\"+0\",\"+1\"]"
        );

        let unsigned_byte = integer_datatype_bounds(
            "http://www.w3.org/2001/XMLSchema#unsignedByte",
        )
        .ok_or_else(|| EncodedValidationError::invariant("unsigned-byte bounds disappeared"))?;
        let out_of_range = integer_data_identity_key("256", unsigned_byte, &mut budget).err();
        assert!(out_of_range.is_some_and(|error| {
            error.code == "NATIVE_ENCODED_INVARIANT"
                && error.message.contains("datatype value space")
        }));

        let limits = NamedClassPhaseLimits {
            max_numeric_digits: 2,
            ..NamedClassPhaseLimits::default()
        };
        let mut limited = PhaseBudget::new(limits);
        let resource = integer_data_identity_key("100", (None, None), &mut limited).err();
        assert!(resource.is_some_and(|error| {
            error.code == "NATIVE_ENCODED_RESOURCE_LIMIT"
                && error.message.contains("numeric digit count")
        }));
        Ok(())
    }

    #[test]
    fn decimal_identities_reduce_exactly_and_reject_hostile_scales() -> EncodedResult<()> {
        let mut budget = PhaseBudget::new(NamedClassPhaseLimits::default());
        assert_eq!(
            decimal_data_identity_key("0.2500", &mut budget)?,
            b"pyhermit:data-identity:v1\0[\"numeric-rational-hex-v1\",\"+1\",\"+4\"]"
        );
        assert_eq!(
            decimal_data_identity_key("-0.00", &mut budget)?,
            b"pyhermit:data-identity:v1\0[\"numeric-rational-hex-v1\",\"+0\",\"+1\"]"
        );
        assert_eq!(
            decimal_data_identity_key("12.", &mut budget)?,
            b"pyhermit:data-identity:v1\0[\"numeric-rational-hex-v1\",\"+c\",\"+1\"]"
        );

        let invalid = decimal_data_identity_key("1e2", &mut budget).err();
        assert!(invalid.is_some_and(|error| {
            error.code == "NATIVE_ENCODED_INVARIANT"
                && error.message.contains("datatype lexical space")
        }));

        let limits = NamedClassPhaseLimits {
            max_decimal_exponent: 2,
            ..NamedClassPhaseLimits::default()
        };
        let mut limited = PhaseBudget::new(limits);
        let resource = decimal_data_identity_key("0.001", &mut limited).err();
        assert!(resource.is_some_and(|error| {
            error.code == "NATIVE_ENCODED_RESOURCE_LIMIT" && error.message.contains("decimal scale")
        }));
        Ok(())
    }

    #[test]
    fn rational_identities_reduce_exactly_and_reject_zero_denominators() -> EncodedResult<()> {
        let mut budget = PhaseBudget::new(NamedClassPhaseLimits::default());
        assert_eq!(
            rational_literal_data_identity_key("6/8", &mut budget)?,
            b"pyhermit:data-identity:v1\0[\"numeric-rational-hex-v1\",\"+3\",\"+4\"]"
        );
        assert_eq!(
            rational_literal_data_identity_key("-0/7", &mut budget)?,
            b"pyhermit:data-identity:v1\0[\"numeric-rational-hex-v1\",\"+0\",\"+1\"]"
        );

        for lexical in ["1/0", "1/+2", "1/2/3"] {
            let invalid = rational_literal_data_identity_key(lexical, &mut budget).err();
            assert!(invalid.is_some_and(|error| {
                error.code == "NATIVE_ENCODED_INVARIANT"
                    && error.message.contains("datatype lexical space")
            }));
        }

        let limits = NamedClassPhaseLimits {
            max_numeric_digits: 2,
            ..NamedClassPhaseLimits::default()
        };
        let mut limited = PhaseBudget::new(limits);
        let resource = rational_literal_data_identity_key("1/100", &mut limited).err();
        assert!(resource.is_some_and(|error| {
            error.code == "NATIVE_ENCODED_RESOURCE_LIMIT"
                && error.message.contains("denominator digit count")
        }));
        Ok(())
    }

    #[test]
    fn ieee_identities_are_bit_exact_and_preserve_signed_zero() -> EncodedResult<()> {
        let mut budget = PhaseBudget::new(NamedClassPhaseLimits::default());
        assert_eq!(
            ieee_data_identity_key("-0", IEEEWidth::Float32, &mut budget)?,
            b"pyhermit:data-identity:v1\0[\"ieee-identity-v1\",\"float32\",\"80000000\"]"
        );
        assert_eq!(
            ieee_data_identity_key("NaN", IEEEWidth::Float32, &mut budget)?,
            b"pyhermit:data-identity:v1\0[\"ieee-identity-v1\",\"float32\",\"7fc00000\"]"
        );
        assert_eq!(
            ieee_data_identity_key("1.401298464324817e-45", IEEEWidth::Float32, &mut budget,)?,
            b"pyhermit:data-identity:v1\0[\"ieee-identity-v1\",\"float32\",\"00000001\"]"
        );
        assert_eq!(
            ieee_data_identity_key("1.0", IEEEWidth::Float64, &mut budget)?,
            b"pyhermit:data-identity:v1\0[\"ieee-identity-v1\",\"float64\",\"3ff0000000000000\"]"
        );
        assert_eq!(
            ieee_data_identity_key("-INF", IEEEWidth::Float64, &mut budget)?,
            b"pyhermit:data-identity:v1\0[\"ieee-identity-v1\",\"float64\",\"fff0000000000000\"]"
        );

        let invalid = ieee_data_identity_key("Infinity", IEEEWidth::Float32, &mut budget).err();
        assert!(invalid.is_some_and(|error| {
            error.code == "NATIVE_ENCODED_INVARIANT"
                && error.message.contains("datatype lexical space")
        }));
        Ok(())
    }

    #[test]
    fn binary_identities_decode_whitespace_and_padding_exactly() -> EncodedResult<()> {
        let mut budget = PhaseBudget::new(NamedClassPhaseLimits::default());
        assert_eq!(
            binary_data_identity_key(" \t0Aff\r\n ", EncodedBinaryKind::Hex, &mut budget)?,
            b"pyhermit:data-identity:v1\0[\"binary-identity-v1\",\"hexBinary\",\"0aff\"]"
        );
        assert_eq!(
            binary_data_identity_key(" C v 8 = ", EncodedBinaryKind::Base64, &mut budget)?,
            b"pyhermit:data-identity:v1\0[\"binary-identity-v1\",\"base64Binary\",\"0aff\"]"
        );
        for lexical in ["A===", "Cv9=", "C=8="] {
            let invalid =
                binary_data_identity_key(lexical, EncodedBinaryKind::Base64, &mut budget).err();
            assert!(invalid.is_some_and(|error| {
                error.code == "NATIVE_ENCODED_INVARIANT"
                    && error.message.contains("datatype lexical space")
            }));
        }

        let limits = NamedClassPhaseLimits {
            max_binary_bytes: 1,
            ..NamedClassPhaseLimits::default()
        };
        let mut limited = PhaseBudget::new(limits);
        let resource = binary_data_identity_key("0aff", EncodedBinaryKind::Hex, &mut limited).err();
        assert!(resource.is_some_and(|error| {
            error.code == "NATIVE_ENCODED_RESOURCE_LIMIT"
                && error.message.contains("decoded binary byte count")
        }));
        Ok(())
    }

    #[test]
    fn uri_identities_preserve_relative_spelling_and_unicode_exactly() -> EncodedResult<()> {
        let mut budget = PhaseBudget::new(NamedClassPhaseLimits::default());
        assert_eq!(
            uri_data_identity_key("../café?q=one two", &mut budget)?,
            "pyhermit:data-identity:v1\0[\"any-uri-v1\",\"../café?q=one two\"]".as_bytes()
        );
        assert_eq!(
            uri_data_identity_key("", &mut budget)?,
            b"pyhermit:data-identity:v1\0[\"any-uri-v1\",\"\"]"
        );
        Ok(())
    }

    #[test]
    fn date_time_identities_cover_arbitrary_years_offsets_and_end_of_day() -> EncodedResult<()> {
        let mut budget = PhaseBudget::new(NamedClassPhaseLimits::default());
        assert_eq!(
            date_time_data_identity_key(" 1970-01-01T00:00:00Z ", false, &mut budget)?,
            b"pyhermit:data-identity:v1\0[\"date-time-identity-v1\",\"+e7791f700\",\"+1\",0,false]"
        );
        assert_eq!(
            date_time_data_identity_key("2000-02-29T24:00:00+00:00", false, &mut budget)?,
            b"pyhermit:data-identity:v1\0[\"date-time-identity-v1\",\"+eb04e5480\",\"+1\",0,false]"
        );
        assert_eq!(
            date_time_data_identity_key("-0001-01-01T00:00:00.25-14:00", false, &mut budget)?,
            b"pyhermit:data-identity:v1\0[\"date-time-identity-v1\",\"-f0ee1ff\",\"+4\",-840,false]"
        );

        for (lexical, require_timezone) in [
            ("2024-01-01T00:00:00", true),
            ("2023-02-29T00:00:00Z", false),
            ("-0000-01-01T00:00:00Z", false),
            ("2024-01-01T24:00:00.1Z", false),
        ] {
            let invalid = date_time_data_identity_key(lexical, require_timezone, &mut budget).err();
            assert!(invalid.is_some_and(|error| {
                error.code == "NATIVE_ENCODED_INVARIANT"
                    && error.message.contains("datatype lexical space")
            }));
        }
        Ok(())
    }

    fn equivalent_classes() -> OwnedColumns {
        OwnedColumns {
            root_kinds: vec![2],
            root_ids: le32(&[5]),
            node_tags: le16(&[1, 1, 2, 2, 62]),
            node_field_offsets: le64(&[0, 1, 2, 4, 6, 8]),
            field_kinds: vec![2, 2, 5, 1, 5, 1, 6, 6],
            field_values: le64(&[0, 5, 10, 1, 15, 2, 0, 2]),
            field_lengths: le64(&[5, 5, 5, 0, 5, 0, 2, 0]),
            item_kinds: vec![1, 1],
            item_values: le64(&[3, 4]),
            item_lengths: le64(&[0, 0]),
            scalar_bytes: b"urn:Aurn:Bclassclass".to_vec(),
        }
    }

    fn disjoint_classes() -> OwnedColumns {
        let mut owned = equivalent_classes();
        owned.node_tags = le16(&[1, 1, 2, 2, 63]);
        owned
    }

    fn class_assertion() -> OwnedColumns {
        OwnedColumns {
            root_kinds: vec![super::super::ROOT_AXIOM],
            root_ids: le32(&[5]),
            node_tags: le16(&[1, 1, 2, 2, CLASS_ASSERTION_TAG]),
            node_field_offsets: le64(&[0, 1, 2, 4, 6, 9]),
            field_kinds: vec![
                super::super::COMPONENT_TEXT,
                super::super::COMPONENT_TEXT,
                super::super::COMPONENT_ENUM,
                super::super::COMPONENT_NODE,
                super::super::COMPONENT_ENUM,
                super::super::COMPONENT_NODE,
                super::super::COMPONENT_NODE,
                super::super::COMPONENT_NODE,
                super::super::COMPONENT_SET,
            ],
            field_values: le64(&[0, 5, 10, 1, 15, 2, 3, 4, 0]),
            field_lengths: le64(&[5, 5, 5, 0, 16, 0, 0, 0, 0]),
            item_kinds: Vec::new(),
            item_values: Vec::new(),
            item_lengths: Vec::new(),
            scalar_bytes: b"urn:Aurn:iclassnamed_individual".to_vec(),
        }
    }

    fn same_individual() -> OwnedColumns {
        OwnedColumns {
            root_kinds: vec![super::super::ROOT_AXIOM],
            root_ids: le32(&[5]),
            node_tags: le16(&[1, 1, 2, 2, SAME_INDIVIDUAL_TAG]),
            node_field_offsets: le64(&[0, 1, 2, 4, 6, 8]),
            field_kinds: vec![
                super::super::COMPONENT_TEXT,
                super::super::COMPONENT_TEXT,
                super::super::COMPONENT_ENUM,
                super::super::COMPONENT_NODE,
                super::super::COMPONENT_ENUM,
                super::super::COMPONENT_NODE,
                super::super::COMPONENT_SET,
                super::super::COMPONENT_SET,
            ],
            field_values: le64(&[0, 5, 10, 1, 26, 2, 0, 2]),
            field_lengths: le64(&[5, 5, 16, 0, 16, 0, 2, 0]),
            item_kinds: vec![super::super::COMPONENT_NODE, super::super::COMPONENT_NODE],
            item_values: le64(&[3, 4]),
            item_lengths: le64(&[0, 0]),
            scalar_bytes: b"urn:aurn:bnamed_individualnamed_individual".to_vec(),
        }
    }

    fn different_individuals() -> OwnedColumns {
        let mut owned = same_individual();
        owned.node_tags = le16(&[1, 1, 2, 2, DIFFERENT_INDIVIDUALS_TAG]);
        owned
    }

    #[test]
    fn equivalent_named_classes_freeze_existing_native_records() -> EncodedResult<()> {
        let owned = equivalent_classes();
        let model = ValidatedModel::new(owned.borrowed(), EncodedLimits::default())?;
        let symbols = compile_symbol_phase(&model, SymbolPhaseLimits::default())?;
        let phase = compile_named_class_phase(&model, &symbols, NamedClassPhaseLimits::default())?;

        assert_eq!(phase.class_domain.kind, SymbolKind::ClassExpression);
        assert_eq!(phase.class_domain.values.len(), 4);
        assert_eq!(phase.class_signature.len(), 4);
        assert!(phase
            .class_signature
            .iter()
            .all(|binding| !binding.declared));
        assert_eq!(phase.compiled_roots, 1);
        assert_eq!(phase.deferred_roots, 0);
        assert_eq!(phase.predicates.len(), 3);
        assert_eq!(phase.clauses.len(), 3);
        assert_eq!(phase.provenance.len(), 2);
        assert!(phase
            .predicates
            .iter()
            .all(|predicate| predicate.kind == PredicateKind::Concept));
        assert!(phase.clauses.iter().all(|clause| {
            clause.body.len() == 1 && clause.join_order == [0] && clause.provenance_ids.len() == 1
        }));
        let manifest: serde_json::Value = serde_json::from_slice(&phase.canonical_manifest_json()?)
            .map_err(|_| EncodedValidationError::invariant("manifest did not decode"))?;
        assert_eq!(manifest["family"], "named_class_axioms");
        assert_eq!(manifest["compiled_roots"], 1);
        Ok(())
    }

    #[test]
    fn duplicate_source_slices_merge_to_one_canonical_owned_program() -> EncodedResult<()> {
        let first_owned = class_assertion();
        let first_model = ValidatedModel::new(first_owned.borrowed(), EncodedLimits::default())?;
        let first_symbols = compile_symbol_phase(&first_model, SymbolPhaseLimits::default())?;
        let first_named = compile_named_class_phase(
            &first_model,
            &first_symbols,
            NamedClassPhaseLimits::default(),
        )?;
        let second_owned = class_assertion();
        let second_model = ValidatedModel::new(second_owned.borrowed(), EncodedLimits::default())?;
        let second_symbols = compile_symbol_phase(&second_model, SymbolPhaseLimits::default())?;
        let second_named = compile_named_class_phase(
            &second_model,
            &second_symbols,
            NamedClassPhaseLimits::default(),
        )?;
        let phases = vec![
            (first_symbols, first_named.clone()),
            (second_symbols, second_named),
        ];

        let merged = merge_named_class_phases(&phases, NamedClassPhaseLimits::default())?;

        let expected: serde_json::Value =
            serde_json::from_slice(&first_named.canonical_manifest_json()?)
                .map_err(|_| EncodedValidationError::invariant("manifest did not decode"))?;
        let actual: serde_json::Value = serde_json::from_slice(&merged.canonical_manifest_json()?)
            .map_err(|_| EncodedValidationError::invariant("manifest did not decode"))?;
        assert_eq!(actual, expected);
        assert_eq!(merged.positive_facts, first_named.positive_facts);
        assert_eq!(merged.clauses, first_named.clauses);
        Ok(())
    }

    #[test]
    fn multi_slice_merge_is_bounded_and_transactional() -> EncodedResult<()> {
        let first_owned = equivalent_classes();
        let first_model = ValidatedModel::new(first_owned.borrowed(), EncodedLimits::default())?;
        let first_symbols = compile_symbol_phase(&first_model, SymbolPhaseLimits::default())?;
        let first_named = compile_named_class_phase(
            &first_model,
            &first_symbols,
            NamedClassPhaseLimits::default(),
        )?;
        let second_owned = class_assertion();
        let second_model = ValidatedModel::new(second_owned.borrowed(), EncodedLimits::default())?;
        let second_symbols = compile_symbol_phase(&second_model, SymbolPhaseLimits::default())?;
        let second_named = compile_named_class_phase(
            &second_model,
            &second_symbols,
            NamedClassPhaseLimits::default(),
        )?;
        let phases = vec![(first_symbols, first_named), (second_symbols, second_named)];
        let before = phases.clone();
        let limits = NamedClassPhaseLimits {
            max_slices: 1,
            ..NamedClassPhaseLimits::default()
        };

        let error = merge_named_class_phases(&phases, limits).err();

        assert!(error.is_some_and(|value| {
            value.code == "NATIVE_ENCODED_RESOURCE_LIMIT" && value.message.contains("slice count")
        }));
        assert_eq!(phases, before);
        Ok(())
    }

    #[test]
    fn clause_limit_rolls_back_without_mutating_symbol_transaction() -> EncodedResult<()> {
        let owned = equivalent_classes();
        let model = ValidatedModel::new(owned.borrowed(), EncodedLimits::default())?;
        let symbols = compile_symbol_phase(&model, SymbolPhaseLimits::default())?;
        let before = symbols.clone();
        let limits = NamedClassPhaseLimits {
            max_clauses: 0,
            ..NamedClassPhaseLimits::default()
        };
        let error = compile_named_class_phase(&model, &symbols, limits).err();
        assert!(error.is_some_and(|value| {
            value.code == "NATIVE_ENCODED_RESOURCE_LIMIT" && value.message.contains("clause")
        }));
        assert_eq!(symbols, before);
        Ok(())
    }

    #[test]
    fn disjoint_named_classes_compile_linear_guard_records() -> EncodedResult<()> {
        let owned = disjoint_classes();
        let model = ValidatedModel::new(owned.borrowed(), EncodedLimits::default())?;
        let symbols = compile_symbol_phase(&model, SymbolPhaseLimits::default())?;
        let phase = compile_named_class_phase(&model, &symbols, NamedClassPhaseLimits::default())?;

        assert_eq!(phase.compiled_roots, 1);
        assert_eq!(phase.deferred_roots, 0);
        assert_eq!(
            phase
                .predicates
                .iter()
                .filter(|predicate| predicate.kind == PredicateKind::DisjointGuard)
                .count(),
            2
        );
        assert_eq!(phase.clauses.len(), 5);
        assert!(phase.clauses.iter().any(|clause| clause.body.len() == 2));
        Ok(())
    }

    #[test]
    fn named_class_assertion_freezes_signature_and_builtin_facts() -> EncodedResult<()> {
        let owned = class_assertion();
        let model = ValidatedModel::new(owned.borrowed(), EncodedLimits::default())?;
        let symbols = compile_symbol_phase(&model, SymbolPhaseLimits::default())?;
        let phase = compile_named_class_phase(&model, &symbols, NamedClassPhaseLimits::default())?;

        assert_eq!(phase.compiled_roots, 1);
        assert_eq!(phase.deferred_roots, 0);
        assert_eq!(phase.individual_domain.kind, SymbolKind::Individual);
        assert_eq!(phase.individual_domain.values.len(), 1);
        assert_eq!(phase.individual_signature.len(), 1);
        assert!(!phase.individual_signature[0].declared);
        assert_eq!(phase.named_individuals, [0]);
        assert_eq!(phase.predicates.len(), 4);
        assert_eq!(phase.clauses.len(), 1);
        assert_eq!(phase.positive_facts.len(), 3);
        assert_eq!(phase.provenance.len(), 2);
        assert!(phase.predicates.iter().any(|predicate| {
            predicate.kind == PredicateKind::NamedIndividual
                && predicate.internal_key.as_deref() == Some("named-individual")
        }));
        assert!(phase.positive_facts.iter().all(|fact| {
            fact.arguments == [DecodedTerm::Individual { individual_id: 0 }]
                && !fact.provenance_ids.is_empty()
        }));
        Ok(())
    }

    #[test]
    fn named_same_individual_freezes_binary_equality_fact() -> EncodedResult<()> {
        let owned = same_individual();
        let model = ValidatedModel::new(owned.borrowed(), EncodedLimits::default())?;
        let symbols = compile_symbol_phase(&model, SymbolPhaseLimits::default())?;
        let phase = compile_named_class_phase(&model, &symbols, NamedClassPhaseLimits::default())?;

        assert_eq!(phase.compiled_roots, 1);
        assert_eq!(phase.deferred_roots, 0);
        assert_eq!(phase.individual_domain.values.len(), 2);
        assert_eq!(phase.named_individuals, [0, 1]);
        assert_eq!(phase.predicates.len(), 4);
        assert_eq!(phase.clauses.len(), 1);
        assert_eq!(phase.positive_facts.len(), 5);
        assert_eq!(phase.provenance.len(), 2);
        let equality = phase
            .predicates
            .iter()
            .find(|predicate| predicate.kind == PredicateKind::Equality)
            .ok_or_else(|| EncodedValidationError::invariant("equality predicate is missing"))?;
        assert_eq!(
            equality.argument_sorts,
            [TermSort::Object, TermSort::Object]
        );
        assert!(phase.positive_facts.iter().any(|fact| {
            fact.predicate_id == equality.predicate_id
                && fact.arguments
                    == [
                        DecodedTerm::Individual { individual_id: 0 },
                        DecodedTerm::Individual { individual_id: 1 },
                    ]
                && fact.provenance_ids.len() == 1
        }));
        Ok(())
    }

    #[test]
    fn named_different_individuals_freezes_binary_inequality_fact() -> EncodedResult<()> {
        let owned = different_individuals();
        let model = ValidatedModel::new(owned.borrowed(), EncodedLimits::default())?;
        let symbols = compile_symbol_phase(&model, SymbolPhaseLimits::default())?;
        let phase = compile_named_class_phase(&model, &symbols, NamedClassPhaseLimits::default())?;

        assert_eq!(phase.compiled_roots, 1);
        assert_eq!(phase.deferred_roots, 0);
        assert_eq!(phase.individual_domain.values.len(), 2);
        assert_eq!(phase.named_individuals, [0, 1]);
        assert_eq!(phase.predicates.len(), 4);
        assert_eq!(phase.clauses.len(), 1);
        assert_eq!(phase.positive_facts.len(), 5);
        assert_eq!(phase.provenance.len(), 2);
        let inequality = phase
            .predicates
            .iter()
            .find(|predicate| predicate.kind == PredicateKind::Inequality)
            .ok_or_else(|| EncodedValidationError::invariant("inequality predicate is missing"))?;
        assert_eq!(
            inequality.argument_sorts,
            [TermSort::Object, TermSort::Object]
        );
        assert!(phase.positive_facts.iter().any(|fact| {
            fact.predicate_id == inequality.predicate_id
                && fact.arguments
                    == [
                        DecodedTerm::Individual { individual_id: 0 },
                        DecodedTerm::Individual { individual_id: 1 },
                    ]
                && fact.provenance_ids.len() == 1
        }));
        Ok(())
    }

    #[test]
    fn different_individual_pair_limit_rolls_back_without_mutating_symbols() -> EncodedResult<()> {
        let owned = different_individuals();
        let model = ValidatedModel::new(owned.borrowed(), EncodedLimits::default())?;
        let symbols = compile_symbol_phase(&model, SymbolPhaseLimits::default())?;
        let before = symbols.clone();
        let limits = NamedClassPhaseLimits {
            max_facts: 0,
            ..NamedClassPhaseLimits::default()
        };
        let error = compile_named_class_phase(&model, &symbols, limits).err();
        assert!(error.is_some_and(|value| {
            value.code == "NATIVE_ENCODED_RESOURCE_LIMIT"
                && value.message.contains("different-individual fact")
        }));
        assert_eq!(symbols, before);
        Ok(())
    }

    #[test]
    fn fact_limit_rolls_back_without_mutating_symbol_transaction() -> EncodedResult<()> {
        let owned = class_assertion();
        let model = ValidatedModel::new(owned.borrowed(), EncodedLimits::default())?;
        let symbols = compile_symbol_phase(&model, SymbolPhaseLimits::default())?;
        let before = symbols.clone();
        let limits = NamedClassPhaseLimits {
            max_facts: 0,
            ..NamedClassPhaseLimits::default()
        };
        let error = compile_named_class_phase(&model, &symbols, limits).err();
        assert!(error.is_some_and(|value| {
            value.code == "NATIVE_ENCODED_RESOURCE_LIMIT" && value.message.contains("fact")
        }));
        assert_eq!(symbols, before);
        Ok(())
    }
}
