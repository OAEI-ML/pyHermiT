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
use super::model::{
    CollectionRef, ComponentKind, ComponentValue, NodeId, NodeRef, ScalarRef, ValidatedModel,
};
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
const DATA_INTERSECTION_OF_TAG: u16 = 21;
const DATA_UNION_OF_TAG: u16 = 22;
const DATA_COMPLEMENT_OF_TAG: u16 = 23;
const DATA_ONE_OF_TAG: u16 = 24;
const DATATYPE_RESTRICTION_TAG: u16 = 25;
const OBJECT_INTERSECTION_OF_TAG: u16 = 30;
const OBJECT_UNION_OF_TAG: u16 = 31;
const OBJECT_COMPLEMENT_OF_TAG: u16 = 32;
const OBJECT_ONE_OF_TAG: u16 = 33;
const OBJECT_SOME_VALUES_FROM_TAG: u16 = 34;
const OBJECT_ALL_VALUES_FROM_TAG: u16 = 35;
const OBJECT_HAS_VALUE_TAG: u16 = 36;
const OBJECT_HAS_SELF_TAG: u16 = 37;
const OBJECT_MIN_CARDINALITY_TAG: u16 = 38;
const OBJECT_MAX_CARDINALITY_TAG: u16 = 39;
const OBJECT_EXACT_CARDINALITY_TAG: u16 = 40;
const DATA_SOME_VALUES_FROM_TAG: u16 = 41;
const DATA_ALL_VALUES_FROM_TAG: u16 = 42;
const DATA_HAS_VALUE_TAG: u16 = 43;
const DATA_MIN_CARDINALITY_TAG: u16 = 44;
const DATA_MAX_CARDINALITY_TAG: u16 = 45;
const DATA_EXACT_CARDINALITY_TAG: u16 = 46;
const SUBCLASS_TAG: u16 = 61;
const EQUIVALENT_CLASSES_TAG: u16 = 62;
const DISJOINT_CLASSES_TAG: u16 = 63;
const DISJOINT_UNION_TAG: u16 = 64;
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
const DEFINITION_DIGEST_DOMAIN: &[u8] = b"pyhermit:normalization-definition:v1\0";
const GENERATED_CLASS_IRI_PREFIX: &str = "urn:pyhermit:generated:v1:class:";
const GENERATED_DATA_IRI_PREFIX: &str = "urn:pyhermit:generated:v1:data:";
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
const BOTTOM_DATA_IRI: &str = "http://www.w3.org/2002/07/owl#bottomDataProperty";

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
    entity_domain: DecodedSymbolDomain,
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
    normalized_boolean_clauses: Vec<NormalizedBooleanClause>,
    normalized_disjoints: Vec<NormalizedDisjoint>,
    normalized_object_constraints: Vec<NormalizedObjectConstraint>,
    normalized_data_constraints: Vec<NormalizedDataConstraint>,
    normalized_object_characteristics: Vec<NormalizedObjectCharacteristic>,
    normalized_data_domains: Vec<NormalizedDataDomain>,
    normalized_data_ranges: Vec<NormalizedDataRange>,
    normalized_data_boolean_clauses: Vec<NormalizedDataBooleanClause>,
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
    generated: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct NormalizedEdge {
    sub_class: u32,
    sub_negative: bool,
    super_class: u32,
    super_negative: bool,
    provenance: Vec<[u8; 32]>,
    generated: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct RawBooleanClause {
    body: Vec<ClassLiteral>,
    head: Vec<ClassLiteral>,
    provenance: [u8; 32],
    generated: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct NormalizedBooleanClause {
    body: Vec<ClassLiteral>,
    head: Vec<ClassLiteral>,
    provenance: Vec<[u8; 32]>,
    generated: bool,
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

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum DefinitionPolarity {
    Positive,
    Negative,
}

impl DefinitionPolarity {
    const fn as_str(self) -> &'static str {
        match self {
            Self::Positive => "positive",
            Self::Negative => "negative",
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ClassBooleanDefinition {
    expressions: Vec<NodeId>,
    roots: Vec<NodeId>,
    expression_key: Vec<u8>,
    expression_symbols: Vec<ClassExpressionSymbolSeed>,
    data_expression_symbols: Vec<DataRangeSymbolSeed>,
    intersection: bool,
    operands: Vec<ClassBooleanOperand>,
    object_self_role_id: Option<u32>,
    object_quantifier: Option<ObjectQuantifierDefinition>,
    object_cardinality: Option<ObjectCardinalityDefinition>,
    data_quantifier: Option<DataQuantifierDefinition>,
    data_cardinality: Option<DataCardinalityDefinition>,
    data_dependencies: Vec<DataBooleanDefinition>,
    complement: bool,
    polarity: DefinitionPolarity,
    generated_key: Vec<u8>,
    generated_display: String,
    provenance: Vec<[u8; 32]>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ClassExpressionSymbolSeed {
    key: Vec<u8>,
    display: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum ClassBooleanOperand {
    Atomic(AtomicClassSelection),
    Nominal {
        key: Vec<u8>,
        individual_entity_ids: Vec<u32>,
        negative: bool,
    },
    Generated {
        key: Vec<u8>,
        negative: bool,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct NormalizedAtomicClassTerm {
    selection: AtomicClassSelection,
    key: Vec<u8>,
    symbols: Vec<ClassExpressionSymbolSeed>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct NormalizedNominalClassTerm {
    base_key: Vec<u8>,
    key: Vec<u8>,
    individual_entity_ids: Vec<u32>,
    negative: bool,
    symbols: Vec<ClassExpressionSymbolSeed>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct NormalizedClassBooleanTerm {
    intersection: bool,
    key: Vec<u8>,
    operands: Vec<NormalizedClassTerm>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct NormalizedObjectSelfTerm {
    role_id: u32,
    base_key: Vec<u8>,
    key: Vec<u8>,
    complemented: bool,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ObjectQuantifierKind {
    Some,
    All,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ObjectQuantifierDefinition {
    kind: ObjectQuantifierKind,
    role_id: u32,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct NormalizedObjectQuantifierTerm {
    kind: ObjectQuantifierKind,
    role_id: u32,
    property_key: Vec<u8>,
    key: Vec<u8>,
    filler: Box<NormalizedClassTerm>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ObjectCardinalityKind {
    Minimum,
    Maximum,
}

enum CardinalityNormalization {
    Quantifier {
        kind: ObjectQuantifierKind,
        complement_filler: bool,
    },
    Cardinality {
        kind: ObjectCardinalityKind,
        cardinality: u32,
        cardinality_bytes: Vec<u8>,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ObjectCardinalityDefinition {
    kind: ObjectCardinalityKind,
    cardinality: u32,
    role_id: u32,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct NormalizedObjectCardinalityTerm {
    kind: ObjectCardinalityKind,
    cardinality: u32,
    cardinality_bytes: Vec<u8>,
    role_id: u32,
    property_key: Vec<u8>,
    key: Vec<u8>,
    filler: Box<NormalizedClassTerm>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum DataQuantifierKind {
    Some,
    All,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct DataRangeDefinition {
    base_key: Vec<u8>,
    negative: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct DataQuantifierDefinition {
    kind: DataQuantifierKind,
    role_id: u32,
    filler: DataRangeDefinition,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct NormalizedDataQuantifierTerm {
    kind: DataQuantifierKind,
    role_id: u32,
    property_key: Vec<u8>,
    key: Vec<u8>,
    filler: NormalizedDataTerm,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum DataCardinalityKind {
    Minimum,
    Maximum,
}

enum DataCardinalityNormalization {
    Quantifier {
        kind: DataQuantifierKind,
        complement_filler: bool,
    },
    Cardinality {
        kind: DataCardinalityKind,
        cardinality: u32,
        cardinality_bytes: Vec<u8>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct DataCardinalityDefinition {
    kind: DataCardinalityKind,
    cardinality: u32,
    role_id: u32,
    filler: DataRangeDefinition,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct NormalizedDataCardinalityTerm {
    kind: DataCardinalityKind,
    cardinality: u32,
    cardinality_bytes: Vec<u8>,
    role_id: u32,
    property_key: Vec<u8>,
    key: Vec<u8>,
    filler: NormalizedDataTerm,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum NormalizedClassTerm {
    Atomic(NormalizedAtomicClassTerm),
    Nominal(NormalizedNominalClassTerm),
    Boolean(NormalizedClassBooleanTerm),
    ObjectSelf(NormalizedObjectSelfTerm),
    ObjectQuantifier(NormalizedObjectQuantifierTerm),
    ObjectCardinality(NormalizedObjectCardinalityTerm),
    DataQuantifier(NormalizedDataQuantifierTerm),
    DataCardinality(NormalizedDataCardinalityTerm),
}

impl NormalizedClassTerm {
    fn key(&self) -> &[u8] {
        match self {
            Self::Atomic(term) => &term.key,
            Self::Nominal(term) => &term.key,
            Self::Boolean(term) => &term.key,
            Self::ObjectSelf(term) => &term.key,
            Self::ObjectQuantifier(term) => &term.key,
            Self::ObjectCardinality(term) => &term.key,
            Self::DataQuantifier(term) => &term.key,
            Self::DataCardinality(term) => &term.key,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct DataBooleanDefinition {
    expressions: Vec<NodeId>,
    expression_key: Vec<u8>,
    expression_symbols: Vec<DataRangeSymbolSeed>,
    intersection: bool,
    operands: Vec<DataBooleanOperand>,
    polarity: DefinitionPolarity,
    generated_key: Vec<u8>,
    generated_display: String,
    provenance: Vec<[u8; 32]>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct FlatDataBooleanExpression {
    expression_key: Vec<u8>,
    expression_symbols: Vec<DataRangeSymbolSeed>,
    intersection: bool,
    operands: Vec<AtomicDataRangeSelection>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct DataRangeSymbolSeed {
    key: Vec<u8>,
    display: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum DataBooleanOperand {
    Atomic(AtomicDataRangeSelection),
    Generated { key: Vec<u8> },
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct NormalizedAtomicDataTerm {
    selection: Option<AtomicDataRangeSelection>,
    base_key: Vec<u8>,
    negative: bool,
    key: Vec<u8>,
    symbols: Vec<DataRangeSymbolSeed>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct NormalizedDataBooleanTerm {
    intersection: bool,
    key: Vec<u8>,
    operands: Vec<NormalizedDataTerm>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum NormalizedDataTerm {
    Atomic(NormalizedAtomicDataTerm),
    Boolean(NormalizedDataBooleanTerm),
}

impl NormalizedDataTerm {
    fn key(&self) -> &[u8] {
        match self {
            Self::Atomic(term) => &term.key,
            Self::Boolean(term) => &term.key,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct DatatypeBooleanDefinition {
    root: NodeId,
    expression: NodeId,
    expression_symbols: Vec<DataRangeSymbolSeed>,
    intersection: bool,
    operands: Vec<AtomicDataRangeSelection>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct AtomicDataRangeSelection {
    base: NodeId,
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
    SelfAntecedent,
    SelfConsequent,
    ExistentialAntecedent,
    ExistentialConsequent,
    UniversalAntecedent,
    UniversalConsequent,
    MinimumAntecedent,
    MinimumConsequent,
    MaximumAntecedent,
    MaximumConsequent,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct RawObjectConstraint {
    kind: ObjectConstraintKind,
    role_id: u32,
    class: ClassLiteral,
    filler: Option<ClassLiteral>,
    cardinality: Option<u32>,
    provenance: [u8; 32],
    generated: bool,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct NormalizedObjectConstraint {
    kind: ObjectConstraintKind,
    role_id: u32,
    class: ClassLiteral,
    filler: Option<ClassLiteral>,
    cardinality: Option<u32>,
    provenance: Vec<[u8; 32]>,
    generated: bool,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum DataConstraintKind {
    ExistentialAntecedent,
    ExistentialConsequent,
    UniversalAntecedent,
    UniversalConsequent,
    MinimumAntecedent,
    MinimumConsequent,
    MaximumAntecedent,
    MaximumConsequent,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct RawDataConstraint {
    kind: DataConstraintKind,
    role_id: u32,
    class: ClassLiteral,
    filler: DataRangeLiteral,
    cardinality: Option<u32>,
    provenance: [u8; 32],
    generated: bool,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct NormalizedDataConstraint {
    kind: DataConstraintKind,
    role_id: u32,
    class: ClassLiteral,
    filler: DataRangeLiteral,
    cardinality: Option<u32>,
    provenance: Vec<[u8; 32]>,
    generated: bool,
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

#[derive(Clone, Debug, Eq, PartialEq)]
struct RawDataBooleanClause {
    body: Vec<DataRangeLiteral>,
    head: Vec<DataRangeLiteral>,
    provenance: [u8; 32],
    generated: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct NormalizedDataBooleanClause {
    body: Vec<DataRangeLiteral>,
    head: Vec<DataRangeLiteral>,
    provenance: Vec<[u8; 32]>,
    generated: bool,
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
    compile_named_class_phase_impl(model, symbols, None, None, &[], None, limits)
}

/// Compile the named fragment with an inner-to-outer anonymous-scope map
/// chain applied only to exact source provenance.
pub fn compile_named_class_phase_scoped<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    scope_maps: &[AnonymousScopeMap],
    limits: NamedClassPhaseLimits,
) -> EncodedResult<NamedClassPhase> {
    compile_named_class_phase_impl(model, symbols, None, None, scope_maps, None, limits)
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
    compile_named_class_phase_impl(
        model,
        symbols,
        Some(object_roles),
        None,
        scope_maps,
        None,
        limits,
    )
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
        None,
        limits,
    )
}

/// Compile the named fragment with the ontology logical fingerprint as the
/// deterministic namespace for scalar-compatible generated definitions.
#[allow(clippy::too_many_arguments)]
pub fn compile_named_class_phase_with_role_domains_scoped_and_namespace<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    object_roles: &ObjectRolePhase,
    data_roles: &DataRolePhase,
    scope_maps: &[AnonymousScopeMap],
    definition_namespace: [u8; 32],
    limits: NamedClassPhaseLimits,
) -> EncodedResult<NamedClassPhase> {
    compile_named_class_phase_impl(
        model,
        symbols,
        Some(object_roles),
        Some(data_roles),
        scope_maps,
        Some(definition_namespace),
        limits,
    )
}

fn compile_named_class_phase_impl<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    object_roles: Option<&ObjectRolePhase>,
    data_roles: Option<&DataRolePhase>,
    scope_maps: &[AnonymousScopeMap],
    definition_namespace: Option<[u8; 32]>,
    limits: NamedClassPhaseLimits,
) -> EncodedResult<NamedClassPhase> {
    let mut budget = PhaseBudget::new(limits);
    canonical::validate_scope_maps(scope_maps, &mut budget)?;
    let (definitions, class_data_definitions) = class_boolean_definitions(
        model,
        symbols,
        object_roles,
        data_roles,
        scope_maps,
        definition_namespace,
        &mut budget,
    )?;
    let data_definitions = data_boolean_definitions(
        model,
        symbols,
        data_roles,
        scope_maps,
        definition_namespace,
        class_data_definitions,
        &mut budget,
    )?;
    let datatype_boolean_definitions =
        datatype_boolean_definitions(model, symbols, scope_maps, &mut budget)?;
    let (entity_domain, source_entity_map) =
        phase_entity_domain(symbols, &definitions, &data_definitions, &mut budget)?;
    let declared_class_ids = declared_class_ids(symbols, &mut budget)?;
    let (class_domain, class_signature) = class_signature(
        model,
        symbols,
        &declared_class_ids,
        object_roles.is_some(),
        data_roles.is_some(),
        scope_maps,
        &definitions,
        &mut budget,
    )?;
    let data_range_domain = named_data_range_domain(
        model,
        symbols,
        data_roles.is_some(),
        scope_maps,
        &definitions,
        &data_definitions,
        &datatype_boolean_definitions,
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
        &definitions,
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
    let mut raw_boolean_clauses = Vec::<RawBooleanClause>::new();
    let mut raw_disjoints = Vec::<RawDisjoint>::new();
    let mut raw_object_constraints = Vec::<RawObjectConstraint>::new();
    let mut raw_data_constraints = Vec::<RawDataConstraint>::new();
    let mut raw_object_characteristics = Vec::<RawObjectCharacteristic>::new();
    let mut raw_data_domains = Vec::<RawDataDomain>::new();
    let mut raw_data_ranges = Vec::<RawDataRange>::new();
    let mut raw_data_boolean_clauses = Vec::<RawDataBooleanClause>::new();
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
    emit_class_boolean_definitions(
        model,
        symbols,
        &class_domain,
        &data_range_domain,
        &class_signature,
        &definitions,
        scope_maps,
        &mut raw_edges,
        &mut raw_boolean_clauses,
        &mut raw_object_constraints,
        &mut raw_data_constraints,
        &mut budget,
    )?;
    emit_data_boolean_definitions(
        model,
        symbols,
        &data_range_domain,
        &data_definitions,
        scope_maps,
        &mut raw_data_boolean_clauses,
        &mut budget,
    )?;
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
                    &definitions,
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
                    &definitions,
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
                    &definitions,
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
            RootHandler::DisjointUnion => {
                match named_disjoint_union(
                    model,
                    symbols,
                    &class_domain,
                    &class_signature,
                    &definitions,
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
                                EncodedValidationError::resource("disjoint-union allocation failed")
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
                    &definitions,
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
                    &definitions,
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
                    &data_definitions,
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
                if let Some(definition) =
                    datatype_boolean_definition_for_root(&datatype_boolean_definitions, root.node)
                {
                    let provenance = emit_datatype_boolean_definition(
                        model,
                        symbols,
                        &data_range_domain,
                        definition,
                        scope_maps,
                        &mut raw_data_boolean_clauses,
                        &mut budget,
                    )?;
                    retain_compiled_root(
                        &mut compiled_root_digests,
                        &mut compiled_roots,
                        provenance,
                        &mut budget,
                    )?;
                    continue;
                }
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
                    &definitions,
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
                    &definitions,
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
    let boolean_clauses = normalize_boolean_clauses(raw_boolean_clauses, &mut budget)?;
    let disjoints = normalize_disjoints(raw_disjoints, &mut budget)?;
    let object_constraints = normalize_object_constraints(raw_object_constraints, &mut budget)?;
    let data_constraints = normalize_data_constraints(raw_data_constraints, &mut budget)?;
    let object_characteristics =
        normalize_object_characteristics(raw_object_characteristics, &mut budget)?;
    let data_domains = normalize_data_domains(raw_data_domains, &mut budget)?;
    let data_ranges = normalize_data_ranges(raw_data_ranges, &mut budget)?;
    let data_boolean_clauses =
        normalize_data_boolean_clauses(raw_data_boolean_clauses, &mut budget)?;
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
        &boolean_clauses,
        &disjoints,
        &object_constraints,
        &data_constraints,
        &object_characteristics,
        &data_domains,
        &data_ranges,
        &data_boolean_clauses,
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
        at_least_object_predicates,
        at_least_data_predicates,
        annotated_equality_predicates,
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
        &boolean_clauses,
        &disjoints,
        &object_constraints,
        &data_constraints,
        &object_characteristics,
        &data_domains,
        &data_ranges,
        &data_boolean_clauses,
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
        &boolean_clauses,
        &disjoints,
        &object_constraints,
        &data_constraints,
        &object_characteristics,
        &data_domains,
        &data_ranges,
        &data_boolean_clauses,
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
        &at_least_object_predicates,
        &at_least_data_predicates,
        &annotated_equality_predicates,
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
            &boolean_clauses,
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
    let class_signature = published_class_signature(
        &class_signature,
        &class_domain,
        &entity_domain,
        &source_entity_map,
        &definitions,
        &mut budget,
    )?;
    let individual_signature =
        published_individual_signature(&individual_signature, &source_entity_map, &mut budget)?;
    Ok(NamedClassPhase {
        entity_domain,
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
        normalized_boolean_clauses: boolean_clauses,
        normalized_disjoints: disjoints,
        normalized_object_constraints: object_constraints,
        normalized_data_constraints: data_constraints,
        normalized_object_characteristics: object_characteristics,
        normalized_data_domains: data_domains,
        normalized_data_ranges: data_ranges,
        normalized_data_boolean_clauses: data_boolean_clauses,
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

fn class_boolean_definitions<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    object_roles: Option<&ObjectRolePhase>,
    data_roles: Option<&DataRolePhase>,
    scope_maps: &[AnonymousScopeMap],
    namespace: Option<[u8; 32]>,
    budget: &mut PhaseBudget,
) -> EncodedResult<(Vec<ClassBooleanDefinition>, Vec<DataBooleanDefinition>)> {
    let Some(namespace) = namespace else {
        return Ok((Vec::new(), Vec::new()));
    };
    let mut definitions = Vec::<ClassBooleanDefinition>::new();
    for root in &symbols.roots {
        budget.claim_work(1)?;
        match root.handler {
            RootHandler::SubClassOf => retain_subclass_boolean_definitions(
                model,
                symbols,
                object_roles,
                data_roles,
                root.node,
                namespace,
                scope_maps,
                &mut definitions,
                budget,
            )?,
            RootHandler::EquivalentClasses => retain_equivalent_boolean_definitions(
                model,
                symbols,
                object_roles,
                data_roles,
                root.node,
                namespace,
                scope_maps,
                &mut definitions,
                budget,
            )?,
            RootHandler::ClassAssertion => retain_class_assertion_boolean_definition(
                model,
                symbols,
                object_roles,
                data_roles,
                root.node,
                namespace,
                scope_maps,
                &mut definitions,
                budget,
            )?,
            RootHandler::ObjectPropertyDomain | RootHandler::ObjectPropertyRange => {
                if let Some(roles) = object_roles {
                    retain_class_constraint_boolean_definition(
                        model,
                        symbols,
                        Some(roles),
                        data_roles,
                        root.handler,
                        root.node,
                        namespace,
                        scope_maps,
                        &mut definitions,
                        budget,
                    )?;
                }
            }
            RootHandler::DataPropertyDomain => {
                if let Some(roles) = data_roles {
                    retain_class_constraint_boolean_definition(
                        model,
                        symbols,
                        object_roles,
                        Some(roles),
                        root.handler,
                        root.node,
                        namespace,
                        scope_maps,
                        &mut definitions,
                        budget,
                    )?;
                }
            }
            RootHandler::HasKey => retain_key_boolean_definition(
                model,
                symbols,
                object_roles,
                data_roles,
                root.node,
                namespace,
                scope_maps,
                &mut definitions,
                budget,
            )?,
            RootHandler::DisjointClasses => retain_disjoint_boolean_definitions(
                model,
                symbols,
                object_roles,
                data_roles,
                root.node,
                namespace,
                scope_maps,
                &mut definitions,
                budget,
            )?,
            RootHandler::DisjointUnion => retain_disjoint_union_boolean_definition(
                model,
                symbols,
                object_roles,
                data_roles,
                root.node,
                namespace,
                scope_maps,
                &mut definitions,
                budget,
            )?,
            _ => {}
        }
    }
    budget.claim_work(sort_work(definitions.len()))?;
    definitions.sort_by(|left, right| {
        left.expression_key
            .cmp(&right.expression_key)
            .then_with(|| left.polarity.cmp(&right.polarity))
    });
    for definition in &mut definitions {
        budget.claim_work(sort_work(definition.expressions.len()))?;
        definition.expressions.sort_unstable();
        definition.expressions.dedup();
        budget.claim_work(sort_work(definition.roots.len()))?;
        definition.roots.sort_unstable();
        definition.roots.dedup();
        budget.claim_work(sort_work(definition.provenance.len()))?;
        definition.provenance.sort_unstable();
        definition.provenance.dedup();
    }
    let mut data_definitions = Vec::new();
    for definition in &mut definitions {
        let dependencies = std::mem::take(&mut definition.data_dependencies);
        for dependency in dependencies {
            retain_data_boolean_definition_provenances(
                &mut data_definitions,
                dependency,
                &definition.provenance,
                budget,
            )?;
        }
    }
    Ok((definitions, data_definitions))
}

fn data_boolean_definitions<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    data_roles: Option<&DataRolePhase>,
    scope_maps: &[AnonymousScopeMap],
    namespace: Option<[u8; 32]>,
    mut definitions: Vec<DataBooleanDefinition>,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<DataBooleanDefinition>> {
    let (Some(namespace), Some(data_roles)) = (namespace, data_roles) else {
        return Ok(definitions);
    };
    for root in &symbols.roots {
        budget.claim_work(1)?;
        if root.handler != RootHandler::DataPropertyRange {
            continue;
        }
        let node = model.node(root.node)?;
        if node.tag() != DATA_PROPERTY_RANGE_TAG || node.field_count() != 3 {
            return Err(EncodedValidationError::invariant(
                "data-property range root no longer has schema-1 shape",
            ));
        }
        let property = node_field(model, node, 0, "data-property range role")?;
        let _role_id = named_data_role_id(model, symbols, data_roles, property, budget)?;
        let expression = node_field(model, node, 1, "data-property range value")?;
        if atomic_data_range_selection(model, symbols, expression, budget)?.is_some() {
            continue;
        }
        let definition = data_boolean_definition_candidate(
            model,
            symbols,
            expression,
            DefinitionPolarity::Positive,
            namespace,
            scope_maps,
            budget,
        )?;
        let provenance = source_axiom_digest(model, root.node, scope_maps, budget)?;
        if let Some(definition) = definition {
            retain_data_boolean_definition_provenances(
                &mut definitions,
                definition,
                std::slice::from_ref(&provenance),
                budget,
            )?;
            continue;
        }
        let _retained = retain_recursive_data_boolean_definitions(
            model,
            symbols,
            expression,
            namespace,
            provenance,
            scope_maps,
            &mut definitions,
            budget,
        )?;
    }
    budget.claim_work(sort_work(definitions.len()))?;
    definitions.sort_by(|left, right| {
        left.expression_key
            .cmp(&right.expression_key)
            .then_with(|| left.polarity.cmp(&right.polarity))
    });
    for definition in &mut definitions {
        budget.claim_work(sort_work(definition.expressions.len()))?;
        definition.expressions.sort_unstable();
        definition.expressions.dedup();
        budget.claim_work(sort_work(definition.provenance.len()))?;
        definition.provenance.sort_unstable();
        definition.provenance.dedup();
    }
    Ok(definitions)
}

#[allow(clippy::too_many_arguments)]
fn data_boolean_definition_candidate<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    expression: NodeId,
    polarity: DefinitionPolarity,
    namespace: [u8; 32],
    scope_maps: &[AnonymousScopeMap],
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<DataBooleanDefinition>> {
    let Some(candidate) =
        flat_data_boolean_expression(model, symbols, expression, scope_maps, budget)?
    else {
        return Ok(None);
    };
    let (generated_key, generated_display) =
        generated_data_symbol(namespace, &candidate.expression_key, polarity, budget)?;
    budget.claim_owned(
        candidate
            .operands
            .len()
            .checked_mul(size_of::<DataBooleanOperand>())
            .ok_or_else(|| {
                EncodedValidationError::resource(
                    "generated data Boolean operand allocation overflowed",
                )
            })?,
    )?;
    let mut operands = Vec::new();
    operands
        .try_reserve_exact(candidate.operands.len())
        .map_err(|_| {
            EncodedValidationError::resource("generated data Boolean operand allocation failed")
        })?;
    operands.extend(
        candidate
            .operands
            .into_iter()
            .map(DataBooleanOperand::Atomic),
    );
    budget.claim_owned(size_of::<NodeId>())?;
    Ok(Some(DataBooleanDefinition {
        expressions: vec![expression],
        expression_key: candidate.expression_key,
        expression_symbols: candidate.expression_symbols,
        intersection: candidate.intersection,
        operands,
        polarity,
        generated_key,
        generated_display,
        provenance: Vec::new(),
    }))
}

fn flat_data_boolean_expression<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    expression: NodeId,
    scope_maps: &[AnonymousScopeMap],
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<FlatDataBooleanExpression>> {
    let mut base = expression;
    let mut complemented = false;
    let mut depth = 0_usize;
    loop {
        let node = model.node(base)?;
        if node.tag() != DATA_COMPLEMENT_OF_TAG {
            break;
        }
        if node.field_count() != 1 {
            return Err(EncodedValidationError::invariant(
                "data complement no longer has schema-1 shape",
            ));
        }
        depth = depth.checked_add(1).ok_or_else(|| {
            EncodedValidationError::resource("data Boolean complement depth overflowed")
        })?;
        PhaseBudget::count(depth, budget.limits.max_canonical_depth, "data-range depth")?;
        budget.claim_work(1)?;
        base = node_field(model, node, 0, "data-complement operand")?;
        complemented = !complemented;
    }
    let node = model.node(base)?;
    if !matches!(node.tag(), DATA_INTERSECTION_OF_TAG | DATA_UNION_OF_TAG) {
        return Ok(None);
    }
    if node.field_count() != 1 {
        return Err(EncodedValidationError::invariant(
            "data Boolean expression no longer has schema-1 shape",
        ));
    }
    let component = required_component(model.field(node.fields().start)?, "data Boolean operands")?;
    let ComponentValue::Collection(operands) = model.resolve(component)? else {
        return Err(EncodedValidationError::invariant(
            "data Boolean operands did not resolve to a collection",
        ));
    };
    if operands.len() < 2 {
        return Err(EncodedValidationError::invariant(
            "data Boolean expression has fewer than two operands",
        ));
    }
    let intersection = (node.tag() == DATA_INTERSECTION_OF_TAG) != complemented;
    let mut selections = Vec::<AtomicDataRangeSelection>::new();
    let operand_depth = child_expression_depth(depth, "data-range depth overflowed")?;
    PhaseBudget::count(
        operand_depth,
        budget.limits.max_canonical_depth,
        "data-range depth",
    )?;
    for item_index in operands.items() {
        budget.claim_work(1)?;
        let item = required_component(model.item(item_index)?, "data Boolean operand")?;
        let ComponentValue::Node(operand) = model.resolve(item)? else {
            return Err(EncodedValidationError::invariant(
                "data Boolean operand did not resolve to a node",
            ));
        };
        if !collect_flat_data_boolean_operand(
            model,
            symbols,
            operand,
            complemented,
            intersection,
            operand_depth,
            &mut selections,
            budget,
        )? {
            return Ok(None);
        }
    }
    if selections.len() < 2 {
        return Ok(None);
    }
    for (index, selection) in selections.iter().copied().enumerate() {
        if atomic_data_range_selection_is_top(model, symbols, selection)?
            || atomic_data_range_selection_is_bottom(model, symbols, selection)?
            || selections
                .iter()
                .take(index)
                .copied()
                .any(|known| atomic_data_range_selections_match(known, selection))
        {
            return Ok(None);
        }
    }
    let mut keyed = Vec::<(Vec<u8>, AtomicDataRangeSelection)>::new();
    budget.claim_owned(
        selections
            .len()
            .checked_mul(size_of::<(Vec<u8>, AtomicDataRangeSelection)>())
            .ok_or_else(|| {
                EncodedValidationError::resource("data Boolean key allocation overflowed")
            })?,
    )?;
    keyed
        .try_reserve_exact(selections.len())
        .map_err(|_| EncodedValidationError::resource("data Boolean key allocation failed"))?;
    let mut expression_symbols = Vec::<DataRangeSymbolSeed>::new();
    for mut selection in selections {
        selection.expression = selection.base;
        let base_key = canonical::canonical_node_key(model, selection.base, scope_maps, budget)?;
        if model.node(selection.base)?.tag() != ENTITY_TAG {
            let seed =
                data_range_symbol_seed(&base_key, model.node(selection.base)?.tag(), budget)?;
            push_data_range_symbol_seed(&mut expression_symbols, seed, budget)?;
        }
        let literal_key = if selection.negative {
            let key = synthetic_data_complement_key(&base_key, budget)?;
            let seed = data_range_symbol_seed(&key, DATA_COMPLEMENT_OF_TAG, budget)?;
            push_data_range_symbol_seed(&mut expression_symbols, seed, budget)?;
            key
        } else {
            base_key
        };
        keyed.push((literal_key, selection));
    }
    budget.claim_work(sort_work(keyed.len()))?;
    keyed.sort_by(|left, right| left.0.cmp(&right.0));
    if keyed.windows(2).any(|pair| pair[0].0 == pair[1].0) {
        return Ok(None);
    }
    let expression_tag = if intersection {
        DATA_INTERSECTION_OF_TAG
    } else {
        DATA_UNION_OF_TAG
    };
    let expression_key = synthetic_boolean_key(
        expression_tag,
        keyed.iter().map(|(key, _)| key.as_slice()),
        keyed.len(),
        budget,
    )?;
    let seed = data_range_symbol_seed(&expression_key, expression_tag, budget)?;
    push_data_range_symbol_seed(&mut expression_symbols, seed, budget)?;
    budget.claim_work(sort_work(expression_symbols.len()))?;
    expression_symbols.sort_by(|left, right| left.key.cmp(&right.key));
    expression_symbols.dedup_by(|left, right| left.key == right.key);
    budget.claim_owned(
        keyed
            .len()
            .checked_mul(size_of::<AtomicDataRangeSelection>())
            .ok_or_else(|| {
                EncodedValidationError::resource(
                    "normalized data Boolean operand allocation overflowed",
                )
            })?,
    )?;
    let mut operands = Vec::new();
    operands.try_reserve_exact(keyed.len()).map_err(|_| {
        EncodedValidationError::resource("normalized data Boolean operand allocation failed")
    })?;
    operands.extend(keyed.into_iter().map(|(_, selection)| selection));
    Ok(Some(FlatDataBooleanExpression {
        expression_key,
        expression_symbols,
        intersection,
        operands,
    }))
}

#[allow(clippy::too_many_arguments)]
fn collect_flat_data_boolean_operand<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    identifier: NodeId,
    inherited_complement: bool,
    intersection: bool,
    initial_depth: usize,
    selections: &mut Vec<AtomicDataRangeSelection>,
    budget: &mut PhaseBudget,
) -> EncodedResult<bool> {
    let mut base = identifier;
    let mut complemented = inherited_complement;
    let mut depth = initial_depth;
    loop {
        let node = model.node(base)?;
        if node.tag() != DATA_COMPLEMENT_OF_TAG {
            break;
        }
        if node.field_count() != 1 {
            return Err(EncodedValidationError::invariant(
                "nested data complement no longer has schema-1 shape",
            ));
        }
        depth = child_expression_depth(depth, "data-range depth overflowed")?;
        PhaseBudget::count(depth, budget.limits.max_canonical_depth, "data-range depth")?;
        budget.claim_work(1)?;
        base = node_field(model, node, 0, "nested data-complement operand")?;
        complemented = !complemented;
    }
    let node = model.node(base)?;
    if matches!(node.tag(), DATA_INTERSECTION_OF_TAG | DATA_UNION_OF_TAG) {
        if node.field_count() != 1 {
            return Err(EncodedValidationError::invariant(
                "nested data Boolean expression no longer has schema-1 shape",
            ));
        }
        let nested_intersection = (node.tag() == DATA_INTERSECTION_OF_TAG) != complemented;
        if nested_intersection != intersection {
            return Ok(false);
        }
        let component = required_component(
            model.field(node.fields().start)?,
            "nested data Boolean operands",
        )?;
        let ComponentValue::Collection(operands) = model.resolve(component)? else {
            return Err(EncodedValidationError::invariant(
                "nested data Boolean operands did not resolve to a collection",
            ));
        };
        if operands.len() < 2 {
            return Err(EncodedValidationError::invariant(
                "nested data Boolean expression has fewer than two operands",
            ));
        }
        let operand_depth = child_expression_depth(depth, "data-range depth overflowed")?;
        PhaseBudget::count(
            operand_depth,
            budget.limits.max_canonical_depth,
            "data-range depth",
        )?;
        for item_index in operands.items() {
            budget.claim_work(1)?;
            let item = required_component(model.item(item_index)?, "nested data Boolean operand")?;
            let ComponentValue::Node(operand) = model.resolve(item)? else {
                return Err(EncodedValidationError::invariant(
                    "nested data Boolean operand did not resolve to a node",
                ));
            };
            if !collect_flat_data_boolean_operand(
                model,
                symbols,
                operand,
                complemented,
                intersection,
                operand_depth,
                selections,
                budget,
            )? {
                return Ok(false);
            }
        }
        return Ok(true);
    }
    let Some(mut selection) =
        positive_atomic_data_range_selection(model, symbols, base, depth, budget)?
    else {
        return Ok(false);
    };
    selection.negative = complemented;
    selection.expression = selection.base;
    let following = selections.len().checked_add(1).ok_or_else(|| {
        EncodedValidationError::resource("flattened data Boolean operand count overflowed")
    })?;
    PhaseBudget::count(
        following,
        budget.limits.max_data_range_symbols,
        "flattened data Boolean operand count",
    )?;
    budget.claim_owned(size_of::<AtomicDataRangeSelection>())?;
    selections.try_reserve(1).map_err(|_| {
        EncodedValidationError::resource("flattened data Boolean operand allocation failed")
    })?;
    selections.push(selection);
    Ok(true)
}

#[allow(clippy::too_many_arguments)]
fn normalized_data_term<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    identifier: NodeId,
    inherited_complement: bool,
    initial_depth: usize,
    scope_maps: &[AnonymousScopeMap],
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<NormalizedDataTerm>> {
    let mut base = identifier;
    let mut complemented = inherited_complement;
    let mut depth = initial_depth;
    loop {
        let node = model.node(base)?;
        if node.tag() != DATA_COMPLEMENT_OF_TAG {
            break;
        }
        if node.field_count() != 1 {
            return Err(EncodedValidationError::invariant(
                "recursive data complement no longer has schema-1 shape",
            ));
        }
        depth = child_expression_depth(depth, "data-range depth overflowed")?;
        PhaseBudget::count(depth, budget.limits.max_canonical_depth, "data-range depth")?;
        budget.claim_work(1)?;
        base = node_field(model, node, 0, "recursive data-complement operand")?;
        complemented = !complemented;
    }
    let node = model.node(base)?;
    if !matches!(node.tag(), DATA_INTERSECTION_OF_TAG | DATA_UNION_OF_TAG) {
        let Some(mut selection) =
            positive_atomic_data_range_selection(model, symbols, base, depth, budget)?
        else {
            return Ok(None);
        };
        selection.negative = complemented;
        selection.expression = selection.base;
        let base_key = canonical::canonical_node_key(model, selection.base, scope_maps, budget)?;
        let mut expression_symbols = Vec::new();
        if model.node(selection.base)?.tag() != ENTITY_TAG {
            let seed =
                data_range_symbol_seed(&base_key, model.node(selection.base)?.tag(), budget)?;
            push_data_range_symbol_seed(&mut expression_symbols, seed, budget)?;
        }
        let key = if selection.negative {
            let key = synthetic_data_complement_key(&base_key, budget)?;
            let seed = data_range_symbol_seed(&key, DATA_COMPLEMENT_OF_TAG, budget)?;
            push_data_range_symbol_seed(&mut expression_symbols, seed, budget)?;
            key
        } else {
            budget.claim_owned(base_key.len())?;
            base_key.clone()
        };
        budget.claim_owned(size_of::<NormalizedAtomicDataTerm>())?;
        return Ok(Some(NormalizedDataTerm::Atomic(NormalizedAtomicDataTerm {
            selection: Some(selection),
            base_key,
            negative: selection.negative,
            key,
            symbols: expression_symbols,
        })));
    }
    if node.field_count() != 1 {
        return Err(EncodedValidationError::invariant(
            "recursive data Boolean expression no longer has schema-1 shape",
        ));
    }
    let component = required_component(
        model.field(node.fields().start)?,
        "recursive data Boolean operands",
    )?;
    let ComponentValue::Collection(source_operands) = model.resolve(component)? else {
        return Err(EncodedValidationError::invariant(
            "recursive data Boolean operands did not resolve to a collection",
        ));
    };
    if source_operands.len() < 2 {
        return Err(EncodedValidationError::invariant(
            "recursive data Boolean expression has fewer than two operands",
        ));
    }
    let intersection = (node.tag() == DATA_INTERSECTION_OF_TAG) != complemented;
    let operand_depth = child_expression_depth(depth, "data-range depth overflowed")?;
    PhaseBudget::count(
        operand_depth,
        budget.limits.max_canonical_depth,
        "data-range depth",
    )?;
    let mut operands = Vec::<NormalizedDataTerm>::new();
    for item_index in source_operands.items() {
        budget.claim_work(1)?;
        let item = required_component(model.item(item_index)?, "recursive data Boolean operand")?;
        let ComponentValue::Node(operand) = model.resolve(item)? else {
            return Err(EncodedValidationError::invariant(
                "recursive data Boolean operand did not resolve to a node",
            ));
        };
        let Some(term) = normalized_data_term(
            model,
            symbols,
            operand,
            complemented,
            operand_depth,
            scope_maps,
            budget,
        )?
        else {
            return Ok(None);
        };
        match term {
            NormalizedDataTerm::Boolean(term) if term.intersection == intersection => {
                for nested in term.operands {
                    push_normalized_data_term(&mut operands, nested, budget)?;
                }
            }
            term => push_normalized_data_term(&mut operands, term, budget)?,
        }
    }
    if operands.len() < 2 {
        return Ok(None);
    }
    for term in &operands {
        if let NormalizedDataTerm::Atomic(term) = term {
            let selection = term.selection.ok_or_else(|| {
                EncodedValidationError::invariant(
                    "recursive data Boolean contains a synthetic atomic operand",
                )
            })?;
            if atomic_data_range_selection_is_top(model, symbols, selection)?
                || atomic_data_range_selection_is_bottom(model, symbols, selection)?
            {
                return Ok(None);
            }
        }
    }
    budget.claim_work(sort_work(operands.len()))?;
    operands.sort_by(|left, right| left.key().cmp(right.key()));
    if operands
        .windows(2)
        .any(|pair| pair[0].key() == pair[1].key())
    {
        return Ok(None);
    }
    let expression_tag = if intersection {
        DATA_INTERSECTION_OF_TAG
    } else {
        DATA_UNION_OF_TAG
    };
    let key = synthetic_boolean_key(
        expression_tag,
        operands.iter().map(NormalizedDataTerm::key),
        operands.len(),
        budget,
    )?;
    budget.claim_owned(size_of::<NormalizedDataBooleanTerm>())?;
    Ok(Some(NormalizedDataTerm::Boolean(
        NormalizedDataBooleanTerm {
            intersection,
            key,
            operands,
        },
    )))
}

fn push_normalized_data_term(
    target: &mut Vec<NormalizedDataTerm>,
    term: NormalizedDataTerm,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    let following = target
        .len()
        .checked_add(1)
        .ok_or_else(|| EncodedValidationError::resource("normalized data term count overflowed"))?;
    PhaseBudget::count(
        following,
        budget.limits.max_data_range_symbols,
        "normalized data term count",
    )?;
    budget.claim_owned(size_of::<NormalizedDataTerm>())?;
    target
        .try_reserve(1)
        .map_err(|_| EncodedValidationError::resource("normalized data term allocation failed"))?;
    target.push(term);
    Ok(())
}

fn synthetic_data_complement_key(
    operand_key: &[u8],
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<u8>> {
    let mut key = Vec::new();
    push_generated_varint(&mut key, u64::from(DATA_COMPLEMENT_OF_TAG), budget)?;
    push_generated_byte(&mut key, 1, budget)?;
    push_generated_frame(&mut key, operand_key, budget)?;
    Ok(key)
}

fn data_range_symbol_seed(
    key: &[u8],
    tag: u16,
    budget: &mut PhaseBudget,
) -> EncodedResult<DataRangeSymbolSeed> {
    budget.claim_work(key.len())?;
    let digest = crate::model::hex(&Sha256::digest(key));
    let prefix = data_range_expression_prefix(tag)?;
    let display_len = prefix
        .len()
        .checked_add(digest.len())
        .ok_or_else(|| EncodedValidationError::resource("data-range display length overflowed"))?;
    budget.claim_owned(
        size_of::<DataRangeSymbolSeed>()
            .checked_add(key.len())
            .and_then(|value| value.checked_add(display_len))
            .ok_or_else(|| {
                EncodedValidationError::resource("data-range seed ownership overflowed")
            })?,
    )?;
    let mut stored_key = Vec::new();
    stored_key
        .try_reserve_exact(key.len())
        .map_err(|_| EncodedValidationError::resource("data-range seed key allocation failed"))?;
    stored_key.extend_from_slice(key);
    let mut display = String::new();
    display.try_reserve_exact(display_len).map_err(|_| {
        EncodedValidationError::resource("data-range seed display allocation failed")
    })?;
    display.push_str(prefix);
    display.push_str(&digest);
    Ok(DataRangeSymbolSeed {
        key: stored_key,
        display,
    })
}

fn push_data_range_symbol_seed(
    target: &mut Vec<DataRangeSymbolSeed>,
    seed: DataRangeSymbolSeed,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    target.try_reserve(1).map_err(|_| {
        EncodedValidationError::resource("data-range seed collection allocation failed")
    })?;
    budget.claim_work(1)?;
    target.push(seed);
    Ok(())
}

fn push_seeded_data_range_symbol(
    target: &mut Vec<DecodedSymbolValue>,
    seed: &DataRangeSymbolSeed,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    let following = target.len().checked_add(1).ok_or_else(|| {
        EncodedValidationError::resource("seeded data-range symbol count overflowed")
    })?;
    PhaseBudget::count(
        following,
        budget.limits.max_data_range_symbols,
        "data-range symbol count",
    )?;
    budget.claim_owned(
        size_of::<DecodedSymbolValue>()
            .checked_add(seed.key.len())
            .and_then(|value| value.checked_add(seed.display.len()))
            .ok_or_else(|| {
                EncodedValidationError::resource("seeded data-range ownership overflowed")
            })?,
    )?;
    target.try_reserve(1).map_err(|_| {
        EncodedValidationError::resource("seeded data-range symbol allocation failed")
    })?;
    target.push(DecodedSymbolValue {
        identifier: 0,
        key: seed.key.clone(),
        display: seed.display.clone(),
        generated: false,
        query_local: false,
    });
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn retain_recursive_data_boolean_definitions<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    expression: NodeId,
    namespace: [u8; 32],
    provenance: [u8; 32],
    scope_maps: &[AnonymousScopeMap],
    definitions: &mut Vec<DataBooleanDefinition>,
    budget: &mut PhaseBudget,
) -> EncodedResult<bool> {
    let Some(term) =
        normalized_data_term(model, symbols, expression, false, 0, scope_maps, budget)?
    else {
        return Ok(false);
    };
    let NormalizedDataTerm::Boolean(term) = term else {
        return Ok(false);
    };
    let mut pending = Vec::new();
    let _generated_key = atomize_normalized_data_boolean(
        term,
        Some(expression),
        namespace,
        DefinitionPolarity::Positive,
        &mut pending,
        budget,
    )?;
    for definition in pending {
        retain_data_boolean_definition_provenances(
            definitions,
            definition,
            std::slice::from_ref(&provenance),
            budget,
        )?;
    }
    Ok(true)
}

fn atomize_normalized_data_boolean(
    term: NormalizedDataBooleanTerm,
    source_expression: Option<NodeId>,
    namespace: [u8; 32],
    polarity: DefinitionPolarity,
    definitions: &mut Vec<DataBooleanDefinition>,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<u8>> {
    let expression_tag = if term.intersection {
        DATA_INTERSECTION_OF_TAG
    } else {
        DATA_UNION_OF_TAG
    };
    let mut expression_symbols = Vec::<DataRangeSymbolSeed>::new();
    let source_seed = data_range_symbol_seed(&term.key, expression_tag, budget)?;
    push_data_range_symbol_seed(&mut expression_symbols, source_seed, budget)?;
    let mut keyed = Vec::<(Vec<u8>, DataBooleanOperand)>::new();
    budget.claim_owned(
        term.operands
            .len()
            .checked_mul(size_of::<(Vec<u8>, DataBooleanOperand)>())
            .ok_or_else(|| {
                EncodedValidationError::resource(
                    "recursive data definition operand allocation overflowed",
                )
            })?,
    )?;
    keyed.try_reserve_exact(term.operands.len()).map_err(|_| {
        EncodedValidationError::resource("recursive data definition operand allocation failed")
    })?;
    for operand in term.operands {
        match operand {
            NormalizedDataTerm::Atomic(operand) => {
                for seed in operand.symbols {
                    push_data_range_symbol_seed(&mut expression_symbols, seed, budget)?;
                }
                let selection = operand.selection.ok_or_else(|| {
                    EncodedValidationError::invariant(
                        "recursive data definition contains a synthetic atomic operand",
                    )
                })?;
                keyed.push((operand.key, DataBooleanOperand::Atomic(selection)));
            }
            NormalizedDataTerm::Boolean(operand) => {
                let generated_key = atomize_normalized_data_boolean(
                    operand,
                    None,
                    namespace,
                    polarity,
                    definitions,
                    budget,
                )?;
                budget.claim_owned(generated_key.len())?;
                keyed.push((
                    generated_key.clone(),
                    DataBooleanOperand::Generated { key: generated_key },
                ));
            }
        }
    }
    budget.claim_work(sort_work(keyed.len()))?;
    keyed.sort_by(|left, right| left.0.cmp(&right.0));
    if keyed.len() < 2 || keyed.windows(2).any(|pair| pair[0].0 == pair[1].0) {
        return Err(EncodedValidationError::invariant(
            "recursive data definition lost distinct operands",
        ));
    }
    let normalized_expression_key = synthetic_boolean_key(
        expression_tag,
        keyed.iter().map(|(key, _)| key.as_slice()),
        keyed.len(),
        budget,
    )?;
    let normalized_seed =
        data_range_symbol_seed(&normalized_expression_key, expression_tag, budget)?;
    push_data_range_symbol_seed(&mut expression_symbols, normalized_seed, budget)?;
    budget.claim_work(sort_work(expression_symbols.len()))?;
    expression_symbols.sort_by(|left, right| left.key.cmp(&right.key));
    expression_symbols.dedup_by(|left, right| left.key == right.key);
    budget.claim_owned(
        keyed
            .len()
            .checked_mul(size_of::<DataBooleanOperand>())
            .ok_or_else(|| {
                EncodedValidationError::resource(
                    "recursive generated operand allocation overflowed",
                )
            })?,
    )?;
    let mut operands = Vec::new();
    operands.try_reserve_exact(keyed.len()).map_err(|_| {
        EncodedValidationError::resource("recursive generated operand allocation failed")
    })?;
    operands.extend(keyed.into_iter().map(|(_, operand)| operand));
    let (generated_key, generated_display) =
        generated_data_symbol(namespace, &term.key, polarity, budget)?;
    budget.claim_owned(generated_key.len())?;
    let returned_key = generated_key.clone();
    let mut expressions = Vec::new();
    if let Some(expression) = source_expression {
        budget.claim_owned(size_of::<NodeId>())?;
        expressions.try_reserve_exact(1).map_err(|_| {
            EncodedValidationError::resource(
                "recursive data definition expression allocation failed",
            )
        })?;
        expressions.push(expression);
    }
    budget.claim_owned(size_of::<DataBooleanDefinition>())?;
    definitions.try_reserve(1).map_err(|_| {
        EncodedValidationError::resource("recursive data definition allocation failed")
    })?;
    definitions.push(DataBooleanDefinition {
        expressions,
        expression_key: term.key,
        expression_symbols,
        intersection: term.intersection,
        operands,
        polarity,
        generated_key,
        generated_display,
        provenance: Vec::new(),
    });
    Ok(returned_key)
}

fn datatype_boolean_definitions<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    scope_maps: &[AnonymousScopeMap],
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<DatatypeBooleanDefinition>> {
    let mut definitions = Vec::<DatatypeBooleanDefinition>::new();
    for root in &symbols.roots {
        budget.claim_work(1)?;
        if root.handler != RootHandler::DatatypeDefinition {
            continue;
        }
        let node = model.node(root.node)?;
        if node.tag() != DATATYPE_DEFINITION_TAG || node.field_count() != 3 {
            return Err(EncodedValidationError::invariant(
                "datatype-definition root no longer has schema-1 shape",
            ));
        }
        let expression = node_field(model, node, 1, "datatype defining range")?;
        if atomic_data_range_selection(model, symbols, expression, budget)?.is_some() {
            continue;
        }
        let Some(candidate) =
            flat_data_boolean_expression(model, symbols, expression, scope_maps, budget)?
        else {
            continue;
        };
        let following = definitions.len().checked_add(1).ok_or_else(|| {
            EncodedValidationError::resource("datatype Boolean definition count overflowed")
        })?;
        PhaseBudget::count(
            following,
            budget.limits.max_compiled_roots,
            "datatype Boolean definition count",
        )?;
        budget.claim_owned(size_of::<DatatypeBooleanDefinition>())?;
        definitions.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("datatype Boolean definition allocation failed")
        })?;
        definitions.push(DatatypeBooleanDefinition {
            root: root.node,
            expression,
            expression_symbols: candidate.expression_symbols,
            intersection: candidate.intersection,
            operands: candidate.operands,
        });
    }
    budget.claim_work(sort_work(definitions.len()))?;
    definitions.sort_by_key(|definition| definition.root);
    if definitions
        .windows(2)
        .any(|pair| pair[0].root == pair[1].root)
    {
        return Err(EncodedValidationError::invariant(
            "datatype Boolean definition root is duplicated",
        ));
    }
    Ok(definitions)
}

fn retain_data_boolean_definition_provenances(
    definitions: &mut Vec<DataBooleanDefinition>,
    mut definition: DataBooleanDefinition,
    provenances: &[[u8; 32]],
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    if !definition.provenance.is_empty() || provenances.is_empty() {
        return Err(EncodedValidationError::invariant(
            "generated data definition has invalid pending provenance",
        ));
    }
    if let Some(known) = definitions.iter_mut().find(|known| {
        known.expression_key == definition.expression_key && known.polarity == definition.polarity
    }) {
        if known.intersection != definition.intersection
            || known.operands != definition.operands
            || known.expression_symbols != definition.expression_symbols
            || known.generated_key != definition.generated_key
            || known.generated_display != definition.generated_display
        {
            return Err(EncodedValidationError::invariant(
                "equivalent generated data definitions disagree",
            ));
        }
        budget.claim_owned(
            definition
                .expressions
                .len()
                .checked_mul(size_of::<NodeId>())
                .and_then(|value| {
                    provenances
                        .len()
                        .checked_mul(size_of::<[u8; 32]>())
                        .and_then(|provenance_bytes| value.checked_add(provenance_bytes))
                })
                .ok_or_else(|| {
                    EncodedValidationError::resource(
                        "generated data definition ownership overflowed",
                    )
                })?,
        )?;
        known
            .expressions
            .try_reserve(definition.expressions.len())
            .map_err(|_| {
                EncodedValidationError::resource(
                    "generated data definition expression allocation failed",
                )
            })?;
        known.expressions.append(&mut definition.expressions);
        known
            .provenance
            .try_reserve(provenances.len())
            .map_err(|_| {
                EncodedValidationError::resource(
                    "generated data definition provenance allocation failed",
                )
            })?;
        known.provenance.extend_from_slice(provenances);
        return Ok(());
    }
    let following = definitions.len().checked_add(1).ok_or_else(|| {
        EncodedValidationError::resource("generated data definition count overflowed")
    })?;
    PhaseBudget::count(
        following,
        budget.limits.max_data_range_symbols,
        "generated data definition count",
    )?;
    budget.claim_owned(
        provenances
            .len()
            .checked_mul(size_of::<[u8; 32]>())
            .and_then(|value| value.checked_add(size_of::<DataBooleanDefinition>()))
            .ok_or_else(|| {
                EncodedValidationError::resource(
                    "generated data definition provenance ownership overflowed",
                )
            })?,
    )?;
    definition
        .provenance
        .try_reserve(provenances.len())
        .map_err(|_| {
            EncodedValidationError::resource(
                "generated data definition provenance allocation failed",
            )
        })?;
    definition.provenance.extend_from_slice(provenances);
    definitions.try_reserve(1).map_err(|_| {
        EncodedValidationError::resource("generated data definition allocation failed")
    })?;
    definitions.push(definition);
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn retain_subclass_boolean_definitions<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    object_roles: Option<&ObjectRolePhase>,
    data_roles: Option<&DataRolePhase>,
    root: NodeId,
    namespace: [u8; 32],
    scope_maps: &[AnonymousScopeMap],
    definitions: &mut Vec<ClassBooleanDefinition>,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    let node = model.node(root)?;
    if node.tag() != SUBCLASS_TAG || node.field_count() != 3 {
        return Err(EncodedValidationError::invariant(
            "subclass root no longer has schema-1 shape",
        ));
    }
    let sub_class = node_field(model, node, 0, "subclass antecedent")?;
    let super_class = node_field(model, node, 1, "subclass consequent")?;
    let sub_atomic = atomic_class_selection(model, symbols, sub_class, budget)?.is_some();
    let super_atomic = atomic_class_selection(model, symbols, super_class, budget)?.is_some();
    let sub_definitions = if sub_atomic {
        None
    } else {
        class_boolean_definition_candidates(
            model,
            symbols,
            object_roles,
            data_roles,
            sub_class,
            DefinitionPolarity::Negative,
            namespace,
            scope_maps,
            budget,
        )?
    };
    let super_definitions = if super_atomic {
        None
    } else {
        class_boolean_definition_candidates(
            model,
            symbols,
            object_roles,
            data_roles,
            super_class,
            DefinitionPolarity::Positive,
            namespace,
            scope_maps,
            budget,
        )?
    };
    if (!sub_atomic && sub_definitions.is_none()) || (!super_atomic && super_definitions.is_none())
    {
        return Ok(());
    }
    let provenance = source_axiom_digest(model, root, scope_maps, budget)?;
    if let Some(candidates) = sub_definitions {
        for definition in candidates {
            retain_class_boolean_definition(definitions, definition, provenance, budget)?;
        }
    }
    if let Some(candidates) = super_definitions {
        for definition in candidates {
            retain_class_boolean_definition(definitions, definition, provenance, budget)?;
        }
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn retain_class_assertion_boolean_definition<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    object_roles: Option<&ObjectRolePhase>,
    data_roles: Option<&DataRolePhase>,
    root: NodeId,
    namespace: [u8; 32],
    scope_maps: &[AnonymousScopeMap],
    definitions: &mut Vec<ClassBooleanDefinition>,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    let node = model.node(root)?;
    if node.tag() != CLASS_ASSERTION_TAG || node.field_count() != 3 {
        return Err(EncodedValidationError::invariant(
            "class-assertion root no longer has schema-1 shape",
        ));
    }
    let expression = node_field(model, node, 0, "class-assertion class expression")?;
    if atomic_class_selection(model, symbols, expression, budget)?.is_some() {
        return Ok(());
    }
    let Some(candidates) = class_boolean_definition_candidates(
        model,
        symbols,
        object_roles,
        data_roles,
        expression,
        DefinitionPolarity::Positive,
        namespace,
        scope_maps,
        budget,
    )?
    else {
        return Ok(());
    };
    let individual = node_field(model, node, 1, "class-assertion individual")?;
    if !supported_class_assertion_individual(model, symbols, individual)? {
        return Ok(());
    }
    let provenance = source_axiom_digest(model, root, scope_maps, budget)?;
    for definition in candidates {
        retain_class_boolean_definition(definitions, definition, provenance, budget)?;
    }
    Ok(())
}

fn supported_class_assertion_individual<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    identifier: NodeId,
) -> EncodedResult<bool> {
    match model.node(identifier)?.tag() {
        ANONYMOUS_INDIVIDUAL_TAG => Ok(true),
        ENTITY_TAG => {
            let entity_id = symbols.entity_symbol_for_node(identifier).ok_or_else(|| {
                EncodedValidationError::invariant(
                    "class-assertion individual is absent from the reachable entity mapping",
                )
            })?;
            Ok(class_entity_display(symbols, entity_id)?.starts_with(NAMED_INDIVIDUAL_PREFIX))
        }
        _ => Ok(false),
    }
}

#[allow(clippy::too_many_arguments)]
fn retain_class_constraint_boolean_definition<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    object_roles: Option<&ObjectRolePhase>,
    data_roles: Option<&DataRolePhase>,
    handler: RootHandler,
    root: NodeId,
    namespace: [u8; 32],
    scope_maps: &[AnonymousScopeMap],
    definitions: &mut Vec<ClassBooleanDefinition>,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    let (tag, name) = match handler {
        RootHandler::ObjectPropertyDomain => (OBJECT_PROPERTY_DOMAIN_TAG, "object-property domain"),
        RootHandler::ObjectPropertyRange => (OBJECT_PROPERTY_RANGE_TAG, "object-property range"),
        RootHandler::DataPropertyDomain => (DATA_PROPERTY_DOMAIN_TAG, "data-property domain"),
        _ => {
            return Err(EncodedValidationError::invariant(
                "class constraint definition received a different root handler",
            ));
        }
    };
    let node = model.node(root)?;
    if node.tag() != tag || node.field_count() != 3 {
        return Err(EncodedValidationError::invariant(format!(
            "{name} root no longer has schema-1 shape"
        )));
    }
    let property = node_field(model, node, 0, "class constraint property")?;
    match handler {
        RootHandler::ObjectPropertyDomain | RootHandler::ObjectPropertyRange => {
            let roles = object_roles.ok_or_else(|| {
                EncodedValidationError::invariant("object class constraint lost its role domain")
            })?;
            let _role_id = named_object_role_id(model, symbols, roles, property, budget)?;
        }
        RootHandler::DataPropertyDomain => {
            let roles = data_roles.ok_or_else(|| {
                EncodedValidationError::invariant("data class constraint lost its role domain")
            })?;
            let _role_id = named_data_role_id(model, symbols, roles, property, budget)?;
        }
        _ => {
            return Err(EncodedValidationError::invariant(
                "class constraint definition handler changed during validation",
            ));
        }
    }
    let expression = node_field(model, node, 1, "class constraint expression")?;
    if atomic_class_selection(model, symbols, expression, budget)?.is_some() {
        return Ok(());
    }
    let Some(candidates) = class_boolean_definition_candidates(
        model,
        symbols,
        object_roles,
        data_roles,
        expression,
        DefinitionPolarity::Positive,
        namespace,
        scope_maps,
        budget,
    )?
    else {
        return Ok(());
    };
    let provenance = source_axiom_digest(model, root, scope_maps, budget)?;
    for definition in candidates {
        retain_class_boolean_definition(definitions, definition, provenance, budget)?;
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn retain_key_boolean_definition<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    object_roles: Option<&ObjectRolePhase>,
    data_roles: Option<&DataRolePhase>,
    root: NodeId,
    namespace: [u8; 32],
    scope_maps: &[AnonymousScopeMap],
    definitions: &mut Vec<ClassBooleanDefinition>,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    let node = model.node(root)?;
    if node.tag() != HAS_KEY_TAG || node.field_count() != 4 {
        return Err(EncodedValidationError::invariant(
            "has-key root no longer has schema-1 shape",
        ));
    }
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
    if (!object_properties.is_empty() && object_roles.is_none())
        || (!data_properties.is_empty() && data_roles.is_none())
    {
        return Ok(());
    }
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
        let _role_id = named_object_role_id(model, symbols, roles, identifier, budget)?;
    }
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
        let _role_id = named_data_role_id(model, symbols, roles, identifier, budget)?;
    }
    let expression = node_field(model, node, 0, "has-key class expression")?;
    if atomic_class_selection(model, symbols, expression, budget)?.is_some() {
        return Ok(());
    }
    let Some(candidates) = class_boolean_definition_candidates(
        model,
        symbols,
        object_roles,
        data_roles,
        expression,
        DefinitionPolarity::Negative,
        namespace,
        scope_maps,
        budget,
    )?
    else {
        return Ok(());
    };
    let provenance = source_axiom_digest(model, root, scope_maps, budget)?;
    for definition in candidates {
        retain_class_boolean_definition(definitions, definition, provenance, budget)?;
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn retain_disjoint_boolean_definitions<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    object_roles: Option<&ObjectRolePhase>,
    data_roles: Option<&DataRolePhase>,
    root: NodeId,
    namespace: [u8; 32],
    scope_maps: &[AnonymousScopeMap],
    definitions: &mut Vec<ClassBooleanDefinition>,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
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
    let mut pending = Vec::<ClassBooleanDefinition>::new();
    for item_index in expressions.items() {
        budget.claim_work(1)?;
        let item = required_component(model.item(item_index)?, "disjoint-classes member")?;
        let ComponentValue::Node(identifier) = model.resolve(item)? else {
            return Err(EncodedValidationError::invariant(
                "disjoint-classes member did not resolve to a node",
            ));
        };
        if atomic_class_selection(model, symbols, identifier, budget)?.is_some() {
            continue;
        }
        let Some(candidates) = class_boolean_definition_candidates(
            model,
            symbols,
            object_roles,
            data_roles,
            identifier,
            DefinitionPolarity::Negative,
            namespace,
            scope_maps,
            budget,
        )?
        else {
            return Ok(());
        };
        budget.claim_owned(
            candidates
                .len()
                .checked_mul(size_of::<ClassBooleanDefinition>())
                .ok_or_else(|| {
                    EncodedValidationError::resource(
                        "disjoint Boolean definition allocation overflowed",
                    )
                })?,
        )?;
        pending.try_reserve(candidates.len()).map_err(|_| {
            EncodedValidationError::resource("disjoint Boolean definition allocation failed")
        })?;
        pending.extend(candidates);
    }
    if pending.is_empty() {
        return Ok(());
    }
    let provenance = source_axiom_digest(model, root, scope_maps, budget)?;
    for definition in pending {
        retain_class_boolean_definition(definitions, definition, provenance, budget)?;
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn retain_disjoint_union_boolean_definition<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    object_roles: Option<&ObjectRolePhase>,
    data_roles: Option<&DataRolePhase>,
    root: NodeId,
    namespace: [u8; 32],
    scope_maps: &[AnonymousScopeMap],
    definitions: &mut Vec<ClassBooleanDefinition>,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    let node = model.node(root)?;
    if node.tag() != DISJOINT_UNION_TAG || node.field_count() != 3 {
        return Err(EncodedValidationError::invariant(
            "disjoint-union root no longer has schema-1 shape",
        ));
    }
    let defined = node_field(model, node, 0, "disjoint-union defined class")?;
    if atomic_class_selection(model, symbols, defined, budget)?.is_none() {
        return Ok(());
    }
    let expressions_component = required_component(
        model.field(node.fields().start + 1)?,
        "disjoint-union expressions",
    )?;
    let ComponentValue::Collection(expressions) = model.resolve(expressions_component)? else {
        return Err(EncodedValidationError::invariant(
            "disjoint-union expressions did not resolve to a collection",
        ));
    };
    if expressions.len() < 2 {
        return Err(EncodedValidationError::invariant(
            "disjoint-union root has fewer than two members",
        ));
    }
    if reducible_class_boolean_operands(model, symbols, expressions, false, 0, budget)?.is_some() {
        return Ok(());
    }
    let member_depth = child_expression_depth(0, "class-expression depth overflowed")?;
    PhaseBudget::count(
        member_depth,
        budget.limits.max_canonical_depth,
        "class-expression depth",
    )?;
    let mut normalized_members = Vec::new();
    let mut pending = Vec::new();
    for item_index in expressions.items() {
        budget.claim_work(1)?;
        let item = required_component(model.item(item_index)?, "disjoint-union member")?;
        let ComponentValue::Node(identifier) = model.resolve(item)? else {
            return Err(EncodedValidationError::invariant(
                "disjoint-union member did not resolve to a node",
            ));
        };
        let Some(term) = normalized_class_term(
            model,
            symbols,
            object_roles,
            data_roles,
            identifier,
            false,
            member_depth,
            scope_maps,
            budget,
        )?
        else {
            return Ok(());
        };
        if !matches!(
            term,
            NormalizedClassTerm::Atomic(_) | NormalizedClassTerm::Nominal(_)
        ) {
            let _generated_key = atomize_normalized_class_term(
                term.clone(),
                Some(identifier),
                DefinitionPolarity::Negative,
                namespace,
                &mut pending,
                budget,
            )?;
        }
        push_normalized_class_term(&mut normalized_members, term, budget)?;
    }
    let Some(union) = normalized_class_boolean_term(symbols, normalized_members, false, budget)?
    else {
        return Ok(());
    };
    let NormalizedClassTerm::Boolean(union) = union else {
        return Ok(());
    };
    let previous_count = pending.len();
    let outer_key = atomize_normalized_class_boolean(
        union,
        None,
        DefinitionPolarity::Positive,
        namespace,
        &mut pending,
        budget,
    )?;
    let new_count = pending.len();
    let outer = pending.last_mut().ok_or_else(|| {
        EncodedValidationError::invariant("recursive disjoint-union definition disappeared")
    })?;
    if new_count <= previous_count
        || outer.generated_key != outer_key
        || outer.polarity != DefinitionPolarity::Positive
    {
        return Err(EncodedValidationError::invariant(
            "recursive disjoint-union outer definition changed",
        ));
    }
    budget.claim_owned(size_of::<NodeId>())?;
    outer.roots.try_reserve(1).map_err(|_| {
        EncodedValidationError::resource("recursive disjoint-union root allocation failed")
    })?;
    outer.roots.push(root);
    let provenance = source_axiom_digest(model, root, scope_maps, budget)?;
    for definition in pending {
        retain_class_boolean_definition(definitions, definition, provenance, budget)?;
    }
    Ok(())
}

fn synthetic_boolean_key<'a>(
    tag: u16,
    keys: impl Iterator<Item = &'a [u8]>,
    count: usize,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<u8>> {
    let mut key = Vec::new();
    push_generated_varint(&mut key, u64::from(tag), budget)?;
    push_generated_byte(&mut key, 6, budget)?;
    push_generated_varint(
        &mut key,
        u64::try_from(count).map_err(|_| {
            EncodedValidationError::resource("synthetic class Boolean arity exceeds u64")
        })?,
        budget,
    )?;
    for member in keys {
        budget.claim_work(1)?;
        push_generated_frame(&mut key, member, budget)?;
    }
    Ok(key)
}

#[allow(clippy::too_many_arguments)]
fn retain_equivalent_boolean_definitions<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    object_roles: Option<&ObjectRolePhase>,
    data_roles: Option<&DataRolePhase>,
    root: NodeId,
    namespace: [u8; 32],
    scope_maps: &[AnonymousScopeMap],
    definitions: &mut Vec<ClassBooleanDefinition>,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
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
    let mut pending = Vec::<ClassBooleanDefinition>::new();
    for item_index in expressions.items() {
        budget.claim_work(1)?;
        let item = required_component(model.item(item_index)?, "equivalent-classes member")?;
        let ComponentValue::Node(identifier) = model.resolve(item)? else {
            return Err(EncodedValidationError::invariant(
                "equivalent-classes member did not resolve to a node",
            ));
        };
        if atomic_class_selection(model, symbols, identifier, budget)?.is_some() {
            continue;
        }
        let Some(negative) = class_boolean_definition_candidates(
            model,
            symbols,
            object_roles,
            data_roles,
            identifier,
            DefinitionPolarity::Negative,
            namespace,
            scope_maps,
            budget,
        )?
        else {
            return Ok(());
        };
        let Some(positive) = class_boolean_definition_candidates(
            model,
            symbols,
            object_roles,
            data_roles,
            identifier,
            DefinitionPolarity::Positive,
            namespace,
            scope_maps,
            budget,
        )?
        else {
            return Ok(());
        };
        let count = negative.len().checked_add(positive.len()).ok_or_else(|| {
            EncodedValidationError::resource("equivalent Boolean definition count overflowed")
        })?;
        budget.claim_owned(
            count
                .checked_mul(size_of::<ClassBooleanDefinition>())
                .ok_or_else(|| {
                    EncodedValidationError::resource(
                        "equivalent Boolean definition allocation overflowed",
                    )
                })?,
        )?;
        pending.try_reserve(count).map_err(|_| {
            EncodedValidationError::resource("equivalent Boolean definition allocation failed")
        })?;
        pending.extend(negative);
        pending.extend(positive);
    }
    if pending.is_empty() {
        return Ok(());
    }
    let provenance = source_axiom_digest(model, root, scope_maps, budget)?;
    for definition in pending {
        retain_class_boolean_definition(definitions, definition, provenance, budget)?;
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn class_boolean_definition_candidates<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    object_roles: Option<&ObjectRolePhase>,
    data_roles: Option<&DataRolePhase>,
    expression: NodeId,
    polarity: DefinitionPolarity,
    namespace: [u8; 32],
    scope_maps: &[AnonymousScopeMap],
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<Vec<ClassBooleanDefinition>>> {
    let Some(term) = normalized_class_term(
        model,
        symbols,
        object_roles,
        data_roles,
        expression,
        false,
        0,
        scope_maps,
        budget,
    )?
    else {
        return Ok(None);
    };
    if matches!(
        term,
        NormalizedClassTerm::Atomic(_) | NormalizedClassTerm::Nominal(_)
    ) {
        return Ok(None);
    }
    let mut definitions = Vec::new();
    let _generated_key = atomize_normalized_class_term(
        term,
        Some(expression),
        polarity,
        namespace,
        &mut definitions,
        budget,
    )?;
    Ok(Some(definitions))
}

#[allow(clippy::too_many_arguments)]
fn normalized_class_term<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    object_roles: Option<&ObjectRolePhase>,
    data_roles: Option<&DataRolePhase>,
    identifier: NodeId,
    inherited_complement: bool,
    initial_depth: usize,
    scope_maps: &[AnonymousScopeMap],
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<NormalizedClassTerm>> {
    let mut base = identifier;
    let mut complemented = inherited_complement;
    let mut depth = initial_depth;
    loop {
        let node = model.node(base)?;
        if node.tag() != OBJECT_COMPLEMENT_OF_TAG {
            break;
        }
        if node.field_count() != 1 {
            return Err(EncodedValidationError::invariant(
                "recursive class complement no longer has schema-1 shape",
            ));
        }
        depth = child_expression_depth(depth, "class-expression depth overflowed")?;
        PhaseBudget::count(
            depth,
            budget.limits.max_canonical_depth,
            "class-expression depth",
        )?;
        budget.claim_work(1)?;
        base = node_field(model, node, 0, "recursive class-complement operand")?;
        complemented = !complemented;
    }

    let node = model.node(base)?;
    if !matches!(node.tag(), OBJECT_INTERSECTION_OF_TAG | OBJECT_UNION_OF_TAG) {
        let selection = positive_atomic_class_selection(model, symbols, base, depth, budget)?;
        if selection.is_none() && node.tag() == OBJECT_HAS_SELF_TAG {
            if node.field_count() != 1 {
                return Err(EncodedValidationError::invariant(
                    "object-self definition no longer has schema-1 shape",
                ));
            }
            let Some(object_roles) = object_roles else {
                return Ok(None);
            };
            let property = node_field(model, node, 0, "object-self definition role")?;
            let role_id = named_object_role_id(model, symbols, object_roles, property, budget)?;
            let base_key = canonical::canonical_node_key(model, base, scope_maps, budget)?;
            let key = if complemented {
                synthetic_class_complement_key(&base_key, budget)?
            } else {
                budget.claim_owned(base_key.len())?;
                base_key.clone()
            };
            budget.claim_owned(size_of::<NormalizedObjectSelfTerm>())?;
            return Ok(Some(NormalizedClassTerm::ObjectSelf(
                NormalizedObjectSelfTerm {
                    role_id,
                    base_key,
                    key,
                    complemented,
                },
            )));
        }
        if selection.is_none() && node.tag() == OBJECT_HAS_VALUE_TAG {
            if node.field_count() != 2 {
                return Err(EncodedValidationError::invariant(
                    "object-has-value definition no longer has schema-1 shape",
                ));
            }
            let Some(object_roles) = object_roles else {
                return Ok(None);
            };
            if !reduction_inputs_are_retained(model, symbols, base, depth, budget)? {
                return Ok(None);
            }
            let property = node_field(model, node, 0, "object-has-value definition role")?;
            let role_id = named_object_role_id(model, symbols, object_roles, property, budget)?;
            let individual = node_field(model, node, 1, "object-has-value definition individual")?;
            if model.node(individual)?.tag() != ENTITY_TAG {
                return Ok(None);
            }
            let individual_entity_id =
                symbols.entity_symbol_for_node(individual).ok_or_else(|| {
                    EncodedValidationError::invariant(
                        "object-has-value individual is absent from the reachable entity mapping",
                    )
                })?;
            let individual_entity = symbols
                .entity_domain
                .values
                .get(usize::try_from(individual_entity_id).map_err(|_| {
                    EncodedValidationError::invariant(
                        "object-has-value individual entity ID exceeds usize",
                    )
                })?)
                .ok_or_else(|| {
                    EncodedValidationError::invariant(
                        "object-has-value individual entity ID is dangling",
                    )
                })?;
            if !individual_entity
                .display
                .starts_with(NAMED_INDIVIDUAL_PREFIX)
            {
                return Ok(None);
            }
            let base_key = synthetic_boolean_key(
                OBJECT_ONE_OF_TAG,
                std::iter::once(individual_entity.key.as_slice()),
                1,
                budget,
            )?;
            let mut symbols_seed = Vec::new();
            let nominal_seed = class_expression_symbol_seed(&base_key, OBJECT_ONE_OF_TAG, budget)?;
            push_class_expression_symbol_seed(&mut symbols_seed, nominal_seed, budget)?;
            let key = if complemented {
                let key = synthetic_class_complement_key(&base_key, budget)?;
                let complement_seed =
                    class_expression_symbol_seed(&key, OBJECT_COMPLEMENT_OF_TAG, budget)?;
                push_class_expression_symbol_seed(&mut symbols_seed, complement_seed, budget)?;
                key
            } else {
                budget.claim_owned(base_key.len())?;
                base_key.clone()
            };
            let mut individual_entity_ids = Vec::new();
            budget.claim_owned(size_of::<u32>())?;
            individual_entity_ids.try_reserve_exact(1).map_err(|_| {
                EncodedValidationError::resource(
                    "object-has-value nominal individual allocation failed",
                )
            })?;
            individual_entity_ids.push(individual_entity_id);
            budget.claim_owned(
                size_of::<NormalizedNominalClassTerm>() + size_of::<NormalizedClassTerm>(),
            )?;
            let filler = NormalizedClassTerm::Nominal(NormalizedNominalClassTerm {
                base_key,
                key,
                individual_entity_ids,
                negative: complemented,
                symbols: symbols_seed,
            });
            let kind = if complemented {
                ObjectQuantifierKind::All
            } else {
                ObjectQuantifierKind::Some
            };
            let property_key = canonical::canonical_node_key(model, property, scope_maps, budget)?;
            let key = synthetic_object_quantifier_key(kind, &property_key, filler.key(), budget)?;
            budget.claim_owned(
                size_of::<NormalizedObjectQuantifierTerm>() + size_of::<NormalizedClassTerm>(),
            )?;
            return Ok(Some(NormalizedClassTerm::ObjectQuantifier(
                NormalizedObjectQuantifierTerm {
                    kind,
                    role_id,
                    property_key,
                    key,
                    filler: Box::new(filler),
                },
            )));
        }
        if selection.is_none() && node.tag() == DATA_HAS_VALUE_TAG {
            if node.field_count() != 2 {
                return Err(EncodedValidationError::invariant(
                    "data-has-value definition no longer has schema-1 shape",
                ));
            }
            let Some(data_roles) = data_roles else {
                return Ok(None);
            };
            let property = node_field(model, node, 0, "data-has-value definition role")?;
            if !reduction_inputs_are_retained(model, symbols, property, depth, budget)? {
                return Ok(None);
            }
            if data_property_has_iri(model, symbols, property, BOTTOM_DATA_IRI)? {
                return Ok(None);
            }
            let role_id = named_data_role_id(model, symbols, data_roles, property, budget)?;
            let literal = node_field(model, node, 1, "data-has-value definition literal")?;
            if model.node(literal)?.tag() != LITERAL_TAG
                || !symbols.semantic_node_is_reachable(literal)
            {
                return Ok(None);
            }
            let literal_key = canonical::canonical_node_key(model, literal, scope_maps, budget)?;
            let base_key = synthetic_boolean_key(
                DATA_ONE_OF_TAG,
                std::iter::once(literal_key.as_slice()),
                1,
                budget,
            )?;
            let mut data_expression_symbols = Vec::new();
            let singleton_seed = data_range_symbol_seed(&base_key, DATA_ONE_OF_TAG, budget)?;
            push_data_range_symbol_seed(&mut data_expression_symbols, singleton_seed, budget)?;
            let filler_key = if complemented {
                let key = synthetic_data_complement_key(&base_key, budget)?;
                let complement_seed = data_range_symbol_seed(&key, DATA_COMPLEMENT_OF_TAG, budget)?;
                push_data_range_symbol_seed(&mut data_expression_symbols, complement_seed, budget)?;
                key
            } else {
                budget.claim_owned(base_key.len())?;
                base_key.clone()
            };
            let filler = NormalizedAtomicDataTerm {
                selection: None,
                base_key,
                negative: complemented,
                key: filler_key,
                symbols: data_expression_symbols,
            };
            let kind = if complemented {
                DataQuantifierKind::All
            } else {
                DataQuantifierKind::Some
            };
            let property_key = canonical::canonical_node_key(model, property, scope_maps, budget)?;
            let key = synthetic_data_quantifier_key(kind, &property_key, &filler.key, budget)?;
            budget.claim_owned(size_of::<NormalizedDataQuantifierTerm>())?;
            return Ok(Some(NormalizedClassTerm::DataQuantifier(
                NormalizedDataQuantifierTerm {
                    kind,
                    role_id,
                    property_key,
                    key,
                    filler: NormalizedDataTerm::Atomic(filler),
                },
            )));
        }
        if selection.is_none()
            && matches!(
                node.tag(),
                OBJECT_SOME_VALUES_FROM_TAG | OBJECT_ALL_VALUES_FROM_TAG
            )
        {
            if node.field_count() != 2 {
                return Err(EncodedValidationError::invariant(
                    "object-quantifier definition no longer has schema-1 shape",
                ));
            }
            let Some(object_roles) = object_roles else {
                return Ok(None);
            };
            if !reduction_inputs_are_retained(model, symbols, base, depth, budget)? {
                return Ok(None);
            }
            let property = node_field(model, node, 0, "object-quantifier definition role")?;
            let role_id = named_object_role_id(model, symbols, object_roles, property, budget)?;
            let filler = node_field(model, node, 1, "object-quantifier definition filler")?;
            let filler_depth =
                child_expression_depth(depth, "object-quantifier filler depth overflowed")?;
            PhaseBudget::count(
                filler_depth,
                budget.limits.max_canonical_depth,
                "class-expression depth",
            )?;
            let Some(filler) = normalized_class_term(
                model,
                symbols,
                Some(object_roles),
                data_roles,
                filler,
                complemented,
                filler_depth,
                scope_maps,
                budget,
            )?
            else {
                return Ok(None);
            };
            let kind = match (node.tag(), complemented) {
                (OBJECT_SOME_VALUES_FROM_TAG, false) | (OBJECT_ALL_VALUES_FROM_TAG, true) => {
                    ObjectQuantifierKind::Some
                }
                (OBJECT_ALL_VALUES_FROM_TAG, false) | (OBJECT_SOME_VALUES_FROM_TAG, true) => {
                    ObjectQuantifierKind::All
                }
                _ => {
                    return Err(EncodedValidationError::invariant(
                        "object-quantifier definition changed constructor",
                    ));
                }
            };
            let property_key = canonical::canonical_node_key(model, property, scope_maps, budget)?;
            let key = synthetic_object_quantifier_key(kind, &property_key, filler.key(), budget)?;
            budget.claim_owned(
                size_of::<NormalizedObjectQuantifierTerm>() + size_of::<NormalizedClassTerm>(),
            )?;
            return Ok(Some(NormalizedClassTerm::ObjectQuantifier(
                NormalizedObjectQuantifierTerm {
                    kind,
                    role_id,
                    property_key,
                    key,
                    filler: Box::new(filler),
                },
            )));
        }
        if selection.is_none()
            && matches!(
                node.tag(),
                DATA_SOME_VALUES_FROM_TAG | DATA_ALL_VALUES_FROM_TAG
            )
        {
            if node.field_count() != 2 {
                return Err(EncodedValidationError::invariant(
                    "data-quantifier definition no longer has schema-1 shape",
                ));
            }
            let Some(data_roles) = data_roles else {
                return Ok(None);
            };
            let properties_component = required_component(
                model.field(node.fields().start)?,
                "data-quantifier definition properties",
            )?;
            let ComponentValue::Collection(properties) = model.resolve(properties_component)?
            else {
                return Err(EncodedValidationError::invariant(
                    "data-quantifier definition properties did not resolve to a collection",
                ));
            };
            if properties.len() != 1 {
                return Ok(None);
            }
            let property_item = required_component(
                model.item(properties.items().start)?,
                "data-quantifier definition property",
            )?;
            let ComponentValue::Node(property) = model.resolve(property_item)? else {
                return Err(EncodedValidationError::invariant(
                    "data-quantifier definition property did not resolve to a node",
                ));
            };
            if !reduction_inputs_are_retained(model, symbols, property, depth, budget)? {
                return Ok(None);
            }
            let role_id = named_data_role_id(model, symbols, data_roles, property, budget)?;
            let filler = node_field(model, node, 1, "data-quantifier definition filler")?;
            let filler_depth =
                child_expression_depth(depth, "data-quantifier filler depth overflowed")?;
            PhaseBudget::count(
                filler_depth,
                budget.limits.max_canonical_depth,
                "class-expression depth",
            )?;
            let Some(filler) = normalized_data_term(
                model,
                symbols,
                filler,
                complemented,
                filler_depth,
                scope_maps,
                budget,
            )?
            else {
                return Ok(None);
            };
            let kind = match (node.tag(), complemented) {
                (DATA_SOME_VALUES_FROM_TAG, false) | (DATA_ALL_VALUES_FROM_TAG, true) => {
                    DataQuantifierKind::Some
                }
                (DATA_ALL_VALUES_FROM_TAG, false) | (DATA_SOME_VALUES_FROM_TAG, true) => {
                    DataQuantifierKind::All
                }
                _ => {
                    return Err(EncodedValidationError::invariant(
                        "data-quantifier definition changed constructor",
                    ));
                }
            };
            let property_key = canonical::canonical_node_key(model, property, scope_maps, budget)?;
            let key = synthetic_data_quantifier_key(kind, &property_key, filler.key(), budget)?;
            budget.claim_owned(size_of::<NormalizedDataQuantifierTerm>())?;
            return Ok(Some(NormalizedClassTerm::DataQuantifier(
                NormalizedDataQuantifierTerm {
                    kind,
                    role_id,
                    property_key,
                    key,
                    filler,
                },
            )));
        }
        if selection.is_none() && node.tag() == DATA_EXACT_CARDINALITY_TAG {
            if node.field_count() != 3 {
                return Err(EncodedValidationError::invariant(
                    "data-exact-cardinality definition no longer has schema-1 shape",
                ));
            }
            let Some(data_roles) = data_roles else {
                return Ok(None);
            };
            let Some((cardinality, cardinality_bytes)) = integer_field_u32_bytes(
                model,
                node,
                0,
                "data-exact-cardinality definition cardinality",
                budget,
            )?
            else {
                return Ok(None);
            };
            let property = node_field(model, node, 1, "data-exact-cardinality definition role")?;
            if !reduction_inputs_are_retained(model, symbols, property, depth, budget)? {
                return Ok(None);
            }
            let role_id = named_data_role_id(model, symbols, data_roles, property, budget)?;
            let filler = node_field(model, node, 2, "data-exact-cardinality definition filler")?;
            let filler_depth =
                child_expression_depth(depth, "data-exact-cardinality filler depth overflowed")?;
            PhaseBudget::count(
                filler_depth,
                budget.limits.max_canonical_depth,
                "class-expression depth",
            )?;

            if cardinality == 0 {
                let normalization = if complemented {
                    DataCardinalityNormalization::Quantifier {
                        kind: DataQuantifierKind::Some,
                        complement_filler: false,
                    }
                } else {
                    DataCardinalityNormalization::Quantifier {
                        kind: DataQuantifierKind::All,
                        complement_filler: true,
                    }
                };
                return normalized_data_restriction_term(
                    model,
                    symbols,
                    property,
                    role_id,
                    filler,
                    filler_depth,
                    normalization,
                    scope_maps,
                    budget,
                );
            }

            let (intersection, first, second) = if complemented {
                let Some(upper_cardinality) = cardinality.checked_add(1) else {
                    return Ok(None);
                };
                let lower = if cardinality == 1 {
                    DataCardinalityNormalization::Quantifier {
                        kind: DataQuantifierKind::All,
                        complement_filler: true,
                    }
                } else {
                    let lower_cardinality = cardinality.checked_sub(1).ok_or_else(|| {
                        EncodedValidationError::invariant(
                            "complemented data exact cardinality underflowed",
                        )
                    })?;
                    DataCardinalityNormalization::Cardinality {
                        kind: DataCardinalityKind::Maximum,
                        cardinality: lower_cardinality,
                        cardinality_bytes: canonical_u32_integer_bytes(lower_cardinality, budget)?,
                    }
                };
                let upper = DataCardinalityNormalization::Cardinality {
                    kind: DataCardinalityKind::Minimum,
                    cardinality: upper_cardinality,
                    cardinality_bytes: canonical_u32_integer_bytes(upper_cardinality, budget)?,
                };
                (false, lower, upper)
            } else {
                if cardinality == u32::MAX {
                    return Ok(None);
                }
                let minimum = if cardinality == 1 {
                    DataCardinalityNormalization::Quantifier {
                        kind: DataQuantifierKind::Some,
                        complement_filler: false,
                    }
                } else {
                    DataCardinalityNormalization::Cardinality {
                        kind: DataCardinalityKind::Minimum,
                        cardinality,
                        cardinality_bytes: canonical_u32_integer_bytes(cardinality, budget)?,
                    }
                };
                let maximum = DataCardinalityNormalization::Cardinality {
                    kind: DataCardinalityKind::Maximum,
                    cardinality,
                    cardinality_bytes,
                };
                (true, minimum, maximum)
            };
            let Some(first) = normalized_data_restriction_term(
                model,
                symbols,
                property,
                role_id,
                filler,
                filler_depth,
                first,
                scope_maps,
                budget,
            )?
            else {
                return Ok(None);
            };
            let Some(second) = normalized_data_restriction_term(
                model,
                symbols,
                property,
                role_id,
                filler,
                filler_depth,
                second,
                scope_maps,
                budget,
            )?
            else {
                return Ok(None);
            };
            let mut terms = Vec::new();
            push_normalized_class_term(&mut terms, first, budget)?;
            push_normalized_class_term(&mut terms, second, budget)?;
            return normalized_class_boolean_term(symbols, terms, intersection, budget);
        }
        if selection.is_none()
            && matches!(
                node.tag(),
                DATA_MIN_CARDINALITY_TAG | DATA_MAX_CARDINALITY_TAG
            )
        {
            if node.field_count() != 3 {
                return Err(EncodedValidationError::invariant(
                    "data-cardinality definition no longer has schema-1 shape",
                ));
            }
            let Some(data_roles) = data_roles else {
                return Ok(None);
            };
            let Some((cardinality, cardinality_bytes)) = integer_field_u32_bytes(
                model,
                node,
                0,
                "data-cardinality definition cardinality",
                budget,
            )?
            else {
                return Ok(None);
            };
            let normalized = match (node.tag(), complemented, cardinality) {
                (DATA_MIN_CARDINALITY_TAG, false, 0) => return Ok(None),
                (DATA_MIN_CARDINALITY_TAG, false, 1) | (DATA_MAX_CARDINALITY_TAG, true, 0) => {
                    DataCardinalityNormalization::Quantifier {
                        kind: DataQuantifierKind::Some,
                        complement_filler: false,
                    }
                }
                (DATA_MIN_CARDINALITY_TAG, false, _) => DataCardinalityNormalization::Cardinality {
                    kind: DataCardinalityKind::Minimum,
                    cardinality,
                    cardinality_bytes,
                },
                (DATA_MIN_CARDINALITY_TAG, true, 0) => {
                    return Err(EncodedValidationError::invariant(
                        "complemented zero data minimum did not reduce to a builtin",
                    ));
                }
                (DATA_MIN_CARDINALITY_TAG, true, 1) | (DATA_MAX_CARDINALITY_TAG, false, 0) => {
                    DataCardinalityNormalization::Quantifier {
                        kind: DataQuantifierKind::All,
                        complement_filler: true,
                    }
                }
                (DATA_MIN_CARDINALITY_TAG, true, _) => {
                    let normalized_cardinality = cardinality.checked_sub(1).ok_or_else(|| {
                        EncodedValidationError::invariant(
                            "complemented data minimum cardinality underflowed",
                        )
                    })?;
                    DataCardinalityNormalization::Cardinality {
                        kind: DataCardinalityKind::Maximum,
                        cardinality: normalized_cardinality,
                        cardinality_bytes: canonical_u32_integer_bytes(
                            normalized_cardinality,
                            budget,
                        )?,
                    }
                }
                (DATA_MAX_CARDINALITY_TAG, false, u32::MAX) => return Ok(None),
                (DATA_MAX_CARDINALITY_TAG, false, _) => DataCardinalityNormalization::Cardinality {
                    kind: DataCardinalityKind::Maximum,
                    cardinality,
                    cardinality_bytes,
                },
                (DATA_MAX_CARDINALITY_TAG, true, _) => {
                    let Some(normalized_cardinality) = cardinality.checked_add(1) else {
                        return Ok(None);
                    };
                    if normalized_cardinality == 1 {
                        DataCardinalityNormalization::Quantifier {
                            kind: DataQuantifierKind::Some,
                            complement_filler: false,
                        }
                    } else {
                        DataCardinalityNormalization::Cardinality {
                            kind: DataCardinalityKind::Minimum,
                            cardinality: normalized_cardinality,
                            cardinality_bytes: canonical_u32_integer_bytes(
                                normalized_cardinality,
                                budget,
                            )?,
                        }
                    }
                }
                _ => {
                    return Err(EncodedValidationError::invariant(
                        "data-cardinality definition changed constructor",
                    ));
                }
            };
            let property = node_field(model, node, 1, "data-cardinality definition role")?;
            if !reduction_inputs_are_retained(model, symbols, property, depth, budget)? {
                return Ok(None);
            }
            let role_id = named_data_role_id(model, symbols, data_roles, property, budget)?;
            let filler = node_field(model, node, 2, "data-cardinality definition filler")?;
            let filler_depth =
                child_expression_depth(depth, "data-cardinality filler depth overflowed")?;
            PhaseBudget::count(
                filler_depth,
                budget.limits.max_canonical_depth,
                "class-expression depth",
            )?;
            let complement_filler = matches!(
                &normalized,
                DataCardinalityNormalization::Quantifier {
                    complement_filler: true,
                    ..
                }
            );
            let Some(filler) = normalized_data_term(
                model,
                symbols,
                filler,
                complement_filler,
                filler_depth,
                scope_maps,
                budget,
            )?
            else {
                return Ok(None);
            };
            if matches!(
                &normalized,
                DataCardinalityNormalization::Cardinality { .. }
            ) {
                if let NormalizedDataTerm::Atomic(atomic) = &filler {
                    if atomic_data_range_selection_is_bottom(
                        model,
                        symbols,
                        atomic.selection.ok_or_else(|| {
                            EncodedValidationError::invariant(
                                "data-cardinality source filler became synthetic",
                            )
                        })?,
                    )? {
                        return Ok(None);
                    }
                }
            }
            let property_key = canonical::canonical_node_key(model, property, scope_maps, budget)?;
            return match normalized {
                DataCardinalityNormalization::Quantifier { kind, .. } => {
                    let key =
                        synthetic_data_quantifier_key(kind, &property_key, filler.key(), budget)?;
                    budget.claim_owned(size_of::<NormalizedDataQuantifierTerm>())?;
                    Ok(Some(NormalizedClassTerm::DataQuantifier(
                        NormalizedDataQuantifierTerm {
                            kind,
                            role_id,
                            property_key,
                            key,
                            filler,
                        },
                    )))
                }
                DataCardinalityNormalization::Cardinality {
                    kind,
                    cardinality,
                    cardinality_bytes,
                } => {
                    let tag = match kind {
                        DataCardinalityKind::Minimum => DATA_MIN_CARDINALITY_TAG,
                        DataCardinalityKind::Maximum => DATA_MAX_CARDINALITY_TAG,
                    };
                    let key = synthetic_data_cardinality_key(
                        tag,
                        &cardinality_bytes,
                        &property_key,
                        filler.key(),
                        budget,
                    )?;
                    budget.claim_owned(size_of::<NormalizedDataCardinalityTerm>())?;
                    Ok(Some(NormalizedClassTerm::DataCardinality(
                        NormalizedDataCardinalityTerm {
                            kind,
                            cardinality,
                            cardinality_bytes,
                            role_id,
                            property_key,
                            key,
                            filler,
                        },
                    )))
                }
            };
        }
        if selection.is_none() && node.tag() == OBJECT_EXACT_CARDINALITY_TAG {
            if node.field_count() != 3 {
                return Err(EncodedValidationError::invariant(
                    "object-exact-cardinality definition no longer has schema-1 shape",
                ));
            }
            let Some(object_roles) = object_roles else {
                return Ok(None);
            };
            if !reduction_inputs_are_retained(model, symbols, base, depth, budget)? {
                return Ok(None);
            }
            let Some((cardinality, cardinality_bytes)) = integer_field_u32_bytes(
                model,
                node,
                0,
                "object-exact-cardinality definition cardinality",
                budget,
            )?
            else {
                return Ok(None);
            };
            let property = node_field(model, node, 1, "object-exact-cardinality definition role")?;
            let role_id = named_object_role_id(model, symbols, object_roles, property, budget)?;
            let filler = node_field(model, node, 2, "object-exact-cardinality definition filler")?;
            let filler_depth =
                child_expression_depth(depth, "object-exact-cardinality filler depth overflowed")?;
            PhaseBudget::count(
                filler_depth,
                budget.limits.max_canonical_depth,
                "class-expression depth",
            )?;

            if cardinality == 0 {
                let normalization = if complemented {
                    CardinalityNormalization::Quantifier {
                        kind: ObjectQuantifierKind::Some,
                        complement_filler: false,
                    }
                } else {
                    CardinalityNormalization::Quantifier {
                        kind: ObjectQuantifierKind::All,
                        complement_filler: true,
                    }
                };
                return normalized_object_restriction_term(
                    model,
                    symbols,
                    object_roles,
                    data_roles,
                    property,
                    role_id,
                    filler,
                    filler_depth,
                    normalization,
                    scope_maps,
                    budget,
                );
            }

            let (intersection, first, second) = if complemented {
                let Some(upper_cardinality) = cardinality.checked_add(1) else {
                    return Ok(None);
                };
                let lower = if cardinality == 1 {
                    CardinalityNormalization::Quantifier {
                        kind: ObjectQuantifierKind::All,
                        complement_filler: true,
                    }
                } else {
                    let lower_cardinality = cardinality.checked_sub(1).ok_or_else(|| {
                        EncodedValidationError::invariant(
                            "complemented object exact cardinality underflowed",
                        )
                    })?;
                    CardinalityNormalization::Cardinality {
                        kind: ObjectCardinalityKind::Maximum,
                        cardinality: lower_cardinality,
                        cardinality_bytes: canonical_u32_integer_bytes(lower_cardinality, budget)?,
                    }
                };
                let upper = CardinalityNormalization::Cardinality {
                    kind: ObjectCardinalityKind::Minimum,
                    cardinality: upper_cardinality,
                    cardinality_bytes: canonical_u32_integer_bytes(upper_cardinality, budget)?,
                };
                (false, lower, upper)
            } else {
                if cardinality == u32::MAX {
                    return Ok(None);
                }
                let minimum = if cardinality == 1 {
                    CardinalityNormalization::Quantifier {
                        kind: ObjectQuantifierKind::Some,
                        complement_filler: false,
                    }
                } else {
                    CardinalityNormalization::Cardinality {
                        kind: ObjectCardinalityKind::Minimum,
                        cardinality,
                        cardinality_bytes: canonical_u32_integer_bytes(cardinality, budget)?,
                    }
                };
                let maximum = CardinalityNormalization::Cardinality {
                    kind: ObjectCardinalityKind::Maximum,
                    cardinality,
                    cardinality_bytes,
                };
                (true, minimum, maximum)
            };
            let Some(first) = normalized_object_restriction_term(
                model,
                symbols,
                object_roles,
                data_roles,
                property,
                role_id,
                filler,
                filler_depth,
                first,
                scope_maps,
                budget,
            )?
            else {
                return Ok(None);
            };
            let Some(second) = normalized_object_restriction_term(
                model,
                symbols,
                object_roles,
                data_roles,
                property,
                role_id,
                filler,
                filler_depth,
                second,
                scope_maps,
                budget,
            )?
            else {
                return Ok(None);
            };
            let mut terms = Vec::new();
            push_normalized_class_term(&mut terms, first, budget)?;
            push_normalized_class_term(&mut terms, second, budget)?;
            return normalized_class_boolean_term(symbols, terms, intersection, budget);
        }
        if selection.is_none()
            && matches!(
                node.tag(),
                OBJECT_MIN_CARDINALITY_TAG | OBJECT_MAX_CARDINALITY_TAG
            )
        {
            if node.field_count() != 3 {
                return Err(EncodedValidationError::invariant(
                    "object-cardinality definition no longer has schema-1 shape",
                ));
            }
            let Some(object_roles) = object_roles else {
                return Ok(None);
            };
            if !reduction_inputs_are_retained(model, symbols, base, depth, budget)? {
                return Ok(None);
            }
            let Some((cardinality, cardinality_bytes)) = integer_field_u32_bytes(
                model,
                node,
                0,
                "object-cardinality definition cardinality",
                budget,
            )?
            else {
                return Ok(None);
            };
            let normalized = match (node.tag(), complemented, cardinality) {
                (OBJECT_MIN_CARDINALITY_TAG, false, 0) => return Ok(None),
                (OBJECT_MIN_CARDINALITY_TAG, false, 1) => CardinalityNormalization::Quantifier {
                    kind: ObjectQuantifierKind::Some,
                    complement_filler: false,
                },
                (OBJECT_MIN_CARDINALITY_TAG, false, _) => CardinalityNormalization::Cardinality {
                    kind: ObjectCardinalityKind::Minimum,
                    cardinality,
                    cardinality_bytes,
                },
                (OBJECT_MIN_CARDINALITY_TAG, true, 0) => {
                    return Err(EncodedValidationError::invariant(
                        "complemented zero minimum did not reduce to a builtin",
                    ));
                }
                (OBJECT_MIN_CARDINALITY_TAG, true, 1) | (OBJECT_MAX_CARDINALITY_TAG, false, 0) => {
                    CardinalityNormalization::Quantifier {
                        kind: ObjectQuantifierKind::All,
                        complement_filler: true,
                    }
                }
                (OBJECT_MIN_CARDINALITY_TAG, true, _) => {
                    let normalized_cardinality = cardinality.checked_sub(1).ok_or_else(|| {
                        EncodedValidationError::invariant(
                            "complemented object minimum cardinality underflowed",
                        )
                    })?;
                    CardinalityNormalization::Cardinality {
                        kind: ObjectCardinalityKind::Maximum,
                        cardinality: normalized_cardinality,
                        cardinality_bytes: canonical_u32_integer_bytes(
                            normalized_cardinality,
                            budget,
                        )?,
                    }
                }
                (OBJECT_MAX_CARDINALITY_TAG, false, u32::MAX) => return Ok(None),
                (OBJECT_MAX_CARDINALITY_TAG, false, _) => CardinalityNormalization::Cardinality {
                    kind: ObjectCardinalityKind::Maximum,
                    cardinality,
                    cardinality_bytes,
                },
                (OBJECT_MAX_CARDINALITY_TAG, true, _) => {
                    let Some(normalized_cardinality) = cardinality.checked_add(1) else {
                        return Ok(None);
                    };
                    if normalized_cardinality == 1 {
                        CardinalityNormalization::Quantifier {
                            kind: ObjectQuantifierKind::Some,
                            complement_filler: false,
                        }
                    } else {
                        CardinalityNormalization::Cardinality {
                            kind: ObjectCardinalityKind::Minimum,
                            cardinality: normalized_cardinality,
                            cardinality_bytes: canonical_u32_integer_bytes(
                                normalized_cardinality,
                                budget,
                            )?,
                        }
                    }
                }
                _ => {
                    return Err(EncodedValidationError::invariant(
                        "object-cardinality definition changed constructor",
                    ));
                }
            };
            let property = node_field(model, node, 1, "object-cardinality definition role")?;
            let role_id = named_object_role_id(model, symbols, object_roles, property, budget)?;
            let filler = node_field(model, node, 2, "object-cardinality definition filler")?;
            let filler_depth =
                child_expression_depth(depth, "object-cardinality filler depth overflowed")?;
            PhaseBudget::count(
                filler_depth,
                budget.limits.max_canonical_depth,
                "class-expression depth",
            )?;
            let complement_filler = matches!(
                &normalized,
                CardinalityNormalization::Quantifier {
                    complement_filler: true,
                    ..
                }
            );
            let Some(filler) = normalized_class_term(
                model,
                symbols,
                Some(object_roles),
                data_roles,
                filler,
                complement_filler,
                filler_depth,
                scope_maps,
                budget,
            )?
            else {
                return Ok(None);
            };
            let property_key = canonical::canonical_node_key(model, property, scope_maps, budget)?;
            return match normalized {
                CardinalityNormalization::Quantifier { kind, .. } => {
                    let key =
                        synthetic_object_quantifier_key(kind, &property_key, filler.key(), budget)?;
                    budget.claim_owned(
                        size_of::<NormalizedObjectQuantifierTerm>()
                            + size_of::<NormalizedClassTerm>(),
                    )?;
                    Ok(Some(NormalizedClassTerm::ObjectQuantifier(
                        NormalizedObjectQuantifierTerm {
                            kind,
                            role_id,
                            property_key,
                            key,
                            filler: Box::new(filler),
                        },
                    )))
                }
                CardinalityNormalization::Cardinality {
                    kind,
                    cardinality,
                    cardinality_bytes,
                } => {
                    let tag = match kind {
                        ObjectCardinalityKind::Minimum => OBJECT_MIN_CARDINALITY_TAG,
                        ObjectCardinalityKind::Maximum => OBJECT_MAX_CARDINALITY_TAG,
                    };
                    let key = synthetic_object_cardinality_key(
                        tag,
                        &cardinality_bytes,
                        &property_key,
                        filler.key(),
                        budget,
                    )?;
                    budget.claim_owned(
                        size_of::<NormalizedObjectCardinalityTerm>()
                            + size_of::<NormalizedClassTerm>(),
                    )?;
                    Ok(Some(NormalizedClassTerm::ObjectCardinality(
                        NormalizedObjectCardinalityTerm {
                            kind,
                            cardinality,
                            cardinality_bytes,
                            role_id,
                            property_key,
                            key,
                            filler: Box::new(filler),
                        },
                    )))
                }
            };
        }
        let Some(mut selection) = selection else {
            return Ok(None);
        };
        if complemented {
            if atomic_class_selection_has_display(symbols, selection, THING_DISPLAY)? {
                selection.source = AtomicClassSource::Entity(class_id_by_display(
                    &symbols.entity_domain,
                    NOTHING_DISPLAY,
                )?);
            } else if atomic_class_selection_has_display(symbols, selection, NOTHING_DISPLAY)? {
                selection.source = AtomicClassSource::Entity(class_id_by_display(
                    &symbols.entity_domain,
                    THING_DISPLAY,
                )?);
            } else if matches!(node.tag(), ENTITY_TAG | OBJECT_ONE_OF_TAG) {
                selection.negative = true;
                selection.expression = base;
            } else {
                return Ok(None);
            }
        }
        if let AtomicClassSource::Nominal(nominal) = selection.source {
            let base_key = canonical::canonical_node_key(model, nominal, scope_maps, budget)?;
            let individual_entity_ids = named_nominal_entity_ids(model, symbols, nominal, budget)?;
            let mut expression_symbols = Vec::new();
            let nominal_seed = class_expression_symbol_seed(&base_key, OBJECT_ONE_OF_TAG, budget)?;
            push_class_expression_symbol_seed(&mut expression_symbols, nominal_seed, budget)?;
            let key = if selection.negative {
                let key = synthetic_class_complement_key(&base_key, budget)?;
                let complement_seed =
                    class_expression_symbol_seed(&key, OBJECT_COMPLEMENT_OF_TAG, budget)?;
                push_class_expression_symbol_seed(
                    &mut expression_symbols,
                    complement_seed,
                    budget,
                )?;
                key
            } else {
                budget.claim_owned(base_key.len())?;
                base_key.clone()
            };
            budget.claim_owned(size_of::<NormalizedNominalClassTerm>())?;
            return Ok(Some(NormalizedClassTerm::Nominal(
                NormalizedNominalClassTerm {
                    base_key,
                    key,
                    individual_entity_ids,
                    negative: selection.negative,
                    symbols: expression_symbols,
                },
            )));
        }
        let AtomicClassSource::Entity(entity_id) = selection.source else {
            return Err(EncodedValidationError::invariant(
                "normalized atomic class source changed kind",
            ));
        };
        let entity = symbols
            .entity_domain
            .values
            .get(usize::try_from(entity_id).unwrap_or(usize::MAX))
            .ok_or_else(|| {
                EncodedValidationError::invariant("normalized class literal entity ID is dangling")
            })?;
        budget.claim_owned(entity.key.len())?;
        let base_key = entity.key.clone();
        let mut expression_symbols = Vec::new();
        let key = if selection.negative {
            let key = synthetic_class_complement_key(&base_key, budget)?;
            let seed = class_expression_symbol_seed(&key, OBJECT_COMPLEMENT_OF_TAG, budget)?;
            push_class_expression_symbol_seed(&mut expression_symbols, seed, budget)?;
            key
        } else {
            base_key
        };
        budget.claim_owned(size_of::<NormalizedAtomicClassTerm>())?;
        return Ok(Some(NormalizedClassTerm::Atomic(
            NormalizedAtomicClassTerm {
                selection,
                key,
                symbols: expression_symbols,
            },
        )));
    }

    if node.field_count() != 1 {
        return Err(EncodedValidationError::invariant(
            "recursive class Boolean expression no longer has schema-1 shape",
        ));
    }
    let component = required_component(
        model.field(node.fields().start)?,
        "recursive class Boolean operands",
    )?;
    let ComponentValue::Collection(source_operands) = model.resolve(component)? else {
        return Err(EncodedValidationError::invariant(
            "recursive class Boolean operands did not resolve to a collection",
        ));
    };
    if source_operands.len() < 2 {
        return Err(EncodedValidationError::invariant(
            "recursive class Boolean expression has fewer than two operands",
        ));
    }
    let intersection = (node.tag() == OBJECT_INTERSECTION_OF_TAG) != complemented;
    let operand_depth = child_expression_depth(depth, "class-expression depth overflowed")?;
    PhaseBudget::count(
        operand_depth,
        budget.limits.max_canonical_depth,
        "class-expression depth",
    )?;
    let mut terms = Vec::<NormalizedClassTerm>::new();
    for item_index in source_operands.items() {
        budget.claim_work(1)?;
        let item = required_component(model.item(item_index)?, "recursive class Boolean operand")?;
        let ComponentValue::Node(operand) = model.resolve(item)? else {
            return Err(EncodedValidationError::invariant(
                "recursive class Boolean operand did not resolve to a node",
            ));
        };
        let Some(term) = normalized_class_term(
            model,
            symbols,
            object_roles,
            data_roles,
            operand,
            complemented,
            operand_depth,
            scope_maps,
            budget,
        )?
        else {
            return Ok(None);
        };
        push_normalized_class_term(&mut terms, term, budget)?;
    }
    normalized_class_boolean_term(symbols, terms, intersection, budget)
}

fn normalized_class_boolean_term(
    symbols: &SymbolPhase,
    terms: Vec<NormalizedClassTerm>,
    intersection: bool,
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<NormalizedClassTerm>> {
    let mut operands = Vec::<NormalizedClassTerm>::new();
    let mut absorbing = None;
    let mut identity = None;
    for term in terms {
        if let NormalizedClassTerm::Atomic(atomic) = &term {
            let is_thing =
                atomic_class_selection_has_display(symbols, atomic.selection, THING_DISPLAY)?;
            let is_nothing =
                atomic_class_selection_has_display(symbols, atomic.selection, NOTHING_DISPLAY)?;
            if (intersection && is_nothing) || (!intersection && is_thing) {
                absorbing.get_or_insert(term);
                continue;
            }
            if (intersection && is_thing) || (!intersection && is_nothing) {
                identity.get_or_insert(term);
                continue;
            }
        }
        match term {
            NormalizedClassTerm::Boolean(term) if term.intersection == intersection => {
                for nested in term.operands {
                    push_normalized_class_term(&mut operands, nested, budget)?;
                }
            }
            term => push_normalized_class_term(&mut operands, term, budget)?,
        }
    }
    if let Some(term) = absorbing {
        return Ok(Some(term));
    }
    budget.claim_work(sort_work(operands.len()))?;
    operands.sort_by(|left, right| left.key().cmp(right.key()));
    operands.dedup_by(|left, right| left.key() == right.key());
    match operands.len() {
        0 => return Ok(identity),
        1 => return Ok(operands.pop()),
        _ => {}
    }
    let expression_tag = if intersection {
        OBJECT_INTERSECTION_OF_TAG
    } else {
        OBJECT_UNION_OF_TAG
    };
    let key = synthetic_boolean_key(
        expression_tag,
        operands.iter().map(NormalizedClassTerm::key),
        operands.len(),
        budget,
    )?;
    budget.claim_owned(size_of::<NormalizedClassBooleanTerm>())?;
    Ok(Some(NormalizedClassTerm::Boolean(
        NormalizedClassBooleanTerm {
            intersection,
            key,
            operands,
        },
    )))
}

#[allow(clippy::too_many_arguments)]
fn normalized_object_restriction_term<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    object_roles: &ObjectRolePhase,
    data_roles: Option<&DataRolePhase>,
    property: NodeId,
    role_id: u32,
    filler: NodeId,
    filler_depth: usize,
    normalization: CardinalityNormalization,
    scope_maps: &[AnonymousScopeMap],
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<NormalizedClassTerm>> {
    let complement_filler = matches!(
        &normalization,
        CardinalityNormalization::Quantifier {
            complement_filler: true,
            ..
        }
    );
    let Some(filler) = normalized_class_term(
        model,
        symbols,
        Some(object_roles),
        data_roles,
        filler,
        complement_filler,
        filler_depth,
        scope_maps,
        budget,
    )?
    else {
        return Ok(None);
    };
    let property_key = canonical::canonical_node_key(model, property, scope_maps, budget)?;
    match normalization {
        CardinalityNormalization::Quantifier { kind, .. } => {
            let key = synthetic_object_quantifier_key(kind, &property_key, filler.key(), budget)?;
            budget.claim_owned(
                size_of::<NormalizedObjectQuantifierTerm>() + size_of::<NormalizedClassTerm>(),
            )?;
            Ok(Some(NormalizedClassTerm::ObjectQuantifier(
                NormalizedObjectQuantifierTerm {
                    kind,
                    role_id,
                    property_key,
                    key,
                    filler: Box::new(filler),
                },
            )))
        }
        CardinalityNormalization::Cardinality {
            kind,
            cardinality,
            cardinality_bytes,
        } => {
            let tag = match kind {
                ObjectCardinalityKind::Minimum => OBJECT_MIN_CARDINALITY_TAG,
                ObjectCardinalityKind::Maximum => OBJECT_MAX_CARDINALITY_TAG,
            };
            let key = synthetic_object_cardinality_key(
                tag,
                &cardinality_bytes,
                &property_key,
                filler.key(),
                budget,
            )?;
            budget.claim_owned(
                size_of::<NormalizedObjectCardinalityTerm>() + size_of::<NormalizedClassTerm>(),
            )?;
            Ok(Some(NormalizedClassTerm::ObjectCardinality(
                NormalizedObjectCardinalityTerm {
                    kind,
                    cardinality,
                    cardinality_bytes,
                    role_id,
                    property_key,
                    key,
                    filler: Box::new(filler),
                },
            )))
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn normalized_data_restriction_term<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    property: NodeId,
    role_id: u32,
    filler: NodeId,
    filler_depth: usize,
    normalization: DataCardinalityNormalization,
    scope_maps: &[AnonymousScopeMap],
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<NormalizedClassTerm>> {
    let complement_filler = matches!(
        &normalization,
        DataCardinalityNormalization::Quantifier {
            complement_filler: true,
            ..
        }
    );
    let Some(filler) = normalized_data_term(
        model,
        symbols,
        filler,
        complement_filler,
        filler_depth,
        scope_maps,
        budget,
    )?
    else {
        return Ok(None);
    };
    if matches!(
        &normalization,
        DataCardinalityNormalization::Cardinality { .. }
    ) {
        if let NormalizedDataTerm::Atomic(atomic) = &filler {
            if atomic_data_range_selection_is_bottom(
                model,
                symbols,
                atomic.selection.ok_or_else(|| {
                    EncodedValidationError::invariant(
                        "normalized data-cardinality filler became synthetic",
                    )
                })?,
            )? {
                return Ok(None);
            }
        }
    }
    let property_key = canonical::canonical_node_key(model, property, scope_maps, budget)?;
    match normalization {
        DataCardinalityNormalization::Quantifier { kind, .. } => {
            let key = synthetic_data_quantifier_key(kind, &property_key, filler.key(), budget)?;
            budget.claim_owned(size_of::<NormalizedDataQuantifierTerm>())?;
            Ok(Some(NormalizedClassTerm::DataQuantifier(
                NormalizedDataQuantifierTerm {
                    kind,
                    role_id,
                    property_key,
                    key,
                    filler,
                },
            )))
        }
        DataCardinalityNormalization::Cardinality {
            kind,
            cardinality,
            cardinality_bytes,
        } => {
            let tag = match kind {
                DataCardinalityKind::Minimum => DATA_MIN_CARDINALITY_TAG,
                DataCardinalityKind::Maximum => DATA_MAX_CARDINALITY_TAG,
            };
            let key = synthetic_data_cardinality_key(
                tag,
                &cardinality_bytes,
                &property_key,
                filler.key(),
                budget,
            )?;
            budget.claim_owned(size_of::<NormalizedDataCardinalityTerm>())?;
            Ok(Some(NormalizedClassTerm::DataCardinality(
                NormalizedDataCardinalityTerm {
                    kind,
                    cardinality,
                    cardinality_bytes,
                    role_id,
                    property_key,
                    key,
                    filler,
                },
            )))
        }
    }
}

fn push_normalized_class_term(
    target: &mut Vec<NormalizedClassTerm>,
    term: NormalizedClassTerm,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    let following = target.len().checked_add(1).ok_or_else(|| {
        EncodedValidationError::resource("normalized class term count overflowed")
    })?;
    PhaseBudget::count(
        following,
        budget.limits.max_class_symbols,
        "normalized class term count",
    )?;
    budget.claim_owned(size_of::<NormalizedClassTerm>())?;
    target
        .try_reserve(1)
        .map_err(|_| EncodedValidationError::resource("normalized class term allocation failed"))?;
    target.push(term);
    Ok(())
}

fn synthetic_class_complement_key(
    operand_key: &[u8],
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<u8>> {
    let mut key = Vec::new();
    push_generated_varint(&mut key, u64::from(OBJECT_COMPLEMENT_OF_TAG), budget)?;
    push_generated_byte(&mut key, 1, budget)?;
    push_generated_frame(&mut key, operand_key, budget)?;
    Ok(key)
}

fn synthetic_object_quantifier_key(
    kind: ObjectQuantifierKind,
    property_key: &[u8],
    filler_key: &[u8],
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<u8>> {
    let tag = match kind {
        ObjectQuantifierKind::Some => OBJECT_SOME_VALUES_FROM_TAG,
        ObjectQuantifierKind::All => OBJECT_ALL_VALUES_FROM_TAG,
    };
    let mut key = Vec::new();
    push_generated_varint(&mut key, u64::from(tag), budget)?;
    push_generated_byte(&mut key, 1, budget)?;
    push_generated_frame(&mut key, property_key, budget)?;
    push_generated_byte(&mut key, 1, budget)?;
    push_generated_frame(&mut key, filler_key, budget)?;
    Ok(key)
}

fn synthetic_data_quantifier_key(
    kind: DataQuantifierKind,
    property_key: &[u8],
    filler_key: &[u8],
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<u8>> {
    let tag = match kind {
        DataQuantifierKind::Some => DATA_SOME_VALUES_FROM_TAG,
        DataQuantifierKind::All => DATA_ALL_VALUES_FROM_TAG,
    };
    let mut key = Vec::new();
    push_generated_varint(&mut key, u64::from(tag), budget)?;
    push_generated_byte(&mut key, 7, budget)?;
    push_generated_varint(&mut key, 1, budget)?;
    push_generated_byte(&mut key, 1, budget)?;
    push_generated_frame(&mut key, property_key, budget)?;
    push_generated_byte(&mut key, 1, budget)?;
    push_generated_frame(&mut key, filler_key, budget)?;
    Ok(key)
}

fn synthetic_data_cardinality_key(
    tag: u16,
    cardinality_bytes: &[u8],
    property_key: &[u8],
    filler_key: &[u8],
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<u8>> {
    if !matches!(
        tag,
        DATA_MIN_CARDINALITY_TAG | DATA_MAX_CARDINALITY_TAG | DATA_EXACT_CARDINALITY_TAG
    ) {
        return Err(EncodedValidationError::invariant(
            "synthetic data cardinality has an unsupported constructor",
        ));
    }
    let mut key = Vec::new();
    push_generated_varint(&mut key, u64::from(tag), budget)?;
    push_generated_byte(&mut key, 4, budget)?;
    for byte in cardinality_bytes {
        push_generated_byte(&mut key, *byte, budget)?;
    }
    push_generated_byte(&mut key, 1, budget)?;
    push_generated_frame(&mut key, property_key, budget)?;
    push_generated_byte(&mut key, 1, budget)?;
    push_generated_frame(&mut key, filler_key, budget)?;
    Ok(key)
}

fn synthetic_object_cardinality_key(
    tag: u16,
    cardinality_bytes: &[u8],
    property_key: &[u8],
    filler_key: &[u8],
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<u8>> {
    if !matches!(
        tag,
        OBJECT_MIN_CARDINALITY_TAG | OBJECT_MAX_CARDINALITY_TAG | OBJECT_EXACT_CARDINALITY_TAG
    ) {
        return Err(EncodedValidationError::invariant(
            "synthetic object cardinality has an unsupported constructor",
        ));
    }
    let mut key = Vec::new();
    push_generated_varint(&mut key, u64::from(tag), budget)?;
    push_generated_byte(&mut key, 4, budget)?;
    for byte in cardinality_bytes {
        push_generated_byte(&mut key, *byte, budget)?;
    }
    push_generated_byte(&mut key, 1, budget)?;
    push_generated_frame(&mut key, property_key, budget)?;
    push_generated_byte(&mut key, 1, budget)?;
    push_generated_frame(&mut key, filler_key, budget)?;
    Ok(key)
}

fn class_expression_symbol_seed(
    key: &[u8],
    tag: u16,
    budget: &mut PhaseBudget,
) -> EncodedResult<ClassExpressionSymbolSeed> {
    budget.claim_work(key.len())?;
    let digest = crate::model::hex(&Sha256::digest(key));
    let prefix = class_expression_prefix(tag)?;
    let display_len = prefix
        .len()
        .checked_add(digest.len())
        .ok_or_else(|| EncodedValidationError::resource("class-expression display overflowed"))?;
    budget.claim_owned(
        size_of::<ClassExpressionSymbolSeed>()
            .checked_add(key.len())
            .and_then(|value| value.checked_add(display_len))
            .ok_or_else(|| {
                EncodedValidationError::resource("class-expression seed ownership overflowed")
            })?,
    )?;
    let mut stored_key = Vec::new();
    stored_key.try_reserve_exact(key.len()).map_err(|_| {
        EncodedValidationError::resource("class-expression seed key allocation failed")
    })?;
    stored_key.extend_from_slice(key);
    let mut display = String::new();
    display.try_reserve_exact(display_len).map_err(|_| {
        EncodedValidationError::resource("class-expression seed display allocation failed")
    })?;
    display.push_str(prefix);
    display.push_str(&digest);
    Ok(ClassExpressionSymbolSeed {
        key: stored_key,
        display,
    })
}

fn push_class_expression_symbol_seed(
    target: &mut Vec<ClassExpressionSymbolSeed>,
    seed: ClassExpressionSymbolSeed,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    budget.claim_work(1)?;
    target.try_reserve(1).map_err(|_| {
        EncodedValidationError::resource("class-expression seed collection allocation failed")
    })?;
    target.push(seed);
    Ok(())
}

fn atomize_normalized_class_term(
    term: NormalizedClassTerm,
    source_expression: Option<NodeId>,
    polarity: DefinitionPolarity,
    namespace: [u8; 32],
    definitions: &mut Vec<ClassBooleanDefinition>,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<u8>> {
    match term {
        NormalizedClassTerm::Atomic(_) => Err(EncodedValidationError::invariant(
            "atomic class term reached generated-definition atomization",
        )),
        NormalizedClassTerm::Nominal(_) => Err(EncodedValidationError::invariant(
            "nominal class term reached generated-definition atomization",
        )),
        NormalizedClassTerm::Boolean(term) => atomize_normalized_class_boolean(
            term,
            source_expression,
            polarity,
            namespace,
            definitions,
            budget,
        ),
        NormalizedClassTerm::ObjectSelf(term) => atomize_normalized_object_self(
            term,
            source_expression,
            polarity,
            namespace,
            definitions,
            budget,
        ),
        NormalizedClassTerm::ObjectQuantifier(term) => atomize_normalized_object_quantifier(
            term,
            source_expression,
            polarity,
            namespace,
            definitions,
            budget,
        ),
        NormalizedClassTerm::ObjectCardinality(term) => atomize_normalized_object_cardinality(
            term,
            source_expression,
            polarity,
            namespace,
            definitions,
            budget,
        ),
        NormalizedClassTerm::DataQuantifier(term) => atomize_normalized_data_quantifier(
            term,
            source_expression,
            polarity,
            namespace,
            definitions,
            budget,
        ),
        NormalizedClassTerm::DataCardinality(term) => atomize_normalized_data_cardinality(
            term,
            source_expression,
            polarity,
            namespace,
            definitions,
            budget,
        ),
    }
}

fn atomize_normalized_data_quantifier(
    term: NormalizedDataQuantifierTerm,
    source_expression: Option<NodeId>,
    polarity: DefinitionPolarity,
    namespace: [u8; 32],
    definitions: &mut Vec<ClassBooleanDefinition>,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<u8>> {
    let NormalizedDataQuantifierTerm {
        kind,
        role_id,
        property_key,
        key,
        filler,
    } = term;
    let expression_tag = match kind {
        DataQuantifierKind::Some => DATA_SOME_VALUES_FROM_TAG,
        DataQuantifierKind::All => DATA_ALL_VALUES_FROM_TAG,
    };
    let mut data_dependencies = Vec::new();
    let (filler_base_key, filler_negative, filler_key, data_expression_symbols) = match filler {
        NormalizedDataTerm::Atomic(filler) => {
            let NormalizedAtomicDataTerm {
                selection: _,
                base_key,
                negative,
                key,
                symbols,
            } = filler;
            (base_key, negative, key, symbols)
        }
        NormalizedDataTerm::Boolean(filler) => {
            let generated_key = atomize_normalized_data_boolean(
                filler,
                None,
                namespace,
                polarity,
                &mut data_dependencies,
                budget,
            )?;
            budget.claim_owned(generated_key.len())?;
            (generated_key.clone(), false, generated_key, Vec::new())
        }
    };
    let mut expression_symbols = Vec::new();
    let source_seed = class_expression_symbol_seed(&key, expression_tag, budget)?;
    push_class_expression_symbol_seed(&mut expression_symbols, source_seed, budget)?;
    let rewritten_key = synthetic_data_quantifier_key(kind, &property_key, &filler_key, budget)?;
    let rewritten_seed = class_expression_symbol_seed(&rewritten_key, expression_tag, budget)?;
    push_class_expression_symbol_seed(&mut expression_symbols, rewritten_seed, budget)?;
    budget.claim_work(sort_work(expression_symbols.len()))?;
    expression_symbols.sort_by(|left, right| left.key.cmp(&right.key));
    expression_symbols.dedup_by(|left, right| left.key == right.key);
    let (generated_key, generated_display) =
        generated_class_symbol(namespace, &key, polarity, budget)?;
    budget.claim_owned(generated_key.len())?;
    let returned_key = generated_key.clone();
    let mut expressions = Vec::new();
    if let Some(expression) = source_expression {
        budget.claim_owned(size_of::<NodeId>())?;
        expressions.try_reserve_exact(1).map_err(|_| {
            EncodedValidationError::resource(
                "data-quantifier definition expression allocation failed",
            )
        })?;
        expressions.push(expression);
    }
    budget.claim_owned(size_of::<ClassBooleanDefinition>())?;
    definitions.try_reserve(1).map_err(|_| {
        EncodedValidationError::resource("data-quantifier definition allocation failed")
    })?;
    definitions.push(ClassBooleanDefinition {
        expressions,
        roots: Vec::new(),
        expression_key: key,
        expression_symbols,
        data_expression_symbols,
        intersection: false,
        operands: Vec::new(),
        object_self_role_id: None,
        object_quantifier: None,
        object_cardinality: None,
        data_quantifier: Some(DataQuantifierDefinition {
            kind,
            role_id,
            filler: DataRangeDefinition {
                base_key: filler_base_key,
                negative: filler_negative,
            },
        }),
        data_cardinality: None,
        data_dependencies,
        complement: false,
        polarity,
        generated_key,
        generated_display,
        provenance: Vec::new(),
    });
    Ok(returned_key)
}

fn atomize_normalized_data_cardinality(
    term: NormalizedDataCardinalityTerm,
    source_expression: Option<NodeId>,
    polarity: DefinitionPolarity,
    namespace: [u8; 32],
    definitions: &mut Vec<ClassBooleanDefinition>,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<u8>> {
    let NormalizedDataCardinalityTerm {
        kind,
        cardinality,
        cardinality_bytes,
        role_id,
        property_key,
        key,
        filler,
    } = term;
    let expression_tag = match kind {
        DataCardinalityKind::Minimum => DATA_MIN_CARDINALITY_TAG,
        DataCardinalityKind::Maximum => DATA_MAX_CARDINALITY_TAG,
    };
    let mut data_dependencies = Vec::new();
    let (filler_base_key, filler_negative, filler_key, data_expression_symbols) = match filler {
        NormalizedDataTerm::Atomic(filler) => {
            let NormalizedAtomicDataTerm {
                selection: _,
                base_key,
                negative,
                key,
                symbols,
            } = filler;
            (base_key, negative, key, symbols)
        }
        NormalizedDataTerm::Boolean(filler) => {
            let filler_polarity = match kind {
                DataCardinalityKind::Minimum => polarity,
                DataCardinalityKind::Maximum => match polarity {
                    DefinitionPolarity::Positive => DefinitionPolarity::Negative,
                    DefinitionPolarity::Negative => DefinitionPolarity::Positive,
                },
            };
            let generated_key = atomize_normalized_data_boolean(
                filler,
                None,
                namespace,
                filler_polarity,
                &mut data_dependencies,
                budget,
            )?;
            budget.claim_owned(generated_key.len())?;
            (generated_key.clone(), false, generated_key, Vec::new())
        }
    };
    let mut expression_symbols = Vec::new();
    let source_seed = class_expression_symbol_seed(&key, expression_tag, budget)?;
    push_class_expression_symbol_seed(&mut expression_symbols, source_seed, budget)?;
    let rewritten_key = synthetic_data_cardinality_key(
        expression_tag,
        &cardinality_bytes,
        &property_key,
        &filler_key,
        budget,
    )?;
    let rewritten_seed = class_expression_symbol_seed(&rewritten_key, expression_tag, budget)?;
    push_class_expression_symbol_seed(&mut expression_symbols, rewritten_seed, budget)?;
    budget.claim_work(sort_work(expression_symbols.len()))?;
    expression_symbols.sort_by(|left, right| left.key.cmp(&right.key));
    expression_symbols.dedup_by(|left, right| left.key == right.key);
    let (generated_key, generated_display) =
        generated_class_symbol(namespace, &key, polarity, budget)?;
    budget.claim_owned(generated_key.len())?;
    let returned_key = generated_key.clone();
    let mut expressions = Vec::new();
    if let Some(expression) = source_expression {
        budget.claim_owned(size_of::<NodeId>())?;
        expressions.try_reserve_exact(1).map_err(|_| {
            EncodedValidationError::resource(
                "data-cardinality definition expression allocation failed",
            )
        })?;
        expressions.push(expression);
    }
    budget.claim_owned(size_of::<ClassBooleanDefinition>())?;
    definitions.try_reserve(1).map_err(|_| {
        EncodedValidationError::resource("data-cardinality definition allocation failed")
    })?;
    definitions.push(ClassBooleanDefinition {
        expressions,
        roots: Vec::new(),
        expression_key: key,
        expression_symbols,
        data_expression_symbols,
        intersection: false,
        operands: Vec::new(),
        object_self_role_id: None,
        object_quantifier: None,
        object_cardinality: None,
        data_quantifier: None,
        data_cardinality: Some(DataCardinalityDefinition {
            kind,
            cardinality,
            role_id,
            filler: DataRangeDefinition {
                base_key: filler_base_key,
                negative: filler_negative,
            },
        }),
        data_dependencies,
        complement: false,
        polarity,
        generated_key,
        generated_display,
        provenance: Vec::new(),
    });
    Ok(returned_key)
}

fn atomize_normalized_object_cardinality(
    term: NormalizedObjectCardinalityTerm,
    source_expression: Option<NodeId>,
    polarity: DefinitionPolarity,
    namespace: [u8; 32],
    definitions: &mut Vec<ClassBooleanDefinition>,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<u8>> {
    let NormalizedObjectCardinalityTerm {
        kind,
        cardinality,
        cardinality_bytes,
        role_id,
        property_key,
        key,
        filler,
    } = term;
    let mut expression_symbols = Vec::new();
    let (filler_key, filler_operand) = match *filler {
        NormalizedClassTerm::Atomic(filler) => {
            for seed in filler.symbols {
                push_class_expression_symbol_seed(&mut expression_symbols, seed, budget)?;
            }
            (filler.key, ClassBooleanOperand::Atomic(filler.selection))
        }
        NormalizedClassTerm::Nominal(filler) => {
            for seed in filler.symbols {
                push_class_expression_symbol_seed(&mut expression_symbols, seed, budget)?;
            }
            (
                filler.key,
                ClassBooleanOperand::Nominal {
                    key: filler.base_key,
                    individual_entity_ids: filler.individual_entity_ids,
                    negative: filler.negative,
                },
            )
        }
        filler => {
            let filler_polarity = match kind {
                ObjectCardinalityKind::Minimum => polarity,
                ObjectCardinalityKind::Maximum => match polarity {
                    DefinitionPolarity::Positive => DefinitionPolarity::Negative,
                    DefinitionPolarity::Negative => DefinitionPolarity::Positive,
                },
            };
            let generated_key = atomize_normalized_class_term(
                filler,
                None,
                filler_polarity,
                namespace,
                definitions,
                budget,
            )?;
            budget.claim_owned(generated_key.len())?;
            (
                generated_key.clone(),
                ClassBooleanOperand::Generated {
                    key: generated_key,
                    negative: false,
                },
            )
        }
    };
    let expression_tag = match kind {
        ObjectCardinalityKind::Minimum => OBJECT_MIN_CARDINALITY_TAG,
        ObjectCardinalityKind::Maximum => OBJECT_MAX_CARDINALITY_TAG,
    };
    let source_seed = class_expression_symbol_seed(&key, expression_tag, budget)?;
    push_class_expression_symbol_seed(&mut expression_symbols, source_seed, budget)?;
    let rewritten_key = synthetic_object_cardinality_key(
        expression_tag,
        &cardinality_bytes,
        &property_key,
        &filler_key,
        budget,
    )?;
    let rewritten_seed = class_expression_symbol_seed(&rewritten_key, expression_tag, budget)?;
    push_class_expression_symbol_seed(&mut expression_symbols, rewritten_seed, budget)?;
    budget.claim_work(sort_work(expression_symbols.len()))?;
    expression_symbols.sort_by(|left, right| left.key.cmp(&right.key));
    expression_symbols.dedup_by(|left, right| left.key == right.key);
    let (generated_key, generated_display) =
        generated_class_symbol(namespace, &key, polarity, budget)?;
    budget.claim_owned(generated_key.len())?;
    let returned_key = generated_key.clone();
    let mut expressions = Vec::new();
    if let Some(expression) = source_expression {
        budget.claim_owned(size_of::<NodeId>())?;
        expressions.try_reserve_exact(1).map_err(|_| {
            EncodedValidationError::resource(
                "object-cardinality definition expression allocation failed",
            )
        })?;
        expressions.push(expression);
    }
    budget.claim_owned(size_of::<ClassBooleanDefinition>() + size_of::<ClassBooleanOperand>())?;
    definitions.try_reserve(1).map_err(|_| {
        EncodedValidationError::resource("object-cardinality definition allocation failed")
    })?;
    definitions.push(ClassBooleanDefinition {
        expressions,
        roots: Vec::new(),
        expression_key: key,
        expression_symbols,
        data_expression_symbols: Vec::new(),
        intersection: false,
        operands: vec![filler_operand],
        object_self_role_id: None,
        object_quantifier: None,
        object_cardinality: Some(ObjectCardinalityDefinition {
            kind,
            cardinality,
            role_id,
        }),
        data_quantifier: None,
        data_cardinality: None,
        data_dependencies: Vec::new(),
        complement: false,
        polarity,
        generated_key,
        generated_display,
        provenance: Vec::new(),
    });
    Ok(returned_key)
}

fn atomize_normalized_object_quantifier(
    term: NormalizedObjectQuantifierTerm,
    source_expression: Option<NodeId>,
    polarity: DefinitionPolarity,
    namespace: [u8; 32],
    definitions: &mut Vec<ClassBooleanDefinition>,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<u8>> {
    let NormalizedObjectQuantifierTerm {
        kind,
        role_id,
        property_key,
        key,
        filler,
    } = term;
    let expression_tag = match kind {
        ObjectQuantifierKind::Some => OBJECT_SOME_VALUES_FROM_TAG,
        ObjectQuantifierKind::All => OBJECT_ALL_VALUES_FROM_TAG,
    };
    let mut expression_symbols = Vec::new();
    let (filler_key, filler_operand) = match *filler {
        NormalizedClassTerm::Atomic(filler) => {
            for seed in filler.symbols {
                push_class_expression_symbol_seed(&mut expression_symbols, seed, budget)?;
            }
            (filler.key, ClassBooleanOperand::Atomic(filler.selection))
        }
        NormalizedClassTerm::Nominal(filler) => {
            for seed in filler.symbols {
                push_class_expression_symbol_seed(&mut expression_symbols, seed, budget)?;
            }
            (
                filler.key,
                ClassBooleanOperand::Nominal {
                    key: filler.base_key,
                    individual_entity_ids: filler.individual_entity_ids,
                    negative: filler.negative,
                },
            )
        }
        filler => {
            let generated_key = atomize_normalized_class_term(
                filler,
                None,
                polarity,
                namespace,
                definitions,
                budget,
            )?;
            budget.claim_owned(generated_key.len())?;
            (
                generated_key.clone(),
                ClassBooleanOperand::Generated {
                    key: generated_key,
                    negative: false,
                },
            )
        }
    };
    let source_seed = class_expression_symbol_seed(&key, expression_tag, budget)?;
    push_class_expression_symbol_seed(&mut expression_symbols, source_seed, budget)?;
    let rewritten_key = synthetic_object_quantifier_key(kind, &property_key, &filler_key, budget)?;
    let rewritten_seed = class_expression_symbol_seed(&rewritten_key, expression_tag, budget)?;
    push_class_expression_symbol_seed(&mut expression_symbols, rewritten_seed, budget)?;
    budget.claim_work(sort_work(expression_symbols.len()))?;
    expression_symbols.sort_by(|left, right| left.key.cmp(&right.key));
    expression_symbols.dedup_by(|left, right| left.key == right.key);
    let (generated_key, generated_display) =
        generated_class_symbol(namespace, &key, polarity, budget)?;
    budget.claim_owned(generated_key.len())?;
    let returned_key = generated_key.clone();
    let mut expressions = Vec::new();
    if let Some(expression) = source_expression {
        budget.claim_owned(size_of::<NodeId>())?;
        expressions.try_reserve_exact(1).map_err(|_| {
            EncodedValidationError::resource(
                "object-quantifier definition expression allocation failed",
            )
        })?;
        expressions.push(expression);
    }
    budget.claim_owned(size_of::<ClassBooleanDefinition>() + size_of::<ClassBooleanOperand>())?;
    definitions.try_reserve(1).map_err(|_| {
        EncodedValidationError::resource("object-quantifier definition allocation failed")
    })?;
    definitions.push(ClassBooleanDefinition {
        expressions,
        roots: Vec::new(),
        expression_key: key,
        expression_symbols,
        data_expression_symbols: Vec::new(),
        intersection: false,
        operands: vec![filler_operand],
        object_self_role_id: None,
        object_quantifier: Some(ObjectQuantifierDefinition { kind, role_id }),
        object_cardinality: None,
        data_quantifier: None,
        data_cardinality: None,
        data_dependencies: Vec::new(),
        complement: false,
        polarity,
        generated_key,
        generated_display,
        provenance: Vec::new(),
    });
    Ok(returned_key)
}

fn atomize_normalized_object_self(
    term: NormalizedObjectSelfTerm,
    source_expression: Option<NodeId>,
    polarity: DefinitionPolarity,
    namespace: [u8; 32],
    definitions: &mut Vec<ClassBooleanDefinition>,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<u8>> {
    let NormalizedObjectSelfTerm {
        role_id,
        base_key,
        key,
        complemented,
    } = term;
    if complemented {
        budget.claim_owned(base_key.len())?;
        let inner_key = base_key.clone();
        let inner_polarity = match polarity {
            DefinitionPolarity::Positive => DefinitionPolarity::Negative,
            DefinitionPolarity::Negative => DefinitionPolarity::Positive,
        };
        let generated_operand = atomize_normalized_object_self(
            NormalizedObjectSelfTerm {
                role_id,
                base_key,
                key: inner_key,
                complemented: false,
            },
            None,
            inner_polarity,
            namespace,
            definitions,
            budget,
        )?;
        let mut expression_symbols = Vec::new();
        let source_seed = class_expression_symbol_seed(&key, OBJECT_COMPLEMENT_OF_TAG, budget)?;
        push_class_expression_symbol_seed(&mut expression_symbols, source_seed, budget)?;
        let rewritten_key = synthetic_class_complement_key(&generated_operand, budget)?;
        let rewritten_seed =
            class_expression_symbol_seed(&rewritten_key, OBJECT_COMPLEMENT_OF_TAG, budget)?;
        push_class_expression_symbol_seed(&mut expression_symbols, rewritten_seed, budget)?;
        budget.claim_work(sort_work(expression_symbols.len()))?;
        expression_symbols.sort_by(|left, right| left.key.cmp(&right.key));
        expression_symbols.dedup_by(|left, right| left.key == right.key);
        let (generated_key, generated_display) =
            generated_class_symbol(namespace, &key, polarity, budget)?;
        budget.claim_owned(generated_key.len())?;
        let returned_key = generated_key.clone();
        let mut expressions = Vec::new();
        if let Some(expression) = source_expression {
            budget.claim_owned(size_of::<NodeId>())?;
            expressions.try_reserve_exact(1).map_err(|_| {
                EncodedValidationError::resource(
                    "object-self complement expression allocation failed",
                )
            })?;
            expressions.push(expression);
        }
        budget
            .claim_owned(size_of::<ClassBooleanDefinition>() + size_of::<ClassBooleanOperand>())?;
        definitions.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("object-self complement definition allocation failed")
        })?;
        definitions.push(ClassBooleanDefinition {
            expressions,
            roots: Vec::new(),
            expression_key: key,
            expression_symbols,
            data_expression_symbols: Vec::new(),
            intersection: false,
            operands: vec![ClassBooleanOperand::Generated {
                key: generated_operand,
                negative: true,
            }],
            object_self_role_id: None,
            object_quantifier: None,
            object_cardinality: None,
            data_quantifier: None,
            data_cardinality: None,
            data_dependencies: Vec::new(),
            complement: true,
            polarity,
            generated_key,
            generated_display,
            provenance: Vec::new(),
        });
        return Ok(returned_key);
    }
    if base_key != key {
        return Err(EncodedValidationError::invariant(
            "object-self definition changed its normalized key",
        ));
    }
    let expression_seed = class_expression_symbol_seed(&key, OBJECT_HAS_SELF_TAG, budget)?;
    let mut expression_symbols = Vec::new();
    push_class_expression_symbol_seed(&mut expression_symbols, expression_seed, budget)?;
    let (generated_key, generated_display) =
        generated_class_symbol(namespace, &key, polarity, budget)?;
    budget.claim_owned(generated_key.len())?;
    let returned_key = generated_key.clone();
    let mut expressions = Vec::new();
    if let Some(expression) = source_expression {
        budget.claim_owned(size_of::<NodeId>())?;
        expressions.try_reserve_exact(1).map_err(|_| {
            EncodedValidationError::resource("object-self definition expression allocation failed")
        })?;
        expressions.push(expression);
    }
    budget.claim_owned(size_of::<ClassBooleanDefinition>())?;
    definitions.try_reserve(1).map_err(|_| {
        EncodedValidationError::resource("object-self definition allocation failed")
    })?;
    definitions.push(ClassBooleanDefinition {
        expressions,
        roots: Vec::new(),
        expression_key: key,
        expression_symbols,
        data_expression_symbols: Vec::new(),
        intersection: false,
        operands: Vec::new(),
        object_self_role_id: Some(role_id),
        object_quantifier: None,
        object_cardinality: None,
        data_quantifier: None,
        data_cardinality: None,
        data_dependencies: Vec::new(),
        complement: false,
        polarity,
        generated_key,
        generated_display,
        provenance: Vec::new(),
    });
    Ok(returned_key)
}

fn atomize_normalized_class_boolean(
    term: NormalizedClassBooleanTerm,
    source_expression: Option<NodeId>,
    polarity: DefinitionPolarity,
    namespace: [u8; 32],
    definitions: &mut Vec<ClassBooleanDefinition>,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<u8>> {
    let expression_tag = if term.intersection {
        OBJECT_INTERSECTION_OF_TAG
    } else {
        OBJECT_UNION_OF_TAG
    };
    let mut expression_symbols = Vec::<ClassExpressionSymbolSeed>::new();
    let source_seed = class_expression_symbol_seed(&term.key, expression_tag, budget)?;
    push_class_expression_symbol_seed(&mut expression_symbols, source_seed, budget)?;
    let mut keyed = Vec::<(Vec<u8>, ClassBooleanOperand)>::new();
    budget.claim_owned(
        term.operands
            .len()
            .checked_mul(size_of::<(Vec<u8>, ClassBooleanOperand)>())
            .ok_or_else(|| {
                EncodedValidationError::resource(
                    "recursive class definition operand allocation overflowed",
                )
            })?,
    )?;
    keyed.try_reserve_exact(term.operands.len()).map_err(|_| {
        EncodedValidationError::resource("recursive class definition operand allocation failed")
    })?;
    for operand in term.operands {
        match operand {
            NormalizedClassTerm::Atomic(operand) => {
                for seed in operand.symbols {
                    push_class_expression_symbol_seed(&mut expression_symbols, seed, budget)?;
                }
                keyed.push((operand.key, ClassBooleanOperand::Atomic(operand.selection)));
            }
            NormalizedClassTerm::Nominal(operand) => {
                for seed in operand.symbols {
                    push_class_expression_symbol_seed(&mut expression_symbols, seed, budget)?;
                }
                keyed.push((
                    operand.key,
                    ClassBooleanOperand::Nominal {
                        key: operand.base_key,
                        individual_entity_ids: operand.individual_entity_ids,
                        negative: operand.negative,
                    },
                ));
            }
            operand => {
                let generated_key = atomize_normalized_class_term(
                    operand,
                    None,
                    polarity,
                    namespace,
                    definitions,
                    budget,
                )?;
                budget.claim_owned(generated_key.len())?;
                keyed.push((
                    generated_key.clone(),
                    ClassBooleanOperand::Generated {
                        key: generated_key,
                        negative: false,
                    },
                ));
            }
        }
    }
    budget.claim_work(sort_work(keyed.len()))?;
    keyed.sort_by(|left, right| left.0.cmp(&right.0));
    if keyed.len() < 2 || keyed.windows(2).any(|pair| pair[0].0 == pair[1].0) {
        return Err(EncodedValidationError::invariant(
            "recursive class definition lost distinct operands",
        ));
    }
    let rewritten_expression_key = synthetic_boolean_key(
        expression_tag,
        keyed.iter().map(|(key, _)| key.as_slice()),
        keyed.len(),
        budget,
    )?;
    let rewritten_seed =
        class_expression_symbol_seed(&rewritten_expression_key, expression_tag, budget)?;
    push_class_expression_symbol_seed(&mut expression_symbols, rewritten_seed, budget)?;
    budget.claim_work(sort_work(expression_symbols.len()))?;
    expression_symbols.sort_by(|left, right| left.key.cmp(&right.key));
    expression_symbols.dedup_by(|left, right| left.key == right.key);
    budget.claim_owned(
        keyed
            .len()
            .checked_mul(size_of::<ClassBooleanOperand>())
            .ok_or_else(|| {
                EncodedValidationError::resource(
                    "recursive generated class operand allocation overflowed",
                )
            })?,
    )?;
    let mut operands = Vec::new();
    operands.try_reserve_exact(keyed.len()).map_err(|_| {
        EncodedValidationError::resource("recursive generated class operand allocation failed")
    })?;
    operands.extend(keyed.into_iter().map(|(_, operand)| operand));
    let (generated_key, generated_display) =
        generated_class_symbol(namespace, &term.key, polarity, budget)?;
    budget.claim_owned(generated_key.len())?;
    let returned_key = generated_key.clone();
    let mut expressions = Vec::new();
    if let Some(expression) = source_expression {
        budget.claim_owned(size_of::<NodeId>())?;
        expressions.try_reserve_exact(1).map_err(|_| {
            EncodedValidationError::resource(
                "recursive class definition expression allocation failed",
            )
        })?;
        expressions.push(expression);
    }
    budget.claim_owned(size_of::<ClassBooleanDefinition>())?;
    definitions.try_reserve(1).map_err(|_| {
        EncodedValidationError::resource("recursive class definition allocation failed")
    })?;
    definitions.push(ClassBooleanDefinition {
        expressions,
        roots: Vec::new(),
        expression_key: term.key,
        expression_symbols,
        data_expression_symbols: Vec::new(),
        intersection: term.intersection,
        operands,
        object_self_role_id: None,
        object_quantifier: None,
        object_cardinality: None,
        data_quantifier: None,
        data_cardinality: None,
        data_dependencies: Vec::new(),
        complement: false,
        polarity,
        generated_key,
        generated_display,
        provenance: Vec::new(),
    });
    Ok(returned_key)
}

fn retain_class_boolean_definition(
    definitions: &mut Vec<ClassBooleanDefinition>,
    mut definition: ClassBooleanDefinition,
    provenance: [u8; 32],
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    if let Some(known) = definitions.iter_mut().find(|known| {
        known.expression_key == definition.expression_key && known.polarity == definition.polarity
    }) {
        if known.intersection != definition.intersection
            || known.operands != definition.operands
            || known.object_self_role_id != definition.object_self_role_id
            || known.object_quantifier != definition.object_quantifier
            || known.object_cardinality != definition.object_cardinality
            || known.data_quantifier != definition.data_quantifier
            || known.data_cardinality != definition.data_cardinality
            || known.data_dependencies != definition.data_dependencies
            || known.complement != definition.complement
            || known.expression_symbols != definition.expression_symbols
            || known.data_expression_symbols != definition.data_expression_symbols
            || known.generated_key != definition.generated_key
            || known.generated_display != definition.generated_display
        {
            return Err(EncodedValidationError::invariant(
                "equivalent generated class definitions disagree",
            ));
        }
        let node_count = definition
            .expressions
            .len()
            .checked_add(definition.roots.len())
            .ok_or_else(|| {
                EncodedValidationError::resource("generated definition node count overflowed")
            })?;
        budget.claim_owned(
            node_count
                .checked_mul(size_of::<NodeId>())
                .and_then(|value| value.checked_add(size_of::<[u8; 32]>()))
                .ok_or_else(|| {
                    EncodedValidationError::resource("generated definition ownership overflowed")
                })?,
        )?;
        known
            .expressions
            .try_reserve(definition.expressions.len())
            .map_err(|_| {
                EncodedValidationError::resource(
                    "generated definition expression allocation failed",
                )
            })?;
        known.expressions.append(&mut definition.expressions);
        known
            .roots
            .try_reserve(definition.roots.len())
            .map_err(|_| {
                EncodedValidationError::resource("generated definition root allocation failed")
            })?;
        known.roots.append(&mut definition.roots);
        known.provenance.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("generated definition provenance allocation failed")
        })?;
        known.provenance.push(provenance);
        return Ok(());
    }
    let following = definitions.len().checked_add(1).ok_or_else(|| {
        EncodedValidationError::resource("generated class definition count overflowed")
    })?;
    PhaseBudget::count(
        following,
        budget.limits.max_class_symbols,
        "generated class definition count",
    )?;
    budget.claim_owned(size_of::<ClassBooleanDefinition>() + size_of::<[u8; 32]>())?;
    definition.provenance.try_reserve(1).map_err(|_| {
        EncodedValidationError::resource("generated definition provenance allocation failed")
    })?;
    definition.provenance.push(provenance);
    definitions.try_reserve(1).map_err(|_| {
        EncodedValidationError::resource("generated class definition allocation failed")
    })?;
    definitions.push(definition);
    Ok(())
}

fn generated_class_symbol(
    namespace: [u8; 32],
    expression_key: &[u8],
    polarity: DefinitionPolarity,
    budget: &mut PhaseBudget,
) -> EncodedResult<(Vec<u8>, String)> {
    let namespace_hex = crate::model::hex(&namespace);
    let mut digest = Sha256::new();
    digest.update(DEFINITION_DIGEST_DOMAIN);
    digest.update(namespace_hex.as_bytes());
    digest.update(b"\0class\0");
    digest.update(polarity.as_str().as_bytes());
    digest.update(b"\0");
    digest.update(expression_key);
    budget.claim_work(
        DEFINITION_DIGEST_DOMAIN
            .len()
            .checked_add(namespace_hex.len())
            .and_then(|value| value.checked_add(b"\0class\0".len()))
            .and_then(|value| value.checked_add(polarity.as_str().len()))
            .and_then(|value| value.checked_add(1))
            .and_then(|value| value.checked_add(expression_key.len()))
            .ok_or_else(|| EncodedValidationError::resource("definition digest work overflowed"))?,
    )?;
    let digest_hex = crate::model::hex(&digest.finalize());
    let iri_len = GENERATED_CLASS_IRI_PREFIX
        .len()
        .checked_add(namespace_hex.len())
        .and_then(|value| value.checked_add(1))
        .and_then(|value| value.checked_add(polarity.as_str().len()))
        .and_then(|value| value.checked_add(1))
        .and_then(|value| value.checked_add(digest_hex.len()))
        .ok_or_else(|| EncodedValidationError::resource("generated class IRI overflowed"))?;
    budget.claim_owned(iri_len)?;
    let mut iri = String::new();
    iri.try_reserve_exact(iri_len)
        .map_err(|_| EncodedValidationError::resource("generated class IRI allocation failed"))?;
    iri.push_str(GENERATED_CLASS_IRI_PREFIX);
    iri.push_str(&namespace_hex);
    iri.push(':');
    iri.push_str(polarity.as_str());
    iri.push(':');
    iri.push_str(&digest_hex);
    let key = generated_class_entity_key(iri.as_bytes(), budget)?;
    let display_len = "class:"
        .len()
        .checked_add(iri.len())
        .ok_or_else(|| EncodedValidationError::resource("generated class display overflowed"))?;
    budget.claim_owned(display_len)?;
    let mut display = String::new();
    display.try_reserve_exact(display_len).map_err(|_| {
        EncodedValidationError::resource("generated class display allocation failed")
    })?;
    display.push_str("class:");
    display.push_str(&iri);
    Ok((key, display))
}

fn generated_class_entity_key(iri: &[u8], budget: &mut PhaseBudget) -> EncodedResult<Vec<u8>> {
    let mut iri_key = Vec::new();
    push_generated_varint(&mut iri_key, 1, budget)?;
    push_generated_byte(&mut iri_key, 2, budget)?;
    push_generated_frame(&mut iri_key, iri, budget)?;

    let mut key = Vec::new();
    push_generated_varint(&mut key, u64::from(ENTITY_TAG), budget)?;
    push_generated_byte(&mut key, 5, budget)?;
    push_generated_frame(&mut key, b"class", budget)?;
    push_generated_byte(&mut key, 1, budget)?;
    push_generated_frame(&mut key, &iri_key, budget)?;
    Ok(key)
}

fn generated_data_symbol(
    namespace: [u8; 32],
    expression_key: &[u8],
    polarity: DefinitionPolarity,
    budget: &mut PhaseBudget,
) -> EncodedResult<(Vec<u8>, String)> {
    let namespace_hex = crate::model::hex(&namespace);
    let mut digest = Sha256::new();
    digest.update(DEFINITION_DIGEST_DOMAIN);
    digest.update(namespace_hex.as_bytes());
    digest.update(b"\0data\0");
    digest.update(polarity.as_str().as_bytes());
    digest.update(b"\0");
    digest.update(expression_key);
    budget.claim_work(
        DEFINITION_DIGEST_DOMAIN
            .len()
            .checked_add(namespace_hex.len())
            .and_then(|value| value.checked_add(b"\0data\0".len()))
            .and_then(|value| value.checked_add(polarity.as_str().len()))
            .and_then(|value| value.checked_add(1))
            .and_then(|value| value.checked_add(expression_key.len()))
            .ok_or_else(|| {
                EncodedValidationError::resource("data definition digest work overflowed")
            })?,
    )?;
    let digest_hex = crate::model::hex(&digest.finalize());
    let iri_len = GENERATED_DATA_IRI_PREFIX
        .len()
        .checked_add(namespace_hex.len())
        .and_then(|value| value.checked_add(1))
        .and_then(|value| value.checked_add(polarity.as_str().len()))
        .and_then(|value| value.checked_add(1))
        .and_then(|value| value.checked_add(digest_hex.len()))
        .ok_or_else(|| EncodedValidationError::resource("generated data IRI overflowed"))?;
    budget.claim_owned(iri_len)?;
    let mut iri = String::new();
    iri.try_reserve_exact(iri_len)
        .map_err(|_| EncodedValidationError::resource("generated data IRI allocation failed"))?;
    iri.push_str(GENERATED_DATA_IRI_PREFIX);
    iri.push_str(&namespace_hex);
    iri.push(':');
    iri.push_str(polarity.as_str());
    iri.push(':');
    iri.push_str(&digest_hex);
    let key = generated_data_entity_key(iri.as_bytes(), budget)?;
    let display_len = "datatype:"
        .len()
        .checked_add(iri.len())
        .ok_or_else(|| EncodedValidationError::resource("generated data display overflowed"))?;
    budget.claim_owned(display_len)?;
    let mut display = String::new();
    display.try_reserve_exact(display_len).map_err(|_| {
        EncodedValidationError::resource("generated data display allocation failed")
    })?;
    display.push_str("datatype:");
    display.push_str(&iri);
    Ok((key, display))
}

fn generated_data_entity_key(iri: &[u8], budget: &mut PhaseBudget) -> EncodedResult<Vec<u8>> {
    let mut iri_key = Vec::new();
    push_generated_varint(&mut iri_key, 1, budget)?;
    push_generated_byte(&mut iri_key, 2, budget)?;
    push_generated_frame(&mut iri_key, iri, budget)?;

    let mut key = Vec::new();
    push_generated_varint(&mut key, u64::from(ENTITY_TAG), budget)?;
    push_generated_byte(&mut key, 5, budget)?;
    push_generated_frame(&mut key, b"datatype", budget)?;
    push_generated_byte(&mut key, 1, budget)?;
    push_generated_frame(&mut key, &iri_key, budget)?;
    Ok(key)
}

fn push_generated_frame(
    target: &mut Vec<u8>,
    value: &[u8],
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    push_generated_varint(
        target,
        u64::try_from(value.len())
            .map_err(|_| EncodedValidationError::resource("generated frame exceeds u64"))?,
        budget,
    )?;
    budget.claim_owned(value.len())?;
    target.try_reserve(value.len()).map_err(|_| {
        EncodedValidationError::resource("generated canonical frame allocation failed")
    })?;
    target.extend_from_slice(value);
    Ok(())
}

fn push_generated_varint(
    target: &mut Vec<u8>,
    mut value: u64,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    loop {
        let mut byte = u8::try_from(value & 0x7f)
            .map_err(|_| EncodedValidationError::invariant("generated varint chunk exceeds u8"))?;
        value >>= 7;
        if value != 0 {
            byte |= 0x80;
        }
        push_generated_byte(target, byte, budget)?;
        if value == 0 {
            return Ok(());
        }
    }
}

fn push_generated_byte(
    target: &mut Vec<u8>,
    value: u8,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    budget.claim_owned(1)?;
    target.try_reserve(1).map_err(|_| {
        EncodedValidationError::resource("generated canonical byte allocation failed")
    })?;
    target.push(value);
    Ok(())
}

fn phase_entity_domain(
    symbols: &SymbolPhase,
    class_definitions: &[ClassBooleanDefinition],
    data_definitions: &[DataBooleanDefinition],
    budget: &mut PhaseBudget,
) -> EncodedResult<(DecodedSymbolDomain, Vec<u32>)> {
    if symbols.entity_domain.kind != SymbolKind::Entity {
        return Err(EncodedValidationError::invariant(
            "generated definitions received a non-entity source domain",
        ));
    }
    let total = symbols
        .entity_domain
        .values
        .len()
        .checked_add(class_definitions.len())
        .and_then(|value| value.checked_add(data_definitions.len()))
        .ok_or_else(|| EncodedValidationError::resource("generated entity count overflowed"))?;
    PhaseBudget::count(
        total,
        budget.limits.max_entity_symbols,
        "entity symbol count",
    )?;
    let mut values = Vec::new();
    values.try_reserve_exact(total).map_err(|_| {
        EncodedValidationError::resource("generated entity domain allocation failed")
    })?;
    for value in &symbols.entity_domain.values {
        budget.claim_work(1)?;
        budget
            .claim_owned(size_of::<DecodedSymbolValue>() + value.key.len() + value.display.len())?;
        values.push(value.clone());
    }
    for definition in class_definitions {
        budget.claim_work(1)?;
        budget.claim_owned(
            size_of::<DecodedSymbolValue>()
                + definition.generated_key.len()
                + definition.generated_display.len(),
        )?;
        values.push(DecodedSymbolValue {
            identifier: 0,
            key: definition.generated_key.clone(),
            display: definition.generated_display.clone(),
            generated: true,
            query_local: false,
        });
    }
    for definition in data_definitions {
        budget.claim_work(1)?;
        budget.claim_owned(
            size_of::<DecodedSymbolValue>()
                + definition.generated_key.len()
                + definition.generated_display.len(),
        )?;
        values.push(DecodedSymbolValue {
            identifier: 0,
            key: definition.generated_key.clone(),
            display: definition.generated_display.clone(),
            generated: true,
            query_local: false,
        });
    }
    budget.claim_work(sort_work(values.len()))?;
    values.sort_by(|left, right| left.key.cmp(&right.key));
    let mut frozen = Vec::<DecodedSymbolValue>::new();
    frozen.try_reserve_exact(values.len()).map_err(|_| {
        EncodedValidationError::resource("generated entity result allocation failed")
    })?;
    for mut candidate in values {
        if let Some(previous) = frozen.last() {
            if previous.key == candidate.key {
                if previous.display != candidate.display
                    || previous.generated != candidate.generated
                    || previous.query_local != candidate.query_local
                {
                    return Err(EncodedValidationError::invariant(
                        "generated entity collides with the source signature",
                    ));
                }
                continue;
            }
        }
        candidate.identifier = u32::try_from(frozen.len())
            .map_err(|_| EncodedValidationError::resource("generated entity ID exceeds u32"))?;
        frozen.push(candidate);
    }
    let mut source_map = Vec::new();
    budget.claim_owned(
        symbols
            .entity_domain
            .values
            .len()
            .checked_mul(size_of::<u32>())
            .ok_or_else(|| EncodedValidationError::resource("source entity map overflowed"))?,
    )?;
    source_map
        .try_reserve_exact(symbols.entity_domain.values.len())
        .map_err(|_| EncodedValidationError::resource("source entity map allocation failed"))?;
    for value in &symbols.entity_domain.values {
        budget.claim_work(binary_search_work(frozen.len()))?;
        let index = frozen
            .binary_search_by(|candidate| candidate.key.cmp(&value.key))
            .map_err(|_| EncodedValidationError::invariant("source entity disappeared"))?;
        source_map.push(
            u32::try_from(index)
                .map_err(|_| EncodedValidationError::resource("source entity map exceeds u32"))?,
        );
    }
    Ok((
        DecodedSymbolDomain {
            kind: SymbolKind::Entity,
            values: frozen,
        },
        source_map,
    ))
}

fn class_boolean_definition(
    definitions: &[ClassBooleanDefinition],
    expression: NodeId,
    polarity: DefinitionPolarity,
) -> Option<&ClassBooleanDefinition> {
    definitions.iter().find(|definition| {
        definition.polarity == polarity && definition.expressions.binary_search(&expression).is_ok()
    })
}

fn class_boolean_definition_for_root(
    definitions: &[ClassBooleanDefinition],
    root: NodeId,
    polarity: DefinitionPolarity,
) -> Option<&ClassBooleanDefinition> {
    definitions.iter().find(|definition| {
        definition.polarity == polarity && definition.roots.binary_search(&root).is_ok()
    })
}

fn data_boolean_definition(
    definitions: &[DataBooleanDefinition],
    expression: NodeId,
    polarity: DefinitionPolarity,
) -> Option<&DataBooleanDefinition> {
    definitions.iter().find(|definition| {
        definition.polarity == polarity && definition.expressions.binary_search(&expression).is_ok()
    })
}

fn datatype_boolean_definition_for_root(
    definitions: &[DatatypeBooleanDefinition],
    root: NodeId,
) -> Option<&DatatypeBooleanDefinition> {
    definitions
        .binary_search_by_key(&root, |definition| definition.root)
        .ok()
        .map(|index| &definitions[index])
}

fn push_class_boolean_definition_selections(
    expressions: &mut Vec<NodeId>,
    definition: &ClassBooleanDefinition,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    for operand in &definition.operands {
        if let ClassBooleanOperand::Atomic(AtomicClassSelection {
            source: AtomicClassSource::Nominal(base),
            ..
        }) = operand
        {
            push_class_expression_selection(expressions, *base, budget)?;
        }
    }
    Ok(())
}

fn push_seeded_class_expression_symbol(
    target: &mut Vec<PendingClassSymbol>,
    seed: &ClassExpressionSymbolSeed,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    let following = target.len().checked_add(1).ok_or_else(|| {
        EncodedValidationError::resource("seeded class-expression symbol count overflowed")
    })?;
    PhaseBudget::count(
        following,
        budget.limits.max_class_symbols,
        "class-expression symbol count",
    )?;
    budget.claim_owned(
        size_of::<PendingClassSymbol>()
            .checked_add(size_of::<DecodedSymbolValue>())
            .and_then(|value| value.checked_add(seed.key.len()))
            .and_then(|value| value.checked_add(seed.display.len()))
            .ok_or_else(|| {
                EncodedValidationError::resource(
                    "seeded class-expression symbol ownership overflowed",
                )
            })?,
    )?;
    target.try_reserve(1).map_err(|_| {
        EncodedValidationError::resource("seeded class-expression symbol allocation failed")
    })?;
    target.push(PendingClassSymbol {
        value: DecodedSymbolValue {
            identifier: 0,
            key: seed.key.clone(),
            display: seed.display.clone(),
            generated: false,
            query_local: false,
        },
        entity: None,
    });
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn class_signature<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    declared_class_ids: &[u32],
    has_object_roles: bool,
    has_data_roles: bool,
    scope_maps: &[AnonymousScopeMap],
    definitions: &[ClassBooleanDefinition],
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

    for definition in definitions {
        for seed in &definition.expression_symbols {
            push_seeded_class_expression_symbol(&mut pending, seed, budget)?;
        }
    }

    let mut selected_expressions = Vec::<NodeId>::new();
    for definition in definitions {
        push_class_boolean_definition_selections(&mut selected_expressions, definition, budget)?;
    }
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
                } else if let Some(definition) =
                    class_boolean_definition(definitions, expression, DefinitionPolarity::Positive)
                {
                    push_class_boolean_definition_selections(
                        &mut selected_expressions,
                        definition,
                        budget,
                    )?;
                }
            }
            RootHandler::SubClassOf => {
                let sub_class = node_field(model, root_node, 0, "subclass antecedent")?;
                let super_class = node_field(model, root_node, 1, "subclass consequent")?;
                let sub_selection = atomic_class_selection(model, symbols, sub_class, budget)?;
                let super_selection = atomic_class_selection(model, symbols, super_class, budget)?;
                let sub_definition =
                    class_boolean_definition(definitions, sub_class, DefinitionPolarity::Negative);
                let super_definition = class_boolean_definition(
                    definitions,
                    super_class,
                    DefinitionPolarity::Positive,
                );
                if (sub_selection.is_none() && sub_definition.is_none())
                    || (super_selection.is_none() && super_definition.is_none())
                {
                    continue;
                }
                if let (Some(sub_selection), Some(super_selection)) =
                    (sub_selection, super_selection)
                {
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
                }
                if let Some(selection) = sub_selection {
                    push_atomic_class_selection(&mut selected_expressions, selection, budget)?;
                }
                if let Some(definition) = sub_definition {
                    push_class_boolean_definition_selections(
                        &mut selected_expressions,
                        definition,
                        budget,
                    )?;
                }
                if let Some(selection) = super_selection {
                    push_atomic_class_selection(&mut selected_expressions, selection, budget)?;
                }
                if let Some(definition) = super_definition {
                    push_class_boolean_definition_selections(
                        &mut selected_expressions,
                        definition,
                        budget,
                    )?;
                }
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
                    let selection = atomic_class_selection(model, symbols, identifier, budget)?;
                    let negative = class_boolean_definition(
                        definitions,
                        identifier,
                        DefinitionPolarity::Negative,
                    );
                    let positive = class_boolean_definition(
                        definitions,
                        identifier,
                        DefinitionPolarity::Positive,
                    );
                    if selection.is_none() && (negative.is_none() || positive.is_none()) {
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
                    } else {
                        for polarity in [DefinitionPolarity::Negative, DefinitionPolarity::Positive]
                        {
                            let definition =
                                class_boolean_definition(definitions, identifier, polarity)
                                    .ok_or_else(|| {
                                        EncodedValidationError::invariant(
                                            "validated equivalent Boolean definition disappeared",
                                        )
                                    })?;
                            push_class_boolean_definition_selections(
                                &mut selected_expressions,
                                definition,
                                budget,
                            )?;
                        }
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
                    if let Some(selection) =
                        atomic_class_selection(model, symbols, identifier, budget)?
                    {
                        if matches!(selection.source, AtomicClassSource::Entity(entity_id)
                            if !selection.negative
                                && class_entity_display(symbols, entity_id)? == NOTHING_DISPLAY)
                        {
                            continue;
                        }
                    } else if class_boolean_definition(
                        definitions,
                        identifier,
                        DefinitionPolarity::Negative,
                    )
                    .is_none()
                    {
                        continue 'root_selection;
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
            RootHandler::DisjointUnion => {
                if root_node.field_count() != 3 {
                    return Err(EncodedValidationError::invariant(
                        "disjoint-union root no longer has schema-1 shape",
                    ));
                }
                let defined = node_field(model, root_node, 0, "disjoint-union defined class")?;
                let Some(defined_selection) =
                    atomic_class_selection(model, symbols, defined, budget)?
                else {
                    continue;
                };
                let expressions_component = required_component(
                    model.field(root_node.fields().start + 1)?,
                    "disjoint-union expressions",
                )?;
                let ComponentValue::Collection(expressions) =
                    model.resolve(expressions_component)?
                else {
                    return Err(EncodedValidationError::invariant(
                        "disjoint-union expressions did not resolve to a collection",
                    ));
                };
                let reducible = reducible_class_boolean_operands(
                    model,
                    symbols,
                    expressions,
                    false,
                    0,
                    budget,
                )?
                .is_some();
                let generated = class_boolean_definition_for_root(
                    definitions,
                    root.node,
                    DefinitionPolarity::Positive,
                )
                .is_some();
                if !reducible && !generated {
                    continue;
                }
                push_atomic_class_selection(&mut selected_expressions, defined_selection, budget)?;
                for item_index in expressions.items() {
                    budget.claim_work(1)?;
                    let item =
                        required_component(model.item(item_index)?, "disjoint-union member")?;
                    let ComponentValue::Node(identifier) = model.resolve(item)? else {
                        return Err(EncodedValidationError::invariant(
                            "disjoint-union member did not resolve to a node",
                        ));
                    };
                    if let Some(selection) =
                        atomic_class_selection(model, symbols, identifier, budget)?
                    {
                        push_atomic_class_selection(&mut selected_expressions, selection, budget)?;
                    } else if class_boolean_definition(
                        definitions,
                        identifier,
                        DefinitionPolarity::Negative,
                    )
                    .is_none()
                    {
                        continue 'root_selection;
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
                } else if let Some(definition) =
                    class_boolean_definition(definitions, expression, DefinitionPolarity::Positive)
                {
                    push_class_boolean_definition_selections(
                        &mut selected_expressions,
                        definition,
                        budget,
                    )?;
                }
            }
            RootHandler::DataPropertyDomain if has_data_roles => {
                let expression =
                    node_field(model, root_node, 1, "data-property domain class expression")?;
                if let Some(selection) = atomic_class_selection(model, symbols, expression, budget)?
                {
                    push_atomic_class_selection(&mut selected_expressions, selection, budget)?;
                } else if let Some(definition) =
                    class_boolean_definition(definitions, expression, DefinitionPolarity::Positive)
                {
                    push_class_boolean_definition_selections(
                        &mut selected_expressions,
                        definition,
                        budget,
                    )?;
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
                } else if let Some(definition) =
                    class_boolean_definition(definitions, expression, DefinitionPolarity::Negative)
                {
                    push_class_boolean_definition_selections(
                        &mut selected_expressions,
                        definition,
                        budget,
                    )?;
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

    for definition in definitions {
        if definition.expressions.is_empty() && definition.expression_symbols.is_empty() {
            if definition.roots.is_empty() {
                return Err(EncodedValidationError::invariant(
                    "synthetic class definition lost its owning root",
                ));
            }
            let following = pending.len().checked_add(1).ok_or_else(|| {
                EncodedValidationError::resource("synthetic class symbol count overflowed")
            })?;
            PhaseBudget::count(
                following,
                budget.limits.max_class_symbols,
                "synthetic class symbol count",
            )?;
            budget.claim_work(definition.expression_key.len())?;
            let digest = crate::model::hex(&Sha256::digest(&definition.expression_key));
            let prefix = if definition.intersection {
                "ObjectIntersectionOf:"
            } else {
                "ObjectUnionOf:"
            };
            let display_len = prefix.len().checked_add(digest.len()).ok_or_else(|| {
                EncodedValidationError::resource("synthetic class display length overflowed")
            })?;
            budget.claim_owned(
                size_of::<PendingClassSymbol>()
                    .checked_add(size_of::<DecodedSymbolValue>())
                    .and_then(|value| value.checked_add(definition.expression_key.len()))
                    .and_then(|value| value.checked_add(display_len))
                    .ok_or_else(|| {
                        EncodedValidationError::resource(
                            "synthetic class symbol ownership overflowed",
                        )
                    })?,
            )?;
            let mut display = String::new();
            display.try_reserve_exact(display_len).map_err(|_| {
                EncodedValidationError::resource("synthetic class display allocation failed")
            })?;
            display.push_str(prefix);
            display.push_str(&digest);
            pending.try_reserve(1).map_err(|_| {
                EncodedValidationError::resource("synthetic class symbol allocation failed")
            })?;
            pending.push(PendingClassSymbol {
                value: DecodedSymbolValue {
                    identifier: 0,
                    key: definition.expression_key.clone(),
                    display,
                    generated: false,
                    query_local: false,
                },
                entity: None,
            });
        }
        let following = pending.len().checked_add(1).ok_or_else(|| {
            EncodedValidationError::resource("generated class symbol count overflowed")
        })?;
        PhaseBudget::count(
            following,
            budget.limits.max_class_symbols,
            "generated class symbol count",
        )?;
        budget.claim_owned(size_of::<PendingClassSymbol>())?;
        budget.claim_owned(size_of::<DecodedSymbolValue>())?;
        budget.claim_owned(definition.generated_key.len())?;
        budget.claim_owned(definition.generated_display.len())?;
        pending.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("generated class symbol allocation failed")
        })?;
        pending.push(PendingClassSymbol {
            value: DecodedSymbolValue {
                identifier: 0,
                key: definition.generated_key.clone(),
                display: definition.generated_display.clone(),
                generated: true,
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
        OBJECT_INTERSECTION_OF_TAG => Ok("ObjectIntersectionOf:"),
        OBJECT_UNION_OF_TAG => Ok("ObjectUnionOf:"),
        OBJECT_ONE_OF_TAG => Ok("ObjectOneOf:"),
        OBJECT_COMPLEMENT_OF_TAG => Ok("ObjectComplementOf:"),
        OBJECT_SOME_VALUES_FROM_TAG => Ok("ObjectSomeValuesFrom:"),
        OBJECT_ALL_VALUES_FROM_TAG => Ok("ObjectAllValuesFrom:"),
        OBJECT_HAS_SELF_TAG => Ok("ObjectHasSelf:"),
        OBJECT_MIN_CARDINALITY_TAG => Ok("ObjectMinCardinality:"),
        OBJECT_MAX_CARDINALITY_TAG => Ok("ObjectMaxCardinality:"),
        OBJECT_EXACT_CARDINALITY_TAG => Ok("ObjectExactCardinality:"),
        DATA_SOME_VALUES_FROM_TAG => Ok("DataSomeValuesFrom:"),
        DATA_ALL_VALUES_FROM_TAG => Ok("DataAllValuesFrom:"),
        DATA_MIN_CARDINALITY_TAG => Ok("DataMinCardinality:"),
        DATA_MAX_CARDINALITY_TAG => Ok("DataMaxCardinality:"),
        DATA_EXACT_CARDINALITY_TAG => Ok("DataExactCardinality:"),
        _ => Err(EncodedValidationError::invariant(
            "selected class expression has an unsupported constructor",
        )),
    }
}

fn published_class_signature(
    source: &[ClassSignatureBinding],
    class_domain: &DecodedSymbolDomain,
    entity_domain: &DecodedSymbolDomain,
    source_entity_map: &[u32],
    definitions: &[ClassBooleanDefinition],
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<ClassSignatureBinding>> {
    let following = source
        .len()
        .checked_add(definitions.len())
        .ok_or_else(|| EncodedValidationError::resource("published class signature overflowed"))?;
    budget.claim_owned(
        following
            .checked_mul(size_of::<ClassSignatureBinding>())
            .ok_or_else(|| {
                EncodedValidationError::resource("published class signature bytes overflowed")
            })?,
    )?;
    let mut published = Vec::new();
    published.try_reserve_exact(following).map_err(|_| {
        EncodedValidationError::resource("published class signature allocation failed")
    })?;
    for binding in source {
        published.push(ClassSignatureBinding {
            class_expression_id: binding.class_expression_id,
            entity_id: mapped_id(source_entity_map, binding.entity_id, "source class entity")?,
            declared: binding.declared,
        });
    }
    for definition in definitions {
        budget.claim_work(binary_search_work(class_domain.values.len()))?;
        let class_index = class_domain
            .values
            .binary_search_by(|candidate| candidate.key.cmp(&definition.generated_key))
            .map_err(|_| EncodedValidationError::invariant("generated class symbol disappeared"))?;
        budget.claim_work(binary_search_work(entity_domain.values.len()))?;
        let entity_index = entity_domain
            .values
            .binary_search_by(|candidate| candidate.key.cmp(&definition.generated_key))
            .map_err(|_| EncodedValidationError::invariant("generated class entity disappeared"))?;
        published.push(ClassSignatureBinding {
            class_expression_id: u32::try_from(class_index).map_err(|_| {
                EncodedValidationError::resource("generated class symbol ID exceeds u32")
            })?,
            entity_id: u32::try_from(entity_index).map_err(|_| {
                EncodedValidationError::resource("generated class entity ID exceeds u32")
            })?,
            declared: false,
        });
    }
    budget.claim_work(sort_work(published.len()))?;
    published.sort_by_key(|binding| binding.class_expression_id);
    if published
        .windows(2)
        .any(|pair| pair[0].class_expression_id == pair[1].class_expression_id)
    {
        return Err(EncodedValidationError::invariant(
            "published class signature contains duplicate symbols",
        ));
    }
    Ok(published)
}

fn published_individual_signature(
    source: &[IndividualSignatureBinding],
    source_entity_map: &[u32],
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<IndividualSignatureBinding>> {
    budget.claim_owned(
        source
            .len()
            .checked_mul(size_of::<IndividualSignatureBinding>())
            .ok_or_else(|| {
                EncodedValidationError::resource("published individual signature overflowed")
            })?,
    )?;
    let mut published = Vec::new();
    published.try_reserve_exact(source.len()).map_err(|_| {
        EncodedValidationError::resource("published individual signature allocation failed")
    })?;
    for binding in source {
        published.push(IndividualSignatureBinding {
            individual_id: binding.individual_id,
            entity_id: mapped_id(
                source_entity_map,
                binding.entity_id,
                "source individual entity",
            )?,
            declared: binding.declared,
        });
    }
    Ok(published)
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

fn named_nominal_entity_ids<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    identifier: NodeId,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<u32>> {
    let node = model.node(identifier)?;
    if node.tag() != OBJECT_ONE_OF_TAG || node.field_count() != 1 {
        return Err(EncodedValidationError::invariant(
            "selected object nominal no longer has schema-1 shape",
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
    budget.claim_owned(
        individuals
            .len()
            .checked_mul(size_of::<u32>())
            .ok_or_else(|| {
                EncodedValidationError::resource("selected object nominal entity IDs overflowed")
            })?,
    )?;
    let mut entity_ids = Vec::new();
    entity_ids
        .try_reserve_exact(individuals.len())
        .map_err(|_| {
            EncodedValidationError::resource("selected object nominal entity ID allocation failed")
        })?;
    for item_index in individuals.items() {
        budget.claim_work(1)?;
        let item = required_component(model.item(item_index)?, "selected object nominal member")?;
        let ComponentValue::Node(individual) = model.resolve(item)? else {
            return Err(EncodedValidationError::invariant(
                "selected object nominal member changed shape",
            ));
        };
        if model.node(individual)?.tag() != ENTITY_TAG {
            return Err(EncodedValidationError::invariant(
                "selected object nominal contains a non-named individual",
            ));
        }
        let entity_id = symbols.entity_symbol_for_node(individual).ok_or_else(|| {
            EncodedValidationError::invariant(
                "selected object nominal member is absent from the reachable entity mapping",
            )
        })?;
        let entity = symbols
            .entity_domain
            .values
            .get(usize::try_from(entity_id).unwrap_or(usize::MAX))
            .ok_or_else(|| {
                EncodedValidationError::invariant(
                    "selected object nominal member entity ID is dangling",
                )
            })?;
        if !entity.display.starts_with(NAMED_INDIVIDUAL_PREFIX) {
            return Err(EncodedValidationError::invariant(
                "selected object nominal member changed entity kind",
            ));
        }
        entity_ids.push(entity_id);
    }
    if entity_ids.is_empty() || !entity_ids.windows(2).all(|pair| pair[0] < pair[1]) {
        return Err(EncodedValidationError::invariant(
            "selected object nominal entity IDs are not canonical",
        ));
    }
    Ok(entity_ids)
}

fn atomic_class_selection<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    identifier: NodeId,
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<AtomicClassSelection>> {
    atomic_class_selection_at_depth(model, symbols, identifier, 0, budget)
}

fn atomic_class_selection_at_depth<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    identifier: NodeId,
    initial_depth: usize,
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<AtomicClassSelection>> {
    let mut base = identifier;
    let mut negative = false;
    let mut normalized_complement = None;
    let mut depth = initial_depth;
    PhaseBudget::count(
        depth,
        budget.limits.max_canonical_depth,
        "class-expression depth",
    )?;
    loop {
        let node = model.node(base)?;
        if node.tag() != OBJECT_COMPLEMENT_OF_TAG {
            break;
        }
        if node.field_count() != 1 {
            return Err(EncodedValidationError::invariant(
                "class complement no longer has schema-1 shape",
            ));
        }
        depth = depth
            .checked_add(1)
            .ok_or_else(|| EncodedValidationError::resource("class-complement depth overflowed"))?;
        PhaseBudget::count(
            depth,
            budget.limits.max_canonical_depth,
            "class-expression depth",
        )?;
        budget.claim_work(1)?;
        normalized_complement = Some(base);
        base = node_field(model, node, 0, "class-complement operand")?;
        negative = !negative;
    }

    let base_node = model.node(base)?;
    let base_is_atomic = matches!(base_node.tag(), ENTITY_TAG | OBJECT_ONE_OF_TAG);
    let Some(selection) = positive_atomic_class_selection(model, symbols, base, depth, budget)?
    else {
        return Ok(None);
    };
    if !negative {
        return Ok(Some(selection));
    }
    complement_atomic_class_selection(
        model,
        symbols,
        selection,
        normalized_complement.unwrap_or(identifier),
        base_is_atomic,
    )
}

fn positive_atomic_class_selection<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    identifier: NodeId,
    depth: usize,
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<AtomicClassSelection>> {
    let node = model.node(identifier)?;
    if node.tag() == ENTITY_TAG {
        let entity_id = symbols.entity_symbol_for_node(identifier).ok_or_else(|| {
            EncodedValidationError::invariant(
                "atomic class is absent from the reachable entity mapping",
            )
        })?;
        let display = class_entity_display(symbols, entity_id)?;
        if !display.starts_with("class:") {
            return Ok(None);
        }
        return Ok(Some(AtomicClassSelection {
            source: AtomicClassSource::Entity(entity_id),
            expression: identifier,
            negative: false,
        }));
    }
    if node.tag() == OBJECT_ONE_OF_TAG {
        if !is_named_nominal(model, symbols, identifier, budget)? {
            return Ok(None);
        }
        return Ok(Some(AtomicClassSelection {
            source: AtomicClassSource::Nominal(identifier),
            expression: identifier,
            negative: false,
        }));
    }
    match node.tag() {
        OBJECT_SOME_VALUES_FROM_TAG | OBJECT_ALL_VALUES_FROM_TAG => {
            return reducible_object_quantifier_selection(model, symbols, node, depth, budget);
        }
        OBJECT_HAS_VALUE_TAG | OBJECT_HAS_SELF_TAG => {
            return reducible_object_value_selection(model, symbols, node, depth, budget);
        }
        OBJECT_MIN_CARDINALITY_TAG | OBJECT_MAX_CARDINALITY_TAG | OBJECT_EXACT_CARDINALITY_TAG => {
            return reducible_object_cardinality_selection(model, symbols, node, depth, budget);
        }
        DATA_SOME_VALUES_FROM_TAG | DATA_ALL_VALUES_FROM_TAG => {
            return reducible_data_quantifier_selection(model, symbols, node, depth, budget);
        }
        DATA_HAS_VALUE_TAG => {
            return reducible_data_has_value_selection(model, symbols, node, depth, budget);
        }
        DATA_MIN_CARDINALITY_TAG | DATA_MAX_CARDINALITY_TAG | DATA_EXACT_CARDINALITY_TAG => {
            return reducible_data_cardinality_selection(model, symbols, node, depth, budget);
        }
        _ => {}
    }
    if !matches!(node.tag(), OBJECT_INTERSECTION_OF_TAG | OBJECT_UNION_OF_TAG) {
        return Ok(None);
    }
    if node.field_count() != 1 {
        return Err(EncodedValidationError::invariant(
            "class Boolean expression no longer has schema-1 shape",
        ));
    }
    let component =
        required_component(model.field(node.fields().start)?, "class Boolean operands")?;
    let ComponentValue::Collection(operands) = model.resolve(component)? else {
        return Err(EncodedValidationError::invariant(
            "class Boolean operands did not resolve to a collection",
        ));
    };
    reducible_class_boolean_operands(
        model,
        symbols,
        operands,
        node.tag() == OBJECT_INTERSECTION_OF_TAG,
        depth,
        budget,
    )
}

fn reducible_class_boolean_operands<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    operands: CollectionRef,
    intersection: bool,
    depth: usize,
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<AtomicClassSelection>> {
    let operand_depth = child_expression_depth(depth, "class-expression depth overflowed")?;
    PhaseBudget::count(
        operand_depth,
        budget.limits.max_canonical_depth,
        "class-expression depth",
    )?;
    let mut absorbing = None;
    let mut retained = None;
    let mut identity = None;
    for item_index in operands.items() {
        budget.claim_work(1)?;
        let item = required_component(model.item(item_index)?, "class Boolean operand")?;
        let ComponentValue::Node(operand) = model.resolve(item)? else {
            return Err(EncodedValidationError::invariant(
                "class Boolean operand did not resolve to a node",
            ));
        };
        let Some(selection) =
            atomic_class_selection_at_depth(model, symbols, operand, operand_depth, budget)?
        else {
            return Ok(None);
        };
        let is_thing = atomic_class_selection_has_display(symbols, selection, THING_DISPLAY)?;
        let is_nothing = atomic_class_selection_has_display(symbols, selection, NOTHING_DISPLAY)?;
        if (intersection && is_nothing) || (!intersection && is_thing) {
            absorbing.get_or_insert(selection);
            continue;
        }
        if absorbing.is_some() {
            continue;
        }
        if (intersection && is_thing) || (!intersection && is_nothing) {
            identity.get_or_insert(selection);
            continue;
        }
        if retained.is_some_and(|known| atomic_class_selections_match(known, selection)) {
            continue;
        }
        if retained.is_some() {
            return Ok(None);
        }
        retained = Some(selection);
    }
    Ok(absorbing.or(retained).or(identity))
}

fn reducible_object_quantifier_selection<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    node: NodeRef,
    depth: usize,
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<AtomicClassSelection>> {
    if node.field_count() != 2 {
        return Err(EncodedValidationError::invariant(
            "object quantifier no longer has schema-1 shape",
        ));
    }
    if !reduction_inputs_are_retained(model, symbols, node.id(), depth, budget)? {
        return Ok(None);
    }
    let some = node.tag() == OBJECT_SOME_VALUES_FROM_TAG;
    let property = node_field(model, node, 0, "object quantifier property")?;
    if object_property_has_iri(model, symbols, property, BOTTOM_OBJECT_IRI)? {
        return builtin_atomic_class_selection(
            symbols,
            node.id(),
            if some { NOTHING_DISPLAY } else { THING_DISPLAY },
        )
        .map(Some);
    }
    let filler = node_field(model, node, 1, "object quantifier filler")?;
    let filler_depth = child_expression_depth(depth, "object quantifier filler depth overflowed")?;
    let Some(selection) =
        atomic_class_selection_at_depth(model, symbols, filler, filler_depth, budget)?
    else {
        return Ok(None);
    };
    if (some && atomic_class_selection_has_display(symbols, selection, NOTHING_DISPLAY)?)
        || (!some && atomic_class_selection_has_display(symbols, selection, THING_DISPLAY)?)
    {
        return Ok(Some(selection));
    }
    Ok(None)
}

fn reducible_object_value_selection<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    node: NodeRef,
    depth: usize,
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<AtomicClassSelection>> {
    let expected_fields = if node.tag() == OBJECT_HAS_VALUE_TAG {
        2
    } else {
        1
    };
    if node.field_count() != expected_fields {
        return Err(EncodedValidationError::invariant(
            "object value restriction no longer has schema-1 shape",
        ));
    }
    if !reduction_inputs_are_retained(model, symbols, node.id(), depth, budget)? {
        return Ok(None);
    }
    let property = node_field(model, node, 0, "object value-restriction property")?;
    if object_property_has_iri(model, symbols, property, BOTTOM_OBJECT_IRI)? {
        return builtin_atomic_class_selection(symbols, node.id(), NOTHING_DISPLAY).map(Some);
    }
    if node.tag() == OBJECT_HAS_SELF_TAG
        && object_property_has_iri(model, symbols, property, TOP_OBJECT_IRI)?
    {
        return builtin_atomic_class_selection(symbols, node.id(), THING_DISPLAY).map(Some);
    }
    budget.claim_work(1)?;
    Ok(None)
}

fn reducible_object_cardinality_selection<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    node: NodeRef,
    depth: usize,
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<AtomicClassSelection>> {
    if node.field_count() != 3 {
        return Err(EncodedValidationError::invariant(
            "object cardinality no longer has schema-1 shape",
        ));
    }
    if !reduction_inputs_are_retained(model, symbols, node.id(), depth, budget)? {
        return Ok(None);
    }
    let zero = integer_field_is_zero(model, node, 0, "object cardinality value")?;
    let property = node_field(model, node, 1, "object cardinality property")?;
    let bottom_property = object_property_has_iri(model, symbols, property, BOTTOM_OBJECT_IRI)?;
    if node.tag() == OBJECT_MIN_CARDINALITY_TAG && zero {
        return builtin_atomic_class_selection(symbols, node.id(), THING_DISPLAY).map(Some);
    }
    if bottom_property {
        let display = if node.tag() == OBJECT_MIN_CARDINALITY_TAG
            || (node.tag() == OBJECT_EXACT_CARDINALITY_TAG && !zero)
        {
            NOTHING_DISPLAY
        } else {
            THING_DISPLAY
        };
        return builtin_atomic_class_selection(symbols, node.id(), display).map(Some);
    }
    let filler = node_field(model, node, 2, "object cardinality filler")?;
    let filler_depth = child_expression_depth(depth, "object cardinality depth overflowed")?;
    let Some(selection) =
        atomic_class_selection_at_depth(model, symbols, filler, filler_depth, budget)?
    else {
        return Ok(None);
    };
    if !atomic_class_selection_has_display(symbols, selection, NOTHING_DISPLAY)? {
        return Ok(None);
    }
    let display = if node.tag() == OBJECT_MAX_CARDINALITY_TAG
        || (node.tag() == OBJECT_EXACT_CARDINALITY_TAG && zero)
    {
        THING_DISPLAY
    } else {
        NOTHING_DISPLAY
    };
    builtin_atomic_class_selection(symbols, node.id(), display).map(Some)
}

fn reducible_data_quantifier_selection<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    node: NodeRef,
    depth: usize,
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<AtomicClassSelection>> {
    if node.field_count() != 2 {
        return Err(EncodedValidationError::invariant(
            "data quantifier no longer has schema-1 shape",
        ));
    }
    if !reduction_inputs_are_retained(model, symbols, node.id(), depth, budget)? {
        return Ok(None);
    }
    let some = node.tag() == DATA_SOME_VALUES_FROM_TAG;
    if data_property_collection_has_iri(model, symbols, node, 0, BOTTOM_DATA_IRI, budget)? {
        return builtin_atomic_class_selection(
            symbols,
            node.id(),
            if some { NOTHING_DISPLAY } else { THING_DISPLAY },
        )
        .map(Some);
    }
    let filler = node_field(model, node, 1, "data quantifier filler")?;
    let filler_depth = child_expression_depth(depth, "data quantifier filler depth overflowed")?;
    let Some(selection) =
        atomic_data_range_selection_at_depth(model, symbols, filler, filler_depth, budget)?
    else {
        return Ok(None);
    };
    if (some && atomic_data_range_selection_is_bottom(model, symbols, selection)?)
        || (!some && atomic_data_range_selection_is_top(model, symbols, selection)?)
    {
        return builtin_atomic_class_selection(
            symbols,
            node.id(),
            if some { NOTHING_DISPLAY } else { THING_DISPLAY },
        )
        .map(Some);
    }
    Ok(None)
}

fn reducible_data_has_value_selection<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    node: NodeRef,
    depth: usize,
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<AtomicClassSelection>> {
    if node.field_count() != 2 {
        return Err(EncodedValidationError::invariant(
            "data has-value restriction no longer has schema-1 shape",
        ));
    }
    if !reduction_inputs_are_retained(model, symbols, node.id(), depth, budget)? {
        return Ok(None);
    }
    let property = node_field(model, node, 0, "data has-value property")?;
    if data_property_has_iri(model, symbols, property, BOTTOM_DATA_IRI)? {
        return builtin_atomic_class_selection(symbols, node.id(), NOTHING_DISPLAY).map(Some);
    }
    budget.claim_work(1)?;
    Ok(None)
}

fn reducible_data_cardinality_selection<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    node: NodeRef,
    depth: usize,
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<AtomicClassSelection>> {
    if node.field_count() != 3 {
        return Err(EncodedValidationError::invariant(
            "data cardinality no longer has schema-1 shape",
        ));
    }
    if !reduction_inputs_are_retained(model, symbols, node.id(), depth, budget)? {
        return Ok(None);
    }
    let zero = integer_field_is_zero(model, node, 0, "data cardinality value")?;
    let property = node_field(model, node, 1, "data cardinality property")?;
    let bottom_property = data_property_has_iri(model, symbols, property, BOTTOM_DATA_IRI)?;
    if node.tag() == DATA_MIN_CARDINALITY_TAG && zero {
        return builtin_atomic_class_selection(symbols, node.id(), THING_DISPLAY).map(Some);
    }
    if bottom_property {
        let display = if node.tag() == DATA_MIN_CARDINALITY_TAG
            || (node.tag() == DATA_EXACT_CARDINALITY_TAG && !zero)
        {
            NOTHING_DISPLAY
        } else {
            THING_DISPLAY
        };
        return builtin_atomic_class_selection(symbols, node.id(), display).map(Some);
    }
    let filler = node_field(model, node, 2, "data cardinality filler")?;
    let filler_depth = child_expression_depth(depth, "data cardinality depth overflowed")?;
    let Some(selection) =
        atomic_data_range_selection_at_depth(model, symbols, filler, filler_depth, budget)?
    else {
        return Ok(None);
    };
    if !atomic_data_range_selection_is_bottom(model, symbols, selection)? {
        return Ok(None);
    }
    let display = if node.tag() == DATA_MAX_CARDINALITY_TAG
        || (node.tag() == DATA_EXACT_CARDINALITY_TAG && zero)
    {
        THING_DISPLAY
    } else {
        NOTHING_DISPLAY
    };
    builtin_atomic_class_selection(symbols, node.id(), display).map(Some)
}

fn reduction_inputs_are_retained<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    identifier: NodeId,
    depth: usize,
    budget: &mut PhaseBudget,
) -> EncodedResult<bool> {
    PhaseBudget::count(
        depth,
        budget.limits.max_canonical_depth,
        "reducible-expression depth",
    )?;
    budget.claim_work(1)?;
    let node = model.node(identifier)?;
    if node.tag() == ENTITY_TAG {
        let entity_id = symbols.entity_symbol_for_node(identifier).ok_or_else(|| {
            EncodedValidationError::invariant(
                "reducible expression entity is absent from the reachable mapping",
            )
        })?;
        return reduction_entity_is_retained(symbols, entity_id);
    }
    if matches!(node.tag(), ANONYMOUS_INDIVIDUAL_TAG | LITERAL_TAG) {
        return Ok(false);
    }
    let child_depth = child_expression_depth(depth, "reducible-expression depth overflowed")?;
    for field_index in node.fields() {
        budget.claim_work(1)?;
        let component =
            required_component(model.field(field_index)?, "reducible-expression field")?;
        match model.resolve(component)? {
            ComponentValue::None | ComponentValue::Scalar(_) => {}
            ComponentValue::Node(child) => {
                if !reduction_inputs_are_retained(model, symbols, child, child_depth, budget)? {
                    return Ok(false);
                }
            }
            ComponentValue::Collection(values) => {
                for item_index in values.items() {
                    budget.claim_work(1)?;
                    let item = required_component(
                        model.item(item_index)?,
                        "reducible-expression collection item",
                    )?;
                    match model.resolve(item)? {
                        ComponentValue::None | ComponentValue::Scalar(_) => {}
                        ComponentValue::Node(child) => {
                            if !reduction_inputs_are_retained(
                                model,
                                symbols,
                                child,
                                child_depth,
                                budget,
                            )? {
                                return Ok(false);
                            }
                        }
                        ComponentValue::Collection(_) => {
                            return Err(EncodedValidationError::invariant(
                                "reducible expression contains a nested collection item",
                            ));
                        }
                    }
                }
            }
        }
    }
    Ok(true)
}

fn reduction_entity_is_retained(symbols: &SymbolPhase, entity_id: u32) -> EncodedResult<bool> {
    let entity = symbols
        .entity_domain
        .values
        .get(usize::try_from(entity_id).unwrap_or(usize::MAX))
        .ok_or_else(|| {
            EncodedValidationError::invariant("reducible expression entity ID is dangling")
        })?;
    let builtin = entity.display == THING_DISPLAY
        || entity.display == NOTHING_DISPLAY
        || entity.display == RDFS_LITERAL_DISPLAY;
    if builtin {
        return Ok(true);
    }
    Ok(symbols.entity_has_source_declaration(entity_id))
}

fn builtin_atomic_class_selection(
    symbols: &SymbolPhase,
    expression: NodeId,
    display: &str,
) -> EncodedResult<AtomicClassSelection> {
    Ok(AtomicClassSelection {
        source: AtomicClassSource::Entity(class_id_by_display(&symbols.entity_domain, display)?),
        expression,
        negative: false,
    })
}

fn child_expression_depth(depth: usize, message: &'static str) -> EncodedResult<usize> {
    depth
        .checked_add(1)
        .ok_or_else(|| EncodedValidationError::resource(message))
}

fn object_property_has_iri<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    identifier: NodeId,
    iri: &str,
) -> EncodedResult<bool> {
    let node = model.node(identifier)?;
    let named = if node.tag() == OBJECT_INVERSE_OF_TAG {
        if node.field_count() != 1 {
            return Err(EncodedValidationError::invariant(
                "inverse object property no longer has schema-1 shape",
            ));
        }
        node_field(model, node, 0, "inverse object-property operand")?
    } else {
        identifier
    };
    if model.node(named)?.tag() != ENTITY_TAG {
        return Err(EncodedValidationError::invariant(
            "object-property restriction has an unsupported property expression",
        ));
    }
    let entity_id = symbols.entity_symbol_for_node(named).ok_or_else(|| {
        EncodedValidationError::invariant(
            "object-property restriction is absent from the reachable entity mapping",
        )
    })?;
    let display = symbols
        .entity_domain
        .values
        .get(usize::try_from(entity_id).unwrap_or(usize::MAX))
        .ok_or_else(|| EncodedValidationError::invariant("object-property entity ID is dangling"))?
        .display
        .strip_prefix(OBJECT_PROPERTY_PREFIX)
        .ok_or_else(|| {
            EncodedValidationError::invariant(
                "object-property restriction resolved to a different entity kind",
            )
        })?;
    Ok(display == iri)
}

fn data_property_has_iri<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    identifier: NodeId,
    iri: &str,
) -> EncodedResult<bool> {
    if model.node(identifier)?.tag() != ENTITY_TAG {
        return Err(EncodedValidationError::invariant(
            "data-property restriction has an unsupported property expression",
        ));
    }
    let entity_id = symbols.entity_symbol_for_node(identifier).ok_or_else(|| {
        EncodedValidationError::invariant(
            "data-property restriction is absent from the reachable entity mapping",
        )
    })?;
    let display = symbols
        .entity_domain
        .values
        .get(usize::try_from(entity_id).unwrap_or(usize::MAX))
        .ok_or_else(|| EncodedValidationError::invariant("data-property entity ID is dangling"))?
        .display
        .strip_prefix(DATA_PROPERTY_PREFIX)
        .ok_or_else(|| {
            EncodedValidationError::invariant(
                "data-property restriction resolved to a different entity kind",
            )
        })?;
    Ok(display == iri)
}

fn data_property_collection_has_iri<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    node: NodeRef,
    offset: usize,
    iri: &str,
    budget: &mut PhaseBudget,
) -> EncodedResult<bool> {
    let field_index = node.fields().start.checked_add(offset).ok_or_else(|| {
        EncodedValidationError::invariant("data-property collection index overflowed")
    })?;
    let component = required_component(
        model.field(field_index)?,
        "data quantifier property collection",
    )?;
    let ComponentValue::Collection(properties) = model.resolve(component)? else {
        return Err(EncodedValidationError::invariant(
            "data quantifier properties did not resolve to a collection",
        ));
    };
    for item_index in properties.items() {
        budget.claim_work(1)?;
        let item = required_component(model.item(item_index)?, "data quantifier property")?;
        let ComponentValue::Node(property) = model.resolve(item)? else {
            return Err(EncodedValidationError::invariant(
                "data quantifier property did not resolve to a node",
            ));
        };
        if data_property_has_iri(model, symbols, property, iri)? {
            return Ok(true);
        }
    }
    Ok(false)
}

fn integer_field_is_zero<B: ByteSource>(
    model: &ValidatedModel<B>,
    node: NodeRef,
    offset: usize,
    name: &'static str,
) -> EncodedResult<bool> {
    let field_index = node
        .fields()
        .start
        .checked_add(offset)
        .ok_or_else(|| EncodedValidationError::invariant(format!("{name} index overflowed")))?;
    let component = required_component(model.field(field_index)?, name)?;
    let ComponentValue::Scalar(value) = model.resolve(component)? else {
        return Err(EncodedValidationError::invariant(format!(
            "{name} is not an integer scalar"
        )));
    };
    if value.kind() != ComponentKind::Integer {
        return Err(EncodedValidationError::invariant(format!(
            "{name} changed component kind"
        )));
    }
    Ok(value.len() == 1 && value.byte(0) == Some(0))
}

fn integer_field_u32_bytes<B: ByteSource>(
    model: &ValidatedModel<B>,
    node: NodeRef,
    offset: usize,
    name: &'static str,
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<(u32, Vec<u8>)>> {
    let field_index = node
        .fields()
        .start
        .checked_add(offset)
        .ok_or_else(|| EncodedValidationError::invariant(format!("{name} index overflowed")))?;
    let component = required_component(model.field(field_index)?, name)?;
    let ComponentValue::Scalar(value) = model.resolve(component)? else {
        return Err(EncodedValidationError::invariant(format!(
            "{name} is not an integer scalar"
        )));
    };
    if value.kind() != ComponentKind::Integer {
        return Err(EncodedValidationError::invariant(format!(
            "{name} changed component kind"
        )));
    }
    budget.claim_work(value.len())?;
    if value.is_empty() {
        return Err(EncodedValidationError::invariant(
            "object cardinality scalar is empty",
        ));
    }
    if value.len() > size_of::<u32>() {
        return Ok(None);
    }
    let mut cardinality = 0_u32;
    for index in 0..value.len() {
        let byte = value.byte(index).ok_or_else(|| {
            EncodedValidationError::invariant("object cardinality scalar became truncated")
        })?;
        let shift = u32::try_from(index)
            .ok()
            .and_then(|value| value.checked_mul(8))
            .ok_or_else(|| {
                EncodedValidationError::resource("object cardinality shift overflowed")
            })?;
        cardinality |= u32::from(byte) << shift;
    }
    Ok(Some((
        cardinality,
        canonical_u32_integer_bytes(cardinality, budget)?,
    )))
}

fn canonical_u32_integer_bytes(
    cardinality: u32,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<u8>> {
    let mut remaining = cardinality;
    let mut bytes = Vec::new();
    bytes.try_reserve_exact(5).map_err(|_| {
        EncodedValidationError::resource("object cardinality scalar allocation failed")
    })?;
    loop {
        budget.claim_work(1)?;
        let chunk = u8::try_from(remaining & 0x7f).map_err(|_| {
            EncodedValidationError::invariant("object cardinality chunk exceeds u8")
        })?;
        remaining >>= 7;
        bytes.push(chunk | if remaining == 0 { 0 } else { 0x80 });
        if remaining == 0 {
            break;
        }
    }
    budget.claim_owned(bytes.len())?;
    Ok(bytes)
}

fn atomic_class_selection_has_display(
    symbols: &SymbolPhase,
    selection: AtomicClassSelection,
    display: &str,
) -> EncodedResult<bool> {
    match selection.source {
        AtomicClassSource::Entity(entity_id) if !selection.negative => {
            Ok(class_entity_display(symbols, entity_id)? == display)
        }
        AtomicClassSource::Entity(_) | AtomicClassSource::Nominal(_) => Ok(false),
    }
}

fn atomic_class_selections_match(left: AtomicClassSelection, right: AtomicClassSelection) -> bool {
    left.source == right.source && left.negative == right.negative
}

fn complement_atomic_class_selection<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    mut selection: AtomicClassSelection,
    complement_expression: NodeId,
    base_is_atomic: bool,
) -> EncodedResult<Option<AtomicClassSelection>> {
    if atomic_class_selection_has_display(symbols, selection, THING_DISPLAY)? {
        selection.source = AtomicClassSource::Entity(class_id_by_display(
            &symbols.entity_domain,
            NOTHING_DISPLAY,
        )?);
        selection.negative = false;
        return Ok(Some(selection));
    }
    if atomic_class_selection_has_display(symbols, selection, NOTHING_DISPLAY)? {
        selection.source =
            AtomicClassSource::Entity(class_id_by_display(&symbols.entity_domain, THING_DISPLAY)?);
        selection.negative = false;
        return Ok(Some(selection));
    }
    if selection.negative {
        let node = model.node(selection.expression)?;
        if node.tag() != OBJECT_COMPLEMENT_OF_TAG || node.field_count() != 1 {
            return Err(EncodedValidationError::invariant(
                "normalized negative class literal lost its complement expression",
            ));
        }
        selection.expression = node_field(model, node, 0, "normalized class-complement operand")?;
        selection.negative = false;
        return Ok(Some(selection));
    }
    if !base_is_atomic {
        return Ok(None);
    }
    selection.expression = complement_expression;
    selection.negative = true;
    Ok(Some(selection))
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
    definitions: &[ClassBooleanDefinition],
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
    for definition in definitions {
        for operand in &definition.operands {
            let ClassBooleanOperand::Nominal {
                key,
                individual_entity_ids,
                ..
            } = operand
            else {
                continue;
            };
            if individual_entity_ids.is_empty()
                || !individual_entity_ids
                    .windows(2)
                    .all(|pair| pair[0] < pair[1])
            {
                return Err(EncodedValidationError::invariant(
                    "normalized object nominal entity IDs are not canonical",
                ));
            }
            budget.claim_work(binary_search_work(class_domain.values.len()))?;
            let class_index = class_domain
                .values
                .binary_search_by(|candidate| candidate.key.cmp(key))
                .map_err(|_| {
                    EncodedValidationError::invariant(
                        "normalized object nominal is absent from the class-expression domain",
                    )
                })?;
            budget.claim_owned(
                individual_entity_ids
                    .len()
                    .checked_mul(size_of::<u32>())
                    .ok_or_else(|| {
                        EncodedValidationError::resource(
                            "normalized object nominal individual IDs overflowed",
                        )
                    })?,
            )?;
            let mut individual_ids = Vec::new();
            individual_ids
                .try_reserve_exact(individual_entity_ids.len())
                .map_err(|_| {
                    EncodedValidationError::resource(
                        "normalized object nominal individual ID allocation failed",
                    )
                })?;
            for entity_id in individual_entity_ids {
                budget.claim_work(binary_search_work(individual_signature.len()))?;
                let binding_index = individual_signature
                    .binary_search_by_key(entity_id, |binding| binding.entity_id)
                    .map_err(|_| {
                        EncodedValidationError::invariant(
                            "normalized object nominal member is absent from the individual signature",
                        )
                    })?;
                individual_ids.push(individual_signature[binding_index].individual_id);
            }
            if !individual_ids.windows(2).all(|pair| pair[0] < pair[1]) {
                return Err(EncodedValidationError::invariant(
                    "normalized object nominal individual IDs are not canonical",
                ));
            }
            budget.claim_owned(size_of::<NominalBinding>())?;
            bindings.try_reserve(1).map_err(|_| {
                EncodedValidationError::resource(
                    "normalized object nominal binding allocation failed",
                )
            })?;
            bindings.push(NominalBinding {
                class_id: u32::try_from(class_index).map_err(|_| {
                    EncodedValidationError::resource(
                        "normalized object nominal class ID exceeds u32",
                    )
                })?,
                individual_ids,
            });
        }
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

fn class_entity_display(symbols: &SymbolPhase, entity_id: u32) -> EncodedResult<&str> {
    symbols
        .entity_domain
        .values
        .get(usize::try_from(entity_id).unwrap_or(usize::MAX))
        .map(|entity| entity.display.as_str())
        .ok_or_else(|| EncodedValidationError::invariant("atomic class entity ID is dangling"))
}

#[allow(clippy::too_many_arguments)]
fn named_data_range_domain<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    has_data_roles: bool,
    scope_maps: &[AnonymousScopeMap],
    class_definitions: &[ClassBooleanDefinition],
    definitions: &[DataBooleanDefinition],
    datatype_definitions: &[DatatypeBooleanDefinition],
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

    for definition in definitions {
        for seed in &definition.expression_symbols {
            push_seeded_data_range_symbol(&mut pending, seed, budget)?;
        }
    }
    for definition in class_definitions {
        for seed in &definition.data_expression_symbols {
            push_seeded_data_range_symbol(&mut pending, seed, budget)?;
        }
    }
    for definition in datatype_definitions {
        for seed in &definition.expression_symbols {
            push_seeded_data_range_symbol(&mut pending, seed, budget)?;
        }
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
        let Some(selection) = atomic_data_range_selection(model, symbols, range, budget)? else {
            continue;
        };
        if model.node(selection.base)?.tag() != ENTITY_TAG {
            budget.claim_owned(size_of::<NodeId>())?;
            expressions.try_reserve(1).map_err(|_| {
                EncodedValidationError::resource("data-range selection allocation failed")
            })?;
            expressions.push(selection.base);
        }
        if selection.negative {
            budget.claim_owned(size_of::<NodeId>())?;
            expressions.try_reserve(1).map_err(|_| {
                EncodedValidationError::resource("data-range selection allocation failed")
            })?;
            expressions.push(selection.expression);
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

    for definition in definitions {
        let following = pending.len().checked_add(1).ok_or_else(|| {
            EncodedValidationError::resource("generated data-range symbol count overflowed")
        })?;
        PhaseBudget::count(
            following,
            budget.limits.max_data_range_symbols,
            "generated data-range symbol count",
        )?;
        budget.claim_owned(
            size_of::<DecodedSymbolValue>()
                + definition.generated_key.len()
                + definition.generated_display.len(),
        )?;
        pending.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("generated data-range symbol allocation failed")
        })?;
        pending.push(DecodedSymbolValue {
            identifier: 0,
            key: definition.generated_key.clone(),
            display: definition.generated_display.clone(),
            generated: true,
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
        DATA_INTERSECTION_OF_TAG => Ok("DataIntersectionOf:"),
        DATA_UNION_OF_TAG => Ok("DataUnionOf:"),
        _ => Err(EncodedValidationError::invariant(
            "selected data-range expression has an unsupported constructor",
        )),
    }
}

fn atomic_data_range_selection<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    identifier: NodeId,
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<AtomicDataRangeSelection>> {
    atomic_data_range_selection_at_depth(model, symbols, identifier, 0, budget)
}

fn atomic_data_range_selection_at_depth<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    identifier: NodeId,
    initial_depth: usize,
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<AtomicDataRangeSelection>> {
    let mut base = identifier;
    let mut negative = false;
    let mut normalized_complement = None;
    let mut depth = initial_depth;
    PhaseBudget::count(depth, budget.limits.max_canonical_depth, "data-range depth")?;
    loop {
        let node = model.node(base)?;
        if node.tag() != DATA_COMPLEMENT_OF_TAG {
            break;
        }
        if node.field_count() != 1 {
            return Err(EncodedValidationError::invariant(
                "data complement no longer has schema-1 shape",
            ));
        }
        depth = depth
            .checked_add(1)
            .ok_or_else(|| EncodedValidationError::resource("data-complement depth overflowed"))?;
        PhaseBudget::count(depth, budget.limits.max_canonical_depth, "data-range depth")?;
        budget.claim_work(1)?;
        normalized_complement = Some(base);
        base = node_field(model, node, 0, "data-complement operand")?;
        negative = !negative;
    }
    let base_node = model.node(base)?;
    let base_is_atomic = matches!(
        base_node.tag(),
        ENTITY_TAG | DATA_ONE_OF_TAG | DATATYPE_RESTRICTION_TAG
    );
    let Some(selection) =
        positive_atomic_data_range_selection(model, symbols, base, depth, budget)?
    else {
        return Ok(None);
    };
    if !negative {
        return Ok(Some(selection));
    }
    Ok(complement_atomic_data_range_selection(
        selection,
        normalized_complement.unwrap_or(identifier),
        base_is_atomic,
    ))
}

fn positive_atomic_data_range_selection<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    identifier: NodeId,
    depth: usize,
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<AtomicDataRangeSelection>> {
    let node = model.node(identifier)?;
    let supported = match node.tag() {
        ENTITY_TAG => {
            let entity_id = symbols.entity_symbol_for_node(identifier).ok_or_else(|| {
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
            entity.display.starts_with("datatype:")
        }
        DATA_ONE_OF_TAG if node.field_count() == 1 => true,
        DATATYPE_RESTRICTION_TAG if node.field_count() == 2 => true,
        DATA_ONE_OF_TAG | DATATYPE_RESTRICTION_TAG => {
            return Err(EncodedValidationError::invariant(
                "atomic data-range expression no longer has schema-1 shape",
            ));
        }
        _ => false,
    };
    if supported {
        return Ok(Some(AtomicDataRangeSelection {
            base: identifier,
            expression: identifier,
            negative: false,
        }));
    }
    if !matches!(node.tag(), DATA_INTERSECTION_OF_TAG | DATA_UNION_OF_TAG) {
        return Ok(None);
    }
    if node.field_count() != 1 {
        return Err(EncodedValidationError::invariant(
            "data Boolean expression no longer has schema-1 shape",
        ));
    }
    let component = required_component(model.field(node.fields().start)?, "data Boolean operands")?;
    let ComponentValue::Collection(operands) = model.resolve(component)? else {
        return Err(EncodedValidationError::invariant(
            "data Boolean operands did not resolve to a collection",
        ));
    };
    let operand_depth = depth
        .checked_add(1)
        .ok_or_else(|| EncodedValidationError::resource("data-range depth overflowed"))?;
    PhaseBudget::count(
        operand_depth,
        budget.limits.max_canonical_depth,
        "data-range depth",
    )?;
    let intersection = node.tag() == DATA_INTERSECTION_OF_TAG;
    let mut absorbing = None;
    let mut retained = None;
    let mut identity = None;
    for item_index in operands.items() {
        budget.claim_work(1)?;
        let item = required_component(model.item(item_index)?, "data Boolean operand")?;
        let ComponentValue::Node(operand) = model.resolve(item)? else {
            return Err(EncodedValidationError::invariant(
                "data Boolean operand did not resolve to a node",
            ));
        };
        let Some(selection) =
            atomic_data_range_selection_at_depth(model, symbols, operand, operand_depth, budget)?
        else {
            return Ok(None);
        };
        let is_top = atomic_data_range_selection_is_top(model, symbols, selection)?;
        let is_bottom = atomic_data_range_selection_is_bottom(model, symbols, selection)?;
        if (intersection && is_bottom) || (!intersection && is_top) {
            absorbing.get_or_insert(selection);
            continue;
        }
        if absorbing.is_some() {
            continue;
        }
        if (intersection && is_top) || (!intersection && is_bottom) {
            identity.get_or_insert(selection);
            continue;
        }
        if retained.is_some_and(|known| atomic_data_range_selections_match(known, selection)) {
            continue;
        }
        if retained.is_some() {
            return Ok(None);
        }
        retained = Some(selection);
    }
    Ok(absorbing.or(retained).or(identity))
}

fn atomic_data_range_selection_is_top<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    selection: AtomicDataRangeSelection,
) -> EncodedResult<bool> {
    if selection.negative || model.node(selection.base)?.tag() != ENTITY_TAG {
        return Ok(false);
    }
    let entity_id = symbols
        .entity_symbol_for_node(selection.base)
        .ok_or_else(|| {
            EncodedValidationError::invariant(
                "atomic data-range entity is absent from the reachable entity mapping",
            )
        })?;
    let entity = symbols
        .entity_domain
        .values
        .get(usize::try_from(entity_id).unwrap_or(usize::MAX))
        .ok_or_else(|| {
            EncodedValidationError::invariant("atomic datatype entity ID is dangling")
        })?;
    Ok(entity.display == RDFS_LITERAL_DISPLAY)
}

fn atomic_data_range_selection_is_bottom<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    selection: AtomicDataRangeSelection,
) -> EncodedResult<bool> {
    if !selection.negative {
        return Ok(false);
    }
    atomic_data_range_selection_is_top(
        model,
        symbols,
        AtomicDataRangeSelection {
            negative: false,
            ..selection
        },
    )
}

fn atomic_data_range_selections_match(
    left: AtomicDataRangeSelection,
    right: AtomicDataRangeSelection,
) -> bool {
    left.base == right.base && left.negative == right.negative
}

const fn complement_atomic_data_range_selection(
    mut selection: AtomicDataRangeSelection,
    complement_expression: NodeId,
    base_is_atomic: bool,
) -> Option<AtomicDataRangeSelection> {
    if selection.negative {
        selection.expression = selection.base;
        selection.negative = false;
        return Some(selection);
    }
    if !base_is_atomic {
        return None;
    }
    selection.expression = complement_expression;
    selection.negative = true;
    Some(selection)
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

#[allow(clippy::too_many_arguments)]
fn named_subclass<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    class_domain: &DecodedSymbolDomain,
    signature: &[ClassSignatureBinding],
    definitions: &[ClassBooleanDefinition],
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
    let sub_selection = atomic_class_selection(model, symbols, sub_class_node, budget)?;
    let super_class_node = node_field(model, node, 1, "subclass consequent")?;
    let super_selection = atomic_class_selection(model, symbols, super_class_node, budget)?;
    if (sub_selection.is_none()
        && class_boolean_definition(definitions, sub_class_node, DefinitionPolarity::Negative)
            .is_none())
        || (super_selection.is_none()
            && class_boolean_definition(
                definitions,
                super_class_node,
                DefinitionPolarity::Positive,
            )
            .is_none())
    {
        return Ok(None);
    }
    if let (Some(sub_selection), Some(super_selection)) = (sub_selection, super_selection) {
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
                generated: false,
            }));
        }
    }
    let Some((sub_class, sub_negative)) = class_expression_literal_with_definitions(
        model,
        symbols,
        class_domain,
        signature,
        sub_class_node,
        DefinitionPolarity::Negative,
        definitions,
        scope_maps,
        budget,
    )?
    else {
        return Ok(None);
    };
    let Some((super_class, super_negative)) = class_expression_literal_with_definitions(
        model,
        symbols,
        class_domain,
        signature,
        super_class_node,
        DefinitionPolarity::Positive,
        definitions,
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
        generated: false,
    }))
}

#[allow(clippy::too_many_arguments)]
fn named_equivalent_classes<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    class_domain: &DecodedSymbolDomain,
    signature: &[ClassSignatureBinding],
    definitions: &[ClassBooleanDefinition],
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
    let mut classes = Vec::new();
    budget.claim_owned(
        expressions
            .len()
            .checked_mul(size_of::<NodeId>())
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
        let selection = atomic_class_selection(model, symbols, identifier, budget)?;
        let negative =
            class_boolean_definition(definitions, identifier, DefinitionPolarity::Negative);
        let positive =
            class_boolean_definition(definitions, identifier, DefinitionPolarity::Positive);
        if selection.is_none() && (negative.is_none() || positive.is_none()) {
            return Ok(None);
        }
        classes.push(identifier);
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
    for (index, sub_identifier) in classes.iter().copied().enumerate() {
        let following = index.checked_add(1).ok_or_else(|| {
            EncodedValidationError::resource("equivalent-classes edge index overflowed")
        })?;
        let super_identifier = classes[following % classes.len()];
        let (sub_class, sub_negative) = class_expression_literal_with_definitions(
            model,
            symbols,
            class_domain,
            signature,
            sub_identifier,
            DefinitionPolarity::Negative,
            definitions,
            scope_maps,
            budget,
        )?
        .ok_or_else(|| {
            EncodedValidationError::invariant(
                "validated equivalent-class antecedent became unsupported",
            )
        })?;
        let (super_class, super_negative) = class_expression_literal_with_definitions(
            model,
            symbols,
            class_domain,
            signature,
            super_identifier,
            DefinitionPolarity::Positive,
            definitions,
            scope_maps,
            budget,
        )?
        .ok_or_else(|| {
            EncodedValidationError::invariant(
                "validated equivalent-class consequent became unsupported",
            )
        })?;
        edges.push(RawEdge {
            sub_class,
            sub_negative,
            super_class,
            super_negative,
            provenance,
            generated: false,
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
    definitions: &[ClassBooleanDefinition],
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
        if let Some(selection) = atomic_class_selection(model, symbols, identifier, budget)? {
            if matches!(selection.source, AtomicClassSource::Entity(entity_id)
                if !selection.negative
                    && class_entity_display(symbols, entity_id)? == NOTHING_DISPLAY)
            {
                continue;
            }
        } else if class_boolean_definition(definitions, identifier, DefinitionPolarity::Negative)
            .is_none()
        {
            return Ok(None);
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
            .checked_mul(size_of::<(ClassLiteral, Vec<u8>)>())
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
        let selection = atomic_class_selection(model, symbols, identifier, budget)?;
        let Some((class_id, negative)) = class_expression_literal_with_definitions(
            model,
            symbols,
            class_domain,
            signature,
            identifier,
            DefinitionPolarity::Negative,
            definitions,
            scope_maps,
            budget,
        )?
        else {
            return Ok(None);
        };
        let literal = ClassLiteral { class_id, negative };
        let key = if let Some(selection) = selection {
            normalized_class_literal_key(
                model,
                class_domain,
                literal,
                selection.expression,
                scope_maps,
                budget,
            )?
        } else {
            let definition =
                class_boolean_definition(definitions, identifier, DefinitionPolarity::Negative)
                    .ok_or_else(|| {
                        EncodedValidationError::invariant(
                            "validated disjoint Boolean definition disappeared",
                        )
                    })?;
            budget.claim_owned(definition.generated_key.len())?;
            definition.generated_key.clone()
        };
        classes.push((literal, key));
    }
    if classes.len() < 2 {
        return Err(EncodedValidationError::invariant(
            "disjoint-classes root has fewer than two members",
        ));
    }
    let provenance = source_axiom_digest(model, root, scope_maps, budget)?;
    normalize_disjoint_class_literals(classes, thing, nothing, provenance, budget).map(Some)
}

fn normalize_disjoint_class_literals(
    classes: Vec<(ClassLiteral, Vec<u8>)>,
    thing: u32,
    nothing: u32,
    provenance: [u8; 32],
    budget: &mut PhaseBudget,
) -> EncodedResult<NamedDisjointOutput> {
    let mut keyed = Vec::new();
    budget.claim_owned(
        classes
            .len()
            .checked_mul(size_of::<(Vec<u8>, ClassLiteral)>())
            .ok_or_else(|| {
                EncodedValidationError::resource("live disjoint-class allocation overflowed")
            })?,
    )?;
    keyed
        .try_reserve_exact(classes.len())
        .map_err(|_| EncodedValidationError::resource("live disjoint-class allocation failed"))?;
    for (literal, key) in classes {
        keyed.push((key, literal));
    }
    budget.claim_work(sort_work(keyed.len()))?;
    keyed.sort_by(|left, right| left.0.cmp(&right.0));

    let mut live = Vec::<(ClassLiteral, Vec<u8>)>::new();
    let mut edges = Vec::new();
    budget.claim_owned(
        keyed
            .len()
            .checked_mul(size_of::<(ClassLiteral, Vec<u8>)>())
            .and_then(|value| value.checked_add(keyed.len().checked_mul(size_of::<RawEdge>())?))
            .ok_or_else(|| {
                EncodedValidationError::resource("normalized disjoint-class allocation overflowed")
            })?,
    )?;
    live.try_reserve_exact(keyed.len()).map_err(|_| {
        EncodedValidationError::resource("normalized disjoint-class allocation failed")
    })?;
    edges.try_reserve_exact(keyed.len()).map_err(|_| {
        EncodedValidationError::resource("duplicate disjoint-class edge allocation failed")
    })?;
    let mut index = 0_usize;
    while index < keyed.len() {
        let mut end = index.checked_add(1).ok_or_else(|| {
            EncodedValidationError::resource("disjoint-class group index overflowed")
        })?;
        while end < keyed.len() && keyed[end].0 == keyed[index].0 {
            if keyed[end].1 != keyed[index].1 {
                return Err(EncodedValidationError::invariant(
                    "normalized disjoint-class key has conflicting literals",
                ));
            }
            end = end.checked_add(1).ok_or_else(|| {
                EncodedValidationError::resource("disjoint-class group index overflowed")
            })?;
        }
        let literal = keyed[index].1;
        if end - index > 1 {
            if literal.negative || literal.class_id != nothing {
                edges.push(RawEdge {
                    sub_class: literal.class_id,
                    sub_negative: literal.negative,
                    super_class: nothing,
                    super_negative: false,
                    provenance,
                    generated: false,
                });
            }
        } else if literal.negative || literal.class_id != nothing {
            live.push((literal, std::mem::take(&mut keyed[index].0)));
        }
        index = end;
    }

    if live
        .iter()
        .any(|(literal, _)| !literal.negative && literal.class_id == thing)
    {
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
        edges.try_reserve(edge_count).map_err(|_| {
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
                    generated: false,
                });
            }
        }
        return Ok(NamedDisjointOutput {
            edges,
            disjoint: None,
            provenance,
        });
    }

    let disjoint = if live.len() >= 2 {
        let guard_digest = disjoint_guard_digest_keys(&live, budget)?;
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
    Ok(NamedDisjointOutput {
        edges,
        disjoint,
        provenance,
    })
}
#[allow(clippy::too_many_arguments)]
fn normalized_class_literal_key<B: ByteSource>(
    model: &ValidatedModel<B>,
    class_domain: &DecodedSymbolDomain,
    literal: ClassLiteral,
    expression: NodeId,
    scope_maps: &[AnonymousScopeMap],
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<u8>> {
    if literal.negative {
        let key = canonical::canonical_node_key(model, expression, scope_maps, budget)?;
        budget.claim_owned(key.len())?;
        return Ok(key);
    }
    let source = &class_domain
        .values
        .get(usize::try_from(literal.class_id).unwrap_or(usize::MAX))
        .ok_or_else(|| {
            EncodedValidationError::invariant("normalized class literal ID is dangling")
        })?
        .key;
    budget.claim_owned(source.len())?;
    let mut key = Vec::new();
    key.try_reserve_exact(source.len()).map_err(|_| {
        EncodedValidationError::resource("normalized class literal key allocation failed")
    })?;
    key.extend_from_slice(source);
    Ok(key)
}

#[allow(clippy::too_many_arguments)]
fn named_disjoint_union<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    class_domain: &DecodedSymbolDomain,
    signature: &[ClassSignatureBinding],
    definitions: &[ClassBooleanDefinition],
    root: NodeId,
    thing: u32,
    nothing: u32,
    scope_maps: &[AnonymousScopeMap],
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<NamedDisjointOutput>> {
    let node = model.node(root)?;
    if node.tag() != DISJOINT_UNION_TAG || node.field_count() != 3 {
        return Err(EncodedValidationError::invariant(
            "disjoint-union root no longer has schema-1 shape",
        ));
    }
    let defined = node_field(model, node, 0, "disjoint-union defined class")?;
    if atomic_class_selection(model, symbols, defined, budget)?.is_none() {
        return Ok(None);
    }
    let expressions_component = required_component(
        model.field(node.fields().start + 1)?,
        "disjoint-union expressions",
    )?;
    let ComponentValue::Collection(expressions) = model.resolve(expressions_component)? else {
        return Err(EncodedValidationError::invariant(
            "disjoint-union expressions did not resolve to a collection",
        ));
    };
    if expressions.len() < 2 {
        return Err(EncodedValidationError::invariant(
            "disjoint-union root has fewer than two members",
        ));
    }
    let union_selection =
        reducible_class_boolean_operands(model, symbols, expressions, false, 0, budget)?;
    let union_definition =
        class_boolean_definition_for_root(definitions, root, DefinitionPolarity::Positive);
    if union_selection.is_none() && union_definition.is_none() {
        return Ok(None);
    }
    let Some((defined_class, defined_negative)) = atomic_class_expression_literal(
        model,
        symbols,
        class_domain,
        signature,
        defined,
        scope_maps,
        budget,
    )?
    else {
        return Ok(None);
    };
    let (union_class, union_negative) = if let Some(selection) = union_selection {
        atomic_class_selection_literal(
            model,
            class_domain,
            signature,
            selection,
            scope_maps,
            budget,
        )?
    } else {
        let definition = union_definition.ok_or_else(|| {
            EncodedValidationError::invariant("generated disjoint-union definition disappeared")
        })?;
        budget.claim_work(binary_search_work(class_domain.values.len()))?;
        let class_index = class_domain
            .values
            .binary_search_by(|candidate| candidate.key.cmp(&definition.generated_key))
            .map_err(|_| {
                EncodedValidationError::invariant(
                    "generated disjoint-union class symbol disappeared",
                )
            })?;
        (
            u32::try_from(class_index).map_err(|_| {
                EncodedValidationError::resource("generated disjoint-union class ID exceeds u32")
            })?,
            false,
        )
    };
    let provenance = source_axiom_digest(model, root, scope_maps, budget)?;
    let definition_edge_count = expressions.len().checked_add(1).ok_or_else(|| {
        EncodedValidationError::resource("disjoint-union definition edge count overflowed")
    })?;
    budget.claim_owned(
        definition_edge_count
            .checked_mul(size_of::<RawEdge>())
            .ok_or_else(|| {
                EncodedValidationError::resource(
                    "disjoint-union definition edge allocation overflowed",
                )
            })?,
    )?;
    let mut definition_edges = Vec::new();
    definition_edges
        .try_reserve_exact(definition_edge_count)
        .map_err(|_| {
            EncodedValidationError::resource("disjoint-union definition edge allocation failed")
        })?;
    definition_edges.push(RawEdge {
        sub_class: defined_class,
        sub_negative: defined_negative,
        super_class: union_class,
        super_negative: union_negative,
        provenance,
        generated: false,
    });
    let mut members = Vec::new();
    budget.claim_owned(
        expressions
            .len()
            .checked_mul(size_of::<(ClassLiteral, Vec<u8>)>())
            .ok_or_else(|| {
                EncodedValidationError::resource("disjoint-union member allocation overflowed")
            })?,
    )?;
    members
        .try_reserve_exact(expressions.len())
        .map_err(|_| EncodedValidationError::resource("disjoint-union member allocation failed"))?;
    for item_index in expressions.items() {
        budget.claim_work(1)?;
        let item = required_component(model.item(item_index)?, "disjoint-union member")?;
        let ComponentValue::Node(identifier) = model.resolve(item)? else {
            return Err(EncodedValidationError::invariant(
                "disjoint-union member did not resolve to a node",
            ));
        };
        let selection = atomic_class_selection(model, symbols, identifier, budget)?;
        let Some((class_id, negative)) = class_expression_literal_with_definitions(
            model,
            symbols,
            class_domain,
            signature,
            identifier,
            DefinitionPolarity::Negative,
            definitions,
            scope_maps,
            budget,
        )?
        else {
            return Ok(None);
        };
        definition_edges.push(RawEdge {
            sub_class: class_id,
            sub_negative: negative,
            super_class: defined_class,
            super_negative: defined_negative,
            provenance,
            generated: false,
        });
        let literal = ClassLiteral { class_id, negative };
        let key = normalized_class_literal_key(
            model,
            class_domain,
            literal,
            selection.map_or(identifier, |selection| selection.expression),
            scope_maps,
            budget,
        )?;
        members.push((literal, key));
    }
    let mut output =
        normalize_disjoint_class_literals(members, thing, nothing, provenance, budget)?;
    output
        .edges
        .try_reserve(definition_edges.len())
        .map_err(|_| {
            EncodedValidationError::resource("disjoint-union edge merge allocation failed")
        })?;
    output.edges.extend(definition_edges);
    Ok(Some(output))
}

#[allow(clippy::too_many_arguments)]
fn named_object_constraint<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    object_roles: &ObjectRolePhase,
    class_domain: &DecodedSymbolDomain,
    class_signature: &[ClassSignatureBinding],
    definitions: &[ClassBooleanDefinition],
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
    let expression = node_field(model, node, 1, "object-property constraint class")?;
    let Some((class_id, negative)) = class_expression_literal_with_definitions(
        model,
        symbols,
        class_domain,
        class_signature,
        expression,
        DefinitionPolarity::Positive,
        definitions,
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
        class: ClassLiteral { class_id, negative },
        filler: None,
        cardinality: None,
        provenance,
        generated: false,
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
    definitions: &[ClassBooleanDefinition],
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
    let expression = node_field(model, node, 1, "data-property domain class")?;
    let Some((class_id, negative)) = class_expression_literal_with_definitions(
        model,
        symbols,
        class_domain,
        class_signature,
        expression,
        DefinitionPolarity::Positive,
        definitions,
        scope_maps,
        budget,
    )?
    else {
        return Ok(None);
    };
    let provenance = source_axiom_digest(model, root, scope_maps, budget)?;
    Ok(Some(RawDataDomain {
        role_id,
        class: ClassLiteral { class_id, negative },
        provenance,
    }))
}

#[allow(clippy::too_many_arguments)]
fn named_data_range<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    data_roles: &DataRolePhase,
    data_range_domain: &DecodedSymbolDomain,
    definitions: &[DataBooleanDefinition],
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
    let Some(range) = data_range_literal_with_definitions(
        model,
        symbols,
        data_range_domain,
        range_node,
        DefinitionPolarity::Positive,
        definitions,
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

#[allow(clippy::too_many_arguments)]
fn data_range_literal_with_definitions<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    data_range_domain: &DecodedSymbolDomain,
    range: NodeId,
    polarity: DefinitionPolarity,
    definitions: &[DataBooleanDefinition],
    scope_maps: &[AnonymousScopeMap],
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<DataRangeLiteral>> {
    if let Some(literal) =
        atomic_data_range_literal(model, symbols, data_range_domain, range, scope_maps, budget)?
    {
        return Ok(Some(literal));
    }
    let Some(definition) = data_boolean_definition(definitions, range, polarity) else {
        return Ok(None);
    };
    budget.claim_work(binary_search_work(data_range_domain.values.len()))?;
    let index = data_range_domain
        .values
        .binary_search_by(|value| value.key.cmp(&definition.generated_key))
        .map_err(|_| {
            EncodedValidationError::invariant("generated data-range symbol disappeared")
        })?;
    Ok(Some(DataRangeLiteral {
        range_id: u32::try_from(index).map_err(|_| {
            EncodedValidationError::resource("generated data-range symbol ID exceeds u32")
        })?,
        negative: false,
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
    let Some(selection) = atomic_data_range_selection(model, symbols, range, budget)? else {
        return Ok(None);
    };
    atomic_data_range_selection_literal(
        model,
        symbols,
        data_range_domain,
        selection,
        scope_maps,
        budget,
    )
    .map(Some)
}

fn atomic_data_range_selection_literal<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    data_range_domain: &DecodedSymbolDomain,
    selection: AtomicDataRangeSelection,
    scope_maps: &[AnonymousScopeMap],
    budget: &mut PhaseBudget,
) -> EncodedResult<DataRangeLiteral> {
    let range_id = if model.node(selection.base)?.tag() == ENTITY_TAG {
        named_data_range_id(model, symbols, data_range_domain, selection.base, budget)?.ok_or_else(
            || {
                EncodedValidationError::invariant(
                    "atomic datatype is absent from the named data-range domain",
                )
            },
        )?
    } else {
        let key = canonical::canonical_node_key(model, selection.base, scope_maps, budget)?;
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
    Ok(DataRangeLiteral {
        range_id,
        negative: selection.negative,
    })
}

fn data_range_definition_literal(
    data_range_domain: &DecodedSymbolDomain,
    definition: &DataRangeDefinition,
    budget: &mut PhaseBudget,
) -> EncodedResult<DataRangeLiteral> {
    if data_range_domain.kind != SymbolKind::DataRange {
        return Err(EncodedValidationError::invariant(
            "data-range definition received the wrong symbol domain",
        ));
    }
    budget.claim_work(binary_search_work(data_range_domain.values.len()))?;
    let index = data_range_domain
        .values
        .binary_search_by(|value| value.key.cmp(&definition.base_key))
        .map_err(|_| {
            EncodedValidationError::invariant(
                "data-range definition base is absent from the symbol domain",
            )
        })?;
    Ok(DataRangeLiteral {
        range_id: u32::try_from(index).map_err(|_| {
            EncodedValidationError::resource("data-range definition symbol ID exceeds u32")
        })?,
        negative: definition.negative,
    })
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
fn emit_datatype_boolean_definition<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    data_range_domain: &DecodedSymbolDomain,
    definition: &DatatypeBooleanDefinition,
    scope_maps: &[AnonymousScopeMap],
    clauses: &mut Vec<RawDataBooleanClause>,
    budget: &mut PhaseBudget,
) -> EncodedResult<[u8; 32]> {
    let node = model.node(definition.root)?;
    if node.tag() != DATATYPE_DEFINITION_TAG || node.field_count() != 3 {
        return Err(EncodedValidationError::invariant(
            "datatype Boolean definition no longer has schema-1 shape",
        ));
    }
    let datatype = node_field(model, node, 0, "defined datatype")?;
    let left_range_id = named_data_range_id(model, symbols, data_range_domain, datatype, budget)?
        .ok_or_else(|| {
        EncodedValidationError::invariant(
            "datatype Boolean definition subject is not a named datatype",
        )
    })?;
    let expression = node_field(model, node, 1, "datatype defining range")?;
    if expression != definition.expression || definition.operands.len() < 2 {
        return Err(EncodedValidationError::invariant(
            "planned datatype Boolean definition changed before emission",
        ));
    }
    let left = DataRangeLiteral {
        range_id: left_range_id,
        negative: false,
    };
    let mut operands = Vec::new();
    budget.claim_owned(
        definition
            .operands
            .len()
            .checked_mul(size_of::<DataRangeLiteral>())
            .ok_or_else(|| {
                EncodedValidationError::resource("datatype Boolean literal allocation overflowed")
            })?,
    )?;
    operands
        .try_reserve_exact(definition.operands.len())
        .map_err(|_| {
            EncodedValidationError::resource("datatype Boolean literal allocation failed")
        })?;
    for selection in definition.operands.iter().copied() {
        operands.push(atomic_data_range_selection_literal(
            model,
            symbols,
            data_range_domain,
            selection,
            scope_maps,
            budget,
        )?);
    }
    let provenance = source_axiom_digest(model, definition.root, scope_maps, budget)?;
    if definition.intersection {
        for operand in &operands {
            push_raw_data_boolean_clause(
                clauses,
                vec![left],
                vec![*operand],
                provenance,
                false,
                budget,
            )?;
        }
        push_raw_data_boolean_clause(clauses, operands, vec![left], provenance, false, budget)?;
    } else {
        push_raw_data_boolean_clause(
            clauses,
            vec![left],
            operands.clone(),
            provenance,
            false,
            budget,
        )?;
        for operand in operands {
            push_raw_data_boolean_clause(
                clauses,
                vec![operand],
                vec![left],
                provenance,
                false,
                budget,
            )?;
        }
    }
    Ok(provenance)
}

#[allow(clippy::too_many_arguments)]
fn named_key<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    object_roles: Option<&ObjectRolePhase>,
    data_roles: Option<&DataRolePhase>,
    class_domain: &DecodedSymbolDomain,
    class_signature: &[ClassSignatureBinding],
    definitions: &[ClassBooleanDefinition],
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
    let expression = node_field(model, node, 0, "has-key class expression")?;
    let Some((class_id, negative)) = class_expression_literal_with_definitions(
        model,
        symbols,
        class_domain,
        class_signature,
        expression,
        DefinitionPolarity::Negative,
        definitions,
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
        class: ClassLiteral { class_id, negative },
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
    definitions: &[ClassBooleanDefinition],
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
        definitions,
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

#[allow(clippy::too_many_arguments)]
fn class_assertion_literal<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    class_domain: &DecodedSymbolDomain,
    signature: &[ClassSignatureBinding],
    definitions: &[ClassBooleanDefinition],
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
    class_expression_literal_with_definitions(
        model,
        symbols,
        class_domain,
        signature,
        identifier,
        DefinitionPolarity::Positive,
        definitions,
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
    atomic_class_selection_literal(
        model,
        class_domain,
        signature,
        selection,
        scope_maps,
        budget,
    )
    .map(Some)
}

fn atomic_class_selection_literal<B: ByteSource>(
    model: &ValidatedModel<B>,
    class_domain: &DecodedSymbolDomain,
    signature: &[ClassSignatureBinding],
    selection: AtomicClassSelection,
    scope_maps: &[AnonymousScopeMap],
    budget: &mut PhaseBudget,
) -> EncodedResult<(u32, bool)> {
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
    Ok((class_id, selection.negative))
}

#[allow(clippy::too_many_arguments)]
fn class_expression_literal_with_definitions<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    class_domain: &DecodedSymbolDomain,
    signature: &[ClassSignatureBinding],
    identifier: NodeId,
    polarity: DefinitionPolarity,
    definitions: &[ClassBooleanDefinition],
    scope_maps: &[AnonymousScopeMap],
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<(u32, bool)>> {
    if let Some(literal) = atomic_class_expression_literal(
        model,
        symbols,
        class_domain,
        signature,
        identifier,
        scope_maps,
        budget,
    )? {
        return Ok(Some(literal));
    }
    let Some(definition) = class_boolean_definition(definitions, identifier, polarity) else {
        return Ok(None);
    };
    budget.claim_work(binary_search_work(class_domain.values.len()))?;
    let class_index = class_domain
        .values
        .binary_search_by(|candidate| candidate.key.cmp(&definition.generated_key))
        .map_err(|_| EncodedValidationError::invariant("generated class symbol disappeared"))?;
    Ok(Some((
        u32::try_from(class_index)
            .map_err(|_| EncodedValidationError::resource("generated class ID exceeds u32"))?,
        false,
    )))
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

#[allow(clippy::too_many_arguments)]
fn emit_class_boolean_definitions<B: ByteSource>(
    model: &ValidatedModel<B>,
    _symbols: &SymbolPhase,
    class_domain: &DecodedSymbolDomain,
    data_range_domain: &DecodedSymbolDomain,
    signature: &[ClassSignatureBinding],
    definitions: &[ClassBooleanDefinition],
    scope_maps: &[AnonymousScopeMap],
    edges: &mut Vec<RawEdge>,
    boolean_clauses: &mut Vec<RawBooleanClause>,
    object_constraints: &mut Vec<RawObjectConstraint>,
    data_constraints: &mut Vec<RawDataConstraint>,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    for definition in definitions {
        if !definition.data_dependencies.is_empty() {
            return Err(EncodedValidationError::invariant(
                "generated class definition retained uncollected data dependencies",
            ));
        }
        budget.claim_work(binary_search_work(class_domain.values.len()))?;
        let generated_index = class_domain
            .values
            .binary_search_by(|candidate| candidate.key.cmp(&definition.generated_key))
            .map_err(|_| {
                EncodedValidationError::invariant("generated definition symbol disappeared")
            })?;
        let generated = ClassLiteral {
            class_id: u32::try_from(generated_index).map_err(|_| {
                EncodedValidationError::resource("generated definition class ID exceeds u32")
            })?,
            negative: false,
        };
        if let Some(role_id) = definition.object_self_role_id {
            if definition.complement
                || !definition.operands.is_empty()
                || definition.object_quantifier.is_some()
                || definition.object_cardinality.is_some()
                || definition.data_quantifier.is_some()
                || definition.data_cardinality.is_some()
                || !definition.data_expression_symbols.is_empty()
                || definition.provenance.is_empty()
            {
                return Err(EncodedValidationError::invariant(
                    "generated object-self definition changed before emission",
                ));
            }
            for provenance in &definition.provenance {
                budget.claim_owned(size_of::<RawObjectConstraint>())?;
                object_constraints.try_reserve(1).map_err(|_| {
                    EncodedValidationError::resource(
                        "generated object-self clause allocation failed",
                    )
                })?;
                object_constraints.push(RawObjectConstraint {
                    kind: match definition.polarity {
                        DefinitionPolarity::Positive => ObjectConstraintKind::SelfConsequent,
                        DefinitionPolarity::Negative => ObjectConstraintKind::SelfAntecedent,
                    },
                    role_id,
                    class: generated,
                    filler: None,
                    cardinality: None,
                    provenance: *provenance,
                    generated: true,
                });
            }
            continue;
        }
        if let Some(quantifier) = definition.object_quantifier {
            if definition.complement
                || definition.object_self_role_id.is_some()
                || definition.object_cardinality.is_some()
                || definition.data_quantifier.is_some()
                || definition.data_cardinality.is_some()
                || !definition.data_expression_symbols.is_empty()
                || definition.operands.len() != 1
                || definition.provenance.is_empty()
            {
                return Err(EncodedValidationError::invariant(
                    "generated object-quantifier definition changed before emission",
                ));
            }
            let (filler_class_id, mut filler_negative) = class_boolean_operand_literal(
                model,
                class_domain,
                signature,
                &definition.operands[0],
                scope_maps,
                budget,
            )?;
            let kind = match (quantifier.kind, definition.polarity) {
                (ObjectQuantifierKind::Some, DefinitionPolarity::Negative) => {
                    ObjectConstraintKind::ExistentialAntecedent
                }
                (ObjectQuantifierKind::Some, DefinitionPolarity::Positive) => {
                    ObjectConstraintKind::ExistentialConsequent
                }
                (ObjectQuantifierKind::All, DefinitionPolarity::Negative) => {
                    filler_negative = !filler_negative;
                    ObjectConstraintKind::UniversalAntecedent
                }
                (ObjectQuantifierKind::All, DefinitionPolarity::Positive) => {
                    ObjectConstraintKind::UniversalConsequent
                }
            };
            for provenance in &definition.provenance {
                budget.claim_owned(size_of::<RawObjectConstraint>())?;
                object_constraints.try_reserve(1).map_err(|_| {
                    EncodedValidationError::resource(
                        "generated object-quantifier clause allocation failed",
                    )
                })?;
                object_constraints.push(RawObjectConstraint {
                    kind,
                    role_id: quantifier.role_id,
                    class: generated,
                    filler: Some(ClassLiteral {
                        class_id: filler_class_id,
                        negative: filler_negative,
                    }),
                    cardinality: None,
                    provenance: *provenance,
                    generated: true,
                });
            }
            continue;
        }
        if let Some(cardinality) = definition.object_cardinality {
            if definition.complement
                || definition.object_self_role_id.is_some()
                || definition.object_quantifier.is_some()
                || definition.data_quantifier.is_some()
                || definition.data_cardinality.is_some()
                || !definition.data_expression_symbols.is_empty()
                || definition.operands.len() != 1
                || definition.provenance.is_empty()
            {
                return Err(EncodedValidationError::invariant(
                    "generated object-cardinality definition changed before emission",
                ));
            }
            let (filler_class_id, filler_negative) = class_boolean_operand_literal(
                model,
                class_domain,
                signature,
                &definition.operands[0],
                scope_maps,
                budget,
            )?;
            for provenance in &definition.provenance {
                budget.claim_owned(size_of::<RawObjectConstraint>())?;
                object_constraints.try_reserve(1).map_err(|_| {
                    EncodedValidationError::resource(
                        "generated object-cardinality clause allocation failed",
                    )
                })?;
                object_constraints.push(RawObjectConstraint {
                    kind: match (cardinality.kind, definition.polarity) {
                        (ObjectCardinalityKind::Minimum, DefinitionPolarity::Positive) => {
                            ObjectConstraintKind::MinimumConsequent
                        }
                        (ObjectCardinalityKind::Minimum, DefinitionPolarity::Negative) => {
                            ObjectConstraintKind::MinimumAntecedent
                        }
                        (ObjectCardinalityKind::Maximum, DefinitionPolarity::Positive) => {
                            ObjectConstraintKind::MaximumConsequent
                        }
                        (ObjectCardinalityKind::Maximum, DefinitionPolarity::Negative) => {
                            ObjectConstraintKind::MaximumAntecedent
                        }
                    },
                    role_id: cardinality.role_id,
                    class: generated,
                    filler: Some(ClassLiteral {
                        class_id: filler_class_id,
                        negative: filler_negative,
                    }),
                    cardinality: Some(cardinality.cardinality),
                    provenance: *provenance,
                    generated: true,
                });
            }
            continue;
        }
        if let Some(quantifier) = &definition.data_quantifier {
            if definition.complement
                || definition.object_self_role_id.is_some()
                || definition.object_quantifier.is_some()
                || definition.object_cardinality.is_some()
                || definition.data_cardinality.is_some()
                || !definition.operands.is_empty()
                || definition.provenance.is_empty()
            {
                return Err(EncodedValidationError::invariant(
                    "generated data-quantifier definition changed before emission",
                ));
            }
            let mut filler =
                data_range_definition_literal(data_range_domain, &quantifier.filler, budget)?;
            let kind = match (quantifier.kind, definition.polarity) {
                (DataQuantifierKind::Some, DefinitionPolarity::Negative) => {
                    DataConstraintKind::ExistentialAntecedent
                }
                (DataQuantifierKind::Some, DefinitionPolarity::Positive) => {
                    DataConstraintKind::ExistentialConsequent
                }
                (DataQuantifierKind::All, DefinitionPolarity::Negative) => {
                    filler.negative = !filler.negative;
                    DataConstraintKind::UniversalAntecedent
                }
                (DataQuantifierKind::All, DefinitionPolarity::Positive) => {
                    DataConstraintKind::UniversalConsequent
                }
            };
            for provenance in &definition.provenance {
                budget.claim_owned(size_of::<RawDataConstraint>())?;
                data_constraints.try_reserve(1).map_err(|_| {
                    EncodedValidationError::resource(
                        "generated data-quantifier clause allocation failed",
                    )
                })?;
                data_constraints.push(RawDataConstraint {
                    kind,
                    role_id: quantifier.role_id,
                    class: generated,
                    filler,
                    cardinality: None,
                    provenance: *provenance,
                    generated: true,
                });
            }
            continue;
        }
        if let Some(cardinality) = &definition.data_cardinality {
            if definition.complement
                || definition.object_self_role_id.is_some()
                || definition.object_quantifier.is_some()
                || definition.object_cardinality.is_some()
                || definition.data_quantifier.is_some()
                || !definition.operands.is_empty()
                || definition.provenance.is_empty()
            {
                return Err(EncodedValidationError::invariant(
                    "generated data-cardinality definition changed before emission",
                ));
            }
            let filler =
                data_range_definition_literal(data_range_domain, &cardinality.filler, budget)?;
            for provenance in &definition.provenance {
                budget.claim_owned(size_of::<RawDataConstraint>())?;
                data_constraints.try_reserve(1).map_err(|_| {
                    EncodedValidationError::resource(
                        "generated data-cardinality clause allocation failed",
                    )
                })?;
                data_constraints.push(RawDataConstraint {
                    kind: match (cardinality.kind, definition.polarity) {
                        (DataCardinalityKind::Minimum, DefinitionPolarity::Positive) => {
                            DataConstraintKind::MinimumConsequent
                        }
                        (DataCardinalityKind::Minimum, DefinitionPolarity::Negative) => {
                            DataConstraintKind::MinimumAntecedent
                        }
                        (DataCardinalityKind::Maximum, DefinitionPolarity::Positive) => {
                            DataConstraintKind::MaximumConsequent
                        }
                        (DataCardinalityKind::Maximum, DefinitionPolarity::Negative) => {
                            DataConstraintKind::MaximumAntecedent
                        }
                    },
                    role_id: cardinality.role_id,
                    class: generated,
                    filler,
                    cardinality: Some(cardinality.cardinality),
                    provenance: *provenance,
                    generated: true,
                });
            }
            continue;
        }
        let mut operands = Vec::new();
        budget.claim_owned(
            definition
                .operands
                .len()
                .checked_mul(size_of::<ClassLiteral>())
                .ok_or_else(|| {
                    EncodedValidationError::resource(
                        "generated definition literal allocation overflowed",
                    )
                })?,
        )?;
        operands
            .try_reserve_exact(definition.operands.len())
            .map_err(|_| {
                EncodedValidationError::resource("generated definition literal allocation failed")
            })?;
        for operand in &definition.operands {
            let (class_id, negative) = class_boolean_operand_literal(
                model,
                class_domain,
                signature,
                operand,
                scope_maps,
                budget,
            )?;
            operands.push(ClassLiteral { class_id, negative });
        }
        if definition.complement {
            if operands.len() != 1 || definition.provenance.is_empty() {
                return Err(EncodedValidationError::invariant(
                    "generated class complement lost its operand or provenance",
                ));
            }
            let operand = operands[0];
            for provenance in &definition.provenance {
                budget.claim_owned(size_of::<RawEdge>())?;
                edges.try_reserve(1).map_err(|_| {
                    EncodedValidationError::resource(
                        "generated class complement edge allocation failed",
                    )
                })?;
                edges.push(match definition.polarity {
                    DefinitionPolarity::Positive => RawEdge {
                        sub_class: generated.class_id,
                        sub_negative: false,
                        super_class: operand.class_id,
                        super_negative: operand.negative,
                        provenance: *provenance,
                        generated: true,
                    },
                    DefinitionPolarity::Negative => RawEdge {
                        sub_class: operand.class_id,
                        sub_negative: operand.negative,
                        super_class: generated.class_id,
                        super_negative: false,
                        provenance: *provenance,
                        generated: true,
                    },
                });
            }
            continue;
        }
        if operands.len() < 2
            || definition.object_self_role_id.is_some()
            || definition.object_quantifier.is_some()
            || definition.object_cardinality.is_some()
            || definition.data_quantifier.is_some()
            || definition.data_cardinality.is_some()
            || !definition.data_expression_symbols.is_empty()
            || definition.provenance.is_empty()
        {
            return Err(EncodedValidationError::invariant(
                "generated Boolean definition lost operands or provenance",
            ));
        }
        for provenance in &definition.provenance {
            match (definition.polarity, definition.intersection) {
                (DefinitionPolarity::Positive, true) => {
                    for operand in &operands {
                        budget.claim_owned(size_of::<RawEdge>())?;
                        edges.try_reserve(1).map_err(|_| {
                            EncodedValidationError::resource(
                                "generated intersection edge allocation failed",
                            )
                        })?;
                        edges.push(RawEdge {
                            sub_class: generated.class_id,
                            sub_negative: false,
                            super_class: operand.class_id,
                            super_negative: operand.negative,
                            provenance: *provenance,
                            generated: true,
                        });
                    }
                }
                (DefinitionPolarity::Negative, false) => {
                    for operand in &operands {
                        budget.claim_owned(size_of::<RawEdge>())?;
                        edges.try_reserve(1).map_err(|_| {
                            EncodedValidationError::resource(
                                "generated union edge allocation failed",
                            )
                        })?;
                        edges.push(RawEdge {
                            sub_class: operand.class_id,
                            sub_negative: operand.negative,
                            super_class: generated.class_id,
                            super_negative: false,
                            provenance: *provenance,
                            generated: true,
                        });
                    }
                }
                (DefinitionPolarity::Positive, false) => push_raw_boolean_clause(
                    boolean_clauses,
                    vec![generated],
                    operands.clone(),
                    *provenance,
                    budget,
                )?,
                (DefinitionPolarity::Negative, true) => push_raw_boolean_clause(
                    boolean_clauses,
                    operands.clone(),
                    vec![generated],
                    *provenance,
                    budget,
                )?,
            }
        }
    }
    Ok(())
}

fn class_boolean_operand_literal<B: ByteSource>(
    model: &ValidatedModel<B>,
    class_domain: &DecodedSymbolDomain,
    signature: &[ClassSignatureBinding],
    operand: &ClassBooleanOperand,
    scope_maps: &[AnonymousScopeMap],
    budget: &mut PhaseBudget,
) -> EncodedResult<(u32, bool)> {
    match operand {
        ClassBooleanOperand::Atomic(selection) => atomic_class_selection_literal(
            model,
            class_domain,
            signature,
            *selection,
            scope_maps,
            budget,
        ),
        ClassBooleanOperand::Nominal { key, negative, .. } => {
            budget.claim_work(binary_search_work(class_domain.values.len()))?;
            let index = class_domain
                .values
                .binary_search_by(|candidate| candidate.key.cmp(key))
                .map_err(|_| {
                    EncodedValidationError::invariant("normalized object nominal disappeared")
                })?;
            Ok((
                u32::try_from(index).map_err(|_| {
                    EncodedValidationError::resource("normalized object nominal ID exceeds u32")
                })?,
                *negative,
            ))
        }
        ClassBooleanOperand::Generated { key, negative } => {
            budget.claim_work(binary_search_work(class_domain.values.len()))?;
            let index = class_domain
                .values
                .binary_search_by(|candidate| candidate.key.cmp(key))
                .map_err(|_| {
                    EncodedValidationError::invariant(
                        "recursive generated class operand disappeared",
                    )
                })?;
            Ok((
                u32::try_from(index).map_err(|_| {
                    EncodedValidationError::resource(
                        "recursive generated class operand ID exceeds u32",
                    )
                })?,
                *negative,
            ))
        }
    }
}

fn push_raw_boolean_clause(
    target: &mut Vec<RawBooleanClause>,
    body: Vec<ClassLiteral>,
    head: Vec<ClassLiteral>,
    provenance: [u8; 32],
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    budget.claim_owned(size_of::<RawBooleanClause>())?;
    target.try_reserve(1).map_err(|_| {
        EncodedValidationError::resource("generated Boolean clause allocation failed")
    })?;
    target.push(RawBooleanClause {
        body,
        head,
        provenance,
        generated: true,
    });
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn emit_data_boolean_definitions<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    data_range_domain: &DecodedSymbolDomain,
    definitions: &[DataBooleanDefinition],
    scope_maps: &[AnonymousScopeMap],
    clauses: &mut Vec<RawDataBooleanClause>,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    for definition in definitions {
        budget.claim_work(binary_search_work(data_range_domain.values.len()))?;
        let generated_index = data_range_domain
            .values
            .binary_search_by(|candidate| candidate.key.cmp(&definition.generated_key))
            .map_err(|_| {
                EncodedValidationError::invariant("generated data definition symbol disappeared")
            })?;
        let generated = DataRangeLiteral {
            range_id: u32::try_from(generated_index).map_err(|_| {
                EncodedValidationError::resource("generated data definition range ID exceeds u32")
            })?,
            negative: false,
        };
        let mut operands = Vec::new();
        budget.claim_owned(
            definition
                .operands
                .len()
                .checked_mul(size_of::<DataRangeLiteral>())
                .ok_or_else(|| {
                    EncodedValidationError::resource(
                        "generated data definition literal allocation overflowed",
                    )
                })?,
        )?;
        operands
            .try_reserve_exact(definition.operands.len())
            .map_err(|_| {
                EncodedValidationError::resource(
                    "generated data definition literal allocation failed",
                )
            })?;
        for operand in &definition.operands {
            operands.push(data_boolean_operand_literal(
                model,
                symbols,
                data_range_domain,
                operand,
                scope_maps,
                budget,
            )?);
        }
        if operands.len() < 2 || definition.provenance.is_empty() {
            return Err(EncodedValidationError::invariant(
                "generated data Boolean definition lost operands or provenance",
            ));
        }
        for provenance in &definition.provenance {
            match (definition.polarity, definition.intersection) {
                (DefinitionPolarity::Positive, true) => {
                    for operand in &operands {
                        push_raw_data_boolean_clause(
                            clauses,
                            vec![generated],
                            vec![*operand],
                            *provenance,
                            true,
                            budget,
                        )?;
                    }
                }
                (DefinitionPolarity::Negative, false) => {
                    for operand in &operands {
                        push_raw_data_boolean_clause(
                            clauses,
                            vec![*operand],
                            vec![generated],
                            *provenance,
                            true,
                            budget,
                        )?;
                    }
                }
                (DefinitionPolarity::Positive, false) => push_raw_data_boolean_clause(
                    clauses,
                    vec![generated],
                    operands.clone(),
                    *provenance,
                    true,
                    budget,
                )?,
                (DefinitionPolarity::Negative, true) => push_raw_data_boolean_clause(
                    clauses,
                    operands.clone(),
                    vec![generated],
                    *provenance,
                    true,
                    budget,
                )?,
            }
        }
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn data_boolean_operand_literal<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    data_range_domain: &DecodedSymbolDomain,
    operand: &DataBooleanOperand,
    scope_maps: &[AnonymousScopeMap],
    budget: &mut PhaseBudget,
) -> EncodedResult<DataRangeLiteral> {
    match operand {
        DataBooleanOperand::Atomic(selection) => atomic_data_range_selection_literal(
            model,
            symbols,
            data_range_domain,
            *selection,
            scope_maps,
            budget,
        ),
        DataBooleanOperand::Generated { key } => {
            budget.claim_work(binary_search_work(data_range_domain.values.len()))?;
            let index = data_range_domain
                .values
                .binary_search_by(|candidate| candidate.key.cmp(key))
                .map_err(|_| {
                    EncodedValidationError::invariant(
                        "nested generated data definition symbol disappeared",
                    )
                })?;
            Ok(DataRangeLiteral {
                range_id: u32::try_from(index).map_err(|_| {
                    EncodedValidationError::resource(
                        "nested generated data definition range ID exceeds u32",
                    )
                })?,
                negative: false,
            })
        }
    }
}

fn push_raw_data_boolean_clause(
    target: &mut Vec<RawDataBooleanClause>,
    body: Vec<DataRangeLiteral>,
    head: Vec<DataRangeLiteral>,
    provenance: [u8; 32],
    generated: bool,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    budget.claim_owned(
        body.len()
            .checked_add(head.len())
            .and_then(|value| value.checked_mul(size_of::<DataRangeLiteral>()))
            .and_then(|value| value.checked_add(size_of::<RawDataBooleanClause>()))
            .ok_or_else(|| {
                EncodedValidationError::resource("data Boolean clause allocation overflowed")
            })?,
    )?;
    target
        .try_reserve(1)
        .map_err(|_| EncodedValidationError::resource("data Boolean clause allocation failed"))?;
    target.push(RawDataBooleanClause {
        body,
        head,
        provenance,
        generated,
    });
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
            edge.generated,
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
                previous.generated |= edge.generated;
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
            generated: edge.generated,
        });
    }
    Ok(normalized)
}

fn normalize_boolean_clauses(
    mut raw: Vec<RawBooleanClause>,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<NormalizedBooleanClause>> {
    for clause in &mut raw {
        budget.claim_work(
            sort_work(clause.body.len())
                .checked_add(sort_work(clause.head.len()))
                .ok_or_else(|| {
                    EncodedValidationError::resource("generated Boolean sort work overflowed")
                })?,
        )?;
        clause.body.sort_unstable();
        clause.body.dedup();
        clause.head.sort_unstable();
        clause.head.dedup();
        if clause.body.is_empty() || clause.head.is_empty() {
            return Err(EncodedValidationError::invariant(
                "generated Boolean clause lost one of its sides",
            ));
        }
    }
    budget.claim_work(sort_work(raw.len()))?;
    raw.sort_by(|left, right| {
        left.body
            .cmp(&right.body)
            .then_with(|| left.head.cmp(&right.head))
            .then_with(|| left.provenance.cmp(&right.provenance))
            .then_with(|| left.generated.cmp(&right.generated))
    });
    let mut normalized = Vec::<NormalizedBooleanClause>::new();
    for clause in raw {
        budget.claim_work(1)?;
        if let Some(previous) = normalized.last_mut() {
            if previous.body == clause.body && previous.head == clause.head {
                previous.generated |= clause.generated;
                if previous.provenance.last() != Some(&clause.provenance) {
                    budget.claim_owned(size_of::<[u8; 32]>())?;
                    previous.provenance.try_reserve(1).map_err(|_| {
                        EncodedValidationError::resource(
                            "generated Boolean provenance allocation failed",
                        )
                    })?;
                    previous.provenance.push(clause.provenance);
                }
                continue;
            }
        }
        budget.claim_owned(size_of::<NormalizedBooleanClause>() + size_of::<[u8; 32]>())?;
        let mut provenance = Vec::new();
        provenance.try_reserve_exact(1).map_err(|_| {
            EncodedValidationError::resource("generated Boolean provenance allocation failed")
        })?;
        provenance.push(clause.provenance);
        normalized.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("normalized Boolean clause allocation failed")
        })?;
        normalized.push(NormalizedBooleanClause {
            body: clause.body,
            head: clause.head,
            provenance,
            generated: clause.generated,
        });
    }
    Ok(normalized)
}

fn normalize_data_boolean_clauses(
    mut raw: Vec<RawDataBooleanClause>,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<NormalizedDataBooleanClause>> {
    for clause in &mut raw {
        budget.claim_work(
            sort_work(clause.body.len())
                .checked_add(sort_work(clause.head.len()))
                .ok_or_else(|| {
                    EncodedValidationError::resource("data Boolean sort work overflowed")
                })?,
        )?;
        clause.body.sort_unstable();
        clause.body.dedup();
        clause.head.sort_unstable();
        clause.head.dedup();
        if clause.body.is_empty() || clause.head.is_empty() {
            return Err(EncodedValidationError::invariant(
                "data Boolean clause lost one of its sides",
            ));
        }
    }
    budget.claim_work(sort_work(raw.len()))?;
    raw.sort_by(|left, right| {
        left.body
            .cmp(&right.body)
            .then_with(|| left.head.cmp(&right.head))
            .then_with(|| left.provenance.cmp(&right.provenance))
            .then_with(|| left.generated.cmp(&right.generated))
    });
    let mut normalized = Vec::<NormalizedDataBooleanClause>::new();
    for clause in raw {
        budget.claim_work(1)?;
        if let Some(previous) = normalized.last_mut() {
            if previous.body == clause.body && previous.head == clause.head {
                previous.generated |= clause.generated;
                if previous.provenance.last() != Some(&clause.provenance) {
                    budget.claim_owned(size_of::<[u8; 32]>())?;
                    previous.provenance.try_reserve(1).map_err(|_| {
                        EncodedValidationError::resource(
                            "data Boolean provenance allocation failed",
                        )
                    })?;
                    previous.provenance.push(clause.provenance);
                }
                continue;
            }
        }
        budget.claim_owned(size_of::<NormalizedDataBooleanClause>() + size_of::<[u8; 32]>())?;
        let mut provenance = Vec::new();
        provenance.try_reserve_exact(1).map_err(|_| {
            EncodedValidationError::resource("data Boolean provenance allocation failed")
        })?;
        provenance.push(clause.provenance);
        normalized.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("normalized data Boolean clause allocation failed")
        })?;
        normalized.push(NormalizedDataBooleanClause {
            body: clause.body,
            head: clause.head,
            provenance,
            generated: clause.generated,
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
                && previous.filler == constraint.filler
                && previous.cardinality == constraint.cardinality
                && previous.generated == constraint.generated
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
            filler: constraint.filler,
            cardinality: constraint.cardinality,
            provenance,
            generated: constraint.generated,
        });
    }
    Ok(normalized)
}

fn normalize_data_constraints(
    mut raw: Vec<RawDataConstraint>,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<NormalizedDataConstraint>> {
    budget.claim_work(sort_work(raw.len()))?;
    raw.sort_unstable();
    let mut normalized = Vec::<NormalizedDataConstraint>::new();
    for constraint in raw {
        budget.claim_work(1)?;
        if let Some(previous) = normalized.last_mut() {
            if previous.kind == constraint.kind
                && previous.role_id == constraint.role_id
                && previous.class == constraint.class
                && previous.filler == constraint.filler
                && previous.cardinality == constraint.cardinality
                && previous.generated == constraint.generated
            {
                if previous.provenance.last() != Some(&constraint.provenance) {
                    budget.claim_owned(size_of::<[u8; 32]>())?;
                    previous.provenance.try_reserve(1).map_err(|_| {
                        EncodedValidationError::resource(
                            "data-quantifier constraint provenance allocation failed",
                        )
                    })?;
                    previous.provenance.push(constraint.provenance);
                }
                continue;
            }
        }
        budget.claim_owned(size_of::<NormalizedDataConstraint>() + size_of::<[u8; 32]>())?;
        normalized.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource(
                "normalized data-quantifier constraint allocation failed",
            )
        })?;
        let mut provenance = Vec::new();
        provenance.try_reserve_exact(1).map_err(|_| {
            EncodedValidationError::resource(
                "data-quantifier constraint provenance allocation failed",
            )
        })?;
        provenance.push(constraint.provenance);
        normalized.push(NormalizedDataConstraint {
            kind: constraint.kind,
            role_id: constraint.role_id,
            class: constraint.class,
            filler: constraint.filler,
            cardinality: constraint.cardinality,
            provenance,
            generated: constraint.generated,
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
    boolean_clauses: &[NormalizedBooleanClause],
    disjoints: &[NormalizedDisjoint],
    object_constraints: &[NormalizedObjectConstraint],
    data_constraints: &[NormalizedDataConstraint],
    object_characteristics: &[NormalizedObjectCharacteristic],
    data_domains: &[NormalizedDataDomain],
    data_ranges: &[NormalizedDataRange],
    data_boolean_clauses: &[NormalizedDataBooleanClause],
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
                generated: edge.generated,
            },
            budget,
        )?;
    }
    for clause in boolean_clauses {
        push_provenance_key(
            &mut keys,
            ProvenanceKey {
                source_sha256: clause.provenance.clone(),
                generated: clause.generated,
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
                generated: constraint.generated,
            },
            budget,
        )?;
    }
    for constraint in data_constraints {
        push_provenance_key(
            &mut keys,
            ProvenanceKey {
                source_sha256: constraint.provenance.clone(),
                generated: constraint.generated,
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
    for clause in data_boolean_clauses {
        push_provenance_key(
            &mut keys,
            ProvenanceKey {
                source_sha256: clause.provenance.clone(),
                generated: clause.generated,
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
    AtLeastObject {
        cardinality: u32,
        role_id: u32,
        filler: ClassLiteral,
    },
    AtLeastData {
        cardinality: u32,
        role_id: u32,
        filler: DataRangeLiteral,
    },
    AnnotatedEquality {
        cardinality: u32,
        role_id: u32,
        filler: ClassLiteral,
    },
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
type AtLeastObjectPredicateIndex = Vec<((u32, u32, ClassLiteral), u32)>;
type AtLeastDataPredicateIndex = Vec<((u32, u32, DataRangeLiteral), u32)>;
type AnnotatedEqualityPredicateIndex = Vec<((u32, u32, ClassLiteral), u32)>;
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
    boolean_clauses: &[NormalizedBooleanClause],
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
    }) || boolean_clauses.iter().any(|clause| {
        clause.body.iter().chain(&clause.head).any(|literal| {
            literal.negative && nominal_binding(bindings, literal.class_id).is_some()
        })
    }) || disjoints.iter().any(|disjoint| {
        disjoint.classes.iter().any(|literal| {
            literal.negative && nominal_binding(bindings, literal.class_id).is_some()
        })
    }) || object_constraints.iter().any(|constraint| {
        [Some(constraint.class), constraint.filler]
            .into_iter()
            .flatten()
            .any(|literal| {
                literal.negative && nominal_binding(bindings, literal.class_id).is_some()
            })
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
    AtLeastObjectPredicateIndex,
    AtLeastDataPredicateIndex,
    AnnotatedEqualityPredicateIndex,
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
    boolean_clauses: &[NormalizedBooleanClause],
    disjoints: &[NormalizedDisjoint],
    object_constraints: &[NormalizedObjectConstraint],
    data_constraints: &[NormalizedDataConstraint],
    object_characteristics: &[NormalizedObjectCharacteristic],
    data_domains: &[NormalizedDataDomain],
    data_ranges: &[NormalizedDataRange],
    data_boolean_clauses: &[NormalizedDataBooleanClause],
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
        || object_constraints.iter().any(|value| {
            matches!(
                value.kind,
                ObjectConstraintKind::UniversalAntecedent | ObjectConstraintKind::MaximumAntecedent
            )
        })
        || data_constraints.iter().any(|value| {
            matches!(
                value.kind,
                DataConstraintKind::UniversalAntecedent | DataConstraintKind::MaximumAntecedent
            )
        })
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
    for constraint in data_constraints
        .iter()
        .filter(|constraint| constraint.class.negative)
    {
        push_u32(
            &mut negative_class_ids,
            constraint.class.class_id,
            "data-quantifier complement clause class",
            budget,
        )?;
    }
    for clause in boolean_clauses {
        for literal in clause.body.iter().chain(&clause.head) {
            push_u32(
                &mut class_ids,
                literal.class_id,
                "Boolean clause class",
                budget,
            )?;
            if literal.negative {
                push_u32(
                    &mut negative_class_ids,
                    literal.class_id,
                    "negated Boolean clause class",
                    budget,
                )?;
            }
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
        for literal in [Some(constraint.class), constraint.filler]
            .into_iter()
            .flatten()
        {
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
    for constraint in data_constraints {
        push_u32(
            &mut class_ids,
            constraint.class.class_id,
            "data-quantifier predicate class",
            budget,
        )?;
        if constraint.class.negative {
            push_u32(
                &mut negative_class_ids,
                constraint.class.class_id,
                "negated data-quantifier predicate class",
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
    if !data_functionalities.is_empty()
        || data_constraints
            .iter()
            .any(|constraint| constraint.kind == DataConstraintKind::MaximumConsequent)
    {
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
    if !inequalities.is_empty()
        || has_negative_nominals
        || object_constraints.iter().any(|constraint| {
            (matches!(
                constraint.kind,
                ObjectConstraintKind::MinimumAntecedent | ObjectConstraintKind::MinimumConsequent
            ) && constraint.cardinality.is_some_and(|value| value > 1))
                || (constraint.kind == ObjectConstraintKind::MaximumAntecedent
                    && constraint.cardinality.is_some())
        })
    {
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
    if !negative_data_facts.is_empty()
        || keys.iter().any(|key| !key.data_role_ids.is_empty())
        || data_constraints.iter().any(|constraint| {
            (matches!(
                constraint.kind,
                DataConstraintKind::MinimumAntecedent | DataConstraintKind::MinimumConsequent
            ) && constraint.cardinality.is_some_and(|value| value > 1))
                || (constraint.kind == DataConstraintKind::MaximumAntecedent
                    && constraint.cardinality.is_some())
        })
    {
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
    if !keys.is_empty()
        || object_constraints.iter().any(|constraint| {
            constraint.kind == ObjectConstraintKind::MaximumConsequent
                && constraint.cardinality.is_some_and(|value| value > 1)
        })
    {
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
    let mut at_least_objects = Vec::<(u32, u32, ClassLiteral)>::new();
    for constraint in object_constraints.iter().filter(|constraint| {
        matches!(
            constraint.kind,
            ObjectConstraintKind::ExistentialConsequent
                | ObjectConstraintKind::UniversalAntecedent
                | ObjectConstraintKind::MinimumAntecedent
                | ObjectConstraintKind::MinimumConsequent
                | ObjectConstraintKind::MaximumAntecedent
        )
    }) {
        let filler = constraint.filler.ok_or_else(|| {
            EncodedValidationError::invariant("object at-least constraint lost its filler literal")
        })?;
        let cardinality = match constraint.kind {
            ObjectConstraintKind::ExistentialConsequent
            | ObjectConstraintKind::UniversalAntecedent => {
                if constraint.cardinality.is_some() {
                    return Err(EncodedValidationError::invariant(
                        "object quantifier unexpectedly carries cardinality metadata",
                    ));
                }
                1
            }
            ObjectConstraintKind::MinimumAntecedent | ObjectConstraintKind::MinimumConsequent => {
                let cardinality = constraint.cardinality.ok_or_else(|| {
                    EncodedValidationError::invariant(
                        "object-minimum constraint lost its cardinality",
                    )
                })?;
                if cardinality <= 1 {
                    return Err(EncodedValidationError::invariant(
                        "object-minimum constraint did not retain a nontrivial cardinality",
                    ));
                }
                cardinality
            }
            ObjectConstraintKind::MaximumAntecedent => constraint
                .cardinality
                .ok_or_else(|| {
                    EncodedValidationError::invariant(
                        "object-maximum constraint lost its cardinality",
                    )
                })?
                .checked_add(1)
                .ok_or_else(|| {
                    EncodedValidationError::invariant(
                        "object-maximum antecedent cardinality overflowed",
                    )
                })?,
            _ => {
                return Err(EncodedValidationError::invariant(
                    "non-cardinality object constraint reached at-least collection",
                ));
            }
        };
        budget.claim_owned(size_of::<(u32, u32, ClassLiteral)>())?;
        at_least_objects.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("object at-least predicate allocation failed")
        })?;
        at_least_objects.push((cardinality, constraint.role_id, filler));
    }
    budget.claim_work(sort_work(at_least_objects.len()))?;
    at_least_objects.sort_unstable();
    at_least_objects.dedup();
    for (cardinality, role_id, filler) in at_least_objects {
        let filler_key = class_literal_predicate_key(nominal_bindings, filler);
        let key = at_least_object_predicate_key(cardinality, role_id, &filler_key, budget)?;
        budget.claim_owned(size_of::<PendingPredicate>() + key.len())?;
        ordered.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("object at-least predicate allocation failed")
        })?;
        ordered.push(PendingPredicate {
            key,
            owner: PredicateOwner::AtLeastObject {
                cardinality,
                role_id,
                filler,
            },
        });
    }
    let mut at_least_data = Vec::<(u32, u32, DataRangeLiteral)>::new();
    for constraint in data_constraints.iter().filter(|constraint| {
        matches!(
            constraint.kind,
            DataConstraintKind::ExistentialConsequent
                | DataConstraintKind::UniversalAntecedent
                | DataConstraintKind::MinimumAntecedent
                | DataConstraintKind::MinimumConsequent
                | DataConstraintKind::MaximumAntecedent
        )
    }) {
        let cardinality = match constraint.kind {
            DataConstraintKind::ExistentialConsequent | DataConstraintKind::UniversalAntecedent => {
                if constraint.cardinality.is_some() {
                    return Err(EncodedValidationError::invariant(
                        "data quantifier unexpectedly carries cardinality metadata",
                    ));
                }
                1
            }
            DataConstraintKind::MinimumAntecedent | DataConstraintKind::MinimumConsequent => {
                let cardinality = constraint.cardinality.ok_or_else(|| {
                    EncodedValidationError::invariant(
                        "data-minimum constraint lost its cardinality",
                    )
                })?;
                if cardinality <= 1 {
                    return Err(EncodedValidationError::invariant(
                        "data-minimum constraint did not retain a nontrivial cardinality",
                    ));
                }
                cardinality
            }
            DataConstraintKind::MaximumAntecedent => constraint
                .cardinality
                .ok_or_else(|| {
                    EncodedValidationError::invariant(
                        "data-maximum constraint lost its cardinality",
                    )
                })?
                .checked_add(1)
                .ok_or_else(|| {
                    EncodedValidationError::invariant(
                        "data-maximum antecedent cardinality overflowed",
                    )
                })?,
            _ => {
                return Err(EncodedValidationError::invariant(
                    "non-cardinality data constraint reached at-least collection",
                ));
            }
        };
        budget.claim_owned(size_of::<(u32, u32, DataRangeLiteral)>())?;
        at_least_data.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("data at-least predicate allocation failed")
        })?;
        at_least_data.push((cardinality, constraint.role_id, constraint.filler));
    }
    budget.claim_work(sort_work(at_least_data.len()))?;
    at_least_data.sort_unstable();
    at_least_data.dedup();
    for (cardinality, role_id, filler) in at_least_data {
        let filler_key = data_range_literal_predicate_key(filler);
        let key = at_least_data_predicate_key(cardinality, role_id, &filler_key, budget)?;
        budget.claim_owned(size_of::<PendingPredicate>() + key.len())?;
        ordered.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("data at-least predicate allocation failed")
        })?;
        ordered.push(PendingPredicate {
            key,
            owner: PredicateOwner::AtLeastData {
                cardinality,
                role_id,
                filler,
            },
        });
    }
    let mut annotated_equalities = Vec::<(u32, u32, ClassLiteral)>::new();
    for constraint in object_constraints
        .iter()
        .filter(|constraint| constraint.kind == ObjectConstraintKind::MaximumConsequent)
    {
        let filler = constraint.filler.ok_or_else(|| {
            EncodedValidationError::invariant("object at-most constraint lost its filler literal")
        })?;
        let cardinality = constraint.cardinality.ok_or_else(|| {
            EncodedValidationError::invariant("object at-most constraint lost its cardinality")
        })?;
        if cardinality == 0 {
            return Err(EncodedValidationError::invariant(
                "zero object at-most constraint did not normalize to a universal restriction",
            ));
        }
        budget.claim_owned(size_of::<(u32, u32, ClassLiteral)>())?;
        annotated_equalities.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("annotated-equality predicate allocation failed")
        })?;
        annotated_equalities.push((cardinality, constraint.role_id, filler));
    }
    budget.claim_work(sort_work(annotated_equalities.len()))?;
    annotated_equalities.sort_unstable();
    annotated_equalities.dedup();
    for (cardinality, role_id, filler) in annotated_equalities {
        let filler_key = class_literal_predicate_key(nominal_bindings, filler);
        let key = annotated_equality_predicate_key(cardinality, role_id, &filler_key, budget)?;
        budget.claim_owned(size_of::<PendingPredicate>() + key.len())?;
        ordered.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("annotated-equality predicate allocation failed")
        })?;
        ordered.push(PendingPredicate {
            key,
            owner: PredicateOwner::AnnotatedEquality {
                cardinality,
                role_id,
                filler,
            },
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
    for constraint in data_constraints {
        push_u32(
            &mut data_role_ids,
            constraint.role_id,
            "predicate data-quantifier role",
            budget,
        )?;
    }
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
    for constraint in data_constraints
        .iter()
        .filter(|constraint| constraint.filler.negative)
    {
        push_u32(
            &mut negative_data_range_ids,
            constraint.filler.range_id,
            "complement clause data-quantifier range",
            budget,
        )?;
    }
    for constraint in data_constraints {
        push_u32(
            &mut data_range_ids,
            constraint.filler.range_id,
            "predicate data-quantifier range",
            budget,
        )?;
        if constraint.filler.negative {
            push_u32(
                &mut negative_data_range_ids,
                constraint.filler.range_id,
                "negated predicate data-quantifier range",
                budget,
            )?;
        }
    }
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
    for clause in data_boolean_clauses {
        for range in clause.body.iter().chain(&clause.head) {
            push_u32(
                &mut data_range_ids,
                range.range_id,
                "predicate data Boolean range",
                budget,
            )?;
            if range.negative {
                push_u32(
                    &mut negative_data_range_ids,
                    range.range_id,
                    "negated predicate data Boolean range",
                    budget,
                )?;
            }
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
    let mut pending_class_predicates = Vec::<(ClassLiteral, u32)>::new();
    budget.claim_owned(
        ordered
            .len()
            .checked_mul(size_of::<(ClassLiteral, u32)>())
            .ok_or_else(|| {
                EncodedValidationError::resource(
                    "pending class-predicate index allocation overflowed",
                )
            })?,
    )?;
    pending_class_predicates
        .try_reserve_exact(ordered.len())
        .map_err(|_| {
            EncodedValidationError::resource("pending class-predicate index allocation failed")
        })?;
    for (identifier, pending) in ordered.iter().enumerate() {
        let literal = match &pending.owner {
            PredicateOwner::Concept(class_id) | PredicateOwner::Nominal { class_id, .. } => {
                Some(ClassLiteral {
                    class_id: *class_id,
                    negative: false,
                })
            }
            PredicateOwner::NegatedConcept(class_id)
            | PredicateOwner::NegatedNominal { class_id, .. } => Some(ClassLiteral {
                class_id: *class_id,
                negative: true,
            }),
            _ => None,
        };
        if let Some(literal) = literal {
            pending_class_predicates.push((
                literal,
                u32::try_from(identifier).map_err(|_| {
                    EncodedValidationError::resource("pending predicate ID exceeds u32")
                })?,
            ));
        }
    }
    budget.claim_work(sort_work(pending_class_predicates.len()))?;
    pending_class_predicates.sort_unstable_by_key(|(literal, _)| *literal);

    let mut pending_data_range_predicates = Vec::<(DataRangeLiteral, u32)>::new();
    budget.claim_owned(
        ordered
            .len()
            .checked_mul(size_of::<(DataRangeLiteral, u32)>())
            .ok_or_else(|| {
                EncodedValidationError::resource(
                    "pending data-range predicate index allocation overflowed",
                )
            })?,
    )?;
    pending_data_range_predicates
        .try_reserve_exact(ordered.len())
        .map_err(|_| {
            EncodedValidationError::resource("pending data-range predicate index allocation failed")
        })?;
    for (identifier, pending) in ordered.iter().enumerate() {
        let literal = match &pending.owner {
            PredicateOwner::DataRange(range_id) => Some(DataRangeLiteral {
                range_id: *range_id,
                negative: false,
            }),
            PredicateOwner::NegatedDataRange(range_id) => Some(DataRangeLiteral {
                range_id: *range_id,
                negative: true,
            }),
            _ => None,
        };
        if let Some(literal) = literal {
            pending_data_range_predicates.push((
                literal,
                u32::try_from(identifier).map_err(|_| {
                    EncodedValidationError::resource("pending predicate ID exceeds u32")
                })?,
            ));
        }
    }
    budget.claim_work(sort_work(pending_data_range_predicates.len()))?;
    pending_data_range_predicates.sort_unstable_by_key(|(literal, _)| *literal);

    let mut predicates = Vec::new();
    let mut predicate_by_class = Vec::new();
    let mut predicate_by_negative_class = Vec::new();
    let mut predicate_by_object_role = Vec::new();
    let mut predicate_by_negative_object_role = Vec::new();
    let mut at_least_object_predicates = Vec::new();
    let mut at_least_data_predicates = Vec::new();
    let mut annotated_equality_predicates = Vec::new();
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
    budget.claim_owned(
        ordered
            .len()
            .checked_mul(size_of::<((u32, u32, ClassLiteral), u32)>())
            .ok_or_else(|| {
                EncodedValidationError::resource(
                    "object at-least predicate index allocation overflowed",
                )
            })?,
    )?;
    at_least_object_predicates
        .try_reserve_exact(ordered.len())
        .map_err(|_| {
            EncodedValidationError::resource("object at-least predicate index allocation failed")
        })?;
    budget.claim_owned(
        ordered
            .len()
            .checked_mul(size_of::<((u32, u32, DataRangeLiteral), u32)>())
            .ok_or_else(|| {
                EncodedValidationError::resource(
                    "data at-least predicate index allocation overflowed",
                )
            })?,
    )?;
    at_least_data_predicates
        .try_reserve_exact(ordered.len())
        .map_err(|_| {
            EncodedValidationError::resource("data at-least predicate index allocation failed")
        })?;
    budget.claim_owned(
        ordered
            .len()
            .checked_mul(size_of::<((u32, u32, ClassLiteral), u32)>())
            .ok_or_else(|| {
                EncodedValidationError::resource(
                    "annotated-equality predicate index allocation overflowed",
                )
            })?,
    )?;
    annotated_equality_predicates
        .try_reserve_exact(ordered.len())
        .map_err(|_| {
            EncodedValidationError::resource("annotated-equality predicate index allocation failed")
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
            PredicateOwner::AtLeastObject {
                cardinality,
                role_id,
                filler,
            } => {
                let filler_predicate_id = pending_class_predicates
                    .binary_search_by_key(&filler, |(literal, _)| *literal)
                    .ok()
                    .map(|position| pending_class_predicates[position].1)
                    .ok_or_else(|| {
                        EncodedValidationError::invariant(
                            "object at-least filler predicate is missing",
                        )
                    })?;
                predicates.push(DecodedPredicate {
                    predicate_id,
                    kind: PredicateKind::AtLeastObject,
                    argument_sorts: vec![TermSort::Object],
                    symbol_id: None,
                    role_id: Some(role_id),
                    cardinality: Some(cardinality),
                    filler_predicate_id: Some(filler_predicate_id),
                    annotation: Vec::new(),
                    internal_key: None,
                });
                at_least_object_predicates.push(((cardinality, role_id, filler), predicate_id));
            }
            PredicateOwner::AtLeastData {
                cardinality,
                role_id,
                filler,
            } => {
                let filler_predicate_id = pending_data_range_predicates
                    .binary_search_by_key(&filler, |(literal, _)| *literal)
                    .ok()
                    .map(|position| pending_data_range_predicates[position].1)
                    .ok_or_else(|| {
                        EncodedValidationError::invariant(
                            "data at-least filler predicate is missing",
                        )
                    })?;
                budget.claim_owned(size_of::<u32>())?;
                predicates.push(DecodedPredicate {
                    predicate_id,
                    kind: PredicateKind::AtLeastData,
                    argument_sorts: vec![TermSort::Object],
                    symbol_id: None,
                    role_id: Some(role_id),
                    cardinality: Some(cardinality),
                    filler_predicate_id: Some(filler_predicate_id),
                    annotation: vec![role_id],
                    internal_key: None,
                });
                at_least_data_predicates.push(((cardinality, role_id, filler), predicate_id));
            }
            PredicateOwner::AnnotatedEquality {
                cardinality,
                role_id,
                filler,
            } => {
                let filler_predicate_id = pending_class_predicates
                    .binary_search_by_key(&filler, |(literal, _)| *literal)
                    .ok()
                    .map(|position| pending_class_predicates[position].1)
                    .ok_or_else(|| {
                        EncodedValidationError::invariant(
                            "annotated-equality filler predicate is missing",
                        )
                    })?;
                budget.claim_owned(2 * size_of::<TermSort>())?;
                predicates.push(DecodedPredicate {
                    predicate_id,
                    kind: PredicateKind::AnnotatedEquality,
                    argument_sorts: vec![TermSort::Object; 3],
                    symbol_id: None,
                    role_id: Some(role_id),
                    cardinality: Some(cardinality),
                    filler_predicate_id: Some(filler_predicate_id),
                    annotation: Vec::new(),
                    internal_key: None,
                });
                annotated_equality_predicates.push(((cardinality, role_id, filler), predicate_id));
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
    at_least_object_predicates.sort_unstable_by_key(|(key, _)| *key);
    at_least_data_predicates.sort_unstable_by_key(|(key, _)| *key);
    annotated_equality_predicates.sort_unstable_by_key(|(key, _)| *key);
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
        at_least_object_predicates,
        at_least_data_predicates,
        annotated_equality_predicates,
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
    boolean_clauses: &[NormalizedBooleanClause],
    disjoints: &[NormalizedDisjoint],
    object_constraints: &[NormalizedObjectConstraint],
    data_constraints: &[NormalizedDataConstraint],
    object_characteristics: &[NormalizedObjectCharacteristic],
    data_domains: &[NormalizedDataDomain],
    data_ranges: &[NormalizedDataRange],
    data_boolean_clauses: &[NormalizedDataBooleanClause],
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
    at_least_object_predicates: &AtLeastObjectPredicateIndex,
    at_least_data_predicates: &AtLeastDataPredicateIndex,
    annotated_equality_predicates: &AnnotatedEqualityPredicateIndex,
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
    for clause in boolean_clauses {
        for literal in clause
            .body
            .iter()
            .chain(&clause.head)
            .filter(|literal| literal.negative)
        {
            push_u32(
                &mut negative_class_ids,
                literal.class_id,
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
    for constraint in object_constraints {
        for literal in [Some(constraint.class), constraint.filler]
            .into_iter()
            .flatten()
            .filter(|literal| literal.negative)
        {
            push_u32(
                &mut negative_class_ids,
                literal.class_id,
                "complement clause class",
                budget,
            )?;
        }
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
    for constraint in data_constraints
        .iter()
        .filter(|constraint| constraint.filler.negative)
    {
        push_u32(
            &mut negative_data_range_ids,
            constraint.filler.range_id,
            "complement clause data-quantifier range",
            budget,
        )?;
    }
    for range in data_ranges.iter().filter(|range| range.range.negative) {
        push_u32(
            &mut negative_data_range_ids,
            range.range.range_id,
            "complement clause data range",
            budget,
        )?;
    }
    for clause in data_boolean_clauses {
        for range in clause
            .body
            .iter()
            .chain(&clause.head)
            .filter(|range| range.negative)
        {
            push_u32(
                &mut negative_data_range_ids,
                range.range_id,
                "complement clause data Boolean range",
                budget,
            )?;
        }
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
        .checked_add(boolean_clauses.len())
        .and_then(|value| value.checked_add(data_boolean_clauses.len()))
        .and_then(|value| value.checked_add(1))
        .and_then(|value| value.checked_add(object_constraints.len()))
        .and_then(|value| value.checked_add(data_constraints.len()))
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
        let provenance = provenance_id(provenance_keys, &edge.provenance, edge.generated)?;
        push_clause(
            &mut ordered,
            &[body],
            &[head],
            provenance,
            scalar_predicate_ids,
            budget,
        )?;
    }
    for clause in boolean_clauses {
        let mut body = Vec::new();
        let mut head = Vec::new();
        budget.claim_owned(
            clause
                .body
                .len()
                .checked_add(clause.head.len())
                .and_then(|value| value.checked_mul(size_of::<u32>()))
                .ok_or_else(|| {
                    EncodedValidationError::resource(
                        "generated Boolean predicate allocation overflowed",
                    )
                })?,
        )?;
        body.try_reserve_exact(clause.body.len()).map_err(|_| {
            EncodedValidationError::resource("generated Boolean body allocation failed")
        })?;
        head.try_reserve_exact(clause.head.len()).map_err(|_| {
            EncodedValidationError::resource("generated Boolean head allocation failed")
        })?;
        for literal in &clause.body {
            body.push(class_literal_predicate_id(
                predicate_by_class,
                predicate_by_negative_class,
                literal.class_id,
                literal.negative,
            )?);
        }
        for literal in &clause.head {
            head.push(class_literal_predicate_id(
                predicate_by_class,
                predicate_by_negative_class,
                literal.class_id,
                literal.negative,
            )?);
        }
        let provenance = provenance_id(provenance_keys, &clause.provenance, clause.generated)?;
        push_clause(
            &mut ordered,
            &body,
            &head,
            provenance,
            scalar_predicate_ids,
            budget,
        )?;
    }
    for clause in data_boolean_clauses {
        let mut body = Vec::new();
        let mut head = Vec::new();
        budget.claim_owned(
            clause
                .body
                .len()
                .checked_add(clause.head.len())
                .and_then(|value| value.checked_mul(size_of::<u32>()))
                .ok_or_else(|| {
                    EncodedValidationError::resource("data Boolean predicate allocation overflowed")
                })?,
        )?;
        body.try_reserve_exact(clause.body.len())
            .map_err(|_| EncodedValidationError::resource("data Boolean body allocation failed"))?;
        head.try_reserve_exact(clause.head.len())
            .map_err(|_| EncodedValidationError::resource("data Boolean head allocation failed"))?;
        for literal in &clause.body {
            body.push(data_range_literal_predicate_id(
                predicate_by_data_range,
                predicate_by_negative_data_range,
                *literal,
            )?);
        }
        for literal in &clause.head {
            head.push(data_range_literal_predicate_id(
                predicate_by_data_range,
                predicate_by_negative_data_range,
                *literal,
            )?);
        }
        let provenance = provenance_id(provenance_keys, &clause.provenance, clause.generated)?;
        push_typed_clause(
            &mut ordered,
            &body,
            &head,
            TermSort::Data,
            provenance,
            scalar_predicate_ids,
            budget,
        )?;
    }
    for constraint in object_constraints {
        let class = class_literal_predicate_id(
            predicate_by_class,
            predicate_by_negative_class,
            constraint.class.class_id,
            constraint.class.negative,
        )?;
        let filler = constraint
            .filler
            .map(|literal| {
                class_literal_predicate_id(
                    predicate_by_class,
                    predicate_by_negative_class,
                    literal.class_id,
                    literal.negative,
                )
            })
            .transpose()?;
        let provenance = provenance_id(
            provenance_keys,
            &constraint.provenance,
            constraint.generated,
        )?;
        match constraint.kind {
            ObjectConstraintKind::ExistentialConsequent => {
                let filler_literal = constraint.filler.ok_or_else(|| {
                    EncodedValidationError::invariant(
                        "existential consequent lost its filler literal",
                    )
                })?;
                let at_least = at_least_object_predicate_id(
                    at_least_object_predicates,
                    1,
                    constraint.role_id,
                    filler_literal,
                )?;
                push_clause(
                    &mut ordered,
                    &[class],
                    &[at_least],
                    provenance,
                    scalar_predicate_ids,
                    budget,
                )?;
            }
            ObjectConstraintKind::UniversalAntecedent => {
                let filler_literal = constraint.filler.ok_or_else(|| {
                    EncodedValidationError::invariant(
                        "universal antecedent lost its filler literal",
                    )
                })?;
                let at_least = at_least_object_predicate_id(
                    at_least_object_predicates,
                    1,
                    constraint.role_id,
                    filler_literal,
                )?;
                let thing_predicate = predicate_id(predicate_by_class, thing)?;
                push_clause(
                    &mut ordered,
                    &[thing_predicate],
                    &[at_least, class],
                    provenance,
                    scalar_predicate_ids,
                    budget,
                )?;
            }
            ObjectConstraintKind::MinimumAntecedent | ObjectConstraintKind::MinimumConsequent => {
                let filler_literal = constraint.filler.ok_or_else(|| {
                    EncodedValidationError::invariant(
                        "object-minimum constraint lost its filler literal",
                    )
                })?;
                let cardinality = constraint.cardinality.ok_or_else(|| {
                    EncodedValidationError::invariant(
                        "object-minimum constraint lost its cardinality",
                    )
                })?;
                let at_least = at_least_object_predicate_id(
                    at_least_object_predicates,
                    cardinality,
                    constraint.role_id,
                    filler_literal,
                )?;
                let (body, head) = match constraint.kind {
                    ObjectConstraintKind::MinimumAntecedent => ([at_least], [class]),
                    ObjectConstraintKind::MinimumConsequent => ([class], [at_least]),
                    _ => {
                        return Err(EncodedValidationError::invariant(
                            "non-minimum constraint reached object-minimum clausification",
                        ));
                    }
                };
                push_clause(
                    &mut ordered,
                    &body,
                    &head,
                    provenance,
                    scalar_predicate_ids,
                    budget,
                )?;
            }
            ObjectConstraintKind::MaximumAntecedent => {
                let filler_literal = constraint.filler.ok_or_else(|| {
                    EncodedValidationError::invariant(
                        "object-maximum antecedent lost its filler literal",
                    )
                })?;
                let cardinality = constraint
                    .cardinality
                    .ok_or_else(|| {
                        EncodedValidationError::invariant(
                            "object-maximum antecedent lost its cardinality",
                        )
                    })?
                    .checked_add(1)
                    .ok_or_else(|| {
                        EncodedValidationError::invariant(
                            "object-maximum antecedent cardinality overflowed",
                        )
                    })?;
                let at_least = at_least_object_predicate_id(
                    at_least_object_predicates,
                    cardinality,
                    constraint.role_id,
                    filler_literal,
                )?;
                let thing_predicate = predicate_id(predicate_by_class, thing)?;
                push_clause(
                    &mut ordered,
                    &[thing_predicate],
                    &[at_least, class],
                    provenance,
                    scalar_predicate_ids,
                    budget,
                )?;
            }
            ObjectConstraintKind::MaximumConsequent => {
                let filler_literal = constraint.filler.ok_or_else(|| {
                    EncodedValidationError::invariant(
                        "object-maximum consequent lost its filler literal",
                    )
                })?;
                let filler_predicate = filler.ok_or_else(|| {
                    EncodedValidationError::invariant(
                        "object-maximum consequent lost its filler predicate",
                    )
                })?;
                let cardinality = constraint.cardinality.ok_or_else(|| {
                    EncodedValidationError::invariant(
                        "object-maximum consequent lost its cardinality",
                    )
                })?;
                let role = object_predicate_id(predicate_by_object_role, constraint.role_id)?;
                let annotated_equality = annotated_equality_predicate_id(
                    annotated_equality_predicates,
                    cardinality,
                    constraint.role_id,
                    filler_literal,
                )?;
                push_object_at_most_clause(
                    &mut ordered,
                    class,
                    role,
                    filler_predicate,
                    annotated_equality,
                    ordering_predicate,
                    cardinality,
                    provenance,
                    scalar_predicate_ids,
                    budget,
                )?;
            }
            _ => {
                let role = object_predicate_id(predicate_by_object_role, constraint.role_id)?;
                push_object_constraint_clause(
                    &mut ordered,
                    ObjectConstraintClauseSpec {
                        role_predicate_id: role,
                        class_predicate_id: class,
                        filler_predicate_id: filler,
                        kind: constraint.kind,
                        provenance_id: provenance,
                    },
                    scalar_predicate_ids,
                    budget,
                )?;
            }
        }
    }
    for constraint in data_constraints {
        let class = class_literal_predicate_id(
            predicate_by_class,
            predicate_by_negative_class,
            constraint.class.class_id,
            constraint.class.negative,
        )?;
        let filler = data_range_literal_predicate_id(
            predicate_by_data_range,
            predicate_by_negative_data_range,
            constraint.filler,
        )?;
        let provenance = provenance_id(
            provenance_keys,
            &constraint.provenance,
            constraint.generated,
        )?;
        match constraint.kind {
            DataConstraintKind::ExistentialConsequent => {
                let at_least = at_least_data_predicate_id(
                    at_least_data_predicates,
                    1,
                    constraint.role_id,
                    constraint.filler,
                )?;
                push_clause(
                    &mut ordered,
                    &[class],
                    &[at_least],
                    provenance,
                    scalar_predicate_ids,
                    budget,
                )?;
            }
            DataConstraintKind::UniversalAntecedent => {
                let at_least = at_least_data_predicate_id(
                    at_least_data_predicates,
                    1,
                    constraint.role_id,
                    constraint.filler,
                )?;
                let thing_predicate = predicate_id(predicate_by_class, thing)?;
                push_clause(
                    &mut ordered,
                    &[thing_predicate],
                    &[at_least, class],
                    provenance,
                    scalar_predicate_ids,
                    budget,
                )?;
            }
            DataConstraintKind::MinimumAntecedent | DataConstraintKind::MinimumConsequent => {
                let cardinality = constraint.cardinality.ok_or_else(|| {
                    EncodedValidationError::invariant(
                        "data-minimum constraint lost its cardinality",
                    )
                })?;
                let at_least = at_least_data_predicate_id(
                    at_least_data_predicates,
                    cardinality,
                    constraint.role_id,
                    constraint.filler,
                )?;
                let (body, head) = match constraint.kind {
                    DataConstraintKind::MinimumAntecedent => ([at_least], [class]),
                    DataConstraintKind::MinimumConsequent => ([class], [at_least]),
                    _ => {
                        return Err(EncodedValidationError::invariant(
                            "non-minimum constraint reached data-minimum clausification",
                        ));
                    }
                };
                push_clause(
                    &mut ordered,
                    &body,
                    &head,
                    provenance,
                    scalar_predicate_ids,
                    budget,
                )?;
            }
            DataConstraintKind::MaximumAntecedent => {
                let cardinality = constraint
                    .cardinality
                    .ok_or_else(|| {
                        EncodedValidationError::invariant(
                            "data-maximum antecedent lost its cardinality",
                        )
                    })?
                    .checked_add(1)
                    .ok_or_else(|| {
                        EncodedValidationError::invariant(
                            "data-maximum antecedent cardinality overflowed",
                        )
                    })?;
                let at_least = at_least_data_predicate_id(
                    at_least_data_predicates,
                    cardinality,
                    constraint.role_id,
                    constraint.filler,
                )?;
                let thing_predicate = predicate_id(predicate_by_class, thing)?;
                push_clause(
                    &mut ordered,
                    &[thing_predicate],
                    &[at_least, class],
                    provenance,
                    scalar_predicate_ids,
                    budget,
                )?;
            }
            DataConstraintKind::MaximumConsequent => {
                let cardinality = constraint.cardinality.ok_or_else(|| {
                    EncodedValidationError::invariant(
                        "data-maximum consequent lost its cardinality",
                    )
                })?;
                let role = data_predicate_id(predicate_by_data_role, constraint.role_id)?;
                let equality = data_equality_predicate.ok_or_else(|| {
                    EncodedValidationError::invariant(
                        "data-maximum consequent lost the data equality predicate",
                    )
                })?;
                push_data_at_most_clause(
                    &mut ordered,
                    class,
                    role,
                    filler,
                    equality,
                    cardinality,
                    provenance,
                    scalar_predicate_ids,
                    budget,
                )?;
            }
            DataConstraintKind::ExistentialAntecedent | DataConstraintKind::UniversalConsequent => {
                let role = data_predicate_id(predicate_by_data_role, constraint.role_id)?;
                push_data_constraint_clause(
                    &mut ordered,
                    role,
                    class,
                    filler,
                    constraint.kind,
                    provenance,
                    scalar_predicate_ids,
                    budget,
                )?;
            }
        }
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
    let inequality_predicate = if inequalities.is_empty() && nominal_usage != NominalUsage::Negative
    {
        None
    } else {
        Some(inequality_predicate.ok_or_else(|| {
            EncodedValidationError::invariant(
                "inequality predicate presence disagrees with inequality facts",
            )
        })?)
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

#[derive(Clone, Copy)]
struct ObjectConstraintClauseSpec {
    role_predicate_id: u32,
    class_predicate_id: u32,
    filler_predicate_id: Option<u32>,
    kind: ObjectConstraintKind,
    provenance_id: u32,
}

fn push_object_constraint_clause(
    clauses: &mut Vec<(Vec<u8>, DecodedClause)>,
    spec: ObjectConstraintClauseSpec,
    scalar_predicate_ids: &[u32],
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    let (body, head) = match (spec.kind, spec.filler_predicate_id) {
        (ObjectConstraintKind::Domain, None) => (
            vec![object_variable_atom(spec.role_predicate_id, 0, 1)],
            vec![variable_atom_at(
                spec.class_predicate_id,
                0,
                TermSort::Object,
            )],
        ),
        (ObjectConstraintKind::Range, None) => (
            vec![object_variable_atom(spec.role_predicate_id, 0, 1)],
            vec![variable_atom_at(
                spec.class_predicate_id,
                1,
                TermSort::Object,
            )],
        ),
        (ObjectConstraintKind::SelfAntecedent, None) => (
            vec![object_variable_atom(spec.role_predicate_id, 0, 0)],
            vec![variable_atom_at(
                spec.class_predicate_id,
                0,
                TermSort::Object,
            )],
        ),
        (ObjectConstraintKind::SelfConsequent, None) => (
            vec![variable_atom_at(
                spec.class_predicate_id,
                0,
                TermSort::Object,
            )],
            vec![object_variable_atom(spec.role_predicate_id, 0, 0)],
        ),
        (ObjectConstraintKind::ExistentialAntecedent, Some(filler)) => (
            vec![
                object_variable_atom(spec.role_predicate_id, 0, 1),
                variable_atom_at(filler, 1, TermSort::Object),
            ],
            vec![variable_atom_at(
                spec.class_predicate_id,
                0,
                TermSort::Object,
            )],
        ),
        (ObjectConstraintKind::UniversalConsequent, Some(filler)) => (
            vec![
                variable_atom_at(spec.class_predicate_id, 0, TermSort::Object),
                object_variable_atom(spec.role_predicate_id, 0, 1),
            ],
            vec![variable_atom_at(filler, 1, TermSort::Object)],
        ),
        _ => {
            return Err(EncodedValidationError::invariant(
                "object-property constraint filler disagrees with its kind",
            ));
        }
    };
    let (body, head) =
        canonicalize_variable_rule(body, head, &[], &[], scalar_predicate_ids, budget)?;
    let join_order = if body.len() == 1 {
        vec![0]
    } else {
        plan_key_join(&body, u32::MAX, scalar_predicate_ids, budget)?
    };
    let key = variable_rule_key(&body, &head)?;
    budget.claim_owned(size_of::<(Vec<u8>, DecodedClause)>() + key.len())?;
    let atom_count = body.len().checked_add(head.len()).ok_or_else(|| {
        EncodedValidationError::resource("object-property constraint atom count overflowed")
    })?;
    let term_count = body.iter().chain(&head).try_fold(0_usize, |count, atom| {
        count.checked_add(atom.arguments.len()).ok_or_else(|| {
            EncodedValidationError::resource("object-property constraint term count overflowed")
        })
    })?;
    budget.claim_owned(
        atom_count
            .checked_mul(size_of::<DecodedAtom>())
            .and_then(|value| value.checked_add(term_count.checked_mul(size_of::<DecodedTerm>())?))
            .and_then(|value| {
                value.checked_add(body.len().checked_add(1)?.checked_mul(size_of::<u32>())?)
            })
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
            body,
            head,
            provenance_ids: vec![spec.provenance_id],
            join_order,
        },
    ));
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn push_data_constraint_clause(
    clauses: &mut Vec<(Vec<u8>, DecodedClause)>,
    role_predicate_id: u32,
    class_predicate_id: u32,
    filler_predicate_id: u32,
    kind: DataConstraintKind,
    provenance_id: u32,
    scalar_predicate_ids: &[u32],
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    let (body, head) = match kind {
        DataConstraintKind::ExistentialAntecedent => (
            vec![
                data_variable_atom(role_predicate_id, 0, 1),
                variable_atom_at(filler_predicate_id, 1, TermSort::Data),
            ],
            vec![variable_atom_at(class_predicate_id, 0, TermSort::Object)],
        ),
        DataConstraintKind::UniversalConsequent => (
            vec![
                variable_atom_at(class_predicate_id, 0, TermSort::Object),
                data_variable_atom(role_predicate_id, 0, 1),
            ],
            vec![variable_atom_at(filler_predicate_id, 1, TermSort::Data)],
        ),
        _ => {
            return Err(EncodedValidationError::invariant(
                "data-quantifier relational clause received an at-least kind",
            ));
        }
    };
    let (body, head) =
        canonicalize_variable_rule(body, head, &[], &[], scalar_predicate_ids, budget)?;
    let join_order = plan_key_join(&body, u32::MAX, scalar_predicate_ids, budget)?;
    let key = variable_rule_key(&body, &head)?;
    budget.claim_owned(size_of::<(Vec<u8>, DecodedClause)>() + key.len())?;
    let atom_count = body.len().checked_add(head.len()).ok_or_else(|| {
        EncodedValidationError::resource("data-quantifier constraint atom count overflowed")
    })?;
    let term_count = body.iter().chain(&head).try_fold(0_usize, |count, atom| {
        count.checked_add(atom.arguments.len()).ok_or_else(|| {
            EncodedValidationError::resource("data-quantifier constraint term count overflowed")
        })
    })?;
    budget.claim_owned(
        atom_count
            .checked_mul(size_of::<DecodedAtom>())
            .and_then(|value| value.checked_add(term_count.checked_mul(size_of::<DecodedTerm>())?))
            .and_then(|value| {
                value.checked_add(body.len().checked_add(1)?.checked_mul(size_of::<u32>())?)
            })
            .ok_or_else(|| {
                EncodedValidationError::resource(
                    "data-quantifier constraint clause payload overflowed",
                )
            })?,
    )?;
    clauses.try_reserve(1).map_err(|_| {
        EncodedValidationError::resource("data-quantifier constraint clause allocation failed")
    })?;
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

#[allow(clippy::too_many_arguments)]
fn push_object_at_most_clause(
    clauses: &mut Vec<(Vec<u8>, DecodedClause)>,
    class_predicate_id: u32,
    role_predicate_id: u32,
    filler_predicate_id: u32,
    annotated_equality_predicate_id: u32,
    ordering_predicate_id: Option<u32>,
    cardinality: u32,
    provenance_id: u32,
    scalar_predicate_ids: &[u32],
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    if cardinality == 0 {
        return Err(EncodedValidationError::invariant(
            "zero object at-most did not normalize to a universal restriction",
        ));
    }
    let target_count = usize::try_from(cardinality)
        .map_err(|_| EncodedValidationError::resource("object at-most cardinality exceeds usize"))?
        .checked_add(1)
        .ok_or_else(|| {
            EncodedValidationError::resource("object at-most target count overflowed")
        })?;
    let equality_count = target_count
        .checked_mul(target_count.checked_sub(1).ok_or_else(|| {
            EncodedValidationError::invariant("object at-most target count is empty")
        })?)
        .and_then(|value| value.checked_div(2))
        .ok_or_else(|| {
            EncodedValidationError::resource("object at-most equality count overflowed")
        })?;
    let ordering_count = if target_count > 2 {
        target_count.checked_sub(1).ok_or_else(|| {
            EncodedValidationError::invariant("object at-most ordering count underflowed")
        })?
    } else {
        0
    };
    let body_count = target_count
        .checked_mul(2)
        .and_then(|value| value.checked_add(ordering_count))
        .and_then(|value| value.checked_add(1))
        .ok_or_else(|| {
            EncodedValidationError::resource("object at-most body atom count overflowed")
        })?;
    let atom_count = body_count
        .checked_add(equality_count)
        .ok_or_else(|| EncodedValidationError::resource("object at-most atom count overflowed"))?;
    let term_count = target_count
        .checked_mul(3)
        .and_then(|value| value.checked_add(ordering_count.checked_mul(2)?))
        .and_then(|value| value.checked_add(equality_count.checked_mul(3)?))
        .and_then(|value| value.checked_add(1))
        .ok_or_else(|| EncodedValidationError::resource("object at-most term count overflowed"))?;
    budget.claim_work(atom_count)?;
    budget.claim_owned(
        atom_count
            .checked_mul(size_of::<DecodedAtom>())
            .and_then(|value| value.checked_add(term_count.checked_mul(size_of::<DecodedTerm>())?))
            .ok_or_else(|| {
                EncodedValidationError::resource(
                    "object at-most temporary clause payload overflowed",
                )
            })?,
    )?;

    let ordering = if ordering_count == 0 {
        None
    } else {
        Some(ordering_predicate_id.ok_or_else(|| {
            EncodedValidationError::invariant(
                "object at-most clause lost its ordering-guard predicate",
            )
        })?)
    };
    let mut body = Vec::new();
    let mut head = Vec::new();
    body.try_reserve_exact(body_count)
        .map_err(|_| EncodedValidationError::resource("object at-most body allocation failed"))?;
    head.try_reserve_exact(equality_count)
        .map_err(|_| EncodedValidationError::resource("object at-most head allocation failed"))?;
    body.push(variable_atom_at(class_predicate_id, 0, TermSort::Object));
    for offset in 0..target_count {
        let target = u32::try_from(offset)
            .ok()
            .and_then(|value| value.checked_add(1))
            .ok_or_else(|| {
                EncodedValidationError::resource("object at-most variable ID exceeds u32")
            })?;
        body.push(object_variable_atom(role_predicate_id, 0, target));
        body.push(variable_atom_at(
            filler_predicate_id,
            target,
            TermSort::Object,
        ));
    }
    if let Some(ordering) = ordering {
        for offset in 0..ordering_count {
            let left = u32::try_from(offset)
                .ok()
                .and_then(|value| value.checked_add(1))
                .ok_or_else(|| {
                    EncodedValidationError::resource("object at-most variable ID exceeds u32")
                })?;
            let right = left.checked_add(1).ok_or_else(|| {
                EncodedValidationError::resource("object at-most variable ID exceeds u32")
            })?;
            body.push(object_variable_atom(ordering, left, right));
        }
    }
    for left_offset in 0..target_count {
        let left = u32::try_from(left_offset)
            .ok()
            .and_then(|value| value.checked_add(1))
            .ok_or_else(|| {
                EncodedValidationError::resource("object at-most variable ID exceeds u32")
            })?;
        for right_offset in left_offset.checked_add(1).ok_or_else(|| {
            EncodedValidationError::resource("object at-most variable offset overflowed")
        })?..target_count
        {
            let right = u32::try_from(right_offset)
                .ok()
                .and_then(|value| value.checked_add(1))
                .ok_or_else(|| {
                    EncodedValidationError::resource("object at-most variable ID exceeds u32")
                })?;
            head.push(DecodedAtom {
                predicate_id: annotated_equality_predicate_id,
                arguments: vec![
                    DecodedTerm::Variable {
                        index: left,
                        sort: TermSort::Object,
                    },
                    DecodedTerm::Variable {
                        index: right,
                        sort: TermSort::Object,
                    },
                    DecodedTerm::Variable {
                        index: 0,
                        sort: TermSort::Object,
                    },
                ],
            });
        }
    }

    let ordering_predicates = ordering.map(|predicate_id| [predicate_id]);
    let symmetric_predicates = ordering_predicates
        .as_ref()
        .map_or(&[][..], |predicates| predicates.as_slice());
    let annotated_equality_predicates = [annotated_equality_predicate_id];
    let (body, head) = canonicalize_variable_rule(
        body,
        head,
        symmetric_predicates,
        &annotated_equality_predicates,
        scalar_predicate_ids,
        budget,
    )?;
    let join_order = plan_key_join(
        &body,
        ordering.unwrap_or(u32::MAX),
        scalar_predicate_ids,
        budget,
    )?;
    let key = variable_rule_key(&body, &head)?;
    budget.claim_owned(size_of::<(Vec<u8>, DecodedClause)>() + key.len())?;
    budget.claim_owned(
        body.len()
            .checked_add(head.len())
            .and_then(|value| value.checked_mul(size_of::<DecodedAtom>()))
            .and_then(|value| value.checked_add(term_count.checked_mul(size_of::<DecodedTerm>())?))
            .and_then(|value| {
                value.checked_add(body.len().checked_add(1)?.checked_mul(size_of::<u32>())?)
            })
            .ok_or_else(|| {
                EncodedValidationError::resource("object at-most clause payload overflowed")
            })?,
    )?;
    clauses
        .try_reserve(1)
        .map_err(|_| EncodedValidationError::resource("object at-most clause allocation failed"))?;
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

#[allow(clippy::too_many_arguments)]
fn push_data_at_most_clause(
    clauses: &mut Vec<(Vec<u8>, DecodedClause)>,
    class_predicate_id: u32,
    role_predicate_id: u32,
    filler_predicate_id: u32,
    equality_predicate_id: u32,
    cardinality: u32,
    provenance_id: u32,
    scalar_predicate_ids: &[u32],
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    if cardinality == 0 {
        return Err(EncodedValidationError::invariant(
            "zero data at-most did not normalize to a universal restriction",
        ));
    }
    let target_count = usize::try_from(cardinality)
        .map_err(|_| EncodedValidationError::resource("data at-most cardinality exceeds usize"))?
        .checked_add(1)
        .ok_or_else(|| EncodedValidationError::resource("data at-most target count overflowed"))?;
    let equality_count = target_count
        .checked_mul(target_count.checked_sub(1).ok_or_else(|| {
            EncodedValidationError::invariant("data at-most target count is empty")
        })?)
        .and_then(|value| value.checked_div(2))
        .ok_or_else(|| {
            EncodedValidationError::resource("data at-most equality count overflowed")
        })?;
    let body_count = target_count
        .checked_mul(2)
        .and_then(|value| value.checked_add(1))
        .ok_or_else(|| {
            EncodedValidationError::resource("data at-most body atom count overflowed")
        })?;
    let atom_count = body_count
        .checked_add(equality_count)
        .ok_or_else(|| EncodedValidationError::resource("data at-most atom count overflowed"))?;
    let term_count = target_count
        .checked_mul(3)
        .and_then(|value| value.checked_add(equality_count.checked_mul(2)?))
        .and_then(|value| value.checked_add(1))
        .ok_or_else(|| EncodedValidationError::resource("data at-most term count overflowed"))?;
    budget.claim_work(atom_count)?;
    budget.claim_owned(
        atom_count
            .checked_mul(size_of::<DecodedAtom>())
            .and_then(|value| value.checked_add(term_count.checked_mul(size_of::<DecodedTerm>())?))
            .ok_or_else(|| {
                EncodedValidationError::resource("data at-most temporary clause payload overflowed")
            })?,
    )?;

    let mut body = Vec::new();
    let mut head = Vec::new();
    body.try_reserve_exact(body_count)
        .map_err(|_| EncodedValidationError::resource("data at-most body allocation failed"))?;
    head.try_reserve_exact(equality_count)
        .map_err(|_| EncodedValidationError::resource("data at-most head allocation failed"))?;
    body.push(variable_atom_at(class_predicate_id, 0, TermSort::Object));
    for offset in 0..target_count {
        let target = u32::try_from(offset)
            .ok()
            .and_then(|value| value.checked_add(1))
            .ok_or_else(|| {
                EncodedValidationError::resource("data at-most variable ID exceeds u32")
            })?;
        body.push(data_variable_atom(role_predicate_id, 0, target));
        body.push(variable_atom_at(
            filler_predicate_id,
            target,
            TermSort::Data,
        ));
    }
    for left_offset in 0..target_count {
        let left = u32::try_from(left_offset)
            .ok()
            .and_then(|value| value.checked_add(1))
            .ok_or_else(|| {
                EncodedValidationError::resource("data at-most variable ID exceeds u32")
            })?;
        for right_offset in left_offset.checked_add(1).ok_or_else(|| {
            EncodedValidationError::resource("data at-most variable offset overflowed")
        })?..target_count
        {
            let right = u32::try_from(right_offset)
                .ok()
                .and_then(|value| value.checked_add(1))
                .ok_or_else(|| {
                    EncodedValidationError::resource("data at-most variable ID exceeds u32")
                })?;
            head.push(data_equality_variable_atom(
                equality_predicate_id,
                left,
                right,
            ));
        }
    }

    let equality_predicates = [equality_predicate_id];
    let (body, head) = canonicalize_variable_rule(
        body,
        head,
        &equality_predicates,
        &[],
        scalar_predicate_ids,
        budget,
    )?;
    let join_order = plan_key_join(&body, u32::MAX, scalar_predicate_ids, budget)?;
    let key = variable_rule_key(&body, &head)?;
    budget.claim_owned(size_of::<(Vec<u8>, DecodedClause)>() + key.len())?;
    budget.claim_owned(
        body.len()
            .checked_add(head.len())
            .and_then(|value| value.checked_mul(size_of::<DecodedAtom>()))
            .and_then(|value| value.checked_add(term_count.checked_mul(size_of::<DecodedTerm>())?))
            .and_then(|value| {
                value.checked_add(body.len().checked_add(1)?.checked_mul(size_of::<u32>())?)
            })
            .ok_or_else(|| {
                EncodedValidationError::resource("data at-most clause payload overflowed")
            })?,
    )?;
    clauses
        .try_reserve(1)
        .map_err(|_| EncodedValidationError::resource("data at-most clause allocation failed"))?;
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
        &[],
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
    annotated_equality_predicates: &[u32],
    scalar_predicate_ids: &[u32],
    budget: &mut PhaseBudget,
) -> EncodedResult<(Vec<DecodedAtom>, Vec<DecodedAtom>)> {
    for atom in body.iter_mut().chain(&mut head) {
        canonicalize_symmetric_variable_atom(
            atom,
            symmetric_predicates,
            annotated_equality_predicates,
        )?;
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
            annotated_equality_predicates,
            scalar_predicate_ids,
            budget,
        )?;
        let renamed_head = rename_variable_atoms(
            &head,
            &mapping,
            symmetric_predicates,
            annotated_equality_predicates,
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
    annotated_equality_predicates: &[u32],
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
        canonicalize_symmetric_variable_atom(
            &mut value,
            symmetric_predicates,
            annotated_equality_predicates,
        )?;
        renamed.push(value);
    }
    sort_atoms_by_canonical_key(renamed, scalar_predicate_ids, budget)
}

fn canonicalize_symmetric_variable_atom(
    atom: &mut DecodedAtom,
    symmetric_predicates: &[u32],
    annotated_equality_predicates: &[u32],
) -> EncodedResult<()> {
    if annotated_equality_predicates.contains(&atom.predicate_id) {
        let [left, right, _root] = atom.arguments.as_mut_slice() else {
            return Err(EncodedValidationError::invariant(
                "annotated-equality atom is not ternary",
            ));
        };
        canonicalize_symmetric_variable_pair(left, right)?;
        return Ok(());
    }
    if !symmetric_predicates.contains(&atom.predicate_id) {
        return Ok(());
    }
    let [left, right] = atom.arguments.as_mut_slice() else {
        return Err(EncodedValidationError::invariant(
            "symmetric variable atom is not binary",
        ));
    };
    canonicalize_symmetric_variable_pair(left, right)
}

fn canonicalize_symmetric_variable_pair(
    left: &mut DecodedTerm,
    right: &mut DecodedTerm,
) -> EncodedResult<()> {
    let DecodedTerm::Variable {
        index: left_index,
        sort: left_sort,
    } = left
    else {
        return Err(EncodedValidationError::invariant(
            "symmetric variable atom contains a non-variable term",
        ));
    };
    let DecodedTerm::Variable {
        index: right_index,
        sort: right_sort,
    } = right
    else {
        return Err(EncodedValidationError::invariant(
            "symmetric variable atom contains a non-variable term",
        ));
    };
    if left_sort != right_sort {
        return Err(EncodedValidationError::invariant(
            "symmetric variable atom mixes term sorts",
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

fn at_least_object_predicate_id(
    index: &AtLeastObjectPredicateIndex,
    cardinality: u32,
    role_id: u32,
    filler: ClassLiteral,
) -> EncodedResult<u32> {
    index
        .binary_search_by_key(&(cardinality, role_id, filler), |(candidate, _)| *candidate)
        .ok()
        .map(|position| index[position].1)
        .ok_or_else(|| {
            EncodedValidationError::invariant("object at-least predicate index is incomplete")
        })
}

fn at_least_data_predicate_id(
    index: &AtLeastDataPredicateIndex,
    cardinality: u32,
    role_id: u32,
    filler: DataRangeLiteral,
) -> EncodedResult<u32> {
    index
        .binary_search_by_key(&(cardinality, role_id, filler), |(candidate, _)| *candidate)
        .ok()
        .map(|position| index[position].1)
        .ok_or_else(|| {
            EncodedValidationError::invariant("data at-least predicate index is incomplete")
        })
}

fn annotated_equality_predicate_id(
    index: &AnnotatedEqualityPredicateIndex,
    cardinality: u32,
    role_id: u32,
    filler: ClassLiteral,
) -> EncodedResult<u32> {
    index
        .binary_search_by_key(&(cardinality, role_id, filler), |(candidate, _)| *candidate)
        .ok()
        .map(|position| index[position].1)
        .ok_or_else(|| {
            EncodedValidationError::invariant("annotated-equality predicate index is incomplete")
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

fn disjoint_guard_digest_keys(
    classes: &[(ClassLiteral, Vec<u8>)],
    budget: &mut PhaseBudget,
) -> EncodedResult<[u8; 32]> {
    let mut digest = Sha256::new();
    digest.update(DISJOINT_GUARD_DOMAIN);
    budget.claim_work(DISJOINT_GUARD_DOMAIN.len())?;
    for (_, key) in classes {
        budget.claim_work(key.len())?;
        digest.update(key);
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
        let key = named_predicate_key(predicate, predicates, budget)?;
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

fn named_predicate_key(
    predicate: &DecodedPredicate,
    predicates: &[DecodedPredicate],
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<u8>> {
    let unary_object = predicate.argument_sorts == [TermSort::Object];
    let unary_data = predicate.argument_sorts == [TermSort::Data];
    let binary_object = predicate.argument_sorts == [TermSort::Object, TermSort::Object];
    let binary_data = predicate.argument_sorts == [TermSort::Object, TermSort::Data];
    let ternary_object = predicate.argument_sorts == [TermSort::Object; 3];
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
    if predicate.kind == PredicateKind::AtLeastObject
        && unary_object
        && predicate.symbol_id.is_none()
        && predicate.cardinality.is_some_and(|value| value > 0)
        && predicate.annotation.is_empty()
        && predicate.internal_key.is_none()
    {
        let role_id = predicate.role_id.ok_or_else(|| {
            EncodedValidationError::invariant("object at-least predicate lost its role ID")
        })?;
        let filler_id = predicate.filler_predicate_id.ok_or_else(|| {
            EncodedValidationError::invariant("object at-least predicate lost its filler")
        })?;
        let filler = predicates
            .get(usize::try_from(filler_id).map_err(|_| {
                EncodedValidationError::invariant(
                    "object at-least filler predicate ID exceeds usize",
                )
            })?)
            .ok_or_else(|| {
                EncodedValidationError::invariant("object at-least filler predicate ID is dangling")
            })?;
        if !matches!(
            filler.kind,
            PredicateKind::Concept
                | PredicateKind::NegatedConcept
                | PredicateKind::Nominal
                | PredicateKind::NegatedNominal
        ) {
            return Err(EncodedValidationError::invariant(
                "object at-least filler is not a class predicate",
            ));
        }
        let filler_key = named_predicate_key(filler, predicates, budget)?;
        return at_least_object_predicate_key(
            predicate.cardinality.ok_or_else(|| {
                EncodedValidationError::invariant("object at-least predicate lost its cardinality")
            })?,
            role_id,
            &filler_key,
            budget,
        );
    }
    if predicate.kind == PredicateKind::AtLeastData
        && unary_object
        && predicate.symbol_id.is_none()
        && predicate.cardinality.is_some_and(|value| value > 0)
        && predicate.annotation.len() == 1
        && predicate.internal_key.is_none()
    {
        let role_id = predicate.role_id.ok_or_else(|| {
            EncodedValidationError::invariant("data at-least predicate lost its role ID")
        })?;
        if predicate.annotation[0] != role_id {
            return Err(EncodedValidationError::invariant(
                "data at-least predicate annotation changed role",
            ));
        }
        let filler_id = predicate.filler_predicate_id.ok_or_else(|| {
            EncodedValidationError::invariant("data at-least predicate lost its filler")
        })?;
        let filler = predicates
            .get(usize::try_from(filler_id).map_err(|_| {
                EncodedValidationError::invariant("data at-least filler predicate ID exceeds usize")
            })?)
            .ok_or_else(|| {
                EncodedValidationError::invariant("data at-least filler predicate ID is dangling")
            })?;
        if !matches!(
            filler.kind,
            PredicateKind::DataRange | PredicateKind::NegatedDataRange
        ) || filler.argument_sorts != [TermSort::Data]
        {
            return Err(EncodedValidationError::invariant(
                "data at-least filler is not a unary data-range predicate",
            ));
        }
        let filler_key = named_predicate_key(filler, predicates, budget)?;
        return at_least_data_predicate_key(
            predicate.cardinality.ok_or_else(|| {
                EncodedValidationError::invariant("data at-least predicate lost its cardinality")
            })?,
            role_id,
            &filler_key,
            budget,
        );
    }
    if predicate.kind == PredicateKind::AnnotatedEquality
        && ternary_object
        && predicate.symbol_id.is_none()
        && predicate.cardinality.is_some_and(|value| value > 0)
        && predicate.annotation.is_empty()
        && predicate.internal_key.is_none()
    {
        let role_id = predicate.role_id.ok_or_else(|| {
            EncodedValidationError::invariant("annotated-equality predicate lost its role ID")
        })?;
        let filler_id = predicate.filler_predicate_id.ok_or_else(|| {
            EncodedValidationError::invariant("annotated-equality predicate lost its filler")
        })?;
        let filler = predicates
            .get(usize::try_from(filler_id).map_err(|_| {
                EncodedValidationError::invariant(
                    "annotated-equality filler predicate ID exceeds usize",
                )
            })?)
            .ok_or_else(|| {
                EncodedValidationError::invariant(
                    "annotated-equality filler predicate ID is dangling",
                )
            })?;
        if !matches!(
            filler.kind,
            PredicateKind::Concept
                | PredicateKind::NegatedConcept
                | PredicateKind::Nominal
                | PredicateKind::NegatedNominal
        ) {
            return Err(EncodedValidationError::invariant(
                "annotated-equality filler is not a class predicate",
            ));
        }
        let filler_key = named_predicate_key(filler, predicates, budget)?;
        return annotated_equality_predicate_key(
            predicate.cardinality.ok_or_else(|| {
                EncodedValidationError::invariant(
                    "annotated-equality predicate lost its cardinality",
                )
            })?,
            role_id,
            &filler_key,
            budget,
        );
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

fn class_literal_predicate_key(
    nominal_bindings: &[NominalBinding],
    literal: ClassLiteral,
) -> Vec<u8> {
    let nominal = nominal_binding(nominal_bindings, literal.class_id);
    nominal.map_or_else(
        || {
            if literal.negative {
                negated_concept_predicate_key(literal.class_id)
            } else {
                concept_predicate_key(literal.class_id)
            }
        },
        |binding| {
            nominal_predicate_key(literal.class_id, &binding.individual_ids, literal.negative)
        },
    )
}

fn at_least_object_predicate_key(
    cardinality: u32,
    role_id: u32,
    filler_key: &[u8],
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<u8>> {
    if cardinality == 0 {
        return Err(EncodedValidationError::invariant(
            "object at-least predicate has zero cardinality",
        ));
    }
    budget.claim_work(filler_key.len())?;
    let filler_digest: [u8; 32] = Sha256::digest(filler_key).into();
    let filler = crate::model::hex(&filler_digest);
    Ok(format!(
        "{{\"annotation\":[],\"argument_sorts\":[\"object\"],\"cardinality\":{cardinality},\"filler\":\"{filler}\",\"internal_key\":null,\"kind\":\"at_least_object\",\"role_id\":{role_id},\"symbol_id\":null}}"
    )
    .into_bytes())
}

fn at_least_data_predicate_key(
    cardinality: u32,
    role_id: u32,
    filler_key: &[u8],
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<u8>> {
    if cardinality == 0 {
        return Err(EncodedValidationError::invariant(
            "data at-least predicate has zero cardinality",
        ));
    }
    budget.claim_work(filler_key.len())?;
    let filler_digest: [u8; 32] = Sha256::digest(filler_key).into();
    let filler = crate::model::hex(&filler_digest);
    Ok(format!(
        "{{\"annotation\":[{role_id}],\"argument_sorts\":[\"object\"],\"cardinality\":{cardinality},\"filler\":\"{filler}\",\"internal_key\":null,\"kind\":\"at_least_data\",\"role_id\":{role_id},\"symbol_id\":null}}"
    )
    .into_bytes())
}

fn annotated_equality_predicate_key(
    cardinality: u32,
    role_id: u32,
    filler_key: &[u8],
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<u8>> {
    if cardinality == 0 {
        return Err(EncodedValidationError::invariant(
            "annotated-equality predicate has zero cardinality",
        ));
    }
    budget.claim_work(filler_key.len())?;
    let filler_digest: [u8; 32] = Sha256::digest(filler_key).into();
    let filler = crate::model::hex(&filler_digest);
    Ok(format!(
        "{{\"annotation\":[],\"argument_sorts\":[\"object\",\"object\",\"object\"],\"cardinality\":{cardinality},\"filler\":\"{filler}\",\"internal_key\":null,\"kind\":\"annotated_equality\",\"role_id\":{role_id},\"symbol_id\":null}}"
    )
    .into_bytes())
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

fn data_range_literal_predicate_key(literal: DataRangeLiteral) -> Vec<u8> {
    if literal.negative {
        negated_data_range_predicate_key(literal.range_id)
    } else {
        data_range_predicate_key(literal.range_id)
    }
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
        .map(|(_, phase)| &phase.entity_domain)
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
    let (
        edges,
        boolean_clauses,
        disjoints,
        object_constraints,
        data_constraints,
        object_characteristics,
        data_domains,
        data_ranges,
        data_boolean_clauses,
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
        &boolean_clauses,
        &disjoints,
        &object_constraints,
        &data_constraints,
        &object_characteristics,
        &data_domains,
        &data_ranges,
        &data_boolean_clauses,
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
        at_least_object_predicates,
        at_least_data_predicates,
        annotated_equality_predicates,
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
        &boolean_clauses,
        &disjoints,
        &object_constraints,
        &data_constraints,
        &object_characteristics,
        &data_domains,
        &data_ranges,
        &data_boolean_clauses,
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
        &boolean_clauses,
        &disjoints,
        &object_constraints,
        &data_constraints,
        &object_characteristics,
        &data_domains,
        &data_ranges,
        &data_boolean_clauses,
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
        &at_least_object_predicates,
        &at_least_data_predicates,
        &annotated_equality_predicates,
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
            &boolean_clauses,
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
        entity_domain,
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
        normalized_boolean_clauses: boolean_clauses,
        normalized_disjoints: disjoints,
        normalized_object_constraints: object_constraints,
        normalized_data_constraints: data_constraints,
        normalized_object_characteristics: object_characteristics,
        normalized_data_domains: data_domains,
        normalized_data_ranges: data_ranges,
        normalized_data_boolean_clauses: data_boolean_clauses,
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
    for (phase_index, (_, phase)) in phases.iter().enumerate() {
        let named_count = phase
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
            let entity = phase
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
    Vec<NormalizedBooleanClause>,
    Vec<NormalizedDisjoint>,
    Vec<NormalizedObjectConstraint>,
    Vec<NormalizedDataConstraint>,
    Vec<NormalizedObjectCharacteristic>,
    Vec<NormalizedDataDomain>,
    Vec<NormalizedDataRange>,
    Vec<NormalizedDataBooleanClause>,
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
    let mut raw_boolean_clauses = Vec::new();
    let mut raw_disjoints = Vec::new();
    let mut raw_object_constraints = Vec::new();
    let mut raw_data_constraints = Vec::new();
    let mut raw_object_characteristics = Vec::new();
    let mut raw_data_domains = Vec::new();
    let mut raw_data_ranges = Vec::new();
    let mut raw_data_boolean_clauses = Vec::new();
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
                    generated: edge.generated,
                });
            }
        }
        for clause in &phase.normalized_boolean_clauses {
            if clause.provenance.is_empty() {
                return Err(EncodedValidationError::invariant(
                    "merged generated Boolean clause lost provenance",
                ));
            }
            let mut body = Vec::new();
            let mut head = Vec::new();
            budget.claim_owned(
                clause
                    .body
                    .len()
                    .checked_add(clause.head.len())
                    .and_then(|value| value.checked_mul(size_of::<ClassLiteral>()))
                    .ok_or_else(|| {
                        EncodedValidationError::resource(
                            "merged Boolean literal allocation overflowed",
                        )
                    })?,
            )?;
            body.try_reserve_exact(clause.body.len()).map_err(|_| {
                EncodedValidationError::resource("merged Boolean body allocation failed")
            })?;
            head.try_reserve_exact(clause.head.len()).map_err(|_| {
                EncodedValidationError::resource("merged Boolean head allocation failed")
            })?;
            for literal in &clause.body {
                body.push(ClassLiteral {
                    class_id: mapped_id(class_map, literal.class_id, "Boolean body class")?,
                    negative: literal.negative,
                });
            }
            for literal in &clause.head {
                head.push(ClassLiteral {
                    class_id: mapped_id(class_map, literal.class_id, "Boolean head class")?,
                    negative: literal.negative,
                });
            }
            for provenance in &clause.provenance {
                budget.claim_work(1)?;
                budget.claim_owned(size_of::<RawBooleanClause>())?;
                raw_boolean_clauses.try_reserve(1).map_err(|_| {
                    EncodedValidationError::resource("merged Boolean clause allocation failed")
                })?;
                raw_boolean_clauses.push(RawBooleanClause {
                    body: body.clone(),
                    head: head.clone(),
                    provenance: *provenance,
                    generated: clause.generated,
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
                        filler: constraint
                            .filler
                            .map(|literal| {
                                Ok(ClassLiteral {
                                    class_id: mapped_id(
                                        class_map,
                                        literal.class_id,
                                        "object-quantifier filler class",
                                    )?,
                                    negative: literal.negative,
                                })
                            })
                            .transpose()?,
                        cardinality: constraint.cardinality,
                        provenance: *provenance,
                        generated: constraint.generated,
                    });
                }
            }
        }
        if !phase.normalized_data_constraints.is_empty() {
            let source_roles = source_data_roles
                .and_then(|roles| roles.get(phase_index))
                .ok_or_else(|| {
                    EncodedValidationError::invariant(
                        "merged data-quantifier constraints lost their source role domain",
                    )
                })?;
            let merged_roles = merged_data_roles.ok_or_else(|| {
                EncodedValidationError::invariant(
                    "merged data-quantifier constraints lost their global role domain",
                )
            })?;
            for constraint in &phase.normalized_data_constraints {
                if constraint.provenance.is_empty() {
                    return Err(EncodedValidationError::invariant(
                        "merged data-quantifier constraint lost provenance",
                    ));
                }
                let role_id =
                    remap_data_role(source_roles, merged_roles, constraint.role_id, budget)?;
                let class = ClassLiteral {
                    class_id: mapped_id(
                        class_map,
                        constraint.class.class_id,
                        "data-quantifier constraint class",
                    )?,
                    negative: constraint.class.negative,
                };
                let filler = DataRangeLiteral {
                    range_id: mapped_id(
                        data_range_map,
                        constraint.filler.range_id,
                        "data-quantifier filler range",
                    )?,
                    negative: constraint.filler.negative,
                };
                for provenance in &constraint.provenance {
                    budget.claim_work(1)?;
                    budget.claim_owned(size_of::<RawDataConstraint>())?;
                    raw_data_constraints.try_reserve(1).map_err(|_| {
                        EncodedValidationError::resource(
                            "merged data-quantifier constraint allocation failed",
                        )
                    })?;
                    raw_data_constraints.push(RawDataConstraint {
                        kind: constraint.kind,
                        role_id,
                        class,
                        filler,
                        cardinality: constraint.cardinality,
                        provenance: *provenance,
                        generated: constraint.generated,
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
        for clause in &phase.normalized_data_boolean_clauses {
            if clause.provenance.is_empty() {
                return Err(EncodedValidationError::invariant(
                    "merged data Boolean clause lost provenance",
                ));
            }
            let mut body = Vec::new();
            let mut head = Vec::new();
            budget.claim_owned(
                clause
                    .body
                    .len()
                    .checked_add(clause.head.len())
                    .and_then(|value| value.checked_mul(size_of::<DataRangeLiteral>()))
                    .ok_or_else(|| {
                        EncodedValidationError::resource(
                            "merged data Boolean literal allocation overflowed",
                        )
                    })?,
            )?;
            body.try_reserve_exact(clause.body.len()).map_err(|_| {
                EncodedValidationError::resource("merged data Boolean body allocation failed")
            })?;
            head.try_reserve_exact(clause.head.len()).map_err(|_| {
                EncodedValidationError::resource("merged data Boolean head allocation failed")
            })?;
            for literal in &clause.body {
                body.push(DataRangeLiteral {
                    range_id: mapped_id(
                        data_range_map,
                        literal.range_id,
                        "data Boolean body range",
                    )?,
                    negative: literal.negative,
                });
            }
            for literal in &clause.head {
                head.push(DataRangeLiteral {
                    range_id: mapped_id(
                        data_range_map,
                        literal.range_id,
                        "data Boolean head range",
                    )?,
                    negative: literal.negative,
                });
            }
            for provenance in &clause.provenance {
                budget.claim_work(1)?;
                push_raw_data_boolean_clause(
                    &mut raw_data_boolean_clauses,
                    body.clone(),
                    head.clone(),
                    *provenance,
                    clause.generated,
                    budget,
                )?;
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
        normalize_boolean_clauses(raw_boolean_clauses, budget)?,
        normalize_disjoints(raw_disjoints, budget)?,
        normalize_object_constraints(raw_object_constraints, budget)?,
        normalize_data_constraints(raw_data_constraints, budget)?,
        normalize_object_characteristics(raw_object_characteristics, budget)?,
        normalize_data_domains(raw_data_domains, budget)?,
        normalize_data_ranges(raw_data_ranges, budget)?,
        normalize_data_boolean_clauses(raw_data_boolean_clauses, budget)?,
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
