//! Bounded OWL 2 DL profile diagnostics over encoded structural input.
//!
//! Profile violations are successful semantic output. Malformed columns,
//! resource exhaustion, and cancellation remain distinct operational failures.
//! This private phase owns exact data-arity, top-data-property, local
//! anonymous-placement, global entity/declaration, datatype, object-role, and
//! extension projections. A separate versioned identity context supplies
//! ontology/version IRIs without changing structural-columns schema 1. That schema
//! does not carry origin rows, so the manifest exposes canonical root provenance
//! without inventing `ProfileIssue.document_keys`. Anonymous graph, entity,
//! declaration, and role facts remain private until all selected slices can be
//! merged and validated globally. Issue ordering and deduplication use the
//! exact projected field tuple published by this phase.
// SPDX-License-Identifier: LGPL-3.0-or-later

#![forbid(unsafe_code)]

use std::borrow::Cow;
use std::cell::RefCell;
use std::convert::Infallible;
use std::mem::size_of;

use serde::Serialize;
use sha2::{Digest, Sha256};

use crate::datatypes::{DatatypeControl, DatatypeError, DatatypeErrorKind, RegexLimits, XsdRegex};

use super::canonical::{self, AnonymousScopeMap, CanonicalBudget};
use super::model::{
    CollectionRef, ComponentKind, ComponentRef, ComponentValue, NodeId, NodeRef, RootKind,
    ScalarRef, ValidatedModel,
};
use super::named_classes::{
    self, NamedClassPhaseLimits, PhaseBudget as LiteralPhaseBudget, ProfileLiteralInvalid,
    ProfileLiteralSemantics, ProfileLiteralValidation,
};
use super::symbols::RootHandler;
use super::{u32_at, ByteSource, EncodedResult, EncodedValidationError};

const PROFILE_PHASE_SCHEMA_VERSION: u16 = 1;
const CORE_STRUCTURAL_DIGEST_PREFIX: &[u8] = b"pyowl-core:structural-value:v1\x00\x01";
const POSTINGS_ALL: u8 = 0;
const POSTINGS_INCLUDE: u8 = 1;
const POSTINGS_EXCLUDE: u8 = 2;
const IRI_TAG: u16 = 1;
const ENTITY_TAG: u16 = 2;
const ANONYMOUS_INDIVIDUAL_TAG: u16 = 3;
const LITERAL_TAG: u16 = 4;
const OBJECT_INVERSE_OF_TAG: u16 = 10;
const OBJECT_PROPERTY_CHAIN_TAG: u16 = 11;
const FACET_RESTRICTION_TAG: u16 = 20;
const DATA_INTERSECTION_OF_TAG: u16 = 21;
const DATA_UNION_OF_TAG: u16 = 22;
const DATA_COMPLEMENT_OF_TAG: u16 = 23;
const DATA_ONE_OF_TAG: u16 = 24;
const DATATYPE_RESTRICTION_TAG: u16 = 25;
const OBJECT_ONE_OF_TAG: u16 = 33;
const OBJECT_HAS_VALUE_TAG: u16 = 36;
const OBJECT_HAS_SELF_TAG: u16 = 37;
const OBJECT_MIN_CARDINALITY_TAG: u16 = 38;
const OBJECT_MAX_CARDINALITY_TAG: u16 = 39;
const OBJECT_EXACT_CARDINALITY_TAG: u16 = 40;
const DATA_SOME_VALUES_FROM_TAG: u16 = 41;
const DATA_ALL_VALUES_FROM_TAG: u16 = 42;
const DECLARATION_TAG: u16 = 60;
const SUB_OBJECT_PROPERTY_TAG: u16 = 70;
const EQUIVALENT_OBJECT_PROPERTIES_TAG: u16 = 71;
const DISJOINT_OBJECT_PROPERTIES_TAG: u16 = 72;
const INVERSE_OBJECT_PROPERTIES_TAG: u16 = 73;
const FUNCTIONAL_OBJECT_PROPERTY_TAG: u16 = 76;
const INVERSE_FUNCTIONAL_OBJECT_PROPERTY_TAG: u16 = 77;
const IRREFLEXIVE_OBJECT_PROPERTY_TAG: u16 = 79;
const SYMMETRIC_OBJECT_PROPERTY_TAG: u16 = 80;
const ASYMMETRIC_OBJECT_PROPERTY_TAG: u16 = 81;
const TRANSITIVE_OBJECT_PROPERTY_TAG: u16 = 82;
const SUB_DATA_PROPERTY_TAG: u16 = 90;
const DATATYPE_DEFINITION_TAG: u16 = 100;
const SAME_INDIVIDUAL_TAG: u16 = 110;
const DIFFERENT_INDIVIDUALS_TAG: u16 = 111;
const OBJECT_PROPERTY_ASSERTION_TAG: u16 = 113;
const NEGATIVE_OBJECT_PROPERTY_ASSERTION_TAG: u16 = 114;
const NEGATIVE_DATA_PROPERTY_ASSERTION_TAG: u16 = 116;
const SWRL_RULE_TAG: u16 = 148;
const TOP_DATA_PROPERTY_IRI: &[u8] = b"http://www.w3.org/2002/07/owl#topDataProperty";
const DATA_RANGE_ARITY_RULE: &str = "OWL2_DATA_RANGE_ARITY";
const DATA_RANGE_ARITY_MESSAGE: &str =
    "OWL 2 defines only unary data ranges, so the restriction must use exactly one data property";
const TOP_DATA_PROPERTY_RULE: &str = "OWL2DL_TOP_DATA_PROPERTY_POSITION";
const TOP_DATA_PROPERTY_MESSAGE: &str =
    "owl:topDataProperty may occur only as the super-property of a data subproperty axiom";
const ANONYMOUS_AXIOM_POSITION_RULE: &str = "OWL2DL_ANONYMOUS_AXIOM_POSITION";
const ANONYMOUS_AXIOM_POSITION_MESSAGE: &str =
    "anonymous individuals are forbidden in this axiom type";
const ANONYMOUS_CLASS_EXPRESSION_RULE: &str = "OWL2DL_ANONYMOUS_CLASS_EXPRESSION";
const ANONYMOUS_CLASS_EXPRESSION_MESSAGE: &str =
    "anonymous individuals are forbidden in ObjectOneOf and ObjectHasValue expressions";
const ANONYMOUS_GRAPH_CYCLE_RULE: &str = "OWL2DL_ANONYMOUS_GRAPH_CYCLE";
const ANONYMOUS_GRAPH_CYCLE_MESSAGE: &str =
    "the anonymous-individual object-assertion graph must be a forest";
const ANONYMOUS_PARALLEL_EDGE_RULE: &str = "OWL2DL_ANONYMOUS_PARALLEL_EDGE";
const ANONYMOUS_PARALLEL_EDGE_MESSAGE: &str =
    "at most one object-property assertion may connect an anonymous pair";
const ANONYMOUS_TREE_ROOT_RULE: &str = "OWL2DL_ANONYMOUS_TREE_ROOT";
const ANONYMOUS_TREE_ROOT_MESSAGE: &str =
    "each anonymous-individual tree must contain a vertex connected by at most one assertion to named individuals";
const RESERVED_ONTOLOGY_IRI_RULE: &str = "OWL2DL_RESERVED_ONTOLOGY_IRI";
const RESERVED_VERSION_IRI_RULE: &str = "OWL2DL_RESERVED_VERSION_IRI";
const RESERVED_ONTOLOGY_IRI_MESSAGE_PREFIX: &str =
    "ontology IRI must not use reserved OWL/RDF vocabulary: ";
const RESERVED_VERSION_IRI_MESSAGE_PREFIX: &str =
    "version IRI must not use reserved OWL/RDF vocabulary: ";
const PROPERTY_PUNNING_RULE: &str = "OWL2DL_PROPERTY_PUNNING";
const CLASS_DATATYPE_PUNNING_RULE: &str = "OWL2DL_CLASS_DATATYPE_PUNNING";
const RESERVED_VOCABULARY_RULE: &str = "OWL2DL_RESERVED_VOCABULARY";
const BUILTIN_ENTITY_KIND_RULE: &str = "OWL2DL_BUILTIN_ENTITY_KIND";
const MISSING_DECLARATION_RULE: &str = "OWL2DL_MISSING_DECLARATION";
const BUILTIN_DATATYPE_REDEFINITION_RULE: &str = "BUILTIN_DATATYPE_REDEFINITION";
const BUILTIN_DATATYPE_REDEFINITION_MESSAGE: &str = "built-in OWL datatypes cannot be redefined";
const DUPLICATE_DATATYPE_DEFINITION_RULE: &str = "DUPLICATE_DATATYPE_DEFINITION";
const DUPLICATE_DATATYPE_DEFINITION_MESSAGE: &str =
    "each custom datatype must have exactly one definition";
const UNSUPPORTED_DATATYPE_RULE: &str = "UNSUPPORTED_DATATYPE";
const UNSUPPORTED_DATATYPE_MESSAGE: &str =
    "datatype is outside the implemented OWL 2 map and has no definition";
const UNSUPPORTED_LITERAL_DATATYPE_MESSAGE: &str =
    "datatype is outside the implemented OWL 2 datatype map";
const UNSUPPORTED_DATATYPE_OPAQUE_RULE: &str = "UNSUPPORTED_DATATYPE_OPAQUE";
const UNSUPPORTED_DATATYPE_OPAQUE_MESSAGE_PREFIX: &str =
    "unsupported datatype is treated as opaque: ";
const RECURSIVE_DATATYPE_DEFINITION_RULE: &str = "RECURSIVE_DATATYPE_DEFINITION";
const RECURSIVE_DATATYPE_DEFINITION_MESSAGE: &str =
    "custom datatype definitions must form an acyclic graph";
const CUSTOM_DATATYPE_LITERAL_RULE: &str = "CUSTOM_DATATYPE_LITERAL";
const CUSTOM_DATATYPE_LITERAL_MESSAGE_PREFIX: &str =
    "a datatype defined in the ontology has no lexical space and cannot be used on a literal: ";
const INVALID_LITERAL_RULE: &str = "INVALID_LITERAL";
const INVALID_LITERAL_MESSAGE: &str = "literal lexical form is outside the datatype lexical space";
const INVALID_XML_LITERAL_MESSAGE: &str = "rdf:XMLLiteral is not a well-formed XML fragment";
const FORBIDDEN_XML_LITERAL_MESSAGE: &str = "rdf:XMLLiteral forbids DTD and entity declarations";
const ILLEGAL_DATATYPE_FACET_RULE: &str = "ILLEGAL_DATATYPE_FACET";
const ILLEGAL_DATATYPE_FACET_MESSAGE: &str = "facet is not legal for the restricted OWL 2 datatype";
const INVALID_FACET_VALUE_RULE: &str = "INVALID_FACET_VALUE";
const INVALID_FACET_VALUE_MESSAGE: &str = "facet literal has the wrong datatype or value domain";
const INVALID_LANGUAGE_RANGE_MESSAGE: &str =
    "rdf:langRange requires an RFC 4647 basic language range";
const RIA_INVERSE_RECURSION_RULE: &str = "RIA_INVERSE_RECURSION";
const RIA_INVERSE_RECURSION_MESSAGE: &str =
    "a complex subproperty chain contains the inverse of its super role";
const RIA_NON_REGULAR_RECURSION_RULE: &str = "RIA_NON_REGULAR_RECURSION";
const RIA_NON_REGULAR_RECURSION_MESSAGE: &str =
    "the super role occurs outside a legal chain boundary pattern";
const RIA_DEPENDENCY_CYCLE_RULE: &str = "RIA_DEPENDENCY_CYCLE";
const RIA_DEPENDENCY_CYCLE_MESSAGE: &str =
    "complex role inclusions create a strict dependency cycle";
const NON_SIMPLE_PROPERTY_RULE: &str = "OWL2DL_NON_SIMPLE_PROPERTY";
const NON_SIMPLE_PROPERTY_MESSAGE: &str =
    "axiom position requires a simple object property expression";
const EXTENSION_COMPONENT_RULE: &str = "OWL2DL_EXTENSION_COMPONENT";
const EXTENSION_COMPONENT_MESSAGE: &str =
    "extension components such as SWRL are outside the OWL 2 DL reasoner scope";
const PROFILE_MANIFEST_BASE_BOUND: usize = 256;
const PROFILE_MANIFEST_ISSUE_BOUND: usize = 640;
const RESERVED_PREFIXES: &[&[u8]] = &[
    b"http://www.w3.org/1999/02/22-rdf-syntax-ns#",
    b"http://www.w3.org/2000/01/rdf-schema#",
    b"http://www.w3.org/2001/XMLSchema#",
    b"http://www.w3.org/2002/07/owl#",
];
const BUILTIN_CLASSES: &[&[u8]] = &[
    b"http://www.w3.org/2002/07/owl#Thing",
    b"http://www.w3.org/2002/07/owl#Nothing",
];
const BUILTIN_OBJECT_PROPERTIES: &[&[u8]] = &[
    b"http://www.w3.org/2002/07/owl#topObjectProperty",
    b"http://www.w3.org/2002/07/owl#bottomObjectProperty",
];
const BUILTIN_DATA_PROPERTIES: &[&[u8]] = &[
    b"http://www.w3.org/2002/07/owl#topDataProperty",
    b"http://www.w3.org/2002/07/owl#bottomDataProperty",
];
const BUILTIN_ANNOTATION_PROPERTIES: &[&[u8]] = &[
    b"http://www.w3.org/2000/01/rdf-schema#label",
    b"http://www.w3.org/2000/01/rdf-schema#comment",
    b"http://www.w3.org/2000/01/rdf-schema#seeAlso",
    b"http://www.w3.org/2000/01/rdf-schema#isDefinedBy",
    b"http://www.w3.org/2002/07/owl#deprecated",
    b"http://www.w3.org/2002/07/owl#versionInfo",
    b"http://www.w3.org/2002/07/owl#priorVersion",
    b"http://www.w3.org/2002/07/owl#backwardCompatibleWith",
    b"http://www.w3.org/2002/07/owl#incompatibleWith",
];
const BUILTIN_DATATYPES: &[&[u8]] = &[
    b"http://www.w3.org/2002/07/owl#real",
    b"http://www.w3.org/2002/07/owl#rational",
    b"http://www.w3.org/2001/XMLSchema#decimal",
    b"http://www.w3.org/2001/XMLSchema#integer",
    b"http://www.w3.org/2001/XMLSchema#nonNegativeInteger",
    b"http://www.w3.org/2001/XMLSchema#positiveInteger",
    b"http://www.w3.org/2001/XMLSchema#nonPositiveInteger",
    b"http://www.w3.org/2001/XMLSchema#negativeInteger",
    b"http://www.w3.org/2001/XMLSchema#long",
    b"http://www.w3.org/2001/XMLSchema#int",
    b"http://www.w3.org/2001/XMLSchema#short",
    b"http://www.w3.org/2001/XMLSchema#byte",
    b"http://www.w3.org/2001/XMLSchema#unsignedLong",
    b"http://www.w3.org/2001/XMLSchema#unsignedInt",
    b"http://www.w3.org/2001/XMLSchema#unsignedShort",
    b"http://www.w3.org/2001/XMLSchema#unsignedByte",
    b"http://www.w3.org/2001/XMLSchema#boolean",
    b"http://www.w3.org/2001/XMLSchema#float",
    b"http://www.w3.org/2001/XMLSchema#double",
    b"http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral",
    b"http://www.w3.org/2001/XMLSchema#string",
    b"http://www.w3.org/2001/XMLSchema#normalizedString",
    b"http://www.w3.org/2001/XMLSchema#token",
    b"http://www.w3.org/2001/XMLSchema#language",
    b"http://www.w3.org/2001/XMLSchema#Name",
    b"http://www.w3.org/2001/XMLSchema#NCName",
    b"http://www.w3.org/2001/XMLSchema#NMTOKEN",
    b"http://www.w3.org/2001/XMLSchema#hexBinary",
    b"http://www.w3.org/2001/XMLSchema#base64Binary",
    b"http://www.w3.org/2001/XMLSchema#anyURI",
    b"http://www.w3.org/2001/XMLSchema#dateTime",
    b"http://www.w3.org/2001/XMLSchema#dateTimeStamp",
    b"http://www.w3.org/1999/02/22-rdf-syntax-ns#XMLLiteral",
    b"http://www.w3.org/2000/01/rdf-schema#Literal",
];
const TOP_OBJECT_PROPERTY_IRI: &[u8] = b"http://www.w3.org/2002/07/owl#topObjectProperty";
const BOTTOM_OBJECT_PROPERTY_IRI: &[u8] = b"http://www.w3.org/2002/07/owl#bottomObjectProperty";
const XSD_NAMESPACE: &str = "http://www.w3.org/2001/XMLSchema#";
const RDF_PLAIN_LITERAL_IRI: &str = "http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral";
const RDF_XML_LITERAL_IRI: &str = "http://www.w3.org/1999/02/22-rdf-syntax-ns#XMLLiteral";
const RDF_LANG_RANGE_IRI: &str = "http://www.w3.org/1999/02/22-rdf-syntax-ns#langRange";
const RDFS_LITERAL_IRI: &str = "http://www.w3.org/2000/01/rdf-schema#Literal";
const OWL_REAL_IRI: &str = "http://www.w3.org/2002/07/owl#real";
const OWL_RATIONAL_IRI: &str = "http://www.w3.org/2002/07/owl#rational";
const XSD_MIN_INCLUSIVE_IRI: &str = "http://www.w3.org/2001/XMLSchema#minInclusive";
const XSD_MIN_EXCLUSIVE_IRI: &str = "http://www.w3.org/2001/XMLSchema#minExclusive";
const XSD_MAX_INCLUSIVE_IRI: &str = "http://www.w3.org/2001/XMLSchema#maxInclusive";
const XSD_MAX_EXCLUSIVE_IRI: &str = "http://www.w3.org/2001/XMLSchema#maxExclusive";
const XSD_LENGTH_IRI: &str = "http://www.w3.org/2001/XMLSchema#length";
const XSD_MIN_LENGTH_IRI: &str = "http://www.w3.org/2001/XMLSchema#minLength";
const XSD_MAX_LENGTH_IRI: &str = "http://www.w3.org/2001/XMLSchema#maxLength";
const XSD_PATTERN_IRI: &str = "http://www.w3.org/2001/XMLSchema#pattern";

/// Scalar-compatible handling for datatypes outside the implemented OWL 2 map.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum ProfileUnsupportedDatatypePolicy {
    #[default]
    Error,
    IgnoreWithWarning,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ProfilePhaseLimits {
    pub max_slices: usize,
    pub max_ontology_documents: usize,
    pub max_axioms: usize,
    pub max_extensions: usize,
    pub max_issues: usize,
    pub max_anonymous_vertices: usize,
    pub max_anonymous_assertions: usize,
    pub max_entity_uses: usize,
    pub max_entity_declarations: usize,
    pub max_datatype_definitions: usize,
    pub max_datatype_references: usize,
    pub max_datatype_failures: usize,
    pub max_literal_datatypes: usize,
    pub max_role_inclusions: usize,
    pub max_complex_role_inclusions: usize,
    pub max_role_dependency_edges: usize,
    pub max_non_simple_role_seeds: usize,
    pub max_simple_role_requirements: usize,
    pub max_owned_bytes: usize,
    pub max_work: u64,
    pub max_manifest_bytes: usize,
    pub max_canonical_depth: usize,
    pub max_scope_maps: usize,
}

impl Default for ProfilePhaseLimits {
    fn default() -> Self {
        Self {
            max_slices: 32_769,
            max_ontology_documents: 10_000_000,
            max_axioms: 10_000_000,
            max_extensions: 10_000_000,
            max_issues: 10_000_000,
            max_anonymous_vertices: 10_000_000,
            max_anonymous_assertions: 10_000_000,
            max_entity_uses: 10_000_000,
            max_entity_declarations: 10_000_000,
            max_datatype_definitions: 10_000_000,
            max_datatype_references: 100_000_000,
            max_datatype_failures: 10_000_000,
            max_literal_datatypes: 10_000_000,
            max_role_inclusions: 100_000_000,
            max_complex_role_inclusions: 1_000_000,
            max_role_dependency_edges: 100_000_000,
            max_non_simple_role_seeds: 10_000_000,
            max_simple_role_requirements: 10_000_000,
            max_owned_bytes: 512 * 1024 * 1024,
            max_work: 2_000_000_000,
            max_manifest_bytes: 512 * 1024 * 1024,
            max_canonical_depth: 512,
            max_scope_maps: 32,
        }
    }
}

/// Exact scalar-compatible issue fields available in structural-columns v1.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ProfileIssue {
    pub rule_id: &'static str,
    pub severity: &'static str,
    pub message: Cow<'static, str>,
    pub constructor: Option<&'static str>,
    pub document_keys: Vec<String>,
    pub provenance_sha256: Option<[u8; 32]>,
}

type AnonymousKey = Vec<u8>;

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct AnonymousAssertion {
    axiom_key: Vec<u8>,
    provenance_sha256: [u8; 32],
    source: Option<AnonymousKey>,
    target: Option<AnonymousKey>,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum ProfileEntityKind {
    AnnotationProperty,
    Class,
    DataProperty,
    Datatype,
    NamedIndividual,
    ObjectProperty,
}

impl ProfileEntityKind {
    fn from_scalar<B: ByteSource>(value: ScalarRef<B>) -> EncodedResult<Self> {
        if value.kind() != ComponentKind::Enum {
            return Err(EncodedValidationError::invariant(
                "validated profile entity kind is not an enum",
            ));
        }
        if value.bytes_equal(b"annotation_property") {
            Ok(Self::AnnotationProperty)
        } else if value.bytes_equal(b"class") {
            Ok(Self::Class)
        } else if value.bytes_equal(b"data_property") {
            Ok(Self::DataProperty)
        } else if value.bytes_equal(b"datatype") {
            Ok(Self::Datatype)
        } else if value.bytes_equal(b"named_individual") {
            Ok(Self::NamedIndividual)
        } else if value.bytes_equal(b"object_property") {
            Ok(Self::ObjectProperty)
        } else {
            Err(EncodedValidationError::invariant(
                "validated profile entity kind is no longer recognized",
            ))
        }
    }

    const fn as_str(self) -> &'static str {
        match self {
            Self::AnnotationProperty => "annotation_property",
            Self::Class => "class",
            Self::DataProperty => "data_property",
            Self::Datatype => "datatype",
            Self::NamedIndividual => "named_individual",
            Self::ObjectProperty => "object_property",
        }
    }

    const fn is_property(self) -> bool {
        matches!(
            self,
            Self::AnnotationProperty | Self::DataProperty | Self::ObjectProperty
        )
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ProfileEntityIdentity {
    iri: Vec<u8>,
    kind: ProfileEntityKind,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ProfileDatatypeDefinition {
    statement_order_key: Vec<u8>,
    datatype_iri: Vec<u8>,
    references: Vec<Vec<u8>>,
    failure: Option<ProfileDatatypeFailure>,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum ProfileDatatypeFailure {
    InvalidLiteral(ProfileLiteralInvalid),
    UnsupportedRange,
    UnsupportedLiteral,
    IllegalFacet,
    InvalidFacetValue,
    InvalidLanguageRange,
    Suppressed,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ProfileDatatypeRangeFailure {
    canonical_key: Vec<u8>,
    failure: ProfileDatatypeFailure,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ProfileLiteralFact {
    canonical_key: Vec<u8>,
    datatype_iri: Vec<u8>,
    failure: Option<ProfileDatatypeFailure>,
}

#[derive(Clone, Copy)]
struct ProfileDatatypeFacts<'a> {
    uses: &'a [ProfileEntityIdentity],
    definitions: &'a [ProfileDatatypeDefinition],
    range_failures: &'a [ProfileDatatypeRangeFailure],
    literals: &'a [ProfileLiteralFact],
}

/// One validated row from the private ontology-identity context schema.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ProfileOntologyIdentifier {
    pub document_key: Vec<u8>,
    pub ontology_iri: Option<Vec<u8>>,
    pub version_iri: Option<Vec<u8>>,
}

/// One canonical root-digest-to-document row from the private origin side context.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ProfileOrigin {
    pub root_digest_sha256: [u8; 32],
    pub document_keys: Vec<String>,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ProfileRootDigestBridge {
    raw_provenance_sha256: [u8; 32],
    core_structural_sha256: [u8; 32],
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ProfileOriginDigestDomain {
    RawProvenance,
    CoreStructural,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ProfileObjectRole {
    iri: Vec<u8>,
    inverse: bool,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ProfileRoleInclusion {
    sub_role: ProfileObjectRole,
    super_role: ProfileObjectRole,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ProfileComplexRoleInclusion {
    super_role: ProfileObjectRole,
    chain_roles: Vec<ProfileObjectRole>,
    inverse_generated: bool,
    statement_order_key: Vec<u8>,
    provenance_sha256: [u8; 32],
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ProfileSimpleRoleRequirement {
    role: ProfileObjectRole,
    constructor: &'static str,
    provenance_sha256: [u8; 32],
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ProfileIndexedComplexRoleInclusion {
    fact_index: usize,
    super_role_id: usize,
    chain_role_ids: Vec<usize>,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ProfileDependencyEdge {
    dependency: usize,
    consumer: usize,
    source_index: Option<usize>,
}

/// Transactional profile result. Violations never use the error channel.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProfilePhase {
    pub issues: Vec<ProfileIssue>,
    pub conforms: bool,
    pub axioms_checked: usize,
    pub extensions_checked: usize,
    pub work: u64,
    pub owned_bytes: usize,
    axiom_keys: Vec<Vec<u8>>,
    extension_keys: Vec<Vec<u8>>,
    anonymous_vertices: Vec<AnonymousKey>,
    anonymous_assertions: Vec<AnonymousAssertion>,
    entity_uses: Vec<ProfileEntityIdentity>,
    entity_declarations: Vec<ProfileEntityIdentity>,
    datatype_definitions: Vec<ProfileDatatypeDefinition>,
    datatype_range_failures: Vec<ProfileDatatypeRangeFailure>,
    literals: Vec<ProfileLiteralFact>,
    role_inclusions: Vec<ProfileRoleInclusion>,
    complex_role_inclusions: Vec<ProfileComplexRoleInclusion>,
    non_simple_role_seeds: Vec<ProfileObjectRole>,
    simple_role_requirements: Vec<ProfileSimpleRoleRequirement>,
    manifest_limit: usize,
}

impl ProfilePhase {
    /// Canonical private manifest used for exact scalar differential checks.
    pub fn canonical_manifest_json(&self) -> EncodedResult<Vec<u8>> {
        self.canonical_manifest_json_with_origins(false)
    }

    /// Canonical private manifest including the full scalar origin projection.
    pub fn canonical_origin_manifest_json(&self) -> EncodedResult<Vec<u8>> {
        self.canonical_manifest_json_with_origins(true)
    }

    fn canonical_manifest_json_with_origins(
        &self,
        include_origins: bool,
    ) -> EncodedResult<Vec<u8>> {
        validate_phase(self)?;
        let issue_bound = self.issues.iter().try_fold(0_usize, |total, issue| {
            let document_bound =
                issue
                    .document_keys
                    .iter()
                    .try_fold(0_usize, |document_total, document_key| {
                        document_key
                            .len()
                            .checked_mul(6)
                            .and_then(|value| document_total.checked_add(value))
                            .ok_or_else(|| {
                                EncodedValidationError::resource(
                                    "profile manifest document-key bound overflowed",
                                )
                            })
                    })?;
            issue
                .message
                .len()
                .checked_mul(6)
                .and_then(|message| message.checked_add(PROFILE_MANIFEST_ISSUE_BOUND))
                .and_then(|issue| issue.checked_add(document_bound))
                .and_then(|issue| total.checked_add(issue))
                .ok_or_else(|| {
                    EncodedValidationError::resource("profile manifest size bound overflowed")
                })
        })?;
        let manifest_bound = issue_bound
            .checked_add(PROFILE_MANIFEST_BASE_BOUND)
            .ok_or_else(|| {
                EncodedValidationError::resource("profile manifest size bound overflowed")
            })?;
        if manifest_bound > self.manifest_limit {
            return Err(EncodedValidationError::resource(
                "profile manifest exceeds its byte limit",
            ));
        }
        let mut ordered_rule_ids = Vec::new();
        reserve_exact(
            &mut ordered_rule_ids,
            self.issues.len(),
            "profile rule-ID manifest allocation failed",
        )?;
        ordered_rule_ids.extend(self.issues.iter().map(|issue| issue.rule_id));

        let mut issues = Vec::new();
        reserve_exact(
            &mut issues,
            self.issues.len(),
            "profile issue manifest allocation failed",
        )?;
        issues.extend(self.issues.iter().map(|issue| {
            ProfileIssueManifest {
                rule_id: issue.rule_id,
                severity: issue.severity,
                message: issue.message.as_ref(),
                constructor: issue.constructor,
                document_keys: include_origins.then_some(issue.document_keys.as_slice()),
                provenance_sha256: issue
                    .provenance_sha256
                    .map(|value| crate::model::hex(&value)),
            }
        }));
        let encoded = serde_json::to_vec(&ProfileManifest {
            schema_version: PROFILE_PHASE_SCHEMA_VERSION,
            family: "owl2_dl_profile",
            conforms: self.conforms,
            axioms_checked: self.axioms_checked,
            extensions_checked: self.extensions_checked,
            ordered_rule_ids,
            issues,
        })
        .map_err(|_| EncodedValidationError::invariant("profile manifest serialization failed"))?;
        if encoded.len() > self.manifest_limit {
            return Err(EncodedValidationError::resource(
                "profile manifest exceeds its byte limit",
            ));
        }
        Ok(encoded)
    }
}

#[derive(Serialize)]
struct ProfileManifest<'a> {
    schema_version: u16,
    family: &'static str,
    conforms: bool,
    axioms_checked: usize,
    extensions_checked: usize,
    ordered_rule_ids: Vec<&'a str>,
    issues: Vec<ProfileIssueManifest<'a>>,
}

#[derive(Serialize)]
struct ProfileIssueManifest<'a> {
    rule_id: &'a str,
    severity: &'a str,
    message: &'a str,
    constructor: Option<&'a str>,
    #[serde(skip_serializing_if = "Option::is_none")]
    document_keys: Option<&'a [String]>,
    provenance_sha256: Option<String>,
}

/// Separates encoded operational failures from caller-owned cancellation.
#[derive(Debug, Eq, PartialEq)]
pub enum ProfilePhaseError<E> {
    Encoded(EncodedValidationError),
    Control(E),
}

impl<E> From<EncodedValidationError> for ProfilePhaseError<E> {
    fn from(error: EncodedValidationError) -> Self {
        Self::Encoded(error)
    }
}

type ControlledResult<T, E> = Result<T, ProfilePhaseError<E>>;

struct PhaseBudget {
    limits: ProfilePhaseLimits,
    work: u64,
    owned_bytes: usize,
    datatype_references: usize,
}

impl PhaseBudget {
    const fn new(limits: ProfilePhaseLimits) -> Self {
        Self {
            limits,
            work: 0,
            owned_bytes: 0,
            datatype_references: 0,
        }
    }

    fn claim_work(&mut self, amount: usize) -> EncodedResult<()> {
        let amount = u64::try_from(amount)
            .map_err(|_| EncodedValidationError::resource("profile work exceeds u64"))?;
        self.claim_work_u64(amount)
    }

    fn claim_work_u64(&mut self, amount: u64) -> EncodedResult<()> {
        let following = self
            .work
            .checked_add(amount)
            .ok_or_else(|| EncodedValidationError::resource("profile work overflowed"))?;
        if following > self.limits.max_work {
            return Err(EncodedValidationError::resource(
                "profile compilation exceeds its work limit",
            ));
        }
        self.work = following;
        Ok(())
    }

    fn claim_owned(&mut self, amount: usize) -> EncodedResult<()> {
        let following = self.owned_bytes.checked_add(amount).ok_or_else(|| {
            EncodedValidationError::resource("profile owned-byte count overflowed")
        })?;
        if following > self.limits.max_owned_bytes {
            return Err(EncodedValidationError::resource(
                "profile compilation exceeds its owned-byte limit",
            ));
        }
        self.owned_bytes = following;
        Ok(())
    }

    fn claim_axiom(&self, following: usize) -> EncodedResult<()> {
        if following > self.limits.max_axioms {
            Err(EncodedValidationError::resource(
                "profile axiom count exceeds its limit",
            ))
        } else {
            Ok(())
        }
    }

    fn claim_ontology_document(&self, following: usize) -> EncodedResult<()> {
        if following > self.limits.max_ontology_documents {
            Err(EncodedValidationError::resource(
                "profile ontology document count exceeds its limit",
            ))
        } else {
            Ok(())
        }
    }

    fn claim_extension(&self, following: usize) -> EncodedResult<()> {
        if following > self.limits.max_extensions {
            Err(EncodedValidationError::resource(
                "profile extension count exceeds its limit",
            ))
        } else {
            Ok(())
        }
    }

    fn claim_issue(&self, following: usize) -> EncodedResult<()> {
        if following > self.limits.max_issues {
            Err(EncodedValidationError::resource(
                "profile issue count exceeds its limit",
            ))
        } else {
            Ok(())
        }
    }

    fn claim_anonymous_vertex(&self, following: usize) -> EncodedResult<()> {
        if following > self.limits.max_anonymous_vertices {
            Err(EncodedValidationError::resource(
                "profile anonymous vertex count exceeds its limit",
            ))
        } else {
            Ok(())
        }
    }

    fn claim_anonymous_assertion(&self, following: usize) -> EncodedResult<()> {
        if following > self.limits.max_anonymous_assertions {
            Err(EncodedValidationError::resource(
                "profile anonymous assertion count exceeds its limit",
            ))
        } else {
            Ok(())
        }
    }

    fn claim_entity_use(&self, following: usize) -> EncodedResult<()> {
        if following > self.limits.max_entity_uses {
            Err(EncodedValidationError::resource(
                "profile entity use count exceeds its limit",
            ))
        } else {
            Ok(())
        }
    }

    fn claim_entity_declaration(&self, following: usize) -> EncodedResult<()> {
        if following > self.limits.max_entity_declarations {
            Err(EncodedValidationError::resource(
                "profile entity declaration count exceeds its limit",
            ))
        } else {
            Ok(())
        }
    }

    fn claim_datatype_definition(&self, following: usize) -> EncodedResult<()> {
        if following > self.limits.max_datatype_definitions {
            Err(EncodedValidationError::resource(
                "profile datatype definition count exceeds its limit",
            ))
        } else {
            Ok(())
        }
    }

    fn claim_datatype_reference(&mut self, additional: usize) -> EncodedResult<()> {
        let following = self
            .datatype_references
            .checked_add(additional)
            .ok_or_else(|| {
                EncodedValidationError::resource("profile datatype reference count overflowed")
            })?;
        if following > self.limits.max_datatype_references {
            Err(EncodedValidationError::resource(
                "profile datatype reference count exceeds its limit",
            ))
        } else {
            self.datatype_references = following;
            Ok(())
        }
    }

    fn claim_datatype_failure(&self, following: usize) -> EncodedResult<()> {
        if following > self.limits.max_datatype_failures {
            Err(EncodedValidationError::resource(
                "profile datatype failure count exceeds its limit",
            ))
        } else {
            Ok(())
        }
    }

    fn claim_literal_datatype(&self, following: usize) -> EncodedResult<()> {
        if following > self.limits.max_literal_datatypes {
            Err(EncodedValidationError::resource(
                "profile literal datatype count exceeds its limit",
            ))
        } else {
            Ok(())
        }
    }

    fn claim_role_inclusion(&self, following: usize) -> EncodedResult<()> {
        if following > self.limits.max_role_inclusions {
            Err(EncodedValidationError::resource(
                "profile role inclusion count exceeds its limit",
            ))
        } else {
            Ok(())
        }
    }

    fn claim_complex_role_inclusion(&self, following: usize) -> EncodedResult<()> {
        if following > self.limits.max_complex_role_inclusions {
            Err(EncodedValidationError::resource(
                "profile complex role inclusion count exceeds its limit",
            ))
        } else {
            Ok(())
        }
    }

    fn claim_non_simple_role_seed(&self, following: usize) -> EncodedResult<()> {
        if following > self.limits.max_non_simple_role_seeds {
            Err(EncodedValidationError::resource(
                "profile non-simple role seed count exceeds its limit",
            ))
        } else {
            Ok(())
        }
    }

    fn claim_simple_role_requirement(&self, following: usize) -> EncodedResult<()> {
        if following > self.limits.max_simple_role_requirements {
            Err(EncodedValidationError::resource(
                "profile simple-role requirement count exceeds its limit",
            ))
        } else {
            Ok(())
        }
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

#[derive(Clone, Copy)]
struct RootPostings<S: ByteSource> {
    postings: S,
    count: usize,
    cursor: usize,
}

impl<S: ByteSource> RootPostings<S> {
    fn new(postings: S, root_count: usize, name: &'static str) -> EncodedResult<Self> {
        if postings.len() % 4 != 0 {
            return Err(EncodedValidationError::protocol(format!(
                "encoded profile root {name} contain a partial u32"
            )));
        }
        let count = postings.len() / 4;
        if count == 0 {
            return Err(EncodedValidationError::protocol(format!(
                "encoded profile root {name} are empty"
            )));
        }
        let mut previous = 0_usize;
        for index in 0..count {
            let current = usize::try_from(u32_at(postings, index, name)?).map_err(|_| {
                EncodedValidationError::resource(format!(
                    "encoded profile root {name} exceeds the platform index width"
                ))
            })?;
            if current <= previous || current > root_count {
                return Err(EncodedValidationError::protocol(format!(
                    "encoded profile root {name} are not sorted unique in-range IDs"
                )));
            }
            previous = current;
        }
        Ok(Self {
            postings,
            count,
            cursor: 0,
        })
    }

    fn contains(&mut self, root_index: usize) -> EncodedResult<bool> {
        if self.cursor >= self.count {
            return Ok(false);
        }
        let current = usize::try_from(u32_at(self.postings, self.cursor, "profile root posting")?)
            .map_err(|_| {
                EncodedValidationError::resource(
                    "encoded profile root posting exceeds the platform index width",
                )
            })?;
        let local_root_id = root_index.checked_add(1).ok_or_else(|| {
            EncodedValidationError::resource("encoded profile root index overflowed")
        })?;
        if current == local_root_id {
            self.cursor += 1;
            Ok(true)
        } else {
            Ok(false)
        }
    }
}

#[derive(Clone, Copy)]
enum RootSelection<S: ByteSource> {
    All,
    Include(RootPostings<S>),
    Exclude(RootPostings<S>),
}

impl<S: ByteSource> RootSelection<S> {
    const fn selected_count(&self, root_count: usize) -> usize {
        match self {
            Self::All => root_count,
            Self::Include(postings) => postings.count,
            Self::Exclude(postings) => root_count - postings.count,
        }
    }

    const fn validation_work(&self) -> usize {
        match self {
            Self::All => 0,
            Self::Include(postings) | Self::Exclude(postings) => postings.count,
        }
    }

    fn excludes(&mut self, root_index: usize) -> EncodedResult<bool> {
        match self {
            Self::All => Ok(false),
            Self::Include(postings) => Ok(!postings.contains(root_index)?),
            Self::Exclude(postings) => postings.contains(root_index),
        }
    }
}

/// Compile all roots with a no-op control.
pub fn compile_profile_phase<B: ByteSource>(
    model: &ValidatedModel<B>,
    scope_maps: &[AnonymousScopeMap],
    limits: ProfilePhaseLimits,
) -> EncodedResult<ProfilePhase> {
    let mut control = |_phase| Ok::<(), Infallible>(());
    into_encoded(compile_profile_phase_controlled(
        model,
        scope_maps,
        limits,
        &mut control,
    ))
}

/// Compile all roots while polling caller-owned cancellation within the phase.
pub fn compile_profile_phase_controlled<B: ByteSource, E>(
    model: &ValidatedModel<B>,
    scope_maps: &[AnonymousScopeMap],
    limits: ProfilePhaseLimits,
    control: &mut impl FnMut(&'static str) -> Result<(), E>,
) -> ControlledResult<ProfilePhase, E> {
    compile_profile_phase_controlled_with_policy(
        model,
        scope_maps,
        limits,
        ProfileUnsupportedDatatypePolicy::Error,
        control,
    )
}

/// Compile all roots with scalar-compatible unsupported-datatype handling.
pub fn compile_profile_phase_controlled_with_policy<B: ByteSource, E>(
    model: &ValidatedModel<B>,
    scope_maps: &[AnonymousScopeMap],
    limits: ProfilePhaseLimits,
    unsupported_datatypes: ProfileUnsupportedDatatypePolicy,
    control: &mut impl FnMut(&'static str) -> Result<(), E>,
) -> ControlledResult<ProfilePhase, E> {
    compile_profile_phase_with_selection(
        model,
        scope_maps,
        limits,
        RootSelection::<&[u8]>::All,
        unsupported_datatypes,
        control,
    )
}

/// Compile a source-local ALL, INCLUDE, or EXCLUDE selection.
pub fn compile_profile_phase_selected_controlled<B: ByteSource, S: ByteSource, E>(
    model: &ValidatedModel<B>,
    scope_maps: &[AnonymousScopeMap],
    limits: ProfilePhaseLimits,
    posting_mode: u8,
    postings: S,
    control: &mut impl FnMut(&'static str) -> Result<(), E>,
) -> ControlledResult<ProfilePhase, E> {
    compile_profile_phase_selected_controlled_with_policy(
        model,
        scope_maps,
        limits,
        posting_mode,
        postings,
        ProfileUnsupportedDatatypePolicy::Error,
        control,
    )
}

/// Compile one selected source with scalar-compatible unsupported-datatype handling.
pub fn compile_profile_phase_selected_controlled_with_policy<B: ByteSource, S: ByteSource, E>(
    model: &ValidatedModel<B>,
    scope_maps: &[AnonymousScopeMap],
    limits: ProfilePhaseLimits,
    posting_mode: u8,
    postings: S,
    unsupported_datatypes: ProfileUnsupportedDatatypePolicy,
    control: &mut impl FnMut(&'static str) -> Result<(), E>,
) -> ControlledResult<ProfilePhase, E> {
    let selection = match posting_mode {
        POSTINGS_ALL if postings.is_empty() => RootSelection::All,
        POSTINGS_ALL => {
            return Err(EncodedValidationError::protocol(
                "ALL encoded profile root selection carries postings",
            )
            .into());
        }
        POSTINGS_INCLUDE => RootSelection::Include(
            RootPostings::new(postings, model.summary().root_count, "inclusions")
                .map_err(ProfilePhaseError::Encoded)?,
        ),
        POSTINGS_EXCLUDE => RootSelection::Exclude(
            RootPostings::new(postings, model.summary().root_count, "exclusions")
                .map_err(ProfilePhaseError::Encoded)?,
        ),
        _ => {
            return Err(EncodedValidationError::protocol(
                "encoded profile root selection mode is unsupported",
            )
            .into());
        }
    };
    compile_profile_phase_with_selection(
        model,
        scope_maps,
        limits,
        selection,
        unsupported_datatypes,
        control,
    )
}

fn compile_profile_phase_with_selection<B: ByteSource, S: ByteSource, E>(
    model: &ValidatedModel<B>,
    scope_maps: &[AnonymousScopeMap],
    limits: ProfilePhaseLimits,
    mut selection: RootSelection<S>,
    unsupported_datatypes: ProfileUnsupportedDatatypePolicy,
    control: &mut impl FnMut(&'static str) -> Result<(), E>,
) -> ControlledResult<ProfilePhase, E> {
    poll(control, "profile-preflight")?;
    let summary = model.summary();
    let mut budget = PhaseBudget::new(limits);
    let mut literal_budget = LiteralPhaseBudget::new(NamedClassPhaseLimits {
        max_work: limits.max_work,
        max_owned_bytes: limits.max_owned_bytes,
        ..NamedClassPhaseLimits::default()
    });
    canonical::validate_scope_maps(scope_maps, &mut budget).map_err(ProfilePhaseError::Encoded)?;
    budget
        .claim_work(selection.validation_work())
        .map_err(ProfilePhaseError::Encoded)?;

    let node_count = summary.node_count;
    budget
        .claim_owned(node_count)
        .map_err(ProfilePhaseError::Encoded)?;
    budget
        .claim_owned(node_count.checked_mul(size_of::<NodeId>()).ok_or_else(|| {
            EncodedValidationError::resource("profile traversal stack size overflowed")
        })?)
        .map_err(ProfilePhaseError::Encoded)?;
    let mut marks = Vec::new();
    reserve_exact(
        &mut marks,
        node_count,
        "profile traversal mark allocation failed",
    )
    .map_err(ProfilePhaseError::Encoded)?;
    marks.resize(node_count, 0_u32);
    budget
        .claim_owned(node_count)
        .map_err(ProfilePhaseError::Encoded)?;
    let mut anonymous_seen = Vec::new();
    reserve_exact(
        &mut anonymous_seen,
        node_count,
        "profile anonymous-node mark allocation failed",
    )
    .map_err(ProfilePhaseError::Encoded)?;
    anonymous_seen.resize(node_count, 0_u8);
    budget
        .claim_owned(node_count)
        .map_err(ProfilePhaseError::Encoded)?;
    let mut entity_seen = Vec::new();
    reserve_exact(
        &mut entity_seen,
        node_count,
        "profile entity-node mark allocation failed",
    )
    .map_err(ProfilePhaseError::Encoded)?;
    entity_seen.resize(node_count, 0_u8);
    let mut stack = Vec::new();
    reserve_exact(
        &mut stack,
        node_count,
        "profile traversal stack allocation failed",
    )
    .map_err(ProfilePhaseError::Encoded)?;

    let selected_count = selection.selected_count(summary.root_count);
    budget
        .claim_owned(
            selected_count
                .checked_mul(size_of::<Vec<u8>>())
                .ok_or_else(|| {
                    EncodedValidationError::resource(
                        "profile canonical axiom vector size overflowed",
                    )
                })?,
        )
        .map_err(ProfilePhaseError::Encoded)?;
    let mut axiom_keys = Vec::new();
    reserve_exact(
        &mut axiom_keys,
        selected_count,
        "profile canonical axiom allocation failed",
    )
    .map_err(ProfilePhaseError::Encoded)?;
    let mut extension_keys = Vec::new();
    let mut issues = Vec::new();
    let mut anonymous_vertices = Vec::new();
    let mut anonymous_assertions = Vec::new();
    let mut entity_uses = Vec::new();
    let mut entity_declarations = Vec::new();
    let mut datatype_definitions = Vec::new();
    let mut datatype_range_failures = Vec::new();
    let mut literals = Vec::new();
    let mut role_inclusions = Vec::new();
    let mut complex_role_inclusions = Vec::new();
    let mut non_simple_role_seeds = Vec::new();
    let mut simple_role_requirements = Vec::new();
    let mut epoch = 0_u32;

    for root_index in 0..summary.root_count {
        poll(control, "profile-root")?;
        budget.claim_work(1).map_err(ProfilePhaseError::Encoded)?;
        if selection
            .excludes(root_index)
            .map_err(ProfilePhaseError::Encoded)?
        {
            continue;
        }
        let root = model
            .root(root_index)
            .map_err(ProfilePhaseError::Encoded)?
            .ok_or_else(|| {
                ProfilePhaseError::Encoded(EncodedValidationError::invariant(
                    "validated profile root row disappeared",
                ))
            })?;
        match root.kind() {
            RootKind::OntologyAnnotation => {
                epoch = epoch.checked_add(1).ok_or_else(|| {
                    ProfilePhaseError::Encoded(EncodedValidationError::resource(
                        "profile traversal epoch overflowed",
                    ))
                })?;
                enqueue_node(root.node(), &mut marks, epoch, &mut stack)
                    .map_err(ProfilePhaseError::Encoded)?;
                while let Some(identifier) = stack.pop() {
                    poll(control, "profile-node")?;
                    budget.claim_work(1).map_err(ProfilePhaseError::Encoded)?;
                    let node = model.node(identifier).map_err(ProfilePhaseError::Encoded)?;
                    if node.tag() == ENTITY_TAG {
                        retain_entity_use(
                            model,
                            identifier,
                            &mut entity_seen,
                            &mut entity_uses,
                            &mut budget,
                        )
                        .map_err(ProfilePhaseError::Encoded)?;
                    }
                    if node.tag() == LITERAL_TAG {
                        retain_profile_literal(
                            model,
                            identifier,
                            scope_maps,
                            &mut literals,
                            &mut budget,
                            &mut literal_budget,
                            control,
                        )?;
                    }
                    if is_profile_complex_data_range(node.tag()) {
                        retain_profile_datatype_range_failure(
                            model,
                            identifier,
                            scope_maps,
                            &mut datatype_range_failures,
                            &mut budget,
                            &mut literal_budget,
                            control,
                        )?;
                    }
                    for field_index in node.fields() {
                        budget.claim_work(1).map_err(ProfilePhaseError::Encoded)?;
                        let component = required_component(
                            model
                                .field(field_index)
                                .map_err(ProfilePhaseError::Encoded)?,
                            "profile ontology annotation field",
                        )
                        .map_err(ProfilePhaseError::Encoded)?;
                        enqueue_component(
                            model,
                            component,
                            &mut marks,
                            epoch,
                            &mut stack,
                            &mut budget,
                        )
                        .map_err(ProfilePhaseError::Encoded)?;
                    }
                }
                continue;
            }
            RootKind::Axiom => {}
            RootKind::Extension => {
                budget
                    .claim_extension(extension_keys.len().checked_add(1).ok_or_else(|| {
                        EncodedValidationError::resource("profile extension count overflowed")
                    })?)
                    .map_err(ProfilePhaseError::Encoded)?;
                let node = model
                    .node(root.node())
                    .map_err(ProfilePhaseError::Encoded)?;
                if node.tag() != SWRL_RULE_TAG {
                    return Err(ProfilePhaseError::Encoded(
                        EncodedValidationError::invariant(
                            "validated profile extension root is not a SWRL rule",
                        ),
                    ));
                }
                poll(control, "profile-extension-provenance")?;
                let key =
                    canonical::canonical_node_key(model, root.node(), scope_maps, &mut budget)
                        .map_err(ProfilePhaseError::Encoded)?;
                budget
                    .claim_work(key.len())
                    .map_err(ProfilePhaseError::Encoded)?;
                let provenance_sha256: [u8; 32] = Sha256::digest(&key).into();
                budget
                    .claim_owned(size_of::<Vec<u8>>())
                    .map_err(ProfilePhaseError::Encoded)?;
                reserve_one(
                    &mut extension_keys,
                    "profile canonical extension allocation failed",
                )
                .map_err(ProfilePhaseError::Encoded)?;
                extension_keys.push(key);

                let following = issues.len().checked_add(1).ok_or_else(|| {
                    ProfilePhaseError::Encoded(EncodedValidationError::resource(
                        "profile issue count overflowed",
                    ))
                })?;
                budget
                    .claim_issue(following)
                    .map_err(ProfilePhaseError::Encoded)?;
                budget
                    .claim_owned(size_of::<ProfileIssue>())
                    .map_err(ProfilePhaseError::Encoded)?;
                reserve_one(&mut issues, "profile issue allocation failed")
                    .map_err(ProfilePhaseError::Encoded)?;
                issues.push(ProfileIssue {
                    rule_id: EXTENSION_COMPONENT_RULE,
                    severity: "error",
                    message: Cow::Borrowed(EXTENSION_COMPONENT_MESSAGE),
                    constructor: Some("SWRLRule"),
                    document_keys: Vec::new(),
                    provenance_sha256: Some(provenance_sha256),
                });
                continue;
            }
        }
        budget
            .claim_axiom(axiom_keys.len().checked_add(1).ok_or_else(|| {
                EncodedValidationError::resource("profile axiom count overflowed")
            })?)
            .map_err(ProfilePhaseError::Encoded)?;
        let axiom_tag = model
            .node(root.node())
            .map_err(ProfilePhaseError::Encoded)?
            .tag();
        let axiom_constructor = RootHandler::from_root(RootKind::Axiom, axiom_tag)
            .map_err(ProfilePhaseError::Encoded)?
            .as_str();
        if axiom_tag == DECLARATION_TAG {
            let identity = declaration_entity(model, root.node(), &mut budget)
                .map_err(ProfilePhaseError::Encoded)?;
            retain_entity_declaration(identity, &mut entity_declarations, &mut budget)
                .map_err(ProfilePhaseError::Encoded)?;
        }
        let anonymous_axiom_forbidden = matches!(
            axiom_tag,
            SAME_INDIVIDUAL_TAG
                | DIFFERENT_INDIVIDUALS_TAG
                | NEGATIVE_OBJECT_PROPERTY_ASSERTION_TAG
                | NEGATIVE_DATA_PROPERTY_ASSERTION_TAG
        );
        let top_data_property_allowed = allows_top_data_property(model, root.node(), &mut budget)
            .map_err(ProfilePhaseError::Encoded)?;

        poll(control, "profile-provenance")?;
        let key = canonical::canonical_node_key(model, root.node(), scope_maps, &mut budget)
            .map_err(ProfilePhaseError::Encoded)?;
        budget
            .claim_work(key.len())
            .map_err(ProfilePhaseError::Encoded)?;
        let provenance_sha256: [u8; 32] = Sha256::digest(&key).into();
        if axiom_tag == DATATYPE_DEFINITION_TAG {
            retain_profile_datatype_definition(
                model,
                root.node(),
                &key,
                &mut datatype_definitions,
                &mut budget,
                &mut literal_budget,
                control,
            )?;
        }
        retain_profile_role_axiom_facts(
            model,
            root.node(),
            &mut role_inclusions,
            &mut complex_role_inclusions,
            &mut non_simple_role_seeds,
            &key,
            provenance_sha256,
            &mut budget,
            control,
        )?;
        if axiom_tag == OBJECT_PROPERTY_ASSERTION_TAG {
            let (source, target) =
                anonymous_assertion_endpoints(model, root.node(), scope_maps, &mut budget)
                    .map_err(ProfilePhaseError::Encoded)?;
            if source.is_some() || target.is_some() {
                let following = anonymous_assertions.len().checked_add(1).ok_or_else(|| {
                    ProfilePhaseError::Encoded(EncodedValidationError::resource(
                        "profile anonymous assertion count overflowed",
                    ))
                })?;
                budget
                    .claim_anonymous_assertion(following)
                    .map_err(ProfilePhaseError::Encoded)?;
                let axiom_key = clone_profile_bytes(
                    &key,
                    &mut budget,
                    "profile anonymous assertion key allocation failed",
                )
                .map_err(ProfilePhaseError::Encoded)?;
                reserve_profile_one(
                    &mut anonymous_assertions,
                    &mut budget,
                    "profile anonymous assertion allocation failed",
                )
                .map_err(ProfilePhaseError::Encoded)?;
                anonymous_assertions.push(AnonymousAssertion {
                    axiom_key,
                    provenance_sha256,
                    source,
                    target,
                });
            }
        }
        axiom_keys.push(key);

        epoch = epoch.checked_add(1).ok_or_else(|| {
            ProfilePhaseError::Encoded(EncodedValidationError::resource(
                "profile traversal epoch overflowed",
            ))
        })?;
        enqueue_node(root.node(), &mut marks, epoch, &mut stack)
            .map_err(ProfilePhaseError::Encoded)?;
        let mut top_data_property_occurs = false;
        let mut anonymous_individual_occurs = false;
        while let Some(identifier) = stack.pop() {
            poll(control, "profile-node")?;
            budget.claim_work(1).map_err(ProfilePhaseError::Encoded)?;
            let node = model.node(identifier).map_err(ProfilePhaseError::Encoded)?;
            retain_simple_role_requirements_for_node(
                model,
                identifier,
                axiom_constructor,
                provenance_sha256,
                &mut simple_role_requirements,
                &mut budget,
                control,
            )?;
            if node.tag() == ANONYMOUS_INDIVIDUAL_TAG {
                anonymous_individual_occurs = true;
                let anonymous_index = usize::try_from(identifier.get() - 1).map_err(|_| {
                    ProfilePhaseError::Encoded(EncodedValidationError::invariant(
                        "profile anonymous node index exceeds the platform width",
                    ))
                })?;
                let seen = anonymous_seen.get_mut(anonymous_index).ok_or_else(|| {
                    ProfilePhaseError::Encoded(EncodedValidationError::invariant(
                        "profile anonymous node identifier is out of range",
                    ))
                })?;
                if *seen == 0 {
                    let following = anonymous_vertices.len().checked_add(1).ok_or_else(|| {
                        ProfilePhaseError::Encoded(EncodedValidationError::resource(
                            "profile anonymous vertex count overflowed",
                        ))
                    })?;
                    budget
                        .claim_anonymous_vertex(following)
                        .map_err(ProfilePhaseError::Encoded)?;
                    let key = anonymous_key(model, identifier, scope_maps, &mut budget)
                        .map_err(ProfilePhaseError::Encoded)?;
                    reserve_profile_one(
                        &mut anonymous_vertices,
                        &mut budget,
                        "profile anonymous vertex allocation failed",
                    )
                    .map_err(ProfilePhaseError::Encoded)?;
                    anonymous_vertices.push(key);
                    *seen = 1;
                }
            }
            if node.tag() == ENTITY_TAG {
                retain_entity_use(
                    model,
                    identifier,
                    &mut entity_seen,
                    &mut entity_uses,
                    &mut budget,
                )
                .map_err(ProfilePhaseError::Encoded)?;
            }
            if node.tag() == LITERAL_TAG {
                retain_profile_literal(
                    model,
                    identifier,
                    scope_maps,
                    &mut literals,
                    &mut budget,
                    &mut literal_budget,
                    control,
                )?;
            }
            if is_profile_complex_data_range(node.tag()) {
                retain_profile_datatype_range_failure(
                    model,
                    identifier,
                    scope_maps,
                    &mut datatype_range_failures,
                    &mut budget,
                    &mut literal_budget,
                    control,
                )?;
            }
            let anonymous_expression =
                if matches!(node.tag(), OBJECT_ONE_OF_TAG | OBJECT_HAS_VALUE_TAG) {
                    forbidden_anonymous_expression(model, identifier, &mut budget)
                        .map_err(ProfilePhaseError::Encoded)?
                } else {
                    None
                };
            if let Some(constructor) = anonymous_expression {
                let following = issues.len().checked_add(1).ok_or_else(|| {
                    ProfilePhaseError::Encoded(EncodedValidationError::resource(
                        "profile issue count overflowed",
                    ))
                })?;
                budget
                    .claim_issue(following)
                    .map_err(ProfilePhaseError::Encoded)?;
                budget
                    .claim_owned(size_of::<ProfileIssue>())
                    .map_err(ProfilePhaseError::Encoded)?;
                reserve_one(&mut issues, "profile issue allocation failed")
                    .map_err(ProfilePhaseError::Encoded)?;
                issues.push(ProfileIssue {
                    rule_id: ANONYMOUS_CLASS_EXPRESSION_RULE,
                    severity: "error",
                    message: Cow::Borrowed(ANONYMOUS_CLASS_EXPRESSION_MESSAGE),
                    constructor: Some(constructor),
                    document_keys: Vec::new(),
                    provenance_sha256: Some(provenance_sha256),
                });
            }
            if node.tag() == ENTITY_TAG
                && is_top_data_property(model, identifier, &mut budget)
                    .map_err(ProfilePhaseError::Encoded)?
            {
                top_data_property_occurs = true;
            }
            if matches!(
                node.tag(),
                DATA_SOME_VALUES_FROM_TAG | DATA_ALL_VALUES_FROM_TAG
            ) {
                let property_field = required_component(
                    model
                        .field(node.fields().start)
                        .map_err(ProfilePhaseError::Encoded)?,
                    "profile data restriction property sequence",
                )
                .map_err(ProfilePhaseError::Encoded)?;
                let ComponentValue::Collection(properties) = model
                    .resolve(property_field)
                    .map_err(ProfilePhaseError::Encoded)?
                else {
                    return Err(ProfilePhaseError::Encoded(
                        EncodedValidationError::invariant(
                            "validated profile data restriction properties are not a sequence",
                        ),
                    ));
                };
                if properties.kind() != ComponentKind::Sequence {
                    return Err(ProfilePhaseError::Encoded(
                        EncodedValidationError::invariant(
                            "validated profile data restriction properties lost sequence order",
                        ),
                    ));
                }
                if properties.len() != 1 {
                    let following = issues.len().checked_add(1).ok_or_else(|| {
                        ProfilePhaseError::Encoded(EncodedValidationError::resource(
                            "profile issue count overflowed",
                        ))
                    })?;
                    budget
                        .claim_issue(following)
                        .map_err(ProfilePhaseError::Encoded)?;
                    budget
                        .claim_owned(size_of::<ProfileIssue>())
                        .map_err(ProfilePhaseError::Encoded)?;
                    reserve_one(&mut issues, "profile issue allocation failed")
                        .map_err(ProfilePhaseError::Encoded)?;
                    issues.push(ProfileIssue {
                        rule_id: DATA_RANGE_ARITY_RULE,
                        severity: "error",
                        message: Cow::Borrowed(DATA_RANGE_ARITY_MESSAGE),
                        constructor: Some(if node.tag() == DATA_SOME_VALUES_FROM_TAG {
                            "DataSomeValuesFrom"
                        } else {
                            "DataAllValuesFrom"
                        }),
                        document_keys: Vec::new(),
                        provenance_sha256: Some(provenance_sha256),
                    });
                }
            }
            for field_index in node.fields() {
                budget.claim_work(1).map_err(ProfilePhaseError::Encoded)?;
                let component = required_component(
                    model
                        .field(field_index)
                        .map_err(ProfilePhaseError::Encoded)?,
                    "profile node field",
                )
                .map_err(ProfilePhaseError::Encoded)?;
                enqueue_component(model, component, &mut marks, epoch, &mut stack, &mut budget)
                    .map_err(ProfilePhaseError::Encoded)?;
            }
        }
        if anonymous_individual_occurs && anonymous_axiom_forbidden {
            let following = issues.len().checked_add(1).ok_or_else(|| {
                ProfilePhaseError::Encoded(EncodedValidationError::resource(
                    "profile issue count overflowed",
                ))
            })?;
            budget
                .claim_issue(following)
                .map_err(ProfilePhaseError::Encoded)?;
            budget
                .claim_owned(size_of::<ProfileIssue>())
                .map_err(ProfilePhaseError::Encoded)?;
            reserve_one(&mut issues, "profile issue allocation failed")
                .map_err(ProfilePhaseError::Encoded)?;
            issues.push(ProfileIssue {
                rule_id: ANONYMOUS_AXIOM_POSITION_RULE,
                severity: "error",
                message: Cow::Borrowed(ANONYMOUS_AXIOM_POSITION_MESSAGE),
                constructor: Some(axiom_constructor),
                document_keys: Vec::new(),
                provenance_sha256: Some(provenance_sha256),
            });
        }
        if top_data_property_occurs && !top_data_property_allowed {
            let following = issues.len().checked_add(1).ok_or_else(|| {
                ProfilePhaseError::Encoded(EncodedValidationError::resource(
                    "profile issue count overflowed",
                ))
            })?;
            budget
                .claim_issue(following)
                .map_err(ProfilePhaseError::Encoded)?;
            budget
                .claim_owned(size_of::<ProfileIssue>())
                .map_err(ProfilePhaseError::Encoded)?;
            reserve_one(&mut issues, "profile issue allocation failed")
                .map_err(ProfilePhaseError::Encoded)?;
            issues.push(ProfileIssue {
                rule_id: TOP_DATA_PROPERTY_RULE,
                severity: "error",
                message: Cow::Borrowed(TOP_DATA_PROPERTY_MESSAGE),
                constructor: Some(axiom_constructor),
                document_keys: Vec::new(),
                provenance_sha256: Some(provenance_sha256),
            });
        }
    }

    poll(control, "profile-canonicalize")?;
    budget
        .claim_work(sort_work(anonymous_vertices.len()))
        .map_err(ProfilePhaseError::Encoded)?;
    anonymous_vertices.sort_unstable();
    anonymous_vertices.dedup();
    budget
        .claim_work(sort_work(anonymous_assertions.len()))
        .map_err(ProfilePhaseError::Encoded)?;
    anonymous_assertions.sort();
    anonymous_assertions.dedup();
    append_anonymous_graph_issues(
        &anonymous_vertices,
        &anonymous_assertions,
        &mut issues,
        &mut budget,
        control,
    )?;
    budget
        .claim_work(sort_work(entity_uses.len()))
        .map_err(ProfilePhaseError::Encoded)?;
    entity_uses.sort();
    entity_uses.dedup();
    budget
        .claim_work(sort_work(entity_declarations.len()))
        .map_err(ProfilePhaseError::Encoded)?;
    entity_declarations.sort();
    entity_declarations.dedup();
    append_entity_issues(
        &entity_uses,
        &entity_declarations,
        &mut issues,
        &mut budget,
        control,
    )?;
    budget
        .claim_work(sort_work(datatype_definitions.len()))
        .map_err(ProfilePhaseError::Encoded)?;
    datatype_definitions.sort();
    datatype_definitions.dedup();
    budget
        .claim_work(sort_work(datatype_range_failures.len()))
        .map_err(ProfilePhaseError::Encoded)?;
    datatype_range_failures.sort();
    datatype_range_failures.dedup();
    budget
        .claim_work(sort_work(literals.len()))
        .map_err(ProfilePhaseError::Encoded)?;
    literals.sort();
    literals.dedup();
    append_datatype_issues(
        ProfileDatatypeFacts {
            uses: &entity_uses,
            definitions: &datatype_definitions,
            range_failures: &datatype_range_failures,
            literals: &literals,
        },
        unsupported_datatypes,
        &mut issues,
        &mut budget,
        control,
    )?;
    budget
        .claim_work(sort_work(role_inclusions.len()))
        .map_err(ProfilePhaseError::Encoded)?;
    role_inclusions.sort();
    role_inclusions.dedup();
    canonicalize_profile_complex_role_inclusions(&mut complex_role_inclusions, &mut budget)
        .map_err(ProfilePhaseError::Encoded)?;
    budget
        .claim_work(sort_work(non_simple_role_seeds.len()))
        .map_err(ProfilePhaseError::Encoded)?;
    non_simple_role_seeds.sort();
    non_simple_role_seeds.dedup();
    budget
        .claim_work(sort_work(simple_role_requirements.len()))
        .map_err(ProfilePhaseError::Encoded)?;
    simple_role_requirements.sort();
    simple_role_requirements.dedup();
    append_role_regularity_issues(
        &role_inclusions,
        &complex_role_inclusions,
        &mut issues,
        &mut budget,
        control,
    )?;
    append_non_simple_role_issues(
        &role_inclusions,
        &non_simple_role_seeds,
        &simple_role_requirements,
        &mut issues,
        &mut budget,
        control,
    )?;
    budget
        .claim_work(sort_work(issues.len()))
        .map_err(ProfilePhaseError::Encoded)?;
    issues.sort();
    issues.dedup();
    budget
        .claim_work(sort_work(axiom_keys.len()))
        .map_err(ProfilePhaseError::Encoded)?;
    axiom_keys.sort();
    axiom_keys.dedup();
    budget
        .claim_work(sort_work(extension_keys.len()))
        .map_err(ProfilePhaseError::Encoded)?;
    extension_keys.sort();
    extension_keys.dedup();
    let phase = ProfilePhase {
        conforms: profile_issues_conform(&issues),
        axioms_checked: axiom_keys.len(),
        extensions_checked: extension_keys.len(),
        issues,
        work: budget.work,
        owned_bytes: budget.owned_bytes,
        axiom_keys,
        extension_keys,
        anonymous_vertices,
        anonymous_assertions,
        entity_uses,
        entity_declarations,
        datatype_definitions,
        datatype_range_failures,
        literals,
        role_inclusions,
        complex_role_inclusions,
        non_simple_role_seeds,
        simple_role_requirements,
        manifest_limit: limits.max_manifest_bytes,
    };
    validate_phase(&phase).map_err(ProfilePhaseError::Encoded)?;
    poll(control, "profile-complete")?;
    Ok(phase)
}

/// Canonically merge source-local reports without losing selection semantics.
pub fn merge_profile_phases(
    phases: Vec<ProfilePhase>,
    limits: ProfilePhaseLimits,
) -> EncodedResult<ProfilePhase> {
    let mut control = |_phase| Ok::<(), Infallible>(());
    into_encoded(merge_profile_phases_controlled(
        phases,
        limits,
        &mut control,
    ))
}

pub fn merge_profile_phases_controlled<E>(
    phases: Vec<ProfilePhase>,
    limits: ProfilePhaseLimits,
    control: &mut impl FnMut(&'static str) -> Result<(), E>,
) -> ControlledResult<ProfilePhase, E> {
    merge_profile_phases_controlled_with_policy(
        phases,
        limits,
        ProfileUnsupportedDatatypePolicy::Error,
        control,
    )
}

/// Merge profile facts with scalar-compatible unsupported-datatype handling.
pub fn merge_profile_phases_controlled_with_policy<E>(
    phases: Vec<ProfilePhase>,
    limits: ProfilePhaseLimits,
    unsupported_datatypes: ProfileUnsupportedDatatypePolicy,
    control: &mut impl FnMut(&'static str) -> Result<(), E>,
) -> ControlledResult<ProfilePhase, E> {
    if phases.is_empty() {
        return Err(EncodedValidationError::invariant(
            "profile merge requires at least one source phase",
        )
        .into());
    }
    if phases.len() > limits.max_slices {
        return Err(
            EncodedValidationError::resource("profile merge exceeds its slice limit").into(),
        );
    }
    poll(control, "profile-merge-preflight")?;
    let issue_count = phases.iter().try_fold(0_usize, |total, phase| {
        let local = phase
            .issues
            .iter()
            .filter(|issue| !is_recomputed_profile_rule(issue.rule_id))
            .count();
        total.checked_add(local).ok_or_else(|| {
            EncodedValidationError::resource("merged profile issue count overflowed")
        })
    })?;
    let axiom_count = phases.iter().try_fold(0_usize, |total, phase| {
        total.checked_add(phase.axiom_keys.len()).ok_or_else(|| {
            EncodedValidationError::resource("merged profile axiom count overflowed")
        })
    })?;
    let extension_count = phases.iter().try_fold(0_usize, |total, phase| {
        total
            .checked_add(phase.extension_keys.len())
            .ok_or_else(|| {
                EncodedValidationError::resource("merged profile extension count overflowed")
            })
    })?;
    let anonymous_vertex_count = phases.iter().try_fold(0_usize, |total, phase| {
        total
            .checked_add(phase.anonymous_vertices.len())
            .ok_or_else(|| {
                EncodedValidationError::resource("merged profile anonymous vertex count overflowed")
            })
    })?;
    let anonymous_assertion_count = phases.iter().try_fold(0_usize, |total, phase| {
        total
            .checked_add(phase.anonymous_assertions.len())
            .ok_or_else(|| {
                EncodedValidationError::resource(
                    "merged profile anonymous assertion count overflowed",
                )
            })
    })?;
    let entity_use_count = phases.iter().try_fold(0_usize, |total, phase| {
        total.checked_add(phase.entity_uses.len()).ok_or_else(|| {
            EncodedValidationError::resource("merged profile entity use count overflowed")
        })
    })?;
    let entity_declaration_count = phases.iter().try_fold(0_usize, |total, phase| {
        total
            .checked_add(phase.entity_declarations.len())
            .ok_or_else(|| {
                EncodedValidationError::resource(
                    "merged profile entity declaration count overflowed",
                )
            })
    })?;
    let datatype_definition_count = phases.iter().try_fold(0_usize, |total, phase| {
        total
            .checked_add(phase.datatype_definitions.len())
            .ok_or_else(|| {
                EncodedValidationError::resource(
                    "merged profile datatype definition count overflowed",
                )
            })
    })?;
    let datatype_reference_count = phases.iter().try_fold(0_usize, |total, phase| {
        phase
            .datatype_definitions
            .iter()
            .try_fold(total, |subtotal, definition| {
                subtotal
                    .checked_add(definition.references.len())
                    .ok_or_else(|| {
                        EncodedValidationError::resource(
                            "merged profile datatype reference count overflowed",
                        )
                    })
            })
    })?;
    let datatype_failure_count = phases.iter().try_fold(0_usize, |total, phase| {
        total
            .checked_add(phase.datatype_range_failures.len())
            .ok_or_else(|| {
                EncodedValidationError::resource("merged profile datatype failure count overflowed")
            })
    })?;
    let literal_count = phases.iter().try_fold(0_usize, |total, phase| {
        total.checked_add(phase.literals.len()).ok_or_else(|| {
            EncodedValidationError::resource("merged profile literal count overflowed")
        })
    })?;
    let role_inclusion_count = phases.iter().try_fold(0_usize, |total, phase| {
        total
            .checked_add(phase.role_inclusions.len())
            .ok_or_else(|| {
                EncodedValidationError::resource("merged profile role inclusion count overflowed")
            })
    })?;
    let complex_role_inclusion_count = phases.iter().try_fold(0_usize, |total, phase| {
        total
            .checked_add(phase.complex_role_inclusions.len())
            .ok_or_else(|| {
                EncodedValidationError::resource(
                    "merged profile complex role inclusion count overflowed",
                )
            })
    })?;
    let non_simple_role_seed_count = phases.iter().try_fold(0_usize, |total, phase| {
        total
            .checked_add(phase.non_simple_role_seeds.len())
            .ok_or_else(|| {
                EncodedValidationError::resource(
                    "merged profile non-simple role seed count overflowed",
                )
            })
    })?;
    let simple_role_requirement_count = phases.iter().try_fold(0_usize, |total, phase| {
        total
            .checked_add(phase.simple_role_requirements.len())
            .ok_or_else(|| {
                EncodedValidationError::resource(
                    "merged profile simple-role requirement count overflowed",
                )
            })
    })?;
    if issue_count > limits.max_issues {
        return Err(EncodedValidationError::resource(
            "merged profile issue count exceeds its limit",
        )
        .into());
    }
    if axiom_count > limits.max_axioms {
        return Err(EncodedValidationError::resource(
            "merged profile axiom count exceeds its limit",
        )
        .into());
    }
    if extension_count > limits.max_extensions {
        return Err(EncodedValidationError::resource(
            "merged profile extension count exceeds its limit",
        )
        .into());
    }
    if anonymous_vertex_count > limits.max_anonymous_vertices {
        return Err(EncodedValidationError::resource(
            "merged profile anonymous vertex count exceeds its limit",
        )
        .into());
    }
    if anonymous_assertion_count > limits.max_anonymous_assertions {
        return Err(EncodedValidationError::resource(
            "merged profile anonymous assertion count exceeds its limit",
        )
        .into());
    }
    if entity_use_count > limits.max_entity_uses {
        return Err(EncodedValidationError::resource(
            "merged profile entity use count exceeds its limit",
        )
        .into());
    }
    if entity_declaration_count > limits.max_entity_declarations {
        return Err(EncodedValidationError::resource(
            "merged profile entity declaration count exceeds its limit",
        )
        .into());
    }
    if datatype_definition_count > limits.max_datatype_definitions {
        return Err(EncodedValidationError::resource(
            "merged profile datatype definition count exceeds its limit",
        )
        .into());
    }
    if datatype_reference_count > limits.max_datatype_references {
        return Err(EncodedValidationError::resource(
            "merged profile datatype reference count exceeds its limit",
        )
        .into());
    }
    if datatype_failure_count > limits.max_datatype_failures {
        return Err(EncodedValidationError::resource(
            "merged profile datatype failure count exceeds its limit",
        )
        .into());
    }
    if literal_count > limits.max_literal_datatypes {
        return Err(EncodedValidationError::resource(
            "merged profile literal count exceeds its limit",
        )
        .into());
    }
    if role_inclusion_count > limits.max_role_inclusions {
        return Err(EncodedValidationError::resource(
            "merged profile role inclusion count exceeds its limit",
        )
        .into());
    }
    if complex_role_inclusion_count > limits.max_complex_role_inclusions {
        return Err(EncodedValidationError::resource(
            "merged profile complex role inclusion count exceeds its limit",
        )
        .into());
    }
    if non_simple_role_seed_count > limits.max_non_simple_role_seeds {
        return Err(EncodedValidationError::resource(
            "merged profile non-simple role seed count exceeds its limit",
        )
        .into());
    }
    if simple_role_requirement_count > limits.max_simple_role_requirements {
        return Err(EncodedValidationError::resource(
            "merged profile simple-role requirement count exceeds its limit",
        )
        .into());
    }

    let mut budget = PhaseBudget::new(limits);
    let mut issues = Vec::new();
    reserve_exact(
        &mut issues,
        issue_count,
        "merged profile issue allocation failed",
    )
    .map_err(ProfilePhaseError::Encoded)?;
    budget
        .claim_owned(
            issue_count
                .checked_mul(size_of::<ProfileIssue>())
                .ok_or_else(|| {
                    EncodedValidationError::resource("merged profile issue size overflowed")
                })?,
        )
        .map_err(ProfilePhaseError::Encoded)?;
    let mut axiom_keys = Vec::new();
    reserve_exact(
        &mut axiom_keys,
        axiom_count,
        "merged profile axiom allocation failed",
    )
    .map_err(ProfilePhaseError::Encoded)?;
    budget
        .claim_owned(
            axiom_count
                .checked_mul(size_of::<Vec<u8>>())
                .ok_or_else(|| {
                    EncodedValidationError::resource("merged profile axiom size overflowed")
                })?,
        )
        .map_err(ProfilePhaseError::Encoded)?;
    let mut extension_keys = Vec::new();
    reserve_exact(
        &mut extension_keys,
        extension_count,
        "merged profile extension allocation failed",
    )
    .map_err(ProfilePhaseError::Encoded)?;
    budget
        .claim_owned(
            extension_count
                .checked_mul(size_of::<Vec<u8>>())
                .ok_or_else(|| {
                    EncodedValidationError::resource("merged profile extension size overflowed")
                })?,
        )
        .map_err(ProfilePhaseError::Encoded)?;
    let mut anonymous_vertices = Vec::new();
    reserve_exact(
        &mut anonymous_vertices,
        anonymous_vertex_count,
        "merged profile anonymous vertex allocation failed",
    )
    .map_err(ProfilePhaseError::Encoded)?;
    budget
        .claim_owned(
            anonymous_vertex_count
                .checked_mul(size_of::<AnonymousKey>())
                .ok_or_else(|| {
                    EncodedValidationError::resource(
                        "merged profile anonymous vertex size overflowed",
                    )
                })?,
        )
        .map_err(ProfilePhaseError::Encoded)?;
    let mut anonymous_assertions = Vec::new();
    reserve_exact(
        &mut anonymous_assertions,
        anonymous_assertion_count,
        "merged profile anonymous assertion allocation failed",
    )
    .map_err(ProfilePhaseError::Encoded)?;
    budget
        .claim_owned(
            anonymous_assertion_count
                .checked_mul(size_of::<AnonymousAssertion>())
                .ok_or_else(|| {
                    EncodedValidationError::resource(
                        "merged profile anonymous assertion size overflowed",
                    )
                })?,
        )
        .map_err(ProfilePhaseError::Encoded)?;
    let mut entity_uses = Vec::new();
    reserve_exact(
        &mut entity_uses,
        entity_use_count,
        "merged profile entity use allocation failed",
    )
    .map_err(ProfilePhaseError::Encoded)?;
    budget
        .claim_owned(
            entity_use_count
                .checked_mul(size_of::<ProfileEntityIdentity>())
                .ok_or_else(|| {
                    EncodedValidationError::resource("merged profile entity use size overflowed")
                })?,
        )
        .map_err(ProfilePhaseError::Encoded)?;
    let mut entity_declarations = Vec::new();
    reserve_exact(
        &mut entity_declarations,
        entity_declaration_count,
        "merged profile entity declaration allocation failed",
    )
    .map_err(ProfilePhaseError::Encoded)?;
    budget
        .claim_owned(
            entity_declaration_count
                .checked_mul(size_of::<ProfileEntityIdentity>())
                .ok_or_else(|| {
                    EncodedValidationError::resource(
                        "merged profile entity declaration size overflowed",
                    )
                })?,
        )
        .map_err(ProfilePhaseError::Encoded)?;
    let mut datatype_definitions = Vec::new();
    reserve_exact(
        &mut datatype_definitions,
        datatype_definition_count,
        "merged profile datatype definition allocation failed",
    )
    .map_err(ProfilePhaseError::Encoded)?;
    budget
        .claim_owned(
            datatype_definition_count
                .checked_mul(size_of::<ProfileDatatypeDefinition>())
                .ok_or_else(|| {
                    EncodedValidationError::resource(
                        "merged profile datatype definition size overflowed",
                    )
                })?,
        )
        .map_err(ProfilePhaseError::Encoded)?;
    let mut datatype_range_failures = Vec::new();
    reserve_exact(
        &mut datatype_range_failures,
        datatype_failure_count,
        "merged profile datatype failure allocation failed",
    )
    .map_err(ProfilePhaseError::Encoded)?;
    budget
        .claim_owned(
            datatype_failure_count
                .checked_mul(size_of::<ProfileDatatypeRangeFailure>())
                .ok_or_else(|| {
                    EncodedValidationError::resource(
                        "merged profile datatype failure size overflowed",
                    )
                })?,
        )
        .map_err(ProfilePhaseError::Encoded)?;
    let mut literals = Vec::new();
    reserve_exact(
        &mut literals,
        literal_count,
        "merged profile literal allocation failed",
    )
    .map_err(ProfilePhaseError::Encoded)?;
    budget
        .claim_owned(
            literal_count
                .checked_mul(size_of::<ProfileLiteralFact>())
                .ok_or_else(|| {
                    EncodedValidationError::resource("merged profile literal size overflowed")
                })?,
        )
        .map_err(ProfilePhaseError::Encoded)?;
    let mut role_inclusions = Vec::new();
    reserve_exact(
        &mut role_inclusions,
        role_inclusion_count,
        "merged profile role inclusion allocation failed",
    )
    .map_err(ProfilePhaseError::Encoded)?;
    budget
        .claim_owned(
            role_inclusion_count
                .checked_mul(size_of::<ProfileRoleInclusion>())
                .ok_or_else(|| {
                    EncodedValidationError::resource(
                        "merged profile role inclusion size overflowed",
                    )
                })?,
        )
        .map_err(ProfilePhaseError::Encoded)?;
    let mut complex_role_inclusions = Vec::new();
    reserve_exact(
        &mut complex_role_inclusions,
        complex_role_inclusion_count,
        "merged profile complex role inclusion allocation failed",
    )
    .map_err(ProfilePhaseError::Encoded)?;
    budget
        .claim_owned(
            complex_role_inclusion_count
                .checked_mul(size_of::<ProfileComplexRoleInclusion>())
                .ok_or_else(|| {
                    EncodedValidationError::resource(
                        "merged profile complex role inclusion size overflowed",
                    )
                })?,
        )
        .map_err(ProfilePhaseError::Encoded)?;
    let mut non_simple_role_seeds = Vec::new();
    reserve_exact(
        &mut non_simple_role_seeds,
        non_simple_role_seed_count,
        "merged profile non-simple role seed allocation failed",
    )
    .map_err(ProfilePhaseError::Encoded)?;
    budget
        .claim_owned(
            non_simple_role_seed_count
                .checked_mul(size_of::<ProfileObjectRole>())
                .ok_or_else(|| {
                    EncodedValidationError::resource(
                        "merged profile non-simple role seed size overflowed",
                    )
                })?,
        )
        .map_err(ProfilePhaseError::Encoded)?;
    let mut simple_role_requirements = Vec::new();
    reserve_exact(
        &mut simple_role_requirements,
        simple_role_requirement_count,
        "merged profile simple-role requirement allocation failed",
    )
    .map_err(ProfilePhaseError::Encoded)?;
    budget
        .claim_owned(
            simple_role_requirement_count
                .checked_mul(size_of::<ProfileSimpleRoleRequirement>())
                .ok_or_else(|| {
                    EncodedValidationError::resource(
                        "merged profile simple-role requirement size overflowed",
                    )
                })?,
        )
        .map_err(ProfilePhaseError::Encoded)?;

    for mut phase in phases {
        validate_phase(&phase).map_err(ProfilePhaseError::Encoded)?;
        budget
            .claim_work_u64(phase.work)
            .map_err(ProfilePhaseError::Encoded)?;
        budget
            .claim_owned(phase.owned_bytes)
            .map_err(ProfilePhaseError::Encoded)?;
        issues.extend(
            phase
                .issues
                .drain(..)
                .filter(|issue| !is_recomputed_profile_rule(issue.rule_id)),
        );
        axiom_keys.append(&mut phase.axiom_keys);
        extension_keys.append(&mut phase.extension_keys);
        anonymous_vertices.append(&mut phase.anonymous_vertices);
        anonymous_assertions.append(&mut phase.anonymous_assertions);
        entity_uses.append(&mut phase.entity_uses);
        entity_declarations.append(&mut phase.entity_declarations);
        datatype_definitions.append(&mut phase.datatype_definitions);
        datatype_range_failures.append(&mut phase.datatype_range_failures);
        literals.append(&mut phase.literals);
        role_inclusions.append(&mut phase.role_inclusions);
        complex_role_inclusions.append(&mut phase.complex_role_inclusions);
        non_simple_role_seeds.append(&mut phase.non_simple_role_seeds);
        simple_role_requirements.append(&mut phase.simple_role_requirements);
        poll(control, "profile-merge-source")?;
    }
    budget
        .claim_work(sort_work(anonymous_vertices.len()))
        .map_err(ProfilePhaseError::Encoded)?;
    anonymous_vertices.sort_unstable();
    anonymous_vertices.dedup();
    budget
        .claim_work(sort_work(anonymous_assertions.len()))
        .map_err(ProfilePhaseError::Encoded)?;
    anonymous_assertions.sort();
    anonymous_assertions.dedup();
    append_anonymous_graph_issues(
        &anonymous_vertices,
        &anonymous_assertions,
        &mut issues,
        &mut budget,
        control,
    )?;
    budget
        .claim_work(sort_work(entity_uses.len()))
        .map_err(ProfilePhaseError::Encoded)?;
    entity_uses.sort();
    entity_uses.dedup();
    budget
        .claim_work(sort_work(entity_declarations.len()))
        .map_err(ProfilePhaseError::Encoded)?;
    entity_declarations.sort();
    entity_declarations.dedup();
    append_entity_issues(
        &entity_uses,
        &entity_declarations,
        &mut issues,
        &mut budget,
        control,
    )?;
    budget
        .claim_work(sort_work(datatype_definitions.len()))
        .map_err(ProfilePhaseError::Encoded)?;
    datatype_definitions.sort();
    datatype_definitions.dedup();
    budget
        .claim_work(sort_work(datatype_range_failures.len()))
        .map_err(ProfilePhaseError::Encoded)?;
    datatype_range_failures.sort();
    datatype_range_failures.dedup();
    budget
        .claim_work(sort_work(literals.len()))
        .map_err(ProfilePhaseError::Encoded)?;
    literals.sort();
    literals.dedup();
    append_datatype_issues(
        ProfileDatatypeFacts {
            uses: &entity_uses,
            definitions: &datatype_definitions,
            range_failures: &datatype_range_failures,
            literals: &literals,
        },
        unsupported_datatypes,
        &mut issues,
        &mut budget,
        control,
    )?;
    budget
        .claim_work(sort_work(role_inclusions.len()))
        .map_err(ProfilePhaseError::Encoded)?;
    role_inclusions.sort();
    role_inclusions.dedup();
    canonicalize_profile_complex_role_inclusions(&mut complex_role_inclusions, &mut budget)
        .map_err(ProfilePhaseError::Encoded)?;
    budget
        .claim_work(sort_work(non_simple_role_seeds.len()))
        .map_err(ProfilePhaseError::Encoded)?;
    non_simple_role_seeds.sort();
    non_simple_role_seeds.dedup();
    budget
        .claim_work(sort_work(simple_role_requirements.len()))
        .map_err(ProfilePhaseError::Encoded)?;
    simple_role_requirements.sort();
    simple_role_requirements.dedup();
    append_role_regularity_issues(
        &role_inclusions,
        &complex_role_inclusions,
        &mut issues,
        &mut budget,
        control,
    )?;
    append_non_simple_role_issues(
        &role_inclusions,
        &non_simple_role_seeds,
        &simple_role_requirements,
        &mut issues,
        &mut budget,
        control,
    )?;
    budget
        .claim_work(sort_work(issues.len()))
        .map_err(ProfilePhaseError::Encoded)?;
    issues.sort();
    issues.dedup();
    budget
        .claim_work(sort_work(axiom_keys.len()))
        .map_err(ProfilePhaseError::Encoded)?;
    axiom_keys.sort();
    axiom_keys.dedup();
    budget
        .claim_work(sort_work(extension_keys.len()))
        .map_err(ProfilePhaseError::Encoded)?;
    extension_keys.sort();
    extension_keys.dedup();
    let phase = ProfilePhase {
        conforms: profile_issues_conform(&issues),
        axioms_checked: axiom_keys.len(),
        extensions_checked: extension_keys.len(),
        issues,
        work: budget.work,
        owned_bytes: budget.owned_bytes,
        axiom_keys,
        extension_keys,
        anonymous_vertices,
        anonymous_assertions,
        entity_uses,
        entity_declarations,
        datatype_definitions,
        datatype_range_failures,
        literals,
        role_inclusions,
        complex_role_inclusions,
        non_simple_role_seeds,
        simple_role_requirements,
        manifest_limit: limits.max_manifest_bytes,
    };
    validate_phase(&phase).map_err(ProfilePhaseError::Encoded)?;
    poll(control, "profile-merge-complete")?;
    Ok(phase)
}

/// Apply one validated private ontology-identity context to a completed phase.
pub fn apply_ontology_identity_context_controlled<E>(
    mut phase: ProfilePhase,
    identifiers: &[ProfileOntologyIdentifier],
    include_document_keys: bool,
    limits: ProfilePhaseLimits,
    control: &mut impl FnMut(&'static str) -> Result<(), E>,
) -> ControlledResult<ProfilePhase, E> {
    poll(control, "profile-ontology-identity-preflight")?;
    validate_phase(&phase).map_err(ProfilePhaseError::Encoded)?;
    let mut budget = PhaseBudget::new(limits);
    budget
        .claim_work_u64(phase.work)
        .map_err(ProfilePhaseError::Encoded)?;
    budget
        .claim_owned(phase.owned_bytes)
        .map_err(ProfilePhaseError::Encoded)?;
    budget
        .claim_ontology_document(identifiers.len())
        .map_err(ProfilePhaseError::Encoded)?;
    budget
        .claim_owned(
            identifiers
                .len()
                .checked_mul(size_of::<ProfileOntologyIdentifier>())
                .ok_or_else(|| {
                    EncodedValidationError::resource(
                        "profile ontology identity context size overflowed",
                    )
                })?,
        )
        .map_err(ProfilePhaseError::Encoded)?;
    if identifiers
        .windows(2)
        .any(|pair| pair[0].document_key >= pair[1].document_key)
    {
        return Err(EncodedValidationError::protocol(
            "profile ontology identity rows are not ordered by unique document key",
        )
        .into());
    }
    for identifier in identifiers {
        poll(control, "profile-ontology-identity-document")?;
        if identifier.document_key.is_empty() {
            return Err(EncodedValidationError::protocol(
                "profile ontology identity document key is empty",
            )
            .into());
        }
        budget
            .claim_owned(identifier.document_key.len())
            .map_err(ProfilePhaseError::Encoded)?;
        budget
            .claim_work(identifier.document_key.len())
            .map_err(ProfilePhaseError::Encoded)?;
        for (iri, rule_id, message_prefix) in [
            (
                identifier.ontology_iri.as_deref(),
                RESERVED_ONTOLOGY_IRI_RULE,
                RESERVED_ONTOLOGY_IRI_MESSAGE_PREFIX,
            ),
            (
                identifier.version_iri.as_deref(),
                RESERVED_VERSION_IRI_RULE,
                RESERVED_VERSION_IRI_MESSAGE_PREFIX,
            ),
        ] {
            poll(control, "profile-ontology-identity-iri")?;
            let Some(iri) = iri else {
                continue;
            };
            if iri.is_empty() {
                return Err(EncodedValidationError::protocol(
                    "profile ontology identity IRI is empty",
                )
                .into());
            }
            budget
                .claim_owned(iri.len())
                .map_err(ProfilePhaseError::Encoded)?;
            budget
                .claim_work(iri.len())
                .map_err(ProfilePhaseError::Encoded)?;
            if !reserved_iri(iri, &mut budget).map_err(ProfilePhaseError::Encoded)? {
                continue;
            }
            let iri = std::str::from_utf8(iri).map_err(|_| {
                ProfilePhaseError::Encoded(EncodedValidationError::protocol(
                    "profile ontology identity IRI is not UTF-8",
                ))
            })?;
            push_dynamic_profile_issue_with_constructor(
                &mut phase.issues,
                rule_id,
                &[message_prefix, iri],
                Some("OntologyID"),
                &mut budget,
            )
            .map_err(ProfilePhaseError::Encoded)?;
            if include_document_keys {
                let document_key = std::str::from_utf8(&identifier.document_key).map_err(|_| {
                    ProfilePhaseError::Encoded(EncodedValidationError::protocol(
                        "profile ontology identity document key is not UTF-8",
                    ))
                })?;
                budget
                    .claim_owned(
                        size_of::<String>()
                            .checked_add(document_key.len())
                            .ok_or_else(|| {
                                ProfilePhaseError::Encoded(EncodedValidationError::resource(
                                    "profile ontology identity document-key ownership overflowed",
                                ))
                            })?,
                    )
                    .map_err(ProfilePhaseError::Encoded)?;
                let issue = phase.issues.last_mut().ok_or_else(|| {
                    ProfilePhaseError::Encoded(EncodedValidationError::invariant(
                        "profile ontology identity issue disappeared",
                    ))
                })?;
                issue.document_keys.try_reserve_exact(1).map_err(|_| {
                    ProfilePhaseError::Encoded(EncodedValidationError::resource(
                        "profile ontology identity document-key allocation failed",
                    ))
                })?;
                issue.document_keys.push(document_key.to_owned());
            }
        }
    }
    poll(control, "profile-ontology-identity-canonicalize")?;
    budget
        .claim_work(sort_work(phase.issues.len()))
        .map_err(ProfilePhaseError::Encoded)?;
    phase.issues.sort();
    phase.issues.dedup();
    phase.conforms = profile_issues_conform(&phase.issues);
    phase.work = budget.work;
    phase.owned_bytes = budget.owned_bytes;
    validate_phase(&phase).map_err(ProfilePhaseError::Encoded)?;
    poll(control, "profile-ontology-identity-complete")?;
    Ok(phase)
}

fn build_profile_root_digest_bridge<E>(
    phase: &ProfilePhase,
    budget: &mut PhaseBudget,
    control: &mut impl FnMut(&'static str) -> Result<(), E>,
) -> ControlledResult<Vec<ProfileRootDigestBridge>, E> {
    let root_count = phase
        .axiom_keys
        .len()
        .checked_add(phase.extension_keys.len())
        .ok_or_else(|| {
            ProfilePhaseError::Encoded(EncodedValidationError::resource(
                "profile origin root count overflowed",
            ))
        })?;
    let mut bridge = Vec::new();
    bridge.try_reserve_exact(root_count).map_err(|_| {
        ProfilePhaseError::Encoded(EncodedValidationError::resource(
            "profile origin root-digest allocation failed",
        ))
    })?;
    budget
        .claim_owned(
            root_count
                .checked_mul(size_of::<ProfileRootDigestBridge>())
                .ok_or_else(|| {
                    EncodedValidationError::resource("profile origin root-digest size overflowed")
                })?,
        )
        .map_err(ProfilePhaseError::Encoded)?;
    for key in phase.axiom_keys.iter().chain(&phase.extension_keys) {
        poll(control, "profile-origin-root-digest")?;
        budget
            .claim_work(
                key.len()
                    .checked_mul(2)
                    .and_then(|value| value.checked_add(CORE_STRUCTURAL_DIGEST_PREFIX.len()))
                    .ok_or_else(|| {
                        EncodedValidationError::resource(
                            "profile origin root-digest work overflowed",
                        )
                    })?,
            )
            .map_err(ProfilePhaseError::Encoded)?;
        let raw_provenance_sha256 = Sha256::digest(key).into();
        let mut structural = Sha256::new();
        structural.update(CORE_STRUCTURAL_DIGEST_PREFIX);
        structural.update(key);
        bridge.push(ProfileRootDigestBridge {
            raw_provenance_sha256,
            core_structural_sha256: structural.finalize().into(),
        });
    }
    budget
        .claim_work(sort_work(bridge.len()))
        .map_err(ProfilePhaseError::Encoded)?;
    bridge.sort_unstable();
    if bridge
        .windows(2)
        .any(|pair| pair[0].raw_provenance_sha256 == pair[1].raw_provenance_sha256)
    {
        return Err(EncodedValidationError::invariant(
            "profile root digest bridge contains ambiguous raw provenance",
        )
        .into());
    }
    Ok(bridge)
}

/// Attach exact effective-origin document keys to every provenance-bearing issue.
pub fn apply_origin_context_controlled<E>(
    mut phase: ProfilePhase,
    origins: &[ProfileOrigin],
    limits: ProfilePhaseLimits,
    control: &mut impl FnMut(&'static str) -> Result<(), E>,
) -> ControlledResult<ProfilePhase, E> {
    poll(control, "profile-origin-preflight")?;
    validate_phase(&phase).map_err(ProfilePhaseError::Encoded)?;
    let mut budget = PhaseBudget::new(limits);
    budget
        .claim_work_u64(phase.work)
        .map_err(ProfilePhaseError::Encoded)?;
    budget
        .claim_owned(phase.owned_bytes)
        .map_err(ProfilePhaseError::Encoded)?;
    if origins.len() > limits.max_axioms {
        return Err(
            EncodedValidationError::resource("profile origin row count exceeds its limit").into(),
        );
    }
    budget
        .claim_owned(
            origins
                .len()
                .checked_mul(size_of::<ProfileOrigin>())
                .ok_or_else(|| {
                    EncodedValidationError::resource("profile origin context size overflowed")
                })?,
        )
        .map_err(ProfilePhaseError::Encoded)?;
    if origins
        .windows(2)
        .any(|pair| pair[0].root_digest_sha256 >= pair[1].root_digest_sha256)
    {
        return Err(EncodedValidationError::protocol(
            "profile origin rows are not ordered by unique provenance",
        )
        .into());
    }
    for origin in origins {
        poll(control, "profile-origin-row")?;
        if origin.document_keys.is_empty()
            || origin
                .document_keys
                .windows(2)
                .any(|pair| pair[0] >= pair[1])
            || origin.document_keys.iter().any(String::is_empty)
        {
            return Err(EncodedValidationError::protocol(
                "profile origin document keys are not nonempty, sorted, and unique",
            )
            .into());
        }
        budget
            .claim_owned(
                origin
                    .document_keys
                    .iter()
                    .try_fold(0_usize, |total, document_key| {
                        total
                            .checked_add(size_of::<String>())
                            .and_then(|value| value.checked_add(document_key.len()))
                            .ok_or_else(|| {
                                EncodedValidationError::resource(
                                    "profile origin document-key ownership overflowed",
                                )
                            })
                    })
                    .map_err(ProfilePhaseError::Encoded)?,
            )
            .map_err(ProfilePhaseError::Encoded)?;
        budget
            .claim_work(origin.document_keys.len())
            .map_err(ProfilePhaseError::Encoded)?;
    }
    let digest_bridge = if phase
        .issues
        .iter()
        .any(|issue| issue.provenance_sha256.is_some())
    {
        build_profile_root_digest_bridge(&phase, &mut budget, control)?
    } else {
        Vec::new()
    };
    let mut selected_domain = None;
    for issue in &mut phase.issues {
        poll(control, "profile-origin-issue")?;
        let Some(provenance) = issue.provenance_sha256 else {
            continue;
        };
        budget
            .claim_work(search_work(origins.len()))
            .map_err(ProfilePhaseError::Encoded)?;
        let raw_position = origins
            .binary_search_by_key(&provenance, |origin| origin.root_digest_sha256)
            .ok();
        budget
            .claim_work(search_work(digest_bridge.len()))
            .map_err(ProfilePhaseError::Encoded)?;
        let structural = digest_bridge
            .binary_search_by_key(&provenance, |row| row.raw_provenance_sha256)
            .ok()
            .and_then(|position| digest_bridge.get(position))
            .map(|row| row.core_structural_sha256)
            .ok_or_else(|| {
                ProfilePhaseError::Encoded(EncodedValidationError::protocol(
                    "profile origin context is missing a provenance-bearing issue",
                ))
            })?;
        budget
            .claim_work(search_work(origins.len()))
            .map_err(ProfilePhaseError::Encoded)?;
        let structural_position = origins
            .binary_search_by_key(&structural, |origin| origin.root_digest_sha256)
            .ok();
        let (domain, position) = match (raw_position, structural_position) {
            (Some(position), None) => (ProfileOriginDigestDomain::RawProvenance, position),
            (None, Some(position)) => (ProfileOriginDigestDomain::CoreStructural, position),
            (Some(position), Some(_)) if provenance == structural => {
                (ProfileOriginDigestDomain::RawProvenance, position)
            }
            (Some(_), Some(_)) => {
                return Err(EncodedValidationError::protocol(
                    "profile origin context mixes ambiguous digest domains",
                )
                .into());
            }
            (None, None) => {
                return Err(EncodedValidationError::protocol(
                    "profile origin context is missing a provenance-bearing issue",
                )
                .into());
            }
        };
        if selected_domain.is_some_and(|selected| selected != domain) {
            return Err(EncodedValidationError::protocol(
                "profile origin context mixes digest domains",
            )
            .into());
        }
        selected_domain = Some(domain);
        let document_keys = &origins[position].document_keys;
        issue
            .document_keys
            .try_reserve_exact(document_keys.len())
            .map_err(|_| {
                ProfilePhaseError::Encoded(EncodedValidationError::resource(
                    "profile issue document-key allocation failed",
                ))
            })?;
        for document_key in document_keys {
            budget
                .claim_owned(
                    size_of::<String>()
                        .checked_add(document_key.len())
                        .ok_or_else(|| {
                            ProfilePhaseError::Encoded(EncodedValidationError::resource(
                                "profile issue document-key ownership overflowed",
                            ))
                        })?,
                )
                .map_err(ProfilePhaseError::Encoded)?;
            issue.document_keys.push(document_key.clone());
        }
    }
    poll(control, "profile-origin-canonicalize")?;
    budget
        .claim_work(sort_work(phase.issues.len()))
        .map_err(ProfilePhaseError::Encoded)?;
    phase.issues.sort();
    phase.issues.dedup();
    phase.conforms = profile_issues_conform(&phase.issues);
    phase.work = budget.work;
    phase.owned_bytes = budget.owned_bytes;
    validate_phase(&phase).map_err(ProfilePhaseError::Encoded)?;
    poll(control, "profile-origin-complete")?;
    Ok(phase)
}

fn declaration_entity<B: ByteSource>(
    model: &ValidatedModel<B>,
    identifier: NodeId,
    budget: &mut PhaseBudget,
) -> EncodedResult<ProfileEntityIdentity> {
    budget.claim_work(1)?;
    let node = model.node(identifier)?;
    if node.tag() != DECLARATION_TAG || node.field_count() != 2 {
        return Err(EncodedValidationError::invariant(
            "validated declaration lost its schema-1 shape",
        ));
    }
    let entity = required_node(model, node.fields().start, "profile declared entity")?;
    profile_entity_identity(model, entity, budget)
}

fn retain_entity_use<B: ByteSource>(
    model: &ValidatedModel<B>,
    identifier: NodeId,
    seen: &mut [u8],
    uses: &mut Vec<ProfileEntityIdentity>,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    let index = usize::try_from(identifier.get() - 1).map_err(|_| {
        EncodedValidationError::invariant("profile entity node index exceeds the platform width")
    })?;
    let retained = seen.get_mut(index).ok_or_else(|| {
        EncodedValidationError::invariant("profile entity node identifier is out of range")
    })?;
    if *retained != 0 {
        return Ok(());
    }
    let following = uses
        .len()
        .checked_add(1)
        .ok_or_else(|| EncodedValidationError::resource("profile entity use count overflowed"))?;
    budget.claim_entity_use(following)?;
    let identity = profile_entity_identity(model, identifier, budget)?;
    reserve_profile_one(uses, budget, "profile entity use allocation failed")?;
    uses.push(identity);
    *retained = 1;
    Ok(())
}

fn retain_entity_declaration(
    identity: ProfileEntityIdentity,
    declarations: &mut Vec<ProfileEntityIdentity>,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    let following = declarations.len().checked_add(1).ok_or_else(|| {
        EncodedValidationError::resource("profile entity declaration count overflowed")
    })?;
    budget.claim_entity_declaration(following)?;
    reserve_profile_one(
        declarations,
        budget,
        "profile entity declaration allocation failed",
    )?;
    declarations.push(identity);
    Ok(())
}

fn retain_profile_literal<B: ByteSource, E>(
    model: &ValidatedModel<B>,
    identifier: NodeId,
    scope_maps: &[AnonymousScopeMap],
    target: &mut Vec<ProfileLiteralFact>,
    budget: &mut PhaseBudget,
    literal_budget: &mut LiteralPhaseBudget,
    control: &mut impl FnMut(&'static str) -> Result<(), E>,
) -> ControlledResult<(), E> {
    poll(control, "profile-literal")?;
    let (datatype_iri, validation) =
        classify_profile_literal(model, identifier, budget, literal_budget, control)?;
    let canonical_key = canonical::canonical_node_key(model, identifier, scope_maps, budget)
        .map_err(ProfilePhaseError::Encoded)?;
    let failure = match validation {
        ProfileLiteralValidation::Valid(_) => None,
        ProfileLiteralValidation::Invalid(invalid) => {
            Some(ProfileDatatypeFailure::InvalidLiteral(invalid))
        }
        ProfileLiteralValidation::Unsupported => Some(ProfileDatatypeFailure::UnsupportedLiteral),
    };
    let following = target.len().checked_add(1).ok_or_else(|| {
        ProfilePhaseError::Encoded(EncodedValidationError::resource(
            "profile literal count overflowed",
        ))
    })?;
    budget
        .claim_literal_datatype(following)
        .map_err(ProfilePhaseError::Encoded)?;
    reserve_profile_one(target, budget, "profile literal allocation failed")
        .map_err(ProfilePhaseError::Encoded)?;
    target.push(ProfileLiteralFact {
        canonical_key,
        datatype_iri,
        failure,
    });
    Ok(())
}

fn classify_profile_literal<B: ByteSource, E>(
    model: &ValidatedModel<B>,
    identifier: NodeId,
    budget: &mut PhaseBudget,
    literal_budget: &mut LiteralPhaseBudget,
    control: &mut impl FnMut(&'static str) -> Result<(), E>,
) -> ControlledResult<(Vec<u8>, ProfileLiteralValidation), E> {
    budget.claim_work(1)?;
    let literal = model.node(identifier)?;
    if literal.tag() != LITERAL_TAG || literal.field_count() != 3 {
        return Err(EncodedValidationError::invariant(
            "validated profile literal lost its schema-1 shape",
        )
        .into());
    }
    let fields = literal.fields();
    let lexical = profile_text_field(model, fields.start, "profile literal lexical form", budget)?;
    let datatype_field = literal
        .fields()
        .start
        .checked_add(1)
        .ok_or_else(|| EncodedValidationError::resource("profile literal field overflowed"))?;
    let datatype = required_node(model, datatype_field, "profile literal datatype")?;
    let identity = profile_entity_identity(model, datatype, budget)?;
    if identity.kind != ProfileEntityKind::Datatype {
        return Err(EncodedValidationError::invariant(
            "validated profile literal datatype is not a datatype entity",
        )
        .into());
    }
    let language_field = fields
        .start
        .checked_add(2)
        .ok_or_else(|| EncodedValidationError::resource("profile literal field overflowed"))?;
    let language_component =
        required_component(model.field(language_field)?, "profile literal language")?;
    let language = match model.resolve(language_component)? {
        ComponentValue::None => None,
        ComponentValue::Scalar(value) => Some(profile_text_scalar(
            value,
            "profile literal language",
            budget,
        )?),
        ComponentValue::Node(_) | ComponentValue::Collection(_) => {
            return Err(EncodedValidationError::invariant(
                "validated profile literal language is not optional text",
            )
            .into());
        }
    };
    let datatype_iri = std::str::from_utf8(&identity.iri).map_err(|_| {
        EncodedValidationError::invariant("validated profile datatype IRI is not UTF-8")
    })?;
    poll(control, "profile-literal-compile")?;
    let before = literal_budget.usage();
    let validation = named_classes::profile_literal_validation(
        &lexical,
        datatype_iri,
        language.as_deref(),
        literal_budget,
    )
    .map_err(ProfilePhaseError::Encoded)?;
    let after = literal_budget.usage();
    budget
        .claim_work_u64(after.0.checked_sub(before.0).ok_or_else(|| {
            EncodedValidationError::invariant("profile literal work counter moved backwards")
        })?)
        .map_err(ProfilePhaseError::Encoded)?;
    budget
        .claim_owned(after.1.checked_sub(before.1).ok_or_else(|| {
            EncodedValidationError::invariant("profile literal ownership counter moved backwards")
        })?)
        .map_err(ProfilePhaseError::Encoded)?;
    poll(control, "profile-literal-compiled")?;
    Ok((identity.iri, validation))
}

fn retain_profile_datatype_definition<B: ByteSource, E>(
    model: &ValidatedModel<B>,
    identifier: NodeId,
    statement_order_key: &[u8],
    target: &mut Vec<ProfileDatatypeDefinition>,
    budget: &mut PhaseBudget,
    literal_budget: &mut LiteralPhaseBudget,
    control: &mut impl FnMut(&'static str) -> Result<(), E>,
) -> ControlledResult<(), E> {
    budget.claim_work(1)?;
    let definition = model.node(identifier)?;
    if definition.tag() != DATATYPE_DEFINITION_TAG || definition.field_count() != 3 {
        return Err(EncodedValidationError::invariant(
            "validated datatype definition lost its schema-1 shape",
        )
        .into());
    }
    let datatype = required_node(
        model,
        definition.fields().start,
        "profile datatype definition head",
    )?;
    let identity = profile_entity_identity(model, datatype, budget)?;
    if identity.kind != ProfileEntityKind::Datatype {
        return Err(EncodedValidationError::invariant(
            "validated datatype definition head is not a datatype",
        )
        .into());
    }
    let data_range_field = definition
        .fields()
        .start
        .checked_add(1)
        .ok_or_else(|| EncodedValidationError::resource("profile datatype field overflowed"))?;
    let data_range = required_node(
        model,
        data_range_field,
        "profile datatype definition data range",
    )?;
    let references = collect_profile_datatype_references(model, data_range, budget, control)?;
    let failure = profile_data_range_failure(model, data_range, budget, literal_budget, control)?;
    let following = target.len().checked_add(1).ok_or_else(|| {
        ProfilePhaseError::Encoded(EncodedValidationError::resource(
            "profile datatype definition count overflowed",
        ))
    })?;
    budget
        .claim_datatype_definition(following)
        .map_err(ProfilePhaseError::Encoded)?;
    let statement_order_key = clone_profile_bytes(
        statement_order_key,
        budget,
        "profile datatype statement key allocation failed",
    )
    .map_err(ProfilePhaseError::Encoded)?;
    reserve_profile_one(
        target,
        budget,
        "profile datatype definition allocation failed",
    )
    .map_err(ProfilePhaseError::Encoded)?;
    target.push(ProfileDatatypeDefinition {
        statement_order_key,
        datatype_iri: identity.iri,
        references,
        failure,
    });
    Ok(())
}

fn collect_profile_datatype_references<B: ByteSource, E>(
    model: &ValidatedModel<B>,
    root: NodeId,
    budget: &mut PhaseBudget,
    control: &mut impl FnMut(&'static str) -> Result<(), E>,
) -> ControlledResult<Vec<Vec<u8>>, E> {
    let mut stack = Vec::new();
    reserve_profile_one(
        &mut stack,
        budget,
        "profile datatype traversal allocation failed",
    )
    .map_err(ProfilePhaseError::Encoded)?;
    stack.push(root);
    let mut references = Vec::new();
    while let Some(identifier) = stack.pop() {
        poll(control, "profile-datatype-definition-node")?;
        budget.claim_work(1).map_err(ProfilePhaseError::Encoded)?;
        let node = model.node(identifier)?;
        match node.tag() {
            ENTITY_TAG => {
                let identity = profile_entity_identity(model, identifier, budget)?;
                if identity.kind != ProfileEntityKind::Datatype {
                    return Err(EncodedValidationError::invariant(
                        "validated datatype reference is not a datatype entity",
                    )
                    .into());
                }
                budget
                    .claim_datatype_reference(1)
                    .map_err(ProfilePhaseError::Encoded)?;
                reserve_profile_one(
                    &mut references,
                    budget,
                    "profile datatype reference allocation failed",
                )
                .map_err(ProfilePhaseError::Encoded)?;
                references.push(identity.iri);
            }
            DATA_INTERSECTION_OF_TAG | DATA_UNION_OF_TAG => {
                if node.field_count() != 1 {
                    return Err(EncodedValidationError::invariant(
                        "validated datatype Boolean lost its schema-1 shape",
                    )
                    .into());
                }
                let component = required_component(
                    model.field(node.fields().start)?,
                    "profile datatype Boolean operands",
                )?;
                let ComponentValue::Collection(collection) = model.resolve(component)? else {
                    return Err(EncodedValidationError::invariant(
                        "validated datatype Boolean operands are not a collection",
                    )
                    .into());
                };
                if collection.kind() != ComponentKind::Set || collection.len() < 2 {
                    return Err(EncodedValidationError::invariant(
                        "validated datatype Boolean operands have an invalid shape",
                    )
                    .into());
                }
                for item_index in collection.items() {
                    poll(control, "profile-datatype-definition-member")?;
                    budget.claim_work(1).map_err(ProfilePhaseError::Encoded)?;
                    let item = required_component(
                        model.item(item_index)?,
                        "profile datatype Boolean operand",
                    )?;
                    let ComponentValue::Node(item) = model.resolve(item)? else {
                        return Err(EncodedValidationError::invariant(
                            "validated datatype Boolean operand is not a node",
                        )
                        .into());
                    };
                    reserve_profile_one(
                        &mut stack,
                        budget,
                        "profile datatype traversal allocation failed",
                    )
                    .map_err(ProfilePhaseError::Encoded)?;
                    stack.push(item);
                }
            }
            DATA_COMPLEMENT_OF_TAG => {
                if node.field_count() != 1 {
                    return Err(EncodedValidationError::invariant(
                        "validated datatype complement lost its schema-1 shape",
                    )
                    .into());
                }
                let operand = required_node(
                    model,
                    node.fields().start,
                    "profile datatype complement operand",
                )?;
                reserve_profile_one(
                    &mut stack,
                    budget,
                    "profile datatype traversal allocation failed",
                )
                .map_err(ProfilePhaseError::Encoded)?;
                stack.push(operand);
            }
            DATA_ONE_OF_TAG => {
                if node.field_count() != 1 {
                    return Err(EncodedValidationError::invariant(
                        "validated data enumeration lost its schema-1 shape",
                    )
                    .into());
                }
            }
            DATATYPE_RESTRICTION_TAG => {
                if node.field_count() != 2 {
                    return Err(EncodedValidationError::invariant(
                        "validated datatype restriction lost its schema-1 shape",
                    )
                    .into());
                }
                let datatype =
                    required_node(model, node.fields().start, "profile restricted datatype")?;
                let identity = profile_entity_identity(model, datatype, budget)?;
                if identity.kind != ProfileEntityKind::Datatype {
                    return Err(EncodedValidationError::invariant(
                        "validated restricted datatype is not a datatype entity",
                    )
                    .into());
                }
                budget
                    .claim_datatype_reference(1)
                    .map_err(ProfilePhaseError::Encoded)?;
                reserve_profile_one(
                    &mut references,
                    budget,
                    "profile datatype reference allocation failed",
                )
                .map_err(ProfilePhaseError::Encoded)?;
                references.push(identity.iri);
            }
            _ => {
                return Err(EncodedValidationError::invariant(
                    "validated datatype definition contains an unknown data range",
                )
                .into());
            }
        }
    }
    budget
        .claim_work(sort_work(references.len()))
        .map_err(ProfilePhaseError::Encoded)?;
    references.sort();
    references.dedup();
    Ok(references)
}

const fn is_profile_complex_data_range(tag: u16) -> bool {
    matches!(
        tag,
        DATA_INTERSECTION_OF_TAG
            | DATA_UNION_OF_TAG
            | DATA_COMPLEMENT_OF_TAG
            | DATA_ONE_OF_TAG
            | DATATYPE_RESTRICTION_TAG
    )
}

fn retain_profile_datatype_range_failure<B: ByteSource, E>(
    model: &ValidatedModel<B>,
    identifier: NodeId,
    scope_maps: &[AnonymousScopeMap],
    target: &mut Vec<ProfileDatatypeRangeFailure>,
    budget: &mut PhaseBudget,
    literal_budget: &mut LiteralPhaseBudget,
    control: &mut impl FnMut(&'static str) -> Result<(), E>,
) -> ControlledResult<(), E> {
    let Some(failure) =
        profile_data_range_failure(model, identifier, budget, literal_budget, control)?
    else {
        return Ok(());
    };
    let following = target.len().checked_add(1).ok_or_else(|| {
        ProfilePhaseError::Encoded(EncodedValidationError::resource(
            "profile datatype failure count overflowed",
        ))
    })?;
    budget
        .claim_datatype_failure(following)
        .map_err(ProfilePhaseError::Encoded)?;
    let canonical_key = canonical::canonical_node_key(model, identifier, scope_maps, budget)
        .map_err(ProfilePhaseError::Encoded)?;
    reserve_profile_one(target, budget, "profile datatype failure allocation failed")
        .map_err(ProfilePhaseError::Encoded)?;
    target.push(ProfileDatatypeRangeFailure {
        canonical_key,
        failure,
    });
    Ok(())
}

#[derive(Debug)]
struct ProfileFacetValue {
    iri: String,
    semantics: ProfileLiteralSemantics,
}

struct ProfilePatternControl<'a, E, F> {
    control: RefCell<&'a mut F>,
    error: RefCell<Option<E>>,
}

impl<'a, E, F> ProfilePatternControl<'a, E, F> {
    const fn new(control: &'a mut F) -> Self {
        Self {
            control: RefCell::new(control),
            error: RefCell::new(None),
        }
    }

    fn into_error(self) -> Option<E> {
        self.error.into_inner()
    }
}

impl<E, F> DatatypeControl for ProfilePatternControl<'_, E, F>
where
    F: FnMut(&'static str) -> Result<(), E>,
{
    fn poll(&self) -> Result<(), DatatypeError> {
        if self.error.borrow().is_some() {
            return Err(DatatypeError::cancelled(
                "profile datatype pattern validation was interrupted",
            ));
        }
        let result = {
            let mut control = self.control.borrow_mut();
            (**control)("profile-datatype-pattern-work")
        };
        match result {
            Ok(()) => Ok(()),
            Err(error) => {
                *self.error.borrow_mut() = Some(error);
                Err(DatatypeError::cancelled(
                    "profile datatype pattern validation was interrupted",
                ))
            }
        }
    }
}

fn profile_data_range_failure<B: ByteSource, E>(
    model: &ValidatedModel<B>,
    identifier: NodeId,
    budget: &mut PhaseBudget,
    literal_budget: &mut LiteralPhaseBudget,
    control: &mut impl FnMut(&'static str) -> Result<(), E>,
) -> ControlledResult<Option<ProfileDatatypeFailure>, E> {
    poll(control, "profile-datatype-range")?;
    budget.claim_work(1).map_err(ProfilePhaseError::Encoded)?;
    let node = model.node(identifier)?;
    match node.tag() {
        ENTITY_TAG => {
            let identity = profile_entity_identity(model, identifier, budget)?;
            if identity.kind != ProfileEntityKind::Datatype {
                return Err(EncodedValidationError::invariant(
                    "validated data range entity is not a datatype",
                )
                .into());
            }
            Ok(None)
        }
        DATA_INTERSECTION_OF_TAG | DATA_UNION_OF_TAG => {
            if node.field_count() != 1 {
                return Err(EncodedValidationError::invariant(
                    "validated datatype Boolean lost its schema-1 shape",
                )
                .into());
            }
            let operands = profile_node_collection(
                model,
                node.fields().start,
                ComponentKind::Set,
                "profile datatype Boolean operands",
            )?;
            if operands.len() < 2 {
                return Err(EncodedValidationError::invariant(
                    "validated datatype Boolean has fewer than two operands",
                )
                .into());
            }
            for item_index in operands.items() {
                poll(control, "profile-datatype-range-member")?;
                let operand =
                    required_item_node(model, item_index, "profile datatype Boolean operand")?;
                if let Some(failure) =
                    profile_data_range_failure(model, operand, budget, literal_budget, control)?
                {
                    return Ok(Some(failure));
                }
            }
            Ok(None)
        }
        DATA_COMPLEMENT_OF_TAG => {
            if node.field_count() != 1 {
                return Err(EncodedValidationError::invariant(
                    "validated datatype complement lost its schema-1 shape",
                )
                .into());
            }
            let operand = required_node(
                model,
                node.fields().start,
                "profile datatype complement operand",
            )?;
            profile_data_range_failure(model, operand, budget, literal_budget, control)
        }
        DATA_ONE_OF_TAG => {
            if node.field_count() != 1 {
                return Err(EncodedValidationError::invariant(
                    "validated data enumeration lost its schema-1 shape",
                )
                .into());
            }
            let values = profile_node_collection(
                model,
                node.fields().start,
                ComponentKind::Set,
                "profile data enumeration values",
            )?;
            if values.is_empty() {
                return Err(EncodedValidationError::invariant(
                    "validated data enumeration is empty",
                )
                .into());
            }
            for item_index in values.items() {
                poll(control, "profile-datatype-enumeration-literal")?;
                let literal =
                    required_item_node(model, item_index, "profile data enumeration literal")?;
                let (_, validation) =
                    classify_profile_literal(model, literal, budget, literal_budget, control)?;
                if let Some(failure) = profile_literal_failure(validation) {
                    return Ok(Some(failure));
                }
            }
            Ok(None)
        }
        DATATYPE_RESTRICTION_TAG => {
            profile_datatype_restriction_failure(model, node, budget, literal_budget, control)
        }
        _ => Err(EncodedValidationError::invariant(
            "profile datatype traversal reached a non-data-range node",
        )
        .into()),
    }
}

fn profile_datatype_restriction_failure<B: ByteSource, E>(
    model: &ValidatedModel<B>,
    restriction: NodeRef,
    budget: &mut PhaseBudget,
    literal_budget: &mut LiteralPhaseBudget,
    control: &mut impl FnMut(&'static str) -> Result<(), E>,
) -> ControlledResult<Option<ProfileDatatypeFailure>, E> {
    if restriction.field_count() != 2 {
        return Err(EncodedValidationError::invariant(
            "validated datatype restriction lost its schema-1 shape",
        )
        .into());
    }
    let fields = restriction.fields();
    let datatype = required_node(model, fields.start, "profile restricted datatype")?;
    let identity = profile_entity_identity(model, datatype, budget)?;
    if identity.kind != ProfileEntityKind::Datatype {
        return Err(EncodedValidationError::invariant(
            "validated restricted datatype is not a datatype entity",
        )
        .into());
    }
    if !is_supported_profile_datatype(&identity.iri, budget).map_err(ProfilePhaseError::Encoded)? {
        return Ok(Some(ProfileDatatypeFailure::UnsupportedRange));
    }
    let datatype_iri = std::str::from_utf8(&identity.iri).map_err(|_| {
        EncodedValidationError::invariant("validated restricted datatype IRI is not UTF-8")
    })?;
    let facets_field = fields.start.checked_add(1).ok_or_else(|| {
        EncodedValidationError::resource("profile datatype restriction field overflowed")
    })?;
    let facets = profile_node_collection(
        model,
        facets_field,
        ComponentKind::Set,
        "profile datatype restriction facets",
    )?;
    if facets.is_empty() {
        return Err(EncodedValidationError::invariant(
            "validated datatype restriction has no facets",
        )
        .into());
    }
    budget
        .claim_owned(
            facets
                .len()
                .checked_mul(size_of::<ProfileFacetValue>())
                .ok_or_else(|| {
                    EncodedValidationError::resource("profile datatype facet value size overflowed")
                })?,
        )
        .map_err(ProfilePhaseError::Encoded)?;
    let mut values = Vec::new();
    reserve_exact(
        &mut values,
        facets.len(),
        "profile datatype facet value allocation failed",
    )
    .map_err(ProfilePhaseError::Encoded)?;
    for item_index in facets.items() {
        poll(control, "profile-datatype-facet-literal")?;
        let facet = required_item_node(model, item_index, "profile datatype facet")?;
        let facet_node = model.node(facet)?;
        if facet_node.tag() != FACET_RESTRICTION_TAG || facet_node.field_count() != 2 {
            return Err(EncodedValidationError::invariant(
                "validated facet restriction lost its schema-1 shape",
            )
            .into());
        }
        let facet_fields = facet_node.fields();
        let iri_node = required_node(model, facet_fields.start, "profile datatype facet IRI")?;
        let iri = profile_iri_text(model, iri_node, budget)?;
        let literal_field = facet_fields.start.checked_add(1).ok_or_else(|| {
            EncodedValidationError::resource("profile datatype facet field overflowed")
        })?;
        let literal = required_node(model, literal_field, "profile datatype facet literal")?;
        let (_, validation) =
            classify_profile_literal(model, literal, budget, literal_budget, control)?;
        match validation {
            ProfileLiteralValidation::Valid(semantics) => {
                values.push(ProfileFacetValue { iri, semantics });
            }
            ProfileLiteralValidation::Invalid(invalid) => {
                return Ok(Some(ProfileDatatypeFailure::InvalidLiteral(invalid)));
            }
            ProfileLiteralValidation::Unsupported => {
                return Ok(Some(ProfileDatatypeFailure::UnsupportedLiteral));
            }
        }
    }
    for value in &values {
        poll(control, "profile-datatype-facet")?;
        if let Some(failure) = profile_facet_failure(datatype_iri, value, budget, control)? {
            return Ok(Some(failure));
        }
    }
    Ok(None)
}

fn profile_facet_failure<E>(
    datatype_iri: &str,
    facet: &ProfileFacetValue,
    budget: &mut PhaseBudget,
    control: &mut impl FnMut(&'static str) -> Result<(), E>,
) -> ControlledResult<Option<ProfileDatatypeFailure>, E> {
    budget
        .claim_work(facet.iri.len())
        .map_err(ProfilePhaseError::Encoded)?;
    let bound = matches!(
        facet.iri.as_str(),
        XSD_MIN_INCLUSIVE_IRI
            | XSD_MIN_EXCLUSIVE_IRI
            | XSD_MAX_INCLUSIVE_IRI
            | XSD_MAX_EXCLUSIVE_IRI
    );
    let length = matches!(
        facet.iri.as_str(),
        XSD_LENGTH_IRI | XSD_MIN_LENGTH_IRI | XSD_MAX_LENGTH_IRI
    );
    if is_profile_numeric_datatype(datatype_iri) {
        if !bound {
            return Ok(Some(ProfileDatatypeFailure::IllegalFacet));
        }
        return Ok(
            (!matches!(facet.semantics, ProfileLiteralSemantics::Numeric { .. }))
                .then_some(ProfileDatatypeFailure::InvalidFacetValue),
        );
    }
    if matches!(
        datatype_iri,
        "http://www.w3.org/2001/XMLSchema#float" | "http://www.w3.org/2001/XMLSchema#double"
    ) {
        if !bound {
            return Ok(Some(ProfileDatatypeFailure::IllegalFacet));
        }
        let valid = matches!(
            (datatype_iri, &facet.semantics),
            (
                "http://www.w3.org/2001/XMLSchema#float",
                ProfileLiteralSemantics::Ieee32
            ) | (
                "http://www.w3.org/2001/XMLSchema#double",
                ProfileLiteralSemantics::Ieee64
            )
        );
        return Ok((!valid).then_some(ProfileDatatypeFailure::InvalidFacetValue));
    }
    if matches!(
        datatype_iri,
        "http://www.w3.org/2001/XMLSchema#dateTime"
            | "http://www.w3.org/2001/XMLSchema#dateTimeStamp"
    ) {
        if !bound {
            return Ok(Some(ProfileDatatypeFailure::IllegalFacet));
        }
        return Ok(
            (!matches!(facet.semantics, ProfileLiteralSemantics::DateTime))
                .then_some(ProfileDatatypeFailure::InvalidFacetValue),
        );
    }
    if matches!(
        datatype_iri,
        "http://www.w3.org/2001/XMLSchema#hexBinary"
            | "http://www.w3.org/2001/XMLSchema#base64Binary"
    ) {
        if !length {
            return Ok(Some(ProfileDatatypeFailure::IllegalFacet));
        }
        return Ok((!matches!(
            facet.semantics,
            ProfileLiteralSemantics::Numeric {
                nonnegative_integer: true
            }
        ))
        .then_some(ProfileDatatypeFailure::InvalidFacetValue));
    }
    if is_profile_string_datatype(datatype_iri) {
        let allowed = length
            || facet.iri == XSD_PATTERN_IRI
            || (datatype_iri == RDF_PLAIN_LITERAL_IRI && facet.iri == RDF_LANG_RANGE_IRI);
        if !allowed {
            return Ok(Some(ProfileDatatypeFailure::IllegalFacet));
        }
        return profile_text_facet_failure(facet, length, budget, control);
    }
    if datatype_iri == "http://www.w3.org/2001/XMLSchema#anyURI" {
        if !length && facet.iri != XSD_PATTERN_IRI {
            return Ok(Some(ProfileDatatypeFailure::IllegalFacet));
        }
        return profile_text_facet_failure(facet, length, budget, control);
    }
    if matches!(
        datatype_iri,
        "http://www.w3.org/2001/XMLSchema#boolean" | RDF_XML_LITERAL_IRI | RDFS_LITERAL_IRI
    ) {
        return Ok(Some(ProfileDatatypeFailure::IllegalFacet));
    }
    Err(
        EncodedValidationError::invariant("supported profile datatype has no facet dispatch")
            .into(),
    )
}

fn profile_text_facet_failure<E>(
    facet: &ProfileFacetValue,
    length: bool,
    budget: &mut PhaseBudget,
    control: &mut impl FnMut(&'static str) -> Result<(), E>,
) -> ControlledResult<Option<ProfileDatatypeFailure>, E> {
    if length {
        return Ok((!matches!(
            facet.semantics,
            ProfileLiteralSemantics::Numeric {
                nonnegative_integer: true
            }
        ))
        .then_some(ProfileDatatypeFailure::InvalidFacetValue));
    }
    let ProfileLiteralSemantics::String {
        ref text,
        tagged: false,
    } = facet.semantics
    else {
        return Ok(Some(ProfileDatatypeFailure::InvalidFacetValue));
    };
    if facet.iri == RDF_LANG_RANGE_IRI {
        return Ok((!valid_profile_language_range(text))
            .then_some(ProfileDatatypeFailure::InvalidLanguageRange));
    }
    poll(control, "profile-datatype-pattern")?;
    budget
        .claim_work(text.len())
        .map_err(ProfilePhaseError::Encoded)?;
    let pattern_control = ProfilePatternControl::new(control);
    let result = XsdRegex::compile(text, RegexLimits::default(), &pattern_control);
    let interrupted = pattern_control.into_error();
    if let Some(error) = interrupted {
        return Err(ProfilePhaseError::Control(error));
    }
    poll(control, "profile-datatype-pattern-complete")?;
    match result {
        Ok(_) => Ok(None),
        Err(error) if error.kind == DatatypeErrorKind::Invalid => {
            Ok(Some(ProfileDatatypeFailure::Suppressed))
        }
        Err(error) if error.kind == DatatypeErrorKind::Resource => {
            Err(EncodedValidationError::resource(format!(
                "profile datatype pattern resource limit: {}",
                error.message
            ))
            .into())
        }
        Err(error) => Err(EncodedValidationError::invariant(format!(
            "profile datatype pattern validation failed unexpectedly: {}",
            error.message
        ))
        .into()),
    }
}

fn profile_literal_failure(validation: ProfileLiteralValidation) -> Option<ProfileDatatypeFailure> {
    match validation {
        ProfileLiteralValidation::Valid(_) => None,
        ProfileLiteralValidation::Invalid(invalid) => {
            Some(ProfileDatatypeFailure::InvalidLiteral(invalid))
        }
        ProfileLiteralValidation::Unsupported => Some(ProfileDatatypeFailure::UnsupportedLiteral),
    }
}

fn is_profile_numeric_datatype(datatype_iri: &str) -> bool {
    datatype_iri == OWL_REAL_IRI
        || datatype_iri == OWL_RATIONAL_IRI
        || datatype_iri
            .strip_prefix(XSD_NAMESPACE)
            .is_some_and(|local| {
                matches!(
                    local,
                    "decimal"
                        | "integer"
                        | "nonNegativeInteger"
                        | "positiveInteger"
                        | "nonPositiveInteger"
                        | "negativeInteger"
                        | "long"
                        | "int"
                        | "short"
                        | "byte"
                        | "unsignedLong"
                        | "unsignedInt"
                        | "unsignedShort"
                        | "unsignedByte"
                )
            })
}

fn is_profile_string_datatype(datatype_iri: &str) -> bool {
    datatype_iri == RDF_PLAIN_LITERAL_IRI
        || datatype_iri
            .strip_prefix(XSD_NAMESPACE)
            .is_some_and(|local| {
                matches!(
                    local,
                    "string"
                        | "normalizedString"
                        | "token"
                        | "language"
                        | "Name"
                        | "NCName"
                        | "NMTOKEN"
                )
            })
}

fn valid_profile_language_range(value: &str) -> bool {
    if value == "*" {
        return true;
    }
    let mut parts = value.split('-');
    let Some(first) = parts.next() else {
        return false;
    };
    (1..=8).contains(&first.len())
        && first.is_ascii()
        && first.bytes().all(|byte| byte.is_ascii_alphabetic())
        && parts.all(|part| {
            (1..=8).contains(&part.len())
                && part.is_ascii()
                && part.bytes().all(|byte| byte.is_ascii_alphanumeric())
        })
}

fn profile_entity_identity<B: ByteSource>(
    model: &ValidatedModel<B>,
    identifier: NodeId,
    budget: &mut PhaseBudget,
) -> EncodedResult<ProfileEntityIdentity> {
    budget.claim_work(1)?;
    let entity = model.node(identifier)?;
    if entity.tag() != ENTITY_TAG || entity.field_count() != 2 {
        return Err(EncodedValidationError::invariant(
            "validated profile entity lost its schema-1 shape",
        ));
    }
    let fields = entity.fields();
    let kind_component = required_component(model.field(fields.start)?, "profile entity kind")?;
    let ComponentValue::Scalar(kind_value) = model.resolve(kind_component)? else {
        return Err(EncodedValidationError::invariant(
            "validated profile entity kind is not scalar",
        ));
    };
    budget.claim_work(kind_value.len())?;
    let kind = ProfileEntityKind::from_scalar(kind_value)?;
    let iri_field = fields
        .start
        .checked_add(1)
        .ok_or_else(|| EncodedValidationError::resource("profile entity field index overflowed"))?;
    let iri_identifier = required_node(model, iri_field, "profile entity IRI")?;
    let iri_node = model.node(iri_identifier)?;
    if iri_node.tag() != IRI_TAG || iri_node.field_count() != 1 {
        return Err(EncodedValidationError::invariant(
            "validated profile entity IRI lost its schema-1 shape",
        ));
    }
    let iri_component = required_component(
        model.field(iri_node.fields().start)?,
        "profile entity IRI text",
    )?;
    let ComponentValue::Scalar(iri_value) = model.resolve(iri_component)? else {
        return Err(EncodedValidationError::invariant(
            "validated profile entity IRI text is not scalar",
        ));
    };
    if iri_value.kind() != ComponentKind::Text {
        return Err(EncodedValidationError::invariant(
            "validated profile entity IRI is not text",
        ));
    }
    let iri = clone_profile_scalar(iri_value, budget, "profile entity IRI allocation failed")?;
    std::str::from_utf8(&iri).map_err(|_| {
        EncodedValidationError::invariant("validated profile entity IRI is no longer UTF-8")
    })?;
    Ok(ProfileEntityIdentity { iri, kind })
}

fn clone_profile_scalar<B: ByteSource>(
    value: ScalarRef<B>,
    budget: &mut PhaseBudget,
    message: &'static str,
) -> EncodedResult<Vec<u8>> {
    budget.claim_work(value.len())?;
    budget.claim_owned(value.len())?;
    let mut owned = Vec::new();
    owned
        .try_reserve_exact(value.len())
        .map_err(|_| EncodedValidationError::resource(message))?;
    for index in 0..value.len() {
        owned.push(value.byte(index).ok_or_else(|| {
            EncodedValidationError::invariant("validated profile scalar disappeared")
        })?);
    }
    Ok(owned)
}

fn profile_text_field<B: ByteSource>(
    model: &ValidatedModel<B>,
    field_index: usize,
    name: &'static str,
    budget: &mut PhaseBudget,
) -> EncodedResult<String> {
    let component = required_component(model.field(field_index)?, name)?;
    let ComponentValue::Scalar(value) = model.resolve(component)? else {
        return Err(EncodedValidationError::invariant(format!(
            "validated {name} is not scalar"
        )));
    };
    profile_text_scalar(value, name, budget)
}

fn profile_text_scalar<B: ByteSource>(
    value: ScalarRef<B>,
    name: &'static str,
    budget: &mut PhaseBudget,
) -> EncodedResult<String> {
    if value.kind() != ComponentKind::Text {
        return Err(EncodedValidationError::invariant(format!(
            "validated {name} is not text"
        )));
    }
    let bytes = clone_profile_scalar(value, budget, "profile text allocation failed")?;
    String::from_utf8(bytes)
        .map_err(|_| EncodedValidationError::invariant(format!("validated {name} is not UTF-8")))
}

fn profile_iri_text<B: ByteSource>(
    model: &ValidatedModel<B>,
    identifier: NodeId,
    budget: &mut PhaseBudget,
) -> EncodedResult<String> {
    let iri = model.node(identifier)?;
    if iri.tag() != IRI_TAG || iri.field_count() != 1 {
        return Err(EncodedValidationError::invariant(
            "validated profile IRI lost its schema-1 shape",
        ));
    }
    profile_text_field(model, iri.fields().start, "profile IRI text", budget)
}

fn profile_node_collection<B: ByteSource>(
    model: &ValidatedModel<B>,
    field_index: usize,
    expected_kind: ComponentKind,
    name: &'static str,
) -> EncodedResult<CollectionRef> {
    let component = required_component(model.field(field_index)?, name)?;
    let ComponentValue::Collection(collection) = model.resolve(component)? else {
        return Err(EncodedValidationError::invariant(format!(
            "validated {name} is not a collection"
        )));
    };
    if collection.kind() != expected_kind {
        return Err(EncodedValidationError::invariant(format!(
            "validated {name} changed collection kind"
        )));
    }
    Ok(collection)
}

fn required_item_node<B: ByteSource>(
    model: &ValidatedModel<B>,
    item_index: usize,
    name: &'static str,
) -> EncodedResult<NodeId> {
    let component = required_component(model.item(item_index)?, name)?;
    let ComponentValue::Node(identifier) = model.resolve(component)? else {
        return Err(EncodedValidationError::invariant(format!(
            "validated {name} is not a node"
        )));
    };
    Ok(identifier)
}

fn profile_object_role<B: ByteSource>(
    model: &ValidatedModel<B>,
    identifier: NodeId,
    budget: &mut PhaseBudget,
) -> EncodedResult<ProfileObjectRole> {
    budget.claim_work(1)?;
    let node = model.node(identifier)?;
    let (entity, inverse) = if node.tag() == ENTITY_TAG {
        (identifier, false)
    } else if node.tag() == OBJECT_INVERSE_OF_TAG && node.field_count() == 1 {
        (
            required_node(
                model,
                node.fields().start,
                "profile inverse object property",
            )?,
            true,
        )
    } else {
        return Err(EncodedValidationError::invariant(
            "validated profile object role lost its schema-1 shape",
        ));
    };
    let identity = profile_entity_identity(model, entity, budget)?;
    if identity.kind != ProfileEntityKind::ObjectProperty {
        return Err(EncodedValidationError::invariant(
            "validated profile object role is not an object-property entity",
        ));
    }
    let inverse = inverse
        && identity.iri != TOP_OBJECT_PROPERTY_IRI
        && identity.iri != BOTTOM_OBJECT_PROPERTY_IRI;
    Ok(ProfileObjectRole {
        iri: identity.iri,
        inverse,
    })
}

fn clone_profile_object_role(
    role: &ProfileObjectRole,
    budget: &mut PhaseBudget,
) -> EncodedResult<ProfileObjectRole> {
    Ok(ProfileObjectRole {
        iri: clone_profile_bytes(
            &role.iri,
            budget,
            "profile object-role IRI allocation failed",
        )?,
        inverse: role.inverse,
    })
}

fn inverse_profile_object_role(
    role: &ProfileObjectRole,
    budget: &mut PhaseBudget,
) -> EncodedResult<ProfileObjectRole> {
    let mut inverse = clone_profile_object_role(role, budget)?;
    if inverse.iri != TOP_OBJECT_PROPERTY_IRI && inverse.iri != BOTTOM_OBJECT_PROPERTY_IRI {
        inverse.inverse = !inverse.inverse;
    }
    Ok(inverse)
}

fn profile_role_collection<B: ByteSource>(
    model: &ValidatedModel<B>,
    node: NodeRef,
    field_offset: usize,
    name: &'static str,
) -> EncodedResult<CollectionRef> {
    let field = node
        .fields()
        .start
        .checked_add(field_offset)
        .ok_or_else(|| EncodedValidationError::resource("profile role field index overflowed"))?;
    let component = required_component(model.field(field)?, name)?;
    let ComponentValue::Collection(collection) = model.resolve(component)? else {
        return Err(EncodedValidationError::invariant(format!(
            "validated {name} is not a collection"
        )));
    };
    if collection.kind() != ComponentKind::Set {
        return Err(EncodedValidationError::invariant(format!(
            "validated {name} is not a canonical set"
        )));
    }
    Ok(collection)
}

fn profile_role_field_with_budget<B: ByteSource>(
    model: &ValidatedModel<B>,
    node: NodeRef,
    field_offset: usize,
    name: &'static str,
    budget: &mut PhaseBudget,
) -> EncodedResult<ProfileObjectRole> {
    let field = node
        .fields()
        .start
        .checked_add(field_offset)
        .ok_or_else(|| EncodedValidationError::resource("profile role field index overflowed"))?;
    profile_object_role(model, required_node(model, field, name)?, budget)
}

fn profile_role_item<B: ByteSource>(
    model: &ValidatedModel<B>,
    item_index: usize,
    name: &'static str,
    budget: &mut PhaseBudget,
) -> EncodedResult<ProfileObjectRole> {
    let item = required_component(model.item(item_index)?, name)?;
    let ComponentValue::Node(identifier) = model.resolve(item)? else {
        return Err(EncodedValidationError::invariant(format!(
            "validated {name} is not a node"
        )));
    };
    profile_object_role(model, identifier, budget)
}

fn push_profile_role_inclusion(
    target: &mut Vec<ProfileRoleInclusion>,
    inclusion: ProfileRoleInclusion,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    let following = target.len().checked_add(1).ok_or_else(|| {
        EncodedValidationError::resource("profile role inclusion count overflowed")
    })?;
    budget.claim_role_inclusion(following)?;
    reserve_profile_one(target, budget, "profile role inclusion allocation failed")?;
    target.push(inclusion);
    Ok(())
}

fn add_profile_simple_inclusion(
    target: &mut Vec<ProfileRoleInclusion>,
    sub_role: &ProfileObjectRole,
    super_role: &ProfileObjectRole,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    let inverse_sub = inverse_profile_object_role(sub_role, budget)?;
    let inverse_super = inverse_profile_object_role(super_role, budget)?;
    push_profile_role_inclusion(
        target,
        ProfileRoleInclusion {
            sub_role: clone_profile_object_role(sub_role, budget)?,
            super_role: clone_profile_object_role(super_role, budget)?,
        },
        budget,
    )?;
    push_profile_role_inclusion(
        target,
        ProfileRoleInclusion {
            sub_role: inverse_sub,
            super_role: inverse_super,
        },
        budget,
    )
}

fn push_non_simple_role_seed(
    target: &mut Vec<ProfileObjectRole>,
    role: ProfileObjectRole,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    let following = target.len().checked_add(1).ok_or_else(|| {
        EncodedValidationError::resource("profile non-simple role seed count overflowed")
    })?;
    budget.claim_non_simple_role_seed(following)?;
    reserve_profile_one(
        target,
        budget,
        "profile non-simple role seed allocation failed",
    )?;
    target.push(role);
    Ok(())
}

fn add_non_simple_role_seed_pair(
    target: &mut Vec<ProfileObjectRole>,
    role: &ProfileObjectRole,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    push_non_simple_role_seed(target, clone_profile_object_role(role, budget)?, budget)?;
    push_non_simple_role_seed(target, inverse_profile_object_role(role, budget)?, budget)
}

fn push_profile_complex_role_inclusion(
    target: &mut Vec<ProfileComplexRoleInclusion>,
    inclusion: ProfileComplexRoleInclusion,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    let following = target.len().checked_add(1).ok_or_else(|| {
        EncodedValidationError::resource("profile complex role inclusion count overflowed")
    })?;
    budget.claim_complex_role_inclusion(following)?;
    reserve_profile_one(
        target,
        budget,
        "profile complex role inclusion allocation failed",
    )?;
    target.push(inclusion);
    Ok(())
}

fn add_profile_complex_role_inclusion_pair(
    target: &mut Vec<ProfileComplexRoleInclusion>,
    chain_roles: Vec<ProfileObjectRole>,
    super_role: ProfileObjectRole,
    statement_order_key: &[u8],
    provenance_sha256: [u8; 32],
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    if chain_roles.len() < 2 {
        return Err(EncodedValidationError::invariant(
            "profile complex role inclusion has fewer than two chain members",
        ));
    }
    let mut inverse_chain = Vec::new();
    for role in chain_roles.iter().rev() {
        let inverse = inverse_profile_object_role(role, budget)?;
        reserve_profile_one(
            &mut inverse_chain,
            budget,
            "profile inverse complex role chain allocation failed",
        )?;
        inverse_chain.push(inverse);
    }
    let inverse_super = inverse_profile_object_role(&super_role, budget)?;
    let needs_inverse = inverse_chain != chain_roles || inverse_super != super_role;
    let source_key = clone_profile_bytes(
        statement_order_key,
        budget,
        "profile complex role statement key allocation failed",
    )?;
    let inverse_key = if needs_inverse {
        Some(clone_profile_bytes(
            statement_order_key,
            budget,
            "profile inverse complex role statement key allocation failed",
        )?)
    } else {
        None
    };
    push_profile_complex_role_inclusion(
        target,
        ProfileComplexRoleInclusion {
            super_role,
            chain_roles,
            inverse_generated: false,
            statement_order_key: source_key,
            provenance_sha256,
        },
        budget,
    )?;
    if let Some(statement_order_key) = inverse_key {
        push_profile_complex_role_inclusion(
            target,
            ProfileComplexRoleInclusion {
                super_role: inverse_super,
                chain_roles: inverse_chain,
                inverse_generated: true,
                statement_order_key,
                provenance_sha256,
            },
            budget,
        )?;
    }
    Ok(())
}

fn same_profile_complex_role_semantics(
    left: &ProfileComplexRoleInclusion,
    right: &ProfileComplexRoleInclusion,
) -> bool {
    left.super_role == right.super_role
        && left.chain_roles == right.chain_roles
        && left.inverse_generated == right.inverse_generated
}

fn canonicalize_profile_complex_role_inclusions(
    values: &mut Vec<ProfileComplexRoleInclusion>,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    budget.claim_work(sort_work(values.len()))?;
    values.sort_by(|left, right| {
        left.super_role
            .cmp(&right.super_role)
            .then_with(|| left.chain_roles.cmp(&right.chain_roles))
            .then_with(|| left.inverse_generated.cmp(&right.inverse_generated))
            .then_with(|| right.statement_order_key.cmp(&left.statement_order_key))
            .then_with(|| right.provenance_sha256.cmp(&left.provenance_sha256))
    });
    values.dedup_by(|later, retained| same_profile_complex_role_semantics(later, retained));
    budget.claim_work(sort_work(values.len()))?;
    values.sort();
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn retain_profile_role_axiom_facts<B: ByteSource, E>(
    model: &ValidatedModel<B>,
    identifier: NodeId,
    inclusions: &mut Vec<ProfileRoleInclusion>,
    complex_inclusions: &mut Vec<ProfileComplexRoleInclusion>,
    seeds: &mut Vec<ProfileObjectRole>,
    statement_order_key: &[u8],
    provenance_sha256: [u8; 32],
    budget: &mut PhaseBudget,
    control: &mut impl FnMut(&'static str) -> Result<(), E>,
) -> ControlledResult<(), E> {
    let node = model.node(identifier)?;
    match node.tag() {
        SUB_OBJECT_PROPERTY_TAG => {
            if node.field_count() != 3 {
                return Err(EncodedValidationError::invariant(
                    "validated sub-object-property axiom lost its schema-1 shape",
                )
                .into());
            }
            let sub_field = node.fields().start;
            let sub_identifier =
                required_node(model, sub_field, "profile sub-object-property expression")?;
            let super_role = profile_role_field_with_budget(
                model,
                node,
                1,
                "profile super object property",
                budget,
            )?;
            let sub_node = model.node(sub_identifier)?;
            if sub_node.tag() == OBJECT_PROPERTY_CHAIN_TAG {
                if sub_node.field_count() != 1 {
                    return Err(EncodedValidationError::invariant(
                        "validated object-property chain lost its schema-1 shape",
                    )
                    .into());
                }
                let component = required_component(
                    model.field(sub_node.fields().start)?,
                    "profile object-property chain members",
                )?;
                let ComponentValue::Collection(chain) = model.resolve(component)? else {
                    return Err(EncodedValidationError::invariant(
                        "validated object-property chain members are not a sequence",
                    )
                    .into());
                };
                if chain.kind() != ComponentKind::Sequence || chain.len() < 2 {
                    return Err(EncodedValidationError::invariant(
                        "validated object-property chain has fewer than two ordered members",
                    )
                    .into());
                }
                let mut chain_roles = Vec::new();
                for item_index in chain.items() {
                    poll(control, "profile-role-axiom-member")?;
                    budget.claim_work(1)?;
                    let role = profile_role_item(
                        model,
                        item_index,
                        "profile object-property chain member",
                        budget,
                    )?;
                    reserve_profile_one(
                        &mut chain_roles,
                        budget,
                        "profile complex role chain allocation failed",
                    )?;
                    chain_roles.push(role);
                }
                add_profile_complex_role_inclusion_pair(
                    complex_inclusions,
                    chain_roles,
                    clone_profile_object_role(&super_role, budget)?,
                    statement_order_key,
                    provenance_sha256,
                    budget,
                )?;
                add_non_simple_role_seed_pair(seeds, &super_role, budget)?;
            } else {
                let sub_role = profile_object_role(model, sub_identifier, budget)?;
                add_profile_simple_inclusion(inclusions, &sub_role, &super_role, budget)?;
            }
        }
        EQUIVALENT_OBJECT_PROPERTIES_TAG => {
            if node.field_count() != 2 {
                return Err(EncodedValidationError::invariant(
                    "validated equivalent-object-properties axiom lost its schema-1 shape",
                )
                .into());
            }
            let collection =
                profile_role_collection(model, node, 0, "profile equivalent object properties")?;
            if collection.len() < 2 {
                return Err(EncodedValidationError::invariant(
                    "validated equivalent-object-properties axiom has fewer than two members",
                )
                .into());
            }
            let mut items = collection.items();
            let first_index = items.next().ok_or_else(|| {
                EncodedValidationError::invariant(
                    "validated equivalent-object-properties set is empty",
                )
            })?;
            let first = profile_role_item(
                model,
                first_index,
                "profile equivalent object property",
                budget,
            )?;
            for item_index in items {
                poll(control, "profile-role-axiom-member")?;
                budget.claim_work(1)?;
                let other = profile_role_item(
                    model,
                    item_index,
                    "profile equivalent object property",
                    budget,
                )?;
                add_profile_simple_inclusion(inclusions, &first, &other, budget)?;
                add_profile_simple_inclusion(inclusions, &other, &first, budget)?;
            }
        }
        INVERSE_OBJECT_PROPERTIES_TAG => {
            if node.field_count() != 3 {
                return Err(EncodedValidationError::invariant(
                    "validated inverse-object-properties axiom lost its schema-1 shape",
                )
                .into());
            }
            let first = profile_role_field_with_budget(
                model,
                node,
                0,
                "profile first inverse object property",
                budget,
            )?;
            let second = profile_role_field_with_budget(
                model,
                node,
                1,
                "profile second inverse object property",
                budget,
            )?;
            let inverse_second = inverse_profile_object_role(&second, budget)?;
            add_profile_simple_inclusion(inclusions, &first, &inverse_second, budget)?;
            add_profile_simple_inclusion(inclusions, &inverse_second, &first, budget)?;
        }
        SYMMETRIC_OBJECT_PROPERTY_TAG => {
            if node.field_count() != 2 {
                return Err(EncodedValidationError::invariant(
                    "validated symmetric-object-property axiom lost its schema-1 shape",
                )
                .into());
            }
            let role = profile_role_field_with_budget(
                model,
                node,
                0,
                "profile symmetric object property",
                budget,
            )?;
            let inverse = inverse_profile_object_role(&role, budget)?;
            add_profile_simple_inclusion(inclusions, &role, &inverse, budget)?;
            add_profile_simple_inclusion(inclusions, &inverse, &role, budget)?;
        }
        TRANSITIVE_OBJECT_PROPERTY_TAG => {
            if node.field_count() != 2 {
                return Err(EncodedValidationError::invariant(
                    "validated transitive-object-property axiom lost its schema-1 shape",
                )
                .into());
            }
            let role = profile_role_field_with_budget(
                model,
                node,
                0,
                "profile transitive object property",
                budget,
            )?;
            let mut chain_roles = Vec::new();
            for _ in 0..2 {
                reserve_profile_one(
                    &mut chain_roles,
                    budget,
                    "profile transitive role chain allocation failed",
                )?;
                chain_roles.push(clone_profile_object_role(&role, budget)?);
            }
            add_profile_complex_role_inclusion_pair(
                complex_inclusions,
                chain_roles,
                clone_profile_object_role(&role, budget)?,
                statement_order_key,
                provenance_sha256,
                budget,
            )?;
            add_non_simple_role_seed_pair(seeds, &role, budget)?;
        }
        _ => {}
    }
    Ok(())
}

fn push_simple_role_requirement(
    target: &mut Vec<ProfileSimpleRoleRequirement>,
    role: ProfileObjectRole,
    constructor: &'static str,
    provenance_sha256: [u8; 32],
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    let following = target.len().checked_add(1).ok_or_else(|| {
        EncodedValidationError::resource("profile simple-role requirement count overflowed")
    })?;
    budget.claim_simple_role_requirement(following)?;
    reserve_profile_one(
        target,
        budget,
        "profile simple-role requirement allocation failed",
    )?;
    target.push(ProfileSimpleRoleRequirement {
        role,
        constructor,
        provenance_sha256,
    });
    Ok(())
}

fn retain_simple_role_requirements_for_node<B: ByteSource, E>(
    model: &ValidatedModel<B>,
    identifier: NodeId,
    constructor: &'static str,
    provenance_sha256: [u8; 32],
    target: &mut Vec<ProfileSimpleRoleRequirement>,
    budget: &mut PhaseBudget,
    control: &mut impl FnMut(&'static str) -> Result<(), E>,
) -> ControlledResult<(), E> {
    let node = model.node(identifier)?;
    match node.tag() {
        FUNCTIONAL_OBJECT_PROPERTY_TAG
        | INVERSE_FUNCTIONAL_OBJECT_PROPERTY_TAG
        | IRREFLEXIVE_OBJECT_PROPERTY_TAG
        | ASYMMETRIC_OBJECT_PROPERTY_TAG => {
            if node.field_count() != 2 {
                return Err(EncodedValidationError::invariant(
                    "validated simple-required object characteristic lost its schema-1 shape",
                )
                .into());
            }
            let role = profile_role_field_with_budget(
                model,
                node,
                0,
                "profile simple-required object property",
                budget,
            )?;
            push_simple_role_requirement(target, role, constructor, provenance_sha256, budget)?;
        }
        DISJOINT_OBJECT_PROPERTIES_TAG => {
            if node.field_count() != 2 {
                return Err(EncodedValidationError::invariant(
                    "validated disjoint-object-properties axiom lost its schema-1 shape",
                )
                .into());
            }
            let collection =
                profile_role_collection(model, node, 0, "profile disjoint object properties")?;
            if collection.len() < 2 {
                return Err(EncodedValidationError::invariant(
                    "validated disjoint-object-properties axiom has fewer than two members",
                )
                .into());
            }
            for item_index in collection.items() {
                poll(control, "profile-simple-requirement-member")?;
                budget.claim_work(1)?;
                let role = profile_role_item(
                    model,
                    item_index,
                    "profile disjoint object property",
                    budget,
                )?;
                push_simple_role_requirement(target, role, constructor, provenance_sha256, budget)?;
            }
        }
        OBJECT_HAS_SELF_TAG => {
            if node.field_count() != 1 {
                return Err(EncodedValidationError::invariant(
                    "validated object-self restriction lost its schema-1 shape",
                )
                .into());
            }
            let role = profile_role_field_with_budget(
                model,
                node,
                0,
                "profile object-self property",
                budget,
            )?;
            push_simple_role_requirement(target, role, constructor, provenance_sha256, budget)?;
        }
        OBJECT_MIN_CARDINALITY_TAG | OBJECT_MAX_CARDINALITY_TAG | OBJECT_EXACT_CARDINALITY_TAG => {
            if node.field_count() != 3 {
                return Err(EncodedValidationError::invariant(
                    "validated object cardinality lost its schema-1 shape",
                )
                .into());
            }
            let role = profile_role_field_with_budget(
                model,
                node,
                1,
                "profile object-cardinality property",
                budget,
            )?;
            push_simple_role_requirement(target, role, constructor, provenance_sha256, budget)?;
        }
        _ => {}
    }
    Ok(())
}

fn append_datatype_issues<E>(
    facts: ProfileDatatypeFacts<'_>,
    unsupported_datatypes: ProfileUnsupportedDatatypePolicy,
    issues: &mut Vec<ProfileIssue>,
    budget: &mut PhaseBudget,
    control: &mut impl FnMut(&'static str) -> Result<(), E>,
) -> ControlledResult<(), E> {
    let ProfileDatatypeFacts {
        uses,
        definitions,
        range_failures,
        literals,
    } = facts;
    poll(control, "profile-datatype-preflight")?;
    let mut definitions_by_head = profile_reserved_vec(
        definitions.len(),
        "profile datatype definition reference allocation failed",
        budget,
    )
    .map_err(ProfilePhaseError::Encoded)?;
    definitions_by_head.extend(definitions);
    budget
        .claim_work(sort_work(definitions_by_head.len()))
        .map_err(ProfilePhaseError::Encoded)?;
    definitions_by_head.sort_unstable_by(|left, right| {
        left.datatype_iri
            .cmp(&right.datatype_iri)
            .then_with(|| left.statement_order_key.cmp(&right.statement_order_key))
    });

    let mut duplicate_statement: Option<&[u8]> = None;
    let mut start = 0_usize;
    while start < definitions_by_head.len() {
        poll(control, "profile-datatype-definition-group")?;
        let mut end = start.checked_add(1).ok_or_else(|| {
            ProfilePhaseError::Encoded(EncodedValidationError::resource(
                "profile datatype definition group overflowed",
            ))
        })?;
        while end < definitions_by_head.len()
            && definitions_by_head[end].datatype_iri == definitions_by_head[start].datatype_iri
        {
            budget.claim_work(1).map_err(ProfilePhaseError::Encoded)?;
            end = end.checked_add(1).ok_or_else(|| {
                ProfilePhaseError::Encoded(EncodedValidationError::resource(
                    "profile datatype definition group overflowed",
                ))
            })?;
        }
        if end - start > 1 {
            let candidate = definitions_by_head[start + 1]
                .statement_order_key
                .as_slice();
            if duplicate_statement.is_none_or(|known| candidate < known) {
                duplicate_statement = Some(candidate);
            }
        }
        start = end;
    }

    let mut builtin_statement: Option<&[u8]> = None;
    for definition in definitions {
        poll(control, "profile-datatype-definition-head")?;
        if is_supported_profile_datatype(&definition.datatype_iri, budget)
            .map_err(ProfilePhaseError::Encoded)?
        {
            let candidate = definition.statement_order_key.as_slice();
            if builtin_statement.is_none_or(|known| candidate < known) {
                builtin_statement = Some(candidate);
            }
        }
    }

    let mut defined_datatypes = profile_reserved_vec(
        definitions_by_head.len(),
        "profile defined datatype allocation failed",
        budget,
    )
    .map_err(ProfilePhaseError::Encoded)?;
    defined_datatypes.extend(
        definitions_by_head
            .iter()
            .map(|definition| definition.datatype_iri.as_slice()),
    );
    defined_datatypes.dedup();

    let mut unsupported_iris = profile_reserved_vec(
        uses.len(),
        "profile unsupported datatype allocation failed",
        budget,
    )
    .map_err(ProfilePhaseError::Encoded)?;
    for identity in uses {
        poll(control, "profile-datatype-use")?;
        if identity.kind != ProfileEntityKind::Datatype {
            continue;
        }
        budget
            .claim_work(search_work(defined_datatypes.len()))
            .map_err(ProfilePhaseError::Encoded)?;
        if !is_supported_profile_datatype(&identity.iri, budget)
            .map_err(ProfilePhaseError::Encoded)?
            && defined_datatypes
                .binary_search_by(|candidate| (*candidate).cmp(&identity.iri))
                .is_err()
        {
            unsupported_iris.push(identity.iri.as_slice());
        }
    }
    budget
        .claim_work(sort_work(unsupported_iris.len()))
        .map_err(ProfilePhaseError::Encoded)?;
    unsupported_iris.sort_unstable();
    unsupported_iris.dedup();
    if unsupported_datatypes == ProfileUnsupportedDatatypePolicy::IgnoreWithWarning {
        for iri in &unsupported_iris {
            poll(control, "profile-datatype-opaque-warning")?;
            let iri = std::str::from_utf8(iri).map_err(|_| {
                ProfilePhaseError::Encoded(EncodedValidationError::invariant(
                    "validated unsupported datatype IRI is not UTF-8",
                ))
            })?;
            push_dynamic_profile_issue_with_severity_and_constructor(
                issues,
                UNSUPPORTED_DATATYPE_OPAQUE_RULE,
                "warning",
                &[UNSUPPORTED_DATATYPE_OPAQUE_MESSAGE_PREFIX, iri],
                Some("Datatype"),
                budget,
            )
            .map_err(ProfilePhaseError::Encoded)?;
        }
    }

    let semantic_error = match (builtin_statement, duplicate_statement) {
        (Some(builtin), Some(duplicate)) if builtin < duplicate => Some((
            BUILTIN_DATATYPE_REDEFINITION_RULE,
            BUILTIN_DATATYPE_REDEFINITION_MESSAGE,
        )),
        (_, Some(_)) => Some((
            DUPLICATE_DATATYPE_DEFINITION_RULE,
            DUPLICATE_DATATYPE_DEFINITION_MESSAGE,
        )),
        (Some(_), None) => Some((
            BUILTIN_DATATYPE_REDEFINITION_RULE,
            BUILTIN_DATATYPE_REDEFINITION_MESSAGE,
        )),
        (None, None) => {
            let unsupported = match unsupported_datatypes {
                ProfileUnsupportedDatatypePolicy::Error => !unsupported_iris.is_empty(),
                ProfileUnsupportedDatatypePolicy::IgnoreWithWarning => {
                    profile_definitions_reference_unsupported_datatype(
                        definitions,
                        &defined_datatypes,
                        budget,
                        control,
                    )?
                }
            };
            if unsupported {
                Some((UNSUPPORTED_DATATYPE_RULE, UNSUPPORTED_DATATYPE_MESSAGE))
            } else if profile_datatype_definitions_have_cycle(
                definitions,
                &defined_datatypes,
                budget,
                control,
            )? {
                Some((
                    RECURSIVE_DATATYPE_DEFINITION_RULE,
                    RECURSIVE_DATATYPE_DEFINITION_MESSAGE,
                ))
            } else {
                let first_failure = definitions_by_head
                    .iter()
                    .find_map(|definition| definition.failure)
                    .or_else(|| range_failures.first().map(|failure| failure.failure));
                first_failure.and_then(profile_datatype_failure_issue)
            }
        }
    };
    if let Some((rule_id, message)) = semantic_error {
        push_profile_issue(
            issues,
            ProfileIssue {
                rule_id,
                severity: "error",
                message: Cow::Borrowed(message),
                constructor: Some("DataRange"),
                document_keys: Vec::new(),
                provenance_sha256: None,
            },
            budget,
        )
        .map_err(ProfilePhaseError::Encoded)?;
    }

    for literal in literals {
        poll(control, "profile-literal-datatype")?;
        budget
            .claim_work(search_work(defined_datatypes.len()))
            .map_err(ProfilePhaseError::Encoded)?;
        if defined_datatypes
            .binary_search_by(|candidate| (*candidate).cmp(&literal.datatype_iri))
            .is_ok()
        {
            let iri = std::str::from_utf8(&literal.datatype_iri).map_err(|_| {
                ProfilePhaseError::Encoded(EncodedValidationError::invariant(
                    "validated literal datatype IRI is not UTF-8",
                ))
            })?;
            push_dynamic_profile_issue_with_constructor(
                issues,
                CUSTOM_DATATYPE_LITERAL_RULE,
                &[CUSTOM_DATATYPE_LITERAL_MESSAGE_PREFIX, iri],
                Some("Literal"),
                budget,
            )
            .map_err(ProfilePhaseError::Encoded)?;
            continue;
        }
        match literal.failure {
            Some(ProfileDatatypeFailure::InvalidLiteral(invalid)) => {
                let message = profile_invalid_literal_message(invalid);
                push_profile_issue(
                    issues,
                    ProfileIssue {
                        rule_id: INVALID_LITERAL_RULE,
                        severity: "error",
                        message: Cow::Borrowed(message),
                        constructor: Some("Literal"),
                        document_keys: Vec::new(),
                        provenance_sha256: None,
                    },
                    budget,
                )
                .map_err(ProfilePhaseError::Encoded)?;
            }
            Some(ProfileDatatypeFailure::UnsupportedLiteral) => {
                if unsupported_datatypes == ProfileUnsupportedDatatypePolicy::Error {
                    push_profile_issue(
                        issues,
                        ProfileIssue {
                            rule_id: UNSUPPORTED_DATATYPE_RULE,
                            severity: "error",
                            message: Cow::Borrowed(UNSUPPORTED_LITERAL_DATATYPE_MESSAGE),
                            constructor: Some("Literal"),
                            document_keys: Vec::new(),
                            provenance_sha256: None,
                        },
                        budget,
                    )
                    .map_err(ProfilePhaseError::Encoded)?;
                }
            }
            None => {}
            Some(_) => {
                return Err(EncodedValidationError::invariant(
                    "profile literal retained a non-literal datatype failure",
                )
                .into());
            }
        }
    }
    poll(control, "profile-datatype-complete")?;
    Ok(())
}

const fn profile_datatype_failure_issue(
    failure: ProfileDatatypeFailure,
) -> Option<(&'static str, &'static str)> {
    match failure {
        ProfileDatatypeFailure::InvalidLiteral(invalid) => Some((
            INVALID_LITERAL_RULE,
            profile_invalid_literal_message(invalid),
        )),
        ProfileDatatypeFailure::UnsupportedLiteral => Some((
            UNSUPPORTED_DATATYPE_RULE,
            UNSUPPORTED_LITERAL_DATATYPE_MESSAGE,
        )),
        ProfileDatatypeFailure::UnsupportedRange => {
            Some((UNSUPPORTED_DATATYPE_RULE, UNSUPPORTED_DATATYPE_MESSAGE))
        }
        ProfileDatatypeFailure::IllegalFacet => {
            Some((ILLEGAL_DATATYPE_FACET_RULE, ILLEGAL_DATATYPE_FACET_MESSAGE))
        }
        ProfileDatatypeFailure::InvalidFacetValue => {
            Some((INVALID_FACET_VALUE_RULE, INVALID_FACET_VALUE_MESSAGE))
        }
        ProfileDatatypeFailure::InvalidLanguageRange => {
            Some((INVALID_FACET_VALUE_RULE, INVALID_LANGUAGE_RANGE_MESSAGE))
        }
        ProfileDatatypeFailure::Suppressed => None,
    }
}

const fn profile_invalid_literal_message(invalid: ProfileLiteralInvalid) -> &'static str {
    match invalid {
        ProfileLiteralInvalid::Lexical => INVALID_LITERAL_MESSAGE,
        ProfileLiteralInvalid::XmlMalformed => INVALID_XML_LITERAL_MESSAGE,
        ProfileLiteralInvalid::XmlForbiddenDeclaration => FORBIDDEN_XML_LITERAL_MESSAGE,
    }
}

fn is_supported_profile_datatype(iri: &[u8], budget: &mut PhaseBudget) -> EncodedResult<bool> {
    for builtin in BUILTIN_DATATYPES {
        budget.claim_work(1)?;
        if iri == *builtin {
            return Ok(true);
        }
    }
    Ok(false)
}

fn profile_definitions_reference_unsupported_datatype<E>(
    definitions: &[ProfileDatatypeDefinition],
    defined_datatypes: &[&[u8]],
    budget: &mut PhaseBudget,
    control: &mut impl FnMut(&'static str) -> Result<(), E>,
) -> ControlledResult<bool, E> {
    for definition in definitions {
        for reference in &definition.references {
            poll(control, "profile-datatype-definition-reference")?;
            budget
                .claim_work(search_work(defined_datatypes.len()))
                .map_err(ProfilePhaseError::Encoded)?;
            if !is_supported_profile_datatype(reference, budget)
                .map_err(ProfilePhaseError::Encoded)?
                && defined_datatypes
                    .binary_search_by(|candidate| (*candidate).cmp(reference))
                    .is_err()
            {
                return Ok(true);
            }
        }
    }
    Ok(false)
}

fn profile_datatype_definitions_have_cycle<E>(
    definitions: &[ProfileDatatypeDefinition],
    defined_datatypes: &[&[u8]],
    budget: &mut PhaseBudget,
    control: &mut impl FnMut(&'static str) -> Result<(), E>,
) -> ControlledResult<bool, E> {
    if definitions.is_empty() {
        return Ok(false);
    }
    if definitions.len() != defined_datatypes.len() {
        return Err(EncodedValidationError::invariant(
            "profile datatype cycle received duplicate definitions",
        )
        .into());
    }
    let mut adjacency = profile_empty_rows(
        definitions.len(),
        "profile datatype dependency rows",
        budget,
    )
    .map_err(ProfilePhaseError::Encoded)?;
    let mut indegree = profile_filled_usize(
        definitions.len(),
        0,
        "profile datatype indegree allocation failed",
        budget,
    )
    .map_err(ProfilePhaseError::Encoded)?;
    for definition in definitions {
        poll(control, "profile-datatype-dependency")?;
        budget
            .claim_work(search_work(defined_datatypes.len()))
            .map_err(ProfilePhaseError::Encoded)?;
        let source = defined_datatypes
            .binary_search_by(|candidate| (*candidate).cmp(&definition.datatype_iri))
            .map_err(|_| {
                ProfilePhaseError::Encoded(EncodedValidationError::invariant(
                    "profile datatype definition head is missing from its domain",
                ))
            })?;
        for reference in &definition.references {
            poll(control, "profile-datatype-dependency")?;
            budget
                .claim_work(search_work(defined_datatypes.len()))
                .map_err(ProfilePhaseError::Encoded)?;
            let Ok(target) =
                defined_datatypes.binary_search_by(|candidate| (*candidate).cmp(reference))
            else {
                continue;
            };
            push_profile_graph_value(
                &mut adjacency[source],
                target,
                "profile datatype dependency allocation failed",
                budget,
            )
            .map_err(ProfilePhaseError::Encoded)?;
            indegree[target] = indegree[target].checked_add(1).ok_or_else(|| {
                ProfilePhaseError::Encoded(EncodedValidationError::resource(
                    "profile datatype indegree overflowed",
                ))
            })?;
        }
    }
    canonicalize_profile_rows(&mut adjacency, budget).map_err(ProfilePhaseError::Encoded)?;
    let mut queue = profile_reserved_vec(
        definitions.len(),
        "profile datatype topological queue allocation failed",
        budget,
    )
    .map_err(ProfilePhaseError::Encoded)?;
    for (node, degree) in indegree.iter().copied().enumerate() {
        if degree == 0 {
            queue.push(node);
        }
    }
    let mut offset = 0_usize;
    while offset < queue.len() {
        poll(control, "profile-datatype-topological")?;
        budget.claim_work(1).map_err(ProfilePhaseError::Encoded)?;
        let node = queue[offset];
        offset = offset.checked_add(1).ok_or_else(|| {
            ProfilePhaseError::Encoded(EncodedValidationError::resource(
                "profile datatype queue offset overflowed",
            ))
        })?;
        for &target in &adjacency[node] {
            let degree = indegree.get_mut(target).ok_or_else(|| {
                ProfilePhaseError::Encoded(EncodedValidationError::invariant(
                    "profile datatype dependency target is dangling",
                ))
            })?;
            *degree = degree.checked_sub(1).ok_or_else(|| {
                ProfilePhaseError::Encoded(EncodedValidationError::invariant(
                    "profile datatype indegree underflowed",
                ))
            })?;
            if *degree == 0 {
                queue.push(target);
            }
        }
    }
    Ok(offset != definitions.len())
}

fn append_role_regularity_issues<E>(
    inclusions: &[ProfileRoleInclusion],
    complex_inclusions: &[ProfileComplexRoleInclusion],
    issues: &mut Vec<ProfileIssue>,
    budget: &mut PhaseBudget,
    control: &mut impl FnMut(&'static str) -> Result<(), E>,
) -> ControlledResult<(), E> {
    if complex_inclusions.is_empty() {
        return Ok(());
    }
    poll(control, "profile-regularity-preflight")?;
    let complex_role_references =
        complex_inclusions
            .iter()
            .try_fold(0_usize, |total, inclusion| {
                total
                    .checked_add(inclusion.chain_roles.len())
                    .and_then(|value| value.checked_add(1))
                    .ok_or_else(|| {
                        EncodedValidationError::resource(
                            "profile regularity role reference count overflowed",
                        )
                    })
            })?;
    let role_reference_count = inclusions
        .len()
        .checked_mul(2)
        .and_then(|count| count.checked_add(complex_role_references))
        .ok_or_else(|| {
            ProfilePhaseError::Encoded(EncodedValidationError::resource(
                "profile regularity role reference count overflowed",
            ))
        })?;
    let maximum_dependency_edges = inclusions
        .len()
        .checked_add(
            complex_inclusions
                .iter()
                .try_fold(0_usize, |total, inclusion| {
                    total
                        .checked_add(inclusion.chain_roles.len())
                        .ok_or_else(|| {
                            EncodedValidationError::resource(
                                "profile role dependency edge count overflowed",
                            )
                        })
                })
                .map_err(ProfilePhaseError::Encoded)?,
        )
        .ok_or_else(|| {
            ProfilePhaseError::Encoded(EncodedValidationError::resource(
                "profile role dependency edge count overflowed",
            ))
        })?;
    if maximum_dependency_edges > budget.limits.max_role_dependency_edges {
        return Err(EncodedValidationError::resource(
            "profile role dependency edge count exceeds its limit",
        )
        .into());
    }

    let mut semantic_roles = profile_reserved_vec(
        role_reference_count,
        "profile regularity role reference allocation failed",
        budget,
    )
    .map_err(ProfilePhaseError::Encoded)?;
    for inclusion in inclusions {
        poll(control, "profile-regularity-role-reference")?;
        budget.claim_work(1).map_err(ProfilePhaseError::Encoded)?;
        semantic_roles.push(&inclusion.sub_role);
        semantic_roles.push(&inclusion.super_role);
    }
    for inclusion in complex_inclusions {
        poll(control, "profile-regularity-role-reference")?;
        budget.claim_work(1).map_err(ProfilePhaseError::Encoded)?;
        semantic_roles.push(&inclusion.super_role);
        semantic_roles.extend(&inclusion.chain_roles);
    }
    budget
        .claim_work(sort_work(semantic_roles.len()))
        .map_err(ProfilePhaseError::Encoded)?;
    semantic_roles.sort_unstable();
    semantic_roles.dedup();

    let mut canonical_keys = profile_reserved_vec(
        semantic_roles.len(),
        "profile canonical role key vector allocation failed",
        budget,
    )
    .map_err(ProfilePhaseError::Encoded)?;
    for role in &semantic_roles {
        poll(control, "profile-regularity-role-key")?;
        canonical_keys
            .push(profile_role_canonical_key(role, budget).map_err(ProfilePhaseError::Encoded)?);
    }
    let mut canonical_order = profile_reserved_vec(
        semantic_roles.len(),
        "profile canonical role order allocation failed",
        budget,
    )
    .map_err(ProfilePhaseError::Encoded)?;
    canonical_order.extend(0..semantic_roles.len());
    budget
        .claim_work(sort_work(canonical_order.len()))
        .map_err(ProfilePhaseError::Encoded)?;
    canonical_order
        .sort_unstable_by(|left, right| canonical_keys[*left].cmp(&canonical_keys[*right]));
    if canonical_order
        .windows(2)
        .any(|pair| canonical_keys[pair[0]] >= canonical_keys[pair[1]])
    {
        return Err(EncodedValidationError::invariant(
            "profile canonical object-role keys are not unique",
        )
        .into());
    }
    let mut canonical_id_by_semantic = profile_filled_usize(
        semantic_roles.len(),
        usize::MAX,
        "profile canonical role ID mapping",
        budget,
    )
    .map_err(ProfilePhaseError::Encoded)?;
    for (canonical_id, semantic_id) in canonical_order.into_iter().enumerate() {
        poll(control, "profile-regularity-role-id")?;
        budget.claim_work(1).map_err(ProfilePhaseError::Encoded)?;
        canonical_id_by_semantic[semantic_id] = canonical_id;
    }

    let mut simple_edges = profile_reserved_vec(
        inclusions.len(),
        "profile indexed simple role edge allocation failed",
        budget,
    )
    .map_err(ProfilePhaseError::Encoded)?;
    for inclusion in inclusions {
        poll(control, "profile-regularity-simple-edge")?;
        let sub = profile_canonical_role_id(
            &semantic_roles,
            &canonical_id_by_semantic,
            &inclusion.sub_role,
            budget,
        )
        .map_err(ProfilePhaseError::Encoded)?;
        let sup = profile_canonical_role_id(
            &semantic_roles,
            &canonical_id_by_semantic,
            &inclusion.super_role,
            budget,
        )
        .map_err(ProfilePhaseError::Encoded)?;
        simple_edges.push((sub, sup));
    }
    budget
        .claim_work(sort_work(simple_edges.len()))
        .map_err(ProfilePhaseError::Encoded)?;
    simple_edges.sort_unstable();
    simple_edges.dedup();

    let mut outgoing = profile_empty_rows(
        semantic_roles.len(),
        "profile regularity outgoing role rows",
        budget,
    )
    .map_err(ProfilePhaseError::Encoded)?;
    let mut incoming = profile_empty_rows(
        semantic_roles.len(),
        "profile regularity incoming role rows",
        budget,
    )
    .map_err(ProfilePhaseError::Encoded)?;
    for &(sub, sup) in &simple_edges {
        poll(control, "profile-regularity-simple-adjacency")?;
        budget.claim_work(1).map_err(ProfilePhaseError::Encoded)?;
        push_profile_graph_value(
            &mut outgoing[sub],
            sup,
            "profile outgoing role adjacency allocation failed",
            budget,
        )
        .map_err(ProfilePhaseError::Encoded)?;
        push_profile_graph_value(
            &mut incoming[sup],
            sub,
            "profile incoming role adjacency allocation failed",
            budget,
        )
        .map_err(ProfilePhaseError::Encoded)?;
    }
    canonicalize_profile_rows(&mut outgoing, budget).map_err(ProfilePhaseError::Encoded)?;
    canonicalize_profile_rows(&mut incoming, budget).map_err(ProfilePhaseError::Encoded)?;
    let (component_by_role, component_count) =
        profile_role_components(&outgoing, &incoming, budget, control)?;

    let mut indexed_complex = profile_reserved_vec(
        complex_inclusions.len(),
        "profile indexed complex role inclusion allocation failed",
        budget,
    )
    .map_err(ProfilePhaseError::Encoded)?;
    for (fact_index, inclusion) in complex_inclusions.iter().enumerate() {
        poll(control, "profile-regularity-complex-index")?;
        let super_role_id = profile_canonical_role_id(
            &semantic_roles,
            &canonical_id_by_semantic,
            &inclusion.super_role,
            budget,
        )
        .map_err(ProfilePhaseError::Encoded)?;
        let mut chain_role_ids = profile_reserved_vec(
            inclusion.chain_roles.len(),
            "profile indexed complex role chain allocation failed",
            budget,
        )
        .map_err(ProfilePhaseError::Encoded)?;
        for role in &inclusion.chain_roles {
            chain_role_ids.push(
                profile_canonical_role_id(&semantic_roles, &canonical_id_by_semantic, role, budget)
                    .map_err(ProfilePhaseError::Encoded)?,
            );
        }
        indexed_complex.push(ProfileIndexedComplexRoleInclusion {
            fact_index,
            super_role_id,
            chain_role_ids,
        });
    }
    budget
        .claim_work(sort_work(indexed_complex.len()))
        .map_err(ProfilePhaseError::Encoded)?;
    indexed_complex.sort_by(|left, right| {
        let left_fact = &complex_inclusions[left.fact_index];
        let right_fact = &complex_inclusions[right.fact_index];
        left.super_role_id
            .cmp(&right.super_role_id)
            .then_with(|| left.chain_role_ids.cmp(&right.chain_role_ids))
            .then_with(|| {
                left_fact
                    .inverse_generated
                    .cmp(&right_fact.inverse_generated)
            })
            .then_with(|| {
                left_fact
                    .provenance_sha256
                    .cmp(&right_fact.provenance_sha256)
            })
    });

    let mut dependency_edges = profile_reserved_vec(
        maximum_dependency_edges,
        "profile role dependency edge allocation failed",
        budget,
    )
    .map_err(ProfilePhaseError::Encoded)?;
    for &(sub, sup) in &simple_edges {
        poll(control, "profile-regularity-simple-dependency")?;
        budget.claim_work(1).map_err(ProfilePhaseError::Encoded)?;
        let dependency = component_by_role[sub];
        let consumer = component_by_role[sup];
        if dependency != consumer {
            dependency_edges.push(ProfileDependencyEdge {
                dependency,
                consumer,
                source_index: None,
            });
        }
    }
    for (source_index, inclusion) in indexed_complex.iter().enumerate() {
        poll(control, "profile-regularity-complex")?;
        budget.claim_work(1).map_err(ProfilePhaseError::Encoded)?;
        let fact = &complex_inclusions[inclusion.fact_index];
        if is_top_object_role(&fact.super_role) {
            continue;
        }
        let target = component_by_role[inclusion.super_role_id];
        let inverse_role_id = profile_inverse_canonical_role_id(
            &semantic_roles,
            &canonical_id_by_semantic,
            &fact.super_role,
            budget,
        )
        .map_err(ProfilePhaseError::Encoded)?;
        let inverse_target = component_by_role[inverse_role_id];
        let mut target_count = 0_usize;
        let mut first_target = None;
        let mut inverse_recursion = false;
        for (position, role_id) in inclusion.chain_role_ids.iter().copied().enumerate() {
            poll(control, "profile-regularity-chain-member")?;
            budget.claim_work(1).map_err(ProfilePhaseError::Encoded)?;
            let component = component_by_role[role_id];
            if component == target {
                target_count = target_count.checked_add(1).ok_or_else(|| {
                    ProfilePhaseError::Encoded(EncodedValidationError::resource(
                        "profile regularity target count overflowed",
                    ))
                })?;
                first_target.get_or_insert(position);
            }
            if component == inverse_target && inverse_target != target {
                inverse_recursion = true;
            }
            if component != target {
                dependency_edges.push(ProfileDependencyEdge {
                    dependency: component,
                    consumer: target,
                    source_index: Some(source_index),
                });
            }
        }
        if inverse_recursion {
            push_profile_issue(
                issues,
                ProfileIssue {
                    rule_id: RIA_INVERSE_RECURSION_RULE,
                    severity: "error",
                    message: Cow::Borrowed(RIA_INVERSE_RECURSION_MESSAGE),
                    constructor: Some("SubObjectPropertyOf"),
                    document_keys: Vec::new(),
                    provenance_sha256: Some(fact.provenance_sha256),
                },
                budget,
            )
            .map_err(ProfilePhaseError::Encoded)?;
        }
        let chain_length = inclusion.chain_role_ids.len();
        let valid_recursive = target_count == 0
            || (target_count == 1
                && first_target.is_some_and(|position| {
                    position == 0 || position == chain_length.saturating_sub(1)
                }))
            || (chain_length == 2 && target_count == 2);
        if !valid_recursive {
            push_profile_issue(
                issues,
                ProfileIssue {
                    rule_id: RIA_NON_REGULAR_RECURSION_RULE,
                    severity: "error",
                    message: Cow::Borrowed(RIA_NON_REGULAR_RECURSION_MESSAGE),
                    constructor: Some("SubObjectPropertyOf"),
                    document_keys: Vec::new(),
                    provenance_sha256: Some(fact.provenance_sha256),
                },
                budget,
            )
            .map_err(ProfilePhaseError::Encoded)?;
        }
    }
    if dependency_edges.len() > budget.limits.max_role_dependency_edges {
        return Err(EncodedValidationError::resource(
            "profile role dependency edge count exceeds its limit",
        )
        .into());
    }
    budget
        .claim_work(sort_work(dependency_edges.len()))
        .map_err(ProfilePhaseError::Encoded)?;
    dependency_edges.sort_unstable_by(|left, right| {
        (left.dependency, left.consumer)
            .cmp(&(right.dependency, right.consumer))
            .then_with(|| match (left.source_index, right.source_index) {
                (Some(left), Some(right)) => left.cmp(&right),
                (Some(_), None) => std::cmp::Ordering::Less,
                (None, Some(_)) => std::cmp::Ordering::Greater,
                (None, None) => std::cmp::Ordering::Equal,
            })
    });
    dependency_edges.dedup_by(|later, retained| {
        (later.dependency, later.consumer) == (retained.dependency, retained.consumer)
    });

    let mut adjacency = profile_empty_rows(
        component_count,
        "profile regularity dependency adjacency",
        budget,
    )
    .map_err(ProfilePhaseError::Encoded)?;
    for edge in &dependency_edges {
        poll(control, "profile-regularity-dependency")?;
        budget.claim_work(1).map_err(ProfilePhaseError::Encoded)?;
        push_profile_graph_value(
            &mut adjacency[edge.dependency],
            edge.consumer,
            "profile regularity dependency row allocation failed",
            budget,
        )
        .map_err(ProfilePhaseError::Encoded)?;
    }
    canonicalize_profile_rows(&mut adjacency, budget).map_err(ProfilePhaseError::Encoded)?;
    if let Some(cycle) = profile_shortest_cycle(&adjacency, budget, control)? {
        let source_index = cycle
            .windows(2)
            .find_map(|pair| profile_dependency_edge_source(&dependency_edges, pair[0], pair[1]));
        if let Some(source_index) = source_index {
            let inclusion = indexed_complex.get(source_index).ok_or_else(|| {
                ProfilePhaseError::Encoded(EncodedValidationError::invariant(
                    "profile regularity cycle source is dangling",
                ))
            })?;
            let fact = complex_inclusions
                .get(inclusion.fact_index)
                .ok_or_else(|| {
                    ProfilePhaseError::Encoded(EncodedValidationError::invariant(
                        "profile regularity cycle fact is dangling",
                    ))
                })?;
            push_profile_issue(
                issues,
                ProfileIssue {
                    rule_id: RIA_DEPENDENCY_CYCLE_RULE,
                    severity: "error",
                    message: Cow::Borrowed(RIA_DEPENDENCY_CYCLE_MESSAGE),
                    constructor: Some("SubObjectPropertyOf"),
                    document_keys: Vec::new(),
                    provenance_sha256: Some(fact.provenance_sha256),
                },
                budget,
            )
            .map_err(ProfilePhaseError::Encoded)?;
        } else {
            return Err(EncodedValidationError::invariant(
                "profile regularity cycle has no complex source",
            )
            .into());
        }
    }
    poll(control, "profile-regularity-complete")?;
    Ok(())
}

fn profile_reserved_vec<T>(
    capacity: usize,
    message: &'static str,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<T>> {
    budget.claim_owned(
        capacity.checked_mul(size_of::<T>()).ok_or_else(|| {
            EncodedValidationError::resource("profile allocation size overflowed")
        })?,
    )?;
    let mut values = Vec::new();
    values
        .try_reserve_exact(capacity)
        .map_err(|_| EncodedValidationError::resource(message))?;
    Ok(values)
}

fn profile_filled_usize(
    count: usize,
    value: usize,
    message: &'static str,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<usize>> {
    let mut values = profile_reserved_vec(count, message, budget)?;
    values.resize(count, value);
    Ok(values)
}

fn profile_empty_rows(
    count: usize,
    message: &'static str,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<Vec<usize>>> {
    let mut rows = profile_reserved_vec(count, message, budget)?;
    rows.resize_with(count, Vec::new);
    Ok(rows)
}

fn push_profile_graph_value(
    target: &mut Vec<usize>,
    value: usize,
    message: &'static str,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    reserve_profile_one(target, budget, message)?;
    target.push(value);
    Ok(())
}

fn canonicalize_profile_rows(
    rows: &mut [Vec<usize>],
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    for row in rows {
        budget.claim_work(sort_work(row.len()))?;
        row.sort_unstable();
        row.dedup();
    }
    Ok(())
}

fn profile_role_canonical_key(
    role: &ProfileObjectRole,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<u8>> {
    let mut direct = Vec::new();
    push_profile_key_varint(&mut direct, u64::from(ENTITY_TAG), budget)?;
    push_profile_key_byte(&mut direct, 5, budget)?;
    push_profile_key_varint(&mut direct, 15, budget)?;
    for &byte in b"object_property" {
        push_profile_key_byte(&mut direct, byte, budget)?;
    }
    push_profile_key_byte(&mut direct, 1, budget)?;
    let iri_length = u64::try_from(role.iri.len())
        .map_err(|_| EncodedValidationError::resource("profile role IRI length exceeds u64"))?;
    let iri_node_length = 2_u64
        .checked_add(profile_key_varint_width(iri_length))
        .and_then(|length| length.checked_add(iri_length))
        .ok_or_else(|| {
            EncodedValidationError::resource("profile canonical role key length overflowed")
        })?;
    push_profile_key_varint(&mut direct, iri_node_length, budget)?;
    push_profile_key_varint(&mut direct, u64::from(IRI_TAG), budget)?;
    push_profile_key_byte(&mut direct, 2, budget)?;
    push_profile_key_varint(&mut direct, iri_length, budget)?;
    for &byte in &role.iri {
        push_profile_key_byte(&mut direct, byte, budget)?;
    }
    if !role.inverse {
        return Ok(direct);
    }
    let mut inverse = Vec::new();
    push_profile_key_varint(&mut inverse, u64::from(OBJECT_INVERSE_OF_TAG), budget)?;
    push_profile_key_byte(&mut inverse, 1, budget)?;
    push_profile_key_varint(
        &mut inverse,
        u64::try_from(direct.len()).map_err(|_| {
            EncodedValidationError::resource("profile direct role key length exceeds u64")
        })?,
        budget,
    )?;
    for byte in direct {
        push_profile_key_byte(&mut inverse, byte, budget)?;
    }
    Ok(inverse)
}

const fn profile_key_varint_width(mut value: u64) -> u64 {
    let mut width = 1_u64;
    while value >= 0x80 {
        width += 1;
        value >>= 7;
    }
    width
}

fn push_profile_key_varint(
    target: &mut Vec<u8>,
    mut value: u64,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    loop {
        let mut byte = u8::try_from(value & 0x7f)
            .map_err(|_| EncodedValidationError::invariant("profile varint chunk exceeds u8"))?;
        value >>= 7;
        if value != 0 {
            byte |= 0x80;
        }
        push_profile_key_byte(target, byte, budget)?;
        if value == 0 {
            return Ok(());
        }
    }
}

fn push_profile_key_byte(
    target: &mut Vec<u8>,
    value: u8,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    budget.claim_work(1)?;
    reserve_profile_one(
        target,
        budget,
        "profile canonical role key allocation failed",
    )?;
    target.push(value);
    Ok(())
}

fn profile_canonical_role_id(
    semantic_roles: &[&ProfileObjectRole],
    canonical_id_by_semantic: &[usize],
    target: &ProfileObjectRole,
    budget: &mut PhaseBudget,
) -> EncodedResult<usize> {
    budget.claim_work(search_work(semantic_roles.len()))?;
    let semantic_id = semantic_roles
        .binary_search_by(|candidate| (*candidate).cmp(target))
        .map_err(|_| EncodedValidationError::invariant("profile role domain is incomplete"))?;
    canonical_id_by_semantic
        .get(semantic_id)
        .copied()
        .filter(|value| *value != usize::MAX)
        .ok_or_else(|| EncodedValidationError::invariant("profile canonical role ID is dangling"))
}

fn profile_inverse_canonical_role_id(
    semantic_roles: &[&ProfileObjectRole],
    canonical_id_by_semantic: &[usize],
    role: &ProfileObjectRole,
    budget: &mut PhaseBudget,
) -> EncodedResult<usize> {
    budget.claim_work(search_work(semantic_roles.len()))?;
    let inverse = if role.iri == TOP_OBJECT_PROPERTY_IRI || role.iri == BOTTOM_OBJECT_PROPERTY_IRI {
        role.inverse
    } else {
        !role.inverse
    };
    let semantic_id = semantic_roles
        .binary_search_by(|candidate| {
            candidate
                .iri
                .as_slice()
                .cmp(&role.iri)
                .then_with(|| candidate.inverse.cmp(&inverse))
        })
        .map_err(|_| {
            EncodedValidationError::invariant("profile inverse role domain is incomplete")
        })?;
    canonical_id_by_semantic
        .get(semantic_id)
        .copied()
        .filter(|value| *value != usize::MAX)
        .ok_or_else(|| EncodedValidationError::invariant("profile inverse role ID is dangling"))
}

fn is_top_object_role(role: &ProfileObjectRole) -> bool {
    !role.inverse && role.iri == TOP_OBJECT_PROPERTY_IRI
}

fn profile_role_components<E>(
    outgoing: &[Vec<usize>],
    incoming: &[Vec<usize>],
    budget: &mut PhaseBudget,
    control: &mut impl FnMut(&'static str) -> Result<(), E>,
) -> ControlledResult<(Vec<usize>, usize), E> {
    if outgoing.len() != incoming.len() || outgoing.is_empty() {
        return Err(EncodedValidationError::invariant(
            "profile role SCC adjacency has an invalid shape",
        )
        .into());
    }
    let role_count = outgoing.len();
    let mut visited = profile_reserved_vec(
        role_count,
        "profile role SCC visited allocation failed",
        budget,
    )
    .map_err(ProfilePhaseError::Encoded)?;
    visited.resize(role_count, 0_u8);
    let mut finish = profile_reserved_vec(
        role_count,
        "profile role SCC finish allocation failed",
        budget,
    )
    .map_err(ProfilePhaseError::Encoded)?;
    let mut depth = profile_reserved_vec(
        role_count,
        "profile role SCC stack allocation failed",
        budget,
    )
    .map_err(ProfilePhaseError::Encoded)?;
    for root in 0..role_count {
        poll(control, "profile-regularity-scc-forward")?;
        if visited[root] != 0 {
            continue;
        }
        visited[root] = 1;
        depth.push((root, 0_usize));
        while let Some((node, offset)) = depth.last_mut() {
            poll(control, "profile-regularity-scc-forward")?;
            budget.claim_work(1).map_err(ProfilePhaseError::Encoded)?;
            if *offset < outgoing[*node].len() {
                let successor = outgoing[*node][*offset];
                *offset = offset.checked_add(1).ok_or_else(|| {
                    ProfilePhaseError::Encoded(EncodedValidationError::resource(
                        "profile role SCC offset overflowed",
                    ))
                })?;
                if visited[successor] == 0 {
                    visited[successor] = 1;
                    depth.push((successor, 0));
                }
            } else {
                finish.push(*node);
                depth.pop();
            }
        }
    }
    if finish.len() != role_count {
        return Err(EncodedValidationError::invariant(
            "profile role SCC traversal omitted a finish record",
        )
        .into());
    }

    let mut assigned = profile_reserved_vec(
        role_count,
        "profile role SCC assigned allocation failed",
        budget,
    )
    .map_err(ProfilePhaseError::Encoded)?;
    assigned.resize(role_count, 0_u8);
    let mut pending = profile_reserved_vec(
        role_count,
        "profile role SCC pending allocation failed",
        budget,
    )
    .map_err(ProfilePhaseError::Encoded)?;
    let mut components = Vec::new();
    for &root in finish.iter().rev() {
        poll(control, "profile-regularity-scc-reverse")?;
        if assigned[root] != 0 {
            continue;
        }
        assigned[root] = 1;
        pending.push(root);
        let mut members = Vec::new();
        while let Some(node) = pending.pop() {
            poll(control, "profile-regularity-scc-reverse")?;
            budget.claim_work(1).map_err(ProfilePhaseError::Encoded)?;
            push_profile_graph_value(
                &mut members,
                node,
                "profile role SCC member allocation failed",
                budget,
            )
            .map_err(ProfilePhaseError::Encoded)?;
            for &predecessor in incoming[node].iter().rev() {
                if assigned[predecessor] == 0 {
                    assigned[predecessor] = 1;
                    pending.push(predecessor);
                }
            }
        }
        budget
            .claim_work(sort_work(members.len()))
            .map_err(ProfilePhaseError::Encoded)?;
        members.sort_unstable();
        reserve_profile_one(
            &mut components,
            budget,
            "profile role SCC component allocation failed",
        )
        .map_err(ProfilePhaseError::Encoded)?;
        components.push(members);
    }
    budget
        .claim_work(sort_work(components.len()))
        .map_err(ProfilePhaseError::Encoded)?;
    components.sort_unstable_by_key(|members| members.first().copied().unwrap_or(usize::MAX));
    if components.iter().any(Vec::is_empty) {
        return Err(EncodedValidationError::invariant(
            "profile role SCC traversal produced an empty component",
        )
        .into());
    }
    let mut component_by_role = profile_filled_usize(
        role_count,
        usize::MAX,
        "profile role component mapping allocation failed",
        budget,
    )
    .map_err(ProfilePhaseError::Encoded)?;
    for (component, members) in components.iter().enumerate() {
        for &role in members {
            poll(control, "profile-regularity-scc-map")?;
            budget.claim_work(1).map_err(ProfilePhaseError::Encoded)?;
            if component_by_role[role] != usize::MAX {
                return Err(EncodedValidationError::invariant(
                    "profile role occurs in multiple SCCs",
                )
                .into());
            }
            component_by_role[role] = component;
        }
    }
    if component_by_role.contains(&usize::MAX) {
        return Err(EncodedValidationError::invariant(
            "profile role SCC decomposition omitted a role",
        )
        .into());
    }
    Ok((component_by_role, components.len()))
}

fn profile_shortest_cycle<E>(
    adjacency: &[Vec<usize>],
    budget: &mut PhaseBudget,
    control: &mut impl FnMut(&'static str) -> Result<(), E>,
) -> ControlledResult<Option<Vec<usize>>, E> {
    let component_count = adjacency.len();
    let mut seen = profile_filled_usize(
        component_count,
        usize::MAX,
        "profile cycle seen allocation failed",
        budget,
    )
    .map_err(ProfilePhaseError::Encoded)?;
    let mut parents = profile_filled_usize(
        component_count,
        usize::MAX,
        "profile cycle parent allocation failed",
        budget,
    )
    .map_err(ProfilePhaseError::Encoded)?;
    let mut queue = profile_reserved_vec(
        component_count,
        "profile cycle queue allocation failed",
        budget,
    )
    .map_err(ProfilePhaseError::Encoded)?;
    let mut best: Option<Vec<usize>> = None;
    for start in 0..component_count {
        poll(control, "profile-regularity-cycle-start")?;
        budget.claim_work(1).map_err(ProfilePhaseError::Encoded)?;
        queue.clear();
        queue.push(start);
        seen[start] = start;
        parents[start] = usize::MAX;
        let mut offset = 0_usize;
        let mut found = None;
        while offset < queue.len() && found.is_none() {
            poll(control, "profile-regularity-cycle-search")?;
            budget.claim_work(1).map_err(ProfilePhaseError::Encoded)?;
            let node = queue[offset];
            offset = offset.checked_add(1).ok_or_else(|| {
                ProfilePhaseError::Encoded(EncodedValidationError::resource(
                    "profile cycle queue offset overflowed",
                ))
            })?;
            for &successor in &adjacency[node] {
                budget.claim_work(1).map_err(ProfilePhaseError::Encoded)?;
                if successor == start {
                    found = Some(node);
                    break;
                }
                if seen[successor] != start {
                    seen[successor] = start;
                    parents[successor] = node;
                    if queue.len() == queue.capacity() {
                        return Err(EncodedValidationError::resource(
                            "profile cycle queue exceeded its component domain",
                        )
                        .into());
                    }
                    queue.push(successor);
                }
            }
        }
        if let Some(last) = found {
            let candidate = profile_reconstruct_cycle(start, last, &parents, budget)
                .map_err(ProfilePhaseError::Encoded)?;
            if best.as_ref().is_none_or(|known| {
                (candidate.len(), candidate.as_slice()) < (known.len(), known.as_slice())
            }) {
                best = Some(candidate);
            }
        }
    }
    Ok(best)
}

fn profile_reconstruct_cycle(
    start: usize,
    mut last: usize,
    parents: &[usize],
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<usize>> {
    let mut reverse = Vec::new();
    loop {
        push_profile_graph_value(
            &mut reverse,
            last,
            "profile cycle witness allocation failed",
            budget,
        )?;
        if last == start {
            break;
        }
        last = *parents
            .get(last)
            .ok_or_else(|| EncodedValidationError::invariant("profile cycle parent is dangling"))?;
        if last == usize::MAX {
            return Err(EncodedValidationError::invariant(
                "profile cycle parent chain is incomplete",
            ));
        }
    }
    budget.claim_work(reverse.len())?;
    reverse.reverse();
    push_profile_graph_value(
        &mut reverse,
        start,
        "profile cycle witness allocation failed",
        budget,
    )?;
    Ok(reverse)
}

fn profile_dependency_edge_source(
    edges: &[ProfileDependencyEdge],
    dependency: usize,
    consumer: usize,
) -> Option<usize> {
    edges
        .binary_search_by_key(&(dependency, consumer), |edge| {
            (edge.dependency, edge.consumer)
        })
        .ok()
        .and_then(|index| edges[index].source_index)
}

fn append_non_simple_role_issues<E>(
    inclusions: &[ProfileRoleInclusion],
    seeds: &[ProfileObjectRole],
    requirements: &[ProfileSimpleRoleRequirement],
    issues: &mut Vec<ProfileIssue>,
    budget: &mut PhaseBudget,
    control: &mut impl FnMut(&'static str) -> Result<(), E>,
) -> ControlledResult<(), E> {
    if requirements.is_empty() {
        return Ok(());
    }
    poll(control, "profile-role-preflight")?;
    let role_reference_count = inclusions
        .len()
        .checked_mul(2)
        .and_then(|count| count.checked_add(seeds.len()))
        .and_then(|count| count.checked_add(requirements.len()))
        .ok_or_else(|| {
            ProfilePhaseError::Encoded(EncodedValidationError::resource(
                "profile role reference count overflowed",
            ))
        })?;
    budget
        .claim_owned(
            role_reference_count
                .checked_mul(size_of::<&ProfileObjectRole>())
                .ok_or_else(|| {
                    EncodedValidationError::resource("profile role reference size overflowed")
                })?,
        )
        .map_err(ProfilePhaseError::Encoded)?;
    let mut roles = Vec::new();
    reserve_exact(
        &mut roles,
        role_reference_count,
        "profile role reference allocation failed",
    )
    .map_err(ProfilePhaseError::Encoded)?;
    for inclusion in inclusions {
        poll(control, "profile-role-reference")?;
        roles.push(&inclusion.sub_role);
        roles.push(&inclusion.super_role);
    }
    roles.extend(seeds);
    roles.extend(requirements.iter().map(|requirement| &requirement.role));
    budget
        .claim_work(sort_work(roles.len()))
        .map_err(ProfilePhaseError::Encoded)?;
    roles.sort_unstable();
    roles.dedup();

    budget
        .claim_owned(
            inclusions
                .len()
                .checked_mul(size_of::<(usize, usize)>())
                .ok_or_else(|| {
                    EncodedValidationError::resource(
                        "profile indexed role inclusion size overflowed",
                    )
                })?,
        )
        .map_err(ProfilePhaseError::Encoded)?;
    let mut indexed_inclusions = Vec::new();
    reserve_exact(
        &mut indexed_inclusions,
        inclusions.len(),
        "profile indexed role inclusion allocation failed",
    )
    .map_err(ProfilePhaseError::Encoded)?;
    for inclusion in inclusions {
        poll(control, "profile-role-inclusion")?;
        budget
            .claim_work(search_work(roles.len()).saturating_mul(2))
            .map_err(ProfilePhaseError::Encoded)?;
        indexed_inclusions.push((
            profile_role_index(&roles, &inclusion.sub_role).map_err(ProfilePhaseError::Encoded)?,
            profile_role_index(&roles, &inclusion.super_role)
                .map_err(ProfilePhaseError::Encoded)?,
        ));
    }
    budget
        .claim_work(sort_work(indexed_inclusions.len()))
        .map_err(ProfilePhaseError::Encoded)?;
    indexed_inclusions.sort_unstable();
    indexed_inclusions.dedup();

    budget
        .claim_owned(roles.len())
        .map_err(ProfilePhaseError::Encoded)?;
    let mut marked = Vec::new();
    reserve_exact(
        &mut marked,
        roles.len(),
        "profile non-simple role mark allocation failed",
    )
    .map_err(ProfilePhaseError::Encoded)?;
    marked.resize(roles.len(), 0_u8);
    budget
        .claim_owned(roles.len().checked_mul(size_of::<usize>()).ok_or_else(|| {
            EncodedValidationError::resource("profile non-simple role queue size overflowed")
        })?)
        .map_err(ProfilePhaseError::Encoded)?;
    let mut queue = Vec::new();
    reserve_exact(
        &mut queue,
        roles.len(),
        "profile non-simple role queue allocation failed",
    )
    .map_err(ProfilePhaseError::Encoded)?;
    for seed in seeds {
        poll(control, "profile-role-seed")?;
        budget
            .claim_work(search_work(roles.len()))
            .map_err(ProfilePhaseError::Encoded)?;
        let index = profile_role_index(&roles, seed).map_err(ProfilePhaseError::Encoded)?;
        mark_non_simple_role(index, &mut marked, &mut queue).map_err(ProfilePhaseError::Encoded)?;
    }
    for (index, role) in roles.iter().enumerate() {
        poll(control, "profile-role-builtin")?;
        budget.claim_work(1).map_err(ProfilePhaseError::Encoded)?;
        if !role.inverse
            && (role.iri == TOP_OBJECT_PROPERTY_IRI || role.iri == BOTTOM_OBJECT_PROPERTY_IRI)
        {
            mark_non_simple_role(index, &mut marked, &mut queue)
                .map_err(ProfilePhaseError::Encoded)?;
        }
    }
    let mut queue_offset = 0_usize;
    while queue_offset < queue.len() {
        poll(control, "profile-role-closure")?;
        let role = queue[queue_offset];
        queue_offset = queue_offset.checked_add(1).ok_or_else(|| {
            ProfilePhaseError::Encoded(EncodedValidationError::resource(
                "profile role queue offset overflowed",
            ))
        })?;
        budget
            .claim_work(search_work(indexed_inclusions.len()).saturating_mul(2))
            .map_err(ProfilePhaseError::Encoded)?;
        let start = indexed_inclusions.partition_point(|edge| edge.0 < role);
        let end = indexed_inclusions.partition_point(|edge| edge.0 <= role);
        for &(_, super_role) in &indexed_inclusions[start..end] {
            budget.claim_work(1).map_err(ProfilePhaseError::Encoded)?;
            mark_non_simple_role(super_role, &mut marked, &mut queue)
                .map_err(ProfilePhaseError::Encoded)?;
        }
    }
    for requirement in requirements {
        poll(control, "profile-simple-requirement")?;
        budget
            .claim_work(search_work(roles.len()))
            .map_err(ProfilePhaseError::Encoded)?;
        let role =
            profile_role_index(&roles, &requirement.role).map_err(ProfilePhaseError::Encoded)?;
        if marked[role] == 0 {
            continue;
        }
        push_profile_issue(
            issues,
            ProfileIssue {
                rule_id: NON_SIMPLE_PROPERTY_RULE,
                severity: "error",
                message: Cow::Borrowed(NON_SIMPLE_PROPERTY_MESSAGE),
                constructor: Some(requirement.constructor),
                document_keys: Vec::new(),
                provenance_sha256: Some(requirement.provenance_sha256),
            },
            budget,
        )
        .map_err(ProfilePhaseError::Encoded)?;
    }
    poll(control, "profile-role-complete")?;
    Ok(())
}

fn profile_role_index(
    roles: &[&ProfileObjectRole],
    target: &ProfileObjectRole,
) -> EncodedResult<usize> {
    roles
        .binary_search_by(|candidate| (*candidate).cmp(target))
        .map_err(|_| EncodedValidationError::invariant("profile role index is incomplete"))
}

fn mark_non_simple_role(
    index: usize,
    marked: &mut [u8],
    queue: &mut Vec<usize>,
) -> EncodedResult<()> {
    let selected = marked.get_mut(index).ok_or_else(|| {
        EncodedValidationError::invariant("profile non-simple role index is dangling")
    })?;
    if *selected == 0 {
        *selected = 1;
        if queue.len() == queue.capacity() {
            return Err(EncodedValidationError::resource(
                "profile non-simple role queue exceeded its domain",
            ));
        }
        queue.push(index);
    }
    Ok(())
}

fn append_entity_issues<E>(
    uses: &[ProfileEntityIdentity],
    declarations: &[ProfileEntityIdentity],
    issues: &mut Vec<ProfileIssue>,
    budget: &mut PhaseBudget,
    control: &mut impl FnMut(&'static str) -> Result<(), E>,
) -> ControlledResult<(), E> {
    if uses.is_empty() {
        return Ok(());
    }
    poll(control, "profile-entity-preflight")?;
    let mut start = 0_usize;
    while start < uses.len() {
        poll(control, "profile-entity-iri")?;
        let mut end = start + 1;
        while end < uses.len() && uses[end].iri == uses[start].iri {
            budget.claim_work(1)?;
            end += 1;
        }
        let group = &uses[start..end];
        let iri_bytes = &group[0].iri;
        let iri = std::str::from_utf8(iri_bytes).map_err(|_| {
            EncodedValidationError::invariant("validated profile entity IRI is no longer UTF-8")
        })?;
        let property_kinds = group
            .iter()
            .filter(|identity| identity.kind.is_property())
            .count();
        budget.claim_work(group.len())?;
        if property_kinds > 1 {
            push_dynamic_profile_issue(
                issues,
                PROPERTY_PUNNING_RULE,
                &["IRI is used for more than one property kind: ", iri],
                budget,
            )?;
        }
        budget.claim_work(group.len().saturating_mul(2))?;
        if group
            .iter()
            .any(|identity| identity.kind == ProfileEntityKind::Class)
            && group
                .iter()
                .any(|identity| identity.kind == ProfileEntityKind::Datatype)
        {
            push_dynamic_profile_issue(
                issues,
                CLASS_DATATYPE_PUNNING_RULE,
                &["IRI is used as both class and datatype: ", iri],
                budget,
            )?;
        }

        let reserved = reserved_iri(iri_bytes, budget)?;
        let builtin = if reserved {
            builtin_entity_kind(iri_bytes, budget)?
        } else {
            None
        };
        if reserved {
            if let Some(expected) = builtin {
                budget.claim_work(group.len())?;
                if group.iter().any(|identity| identity.kind != expected) {
                    push_dynamic_profile_issue(
                        issues,
                        BUILTIN_ENTITY_KIND_RULE,
                        &["built-in IRI is used with an illegal entity kind: ", iri],
                        budget,
                    )?;
                }
            } else {
                push_dynamic_profile_issue(
                    issues,
                    RESERVED_VOCABULARY_RULE,
                    &[
                        "reserved vocabulary IRI is not an OWL 2 built-in entity: ",
                        iri,
                    ],
                    budget,
                )?;
            }
        }

        if builtin.is_none() {
            for identity in group {
                budget.claim_work(search_work(declarations.len()))?;
                if identity.kind != ProfileEntityKind::NamedIndividual
                    && declarations.binary_search(identity).is_err()
                {
                    push_dynamic_profile_issue(
                        issues,
                        MISSING_DECLARATION_RULE,
                        &["used ", identity.kind.as_str(), " is not declared: ", iri],
                        budget,
                    )?;
                }
            }
        }
        start = end;
    }
    poll(control, "profile-entity-complete")?;
    Ok(())
}

fn push_dynamic_profile_issue(
    issues: &mut Vec<ProfileIssue>,
    rule_id: &'static str,
    message_parts: &[&str],
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    push_dynamic_profile_issue_with_constructor(issues, rule_id, message_parts, None, budget)
}

fn push_dynamic_profile_issue_with_constructor(
    issues: &mut Vec<ProfileIssue>,
    rule_id: &'static str,
    message_parts: &[&str],
    constructor: Option<&'static str>,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    push_dynamic_profile_issue_with_severity_and_constructor(
        issues,
        rule_id,
        "error",
        message_parts,
        constructor,
        budget,
    )
}

fn push_dynamic_profile_issue_with_severity_and_constructor(
    issues: &mut Vec<ProfileIssue>,
    rule_id: &'static str,
    severity: &'static str,
    message_parts: &[&str],
    constructor: Option<&'static str>,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    let length = message_parts.iter().try_fold(0_usize, |total, part| {
        total
            .checked_add(part.len())
            .ok_or_else(|| EncodedValidationError::resource("profile issue message overflowed"))
    })?;
    budget.claim_owned(length)?;
    let mut message = String::new();
    message
        .try_reserve_exact(length)
        .map_err(|_| EncodedValidationError::resource("profile issue message allocation failed"))?;
    for part in message_parts {
        message.push_str(part);
    }
    push_profile_issue(
        issues,
        ProfileIssue {
            rule_id,
            severity,
            message: Cow::Owned(message),
            constructor,
            document_keys: Vec::new(),
            provenance_sha256: None,
        },
        budget,
    )
}

fn reserved_iri(iri: &[u8], budget: &mut PhaseBudget) -> EncodedResult<bool> {
    for prefix in RESERVED_PREFIXES {
        budget.claim_work(1)?;
        if iri.starts_with(prefix) {
            return Ok(true);
        }
    }
    Ok(false)
}

fn builtin_entity_kind(
    iri: &[u8],
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<ProfileEntityKind>> {
    for (kind, values) in [
        (ProfileEntityKind::Class, BUILTIN_CLASSES),
        (ProfileEntityKind::ObjectProperty, BUILTIN_OBJECT_PROPERTIES),
        (ProfileEntityKind::DataProperty, BUILTIN_DATA_PROPERTIES),
        (
            ProfileEntityKind::AnnotationProperty,
            BUILTIN_ANNOTATION_PROPERTIES,
        ),
        (ProfileEntityKind::Datatype, BUILTIN_DATATYPES),
    ] {
        for value in values {
            budget.claim_work(1)?;
            if iri == *value {
                return Ok(Some(kind));
            }
        }
    }
    Ok(None)
}

fn anonymous_assertion_endpoints<B: ByteSource>(
    model: &ValidatedModel<B>,
    identifier: NodeId,
    scope_maps: &[AnonymousScopeMap],
    budget: &mut PhaseBudget,
) -> EncodedResult<(Option<AnonymousKey>, Option<AnonymousKey>)> {
    budget.claim_work(1)?;
    let node = model.node(identifier)?;
    if node.tag() != OBJECT_PROPERTY_ASSERTION_TAG || node.field_count() != 4 {
        return Err(EncodedValidationError::invariant(
            "validated object-property assertion lost its schema-1 shape",
        ));
    }
    let fields = node.fields();
    let source_field = fields
        .start
        .checked_add(1)
        .ok_or_else(|| EncodedValidationError::resource("profile field index overflowed"))?;
    let target_field = fields
        .start
        .checked_add(2)
        .ok_or_else(|| EncodedValidationError::resource("profile field index overflowed"))?;
    let source = required_node(model, source_field, "profile object-assertion source")?;
    let target = required_node(model, target_field, "profile object-assertion target")?;
    Ok((
        anonymous_endpoint(model, source, scope_maps, budget)?,
        anonymous_endpoint(model, target, scope_maps, budget)?,
    ))
}

fn anonymous_endpoint<B: ByteSource>(
    model: &ValidatedModel<B>,
    identifier: NodeId,
    scope_maps: &[AnonymousScopeMap],
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<AnonymousKey>> {
    match model.node(identifier)?.tag() {
        ANONYMOUS_INDIVIDUAL_TAG => anonymous_key(model, identifier, scope_maps, budget).map(Some),
        ENTITY_TAG => Ok(None),
        _ => Err(EncodedValidationError::invariant(
            "validated object-property assertion endpoint is not an individual",
        )),
    }
}

fn anonymous_key<B: ByteSource>(
    model: &ValidatedModel<B>,
    identifier: NodeId,
    scope_maps: &[AnonymousScopeMap],
    budget: &mut PhaseBudget,
) -> EncodedResult<AnonymousKey> {
    let node = model.node(identifier)?;
    if node.tag() != ANONYMOUS_INDIVIDUAL_TAG || node.field_count() != 2 {
        return Err(EncodedValidationError::invariant(
            "validated anonymous individual lost its schema-1 shape",
        ));
    }
    canonical::canonical_node_key(model, identifier, scope_maps, budget)
}

fn append_anonymous_graph_issues<E>(
    vertices: &[AnonymousKey],
    assertions: &[AnonymousAssertion],
    issues: &mut Vec<ProfileIssue>,
    budget: &mut PhaseBudget,
    control: &mut impl FnMut(&'static str) -> Result<(), E>,
) -> ControlledResult<(), E> {
    if vertices.is_empty() {
        return Ok(());
    }
    poll(control, "profile-anonymous-graph-preflight")?;
    let index_bytes = vertices
        .len()
        .checked_mul(size_of::<usize>())
        .ok_or_else(|| {
            EncodedValidationError::resource("profile anonymous graph index size overflowed")
        })?;

    budget.claim_owned(index_bytes)?;
    let mut parent = Vec::new();
    reserve_exact(
        &mut parent,
        vertices.len(),
        "profile anonymous parent allocation failed",
    )?;
    parent.extend(0..vertices.len());

    budget.claim_owned(index_bytes)?;
    let mut named_link_counts = Vec::new();
    reserve_exact(
        &mut named_link_counts,
        vertices.len(),
        "profile anonymous named-link count allocation failed",
    )?;
    named_link_counts.resize(vertices.len(), 0_usize);

    budget.claim_owned(index_bytes)?;
    let mut named_link_representatives = Vec::new();
    reserve_exact(
        &mut named_link_representatives,
        vertices.len(),
        "profile anonymous named-link representative allocation failed",
    )?;
    named_link_representatives.resize(vertices.len(), usize::MAX);

    let parallel_bytes = assertions
        .len()
        .checked_mul(size_of::<(usize, usize, usize)>())
        .ok_or_else(|| {
            EncodedValidationError::resource("profile anonymous parallel-edge size overflowed")
        })?;
    budget.claim_owned(parallel_bytes)?;
    let mut parallel_edges = Vec::new();
    reserve_exact(
        &mut parallel_edges,
        assertions.len(),
        "profile anonymous parallel-edge allocation failed",
    )?;

    for (assertion_index, assertion) in assertions.iter().enumerate() {
        poll(control, "profile-anonymous-assertion")?;
        budget.claim_work(1)?;
        match (&assertion.source, &assertion.target) {
            (Some(source), Some(target)) => {
                let source_index = anonymous_index(vertices, source, budget)?;
                let target_index = anonymous_index(vertices, target, budget)?;
                let pair = if source_index <= target_index {
                    (source_index, target_index, assertion_index)
                } else {
                    (target_index, source_index, assertion_index)
                };
                parallel_edges.push(pair);
                let source_root = anonymous_root(&mut parent, source_index, budget)?;
                let target_root = anonymous_root(&mut parent, target_index, budget)?;
                if source_root == target_root {
                    push_profile_issue(
                        issues,
                        ProfileIssue {
                            rule_id: ANONYMOUS_GRAPH_CYCLE_RULE,
                            severity: "error",
                            message: Cow::Borrowed(ANONYMOUS_GRAPH_CYCLE_MESSAGE),
                            constructor: Some("ObjectPropertyAssertion"),
                            document_keys: Vec::new(),
                            provenance_sha256: Some(assertion.provenance_sha256),
                        },
                        budget,
                    )?;
                } else {
                    parent[target_root] = source_root;
                }
            }
            (Some(value), None) | (None, Some(value)) => {
                let index = anonymous_index(vertices, value, budget)?;
                named_link_counts[index] =
                    named_link_counts[index].checked_add(1).ok_or_else(|| {
                        EncodedValidationError::resource(
                            "profile anonymous named-link count overflowed",
                        )
                    })?;
                if named_link_representatives[index] == usize::MAX {
                    named_link_representatives[index] = assertion_index;
                }
            }
            (None, None) => {
                return Err(EncodedValidationError::invariant(
                    "profile anonymous assertion contains no anonymous endpoint",
                )
                .into());
            }
        }
    }

    budget.claim_work(sort_work(parallel_edges.len()))?;
    parallel_edges.sort_unstable();
    let mut start = 0_usize;
    while start < parallel_edges.len() {
        let mut end = start + 1;
        while end < parallel_edges.len()
            && parallel_edges[end].0 == parallel_edges[start].0
            && parallel_edges[end].1 == parallel_edges[start].1
        {
            budget.claim_work(1)?;
            end += 1;
        }
        if end - start > 1 {
            let assertion = assertions.get(parallel_edges[start].2).ok_or_else(|| {
                EncodedValidationError::invariant(
                    "profile parallel-edge representative is out of range",
                )
            })?;
            push_profile_issue(
                issues,
                ProfileIssue {
                    rule_id: ANONYMOUS_PARALLEL_EDGE_RULE,
                    severity: "error",
                    message: Cow::Borrowed(ANONYMOUS_PARALLEL_EDGE_MESSAGE),
                    constructor: Some("ObjectPropertyAssertion"),
                    document_keys: Vec::new(),
                    provenance_sha256: Some(assertion.provenance_sha256),
                },
                budget,
            )?;
        }
        start = end;
    }

    budget.claim_owned(index_bytes)?;
    let mut component_by_vertex = Vec::new();
    reserve_exact(
        &mut component_by_vertex,
        vertices.len(),
        "profile anonymous component allocation failed",
    )?;
    budget.claim_owned(index_bytes)?;
    let mut component_roots = Vec::new();
    reserve_exact(
        &mut component_roots,
        vertices.len(),
        "profile anonymous component-root allocation failed",
    )?;
    for vertex in 0..vertices.len() {
        let root = anonymous_root(&mut parent, vertex, budget)?;
        component_by_vertex.push(root);
        component_roots.push(root);
    }
    budget.claim_work(sort_work(component_roots.len()))?;
    component_roots.sort_unstable();
    component_roots.dedup();

    for component_root in component_roots {
        poll(control, "profile-anonymous-component")?;
        let mut representative = usize::MAX;
        let mut valid = true;
        for (vertex, root) in component_by_vertex.iter().copied().enumerate() {
            budget.claim_work(1)?;
            if root != component_root {
                continue;
            }
            if named_link_counts[vertex] <= 1 {
                valid = false;
                break;
            }
            representative = representative.min(named_link_representatives[vertex]);
        }
        if valid {
            let assertion = assertions.get(representative).ok_or_else(|| {
                EncodedValidationError::invariant(
                    "profile anonymous tree-root representative is out of range",
                )
            })?;
            push_profile_issue(
                issues,
                ProfileIssue {
                    rule_id: ANONYMOUS_TREE_ROOT_RULE,
                    severity: "error",
                    message: Cow::Borrowed(ANONYMOUS_TREE_ROOT_MESSAGE),
                    constructor: Some("ObjectPropertyAssertion"),
                    document_keys: Vec::new(),
                    provenance_sha256: Some(assertion.provenance_sha256),
                },
                budget,
            )?;
        }
    }
    poll(control, "profile-anonymous-graph-complete")?;
    Ok(())
}

fn anonymous_index(
    vertices: &[AnonymousKey],
    value: &AnonymousKey,
    budget: &mut PhaseBudget,
) -> EncodedResult<usize> {
    budget.claim_work(search_work(vertices.len()))?;
    vertices.binary_search(value).map_err(|_| {
        EncodedValidationError::invariant(
            "profile anonymous assertion references a missing graph vertex",
        )
    })
}

fn anonymous_root(
    parent: &mut [usize],
    start: usize,
    budget: &mut PhaseBudget,
) -> EncodedResult<usize> {
    let mut current = start;
    loop {
        budget.claim_work(1)?;
        let following = *parent.get(current).ok_or_else(|| {
            EncodedValidationError::invariant("profile anonymous parent index is out of range")
        })?;
        if following == current {
            break;
        }
        current = following;
    }
    let root = current;
    current = start;
    while parent[current] != current {
        budget.claim_work(1)?;
        let following = parent[current];
        parent[current] = root;
        current = following;
    }
    Ok(root)
}

fn is_recomputed_profile_rule(rule_id: &str) -> bool {
    matches!(
        rule_id,
        ANONYMOUS_GRAPH_CYCLE_RULE
            | ANONYMOUS_PARALLEL_EDGE_RULE
            | ANONYMOUS_TREE_ROOT_RULE
            | PROPERTY_PUNNING_RULE
            | CLASS_DATATYPE_PUNNING_RULE
            | RESERVED_VOCABULARY_RULE
            | BUILTIN_ENTITY_KIND_RULE
            | MISSING_DECLARATION_RULE
            | BUILTIN_DATATYPE_REDEFINITION_RULE
            | DUPLICATE_DATATYPE_DEFINITION_RULE
            | UNSUPPORTED_DATATYPE_RULE
            | UNSUPPORTED_DATATYPE_OPAQUE_RULE
            | RECURSIVE_DATATYPE_DEFINITION_RULE
            | CUSTOM_DATATYPE_LITERAL_RULE
            | INVALID_LITERAL_RULE
            | ILLEGAL_DATATYPE_FACET_RULE
            | INVALID_FACET_VALUE_RULE
            | RIA_INVERSE_RECURSION_RULE
            | RIA_NON_REGULAR_RECURSION_RULE
            | RIA_DEPENDENCY_CYCLE_RULE
            | NON_SIMPLE_PROPERTY_RULE
    )
}

fn push_profile_issue(
    issues: &mut Vec<ProfileIssue>,
    issue: ProfileIssue,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    let following = issues
        .len()
        .checked_add(1)
        .ok_or_else(|| EncodedValidationError::resource("profile issue count overflowed"))?;
    budget.claim_issue(following)?;
    reserve_profile_one(issues, budget, "profile issue allocation failed")?;
    issues.push(issue);
    Ok(())
}

fn profile_issues_conform(issues: &[ProfileIssue]) -> bool {
    issues.iter().all(|issue| issue.severity != "error")
}

fn clone_profile_bytes(
    value: &[u8],
    budget: &mut PhaseBudget,
    message: &'static str,
) -> EncodedResult<Vec<u8>> {
    budget.claim_owned(value.len())?;
    let mut owned = Vec::new();
    owned
        .try_reserve_exact(value.len())
        .map_err(|_| EncodedValidationError::resource(message))?;
    owned.extend_from_slice(value);
    Ok(owned)
}

fn reserve_profile_one<T>(
    values: &mut Vec<T>,
    budget: &mut PhaseBudget,
    message: &'static str,
) -> EncodedResult<()> {
    if values.len() < values.capacity() {
        return Ok(());
    }
    let following_capacity = if values.capacity() == 0 {
        4
    } else {
        values
            .capacity()
            .checked_mul(2)
            .ok_or_else(|| EncodedValidationError::resource("profile capacity overflowed"))?
    };
    let additional = following_capacity - values.capacity();
    budget.claim_owned(
        additional.checked_mul(size_of::<T>()).ok_or_else(|| {
            EncodedValidationError::resource("profile allocation size overflowed")
        })?,
    )?;
    values
        .try_reserve_exact(additional)
        .map_err(|_| EncodedValidationError::resource(message))
}

fn forbidden_anonymous_expression<B: ByteSource>(
    model: &ValidatedModel<B>,
    identifier: NodeId,
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<&'static str>> {
    budget.claim_work(1)?;
    let node = model.node(identifier)?;
    match node.tag() {
        OBJECT_ONE_OF_TAG => {
            if node.field_count() != 1 {
                return Err(EncodedValidationError::invariant(
                    "validated ObjectOneOf lost its schema-1 shape",
                ));
            }
            let component =
                required_component(model.field(node.fields().start)?, "profile nominal members")?;
            let ComponentValue::Collection(members) = model.resolve(component)? else {
                return Err(EncodedValidationError::invariant(
                    "validated ObjectOneOf members are not a collection",
                ));
            };
            if members.kind() != ComponentKind::Set {
                return Err(EncodedValidationError::invariant(
                    "validated ObjectOneOf members are not a canonical set",
                ));
            }
            for item_index in members.items() {
                budget.claim_work(1)?;
                let component =
                    required_component(model.item(item_index)?, "profile nominal member")?;
                let ComponentValue::Node(member) = model.resolve(component)? else {
                    return Err(EncodedValidationError::invariant(
                        "validated ObjectOneOf member is not a node",
                    ));
                };
                if model.node(member)?.tag() == ANONYMOUS_INDIVIDUAL_TAG {
                    return Ok(Some("ObjectOneOf"));
                }
            }
            Ok(None)
        }
        OBJECT_HAS_VALUE_TAG => {
            if node.field_count() != 2 {
                return Err(EncodedValidationError::invariant(
                    "validated ObjectHasValue lost its schema-1 shape",
                ));
            }
            let value_field = node.fields().start.checked_add(1).ok_or_else(|| {
                EncodedValidationError::resource("profile field index overflowed")
            })?;
            let value = required_node(model, value_field, "profile ObjectHasValue value")?;
            if model.node(value)?.tag() == ANONYMOUS_INDIVIDUAL_TAG {
                Ok(Some("ObjectHasValue"))
            } else {
                Ok(None)
            }
        }
        _ => Err(EncodedValidationError::invariant(
            "profile anonymous-expression dispatch received a different constructor",
        )),
    }
}

fn allows_top_data_property<B: ByteSource>(
    model: &ValidatedModel<B>,
    identifier: NodeId,
    budget: &mut PhaseBudget,
) -> EncodedResult<bool> {
    budget.claim_work(1)?;
    let node = model.node(identifier)?;
    if node.tag() != SUB_DATA_PROPERTY_TAG {
        return Ok(false);
    }
    if node.field_count() != 3 {
        return Err(EncodedValidationError::invariant(
            "validated data subproperty axiom lost its schema-1 shape",
        ));
    }
    let fields = node.fields();
    let sub_property = required_node(model, fields.start, "profile data subproperty expression")?;
    let super_field = fields
        .start
        .checked_add(1)
        .ok_or_else(|| EncodedValidationError::resource("profile field index overflowed"))?;
    let super_property =
        required_node(model, super_field, "profile data super-property expression")?;
    if !is_top_data_property(model, super_property, budget)? {
        return Ok(false);
    }
    Ok(!is_top_data_property(model, sub_property, budget)?)
}

fn is_top_data_property<B: ByteSource>(
    model: &ValidatedModel<B>,
    identifier: NodeId,
    budget: &mut PhaseBudget,
) -> EncodedResult<bool> {
    budget.claim_work(5)?;
    let entity = model.node(identifier)?;
    if entity.tag() != ENTITY_TAG || entity.field_count() != 2 {
        return Err(EncodedValidationError::invariant(
            "validated profile entity lost its schema-1 shape",
        ));
    }
    let fields = entity.fields();
    let kind_component = required_component(model.field(fields.start)?, "profile entity kind")?;
    let ComponentValue::Scalar(kind) = model.resolve(kind_component)? else {
        return Err(EncodedValidationError::invariant(
            "validated profile entity kind is not scalar",
        ));
    };
    if kind.kind() != ComponentKind::Enum {
        return Err(EncodedValidationError::invariant(
            "validated profile entity kind is not an enum",
        ));
    }
    if !kind.bytes_equal(b"data_property") {
        return Ok(false);
    }
    let iri_field = fields
        .start
        .checked_add(1)
        .ok_or_else(|| EncodedValidationError::resource("profile entity field index overflowed"))?;
    let iri_identifier = required_node(model, iri_field, "profile entity IRI")?;
    let iri = model.node(iri_identifier)?;
    if iri.tag() != IRI_TAG || iri.field_count() != 1 {
        return Err(EncodedValidationError::invariant(
            "validated profile entity IRI lost its schema-1 shape",
        ));
    }
    let text_component =
        required_component(model.field(iri.fields().start)?, "profile entity IRI text")?;
    let ComponentValue::Scalar(text) = model.resolve(text_component)? else {
        return Err(EncodedValidationError::invariant(
            "validated profile entity IRI text is not scalar",
        ));
    };
    if text.kind() != ComponentKind::Text {
        return Err(EncodedValidationError::invariant(
            "validated profile entity IRI is not text",
        ));
    }
    Ok(text.bytes_equal(TOP_DATA_PROPERTY_IRI))
}

fn required_node<B: ByteSource>(
    model: &ValidatedModel<B>,
    field_index: usize,
    name: &'static str,
) -> EncodedResult<NodeId> {
    let component = required_component(model.field(field_index)?, name)?;
    let ComponentValue::Node(identifier) = model.resolve(component)? else {
        return Err(EncodedValidationError::invariant(format!(
            "validated encoded {name} is not a node"
        )));
    };
    Ok(identifier)
}

fn enqueue_component<B: ByteSource>(
    model: &ValidatedModel<B>,
    component: ComponentRef,
    marks: &mut [u32],
    epoch: u32,
    stack: &mut Vec<NodeId>,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    match model.resolve(component)? {
        ComponentValue::Node(identifier) => enqueue_node(identifier, marks, epoch, stack),
        ComponentValue::Collection(collection) => {
            for item_index in collection.items() {
                budget.claim_work(1)?;
                let item = required_component(model.item(item_index)?, "profile collection item")?;
                if let ComponentValue::Node(identifier) = model.resolve(item)? {
                    enqueue_node(identifier, marks, epoch, stack)?;
                }
            }
            Ok(())
        }
        ComponentValue::None | ComponentValue::Scalar(_) => Ok(()),
    }
}

fn enqueue_node(
    identifier: NodeId,
    marks: &mut [u32],
    epoch: u32,
    stack: &mut Vec<NodeId>,
) -> EncodedResult<()> {
    let index = usize::try_from(identifier.get() - 1).map_err(|_| {
        EncodedValidationError::invariant("profile node index exceeds the platform width")
    })?;
    let mark = marks.get_mut(index).ok_or_else(|| {
        EncodedValidationError::invariant("profile node identifier is out of range")
    })?;
    if *mark != epoch {
        *mark = epoch;
        stack.push(identifier);
    }
    Ok(())
}

fn validate_phase(phase: &ProfilePhase) -> EncodedResult<()> {
    if phase.conforms != profile_issues_conform(&phase.issues) {
        return Err(EncodedValidationError::invariant(
            "profile conformance flag diverges from its issues",
        ));
    }
    if phase
        .issues
        .iter()
        .any(|issue| !matches!(issue.severity, "error" | "warning"))
    {
        return Err(EncodedValidationError::invariant(
            "profile issue severity is not recognized",
        ));
    }
    if phase.issues.iter().any(|issue| {
        issue.document_keys.iter().any(String::is_empty)
            || issue
                .document_keys
                .windows(2)
                .any(|pair| pair[0] >= pair[1])
    }) {
        return Err(EncodedValidationError::invariant(
            "profile issue document keys are not canonical sorted unique",
        ));
    }
    if phase.axioms_checked != phase.axiom_keys.len() {
        return Err(EncodedValidationError::invariant(
            "profile checked-axiom count diverges from its canonical keys",
        ));
    }
    if phase.extensions_checked != phase.extension_keys.len() {
        return Err(EncodedValidationError::invariant(
            "profile checked-extension count diverges from its canonical keys",
        ));
    }
    if phase.issues.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err(EncodedValidationError::invariant(
            "profile issues are not canonical sorted unique",
        ));
    }
    if phase.axiom_keys.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err(EncodedValidationError::invariant(
            "profile axiom keys are not canonical sorted unique",
        ));
    }
    if phase
        .extension_keys
        .windows(2)
        .any(|pair| pair[0] >= pair[1])
    {
        return Err(EncodedValidationError::invariant(
            "profile extension keys are not canonical sorted unique",
        ));
    }
    if phase
        .anonymous_vertices
        .windows(2)
        .any(|pair| pair[0] >= pair[1])
    {
        return Err(EncodedValidationError::invariant(
            "profile anonymous vertices are not canonical sorted unique",
        ));
    }
    if phase
        .anonymous_assertions
        .windows(2)
        .any(|pair| pair[0] >= pair[1])
    {
        return Err(EncodedValidationError::invariant(
            "profile anonymous assertions are not canonical sorted unique",
        ));
    }
    if phase.entity_uses.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err(EncodedValidationError::invariant(
            "profile entity uses are not canonical sorted unique",
        ));
    }
    if phase
        .entity_declarations
        .windows(2)
        .any(|pair| pair[0] >= pair[1])
    {
        return Err(EncodedValidationError::invariant(
            "profile entity declarations are not canonical sorted unique",
        ));
    }
    if phase
        .datatype_definitions
        .windows(2)
        .any(|pair| pair[0] >= pair[1])
    {
        return Err(EncodedValidationError::invariant(
            "profile datatype definitions are not canonical sorted unique",
        ));
    }
    if phase.datatype_definitions.iter().any(|definition| {
        definition.statement_order_key.is_empty()
            || definition
                .references
                .windows(2)
                .any(|pair| pair[0] >= pair[1])
    }) {
        return Err(EncodedValidationError::invariant(
            "profile datatype definition has an invalid private shape",
        ));
    }
    if phase
        .datatype_range_failures
        .windows(2)
        .any(|pair| pair[0] >= pair[1])
    {
        return Err(EncodedValidationError::invariant(
            "profile datatype failures are not canonical sorted unique",
        ));
    }
    if phase
        .datatype_range_failures
        .iter()
        .any(|failure| failure.canonical_key.is_empty())
    {
        return Err(EncodedValidationError::invariant(
            "profile datatype failure has an empty canonical key",
        ));
    }
    if phase.literals.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err(EncodedValidationError::invariant(
            "profile literals are not canonical sorted unique",
        ));
    }
    if phase
        .literals
        .iter()
        .any(|literal| literal.canonical_key.is_empty() || literal.datatype_iri.is_empty())
    {
        return Err(EncodedValidationError::invariant(
            "profile literal has an invalid private shape",
        ));
    }
    if phase
        .role_inclusions
        .windows(2)
        .any(|pair| pair[0] >= pair[1])
    {
        return Err(EncodedValidationError::invariant(
            "profile role inclusions are not canonical sorted unique",
        ));
    }
    if phase
        .complex_role_inclusions
        .windows(2)
        .any(|pair| pair[0] >= pair[1])
    {
        return Err(EncodedValidationError::invariant(
            "profile complex role inclusions are not canonical sorted unique",
        ));
    }
    if phase.complex_role_inclusions.iter().any(|inclusion| {
        inclusion.chain_roles.len() < 2 || inclusion.statement_order_key.is_empty()
    }) {
        return Err(EncodedValidationError::invariant(
            "profile complex role inclusion has an invalid private shape",
        ));
    }
    if phase
        .non_simple_role_seeds
        .windows(2)
        .any(|pair| pair[0] >= pair[1])
    {
        return Err(EncodedValidationError::invariant(
            "profile non-simple role seeds are not canonical sorted unique",
        ));
    }
    if phase
        .simple_role_requirements
        .windows(2)
        .any(|pair| pair[0] >= pair[1])
    {
        return Err(EncodedValidationError::invariant(
            "profile simple-role requirements are not canonical sorted unique",
        ));
    }
    Ok(())
}

fn required_component(
    component: Option<ComponentRef>,
    name: &'static str,
) -> EncodedResult<ComponentRef> {
    component.ok_or_else(|| {
        EncodedValidationError::invariant(format!("validated encoded {name} disappeared"))
    })
}

fn poll<E>(
    control: &mut impl FnMut(&'static str) -> Result<(), E>,
    phase: &'static str,
) -> ControlledResult<(), E> {
    control(phase).map_err(ProfilePhaseError::Control)
}

fn into_encoded<T>(result: ControlledResult<T, Infallible>) -> EncodedResult<T> {
    match result {
        Ok(value) => Ok(value),
        Err(ProfilePhaseError::Encoded(error)) => Err(error),
        Err(ProfilePhaseError::Control(never)) => match never {},
    }
}

fn reserve_exact<T>(
    values: &mut Vec<T>,
    additional: usize,
    message: &'static str,
) -> EncodedResult<()> {
    values
        .try_reserve_exact(additional)
        .map_err(|_| EncodedValidationError::resource(message))
}

fn reserve_one<T>(values: &mut Vec<T>, message: &'static str) -> EncodedResult<()> {
    if values.len() == values.capacity() {
        values
            .try_reserve_exact(1)
            .map_err(|_| EncodedValidationError::resource(message))?;
    }
    Ok(())
}

fn sort_work(count: usize) -> usize {
    if count < 2 {
        return count;
    }
    let rounds = usize::BITS - (count - 1).leading_zeros();
    count.saturating_mul(usize::try_from(rounds).unwrap_or(usize::MAX))
}

fn search_work(count: usize) -> usize {
    if count < 2 {
        return 1;
    }
    usize::try_from(usize::BITS - (count - 1).leading_zeros()).unwrap_or(usize::MAX)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::encoded::{EncodedColumns, EncodedLimits};

    #[derive(Clone, Copy)]
    struct Bytes<'a>(&'a [u8]);

    impl ByteSource for Bytes<'_> {
        fn len(self) -> usize {
            self.0.len()
        }

        fn byte(self, index: usize) -> Option<u8> {
            self.0.get(index).copied()
        }
    }

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
        fn borrowed(&self) -> EncodedColumns<Bytes<'_>> {
            EncodedColumns {
                root_kinds: Bytes(&self.root_kinds),
                root_ids: Bytes(&self.root_ids),
                node_tags: Bytes(&self.node_tags),
                node_field_offsets: Bytes(&self.node_field_offsets),
                field_kinds: Bytes(&self.field_kinds),
                field_values: Bytes(&self.field_values),
                field_lengths: Bytes(&self.field_lengths),
                item_kinds: Bytes(&self.item_kinds),
                item_values: Bytes(&self.item_values),
                item_lengths: Bytes(&self.item_lengths),
                scalar_bytes: Bytes(&self.scalar_bytes),
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

    fn invalid_data_arity_columns() -> OwnedColumns {
        OwnedColumns {
            root_kinds: vec![2, 2, 2, 2],
            root_ids: le32(&[10, 11, 12, 13]),
            node_tags: le16(&[1, 1, 1, 1, 2, 2, 2, 2, 41, 60, 60, 60, 61]),
            node_field_offsets: le64(&[0, 1, 2, 3, 4, 6, 8, 10, 12, 14, 16, 18, 20, 23]),
            field_kinds: vec![
                2, 2, 2, 2, 5, 1, 5, 1, 5, 1, 5, 1, 7, 1, 1, 6, 1, 6, 1, 6, 1, 1, 6,
            ],
            field_values: le64(&[
                0, 18, 36, 54, 93, 1, 98, 4, 106, 2, 119, 3, 0, 6, 5, 2, 7, 2, 8, 2, 5, 9, 2,
            ]),
            field_lengths: le64(&[
                18, 18, 18, 39, 5, 0, 8, 0, 13, 0, 13, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            ]),
            item_kinds: vec![1, 1],
            item_values: le64(&[7, 8]),
            item_lengths: le64(&[0, 0]),
            scalar_bytes: concat!(
                "urn:test:profile#A",
                "urn:test:profile#p",
                "urn:test:profile#q",
                "http://www.w3.org/2001/XMLSchema#string",
                "class",
                "datatype",
                "data_property",
                "data_property",
            )
            .as_bytes()
            .to_vec(),
        }
    }

    fn invalid_top_data_property_columns() -> OwnedColumns {
        OwnedColumns {
            root_kinds: vec![2],
            root_ids: le32(&[3]),
            node_tags: le16(&[IRI_TAG, ENTITY_TAG, 95]),
            node_field_offsets: le64(&[0, 1, 3, 5]),
            field_kinds: vec![2, 5, 1, 1, 6],
            field_values: le64(&[0, 45, 1, 2, 0]),
            field_lengths: le64(&[45, 13, 0, 0, 0]),
            item_kinds: Vec::new(),
            item_values: Vec::new(),
            item_lengths: Vec::new(),
            scalar_bytes: concat!(
                "http://www.w3.org/2002/07/owl#topDataProperty",
                "data_property",
            )
            .as_bytes()
            .to_vec(),
        }
    }

    fn allowed_top_data_property_columns() -> OwnedColumns {
        OwnedColumns {
            root_kinds: vec![2],
            root_ids: le32(&[5]),
            node_tags: le16(&[
                IRI_TAG,
                IRI_TAG,
                ENTITY_TAG,
                ENTITY_TAG,
                SUB_DATA_PROPERTY_TAG,
            ]),
            node_field_offsets: le64(&[0, 1, 2, 4, 6, 9]),
            field_kinds: vec![2, 2, 5, 1, 5, 1, 1, 1, 6],
            field_values: le64(&[0, 10, 55, 1, 68, 2, 3, 4, 0]),
            field_lengths: le64(&[10, 45, 13, 0, 13, 0, 0, 0, 0]),
            item_kinds: Vec::new(),
            item_values: Vec::new(),
            item_lengths: Vec::new(),
            scalar_bytes: concat!(
                "urn:test#p",
                "http://www.w3.org/2002/07/owl#topDataProperty",
                "data_property",
                "data_property",
            )
            .as_bytes()
            .to_vec(),
        }
    }

    fn anonymous_forbidden_columns() -> OwnedColumns {
        let mut scalar_bytes = concat!("urn:test#named", "named_individual")
            .as_bytes()
            .to_vec();
        scalar_bytes.extend_from_slice(&[0x11; 32]);
        scalar_bytes.extend_from_slice(&[0x22; 5]);
        OwnedColumns {
            root_kinds: vec![2],
            root_ids: le32(&[4]),
            node_tags: le16(&[
                IRI_TAG,
                ENTITY_TAG,
                ANONYMOUS_INDIVIDUAL_TAG,
                DIFFERENT_INDIVIDUALS_TAG,
            ]),
            node_field_offsets: le64(&[0, 1, 3, 5, 7]),
            field_kinds: vec![2, 5, 1, 3, 3, 6, 6],
            field_values: le64(&[0, 14, 1, 30, 62, 0, 2]),
            field_lengths: le64(&[14, 16, 0, 32, 5, 2, 0]),
            item_kinds: vec![1, 1],
            item_values: le64(&[2, 3]),
            item_lengths: le64(&[0, 0]),
            scalar_bytes,
        }
    }

    fn extension_columns() -> OwnedColumns {
        OwnedColumns {
            root_kinds: vec![3],
            root_ids: le32(&[1]),
            node_tags: le16(&[SWRL_RULE_TAG]),
            node_field_offsets: le64(&[0, 3]),
            field_kinds: vec![6, 6, 6],
            field_values: le64(&[0, 0, 0]),
            field_lengths: le64(&[0, 0, 0]),
            item_kinds: Vec::new(),
            item_values: Vec::new(),
            item_lengths: Vec::new(),
            scalar_bytes: Vec::new(),
        }
    }

    fn model(columns: &OwnedColumns) -> EncodedResult<ValidatedModel<Bytes<'_>>> {
        ValidatedModel::new(columns.borrowed(), EncodedLimits::default())
    }

    #[test]
    fn data_range_arity_issue_and_provenance_are_exact() -> EncodedResult<()> {
        let columns = invalid_data_arity_columns();
        let phase = compile_profile_phase(&model(&columns)?, &[], ProfilePhaseLimits::default())?;
        assert!(!phase.conforms);
        assert_eq!(phase.axioms_checked, 4);
        assert_eq!(phase.extensions_checked, 0);
        assert_eq!(phase.issues.len(), 1);
        assert_eq!(phase.issues[0].rule_id, DATA_RANGE_ARITY_RULE);
        assert_eq!(phase.issues[0].constructor, Some("DataSomeValuesFrom"));
        assert_eq!(
            phase.issues[0]
                .provenance_sha256
                .map(|value| crate::model::hex(&value))
                .as_deref(),
            Some("6a1bfbadd77d1f86ac453a99501c3f363d5b71f420e67ade72d564f590a16aa7")
        );
        let manifest: serde_json::Value = serde_json::from_slice(&phase.canonical_manifest_json()?)
            .map_err(|_| EncodedValidationError::invariant("profile manifest is not JSON"))?;
        assert_eq!(manifest["family"], "owl2_dl_profile");
        assert_eq!(manifest["ordered_rule_ids"][0], DATA_RANGE_ARITY_RULE);
        Ok(())
    }

    #[test]
    fn ontology_identity_rules_are_canonical_bounded_and_cancellable() -> EncodedResult<()> {
        let columns = invalid_data_arity_columns();
        let phase = compile_profile_phase(&model(&columns)?, &[], ProfilePhaseLimits::default())?;
        let identifiers = vec![
            ProfileOntologyIdentifier {
                document_key: b"document:a".to_vec(),
                ontology_iri: Some(b"http://www.w3.org/2002/07/owl#ontology".to_vec()),
                version_iri: None,
            },
            ProfileOntologyIdentifier {
                document_key: b"document:b".to_vec(),
                ontology_iri: Some(b"urn:ontology:b".to_vec()),
                version_iri: Some(b"http://www.w3.org/2000/01/rdf-schema#version".to_vec()),
            },
        ];
        let applied = into_encoded(apply_ontology_identity_context_controlled(
            phase.clone(),
            &identifiers,
            false,
            ProfilePhaseLimits::default(),
            &mut |_phase| Ok::<(), Infallible>(()),
        ))?;
        assert_eq!(
            applied
                .issues
                .iter()
                .filter(|issue| {
                    matches!(
                        issue.rule_id,
                        RESERVED_ONTOLOGY_IRI_RULE | RESERVED_VERSION_IRI_RULE
                    )
                })
                .map(|issue| (
                    issue.rule_id,
                    issue.message.as_ref(),
                    issue.constructor,
                    issue.provenance_sha256,
                ))
                .collect::<Vec<_>>(),
            vec![
                (
                    RESERVED_ONTOLOGY_IRI_RULE,
                    "ontology IRI must not use reserved OWL/RDF vocabulary: http://www.w3.org/2002/07/owl#ontology",
                    Some("OntologyID"),
                    None,
                ),
                (
                    RESERVED_VERSION_IRI_RULE,
                    "version IRI must not use reserved OWL/RDF vocabulary: http://www.w3.org/2000/01/rdf-schema#version",
                    Some("OntologyID"),
                    None,
                ),
            ]
        );

        let cancelled = apply_ontology_identity_context_controlled(
            phase.clone(),
            &identifiers,
            false,
            ProfilePhaseLimits::default(),
            &mut |checkpoint| {
                if checkpoint == "profile-ontology-identity-iri" {
                    Err("injected ontology identity cancellation")
                } else {
                    Ok(())
                }
            },
        );
        assert_eq!(
            cancelled,
            Err(ProfilePhaseError::Control(
                "injected ontology identity cancellation"
            ))
        );

        let limited = apply_ontology_identity_context_controlled(
            phase.clone(),
            &identifiers,
            false,
            ProfilePhaseLimits {
                max_ontology_documents: 1,
                ..ProfilePhaseLimits::default()
            },
            &mut |_phase| Ok::<(), Infallible>(()),
        );
        let Err(ProfilePhaseError::Encoded(error)) = limited else {
            return Err(EncodedValidationError::invariant(
                "ontology identity document limit unexpectedly succeeded",
            ));
        };
        assert_eq!(error.code, "NATIVE_ENCODED_RESOURCE_LIMIT");

        let ownership_limited = apply_ontology_identity_context_controlled(
            phase.clone(),
            &identifiers,
            false,
            ProfilePhaseLimits {
                max_owned_bytes: phase.owned_bytes,
                ..ProfilePhaseLimits::default()
            },
            &mut |_phase| Ok::<(), Infallible>(()),
        );
        let Err(ProfilePhaseError::Encoded(error)) = ownership_limited else {
            return Err(EncodedValidationError::invariant(
                "ontology identity ownership limit unexpectedly succeeded",
            ));
        };
        assert_eq!(error.code, "NATIVE_ENCODED_RESOURCE_LIMIT");

        let noncanonical = apply_ontology_identity_context_controlled(
            phase,
            &[identifiers[1].clone(), identifiers[0].clone()],
            false,
            ProfilePhaseLimits::default(),
            &mut |_phase| Ok::<(), Infallible>(()),
        );
        let Err(ProfilePhaseError::Encoded(error)) = noncanonical else {
            return Err(EncodedValidationError::invariant(
                "noncanonical ontology identity context unexpectedly succeeded",
            ));
        };
        assert_eq!(error.code, "NATIVE_ENCODED_VIEW_INVALID");
        Ok(())
    }

    #[test]
    fn top_data_property_position_is_exact_and_preserves_the_valid_super_position(
    ) -> EncodedResult<()> {
        let invalid = invalid_top_data_property_columns();
        let phase = compile_profile_phase(&model(&invalid)?, &[], ProfilePhaseLimits::default())?;
        assert!(!phase.conforms);
        assert_eq!(phase.axioms_checked, 1);
        assert_eq!(phase.issues.len(), 1);
        assert_eq!(phase.issues[0].rule_id, TOP_DATA_PROPERTY_RULE);
        assert_eq!(phase.issues[0].constructor, Some("FunctionalDataProperty"));
        assert_eq!(
            phase.issues[0]
                .provenance_sha256
                .map(|value| crate::model::hex(&value))
                .as_deref(),
            Some("721e62a719bbd8248bd2494e9eb90cc60408328ad18fb008d082902082eb6a4d")
        );

        let allowed = allowed_top_data_property_columns();
        let allowed_phase =
            compile_profile_phase(&model(&allowed)?, &[], ProfilePhaseLimits::default())?;
        assert!(!allowed_phase.conforms);
        assert_eq!(allowed_phase.axioms_checked, 1);
        assert_eq!(allowed_phase.issues.len(), 1);
        assert_eq!(allowed_phase.issues[0].rule_id, MISSING_DECLARATION_RULE);
        Ok(())
    }

    #[test]
    fn anonymous_axiom_position_is_exact_and_scope_sensitive() -> EncodedResult<()> {
        let columns = anonymous_forbidden_columns();
        let model = model(&columns)?;
        let phase = compile_profile_phase(&model, &[], ProfilePhaseLimits::default())?;
        assert!(!phase.conforms);
        assert_eq!(phase.axioms_checked, 1);
        assert_eq!(phase.issues.len(), 1);
        assert_eq!(phase.issues[0].rule_id, ANONYMOUS_AXIOM_POSITION_RULE);
        assert_eq!(phase.issues[0].constructor, Some("DifferentIndividuals"));

        let scope_maps = vec![vec![canonical::AnonymousScopeReplacement {
            source: [0x11; 32],
            target: [0x33; 32],
        }]];
        let mapped = compile_profile_phase(&model, &scope_maps, ProfilePhaseLimits::default())?;
        assert_eq!(mapped.issues.len(), 1);
        assert_ne!(
            mapped.issues[0].provenance_sha256,
            phase.issues[0].provenance_sha256
        );
        Ok(())
    }

    #[test]
    fn anonymous_graph_rules_use_global_canonical_assertion_order() -> EncodedResult<()> {
        let vertex = |value| vec![value; 64];
        let assertion = |order: u8, provenance: u8, source: Option<u8>, target: Option<u8>| {
            AnonymousAssertion {
                axiom_key: vec![order],
                provenance_sha256: [provenance; 32],
                source: source.map(vertex),
                target: target.map(vertex),
            }
        };
        let vertices = vec![
            vertex(1),
            vertex(2),
            vertex(3),
            vertex(4),
            vertex(5),
            vertex(6),
        ];
        let assertions = vec![
            assertion(1, 1, Some(1), Some(2)),
            assertion(2, 2, Some(2), Some(3)),
            assertion(3, 3, Some(3), Some(1)),
            assertion(4, 4, Some(4), Some(5)),
            assertion(5, 5, Some(5), Some(4)),
            assertion(6, 6, Some(6), None),
            assertion(7, 7, None, Some(6)),
        ];
        let mut issues = Vec::new();
        let mut budget = PhaseBudget::new(ProfilePhaseLimits::default());
        let mut control = |_phase| Ok::<(), Infallible>(());

        into_encoded(append_anonymous_graph_issues(
            &vertices,
            &assertions,
            &mut issues,
            &mut budget,
            &mut control,
        ))?;
        issues.sort();

        assert_eq!(issues.len(), 4);
        assert_eq!(
            issues
                .iter()
                .filter(|issue| issue.rule_id == ANONYMOUS_GRAPH_CYCLE_RULE)
                .filter_map(|issue| issue.provenance_sha256.map(|value| value[0]))
                .collect::<Vec<_>>(),
            vec![3, 5]
        );
        assert_eq!(
            issues
                .iter()
                .find(|issue| issue.rule_id == ANONYMOUS_PARALLEL_EDGE_RULE)
                .and_then(|issue| issue.provenance_sha256.map(|value| value[0])),
            Some(4)
        );
        assert_eq!(
            issues
                .iter()
                .find(|issue| issue.rule_id == ANONYMOUS_TREE_ROOT_RULE)
                .and_then(|issue| issue.provenance_sha256.map(|value| value[0])),
            Some(6)
        );

        let mut cancelled_issues = Vec::new();
        let mut cancelled_budget = PhaseBudget::new(ProfilePhaseLimits::default());
        let cancelled = append_anonymous_graph_issues(
            &vertices,
            &assertions,
            &mut cancelled_issues,
            &mut cancelled_budget,
            &mut |phase| {
                if phase == "profile-anonymous-assertion" {
                    Err("injected graph cancellation")
                } else {
                    Ok(())
                }
            },
        );
        assert_eq!(
            cancelled,
            Err(ProfilePhaseError::Control("injected graph cancellation"))
        );
        assert!(cancelled_issues.is_empty());

        let mut limited_issues = Vec::new();
        let mut limited_budget = PhaseBudget::new(ProfilePhaseLimits {
            max_issues: 0,
            ..ProfilePhaseLimits::default()
        });
        let limited = append_anonymous_graph_issues(
            &vertices,
            &assertions,
            &mut limited_issues,
            &mut limited_budget,
            &mut control,
        );
        let Err(ProfilePhaseError::Encoded(error)) = limited else {
            return Err(EncodedValidationError::invariant(
                "anonymous graph issue limit unexpectedly succeeded",
            ));
        };
        assert_eq!(error.code, "NATIVE_ENCODED_RESOURCE_LIMIT");
        assert!(limited_issues.is_empty());
        Ok(())
    }

    #[test]
    fn global_entity_rules_use_merged_kind_and_declaration_facts() -> EncodedResult<()> {
        let identity = |iri: &str, kind| ProfileEntityIdentity {
            iri: iri.as_bytes().to_vec(),
            kind,
        };
        let mut uses = vec![
            identity(
                "http://www.w3.org/1999/02/22-rdf-syntax-ns#custom",
                ProfileEntityKind::Class,
            ),
            identity(
                "http://www.w3.org/2002/07/owl#real",
                ProfileEntityKind::Class,
            ),
            identity("urn:annotation", ProfileEntityKind::AnnotationProperty),
            identity("urn:dual", ProfileEntityKind::Class),
            identity("urn:dual", ProfileEntityKind::Datatype),
            identity("urn:missing", ProfileEntityKind::Class),
            identity("urn:named", ProfileEntityKind::NamedIndividual),
            identity("urn:shared", ProfileEntityKind::DataProperty),
            identity("urn:shared", ProfileEntityKind::ObjectProperty),
        ];
        uses.sort();
        let mut declarations = vec![
            uses[0].clone(),
            uses[1].clone(),
            identity("urn:dual", ProfileEntityKind::Class),
            identity("urn:dual", ProfileEntityKind::Datatype),
            identity("urn:shared", ProfileEntityKind::DataProperty),
            identity("urn:shared", ProfileEntityKind::ObjectProperty),
        ];
        declarations.sort();
        let mut issues = Vec::new();
        let mut budget = PhaseBudget::new(ProfilePhaseLimits::default());
        let mut control = |_phase| Ok::<(), Infallible>(());

        into_encoded(append_entity_issues(
            &uses,
            &declarations,
            &mut issues,
            &mut budget,
            &mut control,
        ))?;
        issues.sort();

        assert_eq!(issues.len(), 6);
        assert_eq!(
            issues
                .iter()
                .filter(|issue| issue.rule_id == MISSING_DECLARATION_RULE)
                .count(),
            2
        );
        assert_eq!(
            issues
                .iter()
                .map(|issue| issue.rule_id)
                .collect::<std::collections::BTreeSet<_>>(),
            std::collections::BTreeSet::from([
                BUILTIN_ENTITY_KIND_RULE,
                CLASS_DATATYPE_PUNNING_RULE,
                MISSING_DECLARATION_RULE,
                PROPERTY_PUNNING_RULE,
                RESERVED_VOCABULARY_RULE,
            ])
        );
        assert!(issues
            .iter()
            .all(|issue| issue.constructor.is_none() && issue.provenance_sha256.is_none()));

        let mut cancelled_issues = Vec::new();
        let mut cancelled_budget = PhaseBudget::new(ProfilePhaseLimits::default());
        let cancelled = append_entity_issues(
            &uses,
            &declarations,
            &mut cancelled_issues,
            &mut cancelled_budget,
            &mut |phase| {
                if phase == "profile-entity-iri" {
                    Err("injected entity cancellation")
                } else {
                    Ok(())
                }
            },
        );
        assert_eq!(
            cancelled,
            Err(ProfilePhaseError::Control("injected entity cancellation"))
        );
        assert!(cancelled_issues.is_empty());
        Ok(())
    }

    #[test]
    fn global_datatype_rules_are_bounded_and_cancellable() -> EncodedResult<()> {
        let datatype = |iri: &str| ProfileEntityIdentity {
            iri: iri.as_bytes().to_vec(),
            kind: ProfileEntityKind::Datatype,
        };
        let mut uses = vec![datatype("urn:first"), datatype("urn:second")];
        uses.sort();
        let definitions = vec![
            ProfileDatatypeDefinition {
                statement_order_key: vec![1],
                datatype_iri: b"urn:first".to_vec(),
                references: vec![b"urn:second".to_vec()],
                failure: None,
            },
            ProfileDatatypeDefinition {
                statement_order_key: vec![2],
                datatype_iri: b"urn:second".to_vec(),
                references: vec![b"urn:first".to_vec()],
                failure: None,
            },
        ];
        let literals = vec![ProfileLiteralFact {
            canonical_key: vec![3],
            datatype_iri: b"urn:first".to_vec(),
            failure: Some(ProfileDatatypeFailure::UnsupportedLiteral),
        }];
        let mut issues = Vec::new();
        let mut budget = PhaseBudget::new(ProfilePhaseLimits::default());
        let mut control = |_phase| Ok::<(), Infallible>(());

        into_encoded(append_datatype_issues(
            ProfileDatatypeFacts {
                uses: &uses,
                definitions: &definitions,
                range_failures: &[],
                literals: &literals,
            },
            ProfileUnsupportedDatatypePolicy::Error,
            &mut issues,
            &mut budget,
            &mut control,
        ))?;
        issues.sort();
        issues.dedup();
        assert_eq!(
            issues
                .iter()
                .map(|issue| issue.rule_id)
                .collect::<std::collections::BTreeSet<_>>(),
            std::collections::BTreeSet::from([
                CUSTOM_DATATYPE_LITERAL_RULE,
                RECURSIVE_DATATYPE_DEFINITION_RULE,
            ])
        );

        let range_failures = vec![ProfileDatatypeRangeFailure {
            canonical_key: vec![1],
            failure: ProfileDatatypeFailure::IllegalFacet,
        }];
        let invalid_literals = vec![ProfileLiteralFact {
            canonical_key: vec![2],
            datatype_iri: b"http://www.w3.org/2001/XMLSchema#integer".to_vec(),
            failure: Some(ProfileDatatypeFailure::InvalidLiteral(
                ProfileLiteralInvalid::Lexical,
            )),
        }];
        let mut validation_issues = Vec::new();
        into_encoded(append_datatype_issues(
            ProfileDatatypeFacts {
                uses: &[],
                definitions: &[],
                range_failures: &range_failures,
                literals: &invalid_literals,
            },
            ProfileUnsupportedDatatypePolicy::Error,
            &mut validation_issues,
            &mut PhaseBudget::new(ProfilePhaseLimits::default()),
            &mut control,
        ))?;
        validation_issues.sort();
        validation_issues.dedup();
        assert_eq!(
            validation_issues
                .iter()
                .map(|issue| (issue.rule_id, issue.constructor))
                .collect::<std::collections::BTreeSet<_>>(),
            std::collections::BTreeSet::from([
                (ILLEGAL_DATATYPE_FACET_RULE, Some("DataRange")),
                (INVALID_LITERAL_RULE, Some("Literal")),
            ])
        );

        let opaque_uses = vec![datatype("urn:opaque")];
        let opaque_literals = vec![ProfileLiteralFact {
            canonical_key: vec![4],
            datatype_iri: b"urn:opaque".to_vec(),
            failure: Some(ProfileDatatypeFailure::UnsupportedLiteral),
        }];
        let mut opaque_issues = Vec::new();
        into_encoded(append_datatype_issues(
            ProfileDatatypeFacts {
                uses: &opaque_uses,
                definitions: &[],
                range_failures: &[],
                literals: &opaque_literals,
            },
            ProfileUnsupportedDatatypePolicy::IgnoreWithWarning,
            &mut opaque_issues,
            &mut PhaseBudget::new(ProfilePhaseLimits::default()),
            &mut control,
        ))?;
        assert_eq!(
            opaque_issues,
            vec![ProfileIssue {
                rule_id: UNSUPPORTED_DATATYPE_OPAQUE_RULE,
                severity: "warning",
                message: Cow::Owned(
                    "unsupported datatype is treated as opaque: urn:opaque".to_owned()
                ),
                constructor: Some("Datatype"),
                document_keys: Vec::new(),
                provenance_sha256: None,
            }]
        );
        assert!(profile_issues_conform(&opaque_issues));

        let opaque_definition = vec![ProfileDatatypeDefinition {
            statement_order_key: vec![5],
            datatype_iri: b"urn:defined".to_vec(),
            references: vec![b"urn:opaque".to_vec()],
            failure: None,
        }];
        let mut opaque_definition_issues = Vec::new();
        into_encoded(append_datatype_issues(
            ProfileDatatypeFacts {
                uses: &opaque_uses,
                definitions: &opaque_definition,
                range_failures: &[],
                literals: &[],
            },
            ProfileUnsupportedDatatypePolicy::IgnoreWithWarning,
            &mut opaque_definition_issues,
            &mut PhaseBudget::new(ProfilePhaseLimits::default()),
            &mut control,
        ))?;
        assert!(opaque_definition_issues
            .iter()
            .any(|issue| issue.rule_id == UNSUPPORTED_DATATYPE_RULE));

        let opaque_cancelled = append_datatype_issues(
            ProfileDatatypeFacts {
                uses: &opaque_uses,
                definitions: &[],
                range_failures: &[],
                literals: &opaque_literals,
            },
            ProfileUnsupportedDatatypePolicy::IgnoreWithWarning,
            &mut Vec::new(),
            &mut PhaseBudget::new(ProfilePhaseLimits::default()),
            &mut |phase| {
                if phase == "profile-datatype-opaque-warning" {
                    Err("injected opaque warning cancellation")
                } else {
                    Ok(())
                }
            },
        );
        assert_eq!(
            opaque_cancelled,
            Err(ProfilePhaseError::Control(
                "injected opaque warning cancellation"
            ))
        );

        let pattern_cancelled = profile_facet_failure(
            "http://www.w3.org/2001/XMLSchema#string",
            &ProfileFacetValue {
                iri: XSD_PATTERN_IRI.to_owned(),
                semantics: ProfileLiteralSemantics::String {
                    text: "[ab]{2}".to_owned(),
                    tagged: false,
                },
            },
            &mut PhaseBudget::new(ProfilePhaseLimits::default()),
            &mut |phase| {
                if phase == "profile-datatype-pattern-work" {
                    Err("injected datatype pattern cancellation")
                } else {
                    Ok(())
                }
            },
        );
        assert_eq!(
            pattern_cancelled,
            Err(ProfilePhaseError::Control(
                "injected datatype pattern cancellation"
            ))
        );

        let mut cancelled_issues = Vec::new();
        let cancelled = append_datatype_issues(
            ProfileDatatypeFacts {
                uses: &uses,
                definitions: &definitions,
                range_failures: &[],
                literals: &literals,
            },
            ProfileUnsupportedDatatypePolicy::Error,
            &mut cancelled_issues,
            &mut PhaseBudget::new(ProfilePhaseLimits::default()),
            &mut |phase| {
                if phase == "profile-datatype-preflight" {
                    Err("injected datatype cancellation")
                } else {
                    Ok(())
                }
            },
        );
        assert_eq!(
            cancelled,
            Err(ProfilePhaseError::Control("injected datatype cancellation"))
        );
        assert!(cancelled_issues.is_empty());

        let limited = append_datatype_issues(
            ProfileDatatypeFacts {
                uses: &uses,
                definitions: &definitions,
                range_failures: &[],
                literals: &literals,
            },
            ProfileUnsupportedDatatypePolicy::Error,
            &mut Vec::new(),
            &mut PhaseBudget::new(ProfilePhaseLimits {
                max_owned_bytes: 0,
                ..ProfilePhaseLimits::default()
            }),
            &mut control,
        );
        let Err(ProfilePhaseError::Encoded(error)) = limited else {
            return Err(EncodedValidationError::invariant(
                "datatype ownership limit unexpectedly succeeded",
            ));
        };
        assert_eq!(error.code, "NATIVE_ENCODED_RESOURCE_LIMIT");
        let mut fact_budget = PhaseBudget::new(ProfilePhaseLimits {
            max_datatype_definitions: 0,
            max_datatype_references: 0,
            max_datatype_failures: 0,
            max_literal_datatypes: 0,
            ..ProfilePhaseLimits::default()
        });
        assert_eq!(
            fact_budget
                .claim_datatype_definition(1)
                .map_err(|error| error.code),
            Err("NATIVE_ENCODED_RESOURCE_LIMIT")
        );
        assert_eq!(
            fact_budget
                .claim_datatype_reference(1)
                .map_err(|error| error.code),
            Err("NATIVE_ENCODED_RESOURCE_LIMIT")
        );
        assert_eq!(
            fact_budget
                .claim_datatype_failure(1)
                .map_err(|error| error.code),
            Err("NATIVE_ENCODED_RESOURCE_LIMIT")
        );
        assert_eq!(
            fact_budget
                .claim_literal_datatype(1)
                .map_err(|error| error.code),
            Err("NATIVE_ENCODED_RESOURCE_LIMIT")
        );
        Ok(())
    }

    #[test]
    fn non_simple_role_closure_is_global_bounded_and_cancellable() -> EncodedResult<()> {
        let role = |iri: &str, inverse: bool| ProfileObjectRole {
            iri: iri.as_bytes().to_vec(),
            inverse,
        };
        let inclusions = vec![
            ProfileRoleInclusion {
                sub_role: role("urn:chain", false),
                super_role: role("urn:super", false),
            },
            ProfileRoleInclusion {
                sub_role: role("urn:chain", true),
                super_role: role("urn:super", true),
            },
        ];
        let seeds = vec![role("urn:chain", false), role("urn:chain", true)];
        let requirements = vec![
            ProfileSimpleRoleRequirement {
                role: role("urn:simple", false),
                constructor: "FunctionalObjectProperty",
                provenance_sha256: [1; 32],
            },
            ProfileSimpleRoleRequirement {
                role: role("urn:super", false),
                constructor: "FunctionalObjectProperty",
                provenance_sha256: [2; 32],
            },
            ProfileSimpleRoleRequirement {
                role: role("urn:super", true),
                constructor: "SubClassOf",
                provenance_sha256: [3; 32],
            },
            ProfileSimpleRoleRequirement {
                role: role(
                    std::str::from_utf8(TOP_OBJECT_PROPERTY_IRI).map_err(|_| {
                        EncodedValidationError::invariant("builtin role IRI is not UTF-8")
                    })?,
                    false,
                ),
                constructor: "ObjectHasSelf",
                provenance_sha256: [4; 32],
            },
        ];
        let mut issues = Vec::new();
        let mut budget = PhaseBudget::new(ProfilePhaseLimits::default());
        let mut control = |_phase| Ok::<(), Infallible>(());

        into_encoded(append_non_simple_role_issues(
            &inclusions,
            &seeds,
            &requirements,
            &mut issues,
            &mut budget,
            &mut control,
        ))?;
        issues.sort();

        assert_eq!(issues.len(), 3);
        let mut provenance = issues
            .iter()
            .filter_map(|issue| issue.provenance_sha256.map(|value| value[0]))
            .collect::<Vec<_>>();
        provenance.sort_unstable();
        assert_eq!(provenance, vec![2, 3, 4]);
        assert!(issues
            .iter()
            .all(|issue| issue.rule_id == NON_SIMPLE_PROPERTY_RULE));

        let mut cancelled_issues = Vec::new();
        let mut cancelled_budget = PhaseBudget::new(ProfilePhaseLimits::default());
        let cancelled = append_non_simple_role_issues(
            &inclusions,
            &seeds,
            &requirements,
            &mut cancelled_issues,
            &mut cancelled_budget,
            &mut |phase| {
                if phase == "profile-role-preflight" {
                    Err("injected role cancellation")
                } else {
                    Ok(())
                }
            },
        );
        assert_eq!(
            cancelled,
            Err(ProfilePhaseError::Control("injected role cancellation"))
        );
        assert!(cancelled_issues.is_empty());

        let mut limited_issues = Vec::new();
        let mut limited_budget = PhaseBudget::new(ProfilePhaseLimits {
            max_issues: 0,
            ..ProfilePhaseLimits::default()
        });
        let limited = append_non_simple_role_issues(
            &inclusions,
            &seeds,
            &requirements,
            &mut limited_issues,
            &mut limited_budget,
            &mut control,
        );
        let Err(ProfilePhaseError::Encoded(error)) = limited else {
            return Err(EncodedValidationError::invariant(
                "non-simple role issue limit unexpectedly succeeded",
            ));
        };
        assert_eq!(error.code, "NATIVE_ENCODED_RESOURCE_LIMIT");
        assert!(limited_issues.is_empty());

        let mut fact_budget = PhaseBudget::new(ProfilePhaseLimits {
            max_role_inclusions: 0,
            max_non_simple_role_seeds: 0,
            max_simple_role_requirements: 0,
            ..ProfilePhaseLimits::default()
        });
        assert_eq!(
            push_profile_role_inclusion(&mut Vec::new(), inclusions[0].clone(), &mut fact_budget,)
                .map_err(|error| error.code),
            Err("NATIVE_ENCODED_RESOURCE_LIMIT")
        );
        assert_eq!(
            push_non_simple_role_seed(&mut Vec::new(), seeds[0].clone(), &mut fact_budget,)
                .map_err(|error| error.code),
            Err("NATIVE_ENCODED_RESOURCE_LIMIT")
        );
        assert_eq!(
            push_simple_role_requirement(
                &mut Vec::new(),
                requirements[0].role.clone(),
                requirements[0].constructor,
                requirements[0].provenance_sha256,
                &mut fact_budget,
            )
            .map_err(|error| error.code),
            Err("NATIVE_ENCODED_RESOURCE_LIMIT")
        );
        Ok(())
    }

    #[test]
    fn role_regularity_is_exact_bounded_and_cancellable() -> EncodedResult<()> {
        let role = |iri: &str, inverse: bool| ProfileObjectRole {
            iri: iri.as_bytes().to_vec(),
            inverse,
        };
        let mut facts = Vec::new();
        let mut fact_budget = PhaseBudget::new(ProfilePhaseLimits::default());
        add_profile_complex_role_inclusion_pair(
            &mut facts,
            vec![role("urn:b", false), role("urn:g", false)],
            role("urn:a", false),
            b"cycle-a",
            [1; 32],
            &mut fact_budget,
        )?;
        add_profile_complex_role_inclusion_pair(
            &mut facts,
            vec![role("urn:a", false), role("urn:g", false)],
            role("urn:b", false),
            b"cycle-b",
            [2; 32],
            &mut fact_budget,
        )?;
        add_profile_complex_role_inclusion_pair(
            &mut facts,
            vec![
                role("urn:c", false),
                role("urn:a", false),
                role("urn:d", false),
            ],
            role("urn:a", false),
            b"non-regular",
            [3; 32],
            &mut fact_budget,
        )?;
        add_profile_complex_role_inclusion_pair(
            &mut facts,
            vec![role("urn:a", true), role("urn:g", false)],
            role("urn:a", false),
            b"inverse",
            [4; 32],
            &mut fact_budget,
        )?;
        canonicalize_profile_complex_role_inclusions(&mut facts, &mut fact_budget)?;

        let mut issues = Vec::new();
        let mut budget = PhaseBudget::new(ProfilePhaseLimits::default());
        let mut control = |_phase| Ok::<(), Infallible>(());
        into_encoded(append_role_regularity_issues(
            &[],
            &facts,
            &mut issues,
            &mut budget,
            &mut control,
        ))?;
        issues.sort();
        issues.dedup();
        assert_eq!(
            issues
                .iter()
                .map(|issue| issue.rule_id)
                .collect::<std::collections::BTreeSet<_>>(),
            std::collections::BTreeSet::from([
                RIA_DEPENDENCY_CYCLE_RULE,
                RIA_INVERSE_RECURSION_RULE,
                RIA_NON_REGULAR_RECURSION_RULE,
            ])
        );
        assert!(issues
            .iter()
            .all(|issue| issue.constructor == Some("SubObjectPropertyOf")));

        let mut cancelled_issues = Vec::new();
        let cancelled = append_role_regularity_issues(
            &[],
            &facts,
            &mut cancelled_issues,
            &mut PhaseBudget::new(ProfilePhaseLimits::default()),
            &mut |phase| {
                if phase == "profile-regularity-preflight" {
                    Err("injected regularity cancellation")
                } else {
                    Ok(())
                }
            },
        );
        assert_eq!(
            cancelled,
            Err(ProfilePhaseError::Control(
                "injected regularity cancellation"
            ))
        );
        assert!(cancelled_issues.is_empty());

        let limited = append_role_regularity_issues(
            &[],
            &facts,
            &mut Vec::new(),
            &mut PhaseBudget::new(ProfilePhaseLimits {
                max_role_dependency_edges: 0,
                ..ProfilePhaseLimits::default()
            }),
            &mut control,
        );
        let Err(ProfilePhaseError::Encoded(error)) = limited else {
            return Err(EncodedValidationError::invariant(
                "regularity dependency limit unexpectedly succeeded",
            ));
        };
        assert_eq!(error.code, "NATIVE_ENCODED_RESOURCE_LIMIT");

        let mut limited_facts = Vec::new();
        let limited_fact = add_profile_complex_role_inclusion_pair(
            &mut limited_facts,
            vec![role("urn:a", false), role("urn:b", false)],
            role("urn:c", false),
            b"limited",
            [5; 32],
            &mut PhaseBudget::new(ProfilePhaseLimits {
                max_complex_role_inclusions: 0,
                ..ProfilePhaseLimits::default()
            }),
        );
        assert_eq!(
            limited_fact.map_err(|error| error.code),
            Err("NATIVE_ENCODED_RESOURCE_LIMIT")
        );
        assert!(limited_facts.is_empty());

        let key = profile_role_canonical_key(
            &role("u:z", false),
            &mut PhaseBudget::new(ProfilePhaseLimits::default()),
        )?;
        assert_eq!(
            crate::model::hex(&key),
            "02050f6f626a6563745f70726f70657274790106010203753a7a"
        );
        Ok(())
    }

    #[test]
    fn extension_issue_provenance_and_count_are_exact() -> EncodedResult<()> {
        let columns = extension_columns();
        let phase = compile_profile_phase(&model(&columns)?, &[], ProfilePhaseLimits::default())?;
        assert!(!phase.conforms);
        assert_eq!(phase.axioms_checked, 0);
        assert_eq!(phase.extensions_checked, 1);
        assert_eq!(phase.issues.len(), 1);
        assert_eq!(phase.issues[0].rule_id, EXTENSION_COMPONENT_RULE);
        assert_eq!(phase.issues[0].constructor, Some("SWRLRule"));

        let manifest: serde_json::Value = serde_json::from_slice(&phase.canonical_manifest_json()?)
            .map_err(|_| EncodedValidationError::invariant("profile manifest is not JSON"))?;
        assert_eq!(manifest["extensions_checked"], 1);
        assert_eq!(manifest["ordered_rule_ids"][0], EXTENSION_COMPONENT_RULE);

        let merged =
            merge_profile_phases(vec![phase.clone(), phase], ProfilePhaseLimits::default())?;
        assert_eq!(merged.extensions_checked, 1);
        assert_eq!(merged.issues.len(), 1);

        let limited = ProfilePhaseLimits {
            max_extensions: 0,
            ..ProfilePhaseLimits::default()
        };
        let error = compile_profile_phase(&model(&columns)?, &[], limited)
            .err()
            .ok_or_else(|| {
                EncodedValidationError::invariant("profile extension limit unexpectedly succeeded")
            })?;
        assert_eq!(error.code, "NATIVE_ENCODED_RESOURCE_LIMIT");
        Ok(())
    }

    #[test]
    fn origin_context_bridges_explicit_digest_domains_transactionally() -> EncodedResult<()> {
        let columns = invalid_data_arity_columns();
        let phase = compile_profile_phase(&model(&columns)?, &[], ProfilePhaseLimits::default())?;
        let provenance = phase.issues[0].provenance_sha256.ok_or_else(|| {
            EncodedValidationError::invariant("profile origin fixture lost its provenance")
        })?;
        let origins = vec![ProfileOrigin {
            root_digest_sha256: provenance,
            document_keys: vec!["document:a".to_owned(), "document:b".to_owned()],
        }];
        let applied = into_encoded(apply_origin_context_controlled(
            phase.clone(),
            &origins,
            ProfilePhaseLimits::default(),
            &mut |_phase| Ok::<(), Infallible>(()),
        ))?;
        assert_eq!(
            applied.issues[0].document_keys,
            ["document:a", "document:b"]
        );
        let origin_manifest: serde_json::Value =
            serde_json::from_slice(&applied.canonical_origin_manifest_json()?).map_err(|_| {
                EncodedValidationError::invariant("profile origin manifest is not JSON")
            })?;
        assert_eq!(
            origin_manifest["issues"][0]["document_keys"],
            serde_json::json!(["document:a", "document:b"])
        );
        let projected_manifest: serde_json::Value =
            serde_json::from_slice(&applied.canonical_manifest_json()?).map_err(|_| {
                EncodedValidationError::invariant("projected profile manifest is not JSON")
            })?;
        assert!(projected_manifest["issues"][0]
            .as_object()
            .is_some_and(|issue| !issue.contains_key("document_keys")));

        let canonical_key = phase
            .axiom_keys
            .iter()
            .find(|key| <[u8; 32]>::from(Sha256::digest(key)) == provenance)
            .ok_or_else(|| {
                EncodedValidationError::invariant(
                    "profile origin fixture lost its canonical root key",
                )
            })?;
        let mut structural_hasher = Sha256::new();
        structural_hasher.update(CORE_STRUCTURAL_DIGEST_PREFIX);
        structural_hasher.update(canonical_key);
        let structural: [u8; 32] = structural_hasher.finalize().into();
        assert_eq!(
            crate::model::hex(&provenance),
            "6a1bfbadd77d1f86ac453a99501c3f363d5b71f420e67ade72d564f590a16aa7"
        );
        assert_eq!(
            crate::model::hex(&structural),
            "9954a3e3ad4ca47cfd0e8a589bc39ecc9e7bb317c1d29e24827dfa5031f02d59"
        );
        let structural_origins = vec![ProfileOrigin {
            root_digest_sha256: structural,
            document_keys: vec!["document:a".to_owned(), "document:b".to_owned()],
        }];
        let structurally_applied = into_encoded(apply_origin_context_controlled(
            phase.clone(),
            &structural_origins,
            ProfilePhaseLimits::default(),
            &mut |_phase| Ok::<(), Infallible>(()),
        ))?;
        assert_eq!(
            structurally_applied.issues[0].document_keys,
            ["document:a", "document:b"]
        );

        let mut ambiguous_origins = vec![origins[0].clone(), structural_origins[0].clone()];
        ambiguous_origins.sort_unstable();
        let ambiguous = apply_origin_context_controlled(
            phase.clone(),
            &ambiguous_origins,
            ProfilePhaseLimits::default(),
            &mut |_phase| Ok::<(), Infallible>(()),
        );
        let Err(ProfilePhaseError::Encoded(error)) = ambiguous else {
            return Err(EncodedValidationError::invariant(
                "ambiguous profile origin digest domains unexpectedly succeeded",
            ));
        };
        assert_eq!(error.code, "NATIVE_ENCODED_VIEW_INVALID");

        let cancelled = apply_origin_context_controlled(
            phase.clone(),
            &origins,
            ProfilePhaseLimits::default(),
            &mut |checkpoint| {
                if checkpoint == "profile-origin-issue" {
                    Err("injected origin cancellation")
                } else {
                    Ok(())
                }
            },
        );
        assert_eq!(
            cancelled,
            Err(ProfilePhaseError::Control("injected origin cancellation"))
        );

        let missing = apply_origin_context_controlled(
            phase,
            &[],
            ProfilePhaseLimits::default(),
            &mut |_phase| Ok::<(), Infallible>(()),
        );
        let Err(ProfilePhaseError::Encoded(error)) = missing else {
            return Err(EncodedValidationError::invariant(
                "missing profile origin unexpectedly succeeded",
            ));
        };
        assert_eq!(error.code, "NATIVE_ENCODED_VIEW_INVALID");
        Ok(())
    }

    #[test]
    fn include_exclude_selection_and_merge_are_canonical() -> EncodedResult<()> {
        let columns = invalid_data_arity_columns();
        let model = model(&columns)?;
        let mut control = |_phase| Ok::<(), Infallible>(());
        let included = into_encoded(compile_profile_phase_selected_controlled(
            &model,
            &[],
            ProfilePhaseLimits::default(),
            POSTINGS_INCLUDE,
            4_u32.to_le_bytes().as_slice(),
            &mut control,
        ))?;
        assert_eq!(included.axioms_checked, 1);
        assert_eq!(included.extensions_checked, 0);
        assert_eq!(included.issues.len(), 4);
        assert_eq!(
            included
                .issues
                .iter()
                .filter(|issue| issue.rule_id == DATA_RANGE_ARITY_RULE)
                .count(),
            1
        );
        assert_eq!(
            included
                .issues
                .iter()
                .filter(|issue| issue.rule_id == MISSING_DECLARATION_RULE)
                .count(),
            3
        );
        let excluded = into_encoded(compile_profile_phase_selected_controlled(
            &model,
            &[],
            ProfilePhaseLimits::default(),
            POSTINGS_EXCLUDE,
            4_u32.to_le_bytes().as_slice(),
            &mut control,
        ))?;
        assert_eq!(excluded.axioms_checked, 3);
        assert!(excluded.conforms);

        let left = compile_profile_phase(&model, &[], ProfilePhaseLimits::default())?;
        let right = compile_profile_phase(&model, &[], ProfilePhaseLimits::default())?;
        let merged = merge_profile_phases(
            vec![left.clone(), right.clone()],
            ProfilePhaseLimits::default(),
        )?;
        let reversed = merge_profile_phases(vec![right, left], ProfilePhaseLimits::default())?;
        assert_eq!(
            merged.canonical_manifest_json()?,
            reversed.canonical_manifest_json()?
        );
        assert_eq!(merged.axioms_checked, 4);
        assert_eq!(merged.extensions_checked, 0);
        assert_eq!(merged.issues.len(), 1);
        Ok(())
    }

    #[test]
    fn cancellation_and_resource_failure_leave_retry_available() -> EncodedResult<()> {
        let columns = invalid_data_arity_columns();
        let model = model(&columns)?;
        let mut polls = 0_usize;
        let result = compile_profile_phase_controlled(
            &model,
            &[],
            ProfilePhaseLimits::default(),
            &mut |_phase| {
                polls += 1;
                if polls == 3 {
                    Err("injected cancellation")
                } else {
                    Ok(())
                }
            },
        );
        let Err(error) = result else {
            return Err(EncodedValidationError::invariant(
                "profile cancellation unexpectedly succeeded",
            ));
        };
        assert_eq!(error, ProfilePhaseError::Control("injected cancellation"));

        let limited = ProfilePhaseLimits {
            max_issues: 0,
            ..ProfilePhaseLimits::default()
        };
        let error = compile_profile_phase(&model, &[], limited)
            .err()
            .ok_or_else(|| {
                EncodedValidationError::invariant("profile issue limit unexpectedly succeeded")
            })?;
        assert_eq!(error.code, "NATIVE_ENCODED_RESOURCE_LIMIT");

        let retry = compile_profile_phase(&model, &[], ProfilePhaseLimits::default())?;
        assert_eq!(retry.issues.len(), 1);
        Ok(())
    }

    #[test]
    fn allocation_and_manifest_limits_are_fallible() -> EncodedResult<()> {
        let mut values = Vec::<u8>::new();
        let error = reserve_exact(
            &mut values,
            usize::MAX,
            "injected profile allocation failure",
        )
        .err()
        .ok_or_else(|| {
            EncodedValidationError::invariant(
                "impossible profile allocation unexpectedly succeeded",
            )
        })?;
        assert_eq!(error.code, "NATIVE_ENCODED_RESOURCE_LIMIT");
        assert_eq!(error.message, "injected profile allocation failure");

        let columns = invalid_data_arity_columns();
        let phase = compile_profile_phase(
            &model(&columns)?,
            &[],
            ProfilePhaseLimits {
                max_manifest_bytes: 1,
                ..ProfilePhaseLimits::default()
            },
        )?;
        let error = phase.canonical_manifest_json().err().ok_or_else(|| {
            EncodedValidationError::invariant("profile manifest limit unexpectedly succeeded")
        })?;
        assert_eq!(error.code, "NATIVE_ENCODED_RESOURCE_LIMIT");

        for limited in [
            ProfilePhaseLimits {
                max_entity_uses: 0,
                ..ProfilePhaseLimits::default()
            },
            ProfilePhaseLimits {
                max_entity_declarations: 0,
                ..ProfilePhaseLimits::default()
            },
        ] {
            let error = compile_profile_phase(&model(&columns)?, &[], limited)
                .err()
                .ok_or_else(|| {
                    EncodedValidationError::invariant(
                        "profile entity fact limit unexpectedly succeeded",
                    )
                })?;
            assert_eq!(error.code, "NATIVE_ENCODED_RESOURCE_LIMIT");
        }
        Ok(())
    }
}
