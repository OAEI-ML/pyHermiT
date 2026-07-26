//! Transactional assembly of owned encoded compiler phases.
//!
//! The structural phases deliberately publish fragment-local predicate, clause,
//! and provenance identifiers.  This module is the one place that joins those
//! fragments into the dense namespace accepted by the native input model.  It
//! remains private compiler substrate: incomplete semantic sections fail closed
//! and no session or advertised capability is created here.
// SPDX-License-Identifier: LGPL-3.0-or-later

#![forbid(unsafe_code)]

use std::cmp::Ordering;
use std::io::Write as _;
use std::mem::size_of;

use serde::Serialize;
use sha2::{Digest, Sha256};

use super::complex_roles::ComplexRolePhase;
use super::data_inclusions::DataInclusionPhase;
use super::data_role_hierarchy::DataRoleHierarchyPhase;
use super::data_roles::DataRolePhase;
use super::named_classes::{
    NamedClassPhase, NamedProgramParts, ProgramSemanticEvidence, SourceLiteralSemanticSeed,
};
use super::object_role_hierarchy::ObjectRoleHierarchyPhase;
use super::object_roles::ObjectRolePhase;
use super::role_automata::RoleAutomataPhase;
use super::role_characteristics::RoleCharacteristicPhase;
use super::role_clauses::RoleClausePhase;
use super::role_model::RoleModelPhase;
use super::role_semantics::RoleSemanticsPhase;
use super::simple_roles::SimpleRolePhase;
use super::{EncodedResult, EncodedValidationError};
use crate::input_wire::{
    validate_decoded_program, validate_decoded_session_domains, DecodedAtom, DecodedClause,
    DecodedDatatypeModel, DecodedEntity, DecodedExpressivity, DecodedGroundAtom,
    DecodedLiteralIdentity, DecodedPredicate, DecodedProgram, DecodedProvenanceEntry,
    DecodedSymbolDomain, DecodedTerm, PredicateKind, SymbolKind, TermSort,
};

const PERMANENT_PROGRAM_SCHEMA_VERSION: u16 = 1;
const DATA_INTERSECTION_OF_TAG: u64 = 21;
const DATA_UNION_OF_TAG: u64 = 22;
const DATA_COMPLEMENT_OF_TAG: u64 = 23;
const DATA_ONE_OF_TAG: u64 = 24;
const DATATYPE_RESTRICTION_TAG: u64 = 25;
const FACET_RESTRICTION_TAG: u64 = 20;
const IRI_TAG: u64 = 1;
const CANONICAL_NODE_COMPONENT: u8 = 1;
const CANONICAL_TEXT_COMPONENT: u8 = 2;
const CANONICAL_COLLECTION_COMPONENT: u8 = 6;
const DATA_IDENTITY_PREFIX: &[u8] = b"pyhermit:data-identity:v1\0";
const RDFS_LITERAL_DISPLAY: &str = "datatype:http://www.w3.org/2000/01/rdf-schema#Literal";
const XSD_STRING_IRI: &str = "http://www.w3.org/2001/XMLSchema#string";
const XSD_BOOLEAN_IRI: &str = "http://www.w3.org/2001/XMLSchema#boolean";
const XSD_FLOAT_IRI: &str = "http://www.w3.org/2001/XMLSchema#float";
const XSD_DOUBLE_IRI: &str = "http://www.w3.org/2001/XMLSchema#double";
const XSD_NAMESPACE: &str = "http://www.w3.org/2001/XMLSchema#";
const OWL_RATIONAL_IRI: &str = "http://www.w3.org/2002/07/owl#rational";
const RDF_PLAIN_LITERAL_IRI: &str = "http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral";
const RDF_XML_LITERAL_IRI: &str = "http://www.w3.org/1999/02/22-rdf-syntax-ns#XMLLiteral";
const BUILTIN_PROVENANCE_INPUT: &[u8] = b"pyhermit:clausification:builtins:v1";
const SUPPORTED_FACET_IRIS: [&str; 9] = [
    "http://www.w3.org/2001/XMLSchema#length",
    "http://www.w3.org/2001/XMLSchema#maxExclusive",
    "http://www.w3.org/2001/XMLSchema#maxInclusive",
    "http://www.w3.org/2001/XMLSchema#maxLength",
    "http://www.w3.org/2001/XMLSchema#minExclusive",
    "http://www.w3.org/2001/XMLSchema#minInclusive",
    "http://www.w3.org/2001/XMLSchema#minLength",
    "http://www.w3.org/2001/XMLSchema#pattern",
    "http://www.w3.org/1999/02/22-rdf-syntax-ns#langRange",
];

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum RepresentableLiteralSemantics {
    None,
    Supported,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct RepresentableDatatypeSemantics {
    literals: RepresentableLiteralSemantics,
}

#[derive(Debug, Eq, PartialEq)]
struct DatatypeRestrictionKey<'a> {
    datatype_key: &'a [u8],
    facets: Vec<FacetRestrictionKey<'a>>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct FacetRestrictionKey<'a> {
    facet_iri: &'a str,
    literal_key: &'a [u8],
}

#[derive(Serialize)]
struct LiteralSemanticPayload<'a> {
    comparison: &'a serde_json::Value,
    compatibility: &'static str,
    data_identity: &'a serde_json::Value,
    datatype_iri: &'a str,
    language: Option<&'a str>,
    lexical_form: &'a str,
    record: &'static str,
    schema_version: u16,
}

#[derive(Clone, Copy)]
enum LiteralLanguageRule {
    Forbidden,
    Identity,
}

#[derive(Clone, Copy)]
struct LiteralIdentityRule {
    datatype_iri: &'static str,
    identity_tag: &'static str,
    arity: usize,
    discriminator: Option<(usize, &'static str)>,
    language: LiteralLanguageRule,
}

const LITERAL_IDENTITY_RULES: &[LiteralIdentityRule] = &[
    LiteralIdentityRule {
        datatype_iri: XSD_STRING_IRI,
        identity_tag: "plain-string-v1",
        arity: 3,
        discriminator: None,
        language: LiteralLanguageRule::Forbidden,
    },
    LiteralIdentityRule {
        datatype_iri: "http://www.w3.org/2001/XMLSchema#normalizedString",
        identity_tag: "plain-string-v1",
        arity: 3,
        discriminator: None,
        language: LiteralLanguageRule::Forbidden,
    },
    LiteralIdentityRule {
        datatype_iri: "http://www.w3.org/2001/XMLSchema#token",
        identity_tag: "plain-string-v1",
        arity: 3,
        discriminator: None,
        language: LiteralLanguageRule::Forbidden,
    },
    LiteralIdentityRule {
        datatype_iri: "http://www.w3.org/2001/XMLSchema#language",
        identity_tag: "plain-string-v1",
        arity: 3,
        discriminator: None,
        language: LiteralLanguageRule::Forbidden,
    },
    LiteralIdentityRule {
        datatype_iri: "http://www.w3.org/2001/XMLSchema#Name",
        identity_tag: "plain-string-v1",
        arity: 3,
        discriminator: None,
        language: LiteralLanguageRule::Forbidden,
    },
    LiteralIdentityRule {
        datatype_iri: "http://www.w3.org/2001/XMLSchema#NCName",
        identity_tag: "plain-string-v1",
        arity: 3,
        discriminator: None,
        language: LiteralLanguageRule::Forbidden,
    },
    LiteralIdentityRule {
        datatype_iri: "http://www.w3.org/2001/XMLSchema#NMTOKEN",
        identity_tag: "plain-string-v1",
        arity: 3,
        discriminator: None,
        language: LiteralLanguageRule::Forbidden,
    },
    LiteralIdentityRule {
        datatype_iri: RDF_PLAIN_LITERAL_IRI,
        identity_tag: "plain-string-v1",
        arity: 3,
        discriminator: None,
        language: LiteralLanguageRule::Identity,
    },
    LiteralIdentityRule {
        datatype_iri: XSD_BOOLEAN_IRI,
        identity_tag: "boolean",
        arity: 2,
        discriminator: None,
        language: LiteralLanguageRule::Forbidden,
    },
    LiteralIdentityRule {
        datatype_iri: XSD_FLOAT_IRI,
        identity_tag: "ieee-identity-v1",
        arity: 3,
        discriminator: Some((1, "float32")),
        language: LiteralLanguageRule::Forbidden,
    },
    LiteralIdentityRule {
        datatype_iri: XSD_DOUBLE_IRI,
        identity_tag: "ieee-identity-v1",
        arity: 3,
        discriminator: Some((1, "float64")),
        language: LiteralLanguageRule::Forbidden,
    },
    LiteralIdentityRule {
        datatype_iri: "http://www.w3.org/2001/XMLSchema#hexBinary",
        identity_tag: "binary-identity-v1",
        arity: 3,
        discriminator: Some((1, "hexBinary")),
        language: LiteralLanguageRule::Forbidden,
    },
    LiteralIdentityRule {
        datatype_iri: "http://www.w3.org/2001/XMLSchema#base64Binary",
        identity_tag: "binary-identity-v1",
        arity: 3,
        discriminator: Some((1, "base64Binary")),
        language: LiteralLanguageRule::Forbidden,
    },
    LiteralIdentityRule {
        datatype_iri: "http://www.w3.org/2001/XMLSchema#anyURI",
        identity_tag: "any-uri-v1",
        arity: 2,
        discriminator: None,
        language: LiteralLanguageRule::Forbidden,
    },
    LiteralIdentityRule {
        datatype_iri: RDF_XML_LITERAL_IRI,
        identity_tag: "xml-literal-c14n-v1",
        arity: 2,
        discriminator: None,
        language: LiteralLanguageRule::Forbidden,
    },
    LiteralIdentityRule {
        datatype_iri: "http://www.w3.org/2001/XMLSchema#dateTime",
        identity_tag: "date-time-identity-v1",
        arity: 5,
        discriminator: None,
        language: LiteralLanguageRule::Forbidden,
    },
    LiteralIdentityRule {
        datatype_iri: "http://www.w3.org/2001/XMLSchema#dateTimeStamp",
        identity_tag: "date-time-identity-v1",
        arity: 5,
        discriminator: None,
        language: LiteralLanguageRule::Forbidden,
    },
];

/// Complete set of already-owned phases produced by the coarse structural call.
pub(crate) struct EncodedSliceProgram {
    pub(crate) named_classes: NamedClassPhase,
    pub(crate) object_roles: ObjectRolePhase,
    pub(crate) data_roles: DataRolePhase,
    pub(crate) data_inclusions: DataInclusionPhase,
    pub(crate) data_role_hierarchy: DataRoleHierarchyPhase,
    pub(crate) simple_roles: SimpleRolePhase,
    pub(crate) complex_roles: ComplexRolePhase,
    pub(crate) role_characteristics: RoleCharacteristicPhase,
    pub(crate) object_role_hierarchy: ObjectRoleHierarchyPhase,
    pub(crate) role_semantics: RoleSemanticsPhase,
    pub(crate) role_automata: RoleAutomataPhase,
    pub(crate) role_model: RoleModelPhase,
    pub(crate) role_clauses: RoleClausePhase,
}

#[allow(clippy::struct_field_names)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct PermanentProgramLimits {
    pub max_predicates: usize,
    pub max_clauses: usize,
    pub max_facts: usize,
    pub max_provenance: usize,
    pub max_owned_bytes: usize,
    pub max_work: u64,
    pub max_manifest_bytes: usize,
}

impl Default for PermanentProgramLimits {
    fn default() -> Self {
        Self {
            max_predicates: 100_000_000,
            max_clauses: 100_000_000,
            max_facts: 100_000_000,
            max_provenance: 100_000_000,
            max_owned_bytes: 512 * 1024 * 1024,
            max_work: 2_000_000_000,
            max_manifest_bytes: 512 * 1024 * 1024,
        }
    }
}

#[derive(Debug, Eq, PartialEq)]
pub(crate) enum PermanentProgramError<E> {
    Encoded(EncodedValidationError),
    Control(E),
}

impl<E> From<EncodedValidationError> for PermanentProgramError<E> {
    fn from(error: EncodedValidationError) -> Self {
        Self::Encoded(error)
    }
}

type ControlledResult<T, E> = Result<T, PermanentProgramError<E>>;

/// One fully owned, validator-approved permanent-program candidate.
pub(crate) struct EncodedPermanentProgram {
    pub(crate) program: DecodedProgram,
    pub(crate) declared_entities: Vec<DecodedEntity>,
    pub(crate) named_individuals: Vec<u32>,
    manifest_limit: usize,
}

struct DigestWriter(Sha256);

impl std::io::Write for DigestWriter {
    fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
        self.0.update(bytes);
        Ok(bytes.len())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

impl EncodedPermanentProgram {
    pub(crate) fn semantic_sha256(&self) -> EncodedResult<[u8; 32]> {
        let mut writer = DigestWriter(Sha256::new());
        serde_json::to_writer(&mut writer, &self.program).map_err(|_| {
            EncodedValidationError::invariant("permanent-program semantic serialization failed")
        })?;
        Ok(writer.0.finalize().into())
    }

    pub(crate) fn parity_manifest_json(&self) -> EncodedResult<Vec<u8>> {
        let program_sha256 = self.semantic_sha256()?;
        let encoded = serde_json::to_vec(&PermanentProgramManifest {
            schema_version: PERMANENT_PROGRAM_SCHEMA_VERSION,
            program_sha256: crate::model::hex(&program_sha256),
            program: &self.program,
        })
        .map_err(|_| {
            EncodedValidationError::invariant(
                "permanent-program parity manifest serialization failed",
            )
        })?;
        if encoded.len() > self.manifest_limit {
            return Err(EncodedValidationError::resource(
                "permanent-program parity manifest exceeds its byte limit",
            ));
        }
        Ok(encoded)
    }
}

#[derive(Serialize)]
struct PermanentProgramManifest<'a> {
    schema_version: u16,
    program_sha256: String,
    program: &'a DecodedProgram,
}

struct PendingPredicate {
    key: Vec<u8>,
    value: DecodedPredicate,
    fragment: usize,
    local_id: usize,
}

struct Fragment {
    predicates: Vec<DecodedPredicate>,
    clauses: Vec<DecodedClause>,
    positive_facts: Vec<DecodedGroundAtom>,
    negative_facts: Vec<DecodedGroundAtom>,
    provenance: Vec<DecodedProvenanceEntry>,
}

struct PendingProvenance {
    value: DecodedProvenanceEntry,
    fragment: usize,
    local_id: usize,
}

struct PendingClause {
    key: Vec<u8>,
    value: DecodedClause,
}

struct Budget {
    limits: PermanentProgramLimits,
    live_bytes: usize,
    peak_bytes: usize,
    work: u64,
}

impl Budget {
    fn new(limits: PermanentProgramLimits, live_bytes: usize) -> EncodedResult<Self> {
        let value = Self {
            limits,
            live_bytes,
            peak_bytes: live_bytes,
            work: 0,
        };
        if live_bytes > limits.max_owned_bytes {
            return Err(EncodedValidationError::resource(
                "permanent-program input exceeds its peak owned-byte limit",
            ));
        }
        Ok(value)
    }

    fn claim_owned(&mut self, amount: usize) -> EncodedResult<()> {
        self.allocate(amount)
    }

    fn claim_temporary(&mut self, amount: usize) -> EncodedResult<()> {
        self.allocate(amount)
    }

    fn release_temporary(&mut self, amount: usize) -> EncodedResult<()> {
        self.release(amount)
    }

    fn allocate(&mut self, amount: usize) -> EncodedResult<()> {
        self.live_bytes = self.live_bytes.checked_add(amount).ok_or_else(|| {
            EncodedValidationError::resource("permanent-program live-byte count overflowed")
        })?;
        self.peak_bytes = self.peak_bytes.max(self.live_bytes);
        if self.peak_bytes > self.limits.max_owned_bytes {
            return Err(EncodedValidationError::resource(
                "permanent-program assembly exceeds its peak owned-byte limit",
            ));
        }
        Ok(())
    }

    fn release(&mut self, amount: usize) -> EncodedResult<()> {
        self.live_bytes = self.live_bytes.checked_sub(amount).ok_or_else(|| {
            EncodedValidationError::invariant("permanent-program live-byte accounting underflowed")
        })?;
        Ok(())
    }

    fn resize_allocation(&mut self, before: usize, after: usize) -> EncodedResult<()> {
        if after >= before {
            self.allocate(after - before)
        } else {
            self.release(before - after)
        }
    }

    fn claim_work(&mut self, amount: usize) -> EncodedResult<()> {
        let amount = u64::try_from(amount)
            .map_err(|_| EncodedValidationError::resource("permanent-program work exceeds u64"))?;
        let following = self.work.checked_add(amount).ok_or_else(|| {
            EncodedValidationError::resource("permanent-program work count overflowed")
        })?;
        if following > self.limits.max_work {
            return Err(EncodedValidationError::resource(
                "permanent-program assembly exceeds its work limit",
            ));
        }
        self.work = following;
        Ok(())
    }

    fn count(observed: usize, allowed: usize, name: &'static str) -> EncodedResult<()> {
        if observed > allowed {
            Err(EncodedValidationError::resource(format!(
                "permanent-program {name} exceeds its limit"
            )))
        } else {
            Ok(())
        }
    }
}

/// Consume every fragment and publish one dense program only after final validation.
pub(crate) fn assemble_encoded_permanent_program<E>(
    phases: EncodedSliceProgram,
    limits: PermanentProgramLimits,
    poll: &mut impl FnMut(&'static str) -> Result<(), E>,
) -> ControlledResult<EncodedPermanentProgram, E> {
    poll("permanent-program-preflight").map_err(PermanentProgramError::Control)?;
    let EncodedSliceProgram {
        named_classes,
        object_roles,
        data_roles,
        data_inclusions,
        data_role_hierarchy,
        simple_roles,
        complex_roles,
        role_characteristics,
        object_role_hierarchy,
        role_semantics,
        role_automata,
        role_model,
        role_clauses,
    } = phases;
    let DataRolePhase {
        data_property_domain,
        ..
    } = data_roles;
    let ObjectRolePhase {
        object_role_domain,
        inverse_role_ids: discarded_inverse_role_ids,
        ..
    } = object_roles;
    drop(discarded_inverse_role_ids);
    drop((
        data_inclusions,
        data_role_hierarchy,
        simple_roles,
        complex_roles,
        role_characteristics,
        object_role_hierarchy,
        role_semantics,
        role_automata,
    ));
    let named = named_classes.into_program_parts();
    let datatype_semantics =
        validate_semantic_coverage(&named).map_err(PermanentProgramError::Encoded)?;
    let semantic_evidence = named.semantic_evidence;
    let input_owned = permanent_input_owned_bytes(
        &named,
        &data_property_domain,
        &object_role_domain,
        &role_clauses,
        &role_model.role_model,
    )
    .map_err(PermanentProgramError::Encoded)?;
    let mut budget = Budget::new(limits, input_owned).map_err(PermanentProgramError::Encoded)?;
    let literal_identities = freeze_literal_identities(&named, datatype_semantics, &mut budget)
        .map_err(PermanentProgramError::Encoded)?;
    let semantic_payload_json = freeze_datatype_semantic_payload(&named, &mut budget)
        .map_err(PermanentProgramError::Encoded)?;
    let unknown_datatype_ids =
        freeze_unknown_datatype_ids(&named, &mut budget).map_err(PermanentProgramError::Encoded)?;
    let datatype_definitions = named.datatype_definition_pairs;
    let declared_entities = named.declared_entities;
    let named_individuals = named.named_individuals;
    let symbol_domains = freeze_symbol_domains(
        named.class_domain,
        data_property_domain,
        named.data_range_domain,
        named.data_value_domain,
        named.entity_domain,
        named.individual_domain,
        object_role_domain,
        named.source_literal_domain,
        &mut budget,
    )
    .map_err(PermanentProgramError::Encoded)?;
    poll("permanent-program-symbols").map_err(PermanentProgramError::Control)?;

    let mut fragments = [
        Fragment {
            predicates: named.predicates,
            clauses: named.clauses,
            positive_facts: named.positive_facts,
            negative_facts: named.negative_facts,
            provenance: named.provenance,
        },
        Fragment {
            predicates: role_clauses.predicates,
            clauses: role_clauses.clauses,
            positive_facts: Vec::new(),
            negative_facts: Vec::new(),
            provenance: role_clauses.provenance,
        },
    ];
    let (predicates, predicate_maps) = freeze_predicates(&mut fragments, &mut budget, poll)?;
    poll("permanent-program-predicates").map_err(PermanentProgramError::Control)?;
    let (provenance, provenance_maps) = freeze_provenance(&mut fragments, &mut budget, poll)?;
    poll("permanent-program-provenance").map_err(PermanentProgramError::Control)?;
    let (clauses, promoted_facts) = freeze_clauses(
        &mut fragments,
        &predicate_maps,
        &provenance_maps,
        &predicates,
        &provenance,
        &mut budget,
        poll,
    )?;
    poll("permanent-program-clauses").map_err(PermanentProgramError::Control)?;
    let (positive_facts, negative_facts) = freeze_facts(
        &mut fragments,
        promoted_facts,
        &predicate_maps,
        &provenance_maps,
        &predicates,
        &mut budget,
        poll,
    )?;
    release_remap_storage(predicate_maps, &mut budget).map_err(PermanentProgramError::Encoded)?;
    release_remap_storage(provenance_maps, &mut budget).map_err(PermanentProgramError::Encoded)?;
    poll("permanent-program-facts").map_err(PermanentProgramError::Control)?;

    let role_model = role_model.role_model;
    let expressivity_evidence = RepresentableExpressivityEvidence {
        source: semantic_evidence,
        unknown_datatypes: !unknown_datatype_ids.is_empty(),
    };
    let expressivity = derive_representable_expressivity(
        &predicates,
        &clauses,
        &positive_facts,
        &negative_facts,
        &provenance,
        &role_model,
        expressivity_evidence,
    )
    .map_err(PermanentProgramError::Encoded)?;
    let datatype_model = DecodedDatatypeModel {
        literal_identities,
        datatype_definitions,
        unknown_datatype_ids,
        semantic_payload_json,
    };
    let program = DecodedProgram {
        symbol_domains,
        predicates,
        clauses,
        positive_facts,
        negative_facts,
        ground_disjunctions: Vec::new(),
        role_model,
        datatype_model,
        expressivity,
        provenance,
    };
    validate_decoded_program(&program).map_err(|error| {
        PermanentProgramError::Encoded(EncodedValidationError::invariant(format!(
            "assembled permanent program failed the decoded-program validator: {}",
            error.message
        )))
    })?;
    validate_decoded_session_domains(&program, &declared_entities, &named_individuals).map_err(
        |error| {
            PermanentProgramError::Encoded(EncodedValidationError::invariant(format!(
                "assembled session domains failed the decoded-domain validator: {}",
                error.message
            )))
        },
    )?;
    poll("permanent-program-publication").map_err(PermanentProgramError::Control)?;
    Ok(EncodedPermanentProgram {
        program,
        declared_entities,
        named_individuals,
        manifest_limit: limits.max_manifest_bytes,
    })
}

#[allow(clippy::too_many_arguments)]
fn freeze_symbol_domains(
    class_domain: DecodedSymbolDomain,
    data_property_domain: DecodedSymbolDomain,
    data_range_domain: DecodedSymbolDomain,
    data_value_domain: DecodedSymbolDomain,
    entity_domain: DecodedSymbolDomain,
    individual_domain: DecodedSymbolDomain,
    object_role_domain: DecodedSymbolDomain,
    source_literal_domain: DecodedSymbolDomain,
    budget: &mut Budget,
) -> EncodedResult<Vec<DecodedSymbolDomain>> {
    let mut values = vec![
        class_domain,
        data_property_domain,
        data_range_domain,
        data_value_domain,
        entity_domain,
        individual_domain,
        object_role_domain,
        source_literal_domain,
    ];
    let expected = [
        SymbolKind::ClassExpression,
        SymbolKind::DataProperty,
        SymbolKind::DataRange,
        SymbolKind::DataValue,
        SymbolKind::Entity,
        SymbolKind::Individual,
        SymbolKind::ObjectRole,
        SymbolKind::SourceLiteral,
    ];
    if values.iter().map(|value| value.kind).ne(expected) {
        return Err(EncodedValidationError::invariant(
            "permanent-program symbol domains have the wrong kinds",
        ));
    }
    budget.claim_owned(
        values
            .capacity()
            .saturating_mul(size_of::<DecodedSymbolDomain>()),
    )?;
    for domain in &mut values {
        for (identifier, value) in domain.values.iter_mut().enumerate() {
            if usize::try_from(value.identifier).ok() != Some(identifier) {
                return Err(EncodedValidationError::invariant(
                    "permanent-program symbol IDs are not dense",
                ));
            }
            budget.claim_work(1)?;
        }
    }
    Ok(values)
}

fn validate_semantic_coverage(
    named: &NamedProgramParts,
) -> EncodedResult<RepresentableDatatypeSemantics> {
    const UNSUPPORTED: &str = "permanent-program source semantics require a datatype semantic phase for non-default ranges or literals";
    if named.semantic_evidence.unsupported_extension {
        return Err(EncodedValidationError::protocol(
            "permanent-program source semantics contain an unsupported extension",
        ));
    }
    if named.source_data_identity_ids.len() != named.source_literal_domain.values.len() {
        return Err(EncodedValidationError::invariant(
            "permanent-program source literal identities are incomplete",
        ));
    }
    if named.source_literal_semantics.len() != named.source_literal_domain.values.len() {
        return Err(EncodedValidationError::invariant(
            "permanent-program source literal semantics are incomplete",
        ));
    }
    if !named
        .datatype_definition_pairs
        .windows(2)
        .all(|pair| pair[0].0 < pair[1].0)
    {
        return Err(EncodedValidationError::invariant(
            "permanent-program datatype definitions are not canonical",
        ));
    }
    for (datatype_id, data_range_id) in &named.datatype_definition_pairs {
        let datatype = usize::try_from(*datatype_id)
            .ok()
            .and_then(|index| named.data_range_domain.values.get(index))
            .ok_or_else(|| {
                EncodedValidationError::invariant(
                    "permanent-program defined datatype ID is dangling",
                )
            })?;
        let datatype_iri = datatype
            .display
            .strip_prefix("datatype:")
            .filter(|iri| !crate::datatypes::is_supported_datatype(iri))
            .ok_or_else(|| {
                EncodedValidationError::invariant(
                    "permanent-program definition subject is not a custom datatype",
                )
            })?;
        if datatype_iri.is_empty()
            || usize::try_from(*data_range_id)
                .ok()
                .and_then(|index| named.data_range_domain.values.get(index))
                .is_none()
        {
            return Err(EncodedValidationError::invariant(
                "permanent-program datatype defining range is dangling",
            ));
        }
    }
    let Some(_top) = named
        .data_range_domain
        .values
        .iter()
        .find(|value| value.display == RDFS_LITERAL_DISPLAY)
    else {
        return Err(EncodedValidationError::protocol(UNSUPPORTED));
    };
    if named
        .data_range_domain
        .values
        .iter()
        .any(|value| !data_range_semantics_are_supported(named, &value.key))
    {
        return Err(EncodedValidationError::protocol(UNSUPPORTED));
    }
    let literals = if named.source_literal_domain.values.is_empty()
        && named.data_value_domain.values.is_empty()
    {
        RepresentableLiteralSemantics::None
    } else if supported_literal_domains_are_complete(named) {
        RepresentableLiteralSemantics::Supported
    } else {
        return Err(EncodedValidationError::protocol(UNSUPPORTED));
    };
    Ok(RepresentableDatatypeSemantics { literals })
}

fn data_range_semantics_are_supported(named: &NamedProgramParts, key: &[u8]) -> bool {
    data_range_semantics_are_supported_at(
        named,
        key,
        named.data_range_domain.values.len().saturating_add(1),
    )
}

fn data_range_semantics_are_supported_at(
    named: &NamedProgramParts,
    key: &[u8],
    remaining_depth: usize,
) -> bool {
    if remaining_depth == 0 {
        return false;
    }
    let Ok(index) = named
        .data_range_domain
        .values
        .binary_search_by(|value| value.key.as_slice().cmp(key))
    else {
        return false;
    };
    let value = &named.data_range_domain.values[index];
    if let Some(iri) = value.display.strip_prefix("datatype:") {
        if crate::datatypes::is_supported_datatype(iri) {
            return true;
        }
        let Some(defining_range_id) = datatype_definition_range_id(named, value.identifier) else {
            return true;
        };
        let Some(defining_range) = usize::try_from(defining_range_id)
            .ok()
            .and_then(|index| named.data_range_domain.values.get(index))
        else {
            return false;
        };
        return data_range_semantics_are_supported_at(
            named,
            &defining_range.key,
            remaining_depth.saturating_sub(1),
        );
    }
    if let Some(operand) = data_range_complement_operand_key(key) {
        return operand.len() < key.len()
            && data_range_semantics_are_supported_at(
                named,
                operand,
                remaining_depth.saturating_sub(1),
            );
    }
    if let Some(restriction) = datatype_restriction_key(key) {
        let Ok(datatype_index) = named
            .data_range_domain
            .values
            .binary_search_by(|value| value.key.as_slice().cmp(restriction.datatype_key))
        else {
            return false;
        };
        let Some(datatype_iri) = named.data_range_domain.values[datatype_index]
            .display
            .strip_prefix("datatype:")
        else {
            return false;
        };
        return crate::datatypes::is_supported_datatype(datatype_iri)
            && restriction.facets.iter().all(|facet| {
                SUPPORTED_FACET_IRIS.contains(&facet.facet_iri)
                    && source_literal_semantics_are_supported(named, facet.literal_key)
            });
    }
    if let Some((_, operands)) = data_range_boolean_operand_keys(key) {
        return operands.iter().all(|operand| {
            operand.len() < key.len()
                && data_range_semantics_are_supported_at(
                    named,
                    operand,
                    remaining_depth.saturating_sub(1),
                )
        });
    }
    if let Some(literals) = data_range_enumeration_literal_keys(key) {
        return literals
            .iter()
            .all(|literal| source_literal_semantics_are_supported(named, literal));
    }
    false
}

fn source_literal_semantics_are_supported(named: &NamedProgramParts, key: &[u8]) -> bool {
    let Ok(source_index) = named
        .source_literal_domain
        .values
        .binary_search_by(|value| value.key.as_slice().cmp(key))
    else {
        return false;
    };
    let Some(data_identity_id) = named
        .source_data_identity_ids
        .get(source_index)
        .copied()
        .flatten()
    else {
        return false;
    };
    let Some(source) = named.source_literal_semantics.get(source_index) else {
        return false;
    };
    let Some(data_value) = usize::try_from(data_identity_id)
        .ok()
        .and_then(|index| named.data_value_domain.values.get(index))
    else {
        return false;
    };
    literal_semantic_values(source, &data_value.key).is_some()
}

fn datatype_definition_range_id(named: &NamedProgramParts, datatype_id: u32) -> Option<u32> {
    named
        .datatype_definition_pairs
        .binary_search_by_key(&datatype_id, |(defined_id, _)| *defined_id)
        .ok()
        .map(|index| named.datatype_definition_pairs[index].1)
}

fn freeze_unknown_datatype_ids(
    named: &NamedProgramParts,
    budget: &mut Budget,
) -> EncodedResult<Vec<u32>> {
    let mut identifiers = Vec::new();
    identifiers
        .try_reserve_exact(named.data_range_domain.values.len())
        .map_err(|_| {
            EncodedValidationError::resource("unknown datatype identifier allocation failed")
        })?;
    for value in &named.data_range_domain.values {
        budget.claim_work(1)?;
        if data_range_semantics_are_unknown(
            named,
            &value.key,
            named.data_range_domain.values.len().saturating_add(1),
        ) {
            identifiers.push(value.identifier);
        }
    }
    budget.claim_owned(
        identifiers
            .capacity()
            .checked_mul(size_of::<u32>())
            .ok_or_else(|| {
                EncodedValidationError::resource("unknown datatype identifier ownership overflowed")
            })?,
    )?;
    Ok(identifiers)
}

fn data_range_semantics_are_unknown(
    named: &NamedProgramParts,
    key: &[u8],
    remaining_depth: usize,
) -> bool {
    if remaining_depth == 0 {
        return true;
    }
    let Ok(index) = named
        .data_range_domain
        .values
        .binary_search_by(|value| value.key.as_slice().cmp(key))
    else {
        return true;
    };
    let value = &named.data_range_domain.values[index];
    if let Some(iri) = value.display.strip_prefix("datatype:") {
        if crate::datatypes::is_supported_datatype(iri) {
            return false;
        }
        let Some(defining_range_id) = datatype_definition_range_id(named, value.identifier) else {
            return true;
        };
        return usize::try_from(defining_range_id)
            .ok()
            .and_then(|index| named.data_range_domain.values.get(index))
            .is_none_or(|defining_range| {
                data_range_semantics_are_unknown(
                    named,
                    &defining_range.key,
                    remaining_depth.saturating_sub(1),
                )
            });
    }
    if let Some(operand) = data_range_complement_operand_key(key) {
        return data_range_semantics_are_unknown(named, operand, remaining_depth.saturating_sub(1));
    }
    if data_range_enumeration_literal_keys(key).is_some() {
        return false;
    }
    if datatype_restriction_key(key).is_some() {
        return false;
    }
    data_range_boolean_operand_keys(key).is_none_or(|(_, operands)| {
        operands.iter().any(|operand| {
            data_range_semantics_are_unknown(named, operand, remaining_depth.saturating_sub(1))
        })
    })
}

fn supported_literal_domains_are_complete(named: &NamedProgramParts) -> bool {
    if named.source_literal_domain.values.is_empty()
        || named.data_value_domain.values.is_empty()
        || named.source_data_identity_ids.len() != named.source_literal_domain.values.len()
        || named.source_literal_semantics.len() != named.source_literal_domain.values.len()
    {
        return false;
    }
    let complete = named
        .source_literal_semantics
        .iter()
        .zip(named.source_data_identity_ids.iter())
        .all(|(semantics, data_identity_id)| {
            let Some(data_identity_id) = data_identity_id else {
                return false;
            };
            let Some(data_value) = usize::try_from(*data_identity_id)
                .ok()
                .and_then(|index| named.data_value_domain.values.get(index))
            else {
                return false;
            };
            literal_semantic_values(semantics, &data_value.key).is_some()
        });
    complete
        && (0..named.data_value_domain.values.len()).all(|data_index| {
            u32::try_from(data_index).ok().is_some_and(|identifier| {
                named.source_data_identity_ids.contains(&Some(identifier))
            })
        })
}

fn freeze_literal_identities(
    named: &NamedProgramParts,
    semantics: RepresentableDatatypeSemantics,
    budget: &mut Budget,
) -> EncodedResult<Vec<DecodedLiteralIdentity>> {
    if semantics.literals != RepresentableLiteralSemantics::Supported {
        if named.source_literal_domain.values.is_empty() {
            return Ok(Vec::new());
        }
        return Err(EncodedValidationError::invariant(
            "representable datatype shape retained unsupported literals",
        ));
    }
    let mut identities = Vec::new();
    identities
        .try_reserve_exact(named.source_literal_domain.values.len())
        .map_err(|_| {
            EncodedValidationError::resource("permanent-program literal identity allocation failed")
        })?;
    budget.claim_owned(
        identities
            .capacity()
            .saturating_mul(size_of::<DecodedLiteralIdentity>()),
    )?;
    for (source_index, (data_identity_id, source_semantics)) in named
        .source_data_identity_ids
        .iter()
        .copied()
        .zip(named.source_literal_semantics.iter())
        .enumerate()
    {
        budget.claim_work(1)?;
        let data_identity_id = data_identity_id.ok_or_else(|| {
            EncodedValidationError::invariant("representable source literal lost its data identity")
        })?;
        let data_value = named
            .data_value_domain
            .values
            .get(usize::try_from(data_identity_id).map_err(|_| {
                EncodedValidationError::invariant("literal data identity exceeds usize")
            })?)
            .ok_or_else(|| {
                EncodedValidationError::invariant("literal data identity is dangling")
            })?;
        let (comparison, semantic_payload) =
            literal_semantic_values(source_semantics, &data_value.key).ok_or_else(|| {
                EncodedValidationError::invariant(
                    "representable literal data identity changed encoding",
                )
            })?;
        let comparison_payload = serde_json::to_vec(&comparison)
            .map_err(|_| EncodedValidationError::invariant("literal comparison encoding failed"))?;
        let comparison_key = crate::model::hex(&Sha256::digest(&comparison_payload));
        let semantic_payload_json = serde_json::to_string(&semantic_payload)
            .map_err(|_| EncodedValidationError::invariant("literal semantic encoding failed"))?;
        budget.claim_owned(
            comparison_key
                .capacity()
                .saturating_add(semantic_payload_json.capacity()),
        )?;
        identities.push(DecodedLiteralIdentity {
            source_literal_id: u32::try_from(source_index).map_err(|_| {
                EncodedValidationError::resource("source literal identifier exceeds u32")
            })?,
            data_identity_id,
            comparison_key,
            semantic_payload_json,
        });
    }
    Ok(identities)
}

fn freeze_datatype_semantic_payload(
    named: &NamedProgramParts,
    budget: &mut Budget,
) -> EncodedResult<String> {
    if !named
        .data_range_domain
        .values
        .iter()
        .any(|value| value.display == RDFS_LITERAL_DISPLAY)
    {
        return Err(EncodedValidationError::invariant(
            "representable datatype domain lost rdfs:Literal",
        ));
    }
    let mut ranges = Vec::new();
    ranges
        .try_reserve_exact(named.data_range_domain.values.len())
        .map_err(|_| {
            EncodedValidationError::resource(
                "permanent-program datatype range payload allocation failed",
            )
        })?;
    for value in &named.data_range_domain.values {
        let payload = data_range_semantic_payload(
            named,
            &value.key,
            named.data_range_domain.values.len().saturating_add(1),
            budget,
        )?;
        ranges.push(payload);
    }
    let mut definitions = Vec::new();
    definitions
        .try_reserve_exact(named.datatype_definition_pairs.len())
        .map_err(|_| {
            EncodedValidationError::resource(
                "permanent-program datatype definition payload allocation failed",
            )
        })?;
    for (datatype_id, data_range_id) in &named.datatype_definition_pairs {
        let datatype = named
            .data_range_domain
            .values
            .get(usize::try_from(*datatype_id).map_err(|_| {
                EncodedValidationError::invariant("defined datatype ID exceeds usize")
            })?)
            .ok_or_else(|| EncodedValidationError::invariant("defined datatype ID is dangling"))?;
        let datatype_iri = datatype.display.strip_prefix("datatype:").ok_or_else(|| {
            EncodedValidationError::invariant("definition subject is not a datatype")
        })?;
        let data_range = named
            .data_range_domain
            .values
            .get(usize::try_from(*data_range_id).map_err(|_| {
                EncodedValidationError::invariant("datatype defining range ID exceeds usize")
            })?)
            .ok_or_else(|| {
                EncodedValidationError::invariant("datatype defining range ID is dangling")
            })?;
        let data_range = data_range_semantic_value(
            named,
            &data_range.key,
            named.data_range_domain.values.len().saturating_add(1),
            budget,
        )?;
        let payload = serde_json::to_string(&serde_json::json!({
            "data_range": data_range,
            "datatype_iri": datatype_iri,
            "record": "datatype_definition_semantic",
            "schema_version": 1,
        }))
        .map_err(|_| {
            EncodedValidationError::invariant("datatype definition JSON encoding failed")
        })?;
        definitions.push((datatype_iri, payload));
    }
    budget.claim_work(definitions.len())?;
    definitions.sort_unstable_by(|left, right| left.0.cmp(right.0));
    let range_bytes = ranges.iter().map(String::len).sum::<usize>();
    let definition_bytes = definitions
        .iter()
        .map(|(_, definition)| definition.len())
        .sum::<usize>();
    let separator_bytes = ranges
        .len()
        .saturating_sub(1)
        .saturating_add(definitions.len().saturating_sub(1));
    let capacity = "{\"data_ranges\":[],\"definitions\":[],\"record\":\"datatype_semantic_model\",\"schema_version\":1}"
        .len()
        .saturating_add(range_bytes)
        .saturating_add(definition_bytes)
        .saturating_add(separator_bytes);
    let mut payload = String::new();
    payload.try_reserve_exact(capacity).map_err(|_| {
        EncodedValidationError::resource(
            "permanent-program datatype model payload allocation failed",
        )
    })?;
    payload.push_str("{\"data_ranges\":[");
    for (index, range) in ranges.into_iter().enumerate() {
        if index != 0 {
            payload.push(',');
        }
        payload.push_str(&range);
    }
    payload.push_str("],\"definitions\":[");
    for (index, (_, definition)) in definitions.into_iter().enumerate() {
        if index != 0 {
            payload.push(',');
        }
        payload.push_str(&definition);
    }
    payload.push_str("],\"record\":\"datatype_semantic_model\",\"schema_version\":1}");
    budget.claim_owned(payload.capacity())?;
    Ok(payload)
}

fn data_range_semantic_payload(
    named: &NamedProgramParts,
    key: &[u8],
    remaining_depth: usize,
    budget: &mut Budget,
) -> EncodedResult<String> {
    let value = data_range_semantic_value(named, key, remaining_depth, budget)?;
    serde_json::to_string(&value)
        .map_err(|_| EncodedValidationError::invariant("datatype range JSON encoding failed"))
}

fn data_range_semantic_value(
    named: &NamedProgramParts,
    key: &[u8],
    remaining_depth: usize,
    budget: &mut Budget,
) -> EncodedResult<serde_json::Value> {
    if remaining_depth == 0 {
        return Err(EncodedValidationError::invariant(
            "validated datatype range nesting is cyclic",
        ));
    }
    budget.claim_work(1)?;
    let index = named
        .data_range_domain
        .values
        .binary_search_by(|value| value.key.as_slice().cmp(key))
        .map_err(|_| {
            EncodedValidationError::invariant(
                "validated datatype payload references a missing operand",
            )
        })?;
    let value = &named.data_range_domain.values[index];
    if let Some(iri) = value.display.strip_prefix("datatype:") {
        if crate::datatypes::is_supported_datatype(iri)
            || datatype_definition_range_id(named, value.identifier).is_some()
        {
            return Ok(named_datatype_semantic_value(iri, false));
        }
        return Ok(named_datatype_semantic_value(iri, true));
    }
    if let Some(operand_key) = data_range_complement_operand_key(key) {
        if operand_key.len() >= key.len() {
            return Err(EncodedValidationError::invariant(
                "validated datatype complement operand does not decrease",
            ));
        }
        let operand = data_range_semantic_value(
            named,
            operand_key,
            remaining_depth.saturating_sub(1),
            budget,
        )?;
        return Ok(serde_json::json!({
            "datatype_iri": null,
            "facets": [],
            "kind": "complement",
            "operands": [operand],
            "record": "data_range_semantic",
            "schema_version": 1,
            "values": [],
        }));
    }
    if let Some(literal_keys) = data_range_enumeration_literal_keys(key) {
        budget.claim_work(literal_keys.len())?;
        let mut values = Vec::new();
        values.try_reserve_exact(literal_keys.len()).map_err(|_| {
            EncodedValidationError::resource("datatype enumeration value allocation failed")
        })?;
        for literal_key in literal_keys {
            values.push(source_literal_semantic_value(named, literal_key)?);
        }
        let mut canonical = Vec::new();
        canonical.try_reserve_exact(values.len()).map_err(|_| {
            EncodedValidationError::resource(
                "datatype enumeration canonicalization allocation failed",
            )
        })?;
        for value in values {
            let encoded = serde_json::to_vec(&value).map_err(|_| {
                EncodedValidationError::invariant("datatype enumeration value JSON encoding failed")
            })?;
            canonical.push((encoded, value));
        }
        budget.claim_work(canonical.len())?;
        canonical.sort_unstable_by(|left, right| left.0.cmp(&right.0));
        canonical.dedup_by(|left, right| left.0 == right.0);
        if canonical.is_empty() {
            return Err(EncodedValidationError::invariant(
                "validated datatype enumeration is empty",
            ));
        }
        return Ok(serde_json::json!({
            "datatype_iri": null,
            "facets": [],
            "kind": "enumeration",
            "operands": [],
            "record": "data_range_semantic",
            "schema_version": 1,
            "values": canonical
                .into_iter()
                .map(|(_, value)| value)
                .collect::<Vec<_>>(),
        }));
    }
    if let Some(restriction) = datatype_restriction_key(key) {
        let datatype_index = named
            .data_range_domain
            .values
            .binary_search_by(|value| value.key.as_slice().cmp(restriction.datatype_key))
            .map_err(|_| {
                EncodedValidationError::invariant(
                    "validated datatype restriction references a missing datatype",
                )
            })?;
        let datatype_iri = named.data_range_domain.values[datatype_index]
            .display
            .strip_prefix("datatype:")
            .filter(|iri| crate::datatypes::is_supported_datatype(iri))
            .ok_or_else(|| {
                EncodedValidationError::invariant(
                    "validated datatype restriction has an unsupported base",
                )
            })?;
        budget.claim_work(restriction.facets.len())?;
        let mut canonical = Vec::new();
        canonical
            .try_reserve_exact(restriction.facets.len())
            .map_err(|_| {
                EncodedValidationError::resource("datatype restriction facet allocation failed")
            })?;
        for facet in restriction.facets {
            if !SUPPORTED_FACET_IRIS.contains(&facet.facet_iri) {
                return Err(EncodedValidationError::invariant(
                    "validated datatype restriction has an unsupported facet",
                ));
            }
            let value = serde_json::json!({
                "facet_iri": facet.facet_iri,
                "record": "facet_semantic",
                "schema_version": 1,
                "value": source_literal_semantic_value(named, facet.literal_key)?,
            });
            let encoded = serde_json::to_vec(&value).map_err(|_| {
                EncodedValidationError::invariant("datatype restriction facet JSON encoding failed")
            })?;
            canonical.push((encoded, value));
        }
        canonical.sort_unstable_by(|left, right| left.0.cmp(&right.0));
        canonical.dedup_by(|left, right| left.0 == right.0);
        if canonical.is_empty() {
            return Err(EncodedValidationError::invariant(
                "validated datatype restriction has no facets",
            ));
        }
        return Ok(serde_json::json!({
            "datatype_iri": datatype_iri,
            "facets": canonical
                .into_iter()
                .map(|(_, facet)| facet)
                .collect::<Vec<_>>(),
            "kind": "restriction",
            "operands": [],
            "record": "data_range_semantic",
            "schema_version": 1,
            "values": [],
        }));
    }
    let (tag, operand_keys) = data_range_boolean_operand_keys(key).ok_or_else(|| {
        EncodedValidationError::invariant(
            "validated datatype payload contains an unassembled data range",
        )
    })?;
    let kind = match tag {
        DATA_INTERSECTION_OF_TAG => "intersection",
        DATA_UNION_OF_TAG => "union",
        _ => {
            return Err(EncodedValidationError::invariant(
                "validated datatype Boolean range changed tag",
            ))
        }
    };
    budget.claim_work(operand_keys.len())?;
    let mut operands = Vec::new();
    operands
        .try_reserve_exact(operand_keys.len())
        .map_err(|_| {
            EncodedValidationError::resource("datatype Boolean operand allocation failed")
        })?;
    for operand_key in operand_keys {
        if operand_key.len() >= key.len() {
            return Err(EncodedValidationError::invariant(
                "validated datatype Boolean operand does not decrease",
            ));
        }
        let operand = data_range_semantic_value(
            named,
            operand_key,
            remaining_depth.saturating_sub(1),
            budget,
        )?;
        if operand.get("kind").and_then(serde_json::Value::as_str) == Some(kind) {
            let nested = operand
                .get("operands")
                .and_then(serde_json::Value::as_array)
                .ok_or_else(|| {
                    EncodedValidationError::invariant(
                        "validated datatype Boolean operand lost its children",
                    )
                })?;
            operands.extend(nested.iter().cloned());
        } else {
            operands.push(operand);
        }
    }
    let mut canonical = Vec::new();
    canonical.try_reserve_exact(operands.len()).map_err(|_| {
        EncodedValidationError::resource("datatype Boolean canonicalization allocation failed")
    })?;
    for operand in operands {
        let encoded = serde_json::to_vec(&operand).map_err(|_| {
            EncodedValidationError::invariant("datatype Boolean operand JSON encoding failed")
        })?;
        canonical.push((encoded, operand));
    }
    budget.claim_work(canonical.len())?;
    canonical.sort_unstable_by(|left, right| left.0.cmp(&right.0));
    canonical.dedup_by(|left, right| left.0 == right.0);
    if canonical.len() < 2 {
        return Err(EncodedValidationError::invariant(
            "validated datatype Boolean range no longer has two distinct operands",
        ));
    }
    Ok(serde_json::json!({
        "datatype_iri": null,
        "facets": [],
        "kind": kind,
        "operands": canonical
            .into_iter()
            .map(|(_, operand)| operand)
            .collect::<Vec<_>>(),
        "record": "data_range_semantic",
        "schema_version": 1,
        "values": [],
    }))
}

fn named_datatype_semantic_value(iri: &str, opaque: bool) -> serde_json::Value {
    serde_json::json!({
        "datatype_iri": iri,
        "facets": [],
        "kind": if opaque { "opaque" } else { "datatype" },
        "operands": [],
        "record": "data_range_semantic",
        "schema_version": 1,
        "values": [],
    })
}

fn source_literal_semantic_value(
    named: &NamedProgramParts,
    key: &[u8],
) -> EncodedResult<serde_json::Value> {
    let source_index = named
        .source_literal_domain
        .values
        .binary_search_by(|value| value.key.as_slice().cmp(key))
        .map_err(|_| {
            EncodedValidationError::invariant(
                "validated datatype enumeration references a missing literal",
            )
        })?;
    let data_identity_id = named
        .source_data_identity_ids
        .get(source_index)
        .copied()
        .flatten()
        .ok_or_else(|| {
            EncodedValidationError::invariant(
                "validated datatype enumeration literal lost its data identity",
            )
        })?;
    let source = named
        .source_literal_semantics
        .get(source_index)
        .ok_or_else(|| {
            EncodedValidationError::invariant(
                "validated datatype enumeration literal lost its source semantics",
            )
        })?;
    let data_value = named
        .data_value_domain
        .values
        .get(usize::try_from(data_identity_id).map_err(|_| {
            EncodedValidationError::invariant(
                "validated datatype enumeration data identity exceeds usize",
            )
        })?)
        .ok_or_else(|| {
            EncodedValidationError::invariant(
                "validated datatype enumeration data identity is dangling",
            )
        })?;
    literal_semantic_values(source, &data_value.key)
        .map(|(_, payload)| payload)
        .ok_or_else(|| {
            EncodedValidationError::invariant(
                "validated datatype enumeration literal changed semantic encoding",
            )
        })
}

fn literal_semantic_values(
    source: &SourceLiteralSemanticSeed,
    key: &[u8],
) -> Option<(serde_json::Value, serde_json::Value)> {
    let payload = key.strip_prefix(DATA_IDENTITY_PREFIX)?;
    let data_identity = serde_json::from_slice::<serde_json::Value>(payload).ok()?;
    if serde_json::to_vec(&data_identity).ok()?.as_slice() != payload {
        return None;
    }
    let fields = data_identity.as_array()?;
    if !literal_identity_matches_source(source, fields) {
        return None;
    }
    let comparison = crate::datatypes::comparison_fields_for_identity(
        fields,
        crate::datatypes::DatatypeLimits::default(),
        &crate::datatypes::NeverCancel,
    )
    .ok()?;
    let comparison = serde_json::Value::Array(comparison);
    let payload = serde_json::to_value(LiteralSemanticPayload {
        comparison: &comparison,
        compatibility: "owl2",
        data_identity: &data_identity,
        datatype_iri: &source.datatype_iri,
        language: source.language.as_deref(),
        lexical_form: &source.lexical_form,
        record: "literal_semantic",
        schema_version: 1,
    })
    .ok()?;
    Some((comparison, payload))
}

fn literal_identity_matches_source(
    source: &SourceLiteralSemanticSeed,
    fields: &[serde_json::Value],
) -> bool {
    let Some(tag) = fields.first().and_then(serde_json::Value::as_str) else {
        return false;
    };
    if numeric_literal_datatype_is_supported(&source.datatype_iri) {
        return source.language.is_none() && tag == "numeric-rational-hex-v1" && fields.len() == 3;
    }
    let Some(rule) = LITERAL_IDENTITY_RULES
        .iter()
        .find(|rule| rule.datatype_iri == source.datatype_iri)
    else {
        return false;
    };
    if tag != rule.identity_tag || fields.len() != rule.arity {
        return false;
    }
    if let Some((index, expected)) = rule.discriminator {
        if fields.get(index).and_then(serde_json::Value::as_str) != Some(expected) {
            return false;
        }
    }
    let language_matches = match rule.language {
        LiteralLanguageRule::Forbidden => {
            source.language.is_none()
                && (tag != "plain-string-v1"
                    || fields.get(2).is_some_and(serde_json::Value::is_null))
        }
        LiteralLanguageRule::Identity => match &source.language {
            Some(language) => {
                fields.get(2).and_then(serde_json::Value::as_str) == Some(language.as_str())
            }
            None => fields.get(2).is_some_and(serde_json::Value::is_null),
        },
    };
    if !language_matches {
        return false;
    }
    if source.datatype_iri == XSD_STRING_IRI
        && fields.get(1).and_then(serde_json::Value::as_str) != Some(source.lexical_form.as_str())
    {
        return false;
    }
    if source.datatype_iri == XSD_BOOLEAN_IRI {
        return fields
            .get(1)
            .and_then(serde_json::Value::as_bool)
            .is_some_and(|value| {
                if value {
                    matches!(source.lexical_form.as_str(), "true" | "1")
                } else {
                    matches!(source.lexical_form.as_str(), "false" | "0")
                }
            });
    }
    true
}

fn numeric_literal_datatype_is_supported(iri: &str) -> bool {
    if iri == OWL_RATIONAL_IRI {
        return true;
    }
    iri.strip_prefix(XSD_NAMESPACE).is_some_and(|local| {
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

fn data_range_complement_operand_key(candidate: &[u8]) -> Option<&[u8]> {
    let (tag, after_tag) = decode_canonical_varint(candidate, 0)?;
    if tag != DATA_COMPLEMENT_OF_TAG || candidate.get(after_tag) != Some(&CANONICAL_NODE_COMPONENT)
    {
        return None;
    }
    let (length, after_length) = decode_canonical_varint(candidate, after_tag + 1)?;
    let length = usize::try_from(length).ok()?;
    let end = after_length.checked_add(length)?;
    (end == candidate.len())
        .then(|| candidate.get(after_length..end))
        .flatten()
}

fn datatype_restriction_key(candidate: &[u8]) -> Option<DatatypeRestrictionKey<'_>> {
    let (tag, after_tag) = decode_canonical_varint(candidate, 0)?;
    if tag != DATATYPE_RESTRICTION_TAG {
        return None;
    }
    let (datatype_key, cursor) = canonical_node_component(candidate, after_tag)?;
    let (facet_keys, cursor) = canonical_collection_items(candidate, cursor, 1)?;
    if cursor != candidate.len() {
        return None;
    }
    let mut facets = Vec::new();
    facets.try_reserve_exact(facet_keys.len()).ok()?;
    for facet_key in facet_keys {
        facets.push(facet_restriction_key(facet_key)?);
    }
    Some(DatatypeRestrictionKey {
        datatype_key,
        facets,
    })
}

fn facet_restriction_key(candidate: &[u8]) -> Option<FacetRestrictionKey<'_>> {
    let (tag, after_tag) = decode_canonical_varint(candidate, 0)?;
    if tag != FACET_RESTRICTION_TAG {
        return None;
    }
    let (iri_key, cursor) = canonical_node_component(candidate, after_tag)?;
    let (literal_key, cursor) = canonical_node_component(candidate, cursor)?;
    (cursor == candidate.len()).then_some(FacetRestrictionKey {
        facet_iri: canonical_iri_text(iri_key)?,
        literal_key,
    })
}

fn canonical_iri_text(candidate: &[u8]) -> Option<&str> {
    let (tag, after_tag) = decode_canonical_varint(candidate, 0)?;
    if tag != IRI_TAG || candidate.get(after_tag) != Some(&CANONICAL_TEXT_COMPONENT) {
        return None;
    }
    let (length, after_length) = decode_canonical_varint(candidate, after_tag + 1)?;
    let length = usize::try_from(length).ok()?;
    let end = after_length.checked_add(length)?;
    (end == candidate.len())
        .then(|| std::str::from_utf8(candidate.get(after_length..end)?).ok())
        .flatten()
}

fn canonical_node_component(candidate: &[u8], cursor: usize) -> Option<(&[u8], usize)> {
    if candidate.get(cursor) != Some(&CANONICAL_NODE_COMPONENT) {
        return None;
    }
    let (length, after_length) = decode_canonical_varint(candidate, cursor + 1)?;
    let length = usize::try_from(length).ok()?;
    let end = after_length.checked_add(length)?;
    let key = candidate.get(after_length..end)?;
    (!key.is_empty()).then_some((key, end))
}

fn data_range_boolean_operand_keys(candidate: &[u8]) -> Option<(u64, Vec<&[u8]>)> {
    canonical_collection_item_keys(candidate, &[DATA_INTERSECTION_OF_TAG, DATA_UNION_OF_TAG], 2)
}

fn data_range_enumeration_literal_keys(candidate: &[u8]) -> Option<Vec<&[u8]>> {
    canonical_collection_item_keys(candidate, &[DATA_ONE_OF_TAG], 1).map(|(_, values)| values)
}

fn canonical_collection_item_keys<'a>(
    candidate: &'a [u8],
    accepted_tags: &[u64],
    minimum_count: usize,
) -> Option<(u64, Vec<&'a [u8]>)> {
    let (tag, after_tag) = decode_canonical_varint(candidate, 0)?;
    if !accepted_tags.contains(&tag) {
        return None;
    }
    let (items, cursor) = canonical_collection_items(candidate, after_tag, minimum_count)?;
    (cursor == candidate.len()).then_some((tag, items))
}

fn canonical_collection_items(
    candidate: &[u8],
    cursor: usize,
    minimum_count: usize,
) -> Option<(Vec<&[u8]>, usize)> {
    if candidate.get(cursor) != Some(&CANONICAL_COLLECTION_COMPONENT) {
        return None;
    }
    let (count, mut cursor) = decode_canonical_varint(candidate, cursor + 1)?;
    let count = usize::try_from(count).ok()?;
    if count < minimum_count {
        return None;
    }
    let mut items = Vec::new();
    items.try_reserve_exact(count).ok()?;
    for _ in 0..count {
        let (length, after_length) = decode_canonical_varint(candidate, cursor)?;
        let length = usize::try_from(length).ok()?;
        let end = after_length.checked_add(length)?;
        let item = candidate.get(after_length..end)?;
        if item.is_empty() {
            return None;
        }
        items.push(item);
        cursor = end;
    }
    Some((items, cursor))
}

fn decode_canonical_varint(bytes: &[u8], start: usize) -> Option<(u64, usize)> {
    let mut value = 0_u64;
    let mut shift = 0_u32;
    let end = bytes.len().min(start.saturating_add(10));
    for (index, byte) in bytes.iter().copied().enumerate().take(end).skip(start) {
        let payload = u64::from(byte & 0x7f);
        if shift == 63 && payload > 1 {
            return None;
        }
        value |= payload.checked_shl(shift)?;
        if byte & 0x80 == 0 {
            if index > start && payload == 0 {
                return None;
            }
            return Some((value, index + 1));
        }
        shift = shift.checked_add(7)?;
    }
    None
}

fn permanent_input_owned_bytes(
    named: &NamedProgramParts,
    data_property_domain: &DecodedSymbolDomain,
    object_role_domain: &DecodedSymbolDomain,
    role_clauses: &RoleClausePhase,
    role_model: &crate::input_wire::DecodedRoleModel,
) -> EncodedResult<usize> {
    let mut total = 0_usize;
    for domain in [
        &named.class_domain,
        data_property_domain,
        &named.data_range_domain,
        &named.data_value_domain,
        &named.entity_domain,
        &named.individual_domain,
        object_role_domain,
        &named.source_literal_domain,
    ] {
        add_bytes(
            &mut total,
            domain
                .values
                .capacity()
                .checked_mul(size_of::<crate::input_wire::DecodedSymbolValue>()),
        )?;
        for value in &domain.values {
            add_bytes(&mut total, Some(value.key.capacity()))?;
            add_bytes(&mut total, Some(value.display.capacity()))?;
        }
    }
    add_bytes(
        &mut total,
        named
            .declared_entities
            .capacity()
            .checked_mul(size_of::<DecodedEntity>()),
    )?;
    for entity in &named.declared_entities {
        add_bytes(&mut total, Some(entity.kind.capacity()))?;
        add_bytes(&mut total, Some(entity.iri.capacity()))?;
    }
    add_bytes(
        &mut total,
        named
            .named_individuals
            .capacity()
            .checked_mul(size_of::<u32>()),
    )?;
    add_bytes(
        &mut total,
        named
            .source_data_identity_ids
            .capacity()
            .checked_mul(size_of::<Option<u32>>()),
    )?;
    add_bytes(
        &mut total,
        named
            .source_literal_semantics
            .capacity()
            .checked_mul(size_of::<SourceLiteralSemanticSeed>()),
    )?;
    add_bytes(
        &mut total,
        named
            .datatype_definition_pairs
            .capacity()
            .checked_mul(size_of::<(u32, u32)>()),
    )?;
    for semantics in &named.source_literal_semantics {
        add_bytes(&mut total, Some(semantics.lexical_form.capacity()))?;
        add_bytes(&mut total, Some(semantics.datatype_iri.capacity()))?;
        add_bytes(
            &mut total,
            Some(semantics.language.as_ref().map_or(0, String::capacity)),
        )?;
    }
    for predicates in [&named.predicates, &role_clauses.predicates] {
        add_bytes(
            &mut total,
            predicates
                .capacity()
                .checked_mul(size_of::<DecodedPredicate>()),
        )?;
        for predicate in predicates {
            add_bytes(&mut total, Some(predicate_nested_owned_bytes(predicate)))?;
        }
    }
    for clauses in [&named.clauses, &role_clauses.clauses] {
        add_bytes(
            &mut total,
            clauses.capacity().checked_mul(size_of::<DecodedClause>()),
        )?;
        for clause in clauses {
            add_bytes(&mut total, Some(clause_nested_owned_bytes(clause)))?;
        }
    }
    for facts in [&named.positive_facts, &named.negative_facts] {
        add_bytes(
            &mut total,
            facts.capacity().checked_mul(size_of::<DecodedGroundAtom>()),
        )?;
        for fact in facts {
            add_bytes(&mut total, Some(ground_atom_nested_owned_bytes(fact)))?;
        }
    }
    for provenance in [&named.provenance, &role_clauses.provenance] {
        add_bytes(
            &mut total,
            provenance
                .capacity()
                .checked_mul(size_of::<DecodedProvenanceEntry>()),
        )?;
        for entry in provenance {
            add_bytes(&mut total, Some(provenance_nested_owned_bytes(entry)))?;
        }
    }
    for values in [
        role_model.inverse_role_ids.capacity(),
        role_model.non_simple_components.capacity(),
    ] {
        add_bytes(&mut total, values.checked_mul(size_of::<u32>()))?;
    }
    for capacity in [
        role_model.simple_inclusions.capacity(),
        role_model.data_inclusions.capacity(),
    ] {
        add_bytes(&mut total, capacity.checked_mul(size_of::<(u32, u32)>()))?;
    }
    add_bytes(
        &mut total,
        role_model
            .complex_inclusions
            .capacity()
            .checked_mul(size_of::<(Vec<u32>, u32)>()),
    )?;
    for (chain, _) in &role_model.complex_inclusions {
        add_bytes(&mut total, chain.capacity().checked_mul(size_of::<u32>()))?;
    }
    add_bytes(
        &mut total,
        role_model
            .automata
            .capacity()
            .checked_mul(size_of::<crate::input_wire::DecodedRoleAutomaton>()),
    )?;
    for automaton in &role_model.automata {
        add_bytes(
            &mut total,
            automaton
                .final_states
                .capacity()
                .checked_mul(size_of::<u32>()),
        )?;
        add_bytes(
            &mut total,
            automaton
                .transitions
                .capacity()
                .checked_mul(size_of::<crate::input_wire::DecodedRoleTransition>()),
        )?;
    }
    Ok(total)
}

fn add_bytes(total: &mut usize, amount: Option<usize>) -> EncodedResult<()> {
    let amount = amount.ok_or_else(|| {
        EncodedValidationError::resource("permanent-program owned-byte count overflowed")
    })?;
    *total = total.checked_add(amount).ok_or_else(|| {
        EncodedValidationError::resource("permanent-program owned-byte count overflowed")
    })?;
    Ok(())
}

fn predicate_nested_owned_bytes(value: &DecodedPredicate) -> usize {
    value
        .argument_sorts
        .capacity()
        .saturating_mul(size_of::<TermSort>())
        .saturating_add(value.annotation.capacity().saturating_mul(size_of::<u32>()))
        .saturating_add(value.internal_key.as_ref().map_or(0, String::capacity))
}

fn provenance_nested_owned_bytes(value: &DecodedProvenanceEntry) -> usize {
    value
        .source_sha256
        .capacity()
        .saturating_mul(size_of::<[u8; 32]>())
}

fn clause_nested_owned_bytes(value: &DecodedClause) -> usize {
    value
        .body
        .capacity()
        .saturating_mul(size_of::<DecodedAtom>())
        .saturating_add(
            value
                .head
                .capacity()
                .saturating_mul(size_of::<DecodedAtom>()),
        )
        .saturating_add(
            value
                .provenance_ids
                .capacity()
                .saturating_mul(size_of::<u32>()),
        )
        .saturating_add(value.join_order.capacity().saturating_mul(size_of::<u32>()))
        .saturating_add(
            value
                .body
                .iter()
                .chain(&value.head)
                .map(atom_nested_owned_bytes)
                .sum::<usize>(),
        )
}

fn atom_nested_owned_bytes(value: &DecodedAtom) -> usize {
    value
        .arguments
        .capacity()
        .saturating_mul(size_of::<DecodedTerm>())
}

fn ground_atom_nested_owned_bytes(value: &DecodedGroundAtom) -> usize {
    value
        .arguments
        .capacity()
        .saturating_mul(size_of::<DecodedTerm>())
        .saturating_add(
            value
                .provenance_ids
                .capacity()
                .saturating_mul(size_of::<u32>()),
        )
}

fn freeze_predicates<E>(
    fragments: &mut [Fragment],
    budget: &mut Budget,
    poll: &mut impl FnMut(&'static str) -> Result<(), E>,
) -> ControlledResult<(Vec<DecodedPredicate>, Vec<Vec<u32>>), E> {
    let total = fragments
        .iter()
        .try_fold(0_usize, |count, fragment| {
            count.checked_add(fragment.predicates.len())
        })
        .ok_or_else(|| {
            PermanentProgramError::Encoded(EncodedValidationError::resource(
                "permanent-program predicate count overflowed",
            ))
        })?;
    Budget::count(
        total,
        budget.limits.max_predicates,
        "source predicate count",
    )
    .map_err(PermanentProgramError::Encoded)?;
    let mut maps = fragments
        .iter()
        .map(|fragment| vec![u32::MAX; fragment.predicates.len()])
        .collect::<Vec<_>>();
    let remap_bytes = maps
        .capacity()
        .saturating_mul(size_of::<Vec<u32>>())
        .saturating_add(
            maps.iter()
                .map(|values| values.capacity().saturating_mul(size_of::<u32>()))
                .sum::<usize>(),
        );
    budget
        .claim_temporary(remap_bytes)
        .map_err(PermanentProgramError::Encoded)?;
    let mut pending = Vec::<PendingPredicate>::new();
    pending.try_reserve_exact(total).map_err(|_| {
        PermanentProgramError::Encoded(EncodedValidationError::resource(
            "permanent-program predicate staging allocation failed",
        ))
    })?;
    budget
        .claim_temporary(
            pending
                .capacity()
                .saturating_mul(size_of::<PendingPredicate>()),
        )
        .map_err(PermanentProgramError::Encoded)?;
    for (fragment_index, fragment) in fragments.iter_mut().enumerate() {
        let source_capacity = fragment
            .predicates
            .capacity()
            .saturating_mul(size_of::<DecodedPredicate>());
        let keys =
            predicate_keys(&fragment.predicates, budget).map_err(PermanentProgramError::Encoded)?;
        let key_vector_bytes = keys.capacity().saturating_mul(size_of::<Vec<u8>>());
        for (index, (predicate, key)) in std::mem::take(&mut fragment.predicates)
            .into_iter()
            .zip(keys)
            .enumerate()
        {
            if index % 256 == 0 {
                poll("permanent-program-predicate").map_err(PermanentProgramError::Control)?;
            }
            pending.push(PendingPredicate {
                key,
                value: predicate,
                fragment: fragment_index,
                local_id: index,
            });
            budget
                .claim_work(1)
                .map_err(PermanentProgramError::Encoded)?;
        }
        budget
            .release_temporary(key_vector_bytes)
            .map_err(PermanentProgramError::Encoded)?;
        budget
            .release(source_capacity)
            .map_err(PermanentProgramError::Encoded)?;
    }
    pending.sort_by(|left, right| left.key.cmp(&right.key));
    budget
        .claim_work(pending.len())
        .map_err(PermanentProgramError::Encoded)?;
    let pending_capacity = pending
        .capacity()
        .saturating_mul(size_of::<PendingPredicate>());
    let mut selected = Vec::<PendingPredicate>::new();
    selected.try_reserve_exact(pending.len()).map_err(|_| {
        PermanentProgramError::Encoded(EncodedValidationError::resource(
            "permanent-program predicate selection allocation failed",
        ))
    })?;
    budget
        .claim_temporary(
            selected
                .capacity()
                .saturating_mul(size_of::<PendingPredicate>()),
        )
        .map_err(PermanentProgramError::Encoded)?;
    for candidate in pending {
        let identifier = if let Some(known) = selected.last() {
            if known.key == candidate.key {
                if !same_predicate_shape(known, &candidate) {
                    return Err(PermanentProgramError::Encoded(
                        EncodedValidationError::invariant(
                            "equal permanent-program predicate keys have conflicting payloads",
                        ),
                    ));
                }
                u32::try_from(selected.len() - 1).map_err(|_| {
                    PermanentProgramError::Encoded(EncodedValidationError::resource(
                        "permanent-program predicate ID exceeds u32",
                    ))
                })?
            } else {
                u32::try_from(selected.len()).map_err(|_| {
                    PermanentProgramError::Encoded(EncodedValidationError::resource(
                        "permanent-program predicate ID exceeds u32",
                    ))
                })?
            }
        } else {
            0
        };
        maps[candidate.fragment][candidate.local_id] = identifier;
        if usize::try_from(identifier).ok() == Some(selected.len()) {
            selected.push(candidate);
        } else {
            budget
                .release_temporary(candidate.key.capacity())
                .map_err(PermanentProgramError::Encoded)?;
            budget
                .release(predicate_nested_owned_bytes(&candidate.value))
                .map_err(PermanentProgramError::Encoded)?;
        }
    }
    budget
        .release_temporary(pending_capacity)
        .map_err(PermanentProgramError::Encoded)?;
    Budget::count(
        selected.len(),
        budget.limits.max_predicates,
        "predicate count",
    )
    .map_err(PermanentProgramError::Encoded)?;
    let mut predicates = Vec::new();
    predicates.try_reserve_exact(selected.len()).map_err(|_| {
        PermanentProgramError::Encoded(EncodedValidationError::resource(
            "permanent-program predicate output allocation failed",
        ))
    })?;
    budget
        .claim_owned(
            predicates
                .capacity()
                .saturating_mul(size_of::<DecodedPredicate>()),
        )
        .map_err(PermanentProgramError::Encoded)?;
    let selected_capacity = selected
        .capacity()
        .saturating_mul(size_of::<PendingPredicate>());
    for (identifier, candidate) in selected.into_iter().enumerate() {
        let mut value = candidate.value;
        value.predicate_id = u32::try_from(identifier).map_err(|_| {
            PermanentProgramError::Encoded(EncodedValidationError::resource(
                "permanent-program predicate ID exceeds u32",
            ))
        })?;
        value.filler_predicate_id = value
            .filler_predicate_id
            .map(|local| map_id(local, &maps[candidate.fragment], "filler predicate"))
            .transpose()
            .map_err(PermanentProgramError::Encoded)?;
        budget
            .release_temporary(candidate.key.capacity())
            .map_err(PermanentProgramError::Encoded)?;
        predicates.push(value);
    }
    budget
        .release_temporary(selected_capacity)
        .map_err(PermanentProgramError::Encoded)?;
    Ok((predicates, maps))
}

fn predicate_keys(
    predicates: &[DecodedPredicate],
    budget: &mut Budget,
) -> EncodedResult<Vec<Vec<u8>>> {
    let mut states = vec![0_u8; predicates.len()];
    let mut keys = vec![Vec::new(); predicates.len()];
    budget.claim_temporary(states.capacity())?;
    budget.claim_temporary(keys.capacity().saturating_mul(size_of::<Vec<u8>>()))?;
    for (index, predicate) in predicates.iter().enumerate() {
        if usize::try_from(predicate.predicate_id).ok() != Some(index) {
            return Err(EncodedValidationError::invariant(
                "fragment predicate IDs are not dense",
            ));
        }
        build_predicate_key(index, predicates, &mut states, &mut keys, budget)?;
    }
    budget.release_temporary(states.capacity())?;
    // The caller owns the key-vector buffer and each populated key allocation.
    Ok(keys)
}

fn build_predicate_key(
    index: usize,
    predicates: &[DecodedPredicate],
    states: &mut [u8],
    keys: &mut [Vec<u8>],
    budget: &mut Budget,
) -> EncodedResult<()> {
    match states[index] {
        2 => return Ok(()),
        1 => {
            return Err(EncodedValidationError::invariant(
                "fragment predicate filler graph contains a cycle",
            ))
        }
        _ => states[index] = 1,
    }
    let predicate = &predicates[index];
    let filler = if let Some(identifier) = predicate.filler_predicate_id {
        let filler_index = usize::try_from(identifier).map_err(|_| {
            EncodedValidationError::invariant("fragment filler predicate ID exceeds usize")
        })?;
        if filler_index >= predicates.len() || filler_index == index {
            return Err(EncodedValidationError::invariant(
                "fragment filler predicate is dangling or self-referential",
            ));
        }
        build_predicate_key(filler_index, predicates, states, keys, budget)?;
        let digest: [u8; 32] = Sha256::digest(&keys[filler_index]).into();
        Some(digest)
    } else {
        None
    };
    let mut key = Vec::<u8>::new();
    key.extend_from_slice(b"{\"annotation\":[");
    write_u32_values(&mut key, &predicate.annotation)?;
    key.extend_from_slice(b"],\"argument_sorts\":[");
    for (index, sort) in predicate.argument_sorts.iter().enumerate() {
        if index > 0 {
            key.push(b',');
        }
        write!(&mut key, "\"{}\"", term_sort_name(*sort)).map_err(|_| {
            EncodedValidationError::invariant("permanent-program predicate key write failed")
        })?;
    }
    key.extend_from_slice(b"],\"cardinality\":");
    write_option_u32(&mut key, predicate.cardinality)?;
    key.extend_from_slice(b",\"filler\":");
    if let Some(digest) = filler {
        key.push(b'"');
        write_hex(&mut key, &digest);
        key.push(b'"');
    } else {
        key.extend_from_slice(b"null");
    }
    key.extend_from_slice(b",\"internal_key\":");
    if let Some(value) = &predicate.internal_key {
        serde_json::to_writer(&mut key, value).map_err(|_| {
            EncodedValidationError::invariant(
                "permanent-program predicate internal key cannot be serialized",
            )
        })?;
    } else {
        key.extend_from_slice(b"null");
    }
    write!(
        &mut key,
        ",\"kind\":\"{}\",\"role_id\":",
        predicate_kind_name(predicate.kind)
    )
    .map_err(|_| {
        EncodedValidationError::invariant("permanent-program predicate key write failed")
    })?;
    write_option_u32(&mut key, predicate.role_id)?;
    key.extend_from_slice(b",\"symbol_id\":");
    write_option_u32(&mut key, predicate.symbol_id)?;
    key.push(b'}');
    budget.claim_temporary(key.capacity())?;
    budget.claim_work(1)?;
    keys[index] = key;
    states[index] = 2;
    Ok(())
}

fn same_predicate_shape(left: &PendingPredicate, right: &PendingPredicate) -> bool {
    left.key == right.key
        && left.value.kind == right.value.kind
        && left.value.argument_sorts == right.value.argument_sorts
        && left.value.symbol_id == right.value.symbol_id
        && left.value.role_id == right.value.role_id
        && left.value.cardinality == right.value.cardinality
        && left.value.annotation == right.value.annotation
        && left.value.internal_key == right.value.internal_key
}

fn freeze_provenance<E>(
    fragments: &mut [Fragment],
    budget: &mut Budget,
    poll: &mut impl FnMut(&'static str) -> Result<(), E>,
) -> ControlledResult<(Vec<DecodedProvenanceEntry>, Vec<Vec<u32>>), E> {
    let total = fragments
        .iter()
        .try_fold(0_usize, |count, fragment| {
            count.checked_add(fragment.provenance.len())
        })
        .ok_or_else(|| {
            PermanentProgramError::Encoded(EncodedValidationError::resource(
                "permanent-program provenance count overflowed",
            ))
        })?;
    let mut maps = fragments
        .iter()
        .map(|fragment| vec![u32::MAX; fragment.provenance.len()])
        .collect::<Vec<_>>();
    let remap_bytes = maps
        .capacity()
        .saturating_mul(size_of::<Vec<u32>>())
        .saturating_add(
            maps.iter()
                .map(|values| values.capacity().saturating_mul(size_of::<u32>()))
                .sum::<usize>(),
        );
    budget
        .claim_temporary(remap_bytes)
        .map_err(PermanentProgramError::Encoded)?;
    let mut pending = Vec::<PendingProvenance>::new();
    pending.try_reserve_exact(total).map_err(|_| {
        PermanentProgramError::Encoded(EncodedValidationError::resource(
            "permanent-program provenance staging allocation failed",
        ))
    })?;
    budget
        .claim_temporary(
            pending
                .capacity()
                .saturating_mul(size_of::<PendingProvenance>()),
        )
        .map_err(PermanentProgramError::Encoded)?;
    for (fragment_index, fragment) in fragments.iter_mut().enumerate() {
        let source_capacity = fragment
            .provenance
            .capacity()
            .saturating_mul(size_of::<DecodedProvenanceEntry>());
        for (index, entry) in std::mem::take(&mut fragment.provenance)
            .into_iter()
            .enumerate()
        {
            if index % 256 == 0 {
                poll("permanent-program-provenance-entry")
                    .map_err(PermanentProgramError::Control)?;
            }
            if usize::try_from(entry.provenance_id).ok() != Some(index)
                || entry.source_sha256.is_empty()
                || entry
                    .source_sha256
                    .windows(2)
                    .any(|pair| pair[0] >= pair[1])
            {
                return Err(PermanentProgramError::Encoded(
                    EncodedValidationError::invariant("fragment provenance is not canonical"),
                ));
            }
            pending.push(PendingProvenance {
                value: entry,
                fragment: fragment_index,
                local_id: index,
            });
            budget
                .claim_work(1)
                .map_err(PermanentProgramError::Encoded)?;
        }
        budget
            .release(source_capacity)
            .map_err(PermanentProgramError::Encoded)?;
    }
    Budget::count(
        total,
        budget.limits.max_provenance,
        "source provenance count",
    )
    .map_err(PermanentProgramError::Encoded)?;
    pending.sort_by(|left, right| {
        (left.value.source_sha256.as_slice(), left.value.generated)
            .cmp(&(right.value.source_sha256.as_slice(), right.value.generated))
    });
    let mut provenance = Vec::<DecodedProvenanceEntry>::new();
    provenance.try_reserve_exact(pending.len()).map_err(|_| {
        PermanentProgramError::Encoded(EncodedValidationError::resource(
            "permanent-program provenance allocation failed",
        ))
    })?;
    budget
        .claim_owned(
            provenance
                .capacity()
                .saturating_mul(size_of::<DecodedProvenanceEntry>()),
        )
        .map_err(PermanentProgramError::Encoded)?;
    let pending_capacity = pending
        .capacity()
        .saturating_mul(size_of::<PendingProvenance>());
    for candidate in pending {
        let known = provenance.last().is_some_and(|entry| {
            entry.source_sha256 == candidate.value.source_sha256
                && entry.generated == candidate.value.generated
        });
        let identifier = if known {
            u32::try_from(provenance.len() - 1).map_err(|_| {
                PermanentProgramError::Encoded(EncodedValidationError::resource(
                    "permanent-program provenance ID exceeds u32",
                ))
            })?
        } else {
            u32::try_from(provenance.len()).map_err(|_| {
                PermanentProgramError::Encoded(EncodedValidationError::resource(
                    "permanent-program provenance ID exceeds u32",
                ))
            })?
        };
        maps[candidate.fragment][candidate.local_id] = identifier;
        if known {
            budget
                .release(provenance_nested_owned_bytes(&candidate.value))
                .map_err(PermanentProgramError::Encoded)?;
        } else {
            let mut value = candidate.value;
            value.provenance_id = identifier;
            provenance.push(value);
        }
    }
    budget
        .release_temporary(pending_capacity)
        .map_err(PermanentProgramError::Encoded)?;
    Budget::count(
        provenance.len(),
        budget.limits.max_provenance,
        "provenance count",
    )
    .map_err(PermanentProgramError::Encoded)?;
    Ok((provenance, maps))
}

fn freeze_clauses<E>(
    fragments: &mut [Fragment],
    predicate_maps: &[Vec<u32>],
    provenance_maps: &[Vec<u32>],
    predicates: &[DecodedPredicate],
    provenance: &[DecodedProvenanceEntry],
    budget: &mut Budget,
    poll: &mut impl FnMut(&'static str) -> Result<(), E>,
) -> ControlledResult<(Vec<DecodedClause>, Vec<DecodedGroundAtom>), E> {
    let total = fragments
        .iter()
        .try_fold(0_usize, |count, fragment| {
            count.checked_add(fragment.clauses.len())
        })
        .ok_or_else(|| {
            PermanentProgramError::Encoded(EncodedValidationError::resource(
                "permanent-program clause count overflowed",
            ))
        })?;
    Budget::count(total, budget.limits.max_clauses, "source clause count")
        .map_err(PermanentProgramError::Encoded)?;
    let mut pending = Vec::<PendingClause>::new();
    pending.try_reserve_exact(total).map_err(|_| {
        PermanentProgramError::Encoded(EncodedValidationError::resource(
            "permanent-program clause staging allocation failed",
        ))
    })?;
    budget
        .claim_temporary(
            pending
                .capacity()
                .saturating_mul(size_of::<PendingClause>()),
        )
        .map_err(PermanentProgramError::Encoded)?;
    let mut promoted_facts = Vec::<DecodedGroundAtom>::new();
    promoted_facts.try_reserve_exact(total).map_err(|_| {
        PermanentProgramError::Encoded(EncodedValidationError::resource(
            "permanent-program promoted-fact allocation failed",
        ))
    })?;
    budget
        .claim_temporary(
            promoted_facts
                .capacity()
                .saturating_mul(size_of::<DecodedGroundAtom>()),
        )
        .map_err(PermanentProgramError::Encoded)?;
    for (fragment_index, fragment) in fragments.iter_mut().enumerate() {
        let source_capacity = fragment
            .clauses
            .capacity()
            .saturating_mul(size_of::<DecodedClause>());
        for (index, mut clause) in std::mem::take(&mut fragment.clauses)
            .into_iter()
            .enumerate()
        {
            if index % 64 == 0 {
                poll("permanent-program-clause").map_err(PermanentProgramError::Control)?;
            }
            if usize::try_from(clause.clause_id).ok() != Some(index) {
                return Err(PermanentProgramError::Encoded(
                    EncodedValidationError::invariant("fragment clause IDs are not dense"),
                ));
            }
            remap_atoms_in_place(&mut clause.body, &predicate_maps[fragment_index])
                .map_err(PermanentProgramError::Encoded)?;
            remap_atoms_in_place(&mut clause.head, &predicate_maps[fragment_index])
                .map_err(PermanentProgramError::Encoded)?;
            canonicalize_clause(&mut clause.body, &mut clause.head, predicates, budget)
                .map_err(PermanentProgramError::Encoded)?;
            if clause.body.iter().any(|atom| clause.head.contains(atom)) {
                budget
                    .release(clause_nested_owned_bytes(&clause))
                    .map_err(PermanentProgramError::Encoded)?;
                continue;
            }
            remap_ids_in_place(
                &mut clause.provenance_ids,
                &provenance_maps[fragment_index],
                "clause provenance",
            )
            .map_err(PermanentProgramError::Encoded)?;
            let obsolete_join = std::mem::take(&mut clause.join_order);
            budget
                .release(obsolete_join.capacity().saturating_mul(size_of::<u32>()))
                .map_err(PermanentProgramError::Encoded)?;
            if clause.body.is_empty()
                && !clause.head.is_empty()
                && clause.head.iter().all(|atom| {
                    atom.arguments
                        .iter()
                        .all(|term| !matches!(term, DecodedTerm::Variable { .. }))
                })
            {
                if clause.head.len() > 1 {
                    return Err(PermanentProgramError::Encoded(
                        EncodedValidationError::protocol(
                            "permanent-program ground disjunctions require an encoded disjunction phase",
                        ),
                    ));
                }
                let atom = clause.head.pop().ok_or_else(|| {
                    PermanentProgramError::Encoded(EncodedValidationError::invariant(
                        "permanent-program promoted ground fact disappeared",
                    ))
                })?;
                promoted_facts.push(DecodedGroundAtom {
                    predicate_id: atom.predicate_id,
                    arguments: atom.arguments,
                    provenance_ids: clause.provenance_ids,
                });
                budget
                    .release(
                        clause
                            .body
                            .capacity()
                            .saturating_mul(size_of::<DecodedAtom>())
                            .saturating_add(
                                clause
                                    .head
                                    .capacity()
                                    .saturating_mul(size_of::<DecodedAtom>()),
                            ),
                    )
                    .map_err(PermanentProgramError::Encoded)?;
                continue;
            }
            let key =
                rule_key(&clause.body, &clause.head).map_err(PermanentProgramError::Encoded)?;
            budget
                .claim_temporary(key.capacity())
                .map_err(PermanentProgramError::Encoded)?;
            pending.push(PendingClause { key, value: clause });
            budget
                .claim_work(1)
                .map_err(PermanentProgramError::Encoded)?;
        }
        budget
            .release(source_capacity)
            .map_err(PermanentProgramError::Encoded)?;
    }
    retain_complement_exclusions(&mut pending, predicates, provenance, budget)
        .map_err(PermanentProgramError::Encoded)?;
    pending.sort_by(|left, right| left.key.cmp(&right.key));
    let mut selected = Vec::<PendingClause>::new();
    selected.try_reserve_exact(pending.len()).map_err(|_| {
        PermanentProgramError::Encoded(EncodedValidationError::resource(
            "permanent-program clause selection allocation failed",
        ))
    })?;
    let selected_capacity = selected
        .capacity()
        .saturating_mul(size_of::<PendingClause>());
    budget
        .claim_temporary(selected_capacity)
        .map_err(PermanentProgramError::Encoded)?;
    let pending_capacity = pending
        .capacity()
        .saturating_mul(size_of::<PendingClause>());
    for candidate in pending {
        if let Some(known) = selected
            .last_mut()
            .filter(|known| known.key == candidate.key)
        {
            if known.value.body != candidate.value.body || known.value.head != candidate.value.head
            {
                return Err(PermanentProgramError::Encoded(
                    EncodedValidationError::invariant(
                        "equal permanent-program rule keys have conflicting clauses",
                    ),
                ));
            }
            let discarded_bytes = clause_nested_owned_bytes(&candidate.value);
            merge_sorted_ids(
                &mut known.value.provenance_ids,
                candidate.value.provenance_ids,
                budget,
            )
            .map_err(PermanentProgramError::Encoded)?;
            budget
                .release_temporary(candidate.key.capacity())
                .map_err(PermanentProgramError::Encoded)?;
            budget
                .release(discarded_bytes)
                .map_err(PermanentProgramError::Encoded)?;
        } else {
            selected.push(candidate);
        }
    }
    budget
        .release_temporary(pending_capacity)
        .map_err(PermanentProgramError::Encoded)?;
    Budget::count(selected.len(), budget.limits.max_clauses, "clause count")
        .map_err(PermanentProgramError::Encoded)?;
    let mut output = Vec::new();
    output.try_reserve_exact(selected.len()).map_err(|_| {
        PermanentProgramError::Encoded(EncodedValidationError::resource(
            "permanent-program clause output allocation failed",
        ))
    })?;
    budget
        .claim_owned(output.capacity().saturating_mul(size_of::<DecodedClause>()))
        .map_err(PermanentProgramError::Encoded)?;
    for (identifier, candidate) in selected.into_iter().enumerate() {
        let mut clause = candidate.value;
        clause.clause_id = u32::try_from(identifier).map_err(|_| {
            PermanentProgramError::Encoded(EncodedValidationError::resource(
                "permanent-program clause ID exceeds u32",
            ))
        })?;
        clause.join_order = plan_join_order(&clause.body, predicates, budget)
            .map_err(PermanentProgramError::Encoded)?;
        budget
            .release_temporary(candidate.key.capacity())
            .map_err(PermanentProgramError::Encoded)?;
        output.push(clause);
    }
    budget
        .release_temporary(selected_capacity)
        .map_err(PermanentProgramError::Encoded)?;
    Ok((output, promoted_facts))
}

fn retain_complement_exclusions(
    pending: &mut Vec<PendingClause>,
    predicates: &[DecodedPredicate],
    provenance: &[DecodedProvenanceEntry],
    budget: &mut Budget,
) -> EncodedResult<()> {
    let builtin_digest: [u8; 32] = Sha256::digest(BUILTIN_PROVENANCE_INPUT).into();
    let builtin_provenance = provenance
        .iter()
        .find(|entry| entry.generated && entry.source_sha256.as_slice() == [builtin_digest])
        .map(|entry| entry.provenance_id)
        .ok_or_else(|| {
            EncodedValidationError::invariant("permanent-program provenance has no built-in entry")
        })?;
    for negative in predicates {
        let positive_kind = match negative.kind {
            PredicateKind::NegatedConcept => PredicateKind::Concept,
            PredicateKind::NegatedNominal => PredicateKind::Nominal,
            PredicateKind::NegatedObjectRole => PredicateKind::ObjectRole,
            PredicateKind::NegatedDataRole => PredicateKind::DataRole,
            PredicateKind::NegatedDataRange => PredicateKind::DataRange,
            _ => continue,
        };
        let positive = predicates
            .iter()
            .find(|candidate| {
                candidate.kind == positive_kind
                    && candidate.argument_sorts == negative.argument_sorts
                    && candidate.symbol_id == negative.symbol_id
                    && candidate.role_id == negative.role_id
                    && candidate.annotation == negative.annotation
                    && candidate.internal_key == negative.internal_key
            })
            .ok_or_else(|| {
                EncodedValidationError::invariant(
                    "permanent-program negative predicate has no positive complement",
                )
            })?;
        let mut body = Vec::<DecodedAtom>::new();
        body.try_reserve_exact(2).map_err(|_| {
            EncodedValidationError::resource(
                "permanent-program complement-clause allocation failed",
            )
        })?;
        budget.claim_owned(body.capacity().saturating_mul(size_of::<DecodedAtom>()))?;
        for predicate in [positive, negative] {
            let mut arguments = Vec::new();
            arguments
                .try_reserve_exact(predicate.argument_sorts.len())
                .map_err(|_| {
                    EncodedValidationError::resource(
                        "permanent-program complement-atom allocation failed",
                    )
                })?;
            budget.claim_owned(
                arguments
                    .capacity()
                    .saturating_mul(size_of::<DecodedTerm>()),
            )?;
            for (index, sort) in predicate.argument_sorts.iter().enumerate() {
                arguments.push(DecodedTerm::Variable {
                    index: u32::try_from(index).map_err(|_| {
                        EncodedValidationError::resource(
                            "permanent-program complement variable exceeds u32",
                        )
                    })?,
                    sort: *sort,
                });
            }
            body.push(DecodedAtom {
                predicate_id: predicate.predicate_id,
                arguments,
            });
        }
        let mut provenance_ids = Vec::new();
        provenance_ids.try_reserve_exact(1).map_err(|_| {
            EncodedValidationError::resource(
                "permanent-program complement provenance allocation failed",
            )
        })?;
        budget.claim_owned(provenance_ids.capacity().saturating_mul(size_of::<u32>()))?;
        provenance_ids.push(builtin_provenance);
        let mut clause = DecodedClause {
            clause_id: 0,
            body,
            head: Vec::new(),
            provenance_ids,
            join_order: Vec::new(),
        };
        canonicalize_clause(&mut clause.body, &mut clause.head, predicates, budget)?;
        let key = rule_key(&clause.body, &clause.head)?;
        budget.claim_temporary(key.capacity())?;
        push_counted(pending, PendingClause { key, value: clause }, budget)?;
    }
    Ok(())
}

fn freeze_facts<E>(
    fragments: &mut [Fragment],
    mut promoted_facts: Vec<DecodedGroundAtom>,
    predicate_maps: &[Vec<u32>],
    provenance_maps: &[Vec<u32>],
    predicates: &[DecodedPredicate],
    budget: &mut Budget,
    poll: &mut impl FnMut(&'static str) -> Result<(), E>,
) -> ControlledResult<(Vec<DecodedGroundAtom>, Vec<DecodedGroundAtom>), E> {
    let total = fragments
        .iter()
        .try_fold(0_usize, |count, fragment| {
            count
                .checked_add(fragment.positive_facts.len())
                .and_then(|value| value.checked_add(fragment.negative_facts.len()))
        })
        .ok_or_else(|| {
            PermanentProgramError::Encoded(EncodedValidationError::resource(
                "permanent-program fact count overflowed",
            ))
        })?;
    Budget::count(total, budget.limits.max_facts, "source fact count")
        .map_err(PermanentProgramError::Encoded)?;
    let pending_count = total.checked_add(promoted_facts.len()).ok_or_else(|| {
        PermanentProgramError::Encoded(EncodedValidationError::resource(
            "permanent-program promoted fact count overflowed",
        ))
    })?;
    let mut pending = Vec::<DecodedGroundAtom>::new();
    pending.try_reserve_exact(pending_count).map_err(|_| {
        PermanentProgramError::Encoded(EncodedValidationError::resource(
            "permanent-program fact staging allocation failed",
        ))
    })?;
    let pending_capacity = pending
        .capacity()
        .saturating_mul(size_of::<DecodedGroundAtom>());
    budget
        .claim_temporary(pending_capacity)
        .map_err(PermanentProgramError::Encoded)?;
    let promoted_capacity = promoted_facts
        .capacity()
        .saturating_mul(size_of::<DecodedGroundAtom>());
    pending.append(&mut promoted_facts);
    budget
        .release_temporary(promoted_capacity)
        .map_err(PermanentProgramError::Encoded)?;
    for (fragment_index, fragment) in fragments.iter_mut().enumerate() {
        let positive_capacity = fragment
            .positive_facts
            .capacity()
            .saturating_mul(size_of::<DecodedGroundAtom>());
        let negative_capacity = fragment
            .negative_facts
            .capacity()
            .saturating_mul(size_of::<DecodedGroundAtom>());
        for (expected_negative, (values, source_capacity)) in [
            (
                false,
                (
                    std::mem::take(&mut fragment.positive_facts),
                    positive_capacity,
                ),
            ),
            (
                true,
                (
                    std::mem::take(&mut fragment.negative_facts),
                    negative_capacity,
                ),
            ),
        ] {
            for (index, mut fact) in values.into_iter().enumerate() {
                if index % 256 == 0 {
                    poll("permanent-program-fact").map_err(PermanentProgramError::Control)?;
                }
                fact.predicate_id = map_id(
                    fact.predicate_id,
                    &predicate_maps[fragment_index],
                    "fact predicate",
                )
                .map_err(PermanentProgramError::Encoded)?;
                remap_ids_in_place(
                    &mut fact.provenance_ids,
                    &provenance_maps[fragment_index],
                    "fact provenance",
                )
                .map_err(PermanentProgramError::Encoded)?;
                let predicate = predicate_for(fact.predicate_id, predicates)?;
                if is_negative_kind(predicate.kind) != expected_negative {
                    return Err(PermanentProgramError::Encoded(
                        EncodedValidationError::invariant(
                            "fragment fact is stored in the wrong polarity partition",
                        ),
                    ));
                }
                pending.push(fact);
                budget
                    .claim_work(1)
                    .map_err(PermanentProgramError::Encoded)?;
            }
            budget
                .release(source_capacity)
                .map_err(PermanentProgramError::Encoded)?;
        }
    }
    pending.sort_by(compare_ground_identity);
    let mut merged = Vec::<DecodedGroundAtom>::new();
    merged.try_reserve_exact(pending.len()).map_err(|_| {
        PermanentProgramError::Encoded(EncodedValidationError::resource(
            "permanent-program fact merge allocation failed",
        ))
    })?;
    let merged_capacity = merged
        .capacity()
        .saturating_mul(size_of::<DecodedGroundAtom>());
    budget
        .claim_temporary(merged_capacity)
        .map_err(PermanentProgramError::Encoded)?;
    for fact in pending {
        if let Some(known) = merged.last_mut().filter(|known| {
            known.predicate_id == fact.predicate_id && known.arguments == fact.arguments
        }) {
            let discarded_bytes = ground_atom_nested_owned_bytes(&fact);
            merge_sorted_ids(&mut known.provenance_ids, fact.provenance_ids, budget)
                .map_err(PermanentProgramError::Encoded)?;
            budget
                .release(discarded_bytes)
                .map_err(PermanentProgramError::Encoded)?;
        } else {
            merged.push(fact);
        }
    }
    budget
        .release_temporary(pending_capacity)
        .map_err(PermanentProgramError::Encoded)?;
    Budget::count(merged.len(), budget.limits.max_facts, "fact count")
        .map_err(PermanentProgramError::Encoded)?;
    let mut positive = Vec::new();
    let mut negative = Vec::new();
    for value in merged {
        let predicate = predicate_for(value.predicate_id, predicates)?;
        if is_negative_kind(predicate.kind) {
            push_counted(&mut negative, value, budget).map_err(PermanentProgramError::Encoded)?;
        } else {
            push_counted(&mut positive, value, budget).map_err(PermanentProgramError::Encoded)?;
        }
    }
    budget
        .release_temporary(merged_capacity)
        .map_err(PermanentProgramError::Encoded)?;
    sort_ground_atoms(&mut positive, budget).map_err(PermanentProgramError::Encoded)?;
    sort_ground_atoms(&mut negative, budget).map_err(PermanentProgramError::Encoded)?;
    Ok((positive, negative))
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct RepresentableExpressivityEvidence {
    source: ProgramSemanticEvidence,
    unknown_datatypes: bool,
}

fn derive_representable_expressivity(
    predicates: &[DecodedPredicate],
    clauses: &[DecodedClause],
    positive_facts: &[DecodedGroundAtom],
    negative_facts: &[DecodedGroundAtom],
    provenance: &[DecodedProvenanceEntry],
    roles: &crate::input_wire::DecodedRoleModel,
    evidence: RepresentableExpressivityEvidence,
) -> EncodedResult<DecodedExpressivity> {
    let RepresentableExpressivityEvidence {
        source,
        unknown_datatypes,
    } = evidence;
    let nominals = predicates.iter().any(|predicate| {
        matches!(
            predicate.kind,
            PredicateKind::Nominal | PredicateKind::NegatedNominal
        )
    });
    let number_restrictions = predicates.iter().any(|predicate| {
        matches!(
            predicate.kind,
            PredicateKind::AtLeastObject
                | PredicateKind::AtLeastData
                | PredicateKind::AnnotatedEquality
        )
    });
    let mut keys = false;
    for clause in clauses {
        let mut named_individual = false;
        let mut ordering_guard = false;
        for atom in &clause.body {
            match predicate_for(atom.predicate_id, predicates)?.kind {
                PredicateKind::NamedIndividual => named_individual = true,
                PredicateKind::OrderingGuard => ordering_guard = true,
                _ => {}
            }
        }
        let mut equality = false;
        for atom in &clause.head {
            if predicate_for(atom.predicate_id, predicates)?.kind == PredicateKind::Equality {
                equality = true;
                break;
            }
        }
        if named_individual && ordering_guard && equality {
            keys = true;
            break;
        }
    }
    let non_horn = clauses.iter().any(|clause| clause.head.len() > 1);
    let datatypes = predicates.iter().any(|predicate| {
        matches!(
            predicate.kind,
            PredicateKind::DataRange | PredicateKind::NegatedDataRange | PredicateKind::AtLeastData
        ) || (matches!(
            predicate.kind,
            PredicateKind::DataRole | PredicateKind::NegatedDataRole
        ) && predicate.role_id != Some(roles.bottom_data_property_id))
    });
    let abox = positive_facts
        .iter()
        .chain(negative_facts)
        .any(|fact| has_source_provenance(&fact.provenance_ids, provenance));
    let mut bottom_properties = false;
    for clause in clauses {
        if !has_source_provenance(&clause.provenance_ids, provenance) {
            continue;
        }
        for atom in clause.body.iter().chain(&clause.head) {
            let predicate = predicate_for(atom.predicate_id, predicates)?;
            if (matches!(
                predicate.kind,
                PredicateKind::ObjectRole | PredicateKind::NegatedObjectRole
            ) && predicate.role_id == Some(roles.bottom_object_role_id))
                || (matches!(
                    predicate.kind,
                    PredicateKind::DataRole | PredicateKind::NegatedDataRole
                ) && predicate.role_id == Some(roles.bottom_data_property_id))
            {
                bottom_properties = true;
                break;
            }
        }
        if bottom_properties {
            break;
        }
    }
    Ok(DecodedExpressivity {
        inverse_roles: source.inverse_roles,
        nominals: source.nominals || nominals,
        datatypes,
        unknown_datatypes,
        complex_roles: !roles.complex_inclusions.is_empty() || !roles.automata.is_empty(),
        number_restrictions: source.number_restrictions || number_restrictions,
        keys: source.keys || keys,
        non_horn,
        bottom_properties: source.bottom_properties || bottom_properties,
        abox: source.abox || abox,
    })
}

fn has_source_provenance(ids: &[u32], provenance: &[DecodedProvenanceEntry]) -> bool {
    ids.iter().any(|identifier| {
        provenance
            .get(usize::try_from(*identifier).unwrap_or(usize::MAX))
            .is_some_and(|entry| !entry.generated)
    })
}

fn remap_atoms_in_place(atoms: &mut [DecodedAtom], mapping: &[u32]) -> EncodedResult<()> {
    for atom in atoms {
        atom.predicate_id = map_id(atom.predicate_id, mapping, "atom predicate")?;
    }
    Ok(())
}

fn remap_ids_in_place(
    values: &mut Vec<u32>,
    mapping: &[u32],
    name: &'static str,
) -> EncodedResult<()> {
    for value in values.iter_mut() {
        *value = map_id(*value, mapping, name)?;
    }
    values.sort_unstable();
    values.dedup();
    if values.is_empty() {
        return Err(EncodedValidationError::invariant(format!(
            "permanent-program {name} is empty"
        )));
    }
    Ok(())
}

fn map_id(value: u32, mapping: &[u32], name: &'static str) -> EncodedResult<u32> {
    mapping
        .get(
            usize::try_from(value).map_err(|_| {
                EncodedValidationError::invariant(format!("{name} ID exceeds usize"))
            })?,
        )
        .copied()
        .ok_or_else(|| EncodedValidationError::invariant(format!("{name} ID is dangling")))
}

fn release_remap_storage(maps: Vec<Vec<u32>>, budget: &mut Budget) -> EncodedResult<()> {
    let bytes = maps
        .capacity()
        .saturating_mul(size_of::<Vec<u32>>())
        .saturating_add(
            maps.iter()
                .map(|values| values.capacity().saturating_mul(size_of::<u32>()))
                .sum::<usize>(),
        );
    drop(maps);
    budget.release_temporary(bytes)
}

fn predicate_for(
    identifier: u32,
    predicates: &[DecodedPredicate],
) -> EncodedResult<&DecodedPredicate> {
    predicates
        .get(
            usize::try_from(identifier)
                .map_err(|_| EncodedValidationError::invariant("predicate ID exceeds usize"))?,
        )
        .ok_or_else(|| EncodedValidationError::invariant("predicate ID is dangling"))
}

fn merge_sorted_ids(
    destination: &mut Vec<u32>,
    mut source: Vec<u32>,
    budget: &mut Budget,
) -> EncodedResult<()> {
    let before = destination.capacity().saturating_mul(size_of::<u32>());
    destination.append(&mut source);
    destination.sort_unstable();
    destination.dedup();
    let after = destination.capacity().saturating_mul(size_of::<u32>());
    budget.resize_allocation(before, after)
}

fn push_counted<T>(values: &mut Vec<T>, value: T, budget: &mut Budget) -> EncodedResult<()> {
    let before = values.capacity().saturating_mul(size_of::<T>());
    values.try_reserve(1).map_err(|_| {
        EncodedValidationError::resource("permanent-program vector allocation failed")
    })?;
    let after = values.capacity().saturating_mul(size_of::<T>());
    budget.resize_allocation(before, after)?;
    values.push(value);
    Ok(())
}

fn canonicalize_clause(
    body: &mut Vec<DecodedAtom>,
    head: &mut Vec<DecodedAtom>,
    predicates: &[DecodedPredicate],
    budget: &mut Budget,
) -> EncodedResult<()> {
    for atom in body.iter_mut().chain(head.iter_mut()) {
        canonicalize_symmetric_atom(atom, predicates)?;
    }
    sort_atoms_alpha(body, budget)?;
    sort_atoms_alpha(head, budget)?;
    let mut variables = Vec::<(u32, TermSort)>::new();
    for atom in body.iter().chain(head.iter()) {
        for term in &atom.arguments {
            if let DecodedTerm::Variable { index, sort } = term {
                if !variables.contains(&(*index, *sort)) {
                    push_counted(&mut variables, (*index, *sort), budget)?;
                }
            }
        }
    }
    let maximum_passes = variables.len().checked_add(2).ok_or_else(|| {
        EncodedValidationError::resource(
            "permanent-program alpha-canonicalization bound overflowed",
        )
    })?;
    let variable_storage = variables
        .capacity()
        .saturating_mul(size_of::<(u32, TermSort)>());
    let variable_count = variables.len();
    let mut seen = Vec::<[u8; 32]>::new();
    for _ in 0..maximum_passes.max(2) {
        let state = rule_key(body, head)?;
        budget.claim_temporary(state.capacity())?;
        let digest: [u8; 32] = Sha256::digest(&state).into();
        if seen.contains(&digest) {
            budget.release_temporary(state.capacity())?;
            budget.release_temporary(variable_storage)?;
            let seen_storage = seen.capacity().saturating_mul(size_of::<[u8; 32]>());
            budget.release_temporary(seen_storage)?;
            return Err(EncodedValidationError::invariant(
                "permanent-program alpha-canonicalization entered a cycle",
            ));
        }
        push_counted(&mut seen, digest, budget)?;
        let mut mapping = Vec::<((u32, TermSort), u32)>::new();
        for atom in body.iter().chain(head.iter()) {
            for term in &atom.arguments {
                let DecodedTerm::Variable { index, sort } = term else {
                    continue;
                };
                if mapping.iter().all(|(known, _)| known != &(*index, *sort)) {
                    let target = u32::try_from(mapping.len()).map_err(|_| {
                        EncodedValidationError::resource(
                            "permanent-program variable ID exceeds u32",
                        )
                    })?;
                    push_counted(&mut mapping, ((*index, *sort), target), budget)?;
                }
            }
        }
        for atom in body.iter_mut().chain(head.iter_mut()) {
            for term in &mut atom.arguments {
                if let DecodedTerm::Variable { index, sort } = term {
                    *index = mapping
                        .iter()
                        .find_map(|(source, target)| {
                            (*source == (*index, *sort)).then_some(*target)
                        })
                        .ok_or_else(|| {
                            EncodedValidationError::invariant(
                                "permanent-program variable mapping is incomplete",
                            )
                        })?;
                }
            }
            canonicalize_symmetric_atom(atom, predicates)?;
        }
        let mapping_storage = mapping
            .capacity()
            .saturating_mul(size_of::<((u32, TermSort), u32)>());
        drop(mapping);
        budget.release_temporary(mapping_storage)?;
        sort_atoms_canonical(body, budget)?;
        sort_atoms_canonical(head, budget)?;
        let next = rule_key(body, head)?;
        budget.claim_temporary(next.capacity())?;
        let first_occurrence_dense = first_occurrence_dense(body, head, variable_count, budget)?;
        let stable = state == next && first_occurrence_dense;
        budget.release_temporary(state.capacity())?;
        budget.release_temporary(next.capacity())?;
        if stable {
            drop(variables);
            budget.release_temporary(variable_storage)?;
            let seen_storage = seen.capacity().saturating_mul(size_of::<[u8; 32]>());
            drop(seen);
            budget.release_temporary(seen_storage)?;
            return Ok(());
        }
        budget.claim_work(1)?;
    }
    drop(variables);
    budget.release_temporary(variable_storage)?;
    let seen_storage = seen.capacity().saturating_mul(size_of::<[u8; 32]>());
    drop(seen);
    budget.release_temporary(seen_storage)?;
    Err(EncodedValidationError::invariant(
        "permanent-program alpha-canonicalization exceeded its bounded passes",
    ))
}

fn first_occurrence_dense(
    body: &[DecodedAtom],
    head: &[DecodedAtom],
    variable_count: usize,
    budget: &mut Budget,
) -> EncodedResult<bool> {
    let mut order = Vec::<u32>::new();
    for atom in body.iter().chain(head) {
        for term in &atom.arguments {
            if let DecodedTerm::Variable { index, .. } = term {
                if !order.contains(index) {
                    push_counted(&mut order, *index, budget)?;
                }
            }
        }
    }
    let dense = order.len() == variable_count
        && order
            .iter()
            .enumerate()
            .all(|(index, value)| usize::try_from(*value).ok() == Some(index));
    let storage = order.capacity().saturating_mul(size_of::<u32>());
    drop(order);
    budget.release_temporary(storage)?;
    Ok(dense)
}

fn canonicalize_symmetric_atom(
    atom: &mut DecodedAtom,
    predicates: &[DecodedPredicate],
) -> EncodedResult<()> {
    let predicate = predicate_for(atom.predicate_id, predicates)?;
    let pair = match predicate.kind {
        PredicateKind::AnnotatedEquality => Some((0, 1)),
        PredicateKind::Equality | PredicateKind::Inequality | PredicateKind::OrderingGuard => {
            Some((0, 1))
        }
        _ => None,
    };
    if let Some((left, right)) = pair {
        if atom.arguments.len() <= right {
            return Err(EncodedValidationError::invariant(
                "permanent-program symmetric atom has the wrong arity",
            ));
        }
        if compare_terms(&atom.arguments[right], &atom.arguments[left]) == Ordering::Less {
            atom.arguments.swap(left, right);
        }
    }
    Ok(())
}

fn sort_atoms_alpha(atoms: &mut Vec<DecodedAtom>, budget: &mut Budget) -> EncodedResult<()> {
    atoms.sort_by(|left, right| {
        left.predicate_id
            .cmp(&right.predicate_id)
            .then_with(|| compare_term_slices(&left.arguments, &right.arguments))
    });
    dedup_atoms(atoms, budget)
}

fn sort_atoms_canonical(atoms: &mut Vec<DecodedAtom>, budget: &mut Budget) -> EncodedResult<()> {
    let mut keyed = Vec::<(Vec<u8>, DecodedAtom)>::new();
    keyed.try_reserve_exact(atoms.len()).map_err(|_| {
        EncodedValidationError::resource("permanent-program atom-key allocation failed")
    })?;
    let keyed_storage = keyed
        .capacity()
        .saturating_mul(size_of::<(Vec<u8>, DecodedAtom)>());
    budget.claim_temporary(keyed_storage)?;
    for atom in atoms.drain(..) {
        let key = atom_key(&atom)?;
        budget.claim_temporary(key.capacity())?;
        keyed.push((key, atom));
    }
    keyed.sort_by(|left, right| left.0.cmp(&right.0));
    let mut previous = None::<Vec<u8>>;
    for (key, atom) in keyed {
        if previous.as_ref().is_some_and(|known| known == &key) {
            budget.release(atom_nested_owned_bytes(&atom))?;
            budget.release_temporary(key.capacity())?;
        } else {
            if let Some(known) = previous.replace(key) {
                budget.release_temporary(known.capacity())?;
            }
            atoms.push(atom);
        }
    }
    if let Some(known) = previous {
        budget.release_temporary(known.capacity())?;
    }
    budget.release_temporary(keyed_storage)
}

fn dedup_atoms(atoms: &mut Vec<DecodedAtom>, budget: &mut Budget) -> EncodedResult<()> {
    let mut index = 1;
    while index < atoms.len() {
        if atoms[index - 1] == atoms[index] {
            let duplicate = atoms.remove(index);
            budget.release(atom_nested_owned_bytes(&duplicate))?;
        } else {
            index += 1;
        }
    }
    Ok(())
}

fn compare_ground_identity(left: &DecodedGroundAtom, right: &DecodedGroundAtom) -> Ordering {
    left.predicate_id
        .cmp(&right.predicate_id)
        .then_with(|| compare_term_slices(&left.arguments, &right.arguments))
}

fn compare_term_slices(left: &[DecodedTerm], right: &[DecodedTerm]) -> Ordering {
    for (left, right) in left.iter().zip(right) {
        let order = compare_terms(left, right);
        if order != Ordering::Equal {
            return order;
        }
    }
    left.len().cmp(&right.len())
}

fn compare_terms(left: &DecodedTerm, right: &DecodedTerm) -> Ordering {
    const fn key(value: &DecodedTerm) -> (u8, u8, u32, u32) {
        match value {
            DecodedTerm::Variable {
                index,
                sort: TermSort::Data,
            } => (0, 0, *index, 0),
            DecodedTerm::Variable {
                index,
                sort: TermSort::Object,
            } => (0, 1, *index, 0),
            DecodedTerm::Individual { individual_id } => (1, 0, *individual_id, 0),
            DecodedTerm::Data {
                source_literal_id,
                data_identity_id,
            } => (2, 0, *data_identity_id, *source_literal_id),
        }
    }
    key(left).cmp(&key(right))
}

fn sort_ground_atoms(facts: &mut Vec<DecodedGroundAtom>, budget: &mut Budget) -> EncodedResult<()> {
    let mut keyed = Vec::<(Vec<u8>, DecodedGroundAtom)>::new();
    keyed.try_reserve_exact(facts.len()).map_err(|_| {
        EncodedValidationError::resource("permanent-program fact-key allocation failed")
    })?;
    let keyed_storage = keyed
        .capacity()
        .saturating_mul(size_of::<(Vec<u8>, DecodedGroundAtom)>());
    budget.claim_temporary(keyed_storage)?;
    for fact in facts.drain(..) {
        let key = ground_atom_key(&fact)?;
        budget.claim_temporary(key.capacity())?;
        keyed.push((key, fact));
    }
    keyed.sort_by(|left, right| left.0.cmp(&right.0));
    for (key, value) in keyed {
        budget.release_temporary(key.capacity())?;
        facts.push(value);
    }
    budget.release_temporary(keyed_storage)
}

fn plan_join_order(
    body: &[DecodedAtom],
    predicates: &[DecodedPredicate],
    budget: &mut Budget,
) -> EncodedResult<Vec<u32>> {
    let mut remaining = vec![true; body.len()];
    budget.claim_temporary(remaining.capacity().saturating_mul(size_of::<bool>()))?;
    let mut bound = Vec::<(u32, TermSort)>::new();
    let atom_keys = body
        .iter()
        .map(atom_key)
        .collect::<EncodedResult<Vec<_>>>()?;
    budget.claim_temporary(atom_keys.capacity().saturating_mul(size_of::<Vec<u8>>()))?;
    for key in &atom_keys {
        budget.claim_temporary(key.capacity())?;
    }
    let mut result = Vec::new();
    result.try_reserve_exact(body.len()).map_err(|_| {
        EncodedValidationError::resource("permanent-program join-order allocation failed")
    })?;
    budget.claim_owned(result.capacity().saturating_mul(size_of::<u32>()))?;
    while result.len() < body.len() {
        let mut selected = None::<(usize, (u8, u8, usize, usize, &[u8]))>;
        for (index, atom) in body.iter().enumerate() {
            if !remaining[index] {
                continue;
            }
            budget.claim_work(1)?;
            let predicate = predicates
                .get(usize::try_from(atom.predicate_id).unwrap_or(usize::MAX))
                .ok_or_else(|| {
                    EncodedValidationError::invariant(
                        "permanent-program join predicate is dangling",
                    )
                })?;
            let mut shared = 0_usize;
            let mut new = 0_usize;
            for (term_index, term) in atom.arguments.iter().enumerate() {
                let DecodedTerm::Variable { index, sort } = term else {
                    continue;
                };
                if atom.arguments[..term_index].iter().any(|known| {
                    matches!(
                        known,
                        DecodedTerm::Variable {
                            index: known_index,
                            sort: known_sort
                        } if known_index == index && known_sort == sort
                    )
                }) {
                    continue;
                }
                if bound.contains(&(*index, *sort)) {
                    shared += 1;
                } else {
                    new += 1;
                }
            }
            let filter = matches!(
                predicate.kind,
                PredicateKind::Equality | PredicateKind::Inequality | PredicateKind::OrderingGuard
            );
            let rank = (
                u8::from(filter && new > 0),
                u8::from(shared == 0),
                new,
                atom.arguments.len(),
                atom_keys[index].as_slice(),
            );
            if selected.as_ref().is_none_or(|(_, known)| rank < *known) {
                selected = Some((index, rank));
            }
        }
        let index = selected.map(|(index, _)| index).ok_or_else(|| {
            EncodedValidationError::invariant("permanent-program join planning lost an atom")
        })?;
        remaining[index] = false;
        result.push(u32::try_from(index).map_err(|_| {
            EncodedValidationError::resource("permanent-program join index exceeds u32")
        })?);
        for term in &body[index].arguments {
            if let DecodedTerm::Variable { index, sort } = term {
                if !bound.contains(&(*index, *sort)) {
                    push_counted(&mut bound, (*index, *sort), budget)?;
                }
            }
        }
    }
    budget.release_temporary(remaining.capacity().saturating_mul(size_of::<bool>()))?;
    budget.release_temporary(
        bound
            .capacity()
            .saturating_mul(size_of::<(u32, TermSort)>()),
    )?;
    for key in &atom_keys {
        budget.release_temporary(key.capacity())?;
    }
    budget.release_temporary(atom_keys.capacity().saturating_mul(size_of::<Vec<u8>>()))?;
    Ok(result)
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

fn write_option_u32(output: &mut Vec<u8>, value: Option<u32>) -> EncodedResult<()> {
    if let Some(value) = value {
        write!(output, "{value}").map_err(|_| {
            EncodedValidationError::invariant("permanent-program integer write failed")
        })?;
    } else {
        output.extend_from_slice(b"null");
    }
    Ok(())
}

fn write_u32_values(output: &mut Vec<u8>, values: &[u32]) -> EncodedResult<()> {
    for (index, value) in values.iter().enumerate() {
        if index > 0 {
            output.push(b',');
        }
        write!(output, "{value}").map_err(|_| {
            EncodedValidationError::invariant("permanent-program integer write failed")
        })?;
    }
    Ok(())
}

fn write_hex(output: &mut Vec<u8>, value: &[u8]) {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    for byte in value {
        output.push(HEX[usize::from(byte >> 4)]);
        output.push(HEX[usize::from(byte & 0x0F)]);
    }
}

fn atom_key(atom: &DecodedAtom) -> EncodedResult<Vec<u8>> {
    let mut output = Vec::new();
    write_atom_json(&mut output, atom)?;
    Ok(output)
}

fn ground_atom_key(atom: &DecodedGroundAtom) -> EncodedResult<Vec<u8>> {
    let mut output = Vec::new();
    output.extend_from_slice(b"{\"arguments\":[");
    write_terms_json(&mut output, &atom.arguments)?;
    write!(
        &mut output,
        "],\"predicate_id\":{},\"provenance_ids\":[",
        atom.predicate_id
    )
    .map_err(|_| {
        EncodedValidationError::invariant("permanent-program ground-atom key write failed")
    })?;
    write_u32_values(&mut output, &atom.provenance_ids)?;
    output.extend_from_slice(b"],\"schema_version\":1,\"type\":\"GroundAtom\"}");
    Ok(output)
}

fn write_atom_json(output: &mut Vec<u8>, atom: &DecodedAtom) -> EncodedResult<()> {
    output.extend_from_slice(b"{\"arguments\":[");
    write_terms_json(output, &atom.arguments)?;
    write!(
        output,
        "],\"predicate_id\":{},\"schema_version\":1,\"type\":\"Atom\"}}",
        atom.predicate_id
    )
    .map_err(|_| EncodedValidationError::invariant("permanent-program atom key write failed"))?;
    Ok(())
}

fn write_terms_json(output: &mut Vec<u8>, terms: &[DecodedTerm]) -> EncodedResult<()> {
    for (index, term) in terms.iter().enumerate() {
        if index > 0 {
            output.push(b',');
        }
        write_term_json(output, term)?;
    }
    Ok(())
}

fn write_term_json(output: &mut Vec<u8>, term: &DecodedTerm) -> EncodedResult<()> {
    match term {
        DecodedTerm::Variable { index, sort } => write!(
            output,
            "{{\"index\":{index},\"schema_version\":1,\"sort\":\"{}\",\"type\":\"Variable\"}}",
            term_sort_name(*sort)
        ),
        DecodedTerm::Individual { individual_id } => write!(
            output,
            "{{\"individual_id\":{individual_id},\"schema_version\":1,\"type\":\"IndividualTerm\"}}"
        ),
        DecodedTerm::Data {
            source_literal_id,
            data_identity_id,
        } => write!(
            output,
            "{{\"data_identity_id\":{data_identity_id},\"schema_version\":1,\"source_literal_id\":{source_literal_id},\"type\":\"DataConstant\"}}"
        ),
    }
    .map_err(|_| {
        EncodedValidationError::invariant("permanent-program term key write failed")
    })
}

fn rule_key(body: &[DecodedAtom], head: &[DecodedAtom]) -> EncodedResult<Vec<u8>> {
    let mut output = Vec::new();
    output.extend_from_slice(b"{\"body\":[");
    for (index, atom) in body.iter().enumerate() {
        if index > 0 {
            output.push(b',');
        }
        write_atom_json(&mut output, atom)?;
    }
    output.extend_from_slice(b"],\"head\":[");
    for (index, atom) in head.iter().enumerate() {
        if index > 0 {
            output.push(b',');
        }
        write_atom_json(&mut output, atom)?;
    }
    output.extend_from_slice(b"]}");
    Ok(output)
}

const fn is_negative_kind(kind: PredicateKind) -> bool {
    matches!(
        kind,
        PredicateKind::NegatedConcept
            | PredicateKind::NegatedNominal
            | PredicateKind::NegatedObjectRole
            | PredicateKind::NegatedDataRole
            | PredicateKind::NegatedDataRange
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn named_datatype_payload_is_canonical_json() {
        let payload = serde_json::to_string(&named_datatype_semantic_value(
            "http://www.w3.org/2001/XMLSchema#int",
            false,
        ))
        .unwrap();
        let value: serde_json::Value = serde_json::from_str(&payload).unwrap();
        assert_eq!(serde_json::to_string(&value).unwrap(), payload);
    }

    #[test]
    fn complemented_data_range_key_exposes_exact_operand() {
        let operand = [4_u8, 5, 6];
        assert_eq!(
            data_range_complement_operand_key(&[23, 1, 3, 4, 5, 6]),
            Some(operand.as_slice())
        );
        assert_ne!(
            data_range_complement_operand_key(&[23, 1, 3, 4, 5, 7]),
            Some(operand.as_slice())
        );
        assert_eq!(
            data_range_complement_operand_key(&[23, 1, 0x83, 0, 4, 5, 6]),
            None
        );
    }

    #[test]
    fn boolean_data_range_key_exposes_exact_operands() {
        let key = [21_u8, 6, 2, 1, 4, 1, 5];
        let (tag, operands) = data_range_boolean_operand_keys(&key).unwrap();
        assert_eq!(tag, DATA_INTERSECTION_OF_TAG);
        assert_eq!(operands, vec![&[4][..], &[5][..]]);
        assert!(data_range_boolean_operand_keys(&[22, 6, 1, 1, 4]).is_none());
        assert!(data_range_boolean_operand_keys(&[22, 6, 2, 1, 4, 1, 5, 0]).is_none());
    }

    #[test]
    fn enumeration_data_range_key_exposes_exact_literals() {
        let key = [24_u8, 6, 2, 1, 4, 2, 5, 6];
        assert_eq!(
            data_range_enumeration_literal_keys(&key),
            Some(vec![&[4][..], &[5, 6][..]])
        );
        assert!(data_range_enumeration_literal_keys(&[24, 6, 0]).is_none());
        assert!(data_range_enumeration_literal_keys(&[24, 6, 1, 1, 4, 0]).is_none());
    }

    #[test]
    fn datatype_restriction_key_exposes_exact_facets() {
        let facet = [20_u8, 1, 6, 1, 2, 3, b'i', b'r', b'i', 1, 1, 4];
        let mut key = vec![25_u8, 1, 1, 2, 6, 1, 12];
        key.extend_from_slice(&facet);
        let restriction = datatype_restriction_key(&key).unwrap();
        assert_eq!(restriction.datatype_key, &[2]);
        assert_eq!(
            restriction.facets,
            vec![FacetRestrictionKey {
                facet_iri: "iri",
                literal_key: &[4],
            }]
        );
        assert!(datatype_restriction_key(&[25, 1, 1, 2, 6, 0]).is_none());
        key.push(0);
        assert!(datatype_restriction_key(&key).is_none());
    }

    #[test]
    fn predicate_key_uses_recursive_filler_digest() -> EncodedResult<()> {
        let predicates = vec![
            DecodedPredicate {
                predicate_id: 0,
                kind: PredicateKind::Concept,
                argument_sorts: vec![TermSort::Object],
                symbol_id: Some(0),
                role_id: None,
                cardinality: None,
                filler_predicate_id: None,
                annotation: Vec::new(),
                internal_key: None,
            },
            DecodedPredicate {
                predicate_id: 1,
                kind: PredicateKind::AtLeastObject,
                argument_sorts: vec![TermSort::Object],
                symbol_id: None,
                role_id: Some(0),
                cardinality: Some(1),
                filler_predicate_id: Some(0),
                annotation: Vec::new(),
                internal_key: None,
            },
        ];
        let mut budget = Budget::new(PermanentProgramLimits::default(), 0)?;
        let keys = predicate_keys(&predicates, &mut budget)?;
        let digest: [u8; 32] = Sha256::digest(&keys[0]).into();
        assert!(String::from_utf8(keys[1].clone())
            .unwrap()
            .contains(&crate::model::hex(&digest)));
        Ok(())
    }

    #[test]
    fn cyclic_filler_graph_fails_closed() {
        let predicates = vec![DecodedPredicate {
            predicate_id: 0,
            kind: PredicateKind::AtLeastObject,
            argument_sorts: vec![TermSort::Object],
            symbol_id: None,
            role_id: Some(0),
            cardinality: Some(1),
            filler_predicate_id: Some(0),
            annotation: Vec::new(),
            internal_key: None,
        }];
        let mut budget = Budget::new(PermanentProgramLimits::default(), 0).unwrap();
        assert!(predicate_keys(&predicates, &mut budget)
            .unwrap_err()
            .message
            .contains("self-referential"));
    }
}
