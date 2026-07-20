//! Transactional named-class, named-individual, and axiom compilation.
//!
//! This phase owns a scalar-compatible `class_expression` symbol domain and
//! a scalar-compatible named `individual` domain. It compiles named-only
//! `SubClassOf`, `EquivalentClasses`, `DisjointClasses`, `ClassAssertion`,
//! `SameIndividual`, `DifferentIndividuals`, and named `ObjectPropertyDomain` /
//! `ObjectPropertyRange` / positive and negative `ObjectPropertyAssertion`
//! and `DataPropertyDomain` axioms into the existing native predicate, clause,
//! fact, and provenance records. Exact nested annotations participate in source
//! provenance, with segmented anonymous scopes remapped before hashing.
//! Predicate and clause identifiers are dense within this fragment and must be
//! remapped when a later phase assembles the complete program; no fragment is
//! publishable on its own.
// SPDX-License-Identifier: LGPL-3.0-or-later

#![forbid(unsafe_code)]

use std::mem::size_of;

use serde::Serialize;
use sha2::{Digest, Sha256};

use super::canonical::{
    self, annotation_stripped_axiom_digest, source_axiom_digest, AnonymousScopeMap, CanonicalBudget,
};
use super::data_roles::DataRolePhase;
use super::model::{ComponentValue, NodeId, NodeRef, ValidatedModel};
use super::object_roles::ObjectRolePhase;
use super::symbols::{RootHandler, SymbolPhase};
use super::{ByteSource, EncodedResult, EncodedValidationError};
use crate::input_wire::{
    DecodedAtom, DecodedClause, DecodedGroundAtom, DecodedPredicate, DecodedProvenanceEntry,
    DecodedSymbolDomain, DecodedSymbolValue, DecodedTerm, PredicateKind, SymbolKind, TermSort,
};

const NAMED_CLASS_PHASE_SCHEMA_VERSION: u16 = 1;
const ENTITY_TAG: u16 = 2;
const SUBCLASS_TAG: u16 = 61;
const EQUIVALENT_CLASSES_TAG: u16 = 62;
const DISJOINT_CLASSES_TAG: u16 = 63;
const OBJECT_PROPERTY_DOMAIN_TAG: u16 = 74;
const OBJECT_PROPERTY_RANGE_TAG: u16 = 75;
const DATA_PROPERTY_DOMAIN_TAG: u16 = 93;
const OBJECT_INVERSE_OF_TAG: u16 = 10;
const SAME_INDIVIDUAL_TAG: u16 = 110;
const DIFFERENT_INDIVIDUALS_TAG: u16 = 111;
const CLASS_ASSERTION_TAG: u16 = 112;
const OBJECT_PROPERTY_ASSERTION_TAG: u16 = 113;
const NEGATIVE_OBJECT_PROPERTY_ASSERTION_TAG: u16 = 114;
const BUILTIN_PROVENANCE_INPUT: &[u8] = b"pyhermit:clausification:builtins:v1";
const DISJOINT_GUARD_DOMAIN: &[u8] = b"pyhermit:linear-disjoint-classes:v1\0";
const THING_DISPLAY: &str = "class:http://www.w3.org/2002/07/owl#Thing";
const NOTHING_DISPLAY: &str = "class:http://www.w3.org/2002/07/owl#Nothing";
const OBJECT_PROPERTY_PREFIX: &str = "object_property:";
const DATA_PROPERTY_PREFIX: &str = "data_property:";
const TOP_OBJECT_IRI: &str = "http://www.w3.org/2002/07/owl#topObjectProperty";
const BOTTOM_OBJECT_IRI: &str = "http://www.w3.org/2002/07/owl#bottomObjectProperty";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct NamedClassPhaseLimits {
    pub max_slices: usize,
    pub max_entity_symbols: usize,
    pub max_class_symbols: usize,
    pub max_individual_symbols: usize,
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
            max_individual_symbols: 16_000_000,
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
    pub individual_domain: DecodedSymbolDomain,
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
    normalized_edges: Vec<NormalizedEdge>,
    normalized_disjoints: Vec<NormalizedDisjoint>,
    normalized_object_constraints: Vec<NormalizedObjectConstraint>,
    normalized_data_domains: Vec<NormalizedDataDomain>,
    normalized_facts: Vec<NormalizedFact>,
    normalized_object_facts: Vec<NormalizedObjectFact>,
    normalized_negative_object_facts: Vec<NormalizedObjectFact>,
    normalized_equalities: Vec<NormalizedEqualityFact>,
    normalized_inequalities: Vec<NormalizedInequalityFact>,
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
        let individual_symbols = self
            .individual_domain
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
            individual_symbols,
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
    individual_symbols: Vec<SymbolManifest<'a>>,
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
    super_class: u32,
    provenance: [u8; 32],
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct NormalizedEdge {
    sub_class: u32,
    super_class: u32,
    provenance: Vec<[u8; 32]>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct RawDisjoint {
    classes: Vec<u32>,
    provenance: [u8; 32],
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct NormalizedDisjoint {
    classes: Vec<u32>,
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
    class_id: u32,
    provenance: [u8; 32],
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct NormalizedObjectConstraint {
    kind: ObjectConstraintKind,
    role_id: u32,
    class_id: u32,
    provenance: Vec<[u8; 32]>,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct RawDataDomain {
    role_id: u32,
    class_id: u32,
    provenance: [u8; 32],
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct NormalizedDataDomain {
    role_id: u32,
    class_id: u32,
    provenance: Vec<[u8; 32]>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct RawFact {
    class_id: u32,
    individual_id: u32,
    provenance: [u8; 32],
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct NormalizedFact {
    class_id: u32,
    individual_id: u32,
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
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct NamedDisjointOutput {
    edges: Vec<RawEdge>,
    disjoint: Option<RawDisjoint>,
    provenance: [u8; 32],
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ProvenanceKey {
    source_sha256: Vec<[u8; 32]>,
    generated: bool,
}

struct PhaseBudget {
    limits: NamedClassPhaseLimits,
    work: u64,
    owned_bytes: usize,
}

impl PhaseBudget {
    const fn new(limits: NamedClassPhaseLimits) -> Self {
        Self {
            limits,
            work: 0,
            owned_bytes: 0,
        }
    }

    fn claim_work(&mut self, amount: usize) -> EncodedResult<()> {
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

    fn claim_owned(&mut self, amount: usize) -> EncodedResult<()> {
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
    let (class_domain, class_signature) =
        class_signature(symbols, &declared_class_ids, &mut budget)?;
    let declared_individual_ids = declared_individual_ids(symbols, &mut budget)?;
    let (individual_domain, individual_signature) =
        individual_signature(symbols, &declared_individual_ids, &mut budget)?;
    let mut named_individuals = Vec::new();
    budget.claim_owned(
        individual_domain
            .values
            .len()
            .checked_mul(size_of::<u32>())
            .ok_or_else(|| {
                EncodedValidationError::resource("named-individual ID output overflowed")
            })?,
    )?;
    named_individuals
        .try_reserve_exact(individual_domain.values.len())
        .map_err(|_| {
            EncodedValidationError::resource("named-individual ID output allocation failed")
        })?;
    named_individuals.extend(
        individual_domain
            .values
            .iter()
            .map(|value| value.identifier),
    );
    let thing = class_id_by_display(&class_domain, THING_DISPLAY)?;
    let nothing = class_id_by_display(&class_domain, NOTHING_DISPLAY)?;
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
    let mut raw_data_domains = Vec::<RawDataDomain>::new();
    let mut raw_facts = Vec::<RawFact>::new();
    let mut raw_object_facts = Vec::<RawObjectFact>::new();
    let mut raw_negative_object_facts = Vec::<RawObjectFact>::new();
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
                    &class_signature,
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
    let disjoints = normalize_disjoints(raw_disjoints, &class_domain, &mut budget)?;
    let object_constraints = normalize_object_constraints(raw_object_constraints, &mut budget)?;
    let data_domains = normalize_data_domains(raw_data_domains, &mut budget)?;
    let facts = normalize_facts(raw_facts, &mut budget)?;
    let object_facts = normalize_object_facts(raw_object_facts, &mut budget)?;
    let negative_object_facts = normalize_object_facts(raw_negative_object_facts, &mut budget)?;
    let equalities = normalize_equalities(raw_equalities, &mut budget)?;
    let inequalities = normalize_inequalities(raw_inequalities, &mut budget)?;
    let (provenance, provenance_keys) = freeze_provenance(
        &edges,
        &disjoints,
        &object_constraints,
        &data_domains,
        &facts,
        &object_facts,
        &negative_object_facts,
        &equalities,
        &inequalities,
        &mut budget,
    )?;
    let (
        predicates,
        predicate_by_class,
        predicate_by_object_role,
        predicate_by_negative_object_role,
        predicate_by_data_role,
        guard_predicates,
        named_predicate,
        equality_predicate,
        inequality_predicate,
    ) = freeze_predicates(
        &edges,
        &disjoints,
        &object_constraints,
        &data_domains,
        &facts,
        &object_facts,
        &negative_object_facts,
        &equalities,
        &inequalities,
        thing,
        nothing,
        !individual_domain.values.is_empty(),
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
        &edges,
        &disjoints,
        &object_constraints,
        &data_domains,
        nothing,
        &predicate_by_class,
        &predicate_by_object_role,
        &predicate_by_data_role,
        &guard_predicates,
        &provenance_keys,
        &mut budget,
    )?;
    let positive_facts = freeze_positive_facts(
        &facts,
        &object_facts,
        &equalities,
        &inequalities,
        &individual_domain,
        thing,
        &predicate_by_class,
        &predicate_by_object_role,
        named_predicate,
        equality_predicate,
        inequality_predicate,
        &provenance_keys,
        &scalar_predicate_ids,
        &mut budget,
    )?;
    let negative_facts = freeze_negative_facts(
        &negative_object_facts,
        &individual_domain,
        &predicate_by_negative_object_role,
        &provenance_keys,
        &scalar_predicate_ids,
        positive_facts.len(),
        &mut budget,
    )?;
    Ok(NamedClassPhase {
        class_domain,
        class_signature,
        individual_domain,
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
        normalized_edges: edges,
        normalized_disjoints: disjoints,
        normalized_object_constraints: object_constraints,
        normalized_data_domains: data_domains,
        normalized_facts: facts,
        normalized_object_facts: object_facts,
        normalized_negative_object_facts: negative_object_facts,
        normalized_equalities: equalities,
        normalized_inequalities: inequalities,
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

fn class_signature(
    symbols: &SymbolPhase,
    declared_class_ids: &[u32],
    budget: &mut PhaseBudget,
) -> EncodedResult<(DecodedSymbolDomain, Vec<ClassSignatureBinding>)> {
    let mut values = Vec::new();
    let mut bindings = Vec::new();
    for entity in &symbols.entity_domain.values {
        budget.claim_work(1)?;
        if !entity.display.starts_with("class:") {
            continue;
        }
        let following = values.len().checked_add(1).ok_or_else(|| {
            EncodedValidationError::resource("named-class symbol count overflowed")
        })?;
        PhaseBudget::count(following, budget.limits.max_class_symbols, "symbol count")?;
        budget.claim_owned(size_of::<DecodedSymbolValue>())?;
        budget.claim_owned(size_of::<ClassSignatureBinding>())?;
        budget.claim_owned(entity.key.len())?;
        budget.claim_owned(entity.display.len())?;
        values.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("named-class symbol allocation failed")
        })?;
        bindings.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("named-class signature allocation failed")
        })?;
        let class_expression_id = u32::try_from(values.len())
            .map_err(|_| EncodedValidationError::resource("named-class symbol ID exceeds u32"))?;
        values.push(DecodedSymbolValue {
            identifier: class_expression_id,
            key: entity.key.clone(),
            display: entity.display.clone(),
            generated: entity.generated,
            query_local: entity.query_local,
        });
        bindings.push(ClassSignatureBinding {
            class_expression_id,
            entity_id: entity.identifier,
            declared: declared_class_ids.binary_search(&entity.identifier).is_ok(),
        });
    }
    Ok((
        DecodedSymbolDomain {
            kind: SymbolKind::ClassExpression,
            values,
        },
        bindings,
    ))
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

fn individual_signature(
    symbols: &SymbolPhase,
    declared_individual_ids: &[u32],
    budget: &mut PhaseBudget,
) -> EncodedResult<(DecodedSymbolDomain, Vec<IndividualSignatureBinding>)> {
    let mut values = Vec::new();
    let mut bindings = Vec::new();
    for entity in &symbols.entity_domain.values {
        budget.claim_work(1)?;
        if !entity.display.starts_with("named_individual:") {
            continue;
        }
        let following = values.len().checked_add(1).ok_or_else(|| {
            EncodedValidationError::resource("named-individual symbol count overflowed")
        })?;
        PhaseBudget::count(
            following,
            budget.limits.max_individual_symbols,
            "individual symbol count",
        )?;
        budget.claim_owned(size_of::<DecodedSymbolValue>())?;
        budget.claim_owned(size_of::<IndividualSignatureBinding>())?;
        budget.claim_owned(entity.key.len())?;
        budget.claim_owned(entity.display.len())?;
        values.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("named-individual symbol allocation failed")
        })?;
        bindings.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("named-individual signature allocation failed")
        })?;
        let individual_id = u32::try_from(values.len()).map_err(|_| {
            EncodedValidationError::resource("named-individual symbol ID exceeds u32")
        })?;
        values.push(DecodedSymbolValue {
            identifier: individual_id,
            key: entity.key.clone(),
            display: entity.display.clone(),
            generated: entity.generated,
            query_local: entity.query_local,
        });
        bindings.push(IndividualSignatureBinding {
            individual_id,
            entity_id: entity.identifier,
            declared: declared_individual_ids
                .binary_search(&entity.identifier)
                .is_ok(),
        });
    }
    Ok((
        DecodedSymbolDomain {
            kind: SymbolKind::Individual,
            values,
        },
        bindings,
    ))
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

fn named_subclass<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
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
    let Some(sub_class) = named_class_field(model, symbols, signature, node, 0)? else {
        return Ok(None);
    };
    let Some(super_class) = named_class_field(model, symbols, signature, node, 1)? else {
        return Ok(None);
    };
    let provenance = source_axiom_digest(model, root, scope_maps, budget)?;
    Ok(Some(RawEdge {
        sub_class,
        super_class,
        provenance,
    }))
}

fn named_equivalent_classes<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
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
    let mut classes = Vec::new();
    budget.claim_owned(
        expressions
            .len()
            .checked_mul(size_of::<u32>())
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
        let Some(class_id) = named_class_id(model, symbols, signature, identifier)? else {
            return Ok(None);
        };
        classes.push(class_id);
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
    for (index, sub_class) in classes.iter().copied().enumerate() {
        let following = index.checked_add(1).ok_or_else(|| {
            EncodedValidationError::resource("equivalent-classes edge index overflowed")
        })?;
        edges.push(RawEdge {
            sub_class,
            super_class: classes[following % classes.len()],
            provenance,
        });
    }
    Ok(Some(edges))
}

#[allow(clippy::too_many_arguments)]
fn named_disjoint_classes<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
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
    let mut classes = Vec::new();
    budget.claim_owned(
        expressions
            .len()
            .checked_mul(size_of::<u32>())
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
        let Some(class_id) = named_class_id(model, symbols, signature, identifier)? else {
            return Ok(None);
        };
        classes.push(class_id);
    }
    if classes.len() < 2 {
        return Err(EncodedValidationError::invariant(
            "disjoint-classes root has fewer than two members",
        ));
    }
    let provenance = source_axiom_digest(model, root, scope_maps, budget)?;
    let mut live = Vec::new();
    budget.claim_owned(classes.len().checked_mul(size_of::<u32>()).ok_or_else(|| {
        EncodedValidationError::resource("live disjoint-class allocation overflowed")
    })?)?;
    live.try_reserve_exact(classes.len())
        .map_err(|_| EncodedValidationError::resource("live disjoint-class allocation failed"))?;
    live.extend(classes.into_iter().filter(|class_id| *class_id != nothing));

    if live.contains(&thing) {
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
        for class_id in live {
            if class_id != thing {
                edges.push(RawEdge {
                    sub_class: class_id,
                    super_class: nothing,
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

    Ok(Some(NamedDisjointOutput {
        edges: Vec::new(),
        disjoint: (live.len() >= 2).then_some(RawDisjoint {
            classes: live,
            provenance,
        }),
        provenance,
    }))
}

#[allow(clippy::too_many_arguments)]
fn named_object_constraint<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    object_roles: &ObjectRolePhase,
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
    let Some(class_id) = named_class_field(model, symbols, class_signature, node, 1)? else {
        return Ok(None);
    };
    let provenance = source_axiom_digest(model, root, scope_maps, budget)?;
    Ok(Some(RawObjectConstraint {
        kind,
        role_id,
        class_id,
        provenance,
    }))
}

#[allow(clippy::too_many_arguments)]
fn named_data_domain<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    data_roles: &DataRolePhase,
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
    let Some(class_id) = named_class_field(model, symbols, class_signature, node, 1)? else {
        return Ok(None);
    };
    let provenance = source_axiom_digest(model, root, scope_maps, budget)?;
    Ok(Some(RawDataDomain {
        role_id,
        class_id,
        provenance,
    }))
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
    class_signature: &[ClassSignatureBinding],
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
    let Some(class_id) = named_class_field(model, symbols, class_signature, node, 0)? else {
        return Ok(None);
    };
    let Some(individual_id) =
        named_individual_field(model, symbols, individual_signature, node, 1)?
    else {
        return Ok(None);
    };
    let provenance = source_axiom_digest(model, root, scope_maps, budget)?;
    Ok(Some(RawFact {
        class_id,
        individual_id,
        provenance,
    }))
}

#[allow(clippy::too_many_arguments)]
fn named_object_assertion<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    object_roles: &ObjectRolePhase,
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
    let Some(mut source_individual) =
        named_individual_field(model, symbols, individual_signature, node, 1)?
    else {
        return Ok(None);
    };
    let Some(mut target_individual) =
        named_individual_field(model, symbols, individual_signature, node, 2)?
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

fn named_class_field<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    signature: &[ClassSignatureBinding],
    node: NodeRef,
    relative_field: usize,
) -> EncodedResult<Option<u32>> {
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
    named_class_id(model, symbols, signature, identifier)
}

fn named_class_id<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    signature: &[ClassSignatureBinding],
    identifier: NodeId,
) -> EncodedResult<Option<u32>> {
    if model.node(identifier)?.tag() != ENTITY_TAG {
        return Ok(None);
    }
    let entity_id = symbols.entity_symbol_for_node(identifier).ok_or_else(|| {
        EncodedValidationError::invariant(
            "named class is absent from the reachable entity-node mapping",
        )
    })?;
    Ok(signature
        .binary_search_by_key(&entity_id, |binding| binding.entity_id)
        .ok()
        .map(|index| signature[index].class_expression_id))
}

fn named_individual_field<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    signature: &[IndividualSignatureBinding],
    node: NodeRef,
    relative_field: usize,
) -> EncodedResult<Option<u32>> {
    let field_index = node
        .fields()
        .start
        .checked_add(relative_field)
        .ok_or_else(|| EncodedValidationError::invariant("individual field index overflowed"))?;
    let component = required_component(model.field(field_index)?, "named-individual field")?;
    let ComponentValue::Node(identifier) = model.resolve(component)? else {
        return Err(EncodedValidationError::invariant(
            "individual field did not resolve to a node",
        ));
    };
    named_individual_id(model, symbols, signature, identifier)
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
    if edge.sub_class == nothing || edge.super_class == thing || edge.sub_class == edge.super_class
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
    raw.sort_by_key(|edge| (edge.sub_class, edge.super_class, edge.provenance));
    let mut normalized = Vec::<NormalizedEdge>::new();
    for edge in raw {
        budget.claim_work(1)?;
        if let Some(previous) = normalized.last_mut() {
            if previous.sub_class == edge.sub_class && previous.super_class == edge.super_class {
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
            super_class: edge.super_class,
            provenance,
        });
    }
    Ok(normalized)
}

fn normalize_disjoints(
    mut raw: Vec<RawDisjoint>,
    domain: &DecodedSymbolDomain,
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
        let guard_digest = disjoint_guard_digest(domain, &value.classes, budget)?;
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
            guard_digest,
        });
    }
    Ok(normalized)
}

fn normalize_facts(
    mut raw: Vec<RawFact>,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<NormalizedFact>> {
    budget.claim_work(sort_work(raw.len()))?;
    raw.sort_by_key(|fact| (fact.class_id, fact.individual_id, fact.provenance));
    let mut normalized = Vec::<NormalizedFact>::new();
    for fact in raw {
        budget.claim_work(1)?;
        if let Some(previous) = normalized.last_mut() {
            if previous.class_id == fact.class_id && previous.individual_id == fact.individual_id {
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
                && previous.class_id == constraint.class_id
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
            class_id: constraint.class_id,
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
            if previous.role_id == domain.role_id && previous.class_id == domain.class_id {
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
            class_id: domain.class_id,
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
    data_domains: &[NormalizedDataDomain],
    facts: &[NormalizedFact],
    object_facts: &[NormalizedObjectFact],
    negative_object_facts: &[NormalizedObjectFact],
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
    ObjectRole(u32),
    NegatedObjectRole(u32),
    DataRole(u32),
    Equality,
    Inequality,
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
type FrozenPredicates = (
    Vec<DecodedPredicate>,
    PredicateIndex,
    ObjectPredicateIndex,
    ObjectPredicateIndex,
    ObjectPredicateIndex,
    GuardPredicateIndex,
    Option<u32>,
    Option<u32>,
    Option<u32>,
);

#[allow(clippy::too_many_arguments)]
fn freeze_predicates(
    edges: &[NormalizedEdge],
    disjoints: &[NormalizedDisjoint],
    object_constraints: &[NormalizedObjectConstraint],
    data_domains: &[NormalizedDataDomain],
    facts: &[NormalizedFact],
    object_facts: &[NormalizedObjectFact],
    negative_object_facts: &[NormalizedObjectFact],
    equalities: &[NormalizedEqualityFact],
    inequalities: &[NormalizedInequalityFact],
    thing: u32,
    nothing: u32,
    has_individuals: bool,
    budget: &mut PhaseBudget,
) -> EncodedResult<FrozenPredicates> {
    let mut class_ids = Vec::new();
    push_u32(&mut class_ids, nothing, "predicate class", budget)?;
    if has_individuals {
        push_u32(&mut class_ids, thing, "predicate class", budget)?;
    }
    for edge in edges {
        push_u32(&mut class_ids, edge.sub_class, "predicate class", budget)?;
        push_u32(&mut class_ids, edge.super_class, "predicate class", budget)?;
    }
    for disjoint in disjoints {
        for class_id in &disjoint.classes {
            push_u32(&mut class_ids, *class_id, "predicate class", budget)?;
        }
    }
    for constraint in object_constraints {
        push_u32(
            &mut class_ids,
            constraint.class_id,
            "predicate class",
            budget,
        )?;
    }
    for domain in data_domains {
        push_u32(&mut class_ids, domain.class_id, "predicate class", budget)?;
    }
    for fact in facts {
        push_u32(&mut class_ids, fact.class_id, "predicate class", budget)?;
    }
    budget.claim_work(sort_work(class_ids.len()))?;
    class_ids.sort_unstable();
    class_ids.dedup();

    let mut ordered = Vec::<PendingPredicate>::new();
    if !equalities.is_empty() {
        let key = equality_predicate_key();
        budget.claim_owned(size_of::<PendingPredicate>())?;
        budget.claim_owned(key.len())?;
        ordered.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("equality predicate allocation failed")
        })?;
        ordered.push(PendingPredicate {
            key,
            owner: PredicateOwner::Equality,
        });
    }
    if !inequalities.is_empty() {
        let key = inequality_predicate_key();
        budget.claim_owned(size_of::<PendingPredicate>())?;
        budget.claim_owned(key.len())?;
        ordered.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("inequality predicate allocation failed")
        })?;
        ordered.push(PendingPredicate {
            key,
            owner: PredicateOwner::Inequality,
        });
    }
    if has_individuals {
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
        let key = concept_predicate_key(class_id);
        budget.claim_owned(size_of::<PendingPredicate>())?;
        budget.claim_owned(key.len())?;
        ordered.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("named-class predicate ordering allocation failed")
        })?;
        ordered.push(PendingPredicate {
            key,
            owner: PredicateOwner::Concept(class_id),
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
    let mut predicate_by_object_role = Vec::new();
    let mut predicate_by_negative_object_role = Vec::new();
    let mut predicate_by_data_role = Vec::new();
    let mut guard_predicates = Vec::new();
    let mut named_predicate = None;
    let mut equality_predicate = None;
    let mut inequality_predicate = None;
    budget.claim_owned(
        ordered
            .len()
            .checked_mul(
                size_of::<DecodedPredicate>()
                    + 4 * size_of::<(u32, u32)>()
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
            PredicateOwner::Equality => {
                budget.claim_owned(size_of::<TermSort>())?;
                predicates.push(DecodedPredicate {
                    predicate_id,
                    kind: PredicateKind::Equality,
                    argument_sorts: vec![TermSort::Object, TermSort::Object],
                    symbol_id: None,
                    role_id: None,
                    cardinality: None,
                    filler_predicate_id: None,
                    annotation: Vec::new(),
                    internal_key: None,
                });
                equality_predicate = Some(predicate_id);
            }
            PredicateOwner::Inequality => {
                budget.claim_owned(size_of::<TermSort>())?;
                predicates.push(DecodedPredicate {
                    predicate_id,
                    kind: PredicateKind::Inequality,
                    argument_sorts: vec![TermSort::Object, TermSort::Object],
                    symbol_id: None,
                    role_id: None,
                    cardinality: None,
                    filler_predicate_id: None,
                    annotation: Vec::new(),
                    internal_key: None,
                });
                inequality_predicate = Some(predicate_id);
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
    predicate_by_object_role.sort_unstable_by_key(|(role_id, _)| *role_id);
    predicate_by_negative_object_role.sort_unstable_by_key(|(role_id, _)| *role_id);
    predicate_by_data_role.sort_unstable_by_key(|(role_id, _)| *role_id);
    guard_predicates.sort_unstable_by_key(|(digest, sequence, _)| (*digest, *sequence));
    Ok((
        predicates,
        predicate_by_class,
        predicate_by_object_role,
        predicate_by_negative_object_role,
        predicate_by_data_role,
        guard_predicates,
        named_predicate,
        equality_predicate,
        inequality_predicate,
    ))
}

#[allow(clippy::too_many_arguments)]
fn freeze_clauses(
    edges: &[NormalizedEdge],
    disjoints: &[NormalizedDisjoint],
    object_constraints: &[NormalizedObjectConstraint],
    data_domains: &[NormalizedDataDomain],
    nothing: u32,
    predicate_by_class: &[(u32, u32)],
    predicate_by_object_role: &[(u32, u32)],
    predicate_by_data_role: &[(u32, u32)],
    guard_predicates: &[([u8; 32], u32, u32)],
    provenance_keys: &[ProvenanceKey],
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<DecodedClause>> {
    let mut following = edges
        .len()
        .checked_add(1)
        .and_then(|value| value.checked_add(object_constraints.len()))
        .and_then(|value| value.checked_add(data_domains.len()))
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
        budget,
    )?;
    for edge in edges {
        let body = predicate_id(predicate_by_class, edge.sub_class)?;
        let head = predicate_id(predicate_by_class, edge.super_class)?;
        let provenance = provenance_id(provenance_keys, &edge.provenance, false)?;
        push_clause(&mut ordered, &[body], &[head], provenance, budget)?;
    }
    for constraint in object_constraints {
        let role = object_predicate_id(predicate_by_object_role, constraint.role_id)?;
        let class = predicate_id(predicate_by_class, constraint.class_id)?;
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
    for domain in data_domains {
        let role = data_predicate_id(predicate_by_data_role, domain.role_id)?;
        let class = predicate_id(predicate_by_class, domain.class_id)?;
        let provenance = provenance_id(provenance_keys, &domain.provenance, false)?;
        push_data_domain_clause(&mut ordered, role, class, provenance, budget)?;
    }
    for disjoint in disjoints {
        let provenance = provenance_id(provenance_keys, &disjoint.provenance, false)?;
        let mut previous = None;
        for (index, class_id) in disjoint.classes.iter().copied().enumerate() {
            let sequence = u32::try_from(index).map_err(|_| {
                EncodedValidationError::resource("disjoint-guard sequence exceeds u32")
            })?;
            let current = guard_predicate_id(guard_predicates, disjoint.guard_digest, sequence)?;
            let member = predicate_id(predicate_by_class, class_id)?;
            if let Some(previous_id) = previous {
                push_clause(
                    &mut ordered,
                    &[previous_id, member],
                    &[],
                    provenance,
                    budget,
                )?;
                push_clause(&mut ordered, &[previous_id], &[current], provenance, budget)?;
            }
            push_clause(&mut ordered, &[member], &[current], provenance, budget)?;
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
    equalities: &[NormalizedEqualityFact],
    inequalities: &[NormalizedInequalityFact],
    individual_domain: &DecodedSymbolDomain,
    thing: u32,
    predicate_by_class: &[(u32, u32)],
    predicate_by_object_role: &[(u32, u32)],
    named_predicate: Option<u32>,
    equality_predicate: Option<u32>,
    inequality_predicate: Option<u32>,
    provenance_keys: &[ProvenanceKey],
    scalar_predicate_ids: &[u32],
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<DecodedGroundAtom>> {
    let builtin: [u8; 32] = Sha256::digest(BUILTIN_PROVENANCE_INPUT).into();
    let builtin_provenance = provenance_id(provenance_keys, &[builtin], true)?;
    let thing_predicate = if individual_domain.values.is_empty() {
        None
    } else {
        Some(predicate_id(predicate_by_class, thing)?)
    };
    let named_predicate = match (individual_domain.values.is_empty(), named_predicate) {
        (true, None) => None,
        (false, Some(identifier)) => Some(identifier),
        _ => {
            return Err(EncodedValidationError::invariant(
                "named-individual predicate presence disagrees with its domain",
            ));
        }
    };
    let equality_predicate = match (equalities.is_empty(), equality_predicate) {
        (true, None) => None,
        (false, Some(identifier)) => Some(identifier),
        _ => {
            return Err(EncodedValidationError::invariant(
                "equality predicate presence disagrees with equality facts",
            ));
        }
    };
    let inequality_predicate = match (inequalities.is_empty(), inequality_predicate) {
        (true, None) => None,
        (false, Some(identifier)) => Some(identifier),
        _ => {
            return Err(EncodedValidationError::invariant(
                "inequality predicate presence disagrees with inequality facts",
            ));
        }
    };
    let expected = individual_domain
        .values
        .len()
        .checked_mul(2)
        .and_then(|value| value.checked_add(facts.len()))
        .and_then(|value| value.checked_add(object_facts.len()))
        .and_then(|value| value.checked_add(equalities.len()))
        .and_then(|value| value.checked_add(inequalities.len()))
        .ok_or_else(|| EncodedValidationError::resource("positive-fact count overflowed"))?;
    budget.claim_work(
        facts
            .len()
            .checked_add(object_facts.len())
            .and_then(|value| value.checked_add(equalities.len()))
            .and_then(|value| value.checked_add(inequalities.len()))
            .ok_or_else(|| EncodedValidationError::resource("positive-fact work overflowed"))?,
    )?;
    let top_fact_count = facts.iter().filter(|fact| fact.class_id == thing).count();
    let class_fact_count = facts.len().checked_sub(top_fact_count).ok_or_else(|| {
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
        .checked_mul(2)
        .and_then(|value| value.checked_add(class_fact_count))
        .and_then(|value| value.checked_add(object_facts.len()))
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
        let named = named_predicate.ok_or_else(|| {
            EncodedValidationError::invariant("named-individual predicate index is incomplete")
        })?;
        let top = thing_predicate.ok_or_else(|| {
            EncodedValidationError::invariant("top concept predicate index is incomplete")
        })?;
        pending.push((
            named,
            GroundArguments::Unary(individual.identifier),
            builtin_provenance,
        ));
        pending.push((
            top,
            GroundArguments::Unary(individual.identifier),
            builtin_provenance,
        ));
    }
    for fact in facts {
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
        .filter(|(_, arguments, _)| matches!(arguments, GroundArguments::Binary(_, _)))
        .count();
    let expected_binary_fact_count = equality_fact_count
        .checked_add(inequality_fact_count)
        .and_then(|value| value.checked_add(object_facts.len()))
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

fn freeze_negative_facts(
    facts: &[NormalizedObjectFact],
    individual_domain: &DecodedSymbolDomain,
    predicate_by_negative_object_role: &[(u32, u32)],
    provenance_keys: &[ProvenanceKey],
    scalar_predicate_ids: &[u32],
    positive_fact_count: usize,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<DecodedGroundAtom>> {
    let total_fact_count = positive_fact_count
        .checked_add(facts.len())
        .ok_or_else(|| EncodedValidationError::resource("ground-fact count overflowed"))?;
    PhaseBudget::count(
        total_fact_count,
        budget.limits.max_facts,
        "ground fact count",
    )?;
    budget.claim_work(
        facts
            .len()
            .checked_add(sort_work(facts.len()))
            .ok_or_else(|| EncodedValidationError::resource("negative-fact work overflowed"))?,
    )?;
    budget.claim_owned(
        facts
            .len()
            .checked_mul(size_of::<(Vec<u8>, DecodedGroundAtom)>())
            .ok_or_else(|| EncodedValidationError::resource("negative-fact input overflowed"))?,
    )?;
    let mut ordered = Vec::<(Vec<u8>, DecodedGroundAtom)>::new();
    ordered
        .try_reserve_exact(facts.len())
        .map_err(|_| EncodedValidationError::resource("negative-fact input allocation failed"))?;
    for fact in facts {
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
    ordered.sort_by(|left, right| left.0.cmp(&right.0));
    if ordered.windows(2).any(|pair| pair[0].0 >= pair[1].0) {
        return Err(EncodedValidationError::invariant(
            "negative object-property facts contain duplicate identities",
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
    body_ids.sort_unstable();
    body_ids.dedup();
    head_ids.sort_unstable();
    head_ids.dedup();
    if body_ids.iter().any(|value| head_ids.contains(value)) {
        return Ok(());
    }
    let body_count = body_ids.len();
    let key = rule_key(&body_ids, &head_ids);
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
            body: body_ids.into_iter().map(variable_atom).collect(),
            head: head_ids.into_iter().map(variable_atom).collect(),
            provenance_ids: vec![provenance_id],
            join_order: (0..u32::try_from(body_count).map_err(|_| {
                EncodedValidationError::resource("named-class join order exceeds u32")
            })?)
                .collect(),
        },
    ));
    Ok(())
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

fn variable_atom(predicate_id: u32) -> DecodedAtom {
    variable_atom_at(predicate_id, 0, TermSort::Object)
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

fn disjoint_guard_digest(
    domain: &DecodedSymbolDomain,
    classes: &[u32],
    budget: &mut PhaseBudget,
) -> EncodedResult<[u8; 32]> {
    let mut digest = Sha256::new();
    digest.update(DISJOINT_GUARD_DOMAIN);
    budget.claim_work(DISJOINT_GUARD_DOMAIN.len())?;
    for class_id in classes {
        let key = class_key(domain, *class_id)?;
        budget.claim_work(key.len())?;
        digest.update(key);
    }
    Ok(digest.finalize().into())
}

fn class_key(domain: &DecodedSymbolDomain, identifier: u32) -> EncodedResult<&[u8]> {
    domain
        .values
        .get(
            usize::try_from(identifier).map_err(|_| {
                EncodedValidationError::invariant("class-expression ID exceeds usize")
            })?,
        )
        .map(|value| value.key.as_slice())
        .ok_or_else(|| EncodedValidationError::invariant("class-expression ID is dangling"))
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
        _ => ("", "invalid"),
    };
    format!(
        "{{\"annotation\":[],\"argument_sorts\":[{sorts}],\"cardinality\":null,\"filler\":null,\"internal_key\":null,\"kind\":\"{name}\",\"role_id\":{role_id},\"symbol_id\":null}}"
    )
    .into_bytes()
}

fn named_predicate_key(predicate: &DecodedPredicate) -> EncodedResult<Vec<u8>> {
    let unary_object = predicate.argument_sorts == [TermSort::Object];
    let binary_object = predicate.argument_sorts == [TermSort::Object, TermSort::Object];
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
        PredicateKind::Equality
            if binary_object
                && predicate.symbol_id.is_none()
                && predicate.annotation.is_empty()
                && predicate.internal_key.is_none() =>
        {
            Ok(equality_predicate_key())
        }
        PredicateKind::Inequality
            if binary_object
                && predicate.symbol_id.is_none()
                && predicate.annotation.is_empty()
                && predicate.internal_key.is_none() =>
        {
            Ok(inequality_predicate_key())
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

fn named_individual_predicate_key() -> Vec<u8> {
    b"{\"annotation\":[],\"argument_sorts\":[\"object\"],\"cardinality\":null,\"filler\":null,\"internal_key\":\"named-individual\",\"kind\":\"named_individual\",\"role_id\":null,\"symbol_id\":null}"
        .to_vec()
}

fn equality_predicate_key() -> Vec<u8> {
    b"{\"annotation\":[],\"argument_sorts\":[\"object\",\"object\"],\"cardinality\":null,\"filler\":null,\"internal_key\":null,\"kind\":\"equality\",\"role_id\":null,\"symbol_id\":null}"
        .to_vec()
}

fn inequality_predicate_key() -> Vec<u8> {
    b"{\"annotation\":[],\"argument_sorts\":[\"object\",\"object\"],\"cardinality\":null,\"filler\":null,\"internal_key\":null,\"kind\":\"inequality\",\"role_id\":null,\"symbol_id\":null}"
        .to_vec()
}

fn disjoint_guard_predicate_key(sequence: u32, internal_key: &str) -> Vec<u8> {
    format!(
        "{{\"annotation\":[{sequence}],\"argument_sorts\":[\"object\"],\"cardinality\":null,\"filler\":null,\"internal_key\":\"{internal_key}\",\"kind\":\"disjoint_guard\",\"role_id\":null,\"symbol_id\":null}}"
    )
    .into_bytes()
}

fn rule_key(body_predicates: &[u32], head_predicates: &[u32]) -> Vec<u8> {
    let body = body_predicates
        .iter()
        .copied()
        .map(atom_json)
        .collect::<Vec<_>>()
        .join(",");
    let head = head_predicates
        .iter()
        .copied()
        .map(atom_json)
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

fn variable_json(index: u32, sort: TermSort) -> String {
    let sort = match sort {
        TermSort::Object => "object",
        TermSort::Data => "data",
    };
    format!("{{\"index\":{index},\"schema_version\":1,\"sort\":\"{sort}\",\"type\":\"Variable\"}}")
}

fn atom_json(predicate_id: u32) -> String {
    format!(
        "{{\"arguments\":[{{\"index\":0,\"schema_version\":1,\"sort\":\"object\",\"type\":\"Variable\"}}],\"predicate_id\":{predicate_id},\"schema_version\":1,\"type\":\"Atom\"}}"
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
    let individual_domains = phases
        .iter()
        .map(|(_, phase)| &phase.individual_domain)
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
    let (individual_domain, individual_maps) = merge_symbol_domains(
        &individual_domains,
        SymbolKind::Individual,
        limits.max_individual_symbols,
        "individual",
        &mut budget,
    )?;
    let class_signature = merge_class_signatures(
        phases,
        &entity_maps,
        &class_maps,
        class_domain.values.len(),
        &mut budget,
    )?;
    let individual_signature = merge_individual_signatures(
        phases,
        &entity_maps,
        &individual_maps,
        individual_domain.values.len(),
        &mut budget,
    )?;
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
        data_domains,
        facts,
        object_facts,
        negative_object_facts,
        equalities,
        inequalities,
    ) = merge_normalized_sources(
        phases,
        &class_maps,
        &individual_maps,
        &class_domain,
        source_object_roles,
        merged_object_roles,
        source_data_roles,
        merged_data_roles,
        &mut budget,
    )?;
    let thing = class_id_by_display(&class_domain, THING_DISPLAY)?;
    let nothing = class_id_by_display(&class_domain, NOTHING_DISPLAY)?;
    let (provenance, provenance_keys) = freeze_provenance(
        &edges,
        &disjoints,
        &object_constraints,
        &data_domains,
        &facts,
        &object_facts,
        &negative_object_facts,
        &equalities,
        &inequalities,
        &mut budget,
    )?;
    let (
        predicates,
        predicate_by_class,
        predicate_by_object_role,
        predicate_by_negative_object_role,
        predicate_by_data_role,
        guard_predicates,
        named_predicate,
        equality_predicate,
        inequality_predicate,
    ) = freeze_predicates(
        &edges,
        &disjoints,
        &object_constraints,
        &data_domains,
        &facts,
        &object_facts,
        &negative_object_facts,
        &equalities,
        &inequalities,
        thing,
        nothing,
        !individual_domain.values.is_empty(),
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
        &edges,
        &disjoints,
        &object_constraints,
        &data_domains,
        nothing,
        &predicate_by_class,
        &predicate_by_object_role,
        &predicate_by_data_role,
        &guard_predicates,
        &provenance_keys,
        &mut budget,
    )?;
    let positive_facts = freeze_positive_facts(
        &facts,
        &object_facts,
        &equalities,
        &inequalities,
        &individual_domain,
        thing,
        &predicate_by_class,
        &predicate_by_object_role,
        named_predicate,
        equality_predicate,
        inequality_predicate,
        &provenance_keys,
        &scalar_predicate_ids,
        &mut budget,
    )?;
    let negative_facts = freeze_negative_facts(
        &negative_object_facts,
        &individual_domain,
        &predicate_by_negative_object_role,
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
    let named_individuals = individual_domain
        .values
        .iter()
        .map(|value| value.identifier)
        .collect();
    Ok(NamedClassPhase {
        class_domain,
        class_signature,
        individual_domain,
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
        normalized_edges: edges,
        normalized_disjoints: disjoints,
        normalized_object_constraints: object_constraints,
        normalized_data_domains: data_domains,
        normalized_facts: facts,
        normalized_object_facts: object_facts,
        normalized_negative_object_facts: negative_object_facts,
        normalized_equalities: equalities,
        normalized_inequalities: inequalities,
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
    class_count: usize,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<ClassSignatureBinding>> {
    let mut merged = vec![None::<(u32, bool)>; class_count];
    budget.claim_owned(
        class_count
            .checked_mul(size_of::<Option<(u32, bool)>>())
            .ok_or_else(|| EncodedValidationError::resource("merged class signature overflowed"))?,
    )?;
    for (phase_index, (_, phase)) in phases.iter().enumerate() {
        if phase.class_signature.len() != phase.class_domain.values.len() {
            return Err(EncodedValidationError::invariant(
                "merged class signature no longer covers its domain",
            ));
        }
        for binding in &phase.class_signature {
            budget.claim_work(1)?;
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
        .map(|(index, value)| {
            let (entity_id, declared) = value.ok_or_else(|| {
                EncodedValidationError::invariant("merged class signature is incomplete")
            })?;
            Ok(ClassSignatureBinding {
                class_expression_id: u32::try_from(index).map_err(|_| {
                    EncodedValidationError::resource("merged class signature ID exceeds u32")
                })?,
                entity_id,
                declared,
            })
        })
        .collect()
}

fn merge_individual_signatures(
    phases: &[(SymbolPhase, NamedClassPhase)],
    entity_maps: &[Vec<u32>],
    individual_maps: &[Vec<u32>],
    individual_count: usize,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<IndividualSignatureBinding>> {
    let mut merged = vec![None::<(u32, bool)>; individual_count];
    budget.claim_owned(
        individual_count
            .checked_mul(size_of::<Option<(u32, bool)>>())
            .ok_or_else(|| {
                EncodedValidationError::resource("merged individual signature overflowed")
            })?,
    )?;
    for (phase_index, (_, phase)) in phases.iter().enumerate() {
        if phase.individual_signature.len() != phase.individual_domain.values.len() {
            return Err(EncodedValidationError::invariant(
                "merged individual signature no longer covers its domain",
            ));
        }
        for binding in &phase.individual_signature {
            budget.claim_work(1)?;
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
        .map(|(index, value)| {
            let (entity_id, declared) = value.ok_or_else(|| {
                EncodedValidationError::invariant("merged individual signature is incomplete")
            })?;
            Ok(IndividualSignatureBinding {
                individual_id: u32::try_from(index).map_err(|_| {
                    EncodedValidationError::resource("merged individual signature ID exceeds u32")
                })?,
                entity_id,
                declared,
            })
        })
        .collect()
}

type NormalizedSources = (
    Vec<NormalizedEdge>,
    Vec<NormalizedDisjoint>,
    Vec<NormalizedObjectConstraint>,
    Vec<NormalizedDataDomain>,
    Vec<NormalizedFact>,
    Vec<NormalizedObjectFact>,
    Vec<NormalizedObjectFact>,
    Vec<NormalizedEqualityFact>,
    Vec<NormalizedInequalityFact>,
);

#[allow(clippy::too_many_arguments)]
fn merge_normalized_sources(
    phases: &[(SymbolPhase, NamedClassPhase)],
    class_maps: &[Vec<u32>],
    individual_maps: &[Vec<u32>],
    class_domain: &DecodedSymbolDomain,
    source_object_roles: Option<&[ObjectRolePhase]>,
    merged_object_roles: Option<&ObjectRolePhase>,
    source_data_roles: Option<&[DataRolePhase]>,
    merged_data_roles: Option<&DataRolePhase>,
    budget: &mut PhaseBudget,
) -> EncodedResult<NormalizedSources> {
    let mut raw_edges = Vec::new();
    let mut raw_disjoints = Vec::new();
    let mut raw_object_constraints = Vec::new();
    let mut raw_data_domains = Vec::new();
    let mut raw_facts = Vec::new();
    let mut raw_object_facts = Vec::new();
    let mut raw_negative_object_facts = Vec::new();
    let mut raw_equalities = Vec::new();
    let mut raw_inequalities = Vec::new();
    for (phase_index, (_, phase)) in phases.iter().enumerate() {
        let class_map = class_maps
            .get(phase_index)
            .ok_or_else(|| EncodedValidationError::invariant("merged class mapping disappeared"))?;
        let individual_map = individual_maps.get(phase_index).ok_or_else(|| {
            EncodedValidationError::invariant("merged individual mapping disappeared")
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
                    super_class,
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
                    .checked_mul(size_of::<u32>())
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
                for class_id in &disjoint.classes {
                    classes.push(mapped_id(class_map, *class_id, "disjoint class")?);
                }
                raw_disjoints.try_reserve(1).map_err(|_| {
                    EncodedValidationError::resource(
                        "merged disjoint-class source allocation failed",
                    )
                })?;
                raw_disjoints.push(RawDisjoint {
                    classes,
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
                let class_id = mapped_id(
                    class_map,
                    constraint.class_id,
                    "object-property constraint class",
                )?;
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
                        class_id,
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
                let class_id = mapped_id(class_map, domain.class_id, "data-property domain class")?;
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
                        class_id,
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
        normalize_disjoints(raw_disjoints, class_domain, budget)?,
        normalize_object_constraints(raw_object_constraints, budget)?,
        normalize_data_domains(raw_data_domains, budget)?,
        normalize_facts(raw_facts, budget)?,
        normalize_object_facts(raw_object_facts, budget)?,
        normalize_object_facts(raw_negative_object_facts, budget)?,
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
