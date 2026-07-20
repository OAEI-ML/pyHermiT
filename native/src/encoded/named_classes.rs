//! Transactional named-class, named-individual, and axiom compilation.
//!
//! This phase owns a scalar-compatible `class_expression` symbol domain and
//! a scalar-compatible named `individual` domain. It compiles named-only
//! `SubClassOf`, `EquivalentClasses`, `DisjointClasses`, and `ClassAssertion`
//! axioms into the existing native predicate, clause, fact, and provenance
//! records. Predicate and clause identifiers are dense within this fragment
//! and must be remapped when a later phase assembles the complete program; no
//! fragment is publishable on its own.
// SPDX-License-Identifier: LGPL-3.0-or-later

#![forbid(unsafe_code)]

use std::mem::size_of;

use serde::Serialize;
use sha2::{Digest, Sha256};

use super::model::{ComponentValue, NodeId, NodeRef, ValidatedModel};
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
const CLASS_ASSERTION_TAG: u16 = 112;
const BUILTIN_PROVENANCE_INPUT: &[u8] = b"pyhermit:clausification:builtins:v1";
const DISJOINT_GUARD_DOMAIN: &[u8] = b"pyhermit:linear-disjoint-classes:v1\0";
const THING_DISPLAY: &str = "class:http://www.w3.org/2002/07/owl#Thing";
const NOTHING_DISPLAY: &str = "class:http://www.w3.org/2002/07/owl#Nothing";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct NamedClassPhaseLimits {
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
}

impl Default for NamedClassPhaseLimits {
    fn default() -> Self {
        Self {
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
    pub provenance: Vec<DecodedProvenanceEntry>,
    pub compiled_roots: usize,
    pub deferred_roots: usize,
    pub work: u64,
    pub owned_bytes: usize,
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

#[derive(Clone, Debug, Eq, PartialEq)]
struct NamedDisjointOutput {
    edges: Vec<RawEdge>,
    disjoint: Option<RawDisjoint>,
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

/// Compile the bounded named class and named `ABox` fragment without publishing a session.
pub fn compile_named_class_phase<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    limits: NamedClassPhaseLimits,
) -> EncodedResult<NamedClassPhase> {
    let mut budget = PhaseBudget::new(limits);
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

    let mut raw_edges = Vec::<RawEdge>::new();
    let mut raw_disjoints = Vec::<RawDisjoint>::new();
    let mut raw_facts = Vec::<RawFact>::new();
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
                    &class_domain,
                    root.node,
                    &mut budget,
                )? {
                    Some(edge) => {
                        compiled_roots = compiled_roots.checked_add(1).ok_or_else(|| {
                            EncodedValidationError::resource(
                                "named-class compiled-root count overflowed",
                            )
                        })?;
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
                    &class_domain,
                    root.node,
                    &mut budget,
                )? {
                    Some(edges) => {
                        compiled_roots = compiled_roots.checked_add(1).ok_or_else(|| {
                            EncodedValidationError::resource(
                                "named-class compiled-root count overflowed",
                            )
                        })?;
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
                    &class_domain,
                    root.node,
                    thing,
                    nothing,
                    &mut budget,
                )? {
                    Some(output) => {
                        compiled_roots = compiled_roots.checked_add(1).ok_or_else(|| {
                            EncodedValidationError::resource(
                                "named-class compiled-root count overflowed",
                            )
                        })?;
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
            RootHandler::ClassAssertion => {
                match named_class_assertion(
                    model,
                    symbols,
                    &class_signature,
                    &class_domain,
                    &individual_signature,
                    &individual_domain,
                    root.node,
                    &mut budget,
                )? {
                    Some(fact) => {
                        compiled_roots = compiled_roots.checked_add(1).ok_or_else(|| {
                            EncodedValidationError::resource(
                                "named-class compiled-root count overflowed",
                            )
                        })?;
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

    let edges = normalize_edges(raw_edges, &mut budget)?;
    let disjoints = normalize_disjoints(raw_disjoints, &class_domain, &mut budget)?;
    let facts = normalize_facts(raw_facts, &mut budget)?;
    let (provenance, provenance_keys) = freeze_provenance(&edges, &disjoints, &facts, &mut budget)?;
    let (predicates, predicate_by_class, guard_predicates, named_predicate) = freeze_predicates(
        &edges,
        &disjoints,
        &facts,
        thing,
        nothing,
        !individual_domain.values.is_empty(),
        &mut budget,
    )?;
    let clauses = freeze_clauses(
        &edges,
        &disjoints,
        nothing,
        &predicate_by_class,
        &guard_predicates,
        &provenance_keys,
        &mut budget,
    )?;
    let positive_facts = freeze_positive_facts(
        &facts,
        &individual_domain,
        thing,
        &predicate_by_class,
        named_predicate,
        &provenance_keys,
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
        provenance,
        compiled_roots,
        deferred_roots,
        work: budget.work,
        owned_bytes: budget.owned_bytes,
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
    domain: &DecodedSymbolDomain,
    root: NodeId,
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<RawEdge>> {
    let node = model.node(root)?;
    if node.tag() != SUBCLASS_TAG || node.field_count() != 3 {
        return Err(EncodedValidationError::invariant(
            "subclass root no longer has schema-1 shape",
        ));
    }
    if !annotations_are_empty(model, node, 2)? {
        return Ok(None);
    }
    let Some(sub_class) = named_class_field(model, symbols, signature, node, 0)? else {
        return Ok(None);
    };
    let Some(super_class) = named_class_field(model, symbols, signature, node, 1)? else {
        return Ok(None);
    };
    let provenance = subclass_digest(domain, sub_class, super_class, budget)?;
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
    domain: &DecodedSymbolDomain,
    root: NodeId,
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<Vec<RawEdge>>> {
    let node = model.node(root)?;
    if node.tag() != EQUIVALENT_CLASSES_TAG || node.field_count() != 2 {
        return Err(EncodedValidationError::invariant(
            "equivalent-classes root no longer has schema-1 shape",
        ));
    }
    if !annotations_are_empty(model, node, 1)? {
        return Ok(None);
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
    let provenance = equivalent_digest(domain, &classes, budget)?;
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
    domain: &DecodedSymbolDomain,
    root: NodeId,
    thing: u32,
    nothing: u32,
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<NamedDisjointOutput>> {
    let node = model.node(root)?;
    if node.tag() != DISJOINT_CLASSES_TAG || node.field_count() != 2 {
        return Err(EncodedValidationError::invariant(
            "disjoint-classes root no longer has schema-1 shape",
        ));
    }
    if !annotations_are_empty(model, node, 1)? {
        return Ok(None);
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
    let provenance = class_set_axiom_digest(
        domain,
        DISJOINT_CLASSES_TAG,
        &classes,
        "disjoint-classes",
        budget,
    )?;
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
        }));
    }

    Ok(Some(NamedDisjointOutput {
        edges: Vec::new(),
        disjoint: (live.len() >= 2).then_some(RawDisjoint {
            classes: live,
            provenance,
        }),
    }))
}

#[allow(clippy::too_many_arguments)]
fn named_class_assertion<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    class_signature: &[ClassSignatureBinding],
    class_domain: &DecodedSymbolDomain,
    individual_signature: &[IndividualSignatureBinding],
    individual_domain: &DecodedSymbolDomain,
    root: NodeId,
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<RawFact>> {
    let node = model.node(root)?;
    if node.tag() != CLASS_ASSERTION_TAG || node.field_count() != 3 {
        return Err(EncodedValidationError::invariant(
            "class-assertion root no longer has schema-1 shape",
        ));
    }
    if !annotations_are_empty(model, node, 2)? {
        return Ok(None);
    }
    let Some(class_id) = named_class_field(model, symbols, class_signature, node, 0)? else {
        return Ok(None);
    };
    let Some(individual_id) =
        named_individual_field(model, symbols, individual_signature, node, 1)?
    else {
        return Ok(None);
    };
    let provenance = class_assertion_digest(
        class_domain,
        class_id,
        individual_domain,
        individual_id,
        budget,
    )?;
    Ok(Some(RawFact {
        class_id,
        individual_id,
        provenance,
    }))
}

fn annotations_are_empty<B: ByteSource>(
    model: &ValidatedModel<B>,
    node: NodeRef,
    relative_field: usize,
) -> EncodedResult<bool> {
    let field_index = node
        .fields()
        .start
        .checked_add(relative_field)
        .ok_or_else(|| EncodedValidationError::invariant("annotation field index overflowed"))?;
    let component = required_component(model.field(field_index)?, "axiom annotations")?;
    let ComponentValue::Collection(annotations) = model.resolve(component)? else {
        return Err(EncodedValidationError::invariant(
            "axiom annotations did not resolve to a collection",
        ));
    };
    Ok(annotations.is_empty())
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

fn freeze_provenance(
    edges: &[NormalizedEdge],
    disjoints: &[NormalizedDisjoint],
    facts: &[NormalizedFact],
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
type GuardPredicateIndex = Vec<([u8; 32], u32, u32)>;
type FrozenPredicates = (
    Vec<DecodedPredicate>,
    PredicateIndex,
    GuardPredicateIndex,
    Option<u32>,
);

fn freeze_predicates(
    edges: &[NormalizedEdge],
    disjoints: &[NormalizedDisjoint],
    facts: &[NormalizedFact],
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
    for fact in facts {
        push_u32(&mut class_ids, fact.class_id, "predicate class", budget)?;
    }
    budget.claim_work(sort_work(class_ids.len()))?;
    class_ids.sort_unstable();
    class_ids.dedup();

    let mut ordered = Vec::<PendingPredicate>::new();
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
    let mut guard_predicates = Vec::new();
    let mut named_predicate = None;
    budget.claim_owned(
        ordered
            .len()
            .checked_mul(
                size_of::<DecodedPredicate>()
                    + size_of::<(u32, u32)>()
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
    guard_predicates.sort_unstable_by_key(|(digest, sequence, _)| (*digest, *sequence));
    Ok((
        predicates,
        predicate_by_class,
        guard_predicates,
        named_predicate,
    ))
}

fn freeze_clauses(
    edges: &[NormalizedEdge],
    disjoints: &[NormalizedDisjoint],
    nothing: u32,
    predicate_by_class: &[(u32, u32)],
    guard_predicates: &[([u8; 32], u32, u32)],
    provenance_keys: &[ProvenanceKey],
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<DecodedClause>> {
    let mut following = edges
        .len()
        .checked_add(1)
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

fn freeze_positive_facts(
    facts: &[NormalizedFact],
    individual_domain: &DecodedSymbolDomain,
    thing: u32,
    predicate_by_class: &[(u32, u32)],
    named_predicate: Option<u32>,
    provenance_keys: &[ProvenanceKey],
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
    let expected = individual_domain
        .values
        .len()
        .checked_mul(2)
        .and_then(|value| value.checked_add(facts.len()))
        .ok_or_else(|| EncodedValidationError::resource("positive-fact count overflowed"))?;
    budget.claim_work(facts.len())?;
    let merged_count = expected
        .checked_sub(facts.iter().filter(|fact| fact.class_id == thing).count())
        .ok_or_else(|| {
            EncodedValidationError::invariant("positive-fact merge count underflowed")
        })?;
    PhaseBudget::count(merged_count, budget.limits.max_facts, "positive fact count")?;
    let mut pending = Vec::<(u32, u32, u32)>::new();
    budget.claim_owned(
        expected
            .checked_mul(size_of::<(u32, u32, u32)>())
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
        pending.push((named, individual.identifier, builtin_provenance));
        pending.push((top, individual.identifier, builtin_provenance));
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
            fact.individual_id,
            provenance_id(provenance_keys, &fact.provenance, false)?,
        ));
    }
    budget.claim_work(sort_work(pending.len()))?;
    pending.sort_unstable();

    let mut merged = Vec::<(u32, u32, Vec<u32>)>::new();
    for (predicate, individual, provenance) in pending {
        budget.claim_work(1)?;
        if let Some(previous) = merged.last_mut() {
            if previous.0 == predicate && previous.1 == individual {
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
        budget.claim_owned(size_of::<(u32, u32, Vec<u32>)>() + size_of::<u32>())?;
        merged.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("positive-fact merge allocation failed")
        })?;
        let mut provenance_ids = Vec::new();
        provenance_ids.try_reserve_exact(1).map_err(|_| {
            EncodedValidationError::resource("positive-fact provenance allocation failed")
        })?;
        provenance_ids.push(provenance);
        merged.push((predicate, individual, provenance_ids));
    }
    PhaseBudget::count(merged.len(), budget.limits.max_facts, "positive fact count")?;
    if merged.len() != merged_count {
        return Err(EncodedValidationError::invariant(
            "positive-fact merge count disagrees with its exact bound",
        ));
    }

    let mut ordered = Vec::<(Vec<u8>, DecodedGroundAtom)>::new();
    budget.claim_owned(
        merged
            .len()
            .checked_mul(size_of::<(Vec<u8>, DecodedGroundAtom)>() + size_of::<DecodedTerm>())
            .ok_or_else(|| EncodedValidationError::resource("positive-fact output overflowed"))?,
    )?;
    ordered
        .try_reserve_exact(merged.len())
        .map_err(|_| EncodedValidationError::resource("positive-fact output allocation failed"))?;
    for (predicate_id, individual_id, provenance_ids) in merged {
        budget.claim_owned(
            provenance_ids
                .len()
                .checked_mul(size_of::<u32>())
                .ok_or_else(|| {
                    EncodedValidationError::resource("positive-fact provenance output overflowed")
                })?,
        )?;
        let key = ground_fact_key(predicate_id, individual_id, &provenance_ids);
        budget.claim_owned(key.len())?;
        ordered.push((
            key,
            DecodedGroundAtom {
                predicate_id,
                arguments: vec![DecodedTerm::Individual { individual_id }],
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

fn variable_atom(predicate_id: u32) -> DecodedAtom {
    DecodedAtom {
        predicate_id,
        arguments: vec![DecodedTerm::Variable {
            index: 0,
            sort: TermSort::Object,
        }],
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

fn subclass_digest(
    domain: &DecodedSymbolDomain,
    sub_class: u32,
    super_class: u32,
    budget: &mut PhaseBudget,
) -> EncodedResult<[u8; 32]> {
    let mut encoded = Vec::new();
    push_varint(&mut encoded, u64::from(SUBCLASS_TAG), budget)?;
    push_node(&mut encoded, class_key(domain, sub_class)?, budget)?;
    push_node(&mut encoded, class_key(domain, super_class)?, budget)?;
    push_empty_set(&mut encoded, budget)?;
    budget.claim_work(encoded.len())?;
    Ok(Sha256::digest(encoded).into())
}

fn class_assertion_digest(
    class_domain: &DecodedSymbolDomain,
    class_id: u32,
    individual_domain: &DecodedSymbolDomain,
    individual_id: u32,
    budget: &mut PhaseBudget,
) -> EncodedResult<[u8; 32]> {
    let mut encoded = Vec::new();
    push_varint(&mut encoded, u64::from(CLASS_ASSERTION_TAG), budget)?;
    push_node(&mut encoded, class_key(class_domain, class_id)?, budget)?;
    push_node(
        &mut encoded,
        individual_key(individual_domain, individual_id)?,
        budget,
    )?;
    push_empty_set(&mut encoded, budget)?;
    budget.claim_work(encoded.len())?;
    Ok(Sha256::digest(encoded).into())
}

fn equivalent_digest(
    domain: &DecodedSymbolDomain,
    classes: &[u32],
    budget: &mut PhaseBudget,
) -> EncodedResult<[u8; 32]> {
    class_set_axiom_digest(
        domain,
        EQUIVALENT_CLASSES_TAG,
        classes,
        "equivalent-classes",
        budget,
    )
}

fn class_set_axiom_digest(
    domain: &DecodedSymbolDomain,
    tag: u16,
    classes: &[u32],
    name: &'static str,
    budget: &mut PhaseBudget,
) -> EncodedResult<[u8; 32]> {
    let mut encoded = Vec::new();
    push_varint(&mut encoded, u64::from(tag), budget)?;
    push_byte(&mut encoded, 6, budget)?;
    push_varint(
        &mut encoded,
        u64::try_from(classes.len())
            .map_err(|_| EncodedValidationError::resource(format!("{name} arity exceeds u64")))?,
        budget,
    )?;
    for class_id in classes {
        push_frame(&mut encoded, class_key(domain, *class_id)?, budget)?;
    }
    push_empty_set(&mut encoded, budget)?;
    budget.claim_work(encoded.len())?;
    Ok(Sha256::digest(encoded).into())
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

fn individual_key(domain: &DecodedSymbolDomain, identifier: u32) -> EncodedResult<&[u8]> {
    domain
        .values
        .get(
            usize::try_from(identifier)
                .map_err(|_| EncodedValidationError::invariant("individual ID exceeds usize"))?,
        )
        .map(|value| value.key.as_slice())
        .ok_or_else(|| EncodedValidationError::invariant("individual ID is dangling"))
}

fn push_node(
    target: &mut Vec<u8>,
    encoded_node: &[u8],
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    push_byte(target, 1, budget)?;
    push_frame(target, encoded_node, budget)
}

fn push_empty_set(target: &mut Vec<u8>, budget: &mut PhaseBudget) -> EncodedResult<()> {
    push_byte(target, 6, budget)?;
    push_varint(target, 0, budget)
}

fn push_frame(target: &mut Vec<u8>, value: &[u8], budget: &mut PhaseBudget) -> EncodedResult<()> {
    let length = u64::try_from(value.len())
        .map_err(|_| EncodedValidationError::resource("canonical frame length exceeds u64"))?;
    push_varint(target, length, budget)?;
    push_bytes(target, value, budget)
}

fn push_varint(
    target: &mut Vec<u8>,
    mut value: u64,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    loop {
        let payload = u8::try_from(value & 0x7f)
            .map_err(|_| EncodedValidationError::invariant("canonical varint byte exceeds u8"))?;
        value >>= 7;
        push_byte(target, payload | if value == 0 { 0 } else { 0x80 }, budget)?;
        if value == 0 {
            return Ok(());
        }
    }
}

fn push_byte(target: &mut Vec<u8>, value: u8, budget: &mut PhaseBudget) -> EncodedResult<()> {
    budget.claim_owned(1)?;
    target
        .try_reserve(1)
        .map_err(|_| EncodedValidationError::resource("canonical axiom allocation failed"))?;
    target.push(value);
    Ok(())
}

fn push_bytes(target: &mut Vec<u8>, value: &[u8], budget: &mut PhaseBudget) -> EncodedResult<()> {
    budget.claim_owned(value.len())?;
    target
        .try_reserve(value.len())
        .map_err(|_| EncodedValidationError::resource("canonical axiom allocation failed"))?;
    target.extend_from_slice(value);
    Ok(())
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

fn atom_json(predicate_id: u32) -> String {
    format!(
        "{{\"arguments\":[{{\"index\":0,\"schema_version\":1,\"sort\":\"object\",\"type\":\"Variable\"}}],\"predicate_id\":{predicate_id},\"schema_version\":1,\"type\":\"Atom\"}}"
    )
}

fn ground_fact_key(predicate_id: u32, individual_id: u32, provenance_ids: &[u32]) -> Vec<u8> {
    let provenance = provenance_ids
        .iter()
        .map(u32::to_string)
        .collect::<Vec<_>>()
        .join(",");
    format!(
        "{{\"arguments\":[{{\"individual_id\":{individual_id},\"schema_version\":1,\"type\":\"IndividualTerm\"}}],\"predicate_id\":{predicate_id},\"provenance_ids\":[{provenance}],\"schema_version\":1,\"type\":\"GroundAtom\"}}"
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
