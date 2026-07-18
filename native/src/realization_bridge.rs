//! WPR4 realization adapter over isolated native entailment batches.
//!
//! The canonical result builder in `services::realization` deliberately accepts only
//! completed, entailed facts.  This bridge obtains those facts without Python callbacks:
//! it first reuses the native class hierarchy, then asks the transactional scheduler for
//! counterexamples to each finite public answer.  Query buffers are chunked, permanent
//! state is rolled back by the scheduler, and the existing operation-local realization
//! cache publishes only a complete result.
// SPDX-License-Identifier: LGPL-3.0-or-later

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use sha2::{Digest, Sha256};

use crate::cancel::CancellationState;
use crate::classification_bridge::classify_domain;
use crate::error::{ErrorKind, NativeError, NativeResult};
use crate::input_wire::{
    DecodedConfig, DecodedGroundAtom, DecodedOntology, DecodedPredicate, DecodedProgram,
    DecodedProvenanceEntry, DecodedQuery, DecodedSymbolDomain, DecodedTerm, PredicateKind,
    SymbolKind, TermSort,
};
use crate::native_tableau::ProductionTableau;
use crate::services::{
    realize_cached, ClassificationCache, ClassificationDomain, CompletedModelAccess,
    DataTargetFact, DifferentFromFact, DirectTypeFact, HierarchyIds, ModelIndividual,
    NamedIndividualRecord, ObjectTargetFact, RealizationCache, RealizationCacheKey, RealizationIds,
    RealizationLimits,
};
use crate::session::{OperationControl, QueryKey, SessionQuery, SessionScheduler};

const QUERY_BATCH_SIZE: usize = 4_096;
const MAX_SEMANTIC_TESTS: u64 = 100_000_000;

/// Return the committed realization or construct and atomically publish a complete replacement.
pub(crate) fn realize_ontology(
    ontology: &Arc<DecodedOntology>,
    config: &DecodedConfig,
    scheduler: &SessionScheduler<ProductionTableau>,
    classification_cache: &mut ClassificationCache,
    realization_cache: &mut RealizationCache,
    cancellation: &Arc<CancellationState>,
) -> NativeResult<Arc<RealizationIds>> {
    cancellation.poll()?;
    let key = RealizationCacheKey::new(ontology.metadata.ontology_fingerprint, 0);
    if let Some(result) = realization_cache.lookup(key) {
        cancellation.observe_memory(result.estimated_memory_bytes());
        cancellation.poll()?;
        return Ok(result);
    }
    if !scheduler
        .check_permanent(cancellation.as_ref())?
        .satisfiable
    {
        return Err(NativeError::inconsistent(
            "realization is undefined for an inconsistent ontology",
        ));
    }
    let hierarchy = classify_domain(
        ontology,
        config,
        scheduler,
        classification_cache,
        cancellation,
        ClassificationDomain::Classes,
    )?;
    let mut limits = RealizationLimits::default();
    if let Some(maximum) = config.max_memory_bytes {
        limits.max_memory_bytes = limits.max_memory_bytes.min(maximum);
    }
    let model = EntailedModel::build(
        ontology,
        scheduler,
        &hierarchy,
        key,
        limits,
        cancellation.as_ref(),
    )?;
    let result = realize_cached(&model, realization_cache, limits, cancellation.as_ref())?;
    Ok(result.into_ids())
}

#[derive(Clone, Debug)]
struct EntailedModel {
    key: RealizationCacheKey,
    named: Vec<NamedIndividualRecord>,
    class_node_count: u32,
    object_properties: Vec<u32>,
    data_properties: Vec<u32>,
    source_literals: Vec<u32>,
    direct_types: Vec<DirectTypeFact>,
    object_targets: Vec<ObjectTargetFact>,
    data_targets: Vec<DataTargetFact>,
    different_from: Vec<DifferentFromFact>,
}

impl EntailedModel {
    fn build(
        ontology: &Arc<DecodedOntology>,
        scheduler: &SessionScheduler<ProductionTableau>,
        hierarchy: &HierarchyIds,
        key: RealizationCacheKey,
        limits: RealizationLimits,
        control: &dyn OperationControl,
    ) -> NativeResult<Self> {
        hierarchy.validate()?;
        let object_properties = public_object_properties(&ontology.program)?;
        let data_properties = public_data_properties(&ontology.program)?;
        let source_literals = public_source_literals(&ontology.program)?;
        let literal_identities = source_literal_identities(&ontology.program, &source_literals)?;
        let mut semantic_tests = 0_u64;
        let mut result_facts = 0_u64;
        let groups = same_as_groups(ontology, scheduler, control, &mut semantic_tests)?;
        let named = named_records(&groups)?;

        let direct_types = direct_type_facts(
            ontology,
            scheduler,
            hierarchy,
            &groups,
            control,
            &mut semantic_tests,
            &mut result_facts,
            limits.max_facts,
        )?;
        let object_targets = object_target_facts(
            ontology,
            scheduler,
            &groups,
            &object_properties,
            control,
            &mut semantic_tests,
            &mut result_facts,
            limits.max_facts,
        )?;
        let data_targets = data_target_facts(
            ontology,
            scheduler,
            &groups,
            &data_properties,
            &source_literals,
            &literal_identities,
            control,
            &mut semantic_tests,
            &mut result_facts,
            limits.max_facts,
        )?;
        let different_from = different_from_facts(
            ontology,
            scheduler,
            &groups,
            control,
            &mut semantic_tests,
            &mut result_facts,
            limits.max_facts,
        )?;
        control.poll()?;
        Ok(Self {
            key,
            named,
            class_node_count: u32::try_from(hierarchy.nodes.len())
                .map_err(|_| NativeError::invariant("realization class-node count exceeds u32"))?,
            object_properties,
            data_properties,
            source_literals,
            direct_types,
            object_targets,
            data_targets,
            different_from,
        })
    }
}

impl CompletedModelAccess for EntailedModel {
    fn cache_key(&self) -> RealizationCacheKey {
        self.key
    }

    fn named_individuals(&self) -> &[NamedIndividualRecord] {
        &self.named
    }

    fn class_node_count(&self) -> u32 {
        self.class_node_count
    }

    fn object_property_ids(&self) -> &[u32] {
        &self.object_properties
    }

    fn data_property_ids(&self) -> &[u32] {
        &self.data_properties
    }

    fn source_literal_ids(&self) -> &[u32] {
        &self.source_literals
    }

    fn direct_type_facts(&self) -> &[DirectTypeFact] {
        &self.direct_types
    }

    fn object_target_facts(&self) -> &[ObjectTargetFact] {
        &self.object_targets
    }

    fn data_target_facts(&self) -> &[DataTargetFact] {
        &self.data_targets
    }

    fn different_from_facts(&self) -> &[DifferentFromFact] {
        &self.different_from
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Assertion {
    Class {
        class_id: u32,
        individual_id: u32,
    },
    Object {
        property_id: u32,
        subject_id: u32,
        object_id: u32,
    },
    Data {
        property_id: u32,
        subject_id: u32,
        source_literal_id: u32,
        data_identity_id: u32,
    },
    Same {
        left_id: u32,
        right_id: u32,
    },
    Different {
        left_id: u32,
        right_id: u32,
    },
}

fn same_as_groups(
    ontology: &Arc<DecodedOntology>,
    scheduler: &SessionScheduler<ProductionTableau>,
    control: &dyn OperationControl,
    semantic_tests: &mut u64,
) -> NativeResult<Vec<Vec<u32>>> {
    let individuals = &ontology.named_individuals;
    if individuals.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err(NativeError::wire(
            "named-individual realization domain is not canonical",
        ));
    }
    let index = individuals
        .iter()
        .copied()
        .enumerate()
        .map(|(position, individual)| (individual, position))
        .collect::<BTreeMap<_, _>>();
    let mut union = UnionFind::new(individuals.len());
    for fact in ontology
        .program
        .positive_facts
        .iter()
        .chain(&ontology.program.negative_facts)
    {
        let Some(predicate) = ontology
            .program
            .predicates
            .get(usize::try_from(fact.predicate_id).unwrap_or(usize::MAX))
        else {
            return Err(NativeError::wire(
                "realization seed fact predicate is dangling",
            ));
        };
        if predicate.kind != PredicateKind::Equality || fact.arguments.len() != 2 {
            continue;
        }
        let (
            DecodedTerm::Individual {
                individual_id: left,
            },
            DecodedTerm::Individual {
                individual_id: right,
            },
        ) = (&fact.arguments[0], &fact.arguments[1])
        else {
            continue;
        };
        if let (Some(left), Some(right)) = (index.get(left), index.get(right)) {
            union.union(*left, *right);
        }
    }

    if semantic_equality_possible(&ontology.program) {
        let representatives = seeded_representatives(individuals, &mut union);
        for (left_offset, left) in representatives.iter().copied().enumerate() {
            control.poll()?;
            let assertions = representatives[left_offset + 1..]
                .iter()
                .copied()
                .map(|right| Assertion::Same {
                    left_id: left,
                    right_id: right,
                })
                .collect::<Vec<_>>();
            charge_tests(semantic_tests, assertions.len())?;
            let outcomes = entails_many(ontology, scheduler, &assertions, control)?;
            let left_index = index[&left];
            for (assertion, entailed) in assertions.iter().zip(outcomes) {
                if !entailed {
                    continue;
                }
                let Assertion::Same { right_id, .. } = assertion else {
                    return Err(NativeError::invariant(
                        "same-as batch changed assertion kind",
                    ));
                };
                union.union(left_index, index[right_id]);
            }
        }
    }

    let mut grouped: BTreeMap<usize, Vec<u32>> = BTreeMap::new();
    for (position, individual) in individuals.iter().copied().enumerate() {
        grouped
            .entry(union.find(position))
            .or_default()
            .push(individual);
    }
    let mut groups = grouped.into_values().collect::<Vec<_>>();
    for group in &mut groups {
        group.sort_unstable();
        group.dedup();
    }
    groups.sort();
    Ok(groups)
}

fn seeded_representatives(individuals: &[u32], union: &mut UnionFind) -> Vec<u32> {
    let mut representatives = BTreeMap::new();
    for (position, individual) in individuals.iter().copied().enumerate() {
        representatives
            .entry(union.find(position))
            .and_modify(|value: &mut u32| *value = (*value).min(individual))
            .or_insert(individual);
    }
    representatives.into_values().collect()
}

fn named_records(groups: &[Vec<u32>]) -> NativeResult<Vec<NamedIndividualRecord>> {
    let mut records = Vec::new();
    for group in groups {
        let equality_key = u64::from(
            *group
                .first()
                .ok_or_else(|| NativeError::invariant("realization produced an empty group"))?,
        );
        records.extend(
            group
                .iter()
                .copied()
                .map(|individual_id| NamedIndividualRecord {
                    individual_id,
                    equality_key,
                }),
        );
    }
    records.sort_by_key(|record| record.individual_id);
    Ok(records)
}

#[allow(clippy::too_many_arguments)]
fn direct_type_facts(
    ontology: &Arc<DecodedOntology>,
    scheduler: &SessionScheduler<ProductionTableau>,
    hierarchy: &HierarchyIds,
    groups: &[Vec<u32>],
    control: &dyn OperationControl,
    semantic_tests: &mut u64,
    result_facts: &mut u64,
    max_facts: u64,
) -> NativeResult<Vec<DirectTypeFact>> {
    let child_sets = hierarchy_children(hierarchy)?;
    let mut facts = Vec::new();
    for group in groups {
        control.poll()?;
        let individual = *group
            .first()
            .ok_or_else(|| NativeError::invariant("realization same-as group is empty"))?;
        let mut assertions = Vec::new();
        let mut node_ids = Vec::new();
        let mut selected = BTreeSet::new();
        for (node_index, members) in hierarchy.nodes.iter().enumerate() {
            let node_id = u32::try_from(node_index)
                .map_err(|_| NativeError::invariant("class node index exceeds u32"))?;
            if node_id == hierarchy.top_node {
                selected.insert(node_id);
            } else if node_id != hierarchy.bottom_node {
                assertions.push(Assertion::Class {
                    class_id: *members.first().ok_or_else(|| {
                        NativeError::invariant("class hierarchy contains an empty node")
                    })?,
                    individual_id: individual,
                });
                node_ids.push(node_id);
            }
        }
        charge_tests(semantic_tests, assertions.len())?;
        let outcomes = entails_many(ontology, scheduler, &assertions, control)?;
        for (node_id, entailed) in node_ids.into_iter().zip(outcomes) {
            if entailed {
                selected.insert(node_id);
            }
        }
        for node_id in selected.iter().copied() {
            let node_index = usize::try_from(node_id)
                .map_err(|_| NativeError::invariant("class node ID cannot fit usize"))?;
            if child_sets[node_index]
                .iter()
                .all(|child| !selected.contains(child))
            {
                charge_fact(result_facts, max_facts)?;
                facts.push(DirectTypeFact {
                    subject: ModelIndividual::Named(individual),
                    class_node_id: node_id,
                });
            }
        }
    }
    Ok(facts)
}

#[allow(clippy::too_many_arguments)]
fn object_target_facts(
    ontology: &Arc<DecodedOntology>,
    scheduler: &SessionScheduler<ProductionTableau>,
    groups: &[Vec<u32>],
    properties: &[u32],
    control: &dyn OperationControl,
    semantic_tests: &mut u64,
    result_facts: &mut u64,
    max_facts: u64,
) -> NativeResult<Vec<ObjectTargetFact>> {
    let top = ontology.program.role_model.top_object_role_id;
    let bottom = ontology.program.role_model.bottom_object_role_id;
    let representatives = group_representatives(groups)?;
    let mut facts = Vec::new();
    for subject in &representatives {
        for property in properties {
            control.poll()?;
            if *property == bottom {
                continue;
            }
            if *property == top {
                for target in &representatives {
                    charge_fact(result_facts, max_facts)?;
                    facts.push(ObjectTargetFact {
                        subject: ModelIndividual::Named(*subject),
                        property_id: *property,
                        target: ModelIndividual::Named(*target),
                    });
                }
                continue;
            }
            let assertions = representatives
                .iter()
                .copied()
                .map(|object_id| Assertion::Object {
                    property_id: *property,
                    subject_id: *subject,
                    object_id,
                })
                .collect::<Vec<_>>();
            charge_tests(semantic_tests, assertions.len())?;
            let outcomes = entails_many(ontology, scheduler, &assertions, control)?;
            for (object_id, entailed) in representatives.iter().copied().zip(outcomes) {
                if entailed {
                    charge_fact(result_facts, max_facts)?;
                    facts.push(ObjectTargetFact {
                        subject: ModelIndividual::Named(*subject),
                        property_id: *property,
                        target: ModelIndividual::Named(object_id),
                    });
                }
            }
        }
    }
    Ok(facts)
}

#[allow(clippy::too_many_arguments)]
fn data_target_facts(
    ontology: &Arc<DecodedOntology>,
    scheduler: &SessionScheduler<ProductionTableau>,
    groups: &[Vec<u32>],
    properties: &[u32],
    source_literals: &[u32],
    literal_identities: &BTreeMap<u32, u32>,
    control: &dyn OperationControl,
    semantic_tests: &mut u64,
    result_facts: &mut u64,
    max_facts: u64,
) -> NativeResult<Vec<DataTargetFact>> {
    let top = ontology.program.role_model.top_data_property_id;
    let bottom = ontology.program.role_model.bottom_data_property_id;
    let representatives = group_representatives(groups)?;
    let mut facts = Vec::new();
    for subject in representatives {
        for property in properties {
            control.poll()?;
            if *property == bottom {
                continue;
            }
            if *property == top {
                for source_literal_id in source_literals {
                    charge_fact(result_facts, max_facts)?;
                    facts.push(DataTargetFact {
                        subject: ModelIndividual::Named(subject),
                        property_id: *property,
                        source_literal_id: *source_literal_id,
                    });
                }
                continue;
            }
            let assertions = source_literals
                .iter()
                .copied()
                .map(|source_literal_id| {
                    Ok(Assertion::Data {
                        property_id: *property,
                        subject_id: subject,
                        source_literal_id,
                        data_identity_id: *literal_identities.get(&source_literal_id).ok_or_else(
                            || {
                                NativeError::invariant(
                                    "source literal lacks a native data identity",
                                )
                            },
                        )?,
                    })
                })
                .collect::<NativeResult<Vec<_>>>()?;
            charge_tests(semantic_tests, assertions.len())?;
            let outcomes = entails_many(ontology, scheduler, &assertions, control)?;
            for (source_literal_id, entailed) in source_literals.iter().copied().zip(outcomes) {
                if entailed {
                    charge_fact(result_facts, max_facts)?;
                    facts.push(DataTargetFact {
                        subject: ModelIndividual::Named(subject),
                        property_id: *property,
                        source_literal_id,
                    });
                }
            }
        }
    }
    Ok(facts)
}

#[allow(clippy::too_many_arguments)]
fn different_from_facts(
    ontology: &Arc<DecodedOntology>,
    scheduler: &SessionScheduler<ProductionTableau>,
    groups: &[Vec<u32>],
    control: &dyn OperationControl,
    semantic_tests: &mut u64,
    result_facts: &mut u64,
    max_facts: u64,
) -> NativeResult<Vec<DifferentFromFact>> {
    if !semantic_inequality_possible(&ontology.program) {
        return Ok(Vec::new());
    }
    let representatives = group_representatives(groups)?;
    let mut facts = Vec::new();
    for (left_offset, left) in representatives.iter().copied().enumerate() {
        control.poll()?;
        let rights = &representatives[left_offset + 1..];
        let assertions = rights
            .iter()
            .copied()
            .map(|right_id| Assertion::Different {
                left_id: left,
                right_id,
            })
            .collect::<Vec<_>>();
        charge_tests(semantic_tests, assertions.len())?;
        let outcomes = entails_many(ontology, scheduler, &assertions, control)?;
        for (right, entailed) in rights.iter().copied().zip(outcomes) {
            if entailed {
                charge_fact(result_facts, max_facts)?;
                facts.push(DifferentFromFact {
                    left: ModelIndividual::Named(left),
                    right: ModelIndividual::Named(right),
                });
            }
        }
    }
    Ok(facts)
}

fn entails_many(
    ontology: &Arc<DecodedOntology>,
    scheduler: &SessionScheduler<ProductionTableau>,
    assertions: &[Assertion],
    control: &dyn OperationControl,
) -> NativeResult<Vec<bool>> {
    let mut outcomes = Vec::new();
    outcomes
        .try_reserve_exact(assertions.len())
        .map_err(|_| NativeError::invariant("realization outcome allocation failed"))?;
    for chunk in assertions.chunks(QUERY_BATCH_SIZE) {
        control.poll()?;
        let queries = chunk
            .iter()
            .copied()
            .map(|assertion| counterexample_query(ontology, assertion))
            .collect::<NativeResult<Vec<_>>>()?;
        let results = scheduler.check_many(&queries, control)?;
        if results.len() != chunk.len() {
            return Err(NativeError::invariant(
                "realization check batch returned the wrong result count",
            ));
        }
        outcomes.extend(results.into_iter().map(|result| !result.satisfiable));
    }
    control.poll()?;
    Ok(outcomes)
}

fn counterexample_query(
    ontology: &DecodedOntology,
    assertion: Assertion,
) -> NativeResult<SessionQuery<DecodedQuery>> {
    let query_hash = assertion_hash(&ontology.metadata.ontology_fingerprint, assertion);
    let first_local_symbols = symbol_boundaries(&ontology.program.symbol_domains)?;
    let first_local_predicate_id = u32::try_from(ontology.program.predicates.len())
        .map_err(|_| NativeError::wire("realization predicate boundary exceeds u32"))?;
    let mut predicates = ontology.program.predicates.clone();
    let (counter_kind, arguments) = match assertion {
        Assertion::Class {
            class_id,
            individual_id,
        } => {
            ensure_opposite_pair(
                &mut predicates,
                PredicateKind::Concept,
                PredicateKind::NegatedConcept,
                &[TermSort::Object],
                Some(class_id),
                None,
            )?;
            (
                PredicateKind::NegatedConcept,
                vec![DecodedTerm::Individual { individual_id }],
            )
        }
        Assertion::Object {
            property_id,
            subject_id,
            object_id,
        } => {
            ensure_opposite_pair(
                &mut predicates,
                PredicateKind::ObjectRole,
                PredicateKind::NegatedObjectRole,
                &[TermSort::Object, TermSort::Object],
                None,
                Some(property_id),
            )?;
            (
                PredicateKind::NegatedObjectRole,
                vec![
                    DecodedTerm::Individual {
                        individual_id: subject_id,
                    },
                    DecodedTerm::Individual {
                        individual_id: object_id,
                    },
                ],
            )
        }
        Assertion::Data {
            property_id,
            subject_id,
            source_literal_id,
            data_identity_id,
        } => {
            ensure_opposite_pair(
                &mut predicates,
                PredicateKind::DataRole,
                PredicateKind::NegatedDataRole,
                &[TermSort::Object, TermSort::Data],
                None,
                Some(property_id),
            )?;
            (
                PredicateKind::NegatedDataRole,
                vec![
                    DecodedTerm::Individual {
                        individual_id: subject_id,
                    },
                    DecodedTerm::Data {
                        source_literal_id,
                        data_identity_id,
                    },
                ],
            )
        }
        Assertion::Same { left_id, right_id } => {
            ensure_opposite_pair(
                &mut predicates,
                PredicateKind::Equality,
                PredicateKind::Inequality,
                &[TermSort::Object, TermSort::Object],
                None,
                None,
            )?;
            (
                PredicateKind::Inequality,
                vec![
                    DecodedTerm::Individual {
                        individual_id: left_id,
                    },
                    DecodedTerm::Individual {
                        individual_id: right_id,
                    },
                ],
            )
        }
        Assertion::Different { left_id, right_id } => {
            ensure_opposite_pair(
                &mut predicates,
                PredicateKind::Equality,
                PredicateKind::Inequality,
                &[TermSort::Object, TermSort::Object],
                None,
                None,
            )?;
            (
                PredicateKind::Equality,
                vec![
                    DecodedTerm::Individual {
                        individual_id: left_id,
                    },
                    DecodedTerm::Individual {
                        individual_id: right_id,
                    },
                ],
            )
        }
    };
    let predicate_id = find_predicate_id(
        &predicates,
        counter_kind,
        assertion_argument_sorts(assertion),
        assertion_symbol_id(assertion),
        assertion_role_id(assertion),
    )?;
    let fact = DecodedGroundAtom {
        predicate_id,
        arguments,
        provenance_ids: vec![0],
    };
    let mut expressivity = ontology.program.expressivity;
    expressivity.abox = true;
    let overlay = DecodedProgram {
        symbol_domains: ontology.program.symbol_domains.clone(),
        predicates,
        clauses: Vec::new(),
        positive_facts: vec![fact],
        negative_facts: Vec::new(),
        ground_disjunctions: Vec::new(),
        role_model: ontology.program.role_model.clone(),
        datatype_model: ontology.program.datatype_model.clone(),
        expressivity,
        provenance: vec![DecodedProvenanceEntry {
            provenance_id: 0,
            source_sha256: vec![query_hash],
            generated: true,
        }],
    };
    let query = DecodedQuery {
        permanent_program_sha256: ontology.metadata.program_sha256,
        query_hash,
        overlay_program_sha256: Some(query_hash),
        first_local_predicate_id,
        first_local_symbols,
        requires_rebuild: false,
        program: Some(overlay),
        reason: None,
        interpretation: vec![format!("realization:{assertion:?}")],
    };
    Ok(SessionQuery::new(QueryKey::new(query_hash), query))
}

fn ensure_opposite_pair(
    predicates: &mut Vec<DecodedPredicate>,
    positive: PredicateKind,
    negative: PredicateKind,
    sorts: &[TermSort],
    symbol_id: Option<u32>,
    role_id: Option<u32>,
) -> NativeResult<()> {
    ensure_predicate(predicates, positive, sorts, symbol_id, role_id)?;
    ensure_predicate(predicates, negative, sorts, symbol_id, role_id)?;
    Ok(())
}

fn ensure_predicate(
    predicates: &mut Vec<DecodedPredicate>,
    kind: PredicateKind,
    sorts: &[TermSort],
    symbol_id: Option<u32>,
    role_id: Option<u32>,
) -> NativeResult<u32> {
    let matches = predicates
        .iter()
        .filter(|predicate| {
            predicate.kind == kind
                && predicate.argument_sorts == sorts
                && predicate.symbol_id == symbol_id
                && predicate.role_id == role_id
                && predicate.cardinality.is_none()
                && predicate.filler_predicate_id.is_none()
                && predicate.annotation.is_empty()
        })
        .map(|predicate| predicate.predicate_id)
        .collect::<Vec<_>>();
    if matches.len() > 1 {
        return Err(NativeError::wire(
            "realization predicate identity is duplicated",
        ));
    }
    if let Some(identifier) = matches.first().copied() {
        return Ok(identifier);
    }
    let predicate_id = u32::try_from(predicates.len())
        .map_err(|_| NativeError::wire("realization predicate ID exceeds u32"))?;
    predicates.push(DecodedPredicate {
        predicate_id,
        kind,
        argument_sorts: sorts.to_vec(),
        symbol_id,
        role_id,
        cardinality: None,
        filler_predicate_id: None,
        annotation: Vec::new(),
        internal_key: None,
    });
    Ok(predicate_id)
}

fn find_predicate_id(
    predicates: &[DecodedPredicate],
    kind: PredicateKind,
    sorts: &[TermSort],
    symbol_id: Option<u32>,
    role_id: Option<u32>,
) -> NativeResult<u32> {
    let values = predicates
        .iter()
        .filter(|predicate| {
            predicate.kind == kind
                && predicate.argument_sorts == sorts
                && predicate.symbol_id == symbol_id
                && predicate.role_id == role_id
                && predicate.cardinality.is_none()
                && predicate.filler_predicate_id.is_none()
                && predicate.annotation.is_empty()
        })
        .map(|predicate| predicate.predicate_id)
        .collect::<Vec<_>>();
    match values.as_slice() {
        [identifier] => Ok(*identifier),
        [] => Err(NativeError::invariant(
            "realization counterexample predicate was not installed",
        )),
        _ => Err(NativeError::wire(
            "realization counterexample predicate is ambiguous",
        )),
    }
}

const fn assertion_symbol_id(assertion: Assertion) -> Option<u32> {
    match assertion {
        Assertion::Class { class_id, .. } => Some(class_id),
        Assertion::Object { .. }
        | Assertion::Data { .. }
        | Assertion::Same { .. }
        | Assertion::Different { .. } => None,
    }
}

const fn assertion_argument_sorts(assertion: Assertion) -> &'static [TermSort] {
    match assertion {
        Assertion::Class { .. } => &[TermSort::Object],
        Assertion::Object { .. } | Assertion::Same { .. } | Assertion::Different { .. } => {
            &[TermSort::Object, TermSort::Object]
        }
        Assertion::Data { .. } => &[TermSort::Object, TermSort::Data],
    }
}

const fn assertion_role_id(assertion: Assertion) -> Option<u32> {
    match assertion {
        Assertion::Object { property_id, .. } | Assertion::Data { property_id, .. } => {
            Some(property_id)
        }
        Assertion::Class { .. } | Assertion::Same { .. } | Assertion::Different { .. } => None,
    }
}

fn assertion_hash(ontology_fingerprint: &[u8; 32], assertion: Assertion) -> [u8; 32] {
    let mut digest = Sha256::new();
    digest.update(b"pyhermit:native-realization-query:v1\0");
    digest.update(ontology_fingerprint);
    match assertion {
        Assertion::Class {
            class_id,
            individual_id,
        } => {
            digest.update([0]);
            digest.update(class_id.to_le_bytes());
            digest.update(individual_id.to_le_bytes());
        }
        Assertion::Object {
            property_id,
            subject_id,
            object_id,
        } => {
            digest.update([1]);
            digest.update(property_id.to_le_bytes());
            digest.update(subject_id.to_le_bytes());
            digest.update(object_id.to_le_bytes());
        }
        Assertion::Data {
            property_id,
            subject_id,
            source_literal_id,
            data_identity_id,
        } => {
            digest.update([2]);
            digest.update(property_id.to_le_bytes());
            digest.update(subject_id.to_le_bytes());
            digest.update(source_literal_id.to_le_bytes());
            digest.update(data_identity_id.to_le_bytes());
        }
        Assertion::Same { left_id, right_id } => {
            digest.update([3]);
            digest.update(left_id.to_le_bytes());
            digest.update(right_id.to_le_bytes());
        }
        Assertion::Different { left_id, right_id } => {
            digest.update([4]);
            digest.update(left_id.to_le_bytes());
            digest.update(right_id.to_le_bytes());
        }
    }
    digest.finalize().into()
}

fn public_object_properties(program: &DecodedProgram) -> NativeResult<Vec<u32>> {
    public_symbols(program, SymbolKind::ObjectRole, |display| {
        display.starts_with("object_property:") || display.starts_with("inverse_object_property:")
    })
}

fn public_data_properties(program: &DecodedProgram) -> NativeResult<Vec<u32>> {
    public_symbols(program, SymbolKind::DataProperty, |display| {
        display.starts_with("data_property:")
    })
}

fn public_source_literals(program: &DecodedProgram) -> NativeResult<Vec<u32>> {
    public_symbols(program, SymbolKind::SourceLiteral, |_display| true)
}

fn public_symbols(
    program: &DecodedProgram,
    kind: SymbolKind,
    include: impl Fn(&str) -> bool,
) -> NativeResult<Vec<u32>> {
    let domain = program
        .domain(kind)
        .ok_or_else(|| NativeError::wire("realization symbol domain is absent"))?;
    let values = domain
        .values
        .iter()
        .filter(|value| !value.query_local && !value.generated && include(&value.display))
        .map(|value| value.identifier)
        .collect::<Vec<_>>();
    if values.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err(NativeError::wire(
            "realization public symbol IDs are not canonical",
        ));
    }
    Ok(values)
}

fn source_literal_identities(
    program: &DecodedProgram,
    source_literals: &[u32],
) -> NativeResult<BTreeMap<u32, u32>> {
    let identities = program
        .datatype_model
        .literal_identities
        .iter()
        .map(|identity| (identity.source_literal_id, identity.data_identity_id))
        .collect::<BTreeMap<_, _>>();
    if identities.len() != program.datatype_model.literal_identities.len()
        || source_literals
            .iter()
            .any(|source| !identities.contains_key(source))
    {
        return Err(NativeError::wire(
            "realization source-literal identity map is incomplete",
        ));
    }
    Ok(identities)
}

fn symbol_boundaries(domains: &[DecodedSymbolDomain]) -> NativeResult<[u32; 8]> {
    let mut boundaries = [0_u32; 8];
    for domain in domains {
        boundaries[domain.kind as usize] = u32::try_from(domain.values.len())
            .map_err(|_| NativeError::wire("realization symbol boundary exceeds u32"))?;
    }
    Ok(boundaries)
}

fn hierarchy_children(hierarchy: &HierarchyIds) -> NativeResult<Vec<BTreeSet<u32>>> {
    let mut children = vec![BTreeSet::new(); hierarchy.nodes.len()];
    for &(child, parent) in &hierarchy.edges {
        let index = usize::try_from(parent)
            .map_err(|_| NativeError::invariant("hierarchy parent cannot fit usize"))?;
        children
            .get_mut(index)
            .ok_or_else(|| NativeError::invariant("hierarchy parent is dangling"))?
            .insert(child);
    }
    Ok(children)
}

fn group_representatives(groups: &[Vec<u32>]) -> NativeResult<Vec<u32>> {
    groups
        .iter()
        .map(|group| {
            group
                .first()
                .copied()
                .ok_or_else(|| NativeError::invariant("realization same-as group is empty"))
        })
        .collect()
}

fn semantic_equality_possible(program: &DecodedProgram) -> bool {
    if program.expressivity.nominals
        || program.expressivity.number_restrictions
        || program.expressivity.keys
    {
        return true;
    }
    // Asserted equalities were already folded into the seed union above.  Only a rule or
    // disjunction that can derive a new equality justifies the quadratic candidate set.
    semantic_predicate_can_be_produced(program, false, |predicate| {
        matches!(
            predicate.kind,
            PredicateKind::Equality | PredicateKind::AnnotatedEquality
        ) && predicate.argument_sorts == [TermSort::Object, TermSort::Object]
    })
}

fn semantic_inequality_possible(program: &DecodedProgram) -> bool {
    semantic_predicate_can_be_produced(program, true, |predicate| {
        predicate.kind == PredicateKind::Inequality
            && predicate.argument_sorts == [TermSort::Object, TermSort::Object]
    })
}

fn semantic_predicate_can_be_produced(
    program: &DecodedProgram,
    include_asserted_facts: bool,
    selected: impl Fn(&DecodedPredicate) -> bool,
) -> bool {
    let predicate_ids = program
        .predicates
        .iter()
        .filter(|predicate| selected(predicate))
        .map(|predicate| predicate.predicate_id)
        .collect::<BTreeSet<_>>();
    if predicate_ids.is_empty() {
        return false;
    }
    let appears = (include_asserted_facts
        && program
            .positive_facts
            .iter()
            .chain(&program.negative_facts)
            .any(|fact| predicate_ids.contains(&fact.predicate_id)))
        || program.clauses.iter().any(|clause| {
            clause
                .head
                .iter()
                .any(|atom| predicate_ids.contains(&atom.predicate_id))
        })
        || program.ground_disjunctions.iter().any(|disjunction| {
            disjunction
                .disjuncts
                .iter()
                .any(|atom| predicate_ids.contains(&atom.predicate_id))
        });
    appears
}

fn charge_tests(total: &mut u64, additional: usize) -> NativeResult<()> {
    *total = total
        .checked_add(u64::try_from(additional).unwrap_or(u64::MAX))
        .ok_or_else(|| NativeError::invariant("realization semantic-test count overflow"))?;
    if *total > MAX_SEMANTIC_TESTS {
        return Err(resource_error(
            "max_realization_semantic_tests",
            *total,
            MAX_SEMANTIC_TESTS,
        ));
    }
    Ok(())
}

fn charge_fact(total: &mut u64, allowed: u64) -> NativeResult<()> {
    *total = total
        .checked_add(1)
        .ok_or_else(|| NativeError::invariant("realization fact count overflow"))?;
    if *total > allowed {
        return Err(resource_error("max_facts", *total, allowed));
    }
    Ok(())
}

fn resource_error(limit: &'static str, observed: u64, allowed: u64) -> NativeError {
    NativeError::new(
        ErrorKind::Resource,
        "RESOURCE_LIMIT",
        format!("realization exceeded {limit}"),
    )
    .with_context("limit", limit)
    .with_context("observed", observed.to_string())
    .with_context("allowed", allowed.to_string())
}

#[derive(Clone, Debug)]
struct UnionFind {
    parent: Vec<usize>,
    rank: Vec<u8>,
}

impl UnionFind {
    fn new(size: usize) -> Self {
        Self {
            parent: (0..size).collect(),
            rank: vec![0; size],
        }
    }

    fn find(&mut self, value: usize) -> usize {
        let parent = self.parent[value];
        if parent != value {
            self.parent[value] = self.find(parent);
        }
        self.parent[value]
    }

    fn union(&mut self, left: usize, right: usize) {
        let left = self.find(left);
        let right = self.find(right);
        if left == right {
            return;
        }
        match self.rank[left].cmp(&self.rank[right]) {
            std::cmp::Ordering::Less => self.parent[left] = right,
            std::cmp::Ordering::Greater => self.parent[right] = left,
            std::cmp::Ordering::Equal => {
                self.parent[right] = left;
                self.rank[left] = self.rank[left].saturating_add(1);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn union_find_and_group_order_are_canonical() -> NativeResult<()> {
        let individuals = vec![1, 3, 8, 13];
        let mut union = UnionFind::new(individuals.len());
        union.union(0, 2);
        union.union(1, 3);
        let mut grouped: BTreeMap<usize, Vec<u32>> = BTreeMap::new();
        for (position, individual) in individuals.into_iter().enumerate() {
            grouped
                .entry(union.find(position))
                .or_default()
                .push(individual);
        }
        let mut groups = grouped.into_values().collect::<Vec<_>>();
        groups.sort();
        assert_eq!(groups, vec![vec![1, 8], vec![3, 13]]);
        assert_eq!(
            named_records(&groups)?,
            vec![
                NamedIndividualRecord {
                    individual_id: 1,
                    equality_key: 1,
                },
                NamedIndividualRecord {
                    individual_id: 3,
                    equality_key: 3,
                },
                NamedIndividualRecord {
                    individual_id: 8,
                    equality_key: 1,
                },
                NamedIndividualRecord {
                    individual_id: 13,
                    equality_key: 3,
                },
            ]
        );
        Ok(())
    }

    #[test]
    fn direct_types_keep_only_selected_leaf_nodes() -> NativeResult<()> {
        let hierarchy = HierarchyIds {
            nodes: vec![vec![0], vec![1], vec![2], vec![3]],
            edges: vec![(0, 1), (1, 2), (2, 3)],
            top_node: 3,
            bottom_node: 0,
        };
        hierarchy.validate()?;
        let children = hierarchy_children(&hierarchy)?;
        let selected = BTreeSet::from([1, 2, 3]);
        let direct = selected
            .iter()
            .copied()
            .filter(|node| {
                children[usize::try_from(*node).unwrap_or(usize::MAX)]
                    .iter()
                    .all(|child| !selected.contains(child))
            })
            .collect::<Vec<_>>();
        assert_eq!(direct, vec![1]);
        Ok(())
    }
}
