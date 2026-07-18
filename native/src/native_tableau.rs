//! Concrete production bridge from decoded IR to the transactional session scheduler.
// SPDX-License-Identifier: LGPL-3.0-or-later

use std::collections::BTreeMap;
use std::sync::Arc;

use crate::branching::BranchTransition;
use crate::cancel::CancellationState;
use crate::error::{NativeError, NativeResult};
use crate::existentials::{
    expansion_to_native, AssertedOnlyDatatypes, BranchTransition as ExpansionBranchTransition,
    ExpansionStatus, NativeExpansionControl, RuntimeExpansionAccess, RuntimeExpansionState,
};
use crate::input_wire::{
    DecodedConfig, DecodedExpressivity, DecodedGroundAtom, DecodedGroundDisjunction,
    DecodedOntology, DecodedProgram, DecodedProvenanceEntry, DecodedQuery, PredicateKind,
};
use crate::nominals::NominalIntroductionManager;
use crate::program_bridge::{load_permanent_rule_state, LoadedRuleState};
use crate::rules::RuleEngineCheckpoint;
use crate::session::{
    ClashResolution, DatatypePhaseResult, DeltaPhaseResult, NativeTableau, OperationControl,
    OperationDisposition, PhaseProgress, SessionQuery, ValidationStatus,
};
use crate::store::TableauKernel;

/// The currently integrated production tableau.
///
/// Rule saturation, equality merging, and ground disjunction search execute natively. Owners for
/// role automata and datatype semantics are loaded once with the permanent state, but their
/// remaining scheduler adapters are deliberately capability-gated until their full semantics are
/// connected. Consequently this type is usable by Rust integration tests without making the
/// extension advertise WPR4's `full_reasoner` handshake prematurely.
pub struct ProductionTableau {
    ontology: Arc<DecodedOntology>,
    config: DecodedConfig,
    cancellation: Arc<CancellationState>,
    permanent: LoadedRuleState,
    query: Option<LoadedRuleState>,
    query_expressivity: Option<DecodedExpressivity>,
}

pub struct ProductionCheckpoint {
    kernel: TableauKernel,
    engine: RuleEngineCheckpoint,
    nominals: NominalIntroductionManager,
}

impl ProductionTableau {
    pub fn new(
        ontology: Arc<DecodedOntology>,
        config: DecodedConfig,
        cancellation: Arc<CancellationState>,
        permanent: LoadedRuleState,
    ) -> NativeResult<Self> {
        permanent.kernel.check_invariants()?;
        permanent.engine.check_invariants(&permanent.kernel)?;
        Ok(Self {
            ontology,
            config,
            cancellation,
            permanent,
            query: None,
            query_expressivity: None,
        })
    }

    fn active(&self) -> &LoadedRuleState {
        self.query.as_ref().unwrap_or(&self.permanent)
    }

    fn active_mut(&mut self) -> &mut LoadedRuleState {
        self.query.as_mut().unwrap_or(&mut self.permanent)
    }

    fn active_expressivity(&self) -> DecodedExpressivity {
        match self.query_expressivity {
            Some(value) => value,
            None => self.ontology.program.expressivity,
        }
    }

    #[must_use]
    pub fn logical_counts(&self) -> (u64, u64, u64) {
        self.active().kernel.logical_counts()
    }
}

impl NativeTableau for ProductionTableau {
    type Query = DecodedQuery;
    type OperationCheckpoint = ProductionCheckpoint;

    fn estimated_memory_bytes(&self) -> NativeResult<u64> {
        let active = self.active();
        active
            .kernel
            .estimated_memory_bytes()?
            .checked_add(active.engine.estimated_memory_bytes()?)
            .ok_or_else(|| NativeError::invariant("native tableau memory estimate overflow"))
    }

    fn operation_checkpoint(
        &mut self,
        control: &dyn OperationControl,
    ) -> NativeResult<Self::OperationCheckpoint> {
        if self.query.is_some() {
            return Err(NativeError::invariant(
                "query state survived into a new native operation",
            ));
        }
        control.poll()?;
        let kernel = self.permanent.kernel.clone();
        let nominals = self.permanent.nominals.clone();
        let engine = self.permanent.engine.checkpoint(control)?;
        control.poll()?;
        Ok(ProductionCheckpoint {
            kernel,
            engine,
            nominals,
        })
    }

    fn install_query(
        &mut self,
        query: &SessionQuery<Self::Query>,
        control: &dyn OperationControl,
    ) -> NativeResult<()> {
        if query.key().as_bytes() != query.payload().query_hash {
            return Err(NativeError::wire(
                "session query key differs from the validated query digest",
            ));
        }
        query
            .payload()
            .validate_against(&self.ontology)
            .map_err(|error| NativeError::wire(error.message))?;
        if query.payload().requires_rebuild {
            return Err(NativeError::feature("query_rebuild"));
        }
        control.poll()?;
        let combined = combine_query_ontology(&self.ontology, query.payload())?;
        let expressivity = combined.program.expressivity;
        let loaded = load_permanent_rule_state(
            &combined,
            Arc::clone(&self.cancellation),
            self.config.disjunction_learning,
            self.config.existentials,
        )?;
        control.poll()?;
        self.query = Some(loaded);
        self.query_expressivity = Some(expressivity);
        Ok(())
    }

    fn finish_operation(
        &mut self,
        checkpoint: Self::OperationCheckpoint,
        disposition: OperationDisposition,
    ) -> NativeResult<()> {
        let had_query = self.query.take().is_some();
        self.query_expressivity = None;
        if had_query && disposition == OperationDisposition::CommitPermanent {
            return Err(NativeError::invariant(
                "query tableau cannot be committed as the permanent root",
            ));
        }
        match disposition {
            OperationDisposition::RollbackQuery => self
                .permanent
                .engine
                .rollback_with_kernel(
                    &mut self.permanent.kernel,
                    checkpoint.kernel,
                    checkpoint.engine,
                )
                .map(|()| {
                    self.permanent.nominals = checkpoint.nominals;
                }),
            OperationDisposition::CommitPermanent => {
                self.permanent
                    .engine
                    .release_checkpoint(checkpoint.engine)?;
                self.permanent.kernel.begin_operation()
            }
        }
    }

    fn reset_to_permanent(&mut self) -> NativeResult<()> {
        self.query = None;
        self.query_expressivity = None;
        self.permanent.kernel.check_invariants()?;
        self.permanent
            .engine
            .check_invariants(&self.permanent.kernel)
    }

    fn has_clash(&self) -> bool {
        self.active().kernel.clash().is_some()
    }

    fn process_nominals(&mut self, control: &dyn OperationControl) -> NativeResult<u64> {
        control.poll()?;
        let cancellation = Arc::clone(&self.cancellation);
        let active = self.active_mut();
        let processed = active.nominals.process_all(
            &mut active.kernel,
            &mut active.engine,
            cancellation.as_ref(),
        )?;
        control.poll()?;
        Ok(processed)
    }

    fn apply_next_delta(
        &mut self,
        control: &dyn OperationControl,
    ) -> NativeResult<DeltaPhaseResult> {
        control.poll()?;
        let cancellation = Arc::clone(&self.cancellation);
        let active = self.active_mut();
        let matches = active
            .engine
            .apply_next_delta(&mut active.kernel, cancellation)?;
        let generation = active.kernel.read_generation();
        let rows =
            active
                .kernel
                .active_fact_ids()
                .into_iter()
                .try_fold(0_u64, |count, row_id| {
                    if active.kernel.fact(row_id)?.derivation_generation == generation {
                        count.checked_add(1).ok_or_else(|| {
                            NativeError::invariant("native delta-row counter overflow")
                        })
                    } else {
                        Ok(count)
                    }
                })?;
        control.poll()?;
        Ok(DeltaPhaseResult {
            processed_rows: rows,
            rule_matches: matches,
            role_propagations: 0,
        })
    }

    fn check_datatypes(
        &mut self,
        control: &dyn OperationControl,
    ) -> NativeResult<DatatypePhaseResult> {
        control.poll()?;
        if self.active_expressivity().datatypes
            || self.active().kernel.datatype_component_count() != 0
        {
            return Err(NativeError::feature("native_datatypes"));
        }
        Ok(DatatypePhaseResult::default())
    }

    fn has_existential_candidates(&self) -> bool {
        self.active().kernel.existential_candidate_count() != 0
    }

    fn refresh_blocking(&mut self, control: &dyn OperationControl) -> NativeResult<u64> {
        control.poll()?;
        Ok(0)
    }

    fn process_existential(
        &mut self,
        control: &dyn OperationControl,
    ) -> NativeResult<PhaseProgress> {
        control.poll()?;
        if self.active_expressivity().datatypes {
            return Err(NativeError::feature("native_datatypes"));
        }
        let active = self.active_mut();
        let mut datatypes = AssertedOnlyDatatypes;
        let mut state = RuntimeExpansionState::new(&mut active.kernel, None);
        let mut access = RuntimeExpansionAccess::new(&mut active.engine, &mut datatypes, control);
        let mut expansion_control = NativeExpansionControl::new(control);
        let result = active
            .existentials
            .process_next(&mut state, &mut access, &mut expansion_control)
            .map_err(expansion_to_native)?;
        control.poll()?;
        match result.status {
            ExpansionStatus::NoWork => Ok(PhaseProgress::NoWork),
            ExpansionStatus::Blocked => Err(NativeError::feature("native_blocking")),
            ExpansionStatus::Satisfied | ExpansionStatus::Expanded | ExpansionStatus::Clashed => {
                Ok(PhaseProgress::Progress)
            }
        }
    }

    fn process_disjunction(
        &mut self,
        control: &dyn OperationControl,
    ) -> NativeResult<PhaseProgress> {
        control.poll()?;
        let cancellation = Arc::clone(&self.cancellation);
        let active = self.active_mut();
        let transition = active
            .engine
            .process_next_disjunction(&mut active.kernel, cancellation.as_ref())?;
        control.poll()?;
        match transition {
            BranchTransition::NoWork => Ok(PhaseProgress::NoWork),
            BranchTransition::Satisfied
            | BranchTransition::Deterministic
            | BranchTransition::Branched => Ok(PhaseProgress::Progress),
            BranchTransition::Advanced | BranchTransition::Exhausted | BranchTransition::Unsat => {
                Err(NativeError::invariant(
                    "disjunction phase returned a clash-resolution transition",
                ))
            }
        }
    }

    fn resolve_clash(&mut self, control: &dyn OperationControl) -> NativeResult<ClashResolution> {
        control.poll()?;
        let cancellation = Arc::clone(&self.cancellation);
        let active = self.active_mut();
        loop {
            let expansion_level = active
                .kernel
                .clash()
                .and_then(|clash| clash.dependency.maximum());
            if let Some(level) = expansion_level {
                let owns_branch = {
                    let state = RuntimeExpansionState::new(&mut active.kernel, None);
                    active
                        .existentials
                        .owns_branch(&state, level)
                        .map_err(expansion_to_native)?
                };
                if owns_branch {
                    let mut datatypes = AssertedOnlyDatatypes;
                    let mut state = RuntimeExpansionState::new(&mut active.kernel, None);
                    let mut access =
                        RuntimeExpansionAccess::new(&mut active.engine, &mut datatypes, control);
                    let mut expansion_control = NativeExpansionControl::new(control);
                    match active
                        .existentials
                        .resolve_clash(&mut state, &mut access, &mut expansion_control)
                        .map_err(expansion_to_native)?
                    {
                        ExpansionBranchTransition::Advanced => {
                            return Ok(ClashResolution::Backtracked);
                        }
                        ExpansionBranchTransition::Unsat => {
                            return Ok(ClashResolution::Unsatisfiable);
                        }
                        ExpansionBranchTransition::Exhausted => continue,
                        ExpansionBranchTransition::NoWork => {}
                    }
                }
            }
            match active.nominals.resolve_clash(
                &mut active.kernel,
                &mut active.engine,
                cancellation.as_ref(),
            )? {
                BranchTransition::Advanced => return Ok(ClashResolution::Backtracked),
                BranchTransition::Unsat => return Ok(ClashResolution::Unsatisfiable),
                BranchTransition::Exhausted => continue,
                BranchTransition::NoWork => {}
                BranchTransition::Satisfied
                | BranchTransition::Deterministic
                | BranchTransition::Branched => {
                    return Err(NativeError::invariant(
                        "nominal clash phase returned a forward transition",
                    ));
                }
            }
            let transition = active
                .engine
                .resolve_clash(&mut active.kernel, cancellation.as_ref())?;
            control.poll()?;
            return match transition {
                BranchTransition::Advanced => Ok(ClashResolution::Backtracked),
                BranchTransition::Unsat => Ok(ClashResolution::Unsatisfiable),
                BranchTransition::NoWork
                | BranchTransition::Satisfied
                | BranchTransition::Deterministic
                | BranchTransition::Branched
                | BranchTransition::Exhausted => Err(NativeError::invariant(
                    "clash phase did not return a terminal resolution",
                )),
            };
        }
    }

    fn invalidate_after_backtrack(&mut self) -> NativeResult<()> {
        self.active().kernel.check_invariants()
    }

    fn validate_blocking(
        &mut self,
        control: &dyn OperationControl,
    ) -> NativeResult<(ValidationStatus, u64)> {
        control.poll()?;
        Ok((ValidationStatus::NotRequired, 0))
    }

    fn ready_for_sat(&self) -> NativeResult<bool> {
        let kernel = &self.active().kernel;
        Ok(kernel.clash().is_none()
            && kernel.existential_candidate_count() == 0
            && kernel.annotated_equality_count() == 0
            && kernel.datatype_component_count() == 0
            && kernel.disjunction_queue_count() == 0)
    }

    fn check_invariants(&self) -> NativeResult<()> {
        let active = self.active();
        active.kernel.check_invariants()?;
        active.engine.check_invariants(&active.kernel)
    }
}

fn combine_query_ontology(
    ontology: &DecodedOntology,
    query: &DecodedQuery,
) -> NativeResult<DecodedOntology> {
    let overlay = query
        .program
        .as_ref()
        .ok_or_else(|| NativeError::wire("incremental query has no overlay program"))?;
    if overlay.role_model != ontology.program.role_model {
        return Err(NativeError::wire(
            "incremental query changed the permanent role model",
        ));
    }
    let (provenance, overlay_provenance) =
        append_provenance(&ontology.program.provenance, &overlay.provenance)?;
    let mut clauses = ontology.program.clauses.clone();
    for source in &overlay.clauses {
        let mut clause = source.clone();
        clause.clause_id = u32::try_from(clauses.len())
            .map_err(|_| NativeError::wire("combined query clause count exceeds u32"))?;
        clause.provenance_ids = remap_provenance(&clause.provenance_ids, &overlay_provenance)?;
        clauses.push(clause);
    }
    let mut positive_facts = ontology.program.positive_facts.clone();
    positive_facts.extend(remap_facts(&overlay.positive_facts, &overlay_provenance)?);
    let mut negative_facts = ontology.program.negative_facts.clone();
    negative_facts.extend(remap_facts(&overlay.negative_facts, &overlay_provenance)?);
    let mut ground_disjunctions = ontology.program.ground_disjunctions.clone();
    for source in &overlay.ground_disjunctions {
        let mut disjunction = remap_disjunction(source, &overlay_provenance)?;
        disjunction.disjunction_id = u32::try_from(ground_disjunctions.len())
            .map_err(|_| NativeError::wire("combined query disjunction count exceeds u32"))?;
        ground_disjunctions.push(disjunction);
    }
    let program = DecodedProgram {
        symbol_domains: overlay.symbol_domains.clone(),
        predicates: overlay.predicates.clone(),
        clauses,
        positive_facts,
        negative_facts,
        ground_disjunctions,
        role_model: overlay.role_model.clone(),
        datatype_model: overlay.datatype_model.clone(),
        expressivity: overlay.expressivity,
        provenance,
    };
    let mut named_individuals = ontology.named_individuals.clone();
    let named_predicates: Vec<_> = program
        .predicates
        .iter()
        .filter(|predicate| predicate.kind == PredicateKind::NamedIndividual)
        .map(|predicate| predicate.predicate_id)
        .collect();
    for fact in &program.positive_facts {
        if named_predicates.binary_search(&fact.predicate_id).is_ok() {
            if let Some(crate::input_wire::DecodedTerm::Individual { individual_id }) =
                fact.arguments.first()
            {
                named_individuals.push(*individual_id);
            }
        }
    }
    named_individuals.sort_unstable();
    named_individuals.dedup();
    Ok(DecodedOntology {
        metadata: ontology.metadata.clone(),
        program,
        declared_entities: ontology.declared_entities.clone(),
        named_individuals,
    })
}

fn append_provenance(
    permanent: &[DecodedProvenanceEntry],
    overlay: &[DecodedProvenanceEntry],
) -> NativeResult<(Vec<DecodedProvenanceEntry>, BTreeMap<u32, u32>)> {
    let mut combined = permanent.to_vec();
    let mut mapping = BTreeMap::new();
    for source in overlay {
        let provenance_id = u32::try_from(combined.len())
            .map_err(|_| NativeError::wire("combined provenance count exceeds u32"))?;
        if mapping
            .insert(source.provenance_id, provenance_id)
            .is_some()
        {
            return Err(NativeError::wire(
                "query provenance contains duplicate identifiers",
            ));
        }
        let mut entry = source.clone();
        entry.provenance_id = provenance_id;
        combined.push(entry);
    }
    Ok((combined, mapping))
}

fn remap_provenance(source: &[u32], mapping: &BTreeMap<u32, u32>) -> NativeResult<Vec<u32>> {
    source
        .iter()
        .map(|value| {
            mapping
                .get(value)
                .copied()
                .ok_or_else(|| NativeError::wire("query provenance ID is dangling"))
        })
        .collect()
}

fn remap_facts(
    facts: &[DecodedGroundAtom],
    mapping: &BTreeMap<u32, u32>,
) -> NativeResult<Vec<DecodedGroundAtom>> {
    facts
        .iter()
        .map(|source| {
            let mut fact = source.clone();
            fact.provenance_ids = remap_provenance(&fact.provenance_ids, mapping)?;
            Ok(fact)
        })
        .collect()
}

fn remap_disjunction(
    source: &DecodedGroundDisjunction,
    mapping: &BTreeMap<u32, u32>,
) -> NativeResult<DecodedGroundDisjunction> {
    let mut value = source.clone();
    value.disjuncts = remap_facts(&value.disjuncts, mapping)?;
    Ok(value)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cancel::CancellationHandle;
    use crate::input_wire::{
        decode_config, decode_ontology, DecodeLimits, DecodedGroundAtom, DecodedPredicate,
        DecodedSymbolValue, DecodedTerm, ExistentialChoice, PredicateKind, SymbolKind, TermSort,
    };
    use crate::session::{NeverAbort, SessionLimits, SessionScheduler};

    fn decode_hex(value: &str) -> Vec<u8> {
        value
            .as_bytes()
            .chunks_exact(2)
            .filter_map(|pair| {
                let text = std::str::from_utf8(pair).ok()?;
                u8::from_str_radix(text, 16).ok()
            })
            .collect()
    }

    fn golden_document(name: &str) -> Vec<u8> {
        let fixture: serde_json::Value =
            serde_json::from_str(include_str!("../../tests/data/native-input-v1.json"))
                .unwrap_or(serde_json::Value::Null);
        fixture
            .get("documents")
            .and_then(|documents| documents.get(name))
            .and_then(|document| document.get("hex"))
            .and_then(serde_json::Value::as_str)
            .map_or_else(Vec::new, decode_hex)
    }

    #[test]
    fn production_rule_tableau_runs_through_the_transactional_scheduler() -> NativeResult<()> {
        let limits = DecodeLimits::default();
        let ontology = Arc::new(
            decode_ontology(golden_document("ontology"), &limits)
                .map_err(|error| NativeError::wire(error.message))?,
        );
        let config = decode_config(golden_document("config"), &limits)
            .map_err(|error| NativeError::wire(error.message))?;
        let cancellation = CancellationHandle::from_options(None, None)?.state();
        let loaded = load_permanent_rule_state(
            &ontology,
            Arc::clone(&cancellation),
            config.disjunction_learning,
            config.existentials,
        )?;
        let tableau = ProductionTableau::new(ontology, config, cancellation, loaded)?;
        let session = SessionScheduler::new(tableau, SessionLimits::default())?;
        let first = session.check_permanent(&NeverAbort)?;
        let second = session.check_permanent(&NeverAbort)?;
        assert_eq!(first.satisfiable, second.satisfiable);
        assert!(!first.cache_hit);
        assert!(second.cache_hit);
        Ok(())
    }

    #[test]
    fn production_tableau_expands_a_top_role_object_obligation() -> NativeResult<()> {
        let limits = DecodeLimits::default();
        let mut ontology = decode_ontology(golden_document("ontology"), &limits)
            .map_err(|error| NativeError::wire(error.message))?;
        let class_domain = ontology
            .program
            .symbol_domains
            .iter_mut()
            .find(|domain| domain.kind == SymbolKind::ClassExpression)
            .ok_or_else(|| NativeError::invariant("golden class domain is absent"))?;
        let symbol_id = u32::try_from(class_domain.values.len())
            .map_err(|_| NativeError::invariant("test class domain exceeds u32"))?;
        class_domain.values.push(DecodedSymbolValue {
            identifier: symbol_id,
            key: b"native-expansion-filler".to_vec(),
            display: "native-expansion-filler".to_owned(),
            generated: false,
            query_local: false,
        });
        let filler_predicate_id = u32::try_from(ontology.program.predicates.len())
            .map_err(|_| NativeError::invariant("test predicate count exceeds u32"))?;
        ontology.program.predicates.push(DecodedPredicate {
            predicate_id: filler_predicate_id,
            kind: PredicateKind::Concept,
            argument_sorts: vec![TermSort::Object],
            symbol_id: Some(symbol_id),
            role_id: None,
            cardinality: None,
            filler_predicate_id: None,
            annotation: Vec::new(),
            internal_key: None,
        });
        let existential_predicate_id = filler_predicate_id
            .checked_add(1)
            .ok_or_else(|| NativeError::invariant("test predicate ID overflow"))?;
        ontology.program.predicates.push(DecodedPredicate {
            predicate_id: existential_predicate_id,
            kind: PredicateKind::AtLeastObject,
            argument_sorts: vec![TermSort::Object],
            symbol_id: None,
            role_id: Some(ontology.program.role_model.top_object_role_id),
            cardinality: Some(1),
            filler_predicate_id: Some(filler_predicate_id),
            annotation: Vec::new(),
            internal_key: None,
        });
        let individual_id = ontology
            .program
            .domain(SymbolKind::Individual)
            .and_then(|domain| domain.values.first())
            .map(|value| value.identifier)
            .ok_or_else(|| NativeError::invariant("golden individual domain is empty"))?;
        ontology.program.positive_facts.push(DecodedGroundAtom {
            predicate_id: existential_predicate_id,
            arguments: vec![DecodedTerm::Individual { individual_id }],
            provenance_ids: Vec::new(),
        });
        ontology.program.expressivity.number_restrictions = true;
        let ontology = Arc::new(ontology);
        let mut config = decode_config(golden_document("config"), &limits)
            .map_err(|error| NativeError::wire(error.message))?;
        config.existentials = ExistentialChoice::CreationOrder;
        let cancellation = CancellationHandle::from_options(None, None)?.state();
        let loaded = load_permanent_rule_state(
            &ontology,
            Arc::clone(&cancellation),
            config.disjunction_learning,
            config.existentials,
        )?;
        let tableau = ProductionTableau::new(ontology, config, cancellation, loaded)?;
        let session = SessionScheduler::new(tableau, SessionLimits::default())?;

        let result = session.check_permanent(&NeverAbort)?;

        assert!(result.satisfiable);
        assert_eq!(result.statistics.existential_actions, 1);
        Ok(())
    }
}
