//! Concrete production bridge from decoded IR to the transactional session scheduler.
// SPDX-License-Identifier: LGPL-3.0-or-later

use std::collections::BTreeMap;
use std::sync::Arc;

use crate::blocking::{
    BlockingCheckpoint, CompiledClauseBlockingValidator, NeverCancel as NeverCancelBlocking,
};
use crate::branching::BranchTransition;
use crate::cancel::CancellationState;
use crate::error::{NativeError, NativeResult};
use crate::existentials::{
    expansion_to_native, BranchTransition as ExpansionBranchTransition, ExpansionStatus,
    NativeExpansionControl, RuntimeExpansionAccess, RuntimeExpansionState,
};
use crate::input_wire::{
    DecodedAtom, DecodedClause, DecodedConfig, DecodedGroundAtom, DecodedGroundDisjunction,
    DecodedOntology, DecodedProgram, DecodedProvenanceEntry, DecodedQuery, DecodedTerm,
    PredicateKind,
};
use crate::model::NodeHandle;
use crate::nominals::NominalIntroductionManager;
use crate::operation_bridge::OperationControlBridge;
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
/// role automata and datatype semantics are loaded once with the permanent state. Consequently
/// this type is usable by Rust integration tests without making the extension advertise WPR4's
/// `full_reasoner` handshake prematurely while its remaining service adapters are completed.
pub struct ProductionTableau {
    ontology: Arc<DecodedOntology>,
    config: DecodedConfig,
    cancellation: Arc<CancellationState>,
    permanent: LoadedRuleState,
    query: Option<LoadedRuleState>,
}

pub struct ProductionCheckpoint {
    kernel: TableauKernel,
    engine: RuleEngineCheckpoint,
    nominals: NominalIntroductionManager,
    blocking: BlockingCheckpoint<NodeHandle>,
    datatype_signature: Option<[u8; 32]>,
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
        })
    }

    fn active(&self) -> &LoadedRuleState {
        self.query.as_ref().unwrap_or(&self.permanent)
    }

    fn active_mut(&mut self) -> &mut LoadedRuleState {
        self.query.as_mut().unwrap_or(&mut self.permanent)
    }

    fn restore_permanent_checkpoint(
        &mut self,
        checkpoint: ProductionCheckpoint,
    ) -> NativeResult<()> {
        let ProductionCheckpoint {
            kernel,
            engine,
            nominals,
            blocking,
            datatype_signature,
        } = checkpoint;
        self.permanent
            .engine
            .rollback_with_kernel(&mut self.permanent.kernel, kernel, engine)?;
        self.permanent.nominals = nominals;
        self.permanent.blocking.restore(blocking);
        self.permanent
            .datatypes
            .restore_signature(datatype_signature);
        Ok(())
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
        let blocking = self.permanent.blocking.checkpoint();
        let datatype_signature = self.permanent.datatypes.signature_checkpoint();
        let engine = self.permanent.engine.checkpoint(control)?;
        control.poll()?;
        Ok(ProductionCheckpoint {
            kernel,
            engine,
            nominals,
            blocking,
            datatype_signature,
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
        let loaded = load_permanent_rule_state(
            &combined,
            Arc::clone(&self.cancellation),
            self.config.disjunction_learning,
            self.config.existentials,
            self.config.blocking,
        )?;
        control.poll()?;
        self.query = Some(loaded);
        Ok(())
    }

    fn finish_operation(
        &mut self,
        checkpoint: Self::OperationCheckpoint,
        disposition: OperationDisposition,
    ) -> NativeResult<()> {
        let had_query = self.query.take().is_some();
        if had_query && disposition == OperationDisposition::CommitPermanent {
            return Err(NativeError::invariant(
                "query tableau cannot be committed as the permanent root",
            ));
        }
        match disposition {
            OperationDisposition::RollbackQuery => self.restore_permanent_checkpoint(checkpoint),
            OperationDisposition::CommitPermanent => {
                // A satisfiable nondeterministic model retains live choice points for potential
                // backtracking and cannot become the branch-free permanent operation root.  The
                // scheduler still caches the completed Boolean result, while the tableau returns
                // to its exact pre-check state for subsequent isolated overlays.
                if self.permanent.kernel.logical_counts().2 > 0 {
                    self.restore_permanent_checkpoint(checkpoint)
                } else {
                    self.permanent
                        .engine
                        .release_checkpoint(checkpoint.engine)?;
                    self.permanent.kernel.begin_operation()
                }
            }
        }
    }

    fn reset_to_permanent(&mut self) -> NativeResult<()> {
        self.query = None;
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
        let active = self.active_mut();
        active.datatypes.check(&mut active.kernel, control)
    }

    fn has_existential_candidates(&self) -> bool {
        self.active().kernel.existential_candidate_count() != 0
    }

    fn refresh_blocking(&mut self, control: &dyn OperationControl) -> NativeResult<u64> {
        control.poll()?;
        let bridge = OperationControlBridge::new(control);
        let active = self.active_mut();
        let result = active
            .blocking
            .compute_and_apply(&mut active.kernel, &bridge, false);
        let result = bridge.finish_blocking(result)?;
        u64::try_from(result.stats.candidate_checks)
            .map_err(|_| NativeError::invariant("blocking check count exceeds u64"))
    }

    fn process_existential(
        &mut self,
        control: &dyn OperationControl,
    ) -> NativeResult<PhaseProgress> {
        control.poll()?;
        let active = self.active_mut();
        let mut state = RuntimeExpansionState::new(&mut active.kernel, Some(&active.blocking));
        let mut access =
            RuntimeExpansionAccess::new(&mut active.engine, &mut active.datatypes, control);
        let mut expansion_control = NativeExpansionControl::new(control);
        let result = active
            .existentials
            .process_next(&mut state, &mut access, &mut expansion_control)
            .map_err(expansion_to_native)?;
        control.poll()?;
        match result.status {
            ExpansionStatus::NoWork | ExpansionStatus::Blocked => Ok(PhaseProgress::NoWork),
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
                    let state =
                        RuntimeExpansionState::new(&mut active.kernel, Some(&active.blocking));
                    active
                        .existentials
                        .owns_branch(&state, level)
                        .map_err(expansion_to_native)?
                };
                if owns_branch {
                    let mut state =
                        RuntimeExpansionState::new(&mut active.kernel, Some(&active.blocking));
                    let mut access = RuntimeExpansionAccess::new(
                        &mut active.engine,
                        &mut active.datatypes,
                        control,
                    );
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
        let active = self.active_mut();
        active.blocking.invalidate_all();
        active.datatypes.invalidate();
        active.kernel.check_invariants()
    }

    fn validate_blocking(
        &mut self,
        control: &dyn OperationControl,
    ) -> NativeResult<(ValidationStatus, u64)> {
        control.poll()?;
        let bridge = OperationControlBridge::new(control);
        let active = self.active_mut();
        if active.blocking.plan().validated() {
            let mut validator = CompiledClauseBlockingValidator::new(
                active.engine.program(),
                active.blocking.plan().core_mode,
            )
            .map_err(crate::operation_bridge::blocking_error_to_native)?;
            let result = active.blocking.validation_and_apply(
                &mut active.kernel,
                &mut validator,
                &bridge,
                false,
            );
            let (compute, validation) = bridge.finish_blocking(result)?;
            let checks = compute
                .stats
                .candidate_checks
                .checked_add(validation.checked_blocks)
                .ok_or_else(|| NativeError::invariant("blocking check count overflow"))?;
            let checks = u64::try_from(checks)
                .map_err(|_| NativeError::invariant("blocking check count exceeds u64"))?;
            return Ok((
                if validation.valid {
                    ValidationStatus::Valid
                } else {
                    ValidationStatus::Invalidated
                },
                checks,
            ));
        }
        let ready = active.blocking.ready_for_sat(&active.kernel, &bridge);
        let ready = bridge.finish_blocking(ready)?;
        if !ready {
            return Err(NativeError::invariant(
                "nonvalidated blocking did not reach a SAT-ready state",
            ));
        }
        Ok((ValidationStatus::NotRequired, 0))
    }

    fn ready_for_sat(&self) -> NativeResult<bool> {
        let active = self.active();
        let kernel = &active.kernel;
        let existentials_ready =
            kernel
                .active_node_handles()
                .into_iter()
                .try_fold(true, |ready, handle| {
                    let node = kernel.active_node(handle)?;
                    Ok::<_, NativeError>(
                        ready
                            && (node.unprocessed_existentials.is_empty()
                                || node.blocker.is_some()
                                || active.blocking.is_blocked(handle)),
                    )
                })?;
        Ok(kernel.clash().is_none()
            && existentials_ready
            && kernel.annotated_equality_count() == 0
            && kernel.datatype_component_count() == 0
            && kernel.disjunction_queue_count() == 0)
    }

    fn check_invariants(&self) -> NativeResult<()> {
        let active = self.active();
        active.kernel.check_invariants()?;
        active.engine.check_invariants(&active.kernel)?;
        if active.blocking.projection().is_some() {
            active
                .blocking
                .check_invariants(&NeverCancelBlocking)
                .map_err(crate::operation_bridge::blocking_error_to_native)?;
        }
        Ok(())
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
        merge_provenance(&ontology.program.provenance, &overlay.provenance)?;
    let clauses = merge_clauses(
        &ontology.program.clauses,
        &overlay.clauses,
        &overlay_provenance,
    )?;
    let positive_facts = merge_facts(
        &ontology.program.positive_facts,
        &overlay.positive_facts,
        &overlay_provenance,
    )?;
    let negative_facts = merge_facts(
        &ontology.program.negative_facts,
        &overlay.negative_facts,
        &overlay_provenance,
    )?;
    let ground_disjunctions = merge_disjunctions(
        &ontology.program.ground_disjunctions,
        &overlay.ground_disjunctions,
        &overlay_provenance,
    )?;
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

fn merge_provenance(
    permanent: &[DecodedProvenanceEntry],
    overlay: &[DecodedProvenanceEntry],
) -> NativeResult<(Vec<DecodedProvenanceEntry>, BTreeMap<u32, u32>)> {
    let mut combined = permanent.to_vec();
    let mut identities = BTreeMap::new();
    for entry in permanent {
        if identities
            .insert(
                (entry.source_sha256.clone(), entry.generated),
                entry.provenance_id,
            )
            .is_some()
        {
            return Err(NativeError::wire(
                "permanent provenance contains duplicate semantic identities",
            ));
        }
    }
    let mut mapping = BTreeMap::new();
    for source in overlay {
        let identity = (source.source_sha256.clone(), source.generated);
        let provenance_id = if let Some(existing) = identities.get(&identity).copied() {
            existing
        } else {
            let identifier = u32::try_from(combined.len())
                .map_err(|_| NativeError::wire("combined provenance count exceeds u32"))?;
            let mut entry = source.clone();
            entry.provenance_id = identifier;
            combined.push(entry);
            identities.insert(identity, identifier);
            identifier
        };
        if mapping
            .insert(source.provenance_id, provenance_id)
            .is_some()
        {
            return Err(NativeError::wire(
                "query provenance contains duplicate identifiers",
            ));
        }
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

type AtomIdentity = (u32, Vec<DecodedTerm>);
type ClauseIdentity = (Vec<AtomIdentity>, Vec<AtomIdentity>, Vec<u32>);
type FactIdentity = (u32, Vec<DecodedTerm>);
type DisjunctionIdentity = Vec<FactIdentity>;

fn atom_identity(atom: &DecodedAtom) -> AtomIdentity {
    (atom.predicate_id, atom.arguments.clone())
}

fn clause_identity(clause: &DecodedClause) -> ClauseIdentity {
    (
        clause.body.iter().map(atom_identity).collect(),
        clause.head.iter().map(atom_identity).collect(),
        clause.join_order.clone(),
    )
}

fn fact_identity(fact: &DecodedGroundAtom) -> FactIdentity {
    (fact.predicate_id, fact.arguments.clone())
}

fn union_ids(target: &mut Vec<u32>, incoming: &[u32]) {
    target.extend_from_slice(incoming);
    target.sort_unstable();
    target.dedup();
}

fn merge_clauses(
    permanent: &[DecodedClause],
    overlay: &[DecodedClause],
    mapping: &BTreeMap<u32, u32>,
) -> NativeResult<Vec<DecodedClause>> {
    let mut combined = Vec::new();
    let mut indexes = BTreeMap::new();
    for clause in permanent {
        merge_clause(&mut combined, &mut indexes, clause.clone())?;
    }
    for source in overlay {
        let mut clause = source.clone();
        clause.provenance_ids = remap_provenance(&clause.provenance_ids, mapping)?;
        merge_clause(&mut combined, &mut indexes, clause)?;
    }
    Ok(combined)
}

fn merge_clause(
    combined: &mut Vec<DecodedClause>,
    indexes: &mut BTreeMap<ClauseIdentity, usize>,
    mut clause: DecodedClause,
) -> NativeResult<()> {
    let identity = clause_identity(&clause);
    if let Some(index) = indexes.get(&identity).copied() {
        union_ids(&mut combined[index].provenance_ids, &clause.provenance_ids);
        return Ok(());
    }
    clause.clause_id = u32::try_from(combined.len())
        .map_err(|_| NativeError::wire("combined query clause count exceeds u32"))?;
    clause.provenance_ids.sort_unstable();
    clause.provenance_ids.dedup();
    indexes.insert(identity, combined.len());
    combined.push(clause);
    Ok(())
}

fn merge_facts(
    permanent: &[DecodedGroundAtom],
    overlay: &[DecodedGroundAtom],
    mapping: &BTreeMap<u32, u32>,
) -> NativeResult<Vec<DecodedGroundAtom>> {
    let mut combined = Vec::new();
    let mut indexes = BTreeMap::new();
    for fact in permanent {
        merge_fact(&mut combined, &mut indexes, fact.clone());
    }
    for fact in remap_facts(overlay, mapping)? {
        merge_fact(&mut combined, &mut indexes, fact);
    }
    Ok(combined)
}

fn merge_fact(
    combined: &mut Vec<DecodedGroundAtom>,
    indexes: &mut BTreeMap<FactIdentity, usize>,
    mut fact: DecodedGroundAtom,
) {
    let identity = fact_identity(&fact);
    if let Some(index) = indexes.get(&identity).copied() {
        union_ids(&mut combined[index].provenance_ids, &fact.provenance_ids);
        return;
    }
    fact.provenance_ids.sort_unstable();
    fact.provenance_ids.dedup();
    indexes.insert(identity, combined.len());
    combined.push(fact);
}

fn merge_disjunctions(
    permanent: &[DecodedGroundDisjunction],
    overlay: &[DecodedGroundDisjunction],
    mapping: &BTreeMap<u32, u32>,
) -> NativeResult<Vec<DecodedGroundDisjunction>> {
    let mut combined = Vec::new();
    let mut indexes = BTreeMap::new();
    for disjunction in permanent {
        merge_disjunction(&mut combined, &mut indexes, disjunction.clone())?;
    }
    for source in overlay {
        let mut disjunction = source.clone();
        disjunction.provenance_ids = remap_provenance(&disjunction.provenance_ids, mapping)?;
        disjunction.disjuncts = remap_facts(&disjunction.disjuncts, mapping)?;
        merge_disjunction(&mut combined, &mut indexes, disjunction)?;
    }
    Ok(combined)
}

fn merge_disjunction(
    combined: &mut Vec<DecodedGroundDisjunction>,
    indexes: &mut BTreeMap<DisjunctionIdentity, usize>,
    mut disjunction: DecodedGroundDisjunction,
) -> NativeResult<()> {
    let identity = disjunction
        .disjuncts
        .iter()
        .map(fact_identity)
        .collect::<Vec<_>>();
    if let Some(index) = indexes.get(&identity).copied() {
        let retained = &mut combined[index];
        union_ids(&mut retained.provenance_ids, &disjunction.provenance_ids);
        if retained.disjuncts.len() != disjunction.disjuncts.len() {
            return Err(NativeError::invariant(
                "equal disjunction identities have different cardinality",
            ));
        }
        for (target, source) in retained.disjuncts.iter_mut().zip(&disjunction.disjuncts) {
            union_ids(&mut target.provenance_ids, &source.provenance_ids);
        }
        return Ok(());
    }
    disjunction.disjunction_id = u32::try_from(combined.len())
        .map_err(|_| NativeError::wire("combined query disjunction count exceeds u32"))?;
    disjunction.provenance_ids.sort_unstable();
    disjunction.provenance_ids.dedup();
    for disjunct in &mut disjunction.disjuncts {
        disjunct.provenance_ids.sort_unstable();
        disjunct.provenance_ids.dedup();
    }
    indexes.insert(identity, combined.len());
    combined.push(disjunction);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeSet;

    use crate::cancel::CancellationHandle;
    use crate::input_wire::{
        decode_config, decode_ontology, BlockingChoice, DecodeLimits, DecodedAtom, DecodedClause,
        DecodedGroundAtom, DecodedPredicate, DecodedSymbolValue, DecodedTerm, ExistentialChoice,
        PredicateKind, SymbolKind, TermSort,
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
            config.blocking,
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
    fn complete_query_prefix_merges_to_the_exact_permanent_program() -> NativeResult<()> {
        let limits = DecodeLimits::default();
        let ontology = decode_ontology(golden_document("ontology"), &limits)
            .map_err(|error| NativeError::wire(error.message))?;
        let mut first_local_symbols = [0_u32; 8];
        for domain in &ontology.program.symbol_domains {
            first_local_symbols[domain.kind as usize] = u32::try_from(domain.values.len())
                .map_err(|_| NativeError::invariant("test symbol boundary exceeds u32"))?;
        }
        let query_hash = [19; 32];
        let query = DecodedQuery {
            permanent_program_sha256: ontology.metadata.program_sha256,
            query_hash,
            overlay_program_sha256: Some(query_hash),
            first_local_predicate_id: u32::try_from(ontology.program.predicates.len())
                .map_err(|_| NativeError::invariant("test predicate boundary exceeds u32"))?,
            first_local_symbols,
            requires_rebuild: false,
            program: Some(ontology.program.clone()),
            reason: None,
            interpretation: vec!["duplicate-prefix-regression".to_owned()],
        };

        let combined = combine_query_ontology(&ontology, &query)?;

        assert_eq!(combined, ontology);
        Ok(())
    }

    #[test]
    fn production_tableau_blocks_a_cyclic_object_obligation() -> NativeResult<()> {
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
        let role_id = ontology.program.role_model.object_role_count;
        ontology.program.role_model.object_role_count = role_id
            .checked_add(1)
            .ok_or_else(|| NativeError::invariant("test object-role count overflow"))?;
        ontology.program.role_model.inverse_role_ids.push(role_id);
        let role_predicate_id = filler_predicate_id
            .checked_add(1)
            .ok_or_else(|| NativeError::invariant("test predicate ID overflow"))?;
        ontology.program.predicates.push(DecodedPredicate {
            predicate_id: role_predicate_id,
            kind: PredicateKind::ObjectRole,
            argument_sorts: vec![TermSort::Object, TermSort::Object],
            symbol_id: None,
            role_id: Some(role_id),
            cardinality: None,
            filler_predicate_id: None,
            annotation: Vec::new(),
            internal_key: None,
        });
        let existential_predicate_id = role_predicate_id
            .checked_add(1)
            .ok_or_else(|| NativeError::invariant("test predicate ID overflow"))?;
        ontology.program.predicates.push(DecodedPredicate {
            predicate_id: existential_predicate_id,
            kind: PredicateKind::AtLeastObject,
            argument_sorts: vec![TermSort::Object],
            symbol_id: None,
            role_id: Some(role_id),
            cardinality: Some(1),
            filler_predicate_id: Some(filler_predicate_id),
            annotation: Vec::new(),
            internal_key: None,
        });
        let variable = DecodedTerm::Variable {
            index: 0,
            sort: TermSort::Object,
        };
        ontology.program.clauses.push(DecodedClause {
            clause_id: u32::try_from(ontology.program.clauses.len())
                .map_err(|_| NativeError::invariant("test clause count exceeds u32"))?,
            body: vec![DecodedAtom {
                predicate_id: filler_predicate_id,
                arguments: vec![variable.clone()],
            }],
            head: vec![DecodedAtom {
                predicate_id: existential_predicate_id,
                arguments: vec![variable],
            }],
            provenance_ids: vec![0],
            join_order: vec![0],
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
        config.blocking = BlockingChoice::ValidatedAnywhere;
        let cancellation = CancellationHandle::from_options(None, None)?.state();
        let loaded = load_permanent_rule_state(
            &ontology,
            Arc::clone(&cancellation),
            config.disjunction_learning,
            config.existentials,
            config.blocking,
        )?;
        let tableau = ProductionTableau::new(ontology, config, cancellation, loaded)?;
        let session = SessionScheduler::new(tableau, SessionLimits::default())?;

        let result = session.check_permanent(&NeverAbort)?;

        assert!(result.satisfiable);
        assert_eq!(result.statistics.existential_actions, 2);
        assert!(result.statistics.blocking_checks >= 1);
        assert!(result.statistics.validation_passes >= 1);
        Ok(())
    }

    #[test]
    fn production_tableau_checks_fixed_literals_with_the_native_datatype_solver() -> NativeResult<()>
    {
        let limits = DecodeLimits::default();
        let mut ontology = decode_ontology(golden_document("ontology_datatype"), &limits)
            .map_err(|error| NativeError::wire(error.message))?;
        let int_range_id = ontology
            .program
            .domain(SymbolKind::DataRange)
            .and_then(|domain| {
                domain
                    .values
                    .iter()
                    .find(|value| value.display.ends_with("#int"))
            })
            .map(|value| value.identifier)
            .ok_or_else(|| NativeError::invariant("golden xsd:int data range is absent"))?;
        let existing_datatype_predicates = ontology
            .program
            .predicates
            .iter()
            .filter(|predicate| {
                matches!(
                    predicate.kind,
                    PredicateKind::DataRange | PredicateKind::NegatedDataRange
                )
            })
            .map(|predicate| predicate.predicate_id)
            .collect::<BTreeSet<_>>();
        ontology
            .program
            .positive_facts
            .retain(|fact| !existing_datatype_predicates.contains(&fact.predicate_id));
        ontology
            .program
            .negative_facts
            .retain(|fact| !existing_datatype_predicates.contains(&fact.predicate_id));
        let predicate_id = ontology
            .program
            .predicates
            .iter()
            .find(|predicate| {
                predicate.kind == PredicateKind::NegatedDataRange
                    && predicate.symbol_id == Some(int_range_id)
            })
            .map_or_else(
                || {
                    u32::try_from(ontology.program.predicates.len())
                        .map_err(|_| NativeError::invariant("test predicate count exceeds u32"))
                },
                |predicate| Ok(predicate.predicate_id),
            )?;
        if usize::try_from(predicate_id)
            .ok()
            .is_some_and(|value| value == ontology.program.predicates.len())
        {
            ontology.program.predicates.push(DecodedPredicate {
                predicate_id,
                kind: PredicateKind::NegatedDataRange,
                argument_sorts: vec![TermSort::Data],
                symbol_id: Some(int_range_id),
                role_id: None,
                cardinality: None,
                filler_predicate_id: None,
                annotation: Vec::new(),
                internal_key: None,
            });
        }
        let literal = ontology
            .program
            .datatype_model
            .literal_identities
            .first()
            .ok_or_else(|| NativeError::invariant("golden datatype literal is absent"))?;
        ontology.program.positive_facts.push(DecodedGroundAtom {
            predicate_id,
            arguments: vec![DecodedTerm::Data {
                source_literal_id: literal.source_literal_id,
                data_identity_id: literal.data_identity_id,
            }],
            provenance_ids: Vec::new(),
        });
        ontology.program.expressivity.datatypes = true;
        let ontology = Arc::new(ontology);
        let config = decode_config(golden_document("config"), &limits)
            .map_err(|error| NativeError::wire(error.message))?;
        let cancellation = CancellationHandle::from_options(None, None)?.state();
        let loaded = load_permanent_rule_state(
            &ontology,
            Arc::clone(&cancellation),
            config.disjunction_learning,
            config.existentials,
            config.blocking,
        )?;
        let tableau = ProductionTableau::new(ontology, config, cancellation, loaded)?;
        let session = SessionScheduler::new(tableau, SessionLimits::default())?;

        let result = session.check_permanent(&NeverAbort)?;

        assert!(!result.satisfiable);
        assert_eq!(result.statistics.datatype_components, 1);
        Ok(())
    }
}
