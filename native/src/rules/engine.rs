//! Ground-head dispatch and branch integration for the native Hyp-rule engine.
// SPDX-License-Identifier: LGPL-3.0-or-later

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use crate::branching::{BranchTransition, DisjunctionBrancher, GroundAtomAccess};
use crate::cancel::CancellationState;
use crate::error::{ErrorKind, NativeError, NativeResult};
use crate::merging::{MergeResult, MergingManager};
use crate::model::{DependencySet, NodeHandle, NodeSort};
use crate::store::TableauKernel;

use super::joins::{IndexedJoinEvaluator, NaiveJoinEvaluator};
use super::model::{
    GroundAtom, JoinMatch, PendingAnnotatedEquality, PredicateKind, RuleAtom, RuleLimits,
    RuleProgram, Term, TermSort,
};
use super::plans::{compile_join_program, JoinProgram};

type BindingKey = (TermSort, u32);
type Bindings = BTreeMap<BindingKey, NodeHandle>;
type DisjunctRank = (u8, PredicateKind, u32, Vec<(u32, u32, u32)>);

pub struct RuleEngine {
    program: RuleProgram,
    join_program: JoinProgram,
    source_nodes: Arc<BTreeMap<u32, NodeHandle>>,
    data_nodes: Arc<BTreeMap<u32, NodeHandle>>,
    atom_ids: BTreeMap<GroundAtom, u32>,
    atoms: Vec<GroundAtom>,
    disjunction_keys: BTreeMap<Vec<GroundAtom>, u32>,
    brancher: DisjunctionBrancher,
    merger: MergingManager,
    limits: RuleLimits,
    initialized: bool,
}

impl RuleEngine {
    pub fn new(
        program: RuleProgram,
        source_nodes: BTreeMap<u32, NodeHandle>,
        data_nodes: BTreeMap<u32, NodeHandle>,
        disjunction_learning: bool,
    ) -> NativeResult<Self> {
        Self::with_limits(
            program,
            source_nodes,
            data_nodes,
            RuleLimits::default(),
            disjunction_learning,
        )
    }

    pub fn with_limits(
        program: RuleProgram,
        source_nodes: BTreeMap<u32, NodeHandle>,
        data_nodes: BTreeMap<u32, NodeHandle>,
        limits: RuleLimits,
        disjunction_learning: bool,
    ) -> NativeResult<Self> {
        let limits = RuleLimits::new(
            limits.max_join_steps,
            limits.max_matches_per_generation,
            limits.cancellation_interval,
        )?;
        let join_program = compile_join_program(&program)?;
        let merger = MergingManager::new(&program)?;
        Ok(Self {
            program,
            join_program,
            source_nodes: Arc::new(source_nodes),
            data_nodes: Arc::new(data_nodes),
            atom_ids: BTreeMap::new(),
            atoms: Vec::new(),
            disjunction_keys: BTreeMap::new(),
            brancher: DisjunctionBrancher::new(disjunction_learning),
            merger,
            limits,
            initialized: false,
        })
    }

    #[must_use]
    pub const fn program(&self) -> &RuleProgram {
        &self.program
    }

    #[must_use]
    pub const fn join_program(&self) -> &JoinProgram {
        &self.join_program
    }

    #[must_use]
    pub const fn disjunction_learning(&self) -> bool {
        self.brancher.learning()
    }

    #[must_use]
    pub const fn initialized(&self) -> bool {
        self.initialized
    }

    /// Establish an operation root after seeding reflexive equality and clauses
    /// without a physical delta trigger. Compiled ground facts are dispatched by
    /// the coarse session loader before this call, so no Python callback is needed.
    pub fn initialize(
        &mut self,
        kernel: &mut TableauKernel,
        cancellation: Arc<CancellationState>,
    ) -> NativeResult<()> {
        if self.initialized {
            return Err(NativeError::wire(
                "native hyperresolution engine is already initialized",
            ));
        }
        cancellation.poll()?;
        kernel.begin_operation()?;
        let result = self.initialize_inner(kernel, cancellation);
        match recover_rule_operation(kernel, result) {
            Ok(()) => {
                self.initialized = true;
                Ok(())
            }
            Err(error) => Err(error),
        }
    }

    fn initialize_inner(
        &mut self,
        kernel: &mut TableauKernel,
        cancellation: Arc<CancellationState>,
    ) -> NativeResult<()> {
        IndexedJoinEvaluator::validate_node_maps(kernel, &self.source_nodes, &self.data_nodes)?;
        self.seed_reflexive_equalities(kernel)?;
        self.fire_unconditional(kernel, cancellation)?;
        kernel.check_invariants()?;
        kernel.begin_operation()
    }

    /// Advance one immutable delta generation and execute every matching plan.
    pub fn apply_next_delta(
        &mut self,
        kernel: &mut TableauKernel,
        cancellation: Arc<CancellationState>,
    ) -> NativeResult<u64> {
        if !self.initialized {
            return Err(NativeError::wire(
                "native hyperresolution engine must be initialized first",
            ));
        }
        let result = self.apply_next_delta_inner(kernel, cancellation);
        recover_rule_operation(kernel, result)
    }

    fn apply_next_delta_inner(
        &mut self,
        kernel: &mut TableauKernel,
        cancellation: Arc<CancellationState>,
    ) -> NativeResult<u64> {
        cancellation.poll()?;
        kernel.prepare_next_delta()?;
        let generation = kernel.read_generation();
        let cancellation_interval = usize_from_u64(self.limits.cancellation_interval)?;
        let mut rows = Vec::new();
        for (index, row_id) in kernel.active_fact_ids().into_iter().enumerate() {
            if index % cancellation_interval == 0 {
                cancellation.poll()?;
            }
            if kernel.fact(row_id)?.derivation_generation == generation {
                rows.push(row_id);
            }
        }

        let mut applied = BTreeSet::new();
        let mut match_count = 0_u64;
        let mut join_steps = 0_u64;
        for row_id in &rows {
            cancellation.poll()?;
            if !kernel.fact(*row_id)?.active {
                continue;
            }
            let predicate_id = kernel.fact(*row_id)?.key.predicate_id;
            let plans: Vec<_> = self
                .join_program
                .for_predicate(predicate_id)
                .into_iter()
                .cloned()
                .collect();
            for plan in plans {
                if !kernel.fact(*row_id)?.active || kernel.clash().is_some() {
                    break;
                }
                let limits = remaining_join_limits(self.limits, join_steps)?;
                let (matches, local_steps) = {
                    let mut evaluator = IndexedJoinEvaluator::from_prevalidated_maps(
                        &self.program,
                        kernel,
                        Arc::clone(&self.source_nodes),
                        Arc::clone(&self.data_nodes),
                        Arc::clone(&cancellation),
                        limits,
                    )?;
                    let matches = evaluator
                        .matches(&plan, *row_id)
                        .map_err(|error| adjust_join_limit(error, join_steps, self.limits))?;
                    (matches, evaluator.steps())
                };
                join_steps = join_steps
                    .checked_add(local_steps)
                    .ok_or_else(|| NativeError::invariant("native join-step counter overflow"))?;
                for matched in matches {
                    cancellation.poll()?;
                    let key = (
                        matched.clause_id,
                        matched.bindings.clone(),
                        matched.dependency.clone(),
                    );
                    if !applied.insert(key) {
                        continue;
                    }
                    match_count = match_count.checked_add(1).ok_or_else(|| {
                        NativeError::invariant("native rule-match counter overflow")
                    })?;
                    if match_count > self.limits.max_matches_per_generation {
                        return Err(resource_limit(
                            "hyperresolution match limit exceeded",
                            "max_matches_per_generation",
                            match_count,
                            self.limits.max_matches_per_generation,
                        ));
                    }
                    self.apply_match(kernel, &matched)?;
                    if kernel.clash().is_some() {
                        break;
                    }
                }
            }
        }
        cancellation.poll()?;
        u64::try_from(rows.len()).map_err(|_| NativeError::invariant("delta row count exceeds u64"))
    }

    /// Run delta generations until no new facts remain or a clash is installed.
    pub fn saturate_hyperresolution(
        &mut self,
        kernel: &mut TableauKernel,
        cancellation: Arc<CancellationState>,
    ) -> NativeResult<u64> {
        let mut generations = 0_u64;
        while kernel.clash().is_none() {
            let processed = self.apply_next_delta(kernel, Arc::clone(&cancellation))?;
            if processed == 0 {
                return Ok(generations);
            }
            generations = generations.checked_add(1).ok_or_else(|| {
                NativeError::invariant("hyperresolution generation counter overflow")
            })?;
        }
        Ok(generations)
    }

    /// Evaluate a single compiled plan without mutating the tableau. This is used
    /// by native/Python transition conformance runners at a coarse operation boundary.
    pub fn indexed_matches(
        &self,
        kernel: &TableauKernel,
        plan: &super::plans::ClauseJoinPlan,
        delta_row_id: u32,
        cancellation: Arc<CancellationState>,
    ) -> NativeResult<Vec<JoinMatch>> {
        IndexedJoinEvaluator::validate_node_maps(kernel, &self.source_nodes, &self.data_nodes)?;
        let mut evaluator = IndexedJoinEvaluator::from_prevalidated_maps(
            &self.program,
            kernel,
            Arc::clone(&self.source_nodes),
            Arc::clone(&self.data_nodes),
            cancellation,
            self.limits,
        )?;
        evaluator.matches(plan, delta_row_id)
    }

    /// Independent exhaustive substitution oracle for bounded differential cases.
    pub fn naive_matches(
        &self,
        kernel: &TableauKernel,
        clause_id: u32,
        require_new: bool,
        cancellation: Arc<CancellationState>,
    ) -> NativeResult<Vec<JoinMatch>> {
        IndexedJoinEvaluator::validate_node_maps(kernel, &self.source_nodes, &self.data_nodes)?;
        let mut indexed = IndexedJoinEvaluator::from_prevalidated_maps(
            &self.program,
            kernel,
            Arc::clone(&self.source_nodes),
            Arc::clone(&self.data_nodes),
            cancellation,
            self.limits,
        )?;
        NaiveJoinEvaluator::new(&mut indexed).matches(clause_id, require_new)
    }

    /// Add the reflexive equality fact required for a node created after initialization.
    pub fn register_node(
        &mut self,
        kernel: &mut TableauKernel,
        handle: NodeHandle,
        dependency: DependencySet,
    ) -> NativeResult<bool> {
        let sort = match kernel.node_sort(handle)? {
            NodeSort::Object => TermSort::Object,
            NodeSort::Data => TermSort::Data,
        };
        let predicate_id = self
            .program
            .predicates()
            .iter()
            .filter(|predicate| {
                predicate.kind == PredicateKind::Equality
                    && predicate.argument_sorts.first() == Some(&sort)
            })
            .map(|predicate| predicate.predicate_id)
            .next_back();
        let Some(predicate_id) = predicate_id else {
            return Ok(false);
        };
        self.dispatch_ground_atom(
            kernel,
            GroundAtom::new(predicate_id, vec![handle, handle])?,
            dependency,
            true,
            &[],
        )
    }

    fn seed_reflexive_equalities(&self, kernel: &mut TableauKernel) -> NativeResult<()> {
        let equality_by_sort: BTreeMap<_, _> = self
            .program
            .predicates()
            .iter()
            .filter(|predicate| predicate.kind == PredicateKind::Equality)
            .map(|predicate| (predicate.argument_sorts[0], predicate.predicate_id))
            .collect();
        for handle in kernel.active_node_handles() {
            let sort = match kernel.node_sort(handle)? {
                NodeSort::Object => TermSort::Object,
                NodeSort::Data => TermSort::Data,
            };
            let Some(predicate_id) = equality_by_sort.get(&sort).copied() else {
                continue;
            };
            Self::add_extension_atom(
                kernel,
                &GroundAtom::new(predicate_id, vec![handle, handle])?,
                DependencySet::empty(),
                true,
                &[],
            )?;
        }
        Ok(())
    }

    fn fire_unconditional(
        &mut self,
        kernel: &mut TableauKernel,
        cancellation: Arc<CancellationState>,
    ) -> NativeResult<()> {
        let clause_ids = self.join_program.unconditional_clause_ids().to_vec();
        let mut join_steps = 0_u64;
        let mut match_count = 0_u64;
        for clause_id in clause_ids {
            cancellation.poll()?;
            let limits = remaining_join_limits(self.limits, join_steps)?;
            let (matches, local_steps) = {
                let mut indexed = IndexedJoinEvaluator::from_prevalidated_maps(
                    &self.program,
                    kernel,
                    Arc::clone(&self.source_nodes),
                    Arc::clone(&self.data_nodes),
                    Arc::clone(&cancellation),
                    limits,
                )?;
                let matches = NaiveJoinEvaluator::new(&mut indexed)
                    .matches(clause_id, false)
                    .map_err(|error| adjust_join_limit(error, join_steps, self.limits))?;
                (matches, indexed.steps())
            };
            join_steps = join_steps
                .checked_add(local_steps)
                .ok_or_else(|| NativeError::invariant("native join-step counter overflow"))?;
            for matched in matches {
                cancellation.poll()?;
                match_count = match_count.checked_add(1).ok_or_else(|| {
                    NativeError::invariant("native unconditional-match counter overflow")
                })?;
                if match_count > self.limits.max_matches_per_generation {
                    return Err(resource_limit(
                        "hyperresolution match limit exceeded",
                        "max_matches_per_generation",
                        match_count,
                        self.limits.max_matches_per_generation,
                    ));
                }
                self.apply_match(kernel, &matched)?;
                if kernel.clash().is_some() {
                    return Ok(());
                }
            }
        }
        Ok(())
    }

    pub fn atom_for_id(&self, atom_id: u32) -> NativeResult<&GroundAtom> {
        self.atoms
            .get(usize_from_u32(atom_id, "ground-atom ID")?)
            .ok_or_else(|| NativeError::invariant("ground disjunction references an absent atom"))
    }

    pub fn atom_id(&mut self, atom: GroundAtom) -> NativeResult<u32> {
        if let Some(identifier) = self.atom_ids.get(&atom) {
            return Ok(*identifier);
        }
        let identifier = u32::try_from(self.atoms.len())
            .map_err(|_| NativeError::invariant("ground-atom registry exceeds u32 IDs"))?;
        self.program.validate_ground_atom(&atom)?;
        self.atoms.push(atom.clone());
        self.atom_ids.insert(atom, identifier);
        Ok(identifier)
    }

    pub fn take_pending_annotated_equality(
        &self,
        kernel: &mut TableauKernel,
    ) -> NativeResult<Option<PendingAnnotatedEquality>> {
        let Some(action_id) = kernel.take_integer("annotated_equalities")? else {
            return Ok(None);
        };
        let atom = self.atom_for_id(action_id)?.clone();
        if self.program.predicate_kind(atom.predicate_id)? != PredicateKind::AnnotatedEquality {
            return Err(NativeError::invariant(
                "annotated-equality queue references a different predicate kind",
            ));
        }
        let rows = kernel.fact_history(atom.predicate_id, &atom.arguments);
        let mut supports = Vec::new();
        let mut provenance_ids = Vec::new();
        for row in rows {
            supports.extend(row.supports);
            provenance_ids.extend(row.provenance_ids);
        }
        PendingAnnotatedEquality::new(action_id, atom, supports, provenance_ids).map(Some)
    }

    /// Apply the full merge protocol and re-dispatch survivor rows so semantic
    /// clashes and work queues are updated in the same coarse Rust operation.
    pub fn merge_nodes_semantic(
        &mut self,
        kernel: &mut TableauKernel,
        left: NodeHandle,
        right: NodeHandle,
        dependency: DependencySet,
        cancellation: Option<&CancellationState>,
    ) -> NativeResult<MergeResult> {
        let mut result = self
            .merger
            .merge(kernel, left, right, dependency, cancellation)?;
        if result.clashed || result.merged.is_none() {
            return Ok(result);
        }
        let rows = kernel.facts_for_node(result.representative)?;
        for row in rows {
            if let Some(control) = cancellation {
                control.poll()?;
            }
            let provenance_ids = row.provenance_ids.iter().copied().collect::<Vec<_>>();
            let ground = GroundAtom::new(row.key.predicate_id, row.key.arguments)?;
            for support in row.supports {
                self.dispatch_ground_atom(
                    kernel,
                    ground.clone(),
                    support,
                    row.core,
                    &provenance_ids,
                )?;
                if kernel.clash().is_some() {
                    result.clashed = true;
                    return Ok(result);
                }
            }
        }
        Ok(result)
    }

    pub fn dispatch_ground_atom(
        &mut self,
        kernel: &mut TableauKernel,
        atom: GroundAtom,
        dependency: DependencySet,
        core: bool,
        provenance_ids: &[u32],
    ) -> NativeResult<bool> {
        let (normalized, path) = self.canonical_atom(kernel, atom)?;
        let support = DependencySet::union(&[&dependency, &path]);
        self.dispatch_normalized(kernel, normalized, support, core, provenance_ids)
    }

    pub fn apply_ground_head(
        &mut self,
        kernel: &mut TableauKernel,
        atoms: Vec<GroundAtom>,
        dependency: DependencySet,
        provenance_ids: &[u32],
        participant_ids: &[u32],
    ) -> NativeResult<bool> {
        let mut canonicalized = Vec::new();
        for atom in atoms {
            canonicalized.push(self.canonical_atom(kernel, atom)?);
        }
        let normalized: Vec<_> = canonicalized
            .iter()
            .map(|(atom, _dependency)| atom.clone())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        let normalized = self.order_disjuncts(kernel, normalized)?;
        let single_original = (normalized.len() == 1).then(|| normalized[0].clone());
        for atom in &normalized {
            if self.atom_is_satisfied_impl(kernel, atom)? {
                return Ok(false);
            }
        }

        let mut remaining = Vec::new();
        let mut dependencies = vec![dependency];
        dependencies.extend(canonicalized.into_iter().map(|(_atom, path)| path));
        for atom in normalized {
            if let Some(refutation) = self.atom_refutation_impl(kernel, &atom)? {
                dependencies.push(refutation);
            } else {
                remaining.push(atom);
            }
        }
        let dependency_refs: Vec<_> = dependencies.iter().collect();
        let support = DependencySet::union(&dependency_refs);
        match remaining.as_slice() {
            [] => {
                let kind = if let Some(atom) = single_original.as_ref() {
                    self.single_atom_clash_kind(atom)?
                } else {
                    "empty_head"
                };
                let mut participants = participant_ids.to_vec();
                participants.sort_unstable();
                participants.dedup();
                kernel.install_clash(
                    kind.to_owned(),
                    support,
                    participants,
                    provenance_ids.first().copied(),
                )
            }
            [atom] => {
                self.dispatch_normalized(kernel, atom.clone(), support, false, provenance_ids)
            }
            _ => self.install_disjunction(kernel, remaining, support),
        }
    }

    pub fn apply_match(
        &mut self,
        kernel: &mut TableauKernel,
        matched: &JoinMatch,
    ) -> NativeResult<bool> {
        let clause = self.program.clause(matched.clause_id)?.clone();
        let bindings: Bindings = matched
            .bindings
            .iter()
            .map(|value| ((value.sort, value.variable_id), value.node))
            .collect();
        let mut atoms = Vec::new();
        let mut dependencies = vec![matched.dependency.clone()];
        for atom in &clause.head {
            let (grounded, path) = self.ground_atom(kernel, atom, &bindings)?;
            atoms.push(grounded);
            dependencies.push(path);
        }
        let dependency_refs: Vec<_> = dependencies.iter().collect();
        self.apply_ground_head(
            kernel,
            atoms,
            DependencySet::union(&dependency_refs),
            &clause.provenance_ids,
            &matched.premise_row_ids,
        )
    }

    pub fn process_next_disjunction(
        &mut self,
        kernel: &mut TableauKernel,
        cancellation: &CancellationState,
    ) -> NativeResult<BranchTransition> {
        DisjunctionBrancher::process_next(kernel, self, cancellation)
    }

    pub fn resolve_clash(
        &mut self,
        kernel: &mut TableauKernel,
        cancellation: &CancellationState,
    ) -> NativeResult<BranchTransition> {
        let brancher = self.brancher;
        brancher.resolve_until_choice_or_unsat(kernel, self, cancellation)
    }

    fn dispatch_normalized(
        &mut self,
        kernel: &mut TableauKernel,
        atom: GroundAtom,
        dependency: DependencySet,
        core: bool,
        provenance_ids: &[u32],
    ) -> NativeResult<bool> {
        let predicate = self.program.predicate(atom.predicate_id)?.clone();
        match predicate.kind {
            PredicateKind::OrderingGuard => Err(NativeError::invariant(
                "ordering guards cannot be dispatched as heads",
            )),
            PredicateKind::Equality => {
                self.dispatch_equality(kernel, atom, dependency, core, provenance_ids)
            }
            PredicateKind::AnnotatedEquality => {
                let atom_id = self.atom_id(atom.clone())?;
                let changed =
                    Self::add_extension_atom(kernel, &atom, dependency, core, provenance_ids)?;
                kernel.enqueue_integer(
                    "annotated_equalities",
                    atom_id,
                    vec![i64::from(atom_id)],
                )?;
                Ok(changed)
            }
            _ => {
                let changed = Self::add_extension_atom(
                    kernel,
                    &atom,
                    dependency.clone(),
                    core,
                    provenance_ids,
                )?;
                if predicate.kind == PredicateKind::Inequality
                    && atom.arguments[0] == atom.arguments[1]
                {
                    let atom_id = self.atom_id(atom.clone())?;
                    kernel.install_clash(
                        "equality_inequality".to_owned(),
                        dependency.clone(),
                        vec![atom_id],
                        provenance_ids.first().copied(),
                    )?;
                }
                let mut contradicted = false;
                if let Some(opposite) = predicate.opposite_predicate_id {
                    if let Some(refutation) =
                        Self::fact_dependency(kernel, opposite, &atom.arguments)?
                    {
                        let atom_id = self.atom_id(atom.clone())?;
                        kernel.install_clash(
                            "positive_negative_atom".to_owned(),
                            DependencySet::union(&[&dependency, &refutation]),
                            vec![atom_id],
                            provenance_ids.first().copied(),
                        )?;
                        contradicted = true;
                    }
                }
                if !contradicted
                    && matches!(
                        predicate.kind,
                        PredicateKind::DataRole | PredicateKind::NegatedDataRole
                    )
                {
                    let opposite = predicate.opposite_predicate_id.ok_or_else(|| {
                        NativeError::invariant(
                            "compiled data-role negation lacks its opposite predicate",
                        )
                    })?;
                    self.derive_concrete_role_inequalities(
                        kernel,
                        &atom,
                        opposite,
                        &dependency,
                        core,
                        provenance_ids,
                    )?;
                }
                if matches!(
                    predicate.kind,
                    PredicateKind::AtLeastObject | PredicateKind::AtLeastData
                ) {
                    let root = atom.arguments[0];
                    kernel.mark_existential(root, atom.predicate_id, true)?;
                    let rank = kernel.node_rank(root)?;
                    kernel.enqueue_node(
                        "existential_candidates",
                        root,
                        vec![i64::from(rank.0), i64::from(rank.1), i64::from(rank.2)],
                    )?;
                }
                Ok(changed)
            }
        }
    }

    fn derive_concrete_role_inequalities(
        &mut self,
        kernel: &mut TableauKernel,
        atom: &GroundAtom,
        opposite_predicate_id: u32,
        dependency: &DependencySet,
        core: bool,
        provenance_ids: &[u32],
    ) -> NativeResult<()> {
        let source = atom.arguments[0];
        let target = atom.arguments[1];
        let inequality_id = self
            .program
            .predicates()
            .iter()
            .filter(|predicate| {
                predicate.kind == PredicateKind::Inequality
                    && predicate.argument_sorts == [TermSort::Data, TermSort::Data]
            })
            .map(|predicate| predicate.predicate_id)
            .next_back();
        let candidates = kernel
            .candidate_fact_ids(opposite_predicate_id, &BTreeMap::from([(0, source)]))?
            .into_iter()
            .map(|row_id| {
                let row = kernel.fact(row_id)?;
                Ok((row.key.arguments[1], row.supports.clone(), row.core))
            })
            .collect::<NativeResult<Vec<_>>>()?;
        for (other, supports, opposite_core) in candidates {
            let Some(predicate_id) = inequality_id else {
                if self.fixed_data_values_differ(kernel, target, other)? {
                    continue;
                }
                return Err(NativeError::invariant(
                    "non-fixed data-role negation requires a compiled inequality predicate",
                ));
            };
            for support in supports {
                self.dispatch_ground_atom(
                    kernel,
                    GroundAtom::new(predicate_id, vec![target, other])?,
                    DependencySet::union(&[dependency, &support]),
                    core || opposite_core,
                    provenance_ids,
                )?;
            }
        }
        Ok(())
    }

    fn fixed_data_values_differ(
        &self,
        kernel: &TableauKernel,
        left: NodeHandle,
        right: NodeHandle,
    ) -> NativeResult<bool> {
        let left = kernel.canonical_handle(left)?.0;
        let right = kernel.canonical_handle(right)?.0;
        let mut left_identities = BTreeSet::new();
        let mut right_identities = BTreeSet::new();
        for (identity, handle) in self.data_nodes.iter() {
            let representative = kernel.canonical_handle(*handle)?.0;
            if representative == left {
                left_identities.insert(*identity);
            }
            if representative == right {
                right_identities.insert(*identity);
            }
        }
        Ok(!left_identities.is_empty()
            && !right_identities.is_empty()
            && left_identities.is_disjoint(&right_identities))
    }

    fn dispatch_equality(
        &mut self,
        kernel: &mut TableauKernel,
        atom: GroundAtom,
        dependency: DependencySet,
        core: bool,
        provenance_ids: &[u32],
    ) -> NativeResult<bool> {
        let left = atom.arguments[0];
        let right = atom.arguments[1];
        if self.fixed_data_values_differ(kernel, left, right)? {
            let atom_id = self.atom_id(atom)?;
            return kernel.install_clash(
                "equality_inequality".to_owned(),
                dependency,
                vec![atom_id],
                provenance_ids.first().copied(),
            );
        }
        if let Some(opposite) = self
            .program
            .predicate(atom.predicate_id)?
            .opposite_predicate_id
        {
            if let Some(inequality) = Self::fact_dependency(kernel, opposite, &[left, right])? {
                let atom_id = self.atom_id(atom)?;
                return kernel.install_clash(
                    "equality_inequality".to_owned(),
                    DependencySet::union(&[&dependency, &inequality]),
                    vec![atom_id],
                    provenance_ids.first().copied(),
                );
            }
        }
        let changed = left != right;
        let representative = if changed {
            let result =
                self.merge_nodes_semantic(kernel, left, right, dependency.clone(), None)?;
            if result.clashed {
                return Ok(true);
            }
            result.representative
        } else {
            left
        };
        let reflexive = GroundAtom::new(atom.predicate_id, vec![representative, representative])?;
        Ok(
            Self::add_extension_atom(kernel, &reflexive, dependency, core, provenance_ids)?
                || changed,
        )
    }

    fn add_extension_atom(
        kernel: &mut TableauKernel,
        atom: &GroundAtom,
        dependency: DependencySet,
        core: bool,
        provenance_ids: &[u32],
    ) -> NativeResult<bool> {
        let mut provenance = provenance_ids.to_vec();
        provenance.sort_unstable();
        provenance.dedup();
        let outcome = kernel.add_fact_detailed(
            atom.predicate_id,
            atom.arguments.clone(),
            dependency.clone(),
            core,
            provenance.first().copied(),
        )?;
        for provenance_id in provenance.iter().skip(1) {
            kernel.add_fact(
                atom.predicate_id,
                atom.arguments.clone(),
                dependency.clone(),
                core,
                Some(*provenance_id),
            )?;
        }
        Ok(outcome.created || outcome.support_changed)
    }

    fn install_disjunction(
        &mut self,
        kernel: &mut TableauKernel,
        atoms: Vec<GroundAtom>,
        dependency: DependencySet,
    ) -> NativeResult<bool> {
        let mut atoms = self.order_disjuncts(kernel, atoms)?;
        atoms.dedup();
        if let Some(disjunction_id) = self.disjunction_keys.get(&atoms).copied() {
            match kernel.disjunction(disjunction_id) {
                Ok(record) if record.active => {
                    if kernel.strengthen_disjunction(disjunction_id, dependency.clone())? {
                        for (level, atom_id) in kernel.branch_choices_for_source(disjunction_id) {
                            GroundAtomAccess::dispatch_atom(
                                self,
                                kernel,
                                atom_id,
                                dependency.clone().add(level),
                            )?;
                        }
                    }
                    return Ok(false);
                }
                Ok(_) | Err(_) => {
                    self.disjunction_keys.remove(&atoms);
                }
            }
        }
        let mut identifiers = Vec::new();
        for atom in &atoms {
            identifiers.push(self.atom_id(atom.clone())?);
        }
        let disjunction_id = kernel.add_disjunction(identifiers, dependency)?;
        self.disjunction_keys.insert(atoms, disjunction_id);
        Ok(true)
    }

    fn atom_is_satisfied_impl(
        &self,
        kernel: &TableauKernel,
        atom: &GroundAtom,
    ) -> NativeResult<bool> {
        let (normalized, _path) = self.canonical_atom(kernel, atom.clone())?;
        let kind = self.program.predicate_kind(normalized.predicate_id)?;
        if kind == PredicateKind::Equality {
            return Ok(normalized.arguments[0] == normalized.arguments[1]);
        }
        Ok(
            Self::fact_dependency(kernel, normalized.predicate_id, &normalized.arguments)?
                .is_some(),
        )
    }

    fn atom_refutation_impl(
        &self,
        kernel: &TableauKernel,
        atom: &GroundAtom,
    ) -> NativeResult<Option<DependencySet>> {
        let (normalized, path) = self.canonical_atom(kernel, atom.clone())?;
        let predicate = self.program.predicate(normalized.predicate_id)?;
        if predicate.kind == PredicateKind::Inequality
            && normalized.arguments[0] == normalized.arguments[1]
        {
            return Ok(Some(path));
        }
        let Some(opposite) = predicate.opposite_predicate_id else {
            return Ok(None);
        };
        Ok(
            Self::fact_dependency(kernel, opposite, &normalized.arguments)?
                .map(|dependency| DependencySet::union(&[&path, &dependency])),
        )
    }

    fn fact_dependency(
        kernel: &TableauKernel,
        predicate_id: u32,
        arguments: &[NodeHandle],
    ) -> NativeResult<Option<DependencySet>> {
        let mut bindings = BTreeMap::new();
        for (position, argument) in arguments.iter().copied().enumerate() {
            bindings.insert(
                u32::try_from(position)
                    .map_err(|_| NativeError::invariant("ground atom arity exceeds u32"))?,
                argument,
            );
        }
        let mut supports = Vec::new();
        for row_id in kernel.candidate_fact_ids(predicate_id, &bindings)? {
            supports.extend(kernel.fact(row_id)?.supports.iter());
        }
        Ok(supports
            .into_iter()
            .min_by_key(|value| dependency_rank(value))
            .cloned())
    }

    fn canonical_atom(
        &self,
        kernel: &TableauKernel,
        atom: GroundAtom,
    ) -> NativeResult<(GroundAtom, DependencySet)> {
        self.program.validate_ground_atom(&atom)?;
        let predicate = self.program.predicate(atom.predicate_id)?;
        let mut arguments = Vec::new();
        let mut dependencies = Vec::new();
        for (handle, sort) in atom
            .arguments
            .into_iter()
            .zip(predicate.argument_sorts.iter().copied())
        {
            let (representative, path) = kernel.canonical_handle(handle)?;
            if kernel.node_sort(representative)? != sort.node_sort() {
                return Err(NativeError::invariant(
                    "ground atom argument has the wrong node sort",
                ));
            }
            arguments.push(representative);
            dependencies.push(path);
        }
        if matches!(
            predicate.kind,
            PredicateKind::Equality
                | PredicateKind::Inequality
                | PredicateKind::OrderingGuard
                | PredicateKind::AnnotatedEquality
        ) {
            let first_rank = kernel.node_rank(arguments[0])?;
            let second_rank = kernel.node_rank(arguments[1])?;
            if second_rank < first_rank {
                arguments.swap(0, 1);
            }
        }
        let dependency_refs: Vec<_> = dependencies.iter().collect();
        Ok((
            GroundAtom::new(atom.predicate_id, arguments)?,
            DependencySet::union(&dependency_refs),
        ))
    }

    fn ground_atom(
        &self,
        kernel: &TableauKernel,
        atom: &RuleAtom,
        bindings: &Bindings,
    ) -> NativeResult<(GroundAtom, DependencySet)> {
        let mut arguments = Vec::new();
        let mut dependencies = Vec::new();
        for term in &atom.arguments {
            let handle = match term {
                Term::Variable { sort, variable_id } => bindings
                    .get(&(*sort, *variable_id))
                    .copied()
                    .ok_or_else(|| {
                        NativeError::invariant("head variable is absent from the join substitution")
                    })?,
                Term::Individual { individual_id } => {
                    *self.source_nodes.get(individual_id).ok_or_else(|| {
                        NativeError::invariant("compiled individual has no tableau node")
                    })?
                }
                Term::DataConstant {
                    data_identity_id, ..
                } => *self.data_nodes.get(data_identity_id).ok_or_else(|| {
                    NativeError::invariant("compiled data identity has no tableau node")
                })?,
            };
            let (representative, path) = kernel.canonical_handle(handle)?;
            arguments.push(representative);
            dependencies.push(path);
        }
        let dependency_refs: Vec<_> = dependencies.iter().collect();
        let (grounded, canonical_dependency) =
            self.canonical_atom(kernel, GroundAtom::new(atom.predicate_id, arguments)?)?;
        let resolved_dependency = DependencySet::union(&dependency_refs);
        Ok((
            grounded,
            DependencySet::union(&[&resolved_dependency, &canonical_dependency]),
        ))
    }

    fn order_disjuncts(
        &self,
        kernel: &TableauKernel,
        atoms: Vec<GroundAtom>,
    ) -> NativeResult<Vec<GroundAtom>> {
        let mut ranked = Vec::new();
        for atom in atoms {
            ranked.push((self.disjunct_rank(kernel, &atom)?, atom));
        }
        ranked.sort_by(|left, right| left.0.cmp(&right.0).then_with(|| left.1.cmp(&right.1)));
        Ok(ranked.into_iter().map(|(_rank, atom)| atom).collect())
    }

    fn disjunct_rank(
        &self,
        kernel: &TableauKernel,
        atom: &GroundAtom,
    ) -> NativeResult<DisjunctRank> {
        let kind = self.program.predicate_kind(atom.predicate_id)?;
        let kind_rank = match kind {
            PredicateKind::Equality => 0,
            PredicateKind::AnnotatedEquality => 1,
            PredicateKind::Inequality => 2,
            PredicateKind::Concept
            | PredicateKind::NegatedConcept
            | PredicateKind::Nominal
            | PredicateKind::NegatedNominal => 3,
            _ => 4,
        };
        let ranks = atom
            .arguments
            .iter()
            .map(|handle| kernel.node_rank(*handle))
            .collect::<NativeResult<Vec<_>>>()?;
        Ok((kind_rank, kind, atom.predicate_id, ranks))
    }

    fn single_atom_clash_kind(&self, atom: &GroundAtom) -> NativeResult<&'static str> {
        let predicate = self.program.predicate(atom.predicate_id)?;
        if matches!(
            predicate.kind,
            PredicateKind::Equality | PredicateKind::Inequality
        ) {
            Ok("equality_inequality")
        } else if predicate.opposite_predicate_id.is_some() {
            Ok("positive_negative_atom")
        } else {
            Ok("empty_head")
        }
    }
}

impl GroundAtomAccess for RuleEngine {
    fn atom_is_satisfied(&self, kernel: &TableauKernel, atom_id: u32) -> NativeResult<bool> {
        self.atom_is_satisfied_impl(kernel, self.atom_for_id(atom_id)?)
    }

    fn atom_refutation_dependency(
        &self,
        kernel: &TableauKernel,
        atom_id: u32,
    ) -> NativeResult<Option<DependencySet>> {
        self.atom_refutation_impl(kernel, self.atom_for_id(atom_id)?)
    }

    fn dispatch_atom(
        &mut self,
        kernel: &mut TableauKernel,
        atom_id: u32,
        dependency: DependencySet,
    ) -> NativeResult<bool> {
        let atom = self.atom_for_id(atom_id)?.clone();
        self.dispatch_ground_atom(kernel, atom, dependency, false, &[])
    }
}

fn remaining_join_limits(limits: RuleLimits, completed_steps: u64) -> NativeResult<RuleLimits> {
    let Some(remaining) = limits.max_join_steps.checked_sub(completed_steps) else {
        return Err(NativeError::invariant(
            "completed join steps exceed the configured limit",
        ));
    };
    if remaining == 0 {
        return Err(resource_limit(
            "hyperresolution join-step limit exceeded",
            "max_join_steps",
            completed_steps.saturating_add(1),
            limits.max_join_steps,
        ));
    }
    RuleLimits::new(
        remaining,
        limits.max_matches_per_generation,
        limits.cancellation_interval,
    )
}

fn adjust_join_limit(
    mut error: NativeError,
    completed_steps: u64,
    limits: RuleLimits,
) -> NativeError {
    if error.kind == ErrorKind::Resource
        && error.context.get("limit").map(String::as_str) == Some("max_join_steps")
    {
        let local_observed = error
            .context
            .get("observed")
            .and_then(|value| value.parse::<u64>().ok())
            .unwrap_or(1);
        error.context.insert(
            "observed".to_owned(),
            completed_steps.saturating_add(local_observed).to_string(),
        );
        error
            .context
            .insert("allowed".to_owned(), limits.max_join_steps.to_string());
    }
    error
}

fn resource_limit(
    message: &'static str,
    limit: &'static str,
    observed: u64,
    allowed: u64,
) -> NativeError {
    NativeError::new(ErrorKind::Resource, "RESOURCE_LIMIT", message)
        .with_context("limit", limit)
        .with_context("observed", observed.to_string())
        .with_context("allowed", allowed.to_string())
}

fn recover_rule_operation<T>(
    kernel: &mut TableauKernel,
    result: NativeResult<T>,
) -> NativeResult<T> {
    match result {
        Ok(value) => Ok(value),
        Err(error) => {
            kernel.reset_to_operation_root().map_err(|reset_error| {
                NativeError::invariant(format!(
                    "rule operation recovery failed after {}: {reset_error}",
                    error.code
                ))
            })?;
            Err(error)
        }
    }
}

fn dependency_rank(value: &DependencySet) -> (usize, Option<u32>, Vec<u32>) {
    (
        value.as_slice().len(),
        value.maximum(),
        value.as_slice().iter().rev().copied().collect(),
    )
}

fn usize_from_u32(value: u32, name: &str) -> NativeResult<usize> {
    usize::try_from(value)
        .map_err(|_| NativeError::wire(format!("{name} cannot fit this platform")))
}

fn usize_from_u64(value: u64) -> NativeResult<usize> {
    usize::try_from(value)
        .map_err(|_| NativeError::wire("cancellation interval cannot fit this platform"))
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use crate::cancel::CancellationHandle;
    use crate::model::NodeKind;

    use super::super::model::{RuleClause, RulePredicate, VariableBinding};
    use super::*;

    fn concept(predicate_id: u32) -> NativeResult<RulePredicate> {
        Ok(
            RulePredicate::new(predicate_id, PredicateKind::Concept, vec![TermSort::Object])?
                .with_symbol_id(predicate_id),
        )
    }

    fn atom(predicate_id: u32, node: NodeHandle) -> NativeResult<GroundAtom> {
        GroundAtom::new(predicate_id, vec![node])
    }

    fn has_fact(
        kernel: &TableauKernel,
        predicate_id: u32,
        arguments: &[NodeHandle],
    ) -> NativeResult<bool> {
        let bindings = arguments
            .iter()
            .copied()
            .enumerate()
            .map(|(position, handle)| {
                u32::try_from(position)
                    .map(|position| (position, handle))
                    .map_err(|_| NativeError::invariant("test atom arity exceeds u32"))
            })
            .collect::<NativeResult<BTreeMap<_, _>>>()?;
        Ok(!kernel
            .candidate_fact_ids(predicate_id, &bindings)?
            .is_empty())
    }

    fn cancellation() -> NativeResult<Arc<CancellationState>> {
        Ok(CancellationHandle::from_options(None, None)?.state())
    }

    #[test]
    fn deterministic_and_disjunctive_heads_are_canonical() -> NativeResult<()> {
        let program = RuleProgram::new(vec![concept(0)?, concept(1)?, concept(2)?], Vec::new())?;
        let mut kernel = TableauKernel::new();
        let node = kernel.create_node(NodeKind::Root, None, false, None, None, None)?;
        kernel.begin_operation()?;
        let mut engine = RuleEngine::new(program, BTreeMap::new(), BTreeMap::new(), true)?;

        assert!(engine.apply_ground_head(
            &mut kernel,
            vec![atom(0, node)?, atom(0, node)?],
            DependencySet::empty(),
            &[7],
            &[3, 3],
        )?);
        assert!(has_fact(&kernel, 0, &[node])?);
        assert!(!engine.apply_ground_head(
            &mut kernel,
            vec![atom(0, node)?],
            DependencySet::empty(),
            &[7],
            &[],
        )?);

        assert!(engine.apply_ground_head(
            &mut kernel,
            vec![atom(2, node)?, atom(1, node)?],
            DependencySet::empty(),
            &[8],
            &[4],
        )?);
        let cancellation = cancellation()?;
        assert_eq!(
            engine.process_next_disjunction(&mut kernel, &cancellation)?,
            BranchTransition::Branched
        );
        assert!(has_fact(&kernel, 1, &[node])?);
        assert!(!has_fact(&kernel, 2, &[node])?);
        kernel.check_invariants()
    }

    #[test]
    fn opposite_atoms_and_equality_inequality_install_exact_clashes() -> NativeResult<()> {
        let positive = concept(0)?.with_opposite(1);
        let negative =
            RulePredicate::new(1, PredicateKind::NegatedConcept, vec![TermSort::Object])?
                .with_symbol_id(0)
                .with_opposite(0);
        let equality = RulePredicate::new(
            2,
            PredicateKind::Equality,
            vec![TermSort::Object, TermSort::Object],
        )?
        .with_opposite(3);
        let inequality = RulePredicate::new(
            3,
            PredicateKind::Inequality,
            vec![TermSort::Object, TermSort::Object],
        )?
        .with_opposite(2);
        let program = RuleProgram::new(vec![positive, negative, equality, inequality], Vec::new())?;

        let mut kernel = TableauKernel::new();
        let left = kernel.create_node(NodeKind::Root, None, false, None, None, None)?;
        let mut engine = RuleEngine::new(program.clone(), BTreeMap::new(), BTreeMap::new(), true)?;
        engine.dispatch_ground_atom(
            &mut kernel,
            atom(0, left)?,
            DependencySet::empty(),
            false,
            &[],
        )?;
        engine.dispatch_ground_atom(
            &mut kernel,
            atom(1, left)?,
            DependencySet::empty(),
            false,
            &[],
        )?;
        assert_eq!(
            kernel.clash().map(|value| value.kind.as_str()),
            Some("positive_negative_atom")
        );

        let mut equality_kernel = TableauKernel::new();
        let left = equality_kernel.create_node(NodeKind::Root, None, false, None, None, None)?;
        let right = equality_kernel.create_node(NodeKind::Root, None, false, None, None, None)?;
        let mut equality_engine = RuleEngine::new(program, BTreeMap::new(), BTreeMap::new(), true)?;
        equality_engine.dispatch_ground_atom(
            &mut equality_kernel,
            GroundAtom::new(3, vec![left, right])?,
            DependencySet::empty(),
            false,
            &[],
        )?;
        equality_engine.dispatch_ground_atom(
            &mut equality_kernel,
            GroundAtom::new(2, vec![left, right])?,
            DependencySet::empty(),
            false,
            &[],
        )?;
        assert_eq!(
            equality_kernel.clash().map(|value| value.kind.as_str()),
            Some("equality_inequality")
        );
        assert_ne!(
            equality_kernel.canonical_handle(left)?.0,
            equality_kernel.canonical_handle(right)?.0
        );
        equality_kernel.check_invariants()
    }

    #[test]
    fn opposed_data_roles_materialize_value_inequality() -> NativeResult<()> {
        let positive = RulePredicate::new(
            0,
            PredicateKind::DataRole,
            vec![TermSort::Object, TermSort::Data],
        )?
        .with_role_id(0)
        .with_opposite(1);
        let negative = RulePredicate::new(
            1,
            PredicateKind::NegatedDataRole,
            vec![TermSort::Object, TermSort::Data],
        )?
        .with_role_id(0)
        .with_opposite(0);
        let inequality = RulePredicate::new(
            2,
            PredicateKind::Inequality,
            vec![TermSort::Data, TermSort::Data],
        )?;
        let program = RuleProgram::new(vec![positive, negative, inequality], Vec::new())?;
        let mut kernel = TableauKernel::new();
        let source = kernel.create_node(NodeKind::Root, None, false, None, None, None)?;
        let left = kernel.create_node(NodeKind::Concrete, None, false, None, None, None)?;
        let right = kernel.create_node(NodeKind::Concrete, None, false, None, None, None)?;
        let mut engine = RuleEngine::new(
            program,
            BTreeMap::new(),
            BTreeMap::from([(0, left), (1, right)]),
            true,
        )?;
        engine.dispatch_ground_atom(
            &mut kernel,
            GroundAtom::new(1, vec![source, right])?,
            DependencySet::empty(),
            false,
            &[4],
        )?;
        engine.dispatch_ground_atom(
            &mut kernel,
            GroundAtom::new(0, vec![source, left])?,
            DependencySet::empty(),
            true,
            &[5],
        )?;

        assert!(has_fact(&kernel, 2, &[left, right])?);
        assert!(kernel.clash().is_none());
        kernel.check_invariants()
    }

    #[test]
    fn join_match_grounding_dispatches_the_compiled_head() -> NativeResult<()> {
        let variable = Term::variable(0, TermSort::Object);
        let body = RuleAtom::new(0, vec![variable.clone()])?;
        let head = RuleAtom::new(1, vec![variable])?;
        let clause = RuleClause::new(0, vec![body], vec![head], vec![9], vec![0])?;
        let program = RuleProgram::new(vec![concept(0)?, concept(1)?], vec![clause])?;
        let mut kernel = TableauKernel::new();
        let node = kernel.create_node(NodeKind::Root, None, false, None, None, None)?;
        let mut engine = RuleEngine::new(program, BTreeMap::new(), BTreeMap::new(), true)?;
        let matched = JoinMatch::new(
            0,
            0,
            vec![VariableBinding {
                sort: TermSort::Object,
                variable_id: 0,
                node,
            }],
            DependencySet::empty(),
            vec![4],
        )?;

        assert!(engine.apply_match(&mut kernel, &matched)?);
        assert!(has_fact(&kernel, 1, &[node])?);
        kernel.check_invariants()
    }

    #[test]
    fn semi_naive_saturation_replays_the_wp09_chain() -> NativeResult<()> {
        let variable = Term::variable(0, TermSort::Object);
        let source_to_middle = RuleClause::new(
            0,
            vec![RuleAtom::new(0, vec![variable.clone()])?],
            vec![RuleAtom::new(1, vec![variable.clone()])?],
            vec![0],
            vec![0],
        )?;
        let middle_to_target = RuleClause::new(
            1,
            vec![RuleAtom::new(1, vec![variable.clone()])?],
            vec![RuleAtom::new(2, vec![variable])?],
            vec![1],
            vec![0],
        )?;
        let program = RuleProgram::new(
            vec![concept(0)?, concept(1)?, concept(2)?],
            vec![source_to_middle, middle_to_target],
        )?;
        let mut kernel = TableauKernel::new();
        let node = kernel.create_node(NodeKind::Root, None, false, Some(0), None, None)?;
        let mut engine =
            RuleEngine::new(program, BTreeMap::from([(0, node)]), BTreeMap::new(), true)?;
        engine.dispatch_ground_atom(
            &mut kernel,
            atom(0, node)?,
            DependencySet::empty(),
            true,
            &[2],
        )?;
        let control = cancellation()?;
        engine.initialize(&mut kernel, Arc::clone(&control))?;

        assert!(engine.initialized());
        assert!(engine.saturate_hyperresolution(&mut kernel, control)? >= 2);
        assert!(has_fact(&kernel, 0, &[node])?);
        assert!(has_fact(&kernel, 1, &[node])?);
        assert!(has_fact(&kernel, 2, &[node])?);
        assert_eq!(engine.apply_next_delta(&mut kernel, cancellation()?)?, 0);
        kernel.check_invariants()
    }

    #[test]
    fn initialization_fires_ground_rules_and_reflexive_equality() -> NativeResult<()> {
        let equality = RulePredicate::new(
            0,
            PredicateKind::Equality,
            vec![TermSort::Object, TermSort::Object],
        )?;
        let marker = concept(1)?;
        let ground_rule = RuleClause::new(
            0,
            Vec::new(),
            vec![RuleAtom::new(1, vec![Term::individual(7)])?],
            vec![4],
            Vec::new(),
        )?;
        let program = RuleProgram::new(vec![equality, marker], vec![ground_rule])?;
        let mut kernel = TableauKernel::new();
        let node = kernel.create_node(NodeKind::Root, None, true, Some(7), None, None)?;
        let mut engine =
            RuleEngine::new(program, BTreeMap::from([(7, node)]), BTreeMap::new(), true)?;

        engine.initialize(&mut kernel, cancellation()?)?;

        assert!(has_fact(&kernel, 0, &[node, node])?);
        assert!(has_fact(&kernel, 1, &[node])?);
        kernel.check_invariants()
    }

    #[test]
    fn match_limit_recovers_all_partial_generation_mutations() -> NativeResult<()> {
        let variable = Term::variable(0, TermSort::Object);
        let clause = RuleClause::new(
            0,
            vec![RuleAtom::new(0, vec![variable.clone()])?],
            vec![RuleAtom::new(1, vec![variable])?],
            vec![0],
            vec![0],
        )?;
        let program = RuleProgram::new(vec![concept(0)?, concept(1)?], vec![clause])?;
        let mut kernel = TableauKernel::new();
        let first = kernel.create_node(NodeKind::Root, None, false, None, None, None)?;
        let second = kernel.create_node(NodeKind::Root, None, false, None, None, None)?;
        let mut engine = RuleEngine::with_limits(
            program,
            BTreeMap::new(),
            BTreeMap::new(),
            RuleLimits::new(10_000, 1, 1)?,
            true,
        )?;
        for node in [first, second] {
            engine.dispatch_ground_atom(
                &mut kernel,
                atom(0, node)?,
                DependencySet::empty(),
                false,
                &[],
            )?;
        }
        engine.initialize(&mut kernel, cancellation()?)?;

        let error = engine
            .apply_next_delta(&mut kernel, cancellation()?)
            .err()
            .ok_or_else(|| NativeError::invariant("match limit unexpectedly succeeded"))?;
        assert_eq!(error.kind, ErrorKind::Resource);
        assert_eq!(
            error.context.get("limit").map(String::as_str),
            Some("max_matches_per_generation")
        );
        assert!(!has_fact(&kernel, 1, &[first])?);
        assert!(!has_fact(&kernel, 1, &[second])?);
        assert!(has_fact(&kernel, 0, &[first])?);
        assert!(has_fact(&kernel, 0, &[second])?);
        kernel.check_invariants()
    }

    #[test]
    fn annotated_equalities_remain_queued_actions_with_historical_support() -> NativeResult<()> {
        let filler = concept(0)?;
        let annotated = RulePredicate::new(
            1,
            PredicateKind::AnnotatedEquality,
            vec![TermSort::Object; 3],
        )?
        .with_cardinality(2, 4, 0);
        let program = RuleProgram::new(vec![filler, annotated], Vec::new())?;
        let mut engine = RuleEngine::new(program, BTreeMap::new(), BTreeMap::new(), true)?;
        let mut kernel = TableauKernel::new();
        let first = kernel.create_node(NodeKind::Root, None, false, None, None, None)?;
        let second = kernel.create_node(NodeKind::Root, None, false, None, None, None)?;
        let root = kernel.create_node(NodeKind::Root, None, false, None, None, None)?;
        let atom = GroundAtom::new(1, vec![first, second, root])?;

        assert!(engine.dispatch_ground_atom(
            &mut kernel,
            atom.clone(),
            DependencySet::empty(),
            false,
            &[7, 9],
        )?);
        let pending = engine
            .take_pending_annotated_equality(&mut kernel)?
            .ok_or_else(|| NativeError::invariant("annotated equality was not queued"))?;
        assert_eq!(pending.action_id, 0);
        assert_eq!(pending.atom, atom);
        assert_eq!(pending.supports, vec![DependencySet::empty()]);
        assert_eq!(pending.provenance_ids, vec![7, 9]);
        assert!(engine
            .take_pending_annotated_equality(&mut kernel)?
            .is_none());
        kernel.check_invariants()
    }
}
