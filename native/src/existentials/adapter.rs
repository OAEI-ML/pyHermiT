//! Coarse adapters between the standalone expansion kernel and native runtime state.
// SPDX-License-Identifier: LGPL-3.0-or-later

use std::collections::{BTreeMap, BTreeSet};

use crate::blocking::BlockingManager;
use crate::error::{ErrorKind as NativeErrorKind, NativeError, NativeResult};
use crate::model::{
    DependencySet as NativeDependencySet, NodeHandle, NodeKind as NativeNodeKind, NodeLifecycle,
};
use crate::rules::{
    GroundAtom as NativeGroundAtom, PredicateKind, RuleEngine, RuleProgram, TermSort,
};
use crate::session::OperationControl;
use crate::store::TableauKernel;

use super::model::{
    AtLeastPredicate, BranchRecord, CandidatePriority, CanonicalNode, ClashKind, ClashRecord,
    DependencySet, ExpansionControl, ExpansionError, ExpansionErrorKind, ExpansionProgram,
    ExpansionRuleAccess, ExpansionStateMutation, ExpansionStateRead, FactBinding, FactRecord,
    GroundAtom, NodeKind, NodeRecord, ReuseBranchRecord, RoleVocabulary,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SpecialRoleIds {
    pub top_object: u32,
    pub bottom_object: u32,
    pub top_data: u32,
    pub bottom_data: u32,
}

/// Compile the expansion-specific predicate view once at session construction.
pub fn expansion_program_from_rules(
    program: &RuleProgram,
    special_roles: SpecialRoleIds,
    reusable_atomic_fillers: &BTreeSet<u32>,
) -> Result<ExpansionProgram, ExpansionError> {
    let mut object_roles = BTreeMap::new();
    let mut data_roles = BTreeMap::new();
    let mut object_inequality = None;
    let mut data_inequality = None;
    let mut obligations = Vec::new();
    for predicate in program.predicates() {
        match predicate.kind {
            PredicateKind::ObjectRole => insert_role(
                &mut object_roles,
                predicate.role_id,
                predicate.predicate_id,
                "object",
            )?,
            PredicateKind::DataRole => insert_role(
                &mut data_roles,
                predicate.role_id,
                predicate.predicate_id,
                "data",
            )?,
            PredicateKind::Inequality => match predicate.argument_sorts.first() {
                Some(TermSort::Object) => set_unique(
                    &mut object_inequality,
                    predicate.predicate_id,
                    "object inequality",
                )?,
                Some(TermSort::Data) => set_unique(
                    &mut data_inequality,
                    predicate.predicate_id,
                    "data inequality",
                )?,
                None => {
                    return Err(ExpansionError::invalid(
                        "inequality predicate has no argument sort",
                    ));
                }
            },
            PredicateKind::AtLeastObject => {
                let role_id = required(predicate.role_id, "object at-least role")?;
                let filler = required(predicate.filler_predicate_id, "object at-least filler")?;
                obligations.push(
                    AtLeastPredicate::object(
                        predicate.predicate_id,
                        required(predicate.cardinality, "object at-least cardinality")?,
                        role_id,
                        filler,
                    )
                    .with_reusable_filler(reusable_atomic_fillers.contains(&filler)),
                );
            }
            PredicateKind::AtLeastData => obligations.push(AtLeastPredicate::data(
                predicate.predicate_id,
                required(predicate.cardinality, "data at-least cardinality")?,
                predicate.annotation.clone(),
                required(predicate.filler_predicate_id, "data at-least filler")?,
            )),
            _ => {}
        }
    }
    ExpansionProgram::new(
        obligations,
        RoleVocabulary {
            object_role_predicates: object_roles,
            data_role_predicates: data_roles,
            top_object_role_id: special_roles.top_object,
            bottom_object_role_id: special_roles.bottom_object,
            top_data_role_id: special_roles.top_data,
            bottom_data_role_id: special_roles.bottom_data,
            object_inequality_predicate_id: object_inequality,
            data_inequality_predicate_id: data_inequality,
        },
    )
}

fn insert_role(
    target: &mut BTreeMap<u32, u32>,
    role_id: Option<u32>,
    predicate_id: u32,
    label: &str,
) -> Result<(), ExpansionError> {
    let role_id = required(role_id, &format!("{label} role ID"))?;
    if target.insert(role_id, predicate_id).is_some() {
        return Err(ExpansionError::invalid(format!(
            "{label} role ID has multiple positive extension predicates"
        )));
    }
    Ok(())
}

fn set_unique(
    target: &mut Option<u32>,
    predicate_id: u32,
    label: &str,
) -> Result<(), ExpansionError> {
    if target.replace(predicate_id).is_some() {
        return Err(ExpansionError::invalid(format!(
            "multiple {label} predicates are unavailable to expansion"
        )));
    }
    Ok(())
}

fn required(value: Option<u32>, label: &str) -> Result<u32, ExpansionError> {
    value.ok_or_else(|| ExpansionError::invalid(format!("{label} is absent")))
}

/// Borrowed coarse state used for one expansion scheduler operation.
pub struct RuntimeExpansionState<'a> {
    kernel: &'a mut TableauKernel,
    blocking: Option<&'a BlockingManager<NodeHandle>>,
}

impl<'a> RuntimeExpansionState<'a> {
    #[must_use]
    pub const fn new(
        kernel: &'a mut TableauKernel,
        blocking: Option<&'a BlockingManager<NodeHandle>>,
    ) -> Self {
        Self { kernel, blocking }
    }

    #[must_use]
    pub const fn kernel(&self) -> &TableauKernel {
        self.kernel
    }

    pub const fn kernel_mut(&mut self) -> &mut TableauKernel {
        self.kernel
    }
}

impl ExpansionStateRead for RuntimeExpansionState<'_> {
    type Node = NodeHandle;

    fn candidate_count(&self) -> Result<usize, ExpansionError> {
        Ok(self.kernel.existential_candidate_count())
    }

    fn node_record(
        &self,
        node: Self::Node,
    ) -> Result<Option<NodeRecord<Self::Node>>, ExpansionError> {
        let Ok(record) = self.kernel.node(node) else {
            return Ok(None);
        };
        if record.lifecycle != NodeLifecycle::Active {
            return Ok(None);
        }
        Ok(Some(NodeRecord {
            node,
            priority: CandidatePriority {
                creation_id: record.creation_id,
                slot: node.slot,
                generation: node.generation,
            },
            kind: expansion_node_kind(record.kind),
            parent: record.parent,
            pending_existentials: record.unprocessed_existentials.clone(),
        }))
    }

    fn canonical_node(
        &self,
        node: Self::Node,
    ) -> Result<Option<CanonicalNode<Self::Node>>, ExpansionError> {
        let Ok((node, dependency)) = self.kernel.canonical_handle(node) else {
            return Ok(None);
        };
        Ok(Some(CanonicalNode {
            node,
            dependency: expansion_dependency(&dependency)?,
        }))
    }

    fn active_nodes(&self) -> Result<Vec<NodeRecord<Self::Node>>, ExpansionError> {
        self.kernel
            .active_node_handles()
            .into_iter()
            .map(|node| {
                self.node_record(node)?.ok_or_else(|| {
                    ExpansionError::invariant("active node disappeared during expansion read")
                })
            })
            .collect()
    }

    fn is_blocked(&self, node: Self::Node) -> Result<bool, ExpansionError> {
        let live = self
            .kernel
            .active_node(node)
            .map_err(native_to_expansion)?
            .blocker
            .is_some();
        Ok(live
            || self
                .blocking
                .is_some_and(|manager| manager.is_blocked(node)))
    }

    fn facts(
        &self,
        predicate_id: u32,
        bindings: &[FactBinding<Self::Node>],
    ) -> Result<Vec<FactRecord<Self::Node>>, ExpansionError> {
        let mut indexed = BTreeMap::new();
        for binding in bindings {
            if indexed.insert(binding.position, binding.node).is_some() {
                return Err(ExpansionError::invalid(
                    "expansion fact bindings repeat a position",
                ));
            }
        }
        self.kernel
            .candidate_fact_ids(predicate_id, &indexed)
            .map_err(native_to_expansion)?
            .into_iter()
            .map(|row_id| {
                let row = self.kernel.fact(row_id).map_err(native_to_expansion)?;
                Ok(FactRecord {
                    row_id,
                    predicate_id: row.key.predicate_id,
                    arguments: row.key.arguments.clone(),
                    supports: row
                        .supports
                        .iter()
                        .map(expansion_dependency)
                        .collect::<Result<Vec<_>, _>>()?,
                    core: row.core,
                })
            })
            .collect()
    }

    fn current_clash(&self) -> Result<Option<ClashRecord>, ExpansionError> {
        self.kernel
            .clash()
            .map(|clash| {
                Ok(ClashRecord {
                    kind: match clash.kind.as_str() {
                        "impossible_cardinality" => ClashKind::ImpossibleCardinality,
                        "empty_head" => ClashKind::EmptyHead,
                        _ => ClashKind::Other,
                    },
                    dependency: expansion_dependency(&clash.dependency)?,
                    details: clash.participants.clone(),
                })
            })
            .transpose()
    }

    fn branch(&self, level: u32) -> Result<Option<BranchRecord>, ExpansionError> {
        let Ok(branch) = self.kernel.branch(level) else {
            return Ok(None);
        };
        let current_alternative = branch
            .alternatives
            .get(branch.next_alternative)
            .copied()
            .ok_or_else(|| ExpansionError::invariant("branch has no current alternative"))?;
        Ok(Some(BranchRecord {
            level,
            base_dependency: expansion_dependency(&branch.base_dependency)?,
            learned_dependency: expansion_dependency(&branch.learned_dependency)?,
            current_alternative,
        }))
    }

    fn reuse_branch(
        &self,
        level: u32,
    ) -> Result<Option<ReuseBranchRecord<Self::Node>>, ExpansionError> {
        self.kernel
            .existential_reuse_branch(level)
            .map(|record| {
                Ok(ReuseBranchRecord {
                    level,
                    root: record.root,
                    predicate_id: record.predicate_id,
                    supports: record
                        .supports
                        .iter()
                        .map(expansion_dependency)
                        .collect::<Result<Vec<_>, _>>()?,
                })
            })
            .transpose()
    }

    fn reuse_node(&self, filler_predicate_id: u32) -> Result<Option<Self::Node>, ExpansionError> {
        Ok(self.kernel.existential_reuse_node(filler_predicate_id))
    }

    fn reuse_disabled(&self, predicate_id: u32) -> Result<bool, ExpansionError> {
        Ok(self.kernel.existential_reuse_disabled(predicate_id))
    }
}

impl ExpansionStateMutation for RuntimeExpansionState<'_> {
    type Checkpoint = TableauKernel;

    fn checkpoint(&self) -> Result<Self::Checkpoint, ExpansionError> {
        Ok(self.kernel.clone())
    }

    fn restore(&mut self, checkpoint: Self::Checkpoint) -> Result<(), ExpansionError> {
        self.kernel.restore_full_checkpoint(checkpoint);
        self.kernel.check_invariants().map_err(native_to_expansion)
    }

    fn pop_candidate(&mut self) -> Result<Option<Self::Node>, ExpansionError> {
        self.kernel
            .take_existential_candidate()
            .map_err(native_to_expansion)
    }

    fn enqueue_candidate(
        &mut self,
        node: Self::Node,
        priority: CandidatePriority,
    ) -> Result<(), ExpansionError> {
        self.kernel
            .enqueue_node(
                "existential_candidates",
                node,
                vec![
                    i64::from(priority.creation_id),
                    i64::from(priority.slot),
                    i64::from(priority.generation),
                ],
            )
            .map_err(native_to_expansion)
    }

    fn create_node(
        &mut self,
        kind: NodeKind,
        parent: Option<Self::Node>,
    ) -> Result<Self::Node, ExpansionError> {
        self.kernel
            .create_node(native_node_kind(kind), parent, false, None, None, None)
            .map_err(native_to_expansion)
    }

    fn mark_processed(
        &mut self,
        node: Self::Node,
        predicate_id: u32,
    ) -> Result<(), ExpansionError> {
        self.kernel
            .mark_existential(node, predicate_id, false)
            .map_err(native_to_expansion)
    }

    fn install_clash(&mut self, clash: ClashRecord) -> Result<(), ExpansionError> {
        self.kernel
            .install_clash(
                match clash.kind {
                    ClashKind::ImpossibleCardinality => "impossible_cardinality",
                    ClashKind::EmptyHead => "empty_head",
                    ClashKind::Other => "positive_negative_atom",
                }
                .to_owned(),
                native_dependency(&clash.dependency)?,
                clash.details,
                None,
            )
            .map(|_changed| ())
            .map_err(native_to_expansion)
    }

    fn push_reuse_branch(
        &mut self,
        root: Self::Node,
        predicate_id: u32,
        supports: Vec<DependencySet>,
        base_dependency: DependencySet,
    ) -> Result<BranchRecord, ExpansionError> {
        let supports = supports
            .iter()
            .map(native_dependency)
            .collect::<Result<Vec<_>, _>>()?;
        let level = self
            .kernel
            .push_existential_reuse_branch(
                root,
                predicate_id,
                supports,
                native_dependency(&base_dependency)?,
            )
            .map_err(native_to_expansion)?;
        self.branch(level)?.ok_or_else(|| {
            ExpansionError::invariant("created existential reuse branch is unavailable")
        })
    }

    fn advance_reuse_branch(
        &mut self,
        level: u32,
        learned_dependency: DependencySet,
    ) -> Result<Option<u32>, ExpansionError> {
        self.kernel
            .advance_branch(level, native_dependency(&learned_dependency)?)
            .map_err(native_to_expansion)
    }

    fn remove_reuse_branch(&mut self, level: u32) -> Result<(), ExpansionError> {
        self.kernel
            .remove_existential_reuse_branch(level)
            .map_err(native_to_expansion)
    }

    fn set_reuse_node(
        &mut self,
        filler_predicate_id: u32,
        node: Self::Node,
    ) -> Result<(), ExpansionError> {
        self.kernel
            .set_existential_reuse_node(filler_predicate_id, node)
            .map_err(native_to_expansion)
    }

    fn remove_reuse_node(&mut self, filler_predicate_id: u32) -> Result<(), ExpansionError> {
        self.kernel
            .remove_existential_reuse_node(filler_predicate_id)
            .map_err(native_to_expansion)
    }

    fn set_reuse_disabled(
        &mut self,
        predicate_id: u32,
        disabled: bool,
    ) -> Result<(), ExpansionError> {
        self.kernel
            .set_existential_reuse_disabled(predicate_id, disabled)
            .map_err(native_to_expansion)
    }
}

pub trait NativeDatatypeExpansion {
    fn values_known_different(
        &self,
        kernel: &TableauKernel,
        left: NodeHandle,
        right: NodeHandle,
    ) -> NativeResult<bool>;

    fn value_satisfies(
        &mut self,
        kernel: &TableauKernel,
        node: NodeHandle,
        predicate_id: u32,
        control: &dyn OperationControl,
    ) -> NativeResult<bool>;
}

/// Sound pre-WPR3 adapter: explicit inequality/range rows are handled by the
/// expansion kernel; no additional datatype consequence is invented.
#[derive(Clone, Copy, Debug, Default)]
pub struct AssertedOnlyDatatypes;

impl NativeDatatypeExpansion for AssertedOnlyDatatypes {
    fn values_known_different(
        &self,
        _kernel: &TableauKernel,
        _left: NodeHandle,
        _right: NodeHandle,
    ) -> NativeResult<bool> {
        Ok(false)
    }

    fn value_satisfies(
        &mut self,
        _kernel: &TableauKernel,
        _node: NodeHandle,
        _predicate_id: u32,
        control: &dyn OperationControl,
    ) -> NativeResult<bool> {
        control.poll()?;
        Ok(false)
    }
}

pub struct RuntimeExpansionAccess<'a, D> {
    engine: &'a mut RuleEngine,
    datatypes: &'a mut D,
    control: &'a dyn OperationControl,
}

impl<'a, D> RuntimeExpansionAccess<'a, D> {
    pub const fn new(
        engine: &'a mut RuleEngine,
        datatypes: &'a mut D,
        control: &'a dyn OperationControl,
    ) -> Self {
        Self {
            engine,
            datatypes,
            control,
        }
    }
}

impl<D: NativeDatatypeExpansion> ExpansionRuleAccess<RuntimeExpansionState<'_>>
    for RuntimeExpansionAccess<'_, D>
{
    fn dispatch_ground_atom(
        &mut self,
        state: &mut RuntimeExpansionState<'_>,
        atom: GroundAtom<NodeHandle>,
        dependency: DependencySet,
        core: bool,
    ) -> Result<bool, ExpansionError> {
        self.control.poll().map_err(native_to_expansion)?;
        self.engine
            .dispatch_ground_atom(
                state.kernel_mut(),
                NativeGroundAtom::new(atom.predicate_id, atom.arguments)
                    .map_err(native_to_expansion)?,
                native_dependency(&dependency)?,
                core,
                &[],
            )
            .map_err(native_to_expansion)
    }

    fn register_node(
        &mut self,
        state: &mut RuntimeExpansionState<'_>,
        node: NodeHandle,
        dependency: DependencySet,
    ) -> Result<(), ExpansionError> {
        self.control.poll().map_err(native_to_expansion)?;
        self.engine
            .register_node(state.kernel_mut(), node, native_dependency(&dependency)?)
            .map(|_changed| ())
            .map_err(native_to_expansion)
    }

    fn data_values_known_different(
        &self,
        state: &RuntimeExpansionState<'_>,
        left: NodeHandle,
        right: NodeHandle,
    ) -> Result<bool, ExpansionError> {
        self.datatypes
            .values_known_different(state.kernel(), left, right)
            .map_err(native_to_expansion)
    }

    fn data_value_satisfies<C: ExpansionControl>(
        &mut self,
        state: &RuntimeExpansionState<'_>,
        node: NodeHandle,
        predicate_id: u32,
        control: &mut C,
    ) -> Result<bool, ExpansionError> {
        control.poll()?;
        self.datatypes
            .value_satisfies(state.kernel(), node, predicate_id, self.control)
            .map_err(native_to_expansion)
    }
}

pub struct NativeExpansionControl<'a> {
    control: &'a dyn OperationControl,
}

impl<'a> NativeExpansionControl<'a> {
    #[must_use]
    pub const fn new(control: &'a dyn OperationControl) -> Self {
        Self { control }
    }
}

impl ExpansionControl for NativeExpansionControl<'_> {
    fn poll(&mut self) -> Result<(), ExpansionError> {
        self.control.poll().map_err(native_to_expansion)
    }
}

#[must_use]
pub fn expansion_to_native(error: ExpansionError) -> NativeError {
    let kind = match error.kind {
        ExpansionErrorKind::InvalidInput => NativeErrorKind::Wire,
        ExpansionErrorKind::Cancelled => NativeErrorKind::Cancelled,
        ExpansionErrorKind::Resource => NativeErrorKind::Resource,
        ExpansionErrorKind::Invariant => NativeErrorKind::Invariant,
    };
    let code = match error.kind {
        ExpansionErrorKind::InvalidInput => "NATIVE_EXPANSION_INVALID",
        ExpansionErrorKind::Cancelled => "NATIVE_EXPANSION_CANCELLED",
        ExpansionErrorKind::Resource => "RESOURCE_LIMIT",
        ExpansionErrorKind::Invariant => "NATIVE_EXPANSION_INVARIANT",
    };
    let mut mapped = NativeError::new(kind, code, error.message);
    if let Some(limit) = error.limit {
        mapped = mapped.with_context("limit", limit);
    }
    if let Some(observed) = error.observed {
        mapped = mapped.with_context("observed", observed.to_string());
    }
    if let Some(allowed) = error.allowed {
        mapped = mapped.with_context("allowed", allowed.to_string());
    }
    mapped
}

fn native_to_expansion(error: NativeError) -> ExpansionError {
    match error.kind {
        NativeErrorKind::Cancelled | NativeErrorKind::Timeout => {
            ExpansionError::cancelled(error.message)
        }
        NativeErrorKind::Resource => ExpansionError::resource(
            error.message,
            "native_resource",
            error
                .context
                .get("observed")
                .and_then(|value| value.parse().ok())
                .unwrap_or(0),
            error
                .context
                .get("allowed")
                .and_then(|value| value.parse().ok())
                .unwrap_or(0),
        ),
        NativeErrorKind::Invariant | NativeErrorKind::Poisoned => {
            ExpansionError::invariant(error.message)
        }
        _ => ExpansionError::invalid(error.message),
    }
}

fn expansion_dependency(value: &NativeDependencySet) -> Result<DependencySet, ExpansionError> {
    DependencySet::new(value.as_slice().to_vec())
}

fn native_dependency(value: &DependencySet) -> Result<NativeDependencySet, ExpansionError> {
    NativeDependencySet::new(value.as_slice().to_vec()).map_err(native_to_expansion)
}

const fn expansion_node_kind(value: NativeNodeKind) -> NodeKind {
    match value {
        NativeNodeKind::Root => NodeKind::Root,
        NativeNodeKind::Tree => NodeKind::Tree,
        NativeNodeKind::Ni => NodeKind::Ni,
        NativeNodeKind::Concrete => NodeKind::Concrete,
    }
}

const fn native_node_kind(value: NodeKind) -> NativeNodeKind {
    match value {
        NodeKind::Root => NativeNodeKind::Root,
        NodeKind::Tree => NativeNodeKind::Tree,
        NodeKind::Ni => NativeNodeKind::Ni,
        NodeKind::Concrete => NativeNodeKind::Concrete,
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;
    use crate::blocking::{
        select_blocking_plan, BlockingCacheNamespace, BlockingLimits, BlockingMode,
        BlockingProjection, BlockingRequirements, BlockingSignatureCache, BlockingVocabulary,
        CoreBlockingMode, DirectChecker, NeverCancel,
    };
    use crate::cancel::{CancellationHandle, CancellationState};
    use crate::existentials::{
        BranchTransition, ExistentialExpansionManager, ExpansionLimits, ExpansionStatus,
        ExpansionStrategy,
    };
    use crate::rules::RulePredicate;

    fn object_program(cardinality: u32) -> NativeResult<RuleProgram> {
        RuleProgram::new(
            vec![
                RulePredicate::new(0, PredicateKind::Concept, vec![TermSort::Object])?
                    .with_symbol_id(0),
                RulePredicate::new(
                    1,
                    PredicateKind::Inequality,
                    vec![TermSort::Object, TermSort::Object],
                )?,
                RulePredicate::new(
                    2,
                    PredicateKind::ObjectRole,
                    vec![TermSort::Object, TermSort::Object],
                )?
                .with_role_id(10),
                RulePredicate::new(3, PredicateKind::AtLeastObject, vec![TermSort::Object])?
                    .with_cardinality(cardinality, 10, 0),
            ],
            Vec::new(),
        )
    }

    const fn special_roles() -> SpecialRoleIds {
        SpecialRoleIds {
            top_object: 98,
            bottom_object: 99,
            top_data: 198,
            bottom_data: 199,
        }
    }

    fn cancellation() -> NativeResult<Arc<CancellationState>> {
        Ok(CancellationHandle::from_options(None, None)?.state())
    }

    #[test]
    fn real_kernel_creation_order_expands_and_marks_cardinality_processed() -> NativeResult<()> {
        let program = object_program(2)?;
        let expansion = expansion_program_from_rules(&program, special_roles(), &BTreeSet::new())
            .map_err(expansion_to_native)?;
        let manager = ExistentialExpansionManager::new(
            expansion,
            ExpansionStrategy::CreationOrder,
            ExpansionLimits::default(),
        )
        .map_err(expansion_to_native)?;
        let mut kernel = TableauKernel::new();
        let root = kernel.create_node(NativeNodeKind::Root, None, false, None, None, None)?;
        let mut engine = RuleEngine::new(program, BTreeMap::new(), BTreeMap::new(), true)?;
        engine.dispatch_ground_atom(
            &mut kernel,
            NativeGroundAtom::new(3, vec![root])?,
            NativeDependencySet::empty(),
            false,
            &[7],
        )?;
        let cancellation = cancellation()?;
        let mut datatypes = AssertedOnlyDatatypes;
        let mut state = RuntimeExpansionState::new(&mut kernel, None);
        let mut access =
            RuntimeExpansionAccess::new(&mut engine, &mut datatypes, cancellation.as_ref());
        let mut control = NativeExpansionControl::new(cancellation.as_ref());

        let result = manager
            .process_next(&mut state, &mut access, &mut control)
            .map_err(expansion_to_native)?;
        assert_eq!(result.status, ExpansionStatus::Expanded);
        assert_eq!(result.root, Some(root));
        assert_eq!(result.existential_id, Some(3));
        assert_eq!(result.witnesses.len(), 2);
        assert!(result.witnesses.iter().all(|witness| {
            state
                .kernel()
                .active_node(*witness)
                .is_ok_and(|node| node.kind == NativeNodeKind::Tree && node.parent == Some(root))
        }));
        assert!(state
            .kernel()
            .active_node(root)?
            .unprocessed_existentials
            .is_empty());
        assert_eq!(state.candidate_count().map_err(expansion_to_native)?, 0);
        assert_eq!(
            state
                .facts(
                    2,
                    &[FactBinding {
                        position: 0,
                        node: root
                    }]
                )
                .map_err(expansion_to_native)?
                .len(),
            2
        );
        assert_eq!(state.facts(0, &[]).map_err(expansion_to_native)?.len(), 2);
        assert_eq!(state.facts(1, &[]).map_err(expansion_to_native)?.len(), 1);
        state.kernel().check_invariants()
    }

    #[test]
    fn cache_owned_block_is_visible_without_a_live_kernel_blocker() -> NativeResult<()> {
        let mut kernel = TableauKernel::new();
        let root = kernel.create_node(NativeNodeKind::Root, None, false, None, None, None)?;
        let child =
            kernel.create_node(NativeNodeKind::Tree, Some(root), false, None, None, None)?;
        kernel.add_fact(0, vec![child], NativeDependencySet::empty(), false, None)?;
        let vocabulary = BlockingVocabulary::new([0], [])
            .map_err(|error| NativeError::invariant(error.to_string()))?;
        let plan = select_blocking_plan(BlockingMode::Anywhere, BlockingRequirements::default())
            .map_err(|error| NativeError::invariant(error.to_string()))?;
        let checker = DirectChecker::new(plan.direct_checker_kind, vocabulary.clone(), false)
            .map_err(|error| NativeError::invariant(error.to_string()))?;
        let projection = BlockingProjection::from_state(
            &kernel,
            &vocabulary,
            BlockingLimits::default(),
            &NeverCancel,
        )
        .map_err(|error| NativeError::invariant(error.to_string()))?;
        let signature = checker
            .signature(&projection, child)
            .map_err(|error| NativeError::invariant(error.to_string()))?;
        let namespace = BlockingCacheNamespace::new(
            "ontology",
            vocabulary.fingerprint(),
            plan.direct_checker_kind,
            CoreBlockingMode::None,
            "configuration",
        )
        .map_err(|error| NativeError::invariant(error.to_string()))?;
        let mut cache = BlockingSignatureCache::new(namespace, 8, 16_384)
            .map_err(|error| NativeError::invariant(error.to_string()))?;
        assert!(cache
            .add(signature)
            .map_err(|error| NativeError::invariant(error.to_string()))?);
        let mut blocking =
            BlockingManager::new(plan, checker, Some(cache), BlockingLimits::default(), 32)
                .map_err(|error| NativeError::invariant(error.to_string()))?;
        blocking
            .compute_unbounded(&kernel, false)
            .map_err(|error| NativeError::invariant(error.to_string()))?;
        assert!(blocking.is_blocked(child));
        assert_eq!(blocking.blocker(child), None);
        assert_eq!(kernel.active_node(child)?.blocker, None);

        let state = RuntimeExpansionState::new(&mut kernel, Some(&blocking));
        assert!(state.is_blocked(child).map_err(expansion_to_native)?);
        Ok(())
    }

    #[test]
    fn real_reuse_branch_rolls_back_ni_state_and_advances_to_fresh_witness() -> NativeResult<()> {
        let program = object_program(1)?;
        let expansion =
            expansion_program_from_rules(&program, special_roles(), &BTreeSet::from([0]))
                .map_err(expansion_to_native)?;
        let manager = ExistentialExpansionManager::new(
            expansion,
            ExpansionStrategy::IndividualReuse,
            ExpansionLimits::default(),
        )
        .map_err(expansion_to_native)?;
        let mut kernel = TableauKernel::new();
        let root = kernel.create_node(NativeNodeKind::Root, None, false, None, None, None)?;
        let mut engine = RuleEngine::new(program, BTreeMap::new(), BTreeMap::new(), true)?;
        engine.dispatch_ground_atom(
            &mut kernel,
            NativeGroundAtom::new(3, vec![root])?,
            NativeDependencySet::empty(),
            false,
            &[8],
        )?;
        let cancellation = cancellation()?;
        let mut datatypes = AssertedOnlyDatatypes;
        let mut state = RuntimeExpansionState::new(&mut kernel, None);
        let mut access =
            RuntimeExpansionAccess::new(&mut engine, &mut datatypes, cancellation.as_ref());
        let mut control = NativeExpansionControl::new(cancellation.as_ref());

        let first = manager
            .process_next(&mut state, &mut access, &mut control)
            .map_err(expansion_to_native)?;
        assert_eq!(first.status, ExpansionStatus::Expanded);
        assert_eq!(first.witnesses.len(), 1);
        assert_eq!(
            state
                .node_record(first.witnesses[0])
                .map_err(expansion_to_native)?
                .map(|record| record.kind),
            Some(NodeKind::Ni)
        );
        assert!(state
            .reuse_branch(0)
            .map_err(expansion_to_native)?
            .is_some());
        assert_eq!(
            state.reuse_node(0).map_err(expansion_to_native)?,
            first.witnesses.first().copied()
        );

        state
            .install_clash(ClashRecord {
                kind: ClashKind::Other,
                dependency: DependencySet::new(vec![0]).map_err(expansion_to_native)?,
                details: vec![90],
            })
            .map_err(expansion_to_native)?;
        assert_eq!(
            manager
                .resolve_clash(&mut state, &mut access, &mut control)
                .map_err(expansion_to_native)?,
            BranchTransition::Advanced
        );
        assert!(state.reuse_disabled(3).map_err(expansion_to_native)?);
        assert_eq!(state.reuse_node(0).map_err(expansion_to_native)?, None);
        assert!(state
            .active_nodes()
            .map_err(expansion_to_native)?
            .iter()
            .any(|record| record.kind == NodeKind::Tree && record.parent == Some(root)));
        assert!(state
            .active_nodes()
            .map_err(expansion_to_native)?
            .iter()
            .all(|record| record.kind != NodeKind::Ni));

        state
            .install_clash(ClashRecord {
                kind: ClashKind::Other,
                dependency: DependencySet::new(vec![0]).map_err(expansion_to_native)?,
                details: vec![91],
            })
            .map_err(expansion_to_native)?;
        assert_eq!(
            manager
                .resolve_clash(&mut state, &mut access, &mut control)
                .map_err(expansion_to_native)?,
            BranchTransition::Exhausted
        );
        assert!(state
            .reuse_branch(0)
            .map_err(expansion_to_native)?
            .is_none());
        assert_eq!(
            state
                .current_clash()
                .map_err(expansion_to_native)?
                .map(|clash| clash.kind),
            Some(ClashKind::EmptyHead)
        );
        state.kernel().check_invariants()
    }
}
