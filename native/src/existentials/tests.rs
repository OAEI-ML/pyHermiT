//! Colocated fake-state, generated differential, and transition tests.
// SPDX-License-Identifier: LGPL-3.0-or-later

use std::collections::{BTreeMap, BTreeSet};

use super::*;

const OBJECT_ROLE_ID: u32 = 100;
const DATA_ROLE_ID: u32 = 101;
const SECOND_DATA_ROLE_ID: u32 = 102;
const OBJECT_ROLE_PREDICATE: u32 = 20;
const DATA_ROLE_PREDICATE: u32 = 21;
const SECOND_DATA_ROLE_PREDICATE: u32 = 22;
const OBJECT_INEQUALITY: u32 = 30;
const DATA_INEQUALITY: u32 = 31;
const TOP_OBJECT_ROLE: u32 = 900;
const TOP_DATA_ROLE: u32 = 901;
const BOTTOM_OBJECT_ROLE: u32 = 910;
const BOTTOM_DATA_ROLE: u32 = 911;

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct FakeNode(u32);

#[derive(Clone, Debug, Eq, PartialEq)]
struct StoredNode {
    record: NodeRecord<FakeNode>,
    canonical: FakeNode,
    canonical_dependency: DependencySet,
    active: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct FakeTableauSnapshot {
    next_node: u32,
    next_row: u32,
    nodes: BTreeMap<FakeNode, StoredNode>,
    candidates: BTreeMap<CandidatePriority, FakeNode>,
    candidate_members: BTreeSet<FakeNode>,
    facts: Vec<FactRecord<FakeNode>>,
    clash: Option<ClashRecord>,
    kernel_blocked: BTreeSet<FakeNode>,
    manager_blocked: BTreeSet<FakeNode>,
    reuse_nodes: BTreeMap<u32, FakeNode>,
    reuse_disabled: BTreeSet<u32>,
    reuse_branches: BTreeMap<u32, ReuseBranchRecord<FakeNode>>,
    registrations: Vec<(FakeNode, DependencySet)>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct FakeBranch {
    record: BranchRecord,
    initial_base_dependency: DependencySet,
    next_alternative: usize,
    snapshot: FakeTableauSnapshot,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct FakeState {
    next_node: u32,
    next_row: u32,
    nodes: BTreeMap<FakeNode, StoredNode>,
    candidates: BTreeMap<CandidatePriority, FakeNode>,
    candidate_members: BTreeSet<FakeNode>,
    facts: Vec<FactRecord<FakeNode>>,
    clash: Option<ClashRecord>,
    kernel_blocked: BTreeSet<FakeNode>,
    manager_blocked: BTreeSet<FakeNode>,
    reuse_nodes: BTreeMap<u32, FakeNode>,
    reuse_disabled: BTreeSet<u32>,
    reuse_branches: BTreeMap<u32, ReuseBranchRecord<FakeNode>>,
    registrations: Vec<(FakeNode, DependencySet)>,
    branches: Vec<FakeBranch>,
}

impl FakeState {
    fn tableau_snapshot(&self) -> FakeTableauSnapshot {
        FakeTableauSnapshot {
            next_node: self.next_node,
            next_row: self.next_row,
            nodes: self.nodes.clone(),
            candidates: self.candidates.clone(),
            candidate_members: self.candidate_members.clone(),
            facts: self.facts.clone(),
            clash: self.clash.clone(),
            kernel_blocked: self.kernel_blocked.clone(),
            manager_blocked: self.manager_blocked.clone(),
            reuse_nodes: self.reuse_nodes.clone(),
            reuse_disabled: self.reuse_disabled.clone(),
            reuse_branches: self.reuse_branches.clone(),
            registrations: self.registrations.clone(),
        }
    }

    fn restore_tableau(&mut self, snapshot: FakeTableauSnapshot) {
        self.next_node = snapshot.next_node;
        self.next_row = snapshot.next_row;
        self.nodes = snapshot.nodes;
        self.candidates = snapshot.candidates;
        self.candidate_members = snapshot.candidate_members;
        self.facts = snapshot.facts;
        self.clash = snapshot.clash;
        self.kernel_blocked = snapshot.kernel_blocked;
        self.manager_blocked = snapshot.manager_blocked;
        self.reuse_nodes = snapshot.reuse_nodes;
        self.reuse_disabled = snapshot.reuse_disabled;
        self.reuse_branches = snapshot.reuse_branches;
        self.registrations = snapshot.registrations;
    }

    fn add_node(&mut self, kind: NodeKind, parent: Option<FakeNode>) -> FakeNode {
        let node = FakeNode(self.next_node);
        self.next_node += 1;
        let priority = CandidatePriority {
            creation_id: node.0,
            slot: node.0,
            generation: 1,
        };
        self.nodes.insert(
            node,
            StoredNode {
                record: NodeRecord {
                    node,
                    priority,
                    kind,
                    parent,
                    pending_existentials: BTreeSet::new(),
                },
                canonical: node,
                canonical_dependency: DependencySet::empty(),
                active: true,
            },
        );
        node
    }

    fn alias(&mut self, source: FakeNode, target: FakeNode, dependency: DependencySet) {
        if let Some(stored) = self.nodes.get_mut(&source) {
            stored.canonical = target;
            stored.canonical_dependency = dependency;
            stored.active = false;
        }
    }

    fn seed_obligation(
        &mut self,
        root: FakeNode,
        predicate_id: u32,
        dependency: DependencySet,
    ) -> Result<(), ExpansionError> {
        self.add_fact(
            GroundAtom {
                predicate_id,
                arguments: vec![root],
            },
            dependency,
            false,
        )?;
        let stored = self
            .nodes
            .get_mut(&root)
            .ok_or_else(|| ExpansionError::invariant("seed root is unavailable"))?;
        stored.record.pending_existentials.insert(predicate_id);
        let priority = stored.record.priority;
        self.enqueue_candidate(root, priority)
    }

    #[allow(clippy::unnecessary_wraps)]
    fn add_fact(
        &mut self,
        atom: GroundAtom<FakeNode>,
        dependency: DependencySet,
        core: bool,
    ) -> Result<bool, ExpansionError> {
        if let Some(row) = self
            .facts
            .iter_mut()
            .find(|row| row.predicate_id == atom.predicate_id && row.arguments == atom.arguments)
        {
            let support_changed = !row.supports.contains(&dependency);
            if support_changed {
                row.supports.push(dependency);
                row.supports.sort();
                row.supports.dedup();
            }
            let core_changed = core && !row.core;
            if core_changed {
                row.core = true;
            }
            return Ok(support_changed || core_changed);
        }
        let row_id = self.next_row;
        self.next_row += 1;
        self.facts.push(FactRecord {
            row_id,
            predicate_id: atom.predicate_id,
            arguments: atom.arguments,
            supports: vec![dependency],
            core,
        });
        Ok(true)
    }

    fn fact(&self, predicate_id: u32, arguments: &[FakeNode]) -> Option<&FactRecord<FakeNode>> {
        self.facts
            .iter()
            .find(|row| row.predicate_id == predicate_id && row.arguments.as_slice() == arguments)
    }

    fn pending(&self, node: FakeNode, predicate_id: u32) -> bool {
        self.nodes
            .get(&node)
            .is_some_and(|stored| stored.record.pending_existentials.contains(&predicate_id))
    }
}

impl ExpansionStateRead for FakeState {
    type Node = FakeNode;

    fn candidate_count(&self) -> Result<usize, ExpansionError> {
        Ok(self.candidates.len())
    }

    fn node_record(
        &self,
        node: Self::Node,
    ) -> Result<Option<NodeRecord<Self::Node>>, ExpansionError> {
        Ok(self
            .nodes
            .get(&node)
            .filter(|stored| stored.active)
            .map(|stored| stored.record.clone()))
    }

    fn canonical_node(
        &self,
        node: Self::Node,
    ) -> Result<Option<CanonicalNode<Self::Node>>, ExpansionError> {
        let Some(stored) = self.nodes.get(&node) else {
            return Ok(None);
        };
        let Some(representative) = self.nodes.get(&stored.canonical) else {
            return Ok(None);
        };
        if !representative.active {
            return Err(ExpansionError::invariant(
                "fake canonical chain is not flattened",
            ));
        }
        Ok(Some(CanonicalNode {
            node: stored.canonical,
            dependency: stored.canonical_dependency.clone(),
        }))
    }

    fn active_nodes(&self) -> Result<Vec<NodeRecord<Self::Node>>, ExpansionError> {
        let mut records = self
            .nodes
            .values()
            .filter(|stored| stored.active)
            .map(|stored| stored.record.clone())
            .collect::<Vec<_>>();
        records.sort_by_key(|record| (record.priority, record.node));
        Ok(records)
    }

    fn is_blocked(&self, node: Self::Node) -> Result<bool, ExpansionError> {
        Ok(self.kernel_blocked.contains(&node) || self.manager_blocked.contains(&node))
    }

    fn facts(
        &self,
        predicate_id: u32,
        bindings: &[FactBinding<Self::Node>],
    ) -> Result<Vec<FactRecord<Self::Node>>, ExpansionError> {
        let mut rows = Vec::new();
        'rows: for row in &self.facts {
            if row.predicate_id != predicate_id {
                continue;
            }
            for binding in bindings {
                let position = usize::try_from(binding.position).map_err(|_| {
                    ExpansionError::invariant("fake binding position cannot fit usize")
                })?;
                if row.arguments.get(position) != Some(&binding.node) {
                    continue 'rows;
                }
            }
            rows.push(row.clone());
        }
        rows.sort_by_key(|row| row.row_id);
        Ok(rows)
    }

    fn current_clash(&self) -> Result<Option<ClashRecord>, ExpansionError> {
        Ok(self.clash.clone())
    }

    fn branch(&self, level: u32) -> Result<Option<BranchRecord>, ExpansionError> {
        let index = usize::try_from(level)
            .map_err(|_| ExpansionError::invariant("fake branch level cannot fit usize"))?;
        Ok(self.branches.get(index).map(|branch| branch.record.clone()))
    }

    fn reuse_branch(
        &self,
        level: u32,
    ) -> Result<Option<ReuseBranchRecord<Self::Node>>, ExpansionError> {
        Ok(self.reuse_branches.get(&level).cloned())
    }

    fn reuse_node(&self, filler_predicate_id: u32) -> Result<Option<Self::Node>, ExpansionError> {
        Ok(self.reuse_nodes.get(&filler_predicate_id).copied())
    }

    fn reuse_disabled(&self, predicate_id: u32) -> Result<bool, ExpansionError> {
        Ok(self.reuse_disabled.contains(&predicate_id))
    }
}

impl ExpansionStateMutation for FakeState {
    type Checkpoint = Self;

    fn checkpoint(&self) -> Result<Self::Checkpoint, ExpansionError> {
        Ok(self.clone())
    }

    fn restore(&mut self, checkpoint: Self::Checkpoint) -> Result<(), ExpansionError> {
        *self = checkpoint;
        Ok(())
    }

    fn pop_candidate(&mut self) -> Result<Option<Self::Node>, ExpansionError> {
        let Some(priority) = self.candidates.keys().next().copied() else {
            return Ok(None);
        };
        let node = self
            .candidates
            .remove(&priority)
            .ok_or_else(|| ExpansionError::invariant("fake candidate disappeared"))?;
        self.candidate_members.remove(&node);
        Ok(Some(node))
    }

    fn enqueue_candidate(
        &mut self,
        node: Self::Node,
        priority: CandidatePriority,
    ) -> Result<(), ExpansionError> {
        if self.candidate_members.contains(&node) {
            return Ok(());
        }
        if self.candidates.insert(priority, node).is_some() {
            return Err(ExpansionError::invariant(
                "fake candidate priority is not unique",
            ));
        }
        self.candidate_members.insert(node);
        Ok(())
    }

    fn create_node(
        &mut self,
        kind: NodeKind,
        parent: Option<Self::Node>,
    ) -> Result<Self::Node, ExpansionError> {
        if kind == NodeKind::Tree && parent.is_none() {
            return Err(ExpansionError::invariant(
                "fake tree witness requires a parent",
            ));
        }
        if kind != NodeKind::Tree && parent.is_some() {
            return Err(ExpansionError::invariant(
                "fake non-tree witness cannot have a parent",
            ));
        }
        Ok(self.add_node(kind, parent))
    }

    fn mark_processed(
        &mut self,
        node: Self::Node,
        predicate_id: u32,
    ) -> Result<(), ExpansionError> {
        let stored = self
            .nodes
            .get_mut(&node)
            .ok_or_else(|| ExpansionError::invariant("fake processed node is unavailable"))?;
        stored.record.pending_existentials.remove(&predicate_id);
        Ok(())
    }

    fn install_clash(&mut self, clash: ClashRecord) -> Result<(), ExpansionError> {
        self.clash = Some(clash);
        Ok(())
    }

    fn push_reuse_branch(
        &mut self,
        root: Self::Node,
        predicate_id: u32,
        supports: Vec<DependencySet>,
        base_dependency: DependencySet,
    ) -> Result<BranchRecord, ExpansionError> {
        let level = u32::try_from(self.branches.len())
            .map_err(|_| ExpansionError::invariant("fake branch count exceeds u32"))?;
        if base_dependency
            .maximum()
            .is_some_and(|maximum| maximum >= level)
        {
            return Err(ExpansionError::invariant(
                "fake reuse dependency references a future branch",
            ));
        }
        let reuse_record = ReuseBranchRecord {
            level,
            root,
            predicate_id,
            supports,
        };
        if self.reuse_branches.insert(level, reuse_record).is_some() {
            return Err(ExpansionError::invariant(
                "fake reuse branch already exists",
            ));
        }
        let snapshot = self.tableau_snapshot();
        let record = BranchRecord {
            level,
            base_dependency: base_dependency.clone(),
            learned_dependency: DependencySet::empty(),
            current_alternative: 0,
        };
        self.branches.push(FakeBranch {
            record: record.clone(),
            initial_base_dependency: base_dependency,
            next_alternative: 0,
            snapshot,
        });
        Ok(record)
    }

    fn advance_reuse_branch(
        &mut self,
        level: u32,
        learned_dependency: DependencySet,
    ) -> Result<Option<u32>, ExpansionError> {
        let index = usize::try_from(level)
            .map_err(|_| ExpansionError::invariant("fake branch level cannot fit usize"))?;
        let previous = self
            .branches
            .get(index)
            .cloned()
            .ok_or_else(|| ExpansionError::invariant("fake reuse branch is unavailable"))?;
        self.restore_tableau(previous.snapshot);
        self.branches.truncate(index + 1);
        let branch = self
            .branches
            .get_mut(index)
            .ok_or_else(|| ExpansionError::invariant("fake reuse branch disappeared"))?;
        branch.record.base_dependency = branch.initial_base_dependency.clone();
        branch.record.learned_dependency =
            DependencySet::union(&[&branch.record.learned_dependency, &learned_dependency]);
        branch.next_alternative += 1;
        if branch.next_alternative >= 2 {
            self.branches.pop();
            return Ok(None);
        }
        branch.record.current_alternative = 1;
        Ok(Some(1))
    }

    fn remove_reuse_branch(&mut self, level: u32) -> Result<(), ExpansionError> {
        self.reuse_branches.remove(&level);
        Ok(())
    }

    fn set_reuse_node(
        &mut self,
        filler_predicate_id: u32,
        node: Self::Node,
    ) -> Result<(), ExpansionError> {
        if self.reuse_nodes.insert(filler_predicate_id, node).is_some() {
            return Err(ExpansionError::invariant(
                "fake reuse filler already has a node",
            ));
        }
        Ok(())
    }

    fn remove_reuse_node(&mut self, filler_predicate_id: u32) -> Result<(), ExpansionError> {
        self.reuse_nodes.remove(&filler_predicate_id);
        Ok(())
    }

    fn set_reuse_disabled(
        &mut self,
        predicate_id: u32,
        disabled: bool,
    ) -> Result<(), ExpansionError> {
        if disabled {
            self.reuse_disabled.insert(predicate_id);
        } else {
            self.reuse_disabled.remove(&predicate_id);
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct FakeAccess {
    fixed_differences: BTreeSet<(FakeNode, FakeNode)>,
    datatype_satisfactions: BTreeSet<(FakeNode, u32)>,
    bottom_fillers: BTreeSet<u32>,
}

impl FakeAccess {
    fn mark_fixed_difference(&mut self, left: FakeNode, right: FakeNode) {
        self.fixed_differences
            .insert(ordered_fake_pair(left, right));
    }
}

impl ExpansionRuleAccess<FakeState> for FakeAccess {
    fn dispatch_ground_atom(
        &mut self,
        state: &mut FakeState,
        atom: GroundAtom<FakeNode>,
        dependency: DependencySet,
        core: bool,
    ) -> Result<bool, ExpansionError> {
        let bottom = self.bottom_fillers.contains(&atom.predicate_id);
        let predicate_id = atom.predicate_id;
        let changed = state.add_fact(atom, dependency.clone(), core)?;
        if bottom {
            state.install_clash(ClashRecord {
                kind: ClashKind::Other,
                dependency,
                details: vec![predicate_id],
            })?;
        }
        Ok(changed)
    }

    fn register_node(
        &mut self,
        state: &mut FakeState,
        node: FakeNode,
        dependency: DependencySet,
    ) -> Result<(), ExpansionError> {
        state.registrations.push((node, dependency));
        Ok(())
    }

    fn data_values_known_different(
        &self,
        _state: &FakeState,
        left: FakeNode,
        right: FakeNode,
    ) -> Result<bool, ExpansionError> {
        Ok(self
            .fixed_differences
            .contains(&ordered_fake_pair(left, right)))
    }

    fn data_value_satisfies<C: ExpansionControl>(
        &mut self,
        _state: &FakeState,
        node: FakeNode,
        predicate_id: u32,
        control: &mut C,
    ) -> Result<bool, ExpansionError> {
        control.poll()?;
        Ok(self.datatype_satisfactions.contains(&(node, predicate_id)))
    }
}

#[derive(Clone, Debug, Default)]
struct CountingControl {
    polls: u64,
    work: u64,
    cancel_at_poll: Option<u64>,
}

impl CountingControl {
    const fn cancelling(cancel_at_poll: u64) -> Self {
        Self {
            polls: 0,
            work: 0,
            cancel_at_poll: Some(cancel_at_poll),
        }
    }
}

impl ExpansionControl for CountingControl {
    fn poll(&mut self) -> Result<(), ExpansionError> {
        self.polls += 1;
        if self
            .cancel_at_poll
            .is_some_and(|cancel_at| self.polls >= cancel_at)
        {
            return Err(ExpansionError::cancelled(
                "injected existential cancellation",
            ));
        }
        Ok(())
    }

    fn add_work(&mut self, amount: u64) -> Result<(), ExpansionError> {
        self.work = self
            .work
            .checked_add(amount)
            .ok_or_else(|| ExpansionError::invariant("fake work counter overflow"))?;
        Ok(())
    }
}

fn ordered_fake_pair(left: FakeNode, right: FakeNode) -> (FakeNode, FakeNode) {
    if left <= right {
        (left, right)
    } else {
        (right, left)
    }
}

fn roles() -> RoleVocabulary {
    RoleVocabulary {
        object_role_predicates: BTreeMap::from([(OBJECT_ROLE_ID, OBJECT_ROLE_PREDICATE)]),
        data_role_predicates: BTreeMap::from([
            (DATA_ROLE_ID, DATA_ROLE_PREDICATE),
            (SECOND_DATA_ROLE_ID, SECOND_DATA_ROLE_PREDICATE),
        ]),
        top_object_role_id: TOP_OBJECT_ROLE,
        bottom_object_role_id: BOTTOM_OBJECT_ROLE,
        top_data_role_id: TOP_DATA_ROLE,
        bottom_data_role_id: BOTTOM_DATA_ROLE,
        object_inequality_predicate_id: Some(OBJECT_INEQUALITY),
        data_inequality_predicate_id: Some(DATA_INEQUALITY),
    }
}

fn manager(
    obligations: Vec<AtLeastPredicate>,
    strategy: ExpansionStrategy,
) -> Result<ExistentialExpansionManager, ExpansionError> {
    ExistentialExpansionManager::new(
        ExpansionProgram::new(obligations, roles())?,
        strategy,
        ExpansionLimits::default(),
    )
}

fn dependency(levels: &[u32]) -> Result<DependencySet, ExpansionError> {
    DependencySet::new(levels.to_vec())
}

fn add_core_fact(
    state: &mut FakeState,
    predicate_id: u32,
    arguments: Vec<FakeNode>,
) -> Result<(), ExpansionError> {
    state.add_fact(
        GroundAtom {
            predicate_id,
            arguments,
        },
        DependencySet::empty(),
        true,
    )?;
    Ok(())
}

#[test]
fn creation_order_builds_core_object_witnesses_and_processes_once() -> Result<(), ExpansionError> {
    let predicate = AtLeastPredicate::object(0, 2, OBJECT_ROLE_ID, 10);
    let manager = manager(vec![predicate], ExpansionStrategy::CreationOrder)?;
    let mut state = FakeState::default();
    let root = state.add_node(NodeKind::Root, None);
    let support = dependency(&[])?;
    state.seed_obligation(root, 0, support.clone())?;
    let mut access = FakeAccess::default();
    let mut control = CountingControl::default();

    let result = manager.process_next(&mut state, &mut access, &mut control)?;
    assert_eq!(result.status, ExpansionStatus::Expanded);
    assert_eq!(result.root, Some(root));
    assert_eq!(result.existential_id, Some(0));
    assert_eq!(result.witnesses.len(), 2);
    assert!(!state.pending(root, 0));
    assert_eq!(state.candidate_count()?, 0);
    assert_eq!(state.registrations.len(), 2);

    for witness in &result.witnesses {
        let record = state
            .node_record(*witness)?
            .ok_or_else(|| ExpansionError::invariant("object witness is unavailable"))?;
        assert_eq!(record.kind, NodeKind::Tree);
        assert_eq!(record.parent, Some(root));
        let role = state
            .fact(OBJECT_ROLE_PREDICATE, &[root, *witness])
            .ok_or_else(|| ExpansionError::invariant("object witness role is absent"))?;
        let filler = state
            .fact(10, &[*witness])
            .ok_or_else(|| ExpansionError::invariant("object witness filler is absent"))?;
        assert!(role.core);
        assert!(filler.core);
        assert_eq!(role.supports, vec![support.clone()]);
        assert_eq!(filler.supports, vec![support.clone()]);
    }
    let inequality = state
        .fact(OBJECT_INEQUALITY, &result.witnesses)
        .ok_or_else(|| ExpansionError::invariant("object witness inequality is absent"))?;
    assert!(inequality.core);
    assert_eq!(inequality.supports, vec![support]);
    assert_eq!(
        manager
            .process_next(&mut state, &mut access, &mut control)?
            .status,
        ExpansionStatus::NoWork
    );
    Ok(())
}

#[test]
fn candidate_selection_is_stable_and_uses_coarse_blocking_state() -> Result<(), ExpansionError> {
    let manager = manager(
        vec![AtLeastPredicate::object(0, 1, OBJECT_ROLE_ID, 10)],
        ExpansionStrategy::CreationOrder,
    )?;
    let mut state = FakeState::default();
    let first = state.add_node(NodeKind::Root, None);
    let second = state.add_node(NodeKind::Root, None);
    state.seed_obligation(second, 0, DependencySet::empty())?;
    state.seed_obligation(first, 0, DependencySet::empty())?;
    // This block is intentionally manager-owned; no kernel blocker is present.
    state.manager_blocked.insert(first);
    let mut access = FakeAccess::default();
    let mut control = NeverCancel;

    let selected = manager.process_next(&mut state, &mut access, &mut control)?;
    assert_eq!(selected.root, Some(second));
    assert!(state.pending(first, 0));
    assert_eq!(
        manager
            .process_next(&mut state, &mut access, &mut control)?
            .status,
        ExpansionStatus::Blocked
    );
    assert_eq!(state.candidate_count()?, 1);

    state.manager_blocked.remove(&first);
    let resumed = manager.process_next(&mut state, &mut access, &mut control)?;
    assert_eq!(resumed.root, Some(first));
    assert_eq!(resumed.status, ExpansionStatus::Expanded);
    Ok(())
}

#[test]
fn object_satisfaction_uses_canonical_pairwise_distinct_subsets() -> Result<(), ExpansionError> {
    let predicate = AtLeastPredicate::object(0, 2, OBJECT_ROLE_ID, 10);
    let object_manager = manager(vec![predicate.clone()], ExpansionStrategy::CreationOrder)?;
    let mut state = FakeState::default();
    let root = state.add_node(NodeKind::Root, None);
    let first = state.add_node(NodeKind::Root, None);
    let second = state.add_node(NodeKind::Root, None);
    let third = state.add_node(NodeKind::Root, None);
    for target in [first, second, third] {
        add_core_fact(&mut state, OBJECT_ROLE_PREDICATE, vec![root, target])?;
        add_core_fact(&mut state, 10, vec![target])?;
    }
    // The first candidate is not known different from either later value; the
    // complete subset search must backtrack and find (second, third).
    add_core_fact(&mut state, OBJECT_INEQUALITY, vec![second, third])?;
    let mut access = FakeAccess::default();
    let mut control = CountingControl::default();
    assert!(object_manager.is_satisfied(&state, &mut access, &predicate, root, &mut control)?);
    assert!(control.work > 0);

    let mut merged = FakeState::default();
    let merged_root = merged.add_node(NodeKind::Root, None);
    let representative = merged.add_node(NodeKind::Root, None);
    let alias = merged.add_node(NodeKind::Root, None);
    add_core_fact(
        &mut merged,
        OBJECT_ROLE_PREDICATE,
        vec![merged_root, representative],
    )?;
    add_core_fact(&mut merged, OBJECT_ROLE_PREDICATE, vec![merged_root, alias])?;
    add_core_fact(&mut merged, 10, vec![representative])?;
    merged.alias(alias, representative, dependency(&[0])?);
    let mut merged_control = NeverCancel;
    assert!(!object_manager.is_satisfied(
        &merged,
        &mut access,
        &predicate,
        merged_root,
        &mut merged_control
    )?);
    Ok(())
}

#[test]
fn successor_filter_observes_cache_blocks_but_keeps_own_children() -> Result<(), ExpansionError> {
    let predicate = AtLeastPredicate::object(0, 1, OBJECT_ROLE_ID, 10);
    let manager = manager(vec![predicate.clone()], ExpansionStrategy::CreationOrder)?;
    let mut state = FakeState::default();
    let root = state.add_node(NodeKind::Root, None);
    let unrelated_parent = state.add_node(NodeKind::Root, None);
    let blocked_other = state.add_node(NodeKind::Tree, Some(unrelated_parent));
    add_core_fact(&mut state, OBJECT_ROLE_PREDICATE, vec![root, blocked_other])?;
    add_core_fact(&mut state, 10, vec![blocked_other])?;
    state.manager_blocked.insert(blocked_other);
    let mut access = FakeAccess::default();
    let mut control = NeverCancel;
    assert!(!manager.is_satisfied(&state, &mut access, &predicate, root, &mut control)?);

    let own_child = state.add_node(NodeKind::Tree, Some(root));
    add_core_fact(&mut state, OBJECT_ROLE_PREDICATE, vec![root, own_child])?;
    add_core_fact(&mut state, 10, vec![own_child])?;
    state.manager_blocked.insert(own_child);
    assert!(manager.is_satisfied(&state, &mut access, &predicate, root, &mut control)?);
    Ok(())
}

#[test]
fn unary_data_satisfaction_combines_datatype_and_fixed_value_semantics(
) -> Result<(), ExpansionError> {
    let predicate = AtLeastPredicate::data(1, 2, vec![DATA_ROLE_ID], 11);
    let data_manager = manager(vec![predicate.clone()], ExpansionStrategy::CreationOrder)?;
    let mut state = FakeState::default();
    let root = state.add_node(NodeKind::Root, None);
    let first = state.add_node(NodeKind::Concrete, None);
    let second = state.add_node(NodeKind::Concrete, None);
    for value in [first, second] {
        add_core_fact(&mut state, DATA_ROLE_PREDICATE, vec![root, value])?;
    }
    add_core_fact(&mut state, 11, vec![first])?;
    let mut access = FakeAccess::default();
    access.datatype_satisfactions.insert((second, 11));
    access.mark_fixed_difference(first, second);
    let mut control = NeverCancel;
    assert!(data_manager.is_satisfied(&state, &mut access, &predicate, root, &mut control)?);

    let top = AtLeastPredicate::data(2, 2, vec![TOP_DATA_ROLE], 11);
    let top_manager = manager(vec![top.clone()], ExpansionStrategy::CreationOrder)?;
    assert!(top_manager.is_satisfied(&state, &mut access, &top, root, &mut control)?);
    Ok(())
}

#[test]
fn nary_data_expansion_and_existing_tuple_satisfaction_are_exact() -> Result<(), ExpansionError> {
    let predicate = AtLeastPredicate::data(2, 1, vec![DATA_ROLE_ID, SECOND_DATA_ROLE_ID], 12);
    let manager = manager(vec![predicate.clone()], ExpansionStrategy::CreationOrder)?;
    let mut state = FakeState::default();
    let root = state.add_node(NodeKind::Root, None);
    state.seed_obligation(root, 2, DependencySet::empty())?;
    let mut access = FakeAccess::default();
    let mut control = NeverCancel;
    let expanded = manager.process_next(&mut state, &mut access, &mut control)?;
    assert_eq!(expanded.status, ExpansionStatus::Expanded);
    assert_eq!(expanded.witnesses.len(), 2);
    assert!(expanded.witnesses.iter().all(|node| state
        .node_record(*node)
        .ok()
        .flatten()
        .is_some_and(|record| record.kind == NodeKind::Concrete)));
    assert!(state
        .fact(DATA_ROLE_PREDICATE, &[root, expanded.witnesses[0]],)
        .is_some_and(|row| row.core));
    assert!(state
        .fact(SECOND_DATA_ROLE_PREDICATE, &[root, expanded.witnesses[1]],)
        .is_some_and(|row| row.core));
    assert!(state
        .fact(12, &expanded.witnesses)
        .is_some_and(|row| row.core));

    let mut existing = FakeState::default();
    let existing_root = existing.add_node(NodeKind::Root, None);
    let first = existing.add_node(NodeKind::Concrete, None);
    let second = existing.add_node(NodeKind::Concrete, None);
    add_core_fact(
        &mut existing,
        DATA_ROLE_PREDICATE,
        vec![existing_root, first],
    )?;
    add_core_fact(
        &mut existing,
        SECOND_DATA_ROLE_PREDICATE,
        vec![existing_root, second],
    )?;
    add_core_fact(&mut existing, 12, vec![first, second])?;
    assert!(manager.is_satisfied(
        &existing,
        &mut access,
        &predicate,
        existing_root,
        &mut control
    )?);
    Ok(())
}

#[test]
fn top_roles_avoid_materialization_and_bottom_roles_clash() -> Result<(), ExpansionError> {
    let top = AtLeastPredicate::object(0, 1, TOP_OBJECT_ROLE, 10);
    let top_manager = manager(vec![top], ExpansionStrategy::CreationOrder)?;
    let mut top_state = FakeState::default();
    let top_root = top_state.add_node(NodeKind::Root, None);
    top_state.seed_obligation(top_root, 0, DependencySet::empty())?;
    let mut access = FakeAccess::default();
    let mut control = NeverCancel;
    let top_result = top_manager.process_next(&mut top_state, &mut access, &mut control)?;
    assert_eq!(top_result.status, ExpansionStatus::Expanded);
    assert_eq!(top_result.witnesses.len(), 1);
    assert!(top_state.facts(OBJECT_ROLE_PREDICATE, &[])?.is_empty());
    assert!(top_state.fact(10, &top_result.witnesses).is_some());

    let bottom = AtLeastPredicate::object(1, 1, BOTTOM_OBJECT_ROLE, 10);
    let bottom_manager = manager(vec![bottom], ExpansionStrategy::CreationOrder)?;
    let mut bottom_state = FakeState::default();
    let bottom_root = bottom_state.add_node(NodeKind::Root, None);
    bottom_state.seed_obligation(bottom_root, 1, dependency(&[])?)?;
    let bottom_result =
        bottom_manager.process_next(&mut bottom_state, &mut access, &mut control)?;
    assert_eq!(bottom_result.status, ExpansionStatus::Clashed);
    assert!(bottom_result.witnesses.is_empty());
    assert!(bottom_state.pending(bottom_root, 1));
    assert_eq!(
        bottom_state.current_clash()?.map(|clash| clash.kind),
        Some(ClashKind::ImpossibleCardinality)
    );

    let bottom_nary = AtLeastPredicate::data(2, 1, vec![DATA_ROLE_ID, BOTTOM_DATA_ROLE], 12);
    let bottom_nary_manager = manager(vec![bottom_nary], ExpansionStrategy::CreationOrder)?;
    let mut bottom_nary_state = FakeState::default();
    let nary_root = bottom_nary_state.add_node(NodeKind::Root, None);
    bottom_nary_state.seed_obligation(nary_root, 2, DependencySet::empty())?;
    assert_eq!(
        bottom_nary_manager
            .process_next(&mut bottom_nary_state, &mut access, &mut control)?
            .status,
        ExpansionStatus::Clashed
    );
    Ok(())
}

#[test]
fn bottom_filler_clashes_through_normal_dispatch_consequences() -> Result<(), ExpansionError> {
    let manager = manager(
        vec![AtLeastPredicate::object(0, 1, OBJECT_ROLE_ID, 10)],
        ExpansionStrategy::CreationOrder,
    )?;
    let mut state = FakeState::default();
    let root = state.add_node(NodeKind::Root, None);
    state.seed_obligation(root, 0, DependencySet::empty())?;
    let mut access = FakeAccess::default();
    access.bottom_fillers.insert(10);
    let mut control = NeverCancel;
    let result = manager.process_next(&mut state, &mut access, &mut control)?;
    // Python reports the mutation batch as expanded; the dispatched bottom
    // filler installs the normal clash consumed by the scheduler next.
    assert_eq!(result.status, ExpansionStatus::Expanded);
    assert_eq!(
        state.current_clash()?.map(|clash| clash.kind),
        Some(ClashKind::Other)
    );
    Ok(())
}

#[test]
fn individual_reuse_shares_atomic_fillers_and_prefers_a_qualified_parent(
) -> Result<(), ExpansionError> {
    let reusable = AtLeastPredicate::object(0, 1, OBJECT_ROLE_ID, 10).with_reusable_filler(true);
    let manager = manager(vec![reusable], ExpansionStrategy::IndividualReuse)?;
    let mut state = FakeState::default();
    let first = state.add_node(NodeKind::Root, None);
    let second = state.add_node(NodeKind::Root, None);
    state.seed_obligation(first, 0, DependencySet::empty())?;
    state.seed_obligation(second, 0, DependencySet::empty())?;
    let mut access = FakeAccess::default();
    let mut control = NeverCancel;
    let first_result = manager.process_next(&mut state, &mut access, &mut control)?;
    let second_result = manager.process_next(&mut state, &mut access, &mut control)?;
    assert_eq!(first_result.witnesses, second_result.witnesses);
    let shared = first_result.witnesses[0];
    assert_eq!(
        state
            .node_record(shared)?
            .ok_or_else(|| ExpansionError::invariant("shared NI node is unavailable"))?
            .kind,
        NodeKind::Ni
    );
    assert_eq!(state.branches.len(), 2);
    assert!(manager.owns_branch(&state, 0)?);
    assert!(manager.owns_branch(&state, 1)?);

    let mut parent_state = FakeState::default();
    let parent = parent_state.add_node(NodeKind::Root, None);
    let child = parent_state.add_node(NodeKind::Tree, Some(parent));
    add_core_fact(&mut parent_state, 10, vec![parent])?;
    parent_state.seed_obligation(child, 0, DependencySet::empty())?;
    let parent_result = manager.process_next(&mut parent_state, &mut access, &mut control)?;
    assert_eq!(parent_result.witnesses, vec![parent]);
    assert!(parent_state.reuse_nodes.is_empty());
    Ok(())
}

#[test]
fn reuse_clash_advances_to_fresh_witness_then_propagates_exhaustion() -> Result<(), ExpansionError>
{
    let reusable = AtLeastPredicate::object(0, 1, OBJECT_ROLE_ID, 10).with_reusable_filler(true);
    let manager = manager(vec![reusable], ExpansionStrategy::IndividualReuse)?;
    let mut state = FakeState::default();
    let root = state.add_node(NodeKind::Root, None);
    state.seed_obligation(root, 0, DependencySet::empty())?;
    let mut access = FakeAccess::default();
    let mut control = NeverCancel;
    let reused = manager.process_next(&mut state, &mut access, &mut control)?;
    assert_eq!(
        state
            .node_record(reused.witnesses[0])?
            .ok_or_else(|| ExpansionError::invariant("reuse witness is unavailable"))?
            .kind,
        NodeKind::Ni
    );
    state.install_clash(ClashRecord {
        kind: ClashKind::Other,
        dependency: dependency(&[0])?,
        details: vec![77],
    })?;
    assert_eq!(
        manager.resolve_clash(&mut state, &mut access, &mut control)?,
        BranchTransition::Advanced
    );
    assert!(state.current_clash()?.is_none());
    assert!(state.reuse_disabled.contains(&0));
    assert!(state.reuse_nodes.is_empty());
    let fresh = state
        .active_nodes()?
        .into_iter()
        .max_by_key(|record| record.priority)
        .ok_or_else(|| ExpansionError::invariant("fresh fallback witness is absent"))?;
    assert_eq!(fresh.kind, NodeKind::Tree);
    assert_eq!(fresh.parent, Some(root));
    assert!(state
        .fact(OBJECT_ROLE_PREDICATE, &[root, fresh.node])
        .is_some());
    assert_eq!(
        state
            .fact(10, &[fresh.node])
            .ok_or_else(|| ExpansionError::invariant("fallback filler is absent"))?
            .supports,
        vec![dependency(&[0])?]
    );

    state.install_clash(ClashRecord {
        kind: ClashKind::Other,
        dependency: dependency(&[0])?,
        details: vec![78],
    })?;
    assert_eq!(
        manager.resolve_clash(&mut state, &mut access, &mut control)?,
        BranchTransition::Exhausted
    );
    let propagated = state
        .current_clash()?
        .ok_or_else(|| ExpansionError::invariant("exhausted clash is absent"))?;
    assert_eq!(propagated.kind, ClashKind::EmptyHead);
    assert_eq!(propagated.dependency, DependencySet::empty());
    assert!(!manager.owns_branch(&state, 0)?);
    Ok(())
}

#[test]
fn resource_and_cancellation_failures_restore_the_exact_checkpoint() -> Result<(), ExpansionError> {
    let predicate = AtLeastPredicate::object(0, 2, OBJECT_ROLE_ID, 10);
    let limited = ExistentialExpansionManager::new(
        ExpansionProgram::new(vec![predicate.clone()], roles())?,
        ExpansionStrategy::CreationOrder,
        ExpansionLimits::new(1, 100, 2)?,
    )?;
    let mut limited_state = FakeState::default();
    let limited_root = limited_state.add_node(NodeKind::Root, None);
    limited_state.seed_obligation(limited_root, 0, DependencySet::empty())?;
    let limited_before = limited_state.clone();
    let mut access = FakeAccess::default();
    let mut control = NeverCancel;
    let limit_error = limited
        .process_next(&mut limited_state, &mut access, &mut control)
        .err()
        .ok_or_else(|| ExpansionError::invariant("witness limit did not fail"))?;
    assert_eq!(limit_error.kind, ExpansionErrorKind::Resource);
    assert_eq!(limit_error.limit, Some("max_witnesses_per_obligation"));
    assert_eq!(limited_state, limited_before);

    let creation_manager = manager(vec![predicate], ExpansionStrategy::CreationOrder)?;
    let mut cancelled_state = FakeState::default();
    let cancelled_root = cancelled_state.add_node(NodeKind::Root, None);
    cancelled_state.seed_obligation(cancelled_root, 0, DependencySet::empty())?;
    let cancelled_before = cancelled_state.clone();
    let mut cancellation = CountingControl::cancelling(5);
    let cancelled = creation_manager
        .process_next(&mut cancelled_state, &mut access, &mut cancellation)
        .err()
        .ok_or_else(|| ExpansionError::invariant("injected cancellation did not fire"))?;
    assert_eq!(cancelled.kind, ExpansionErrorKind::Cancelled);
    assert_eq!(cancelled_state, cancelled_before);

    let reusable = AtLeastPredicate::object(3, 1, OBJECT_ROLE_ID, 10).with_reusable_filler(true);
    let reuse_manager = manager(vec![reusable], ExpansionStrategy::IndividualReuse)?;
    let mut reuse_state = FakeState::default();
    let reuse_root = reuse_state.add_node(NodeKind::Root, None);
    reuse_state.seed_obligation(reuse_root, 3, DependencySet::empty())?;
    let reuse_before = reuse_state.clone();
    let mut reuse_cancellation = CountingControl::cancelling(4);
    let reuse_error = reuse_manager
        .process_next(&mut reuse_state, &mut access, &mut reuse_cancellation)
        .err()
        .ok_or_else(|| ExpansionError::invariant("reuse cancellation did not fire"))?;
    assert_eq!(reuse_error.kind, ExpansionErrorKind::Cancelled);
    assert_eq!(reuse_state, reuse_before);
    Ok(())
}

#[test]
fn unary_data_expansion_adds_role_filler_and_pairwise_inequality() -> Result<(), ExpansionError> {
    let predicate = AtLeastPredicate::data(1, 2, vec![DATA_ROLE_ID], 11);
    let data_manager = manager(vec![predicate], ExpansionStrategy::CreationOrder)?;
    let mut state = FakeState::default();
    let root = state.add_node(NodeKind::Root, None);
    let support = dependency(&[])?;
    state.seed_obligation(root, 1, support.clone())?;
    let mut access = FakeAccess::default();
    let mut control = NeverCancel;
    let result = data_manager.process_next(&mut state, &mut access, &mut control)?;
    assert_eq!(result.status, ExpansionStatus::Expanded);
    assert_eq!(result.witnesses.len(), 2);
    for witness in &result.witnesses {
        assert!(state
            .fact(DATA_ROLE_PREDICATE, &[root, *witness])
            .is_some_and(|row| row.core));
        assert!(state.fact(11, &[*witness]).is_some_and(|row| row.core));
    }
    assert!(state
        .fact(DATA_INEQUALITY, &result.witnesses)
        .is_some_and(|row| row.core && row.supports == vec![support]));
    Ok(())
}

#[test]
fn compiled_inverse_role_keeps_root_target_direction() -> Result<(), ExpansionError> {
    let inverse_role_id = 103;
    let inverse_role_predicate = 23;
    let mut vocabulary = roles();
    vocabulary
        .object_role_predicates
        .insert(inverse_role_id, inverse_role_predicate);
    let predicate = AtLeastPredicate::object(4, 1, inverse_role_id, 10);
    let inverse_manager = ExistentialExpansionManager::new(
        ExpansionProgram::new(vec![predicate], vocabulary)?,
        ExpansionStrategy::CreationOrder,
        ExpansionLimits::default(),
    )?;
    let mut state = FakeState::default();
    let root = state.add_node(NodeKind::Root, None);
    state.seed_obligation(root, 4, DependencySet::empty())?;
    let mut access = FakeAccess::default();
    let mut control = NeverCancel;
    let result = inverse_manager.process_next(&mut state, &mut access, &mut control)?;
    let witness = result.witnesses[0];
    assert!(state
        .fact(inverse_role_predicate, &[root, witness])
        .is_some());
    assert!(state
        .fact(inverse_role_predicate, &[witness, root])
        .is_none());
    Ok(())
}

#[test]
fn distinct_primitive_matches_generated_bruteforce_reference() -> Result<(), ExpansionError> {
    let mut seed = 0x05ee_dcaf_ed15_ca11_u64;
    for _case in 0..512 {
        seed = next_random(seed);
        let size = usize::try_from(seed % 7 + 1)
            .map_err(|_| ExpansionError::invariant("generated size cannot fit usize"))?;
        seed = next_random(seed);
        let cardinality = usize::try_from(seed % u64_from_usize(size + 1)?)
            .map_err(|_| ExpansionError::invariant("generated cardinality cannot fit usize"))?;
        let mut matrix = vec![false; size * size];
        for left in 0..size {
            for right in (left + 1)..size {
                seed = next_random(seed);
                let different = seed & 1 == 1;
                matrix[left * size + right] = different;
                matrix[right * size + left] = different;
            }
        }
        let candidates = (0..size).collect::<Vec<_>>();
        let expected = brute_distinct_exists(&candidates, cardinality, |left, right| {
            matrix[*left * size + *right]
        });
        let mut control = CountingControl::default();
        let actual = pairwise_distinct_subset(
            &candidates,
            cardinality,
            ExpansionLimits::default(),
            &mut control,
            |left, right| Ok(matrix[*left * size + *right]),
        )?;
        assert_eq!(actual.satisfied, expected);
        assert_eq!(actual.steps, control.work);
        if actual.satisfied {
            assert_eq!(actual.selected_indices.len(), cardinality);
            assert!(actual
                .selected_indices
                .windows(2)
                .all(|pair| pair[0] < pair[1]));
            for left in 0..actual.selected_indices.len() {
                for right in (left + 1)..actual.selected_indices.len() {
                    assert!(
                        matrix
                            [actual.selected_indices[left] * size + actual.selected_indices[right]]
                    );
                }
            }
        }
    }

    let candidates = [0_u32, 1, 2, 3];
    let mut control = NeverCancel;
    let limited = pairwise_distinct_subset(
        &candidates,
        3,
        ExpansionLimits::new(10, 1, 1)?,
        &mut control,
        |_left, _right| Ok(false),
    )
    .err()
    .ok_or_else(|| ExpansionError::invariant("distinct-search limit did not fail"))?;
    assert_eq!(limited.kind, ExpansionErrorKind::Resource);
    assert_eq!(limited.limit, Some("max_distinct_search_steps"));
    Ok(())
}

#[test]
fn generated_object_satisfaction_matches_reference_enumeration() -> Result<(), ExpansionError> {
    let mut seed = 0xdec0_de01_5eed_f00du64;
    for case in 0..192_u32 {
        seed = next_random(seed);
        let size = usize::try_from(seed % 6 + 1)
            .map_err(|_| ExpansionError::invariant("generated size cannot fit usize"))?;
        seed = next_random(seed);
        let cardinality = u32::try_from(seed % 5)
            .map_err(|_| ExpansionError::invariant("generated cardinality exceeds u32"))?;
        let predicate = AtLeastPredicate::object(case, cardinality, OBJECT_ROLE_ID, 10);
        let generated_manager = manager(vec![predicate.clone()], ExpansionStrategy::CreationOrder)?;
        let mut state = FakeState::default();
        let root = state.add_node(NodeKind::Root, None);
        let mut eligible = Vec::new();
        for _ in 0..size {
            let target = state.add_node(NodeKind::Root, None);
            seed = next_random(seed);
            let has_role = seed & 1 == 1;
            seed = next_random(seed);
            let has_filler = seed & 1 == 1;
            if has_role {
                add_core_fact(&mut state, OBJECT_ROLE_PREDICATE, vec![root, target])?;
            }
            if has_filler {
                add_core_fact(&mut state, 10, vec![target])?;
            }
            if has_role && has_filler {
                eligible.push(target);
            }
        }
        let mut differences = BTreeSet::new();
        let all_nodes = state
            .active_nodes()?
            .into_iter()
            .filter(|record| record.node != root)
            .map(|record| record.node)
            .collect::<Vec<_>>();
        for left in 0..all_nodes.len() {
            for right in (left + 1)..all_nodes.len() {
                seed = next_random(seed);
                if seed & 1 == 1 {
                    let pair = ordered_fake_pair(all_nodes[left], all_nodes[right]);
                    differences.insert(pair);
                    add_core_fact(&mut state, OBJECT_INEQUALITY, vec![pair.0, pair.1])?;
                }
            }
        }
        let expected = brute_distinct_exists(
            &eligible,
            usize_from_u32_test(cardinality)?,
            |left, right| differences.contains(&ordered_fake_pair(*left, *right)),
        );
        let mut access = FakeAccess::default();
        let mut control = NeverCancel;
        let actual =
            generated_manager.is_satisfied(&state, &mut access, &predicate, root, &mut control)?;
        assert_eq!(actual, expected, "generated differential case {case}");
    }
    Ok(())
}

fn next_random(value: u64) -> u64 {
    value
        .wrapping_mul(6_364_136_223_846_793_005)
        .wrapping_add(1_442_695_040_888_963_407)
}

fn brute_distinct_exists<T, F>(candidates: &[T], cardinality: usize, different: F) -> bool
where
    F: Fn(&T, &T) -> bool,
{
    if cardinality == 0 {
        return true;
    }
    if cardinality > candidates.len() || candidates.len() >= u64::BITS as usize {
        return false;
    }
    let upper = 1_u64 << candidates.len();
    for mask in 0..upper {
        if mask.count_ones() as usize != cardinality {
            continue;
        }
        let selected = (0..candidates.len())
            .filter(|index| mask & (1_u64 << index) != 0)
            .collect::<Vec<_>>();
        let mut pairwise = true;
        for left in 0..selected.len() {
            for right in (left + 1)..selected.len() {
                if !different(&candidates[selected[left]], &candidates[selected[right]]) {
                    pairwise = false;
                    break;
                }
            }
            if !pairwise {
                break;
            }
        }
        if pairwise {
            return true;
        }
    }
    false
}

fn usize_from_u32_test(value: u32) -> Result<usize, ExpansionError> {
    usize::try_from(value)
        .map_err(|_| ExpansionError::invariant("test cardinality cannot fit usize"))
}

fn u64_from_usize(value: usize) -> Result<u64, ExpansionError> {
    u64::try_from(value).map_err(|_| ExpansionError::invariant("test size cannot fit u64"))
}
