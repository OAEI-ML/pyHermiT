//! Generation-safe arenas, unique rows, deterministic queues, checkpoints, and invariants.
// SPDX-License-Identifier: LGPL-3.0-or-later

use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};

use serde_json::{json, Value};

use crate::error::{NativeError, NativeResult};
use crate::model::{DependencySet, NodeHandle, NodeKind, NodeLifecycle, NodeSort};

#[derive(Clone, Debug)]
pub(crate) struct Node {
    pub(crate) handle: NodeHandle,
    pub(crate) creation_id: u32,
    pub(crate) kind: NodeKind,
    pub(crate) sort: NodeSort,
    pub(crate) lifecycle: NodeLifecycle,
    pub(crate) parent: Option<NodeHandle>,
    pub(crate) tree_depth: u32,
    pub(crate) creation_checkpoint: u32,
    pub(crate) is_owl_named_individual: bool,
    pub(crate) source_individual_id: Option<u32>,
    pub(crate) representative: Option<NodeHandle>,
    pub(crate) merge_dependency: DependencySet,
    pub(crate) blocker: Option<NodeHandle>,
    pub(crate) directly_blocked: bool,
    pub(crate) blocking_generation: u32,
    pub(crate) unprocessed_existentials: BTreeSet<u32>,
    pub(crate) nominal_level: Option<u32>,
    pub(crate) cardinality_tag: Option<u32>,
}

impl Node {
    fn logical_value(&self) -> Value {
        json!({
            "blocker": self.blocker.map(handle_value),
            "blocking_generation": self.blocking_generation,
            "cardinality_tag": self.cardinality_tag,
            "creation_id": self.creation_id,
            "directly_blocked": self.directly_blocked,
            "existentials": self.unprocessed_existentials.iter().copied().collect::<Vec<_>>(),
            "handle": handle_value(self.handle),
            "is_owl_named_individual": self.is_owl_named_individual,
            "kind": self.kind.to_string(),
            "lifecycle": lifecycle_name(self.lifecycle),
            "merge_dependency": self.merge_dependency.as_slice(),
            "nominal_level": self.nominal_level,
            "parent": self.parent.map(handle_value),
            "representative": self.representative.map(handle_value),
            "sort": sort_name(self.sort),
            "source_individual_id": self.source_individual_id,
            "tree_depth": self.tree_depth,
        })
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct FactKey {
    pub(crate) predicate_id: u32,
    pub(crate) arguments: Vec<NodeHandle>,
}

#[derive(Clone, Debug)]
pub(crate) struct FactRow {
    pub(crate) row_id: u32,
    pub(crate) key: FactKey,
    pub(crate) supports: Vec<DependencySet>,
    pub(crate) core: bool,
    pub(crate) active: bool,
    pub(crate) derivation_generation: u32,
    pub(crate) provenance_ids: BTreeSet<u32>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct FactAddOutcome {
    pub(crate) row_id: u32,
    pub(crate) created: bool,
    pub(crate) support_changed: bool,
}

impl FactRow {
    pub(crate) fn minimal_dependency(&self) -> NativeResult<&DependencySet> {
        self.supports
            .iter()
            .min_by(|left, right| dependency_rank(left).cmp(&dependency_rank(right)))
            .ok_or_else(|| NativeError::invariant("active fact row has no support"))
    }

    fn logical_value(&self) -> Value {
        json!({
            "arguments": self.key.arguments.iter().copied().map(handle_value).collect::<Vec<_>>(),
            "core": self.core,
            "generation": self.derivation_generation,
            "predicate_id": self.key.predicate_id,
            "provenance_ids": self.provenance_ids.iter().copied().collect::<Vec<_>>(),
            "row_id": self.row_id,
            "supports": self.supports.iter().map(DependencySet::as_slice).collect::<Vec<_>>(),
        })
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum QueueValue {
    Integer(u32),
    Node(NodeHandle),
}

#[derive(Clone, Debug, Default)]
struct StableQueue {
    entries: BTreeMap<Vec<i64>, QueueValue>,
    members: BTreeSet<QueueValue>,
}

impl StableQueue {
    fn enqueue(&mut self, value: QueueValue, priority: Vec<i64>) -> NativeResult<bool> {
        if self.members.contains(&value) {
            return Ok(false);
        }
        if self.entries.contains_key(&priority) {
            return Err(NativeError::wire(
                "queue priorities must uniquely include a stable identifier",
            ));
        }
        self.members.insert(value.clone());
        self.entries.insert(priority, value);
        Ok(true)
    }

    fn pop(&mut self) -> Option<QueueValue> {
        let priority = self.entries.keys().next()?.clone();
        let value = self.entries.remove(&priority)?;
        self.members.remove(&value);
        Some(value)
    }

    fn values(&self) -> impl Iterator<Item = &QueueValue> {
        self.entries.values()
    }

    fn check_invariants(&self) -> NativeResult<()> {
        let values: BTreeSet<_> = self.entries.values().cloned().collect();
        if values.len() != self.entries.len() || values != self.members {
            return Err(NativeError::invariant(
                "queue priorities and membership are inconsistent",
            ));
        }
        Ok(())
    }
}

#[derive(Clone, Debug)]
pub(crate) struct GroundDisjunction {
    pub(crate) disjunction_id: u32,
    pub(crate) disjunct_ids: Vec<u32>,
    pub(crate) base_dependency: DependencySet,
    pub(crate) creation_checkpoint: u32,
    pub(crate) active: bool,
    pub(crate) processed: bool,
}

impl GroundDisjunction {
    fn logical_value(&self) -> Value {
        json!({
            "active": self.active,
            "base_dependency": self.base_dependency.as_slice(),
            "creation_checkpoint": self.creation_checkpoint,
            "disjunct_ids": self.disjunct_ids,
            "disjunction_id": self.disjunction_id,
            "processed": self.processed,
        })
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Clash {
    pub(crate) kind: String,
    pub(crate) dependency: DependencySet,
    pub(crate) participants: Vec<u32>,
    pub(crate) provenance_id: Option<u32>,
}

impl Clash {
    fn logical_value(&self) -> Value {
        json!({
            "dependency": self.dependency.as_slice(),
            "kind": self.kind,
            "participants": self.participants,
            "provenance_id": self.provenance_id,
        })
    }
}

#[derive(Clone, Debug)]
struct MutableState {
    nodes: Vec<Option<Node>>,
    generations: Vec<u32>,
    free_slots: BTreeSet<u32>,
    next_creation_id: u32,
    facts: Vec<FactRow>,
    facts_by_key: BTreeMap<FactKey, u32>,
    facts_by_node: BTreeMap<NodeHandle, BTreeSet<u32>>,
    facts_by_predicate: BTreeMap<u32, BTreeSet<u32>>,
    facts_by_position: BTreeMap<(u32, u32, NodeHandle), BTreeSet<u32>>,
    read_generation: u32,
    write_generation: u32,
    disjunctions: Vec<GroundDisjunction>,
    clash: Option<Clash>,
    delta_rows: StableQueue,
    annotated_equalities: StableQueue,
    existential_candidates: StableQueue,
    disjunction_queue: StableQueue,
    datatype_components: StableQueue,
    blocking_invalidations: StableQueue,
}

impl MutableState {
    fn new() -> Self {
        Self {
            nodes: Vec::new(),
            generations: Vec::new(),
            free_slots: BTreeSet::new(),
            next_creation_id: 0,
            facts: Vec::new(),
            facts_by_key: BTreeMap::new(),
            facts_by_node: BTreeMap::new(),
            facts_by_predicate: BTreeMap::new(),
            facts_by_position: BTreeMap::new(),
            read_generation: 0,
            write_generation: 0,
            disjunctions: Vec::new(),
            clash: None,
            delta_rows: StableQueue::default(),
            annotated_equalities: StableQueue::default(),
            existential_candidates: StableQueue::default(),
            disjunction_queue: StableQueue::default(),
            datatype_components: StableQueue::default(),
            blocking_invalidations: StableQueue::default(),
        }
    }
}

#[derive(Clone, Debug)]
struct StateCheckpoint {
    state: MutableState,
    trail_length: u64,
}

#[derive(Clone, Debug)]
struct CheckpointMeta {
    sequence: u64,
    trail_length: u64,
    label: String,
}

impl CheckpointMeta {
    fn logical_value(&self) -> Value {
        json!({
            "label": self.label,
            "sequence": self.sequence,
            "trail_length": self.trail_length,
        })
    }
}

#[derive(Clone, Debug)]
pub(crate) struct Branch {
    pub(crate) level: u32,
    pub(crate) choice_kind: String,
    checkpoint: CheckpointMeta,
    snapshot: StateCheckpoint,
    pub(crate) alternatives: Vec<u32>,
    pub(crate) source_id: u32,
    pub(crate) base_dependency: DependencySet,
    pub(crate) initial_base_dependency: DependencySet,
    pub(crate) next_alternative: usize,
    pub(crate) learned_dependency: DependencySet,
}

impl Branch {
    fn logical_value(&self) -> Value {
        json!({
            "alternatives": self.alternatives,
            "base_dependency": self.base_dependency.as_slice(),
            "checkpoint": self.checkpoint.logical_value(),
            "choice_kind": self.choice_kind,
            "learned_dependency": self.learned_dependency.as_slice(),
            "level": self.level,
            "next_alternative": self.next_alternative,
            "source_id": self.source_id,
        })
    }
}

/// Pure-Rust mutable state for one ontology/query pair.
#[derive(Clone, Debug)]
pub struct TableauKernel {
    state: MutableState,
    branches: Vec<Branch>,
    operation_root: StateCheckpoint,
    trail_length: u64,
    checkpoint_sequence: u64,
}

impl Default for TableauKernel {
    fn default() -> Self {
        Self::new()
    }
}

impl TableauKernel {
    #[must_use]
    pub fn new() -> Self {
        let state = MutableState::new();
        Self {
            operation_root: StateCheckpoint {
                state: state.clone(),
                trail_length: 0,
            },
            state,
            branches: Vec::new(),
            trail_length: 0,
            checkpoint_sequence: 1,
        }
    }

    pub fn begin_operation(&mut self) -> NativeResult<()> {
        if !self.branches.is_empty() {
            return Err(NativeError::wire(
                "cannot replace the operation root while branches survive",
            ));
        }
        self.checkpoint_sequence = self
            .checkpoint_sequence
            .checked_add(1)
            .ok_or_else(|| NativeError::invariant("checkpoint sequence overflow"))?;
        self.operation_root = self.snapshot();
        Ok(())
    }

    /// Execute one compound semantic mutation atomically. This is deliberately
    /// crate-private: public callers use the coarse reasoner operation boundary,
    /// while merge/expansion/blocking managers share this exact rollback primitive.
    pub(crate) fn atomic<T>(
        &mut self,
        operation: impl FnOnce(&mut Self) -> NativeResult<T>,
    ) -> NativeResult<T> {
        let checkpoint = self.snapshot();
        match operation(self) {
            Ok(value) => Ok(value),
            Err(error) => {
                self.restore(checkpoint);
                Err(error)
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub fn create_node(
        &mut self,
        kind: NodeKind,
        parent: Option<NodeHandle>,
        is_owl_named_individual: bool,
        source_individual_id: Option<u32>,
        nominal_level: Option<u32>,
        cardinality_tag: Option<u32>,
    ) -> NativeResult<NodeHandle> {
        let sort = kind.sort();
        let tree_depth = if kind == NodeKind::Tree {
            let parent = parent.ok_or_else(|| NativeError::wire("tree nodes require a parent"))?;
            let parent_node = self.require_active(parent)?;
            if parent_node.sort != NodeSort::Object {
                return Err(NativeError::wire("tree node parent must have object sort"));
            }
            parent_node
                .tree_depth
                .checked_add(1)
                .ok_or_else(|| NativeError::invariant("tree depth overflow"))?
        } else {
            if parent.is_some() {
                return Err(NativeError::wire(
                    "root, NI, and concrete nodes cannot have a parent",
                ));
            }
            0
        };
        if is_owl_named_individual && (kind != NodeKind::Root || source_individual_id.is_none()) {
            return Err(NativeError::wire(
                "only source named-individual roots may carry the named guard",
            ));
        }
        let slot = if let Some(slot) = self.state.free_slots.pop_first() {
            slot
        } else {
            let slot = u32::try_from(self.state.nodes.len())
                .map_err(|_| NativeError::invariant("node arena exceeds u32 slots"))?;
            self.state.nodes.push(None);
            self.state.generations.push(0);
            slot
        };
        let index = usize::try_from(slot)
            .map_err(|_| NativeError::invariant("node slot cannot fit this platform"))?;
        let generation = self.state.generations[index]
            .checked_add(1)
            .ok_or_else(|| NativeError::invariant("node generation overflow"))?;
        self.state.generations[index] = generation;
        let handle = NodeHandle::new(slot, generation);
        let creation_id = self.state.next_creation_id;
        self.state.next_creation_id = creation_id
            .checked_add(1)
            .ok_or_else(|| NativeError::invariant("node creation ID overflow"))?;
        let creation_checkpoint = self.highest_branch_level().unwrap_or(0);
        self.state.nodes[index] = Some(Node {
            handle,
            creation_id,
            kind,
            sort,
            lifecycle: NodeLifecycle::Active,
            parent,
            tree_depth,
            creation_checkpoint,
            is_owl_named_individual,
            source_individual_id,
            representative: None,
            merge_dependency: DependencySet::empty(),
            blocker: None,
            directly_blocked: false,
            blocking_generation: 0,
            unprocessed_existentials: BTreeSet::new(),
            nominal_level,
            cardinality_tag,
        });
        self.record_mutation()?;
        Ok(handle)
    }

    pub fn retire_node(&mut self, handle: NodeHandle) -> NativeResult<()> {
        let index = self.node_index(handle)?;
        if self
            .state
            .facts_by_node
            .get(&handle)
            .is_some_and(|rows| !rows.is_empty())
        {
            return Err(NativeError::wire(
                "cannot retire a node referenced by an active fact",
            ));
        }
        for node in self.state.nodes.iter().flatten() {
            if node.handle != handle
                && (node.parent == Some(handle)
                    || node.representative == Some(handle)
                    || node.blocker == Some(handle))
            {
                return Err(NativeError::wire(
                    "cannot retire a node that remains structurally referenced",
                ));
            }
        }
        let node = self.state.nodes[index]
            .as_mut()
            .ok_or_else(|| NativeError::invariant("node disappeared during retirement"))?;
        node.lifecycle = NodeLifecycle::Retired;
        self.state.nodes[index] = None;
        self.state.free_slots.insert(handle.slot);
        self.record_mutation()
    }

    pub fn add_fact(
        &mut self,
        predicate_id: u32,
        arguments: Vec<NodeHandle>,
        dependency: DependencySet,
        core: bool,
        provenance_id: Option<u32>,
    ) -> NativeResult<u32> {
        self.add_fact_detailed(predicate_id, arguments, dependency, core, provenance_id)
            .map(|outcome| outcome.row_id)
    }

    pub(crate) fn add_fact_detailed(
        &mut self,
        predicate_id: u32,
        arguments: Vec<NodeHandle>,
        dependency: DependencySet,
        core: bool,
        provenance_id: Option<u32>,
    ) -> NativeResult<FactAddOutcome> {
        if arguments.is_empty() {
            return Err(NativeError::wire("fact rows must have positive arity"));
        }
        u32::try_from(arguments.len())
            .map_err(|_| NativeError::wire("fact arity exceeds u32 positions"))?;
        self.validate_dependency(&dependency)?;
        let mut canonical = Vec::new();
        let mut dependencies = vec![dependency];
        canonical
            .try_reserve_exact(arguments.len())
            .map_err(|_| NativeError::invariant("fact argument allocation failed"))?;
        for argument in arguments {
            let (representative, path) = self.representative(argument)?;
            self.require_active(representative)?;
            canonical.push(representative);
            dependencies.push(path);
        }
        let refs: Vec<_> = dependencies.iter().collect();
        let support = DependencySet::union(&refs);
        let key = FactKey {
            predicate_id,
            arguments: canonical,
        };
        if let Some(row_id) = self.state.facts_by_key.get(&key).copied() {
            let index = usize::try_from(row_id)
                .map_err(|_| NativeError::invariant("fact row ID cannot fit this platform"))?;
            let row = self
                .state
                .facts
                .get_mut(index)
                .ok_or_else(|| NativeError::invariant("fact index references a missing row"))?;
            let old_supports = row.supports.clone();
            if !old_supports
                .iter()
                .any(|value| value.is_subset_of(&support))
            {
                row.supports.retain(|value| !support.is_subset_of(value));
                row.supports.push(support);
                sort_dependencies(&mut row.supports);
            }
            let old_core = row.core;
            row.core |= core;
            let provenance_changed =
                provenance_id.is_some_and(|value| row.provenance_ids.insert(value));
            let support_changed = row.supports != old_supports;
            if support_changed || row.core != old_core || provenance_changed {
                self.record_mutation()?;
            }
            return Ok(FactAddOutcome {
                row_id,
                created: false,
                support_changed,
            });
        }
        let row_id = u32::try_from(self.state.facts.len())
            .map_err(|_| NativeError::invariant("fact store exceeds u32 rows"))?;
        let mut provenance_ids = BTreeSet::new();
        if let Some(value) = provenance_id {
            provenance_ids.insert(value);
        }
        let row = FactRow {
            row_id,
            key: key.clone(),
            supports: vec![support],
            core,
            active: true,
            derivation_generation: self.state.write_generation,
            provenance_ids,
        };
        self.state.facts.push(row);
        self.state.facts_by_key.insert(key.clone(), row_id);
        self.state
            .facts_by_predicate
            .entry(predicate_id)
            .or_default()
            .insert(row_id);
        for (position, argument) in key.arguments.iter().copied().enumerate() {
            let position = u32::try_from(position)
                .map_err(|_| NativeError::invariant("fact arity exceeds u32 positions"))?;
            self.state
                .facts_by_position
                .entry((predicate_id, position, argument))
                .or_default()
                .insert(row_id);
        }
        let unique_arguments: BTreeSet<_> = key.arguments.iter().copied().collect();
        for argument in unique_arguments {
            self.state
                .facts_by_node
                .entry(argument)
                .or_default()
                .insert(row_id);
        }
        self.record_mutation()?;
        Ok(FactAddOutcome {
            row_id,
            created: true,
            support_changed: true,
        })
    }

    pub fn prepare_next_delta(&mut self) -> NativeResult<()> {
        if self.state.write_generation == self.state.read_generation {
            self.state.write_generation = self
                .state
                .write_generation
                .checked_add(1)
                .ok_or_else(|| NativeError::invariant("delta generation overflow"))?;
        } else {
            self.state.read_generation = self.state.write_generation;
            self.state.write_generation = self
                .state
                .write_generation
                .checked_add(1)
                .ok_or_else(|| NativeError::invariant("delta generation overflow"))?;
        }
        self.record_mutation()
    }

    #[must_use]
    pub(crate) const fn read_generation(&self) -> u32 {
        self.state.read_generation
    }

    pub(crate) fn candidate_fact_ids(
        &self,
        predicate_id: u32,
        bindings: &BTreeMap<u32, NodeHandle>,
    ) -> NativeResult<Vec<u32>> {
        let Some(predicate_rows) = self.state.facts_by_predicate.get(&predicate_id) else {
            return Ok(Vec::new());
        };
        let mut smallest = predicate_rows;
        for (position, handle) in bindings {
            self.require_active(*handle)?;
            let Some(rows) = self
                .state
                .facts_by_position
                .get(&(predicate_id, *position, *handle))
            else {
                return Ok(Vec::new());
            };
            if rows.len() < smallest.len() {
                smallest = rows;
            }
        }
        let mut result = Vec::new();
        result
            .try_reserve_exact(smallest.len())
            .map_err(|_| NativeError::invariant("fact candidate allocation failed"))?;
        'rows: for row_id in smallest {
            let row = self.fact(*row_id)?;
            if !row.active || row.key.predicate_id != predicate_id {
                continue;
            }
            for (position, handle) in bindings {
                let index = usize::try_from(*position)
                    .map_err(|_| NativeError::wire("fact position cannot fit this platform"))?;
                if row.key.arguments.get(index) != Some(handle) {
                    continue 'rows;
                }
            }
            result.push(*row_id);
        }
        Ok(result)
    }

    #[must_use]
    pub(crate) fn active_fact_ids(&self) -> Vec<u32> {
        self.state
            .facts
            .iter()
            .filter(|row| row.active)
            .map(|row| row.row_id)
            .collect()
    }

    pub(crate) fn canonical_handle(
        &self,
        handle: NodeHandle,
    ) -> NativeResult<(NodeHandle, DependencySet)> {
        let result = self.representative(handle)?;
        self.require_active(result.0)?;
        Ok(result)
    }

    pub(crate) fn node_sort(&self, handle: NodeHandle) -> NativeResult<NodeSort> {
        Ok(self.require_active(handle)?.sort)
    }

    pub(crate) fn node_rank(&self, handle: NodeHandle) -> NativeResult<(u32, u32, u32)> {
        let node = self.require_active(handle)?;
        Ok((node.creation_id, handle.slot, handle.generation))
    }

    pub(crate) fn active_node(&self, handle: NodeHandle) -> NativeResult<&Node> {
        self.require_active(handle)
    }

    pub(crate) fn node(&self, handle: NodeHandle) -> NativeResult<&Node> {
        self.require_node(handle)
    }

    pub(crate) fn direct_children(&self, parent: NodeHandle) -> NativeResult<Vec<NodeHandle>> {
        self.require_active(parent)?;
        let mut children: Vec<_> = self
            .state
            .nodes
            .iter()
            .flatten()
            .filter(|node| node.lifecycle == NodeLifecycle::Active && node.parent == Some(parent))
            .map(|node| (node.creation_id, node.handle))
            .collect();
        children.sort_unstable();
        Ok(children
            .into_iter()
            .map(|(_creation_id, handle)| handle)
            .collect())
    }

    pub(crate) fn merge_orientation(
        &self,
        left: NodeHandle,
        right: NodeHandle,
    ) -> NativeResult<(NodeHandle, NodeHandle)> {
        let (target, source) =
            self.merge_direction(self.require_active(left)?, self.require_active(right)?)?;
        Ok((target.handle, source.handle))
    }

    pub(crate) fn facts_for_node(&self, handle: NodeHandle) -> NativeResult<Vec<FactRow>> {
        self.require_active(handle)?;
        self.state
            .facts_by_node
            .get(&handle)
            .into_iter()
            .flat_map(BTreeSet::iter)
            .map(|row_id| self.fact(*row_id).cloned())
            .collect()
    }

    pub(crate) fn fact_history(&self, predicate_id: u32, arguments: &[NodeHandle]) -> Vec<FactRow> {
        self.state
            .facts
            .iter()
            .filter(|row| row.key.predicate_id == predicate_id && row.key.arguments == arguments)
            .cloned()
            .collect()
    }

    #[must_use]
    pub(crate) fn active_node_handles(&self) -> Vec<NodeHandle> {
        let mut values: Vec<_> = self
            .state
            .nodes
            .iter()
            .flatten()
            .filter(|node| node.lifecycle == NodeLifecycle::Active)
            .map(|node| (node.creation_id, node.handle))
            .collect();
        values.sort_unstable();
        values
            .into_iter()
            .map(|(_creation_id, handle)| handle)
            .collect()
    }

    pub(crate) fn disjunction(&self, disjunction_id: u32) -> NativeResult<&GroundDisjunction> {
        self.state
            .disjunctions
            .get(
                usize::try_from(disjunction_id).map_err(|_| {
                    NativeError::wire("ground-disjunction ID cannot fit this platform")
                })?,
            )
            .ok_or_else(|| NativeError::wire("ground-disjunction ID is unavailable"))
    }

    pub(crate) fn strengthen_disjunction(
        &mut self,
        disjunction_id: u32,
        dependency: DependencySet,
    ) -> NativeResult<bool> {
        self.validate_dependency(&dependency)?;
        let index = usize::try_from(disjunction_id)
            .map_err(|_| NativeError::wire("ground-disjunction ID cannot fit this platform"))?;
        let current = self
            .state
            .disjunctions
            .get(index)
            .ok_or_else(|| NativeError::wire("ground-disjunction ID is unavailable"))?;
        if !current.active
            || dependency_rank(&current.base_dependency) <= dependency_rank(&dependency)
        {
            return Ok(false);
        }
        self.record_mutation()?;
        self.state.disjunctions[index].base_dependency = dependency.clone();
        for branch in &mut self.branches {
            if branch.choice_kind == "ground_disjunction" && branch.source_id == disjunction_id {
                branch.base_dependency = dependency.clone();
            }
        }
        Ok(true)
    }

    #[must_use]
    pub(crate) fn branch_choices_for_source(&self, source_id: u32) -> Vec<(u32, u32)> {
        self.branches
            .iter()
            .filter(|branch| branch.source_id == source_id)
            .filter_map(|branch| {
                branch
                    .alternatives
                    .get(branch.next_alternative)
                    .copied()
                    .map(|current| (branch.level, current))
            })
            .collect()
    }

    #[must_use]
    pub(crate) const fn clash(&self) -> Option<&Clash> {
        self.state.clash.as_ref()
    }

    pub(crate) fn branch(&self, level: u32) -> NativeResult<&Branch> {
        self.branches
            .get(
                usize::try_from(level)
                    .map_err(|_| NativeError::wire("branch level cannot fit this platform"))?,
            )
            .ok_or_else(|| NativeError::wire("branch level is unavailable"))
    }

    pub fn push_branch(
        &mut self,
        choice_kind: String,
        alternatives: Vec<u32>,
        source_id: u32,
        base_dependency: DependencySet,
    ) -> NativeResult<u32> {
        if !matches!(
            choice_kind.as_str(),
            "ground_disjunction" | "merge" | "datatype"
        ) {
            return Err(NativeError::wire("branch choice kind is unknown"));
        }
        if alternatives.len() < 2 || !is_unique(&alternatives) {
            return Err(NativeError::wire(
                "a branch requires at least two unique alternatives",
            ));
        }
        if self.state.clash.is_some() {
            return Err(NativeError::wire(
                "cannot create a branch while a clash is installed",
            ));
        }
        let level = u32::try_from(self.branches.len())
            .map_err(|_| NativeError::invariant("branch count exceeds u32"))?;
        if base_dependency
            .maximum()
            .is_some_and(|maximum| maximum >= level)
        {
            return Err(NativeError::wire(
                "branch dependency references its own or a future level",
            ));
        }
        self.checkpoint_sequence = self
            .checkpoint_sequence
            .checked_add(1)
            .ok_or_else(|| NativeError::invariant("checkpoint sequence overflow"))?;
        self.branches.push(Branch {
            level,
            choice_kind,
            checkpoint: CheckpointMeta {
                sequence: self.checkpoint_sequence,
                trail_length: self.trail_length,
                label: format!("branch-{level}"),
            },
            snapshot: self.snapshot(),
            alternatives,
            source_id,
            initial_base_dependency: base_dependency.clone(),
            base_dependency,
            next_alternative: 0,
            learned_dependency: DependencySet::empty(),
        });
        Ok(level)
    }

    pub fn backtrack_to(&mut self, level: u32) -> NativeResult<()> {
        let index = usize::try_from(level)
            .map_err(|_| NativeError::wire("branch level cannot fit this platform"))?;
        let snapshot = self
            .branches
            .get(index)
            .ok_or_else(|| NativeError::wire("branch level is unavailable"))?
            .snapshot
            .clone();
        self.restore(snapshot);
        self.branches.truncate(index + 1);
        self.check_invariants()
    }

    pub fn advance_branch(
        &mut self,
        level: u32,
        learned_dependency: DependencySet,
    ) -> NativeResult<Option<u32>> {
        self.backtrack_to(level)?;
        let index = usize::try_from(level)
            .map_err(|_| NativeError::wire("branch level cannot fit this platform"))?;
        let branch = self
            .branches
            .get_mut(index)
            .ok_or_else(|| NativeError::invariant("branch disappeared after backtrack"))?;
        branch.base_dependency = branch.initial_base_dependency.clone();
        branch.learned_dependency =
            DependencySet::union(&[&branch.learned_dependency, &learned_dependency]);
        branch.next_alternative = branch
            .next_alternative
            .checked_add(1)
            .ok_or_else(|| NativeError::invariant("branch alternative index overflow"))?;
        if branch.next_alternative >= branch.alternatives.len() {
            self.branches.pop();
            return Ok(None);
        }
        let current = branch.alternatives[branch.next_alternative];
        self.check_invariants()?;
        Ok(Some(current))
    }

    pub fn merge_nodes(
        &mut self,
        left: NodeHandle,
        right: NodeHandle,
        dependency: DependencySet,
    ) -> NativeResult<NodeHandle> {
        self.validate_dependency(&dependency)?;
        let checkpoint = self.snapshot();
        match self.merge_nodes_inner(left, right, dependency) {
            Ok(handle) => Ok(handle),
            Err(error) => {
                self.restore(checkpoint);
                Err(error)
            }
        }
    }

    /// Merge inside an already established [`Self::atomic`] transaction.
    /// Semantic managers use this to avoid cloning the full state twice.
    pub(crate) fn merge_nodes_in_transaction(
        &mut self,
        left: NodeHandle,
        right: NodeHandle,
        dependency: DependencySet,
    ) -> NativeResult<NodeHandle> {
        self.validate_dependency(&dependency)?;
        self.merge_nodes_inner(left, right, dependency)
    }

    fn merge_nodes_inner(
        &mut self,
        left: NodeHandle,
        right: NodeHandle,
        dependency: DependencySet,
    ) -> NativeResult<NodeHandle> {
        let (left_rep, left_path) = self.representative(left)?;
        let (right_rep, right_path) = self.representative(right)?;
        let combined = DependencySet::union(&[&dependency, &left_path, &right_path]);
        if left_rep == right_rep {
            return Ok(left_rep);
        }
        let left_node = self.require_active(left_rep)?.clone();
        let right_node = self.require_active(right_rep)?.clone();
        if left_node.sort != right_node.sort {
            return Err(NativeError::invariant(
                "cannot merge object and concrete nodes",
            ));
        }
        let (target, source) = self.merge_direction(&left_node, &right_node)?;
        self.checkpoint_sequence = self
            .checkpoint_sequence
            .checked_add(1)
            .ok_or_else(|| NativeError::invariant("checkpoint sequence overflow"))?;

        let blocked: Vec<_> = self
            .state
            .nodes
            .iter()
            .flatten()
            .filter(|node| {
                node.lifecycle == NodeLifecycle::Active && node.blocker == Some(source.handle)
            })
            .map(|node| node.handle)
            .collect();
        for handle in blocked {
            self.set_blocked(handle, None, false)?;
        }
        let affected: Vec<u32> = self
            .state
            .facts_by_node
            .get(&source.handle)
            .map_or_else(Vec::new, |values| values.iter().copied().collect());
        for row_id in affected {
            let row = self.fact(row_id)?.clone();
            if !row.active {
                continue;
            }
            let arguments: Vec<NodeHandle> = row
                .key
                .arguments
                .iter()
                .map(|value| {
                    if *value == source.handle {
                        target.handle
                    } else {
                        *value
                    }
                })
                .collect();
            for support in &row.supports {
                self.add_fact(
                    row.key.predicate_id,
                    arguments.clone(),
                    DependencySet::union(&[support, &combined]),
                    row.core,
                    None,
                )?;
            }
            let minimal = row.minimal_dependency()?.clone();
            for provenance in &row.provenance_ids {
                self.add_fact(
                    row.key.predicate_id,
                    arguments.clone(),
                    DependencySet::union(&[&minimal, &combined]),
                    row.core,
                    Some(*provenance),
                )?;
            }
            self.deactivate_fact(row_id)?;
        }
        let source_index = self.node_index(source.handle)?;
        let source_node = self.state.nodes[source_index]
            .as_mut()
            .ok_or_else(|| NativeError::invariant("merge source disappeared"))?;
        source_node.lifecycle = NodeLifecycle::Merged;
        source_node.representative = Some(target.handle);
        source_node.merge_dependency = combined;
        source_node.blocker = None;
        source_node.directly_blocked = false;
        source_node.blocking_generation = source_node
            .blocking_generation
            .checked_add(1)
            .ok_or_else(|| NativeError::invariant("blocking generation overflow"))?;
        self.record_mutation()?;
        Ok(target.handle)
    }

    pub fn prune_subtree(&mut self, root: NodeHandle) -> NativeResult<Vec<NodeHandle>> {
        self.require_active(root)?;
        let checkpoint = self.snapshot();
        match self.prune_subtree_inner(root) {
            Ok(handles) => Ok(handles),
            Err(error) => {
                self.restore(checkpoint);
                Err(error)
            }
        }
    }

    /// Prune inside an already established [`Self::atomic`] transaction.
    /// Semantic managers use this to keep multi-child pruning one rollback unit.
    pub(crate) fn prune_subtree_in_transaction(
        &mut self,
        root: NodeHandle,
    ) -> NativeResult<Vec<NodeHandle>> {
        self.require_active(root)?;
        self.prune_subtree_inner(root)
    }

    fn prune_subtree_inner(&mut self, root: NodeHandle) -> NativeResult<Vec<NodeHandle>> {
        self.checkpoint_sequence = self
            .checkpoint_sequence
            .checked_add(1)
            .ok_or_else(|| NativeError::invariant("checkpoint sequence overflow"))?;
        let mut affected = Vec::new();
        for node in self.state.nodes.iter().flatten() {
            if node.lifecycle == NodeLifecycle::Active
                && (node.handle == root || self.has_ancestor(node, root)?)
            {
                affected.push(node.clone());
            }
        }
        affected.sort_by_key(|node| (std::cmp::Reverse(node.tree_depth), node.creation_id));
        let handles: BTreeSet<_> = affected.iter().map(|node| node.handle).collect();
        let blocked: Vec<_> = self
            .state
            .nodes
            .iter()
            .flatten()
            .filter(|node| {
                node.lifecycle == NodeLifecycle::Active
                    && node
                        .blocker
                        .is_some_and(|blocker| handles.contains(&blocker))
            })
            .map(|node| node.handle)
            .collect();
        for handle in blocked {
            self.set_blocked(handle, None, false)?;
        }
        let row_ids: BTreeSet<u32> = handles
            .iter()
            .filter_map(|handle| self.state.facts_by_node.get(handle))
            .flat_map(BTreeSet::iter)
            .copied()
            .collect();
        for row_id in row_ids {
            if self.fact(row_id)?.active {
                self.deactivate_fact(row_id)?;
            }
        }
        for node in &affected {
            let index = self.node_index(node.handle)?;
            let selected = self.state.nodes[index]
                .as_mut()
                .ok_or_else(|| NativeError::invariant("pruned node disappeared"))?;
            selected.lifecycle = NodeLifecycle::Pruned;
            selected.blocker = None;
            selected.directly_blocked = false;
            selected.blocking_generation = selected
                .blocking_generation
                .checked_add(1)
                .ok_or_else(|| NativeError::invariant("blocking generation overflow"))?;
            self.record_mutation()?;
        }
        Ok(affected.into_iter().map(|node| node.handle).collect())
    }

    pub fn add_disjunction(
        &mut self,
        disjunct_ids: Vec<u32>,
        dependency: DependencySet,
    ) -> NativeResult<u32> {
        if disjunct_ids.is_empty() || !is_unique(&disjunct_ids) {
            return Err(NativeError::wire(
                "ground disjunct identifiers must be nonempty and unique",
            ));
        }
        self.validate_dependency(&dependency)?;
        let disjunction_id = u32::try_from(self.state.disjunctions.len())
            .map_err(|_| NativeError::invariant("disjunction store exceeds u32"))?;
        self.state.disjunctions.push(GroundDisjunction {
            disjunction_id,
            disjunct_ids,
            base_dependency: dependency,
            creation_checkpoint: self.highest_branch_level().unwrap_or(0),
            active: true,
            processed: false,
        });
        self.record_mutation()?;
        self.state.disjunction_queue.enqueue(
            QueueValue::Integer(disjunction_id),
            vec![i64::from(disjunction_id)],
        )?;
        self.record_mutation()?;
        Ok(disjunction_id)
    }

    pub fn take_disjunction(&mut self) -> NativeResult<Option<u32>> {
        while let Some(value) = self.state.disjunction_queue.pop() {
            self.record_mutation()?;
            let QueueValue::Integer(disjunction_id) = value else {
                return Err(NativeError::invariant(
                    "disjunction queue contains a node handle",
                ));
            };
            let index = usize::try_from(disjunction_id)
                .map_err(|_| NativeError::invariant("disjunction ID cannot fit platform"))?;
            let Some(record) = self.state.disjunctions.get_mut(index) else {
                return Err(NativeError::invariant(
                    "disjunction queue references a missing record",
                ));
            };
            if !record.active || record.processed {
                continue;
            }
            record.processed = true;
            self.record_mutation()?;
            return Ok(Some(disjunction_id));
        }
        Ok(None)
    }

    pub fn install_clash(
        &mut self,
        kind: String,
        dependency: DependencySet,
        participants: Vec<u32>,
        provenance_id: Option<u32>,
    ) -> NativeResult<bool> {
        if !is_clash_kind(&kind) {
            return Err(NativeError::wire("clash kind is unknown"));
        }
        if participants.windows(2).any(|pair| pair[0] >= pair[1]) {
            return Err(NativeError::wire(
                "clash participants must be ascending and unique",
            ));
        }
        self.validate_dependency(&dependency)?;
        let candidate = Clash {
            kind,
            dependency,
            participants,
            provenance_id,
        };
        if self
            .state
            .clash
            .as_ref()
            .is_some_and(|current| select_clash(current, &candidate) == current)
        {
            return Ok(false);
        }
        self.state.clash = Some(candidate);
        self.record_mutation()?;
        Ok(true)
    }

    pub fn enqueue_integer(
        &mut self,
        queue: &str,
        value: u32,
        priority: Vec<i64>,
    ) -> NativeResult<()> {
        let selected = match queue {
            "delta_rows" => &mut self.state.delta_rows,
            "annotated_equalities" => &mut self.state.annotated_equalities,
            "datatype_components" => &mut self.state.datatype_components,
            _ => return Err(NativeError::wire("trace integer queue is unknown")),
        };
        if selected.enqueue(QueueValue::Integer(value), priority)? {
            self.record_mutation()?;
        }
        Ok(())
    }

    pub(crate) fn take_integer(&mut self, queue: &str) -> NativeResult<Option<u32>> {
        let selected = match queue {
            "delta_rows" => &mut self.state.delta_rows,
            "annotated_equalities" => &mut self.state.annotated_equalities,
            "datatype_components" => &mut self.state.datatype_components,
            _ => return Err(NativeError::wire("native integer queue is unknown")),
        };
        let Some(value) = selected.pop() else {
            return Ok(None);
        };
        self.record_mutation()?;
        let QueueValue::Integer(value) = value else {
            return Err(NativeError::invariant(
                "integer queue contains a node handle",
            ));
        };
        Ok(Some(value))
    }

    pub fn enqueue_node(
        &mut self,
        queue: &str,
        value: NodeHandle,
        priority: Vec<i64>,
    ) -> NativeResult<()> {
        self.require_node(value)?;
        let selected = match queue {
            "existential_candidates" => &mut self.state.existential_candidates,
            "blocking_invalidations" => &mut self.state.blocking_invalidations,
            _ => return Err(NativeError::wire("trace node queue is unknown")),
        };
        if selected.enqueue(QueueValue::Node(value), priority)? {
            self.record_mutation()?;
        }
        Ok(())
    }

    pub fn mark_existential(
        &mut self,
        handle: NodeHandle,
        existential_id: u32,
        pending: bool,
    ) -> NativeResult<()> {
        let index = self.node_index(handle)?;
        if self
            .require_active(handle)?
            .unprocessed_existentials
            .contains(&existential_id)
            == pending
        {
            return Ok(());
        }
        let node = self.state.nodes[index]
            .as_mut()
            .ok_or_else(|| NativeError::invariant("existential node disappeared"))?;
        if pending {
            node.unprocessed_existentials.insert(existential_id);
        } else {
            node.unprocessed_existentials.remove(&existential_id);
        }
        self.record_mutation()
    }

    pub fn set_blocked(
        &mut self,
        handle: NodeHandle,
        blocker: Option<NodeHandle>,
        directly: bool,
    ) -> NativeResult<()> {
        let index = self.node_index(handle)?;
        if self.require_active(handle)?.sort == NodeSort::Data {
            return Err(NativeError::wire("concrete nodes cannot be blocked"));
        }
        if let Some(value) = blocker {
            if self.require_active(value)?.sort == NodeSort::Data {
                return Err(NativeError::wire("a concrete node cannot be a blocker"));
            }
        }
        let node = self.state.nodes[index]
            .as_mut()
            .ok_or_else(|| NativeError::invariant("blocked node disappeared"))?;
        node.blocker = blocker;
        node.directly_blocked = blocker.is_some() && directly;
        node.blocking_generation = node
            .blocking_generation
            .checked_add(1)
            .ok_or_else(|| NativeError::invariant("blocking generation overflow"))?;
        self.record_mutation()
    }

    pub fn reset_to_operation_root(&mut self) -> NativeResult<()> {
        self.restore(self.operation_root.clone());
        self.branches.clear();
        self.check_invariants()
    }

    pub fn check_invariants(&self) -> NativeResult<()> {
        let highest_branch_level = self.highest_branch_level().unwrap_or(0);
        let expected_free: BTreeSet<u32> = self
            .state
            .nodes
            .iter()
            .enumerate()
            .filter_map(|(index, node)| node.is_none().then(|| u32::try_from(index).ok()).flatten())
            .collect();
        if expected_free != self.state.free_slots
            || self.state.nodes.len() != self.state.generations.len()
        {
            return Err(NativeError::invariant(
                "node arena free list or generation table is inconsistent",
            ));
        }
        let mut creation_ids = BTreeSet::new();
        for (index, node) in self
            .state
            .nodes
            .iter()
            .enumerate()
            .filter_map(|(index, node)| node.as_ref().map(|node| (index, node)))
        {
            if usize::try_from(node.handle.slot).ok() != Some(index)
                || node.handle.generation > self.state.generations[index]
                || !creation_ids.insert(node.creation_id)
                || node.creation_checkpoint > highest_branch_level
            {
                return Err(NativeError::invariant(
                    "node handle, generation, or creation ID is inconsistent",
                ));
            }
            if node.kind == NodeKind::Tree {
                let parent = node
                    .parent
                    .ok_or_else(|| NativeError::invariant("tree node lacks a parent"))?;
                if node.tree_depth != self.require_node(parent)?.tree_depth + 1 {
                    return Err(NativeError::invariant("tree node depth is inconsistent"));
                }
            } else if node.parent.is_some() || node.tree_depth != 0 {
                return Err(NativeError::invariant(
                    "non-tree node has parent or nonzero depth",
                ));
            }
            if node.sort != node.kind.sort() {
                return Err(NativeError::invariant("node kind and sort disagree"));
            }
            if node.lifecycle == NodeLifecycle::Merged {
                let representative = node
                    .representative
                    .ok_or_else(|| NativeError::invariant("merged node lacks a representative"))?;
                if self.representative(representative)?.0 == node.handle
                    || self
                        .require_active(self.representative(representative)?.0)
                        .is_err()
                    || node
                        .merge_dependency
                        .maximum()
                        .is_some_and(|maximum| maximum > highest_branch_level)
                {
                    return Err(NativeError::invariant(
                        "merged node representative is invalid",
                    ));
                }
            } else if node.representative.is_some() {
                return Err(NativeError::invariant(
                    "nonmerged node carries a representative",
                ));
            }
            if let Some(blocker) = node.blocker {
                if node.sort != NodeSort::Object
                    || self.require_active(blocker)?.sort != NodeSort::Object
                {
                    return Err(NativeError::invariant("blocking relation has data sort"));
                }
            }
        }

        let mut by_key = BTreeMap::new();
        let mut by_node: BTreeMap<NodeHandle, BTreeSet<u32>> = BTreeMap::new();
        let mut by_predicate: BTreeMap<u32, BTreeSet<u32>> = BTreeMap::new();
        let mut by_position: BTreeMap<(u32, u32, NodeHandle), BTreeSet<u32>> = BTreeMap::new();
        for (index, row) in self.state.facts.iter().enumerate() {
            if usize::try_from(row.row_id).ok() != Some(index) || !row.active {
                if usize::try_from(row.row_id).ok() != Some(index) {
                    return Err(NativeError::invariant(
                        "fact row ID disagrees with position",
                    ));
                }
                continue;
            }
            if by_key.insert(row.key.clone(), row.row_id).is_some() || row.supports.is_empty() {
                return Err(NativeError::invariant(
                    "active facts are duplicated or unsupported",
                ));
            }
            if row.derivation_generation > self.state.write_generation {
                return Err(NativeError::invariant(
                    "fact derivation generation exceeds the current delta generation",
                ));
            }
            by_predicate
                .entry(row.key.predicate_id)
                .or_default()
                .insert(row.row_id);
            for (position, argument) in row.key.arguments.iter().copied().enumerate() {
                let position = u32::try_from(position)
                    .map_err(|_| NativeError::invariant("fact position exceeds u32"))?;
                by_position
                    .entry((row.key.predicate_id, position, argument))
                    .or_default()
                    .insert(row.row_id);
            }
            for left in &row.supports {
                if left
                    .maximum()
                    .is_some_and(|maximum| maximum > highest_branch_level)
                {
                    return Err(NativeError::invariant(
                        "fact support references a future branch level",
                    ));
                }
                for right in &row.supports {
                    if left != right && left.is_subset_of(right) {
                        return Err(NativeError::invariant("fact retains a dominated support"));
                    }
                }
            }
            let mut sorted = row.supports.clone();
            sort_dependencies(&mut sorted);
            if sorted != row.supports {
                return Err(NativeError::invariant("fact supports are not canonical"));
            }
            for argument in &row.key.arguments {
                if self.require_active(*argument).is_err() {
                    return Err(NativeError::invariant(
                        "active fact references an inactive node",
                    ));
                }
                by_node.entry(*argument).or_default().insert(row.row_id);
            }
        }
        if by_key != self.state.facts_by_key
            || by_node != self.state.facts_by_node
            || by_predicate != self.state.facts_by_predicate
            || by_position != self.state.facts_by_position
        {
            return Err(NativeError::invariant(
                "fact indexes differ from exact reconstruction",
            ));
        }
        if self.state.write_generation < self.state.read_generation {
            return Err(NativeError::invariant(
                "delta write generation precedes read generation",
            ));
        }
        for queue in [
            &self.state.delta_rows,
            &self.state.annotated_equalities,
            &self.state.existential_candidates,
            &self.state.disjunction_queue,
            &self.state.datatype_components,
            &self.state.blocking_invalidations,
        ] {
            queue.check_invariants()?;
        }
        let expected_disjunctions: Vec<_> = self
            .state
            .disjunctions
            .iter()
            .filter(|record| record.active && !record.processed)
            .map(|record| QueueValue::Integer(record.disjunction_id))
            .collect();
        if self
            .state
            .disjunction_queue
            .values()
            .cloned()
            .collect::<Vec<_>>()
            != expected_disjunctions
        {
            return Err(NativeError::invariant(
                "ground-disjunction queue differs from records",
            ));
        }
        for record in self
            .state
            .disjunctions
            .iter()
            .filter(|record| record.active)
        {
            if record.creation_checkpoint > highest_branch_level
                || record
                    .base_dependency
                    .maximum()
                    .is_some_and(|maximum| maximum > highest_branch_level)
            {
                return Err(NativeError::invariant(
                    "ground disjunction references a future branch level",
                ));
            }
        }
        if self
            .state
            .clash
            .as_ref()
            .and_then(|clash| clash.dependency.maximum())
            .is_some_and(|maximum| maximum > highest_branch_level)
        {
            return Err(NativeError::invariant(
                "clash references a future branch level",
            ));
        }
        for (index, branch) in self.branches.iter().enumerate() {
            if usize::try_from(branch.level).ok() != Some(index)
                || branch.next_alternative >= branch.alternatives.len()
                || branch.checkpoint.trail_length > self.trail_length
            {
                return Err(NativeError::invariant("branch metadata is inconsistent"));
            }
        }
        Ok(())
    }

    pub fn canonical_snapshot(&self) -> NativeResult<String> {
        self.check_invariants()?;
        serde_json::to_string(&self.logical_value()).map_err(Into::into)
    }

    #[must_use]
    pub fn logical_value(&self) -> Value {
        json!({
            "branches": self.branches.iter().map(Branch::logical_value).collect::<Vec<_>>(),
            "clash": self.state.clash.as_ref().map(Clash::logical_value),
            "delta": {
                "read_generation": self.state.read_generation,
                "write_generation": self.state.write_generation,
            },
            "disjunctions": self.state.disjunctions.iter().map(GroundDisjunction::logical_value).collect::<Vec<_>>(),
            "facts": self.state.facts.iter().filter(|row| row.active).map(FactRow::logical_value).collect::<Vec<_>>(),
            "nodes": self.state.nodes.iter().flatten().filter(|node| node.lifecycle != NodeLifecycle::Retired).map(Node::logical_value).collect::<Vec<_>>(),
            "queues": {
                "annotated_equalities": integer_queue_values(&self.state.annotated_equalities),
                "blocking_invalidations": node_queue_values(&self.state.blocking_invalidations),
                "datatype_components": integer_queue_values(&self.state.datatype_components),
                "delta_rows": integer_queue_values(&self.state.delta_rows),
                "disjunctions": integer_queue_values(&self.state.disjunction_queue),
                "existential_candidates": node_queue_values(&self.state.existential_candidates),
            },
        })
    }

    fn record_mutation(&mut self) -> NativeResult<()> {
        self.trail_length = self
            .trail_length
            .checked_add(1)
            .ok_or_else(|| NativeError::invariant("trail length overflow"))?;
        Ok(())
    }

    fn snapshot(&self) -> StateCheckpoint {
        StateCheckpoint {
            state: self.state.clone(),
            trail_length: self.trail_length,
        }
    }

    fn restore(&mut self, snapshot: StateCheckpoint) {
        let current_generations = self.state.generations.clone();
        self.state = snapshot.state;
        let length = self.state.generations.len().max(current_generations.len());
        self.state.generations.resize(length, 0);
        self.state.nodes.resize(length, None);
        for (index, generation) in current_generations.into_iter().enumerate() {
            self.state.generations[index] = self.state.generations[index].max(generation);
        }
        self.state.free_slots = self
            .state
            .nodes
            .iter()
            .enumerate()
            .filter_map(|(index, node)| node.is_none().then(|| u32::try_from(index).ok()).flatten())
            .collect();
        self.trail_length = snapshot.trail_length;
    }

    pub(crate) fn highest_branch_level(&self) -> Option<u32> {
        self.branches.last().map(|branch| branch.level)
    }

    fn validate_dependency(&self, dependency: &DependencySet) -> NativeResult<()> {
        if dependency.maximum().is_some_and(|maximum| {
            self.highest_branch_level()
                .is_none_or(|highest| maximum > highest)
        }) {
            return Err(NativeError::wire(
                "dependency references a future branch level",
            ));
        }
        Ok(())
    }

    fn node_index(&self, handle: NodeHandle) -> NativeResult<usize> {
        let index = usize::try_from(handle.slot)
            .map_err(|_| NativeError::wire("node slot cannot fit this platform"))?;
        let node = self
            .state
            .nodes
            .get(index)
            .and_then(Option::as_ref)
            .ok_or_else(|| NativeError::wire("stale native node handle"))?;
        if node.handle.generation != handle.generation || node.lifecycle == NodeLifecycle::Retired {
            return Err(NativeError::wire("stale native node handle"));
        }
        Ok(index)
    }

    fn require_node(&self, handle: NodeHandle) -> NativeResult<&Node> {
        let index = self.node_index(handle)?;
        self.state.nodes[index]
            .as_ref()
            .ok_or_else(|| NativeError::invariant("validated node slot is empty"))
    }

    fn require_active(&self, handle: NodeHandle) -> NativeResult<&Node> {
        let node = self.require_node(handle)?;
        if node.lifecycle != NodeLifecycle::Active {
            return Err(NativeError::wire("node is not active"));
        }
        Ok(node)
    }

    fn representative(&self, handle: NodeHandle) -> NativeResult<(NodeHandle, DependencySet)> {
        let mut node = self.require_node(handle)?;
        let mut dependencies = Vec::new();
        let mut seen = BTreeSet::new();
        while let Some(representative) = node.representative {
            if !seen.insert(node.handle) {
                return Err(NativeError::invariant(
                    "cycle in node representative relation",
                ));
            }
            dependencies.push(node.merge_dependency.clone());
            node = self.require_node(representative)?;
        }
        let refs: Vec<_> = dependencies.iter().collect();
        Ok((node.handle, DependencySet::union(&refs)))
    }

    pub(crate) fn fact(&self, row_id: u32) -> NativeResult<&FactRow> {
        self.state
            .facts
            .get(
                usize::try_from(row_id)
                    .map_err(|_| NativeError::wire("fact row ID cannot fit this platform"))?,
            )
            .ok_or_else(|| NativeError::wire("fact row ID is unavailable"))
    }

    fn deactivate_fact(&mut self, row_id: u32) -> NativeResult<()> {
        let row = self.fact(row_id)?.clone();
        if !row.active {
            return Ok(());
        }
        self.state.facts_by_key.remove(&row.key);
        let predicate_rows = self
            .state
            .facts_by_predicate
            .get_mut(&row.key.predicate_id)
            .ok_or_else(|| NativeError::invariant("fact row is absent from predicate index"))?;
        predicate_rows.remove(&row_id);
        if predicate_rows.is_empty() {
            self.state.facts_by_predicate.remove(&row.key.predicate_id);
        }
        for (position, argument) in row.key.arguments.iter().copied().enumerate() {
            let position = u32::try_from(position)
                .map_err(|_| NativeError::invariant("fact position exceeds u32"))?;
            let index_key = (row.key.predicate_id, position, argument);
            let position_rows = self
                .state
                .facts_by_position
                .get_mut(&index_key)
                .ok_or_else(|| {
                    NativeError::invariant("fact row is absent from positional index")
                })?;
            position_rows.remove(&row_id);
            if position_rows.is_empty() {
                self.state.facts_by_position.remove(&index_key);
            }
        }
        let unique_arguments: BTreeSet<_> = row.key.arguments.iter().copied().collect();
        for argument in unique_arguments {
            let values = self.state.facts_by_node.get_mut(&argument).ok_or_else(|| {
                NativeError::invariant("fact row is absent from node incidence index")
            })?;
            values.remove(&row_id);
            if values.is_empty() {
                self.state.facts_by_node.remove(&argument);
            }
        }
        let index = usize::try_from(row_id)
            .map_err(|_| NativeError::wire("fact row ID cannot fit this platform"))?;
        self.state.facts[index].active = false;
        self.record_mutation()
    }

    fn merge_direction<'a>(
        &self,
        left: &'a Node,
        right: &'a Node,
    ) -> NativeResult<(&'a Node, &'a Node)> {
        if self.has_ancestor(left, right.handle)? {
            return Ok((right, left));
        }
        if self.has_ancestor(right, left.handle)? {
            return Ok((left, right));
        }
        Ok(if merge_rank(left) <= merge_rank(right) {
            (left, right)
        } else {
            (right, left)
        })
    }

    fn has_ancestor(&self, node: &Node, ancestor: NodeHandle) -> NativeResult<bool> {
        let mut parent = node.parent;
        let mut seen = BTreeSet::new();
        while let Some(value) = parent {
            if value == ancestor {
                return Ok(true);
            }
            if !seen.insert(value) {
                return Err(NativeError::invariant("cycle in tree parent relation"));
            }
            parent = self.require_node(value)?.parent;
        }
        Ok(false)
    }
}

impl crate::blocking::BlockingStateRead for TableauKernel {
    type Node = NodeHandle;

    fn revision(&self) -> u64 {
        self.trail_length
    }

    fn node_records(
        &self,
    ) -> Result<Vec<crate::blocking::NodeRecord<Self::Node>>, crate::blocking::BlockingError> {
        Ok(self
            .state
            .nodes
            .iter()
            .flatten()
            .map(|node| crate::blocking::NodeRecord {
                node: node.handle,
                key: crate::blocking::NodeKey::new(node.handle.slot, node.handle.generation),
                creation_id: node.creation_id,
                kind: match node.kind {
                    NodeKind::Root => crate::blocking::NodeKind::Root,
                    NodeKind::Tree => crate::blocking::NodeKind::Tree,
                    NodeKind::Ni => crate::blocking::NodeKind::Ni,
                    NodeKind::Concrete => crate::blocking::NodeKind::Concrete,
                },
                lifecycle: match node.lifecycle {
                    NodeLifecycle::Active => crate::blocking::NodeLifecycle::Active,
                    NodeLifecycle::Merged => crate::blocking::NodeLifecycle::Merged,
                    NodeLifecycle::Pruned => crate::blocking::NodeLifecycle::Pruned,
                    NodeLifecycle::Retired => crate::blocking::NodeLifecycle::Retired,
                },
                parent: node.parent,
                has_pending_existentials: !node.unprocessed_existentials.is_empty(),
            })
            .collect())
    }

    fn active_fact_records(
        &self,
    ) -> Result<Vec<crate::blocking::FactRecord<Self::Node>>, crate::blocking::BlockingError> {
        Ok(self
            .state
            .facts
            .iter()
            .filter(|row| row.active)
            .map(|row| crate::blocking::FactRecord {
                row_id: row.row_id,
                predicate_id: row.key.predicate_id,
                arguments: row.key.arguments.clone(),
                core: row.core,
                active: true,
            })
            .collect())
    }
}

impl crate::blocking::BlockingStateMutate for TableauKernel {
    fn blocking_atomic<T, F>(&mut self, operation: F) -> Result<T, crate::blocking::BlockingError>
    where
        F: FnOnce(&mut Self) -> Result<T, crate::blocking::BlockingError>,
    {
        let checkpoint = self.snapshot();
        let result = operation(self);
        if result.is_err() {
            self.restore(checkpoint);
        }
        result
    }

    fn apply_assignment_change(
        &mut self,
        change: &crate::blocking::AssignmentChange<Self::Node>,
    ) -> Result<(), crate::blocking::BlockingError> {
        let (blocker, directly) = change.after.map_or((None, false), |assignment| {
            if assignment.from_cache {
                (None, false)
            } else {
                (assignment.blocker, assignment.directly)
            }
        });
        self.set_blocked(change.node, blocker, directly)
            .map_err(blocking_error)
    }

    fn promote_core_fact(&mut self, row_id: u32) -> Result<(), crate::blocking::BlockingError> {
        let index = usize::try_from(row_id)
            .map_err(|_| crate::blocking::BlockingError::invalid("fact row ID is too large"))?;
        let row =
            self.state.facts.get(index).ok_or_else(|| {
                crate::blocking::BlockingError::invalid("fact row ID is unavailable")
            })?;
        if !row.active {
            return Err(crate::blocking::BlockingError::invalid(
                "cannot promote an inactive fact row",
            ));
        }
        if row.core {
            return Ok(());
        }
        self.state.facts[index].core = true;
        self.record_mutation().map_err(blocking_error)
    }

    fn reschedule_existentials(
        &mut self,
        node: Self::Node,
    ) -> Result<(), crate::blocking::BlockingError> {
        if self
            .require_active(node)
            .map_err(blocking_error)?
            .unprocessed_existentials
            .is_empty()
        {
            return Ok(());
        }
        let rank = self.node_rank(node).map_err(blocking_error)?;
        self.enqueue_node(
            "existential_candidates",
            node,
            vec![i64::from(rank.0), i64::from(rank.1), i64::from(rank.2)],
        )
        .map_err(blocking_error)
    }
}

fn blocking_error(error: NativeError) -> crate::blocking::BlockingError {
    match error.kind {
        crate::error::ErrorKind::Wire | crate::error::ErrorKind::Version => {
            crate::blocking::BlockingError::invalid(error.message)
        }
        crate::error::ErrorKind::Cancelled | crate::error::ErrorKind::Timeout => {
            crate::blocking::BlockingError::cancelled(error.message)
        }
        crate::error::ErrorKind::Resource => crate::blocking::BlockingError::resource(
            error.message,
            "native_resource",
            error
                .context
                .get("observed")
                .and_then(|value| value.parse().ok())
                .unwrap_or_default(),
            error
                .context
                .get("allowed")
                .and_then(|value| value.parse().ok())
                .unwrap_or_default(),
        ),
        _ => crate::blocking::BlockingError::invariant(error.message),
    }
}

fn merge_rank(node: &Node) -> (u8, u32, u32) {
    let kind = if node.is_owl_named_individual {
        0
    } else {
        match node.kind {
            NodeKind::Ni => 1,
            NodeKind::Root => 2,
            NodeKind::Tree => 3,
            NodeKind::Concrete => 4,
        }
    };
    (
        kind,
        node.nominal_level.unwrap_or(1 << 31),
        node.creation_id,
    )
}

fn dependency_rank(value: &DependencySet) -> (usize, Option<u32>, Vec<u32>) {
    (
        value.as_slice().len(),
        value.maximum(),
        value.as_slice().iter().rev().copied().collect(),
    )
}

fn dependency_bits_cmp(left: &DependencySet, right: &DependencySet) -> Ordering {
    left.as_slice()
        .iter()
        .rev()
        .cmp(right.as_slice().iter().rev())
}

fn sort_dependencies(values: &mut [DependencySet]) {
    values.sort_by(dependency_bits_cmp);
}

fn select_clash<'a>(current: &'a Clash, candidate: &'a Clash) -> &'a Clash {
    if current.dependency.is_subset_of(&candidate.dependency) {
        return current;
    }
    if candidate.dependency.is_subset_of(&current.dependency) {
        return candidate;
    }
    if clash_rank(current) <= clash_rank(candidate) {
        current
    } else {
        candidate
    }
}

type ClashRank<'a> = (
    usize,
    Option<u32>,
    Vec<u32>,
    &'a str,
    &'a [u32],
    Option<u32>,
);

fn clash_rank(clash: &Clash) -> ClashRank<'_> {
    (
        clash.dependency.as_slice().len(),
        clash.dependency.maximum(),
        clash.dependency.as_slice().iter().rev().copied().collect(),
        clash.kind.as_str(),
        clash.participants.as_slice(),
        clash.provenance_id,
    )
}

fn is_clash_kind(value: &str) -> bool {
    matches!(
        value,
        "bottom"
            | "empty_head"
            | "positive_negative_atom"
            | "equality_inequality"
            | "irreflexive_role"
            | "asymmetric_role"
            | "disjoint_roles"
            | "impossible_cardinality"
            | "datatype_unsatisfiable"
    )
}

fn integer_queue_values(queue: &StableQueue) -> Vec<u32> {
    queue
        .values()
        .filter_map(|value| match value {
            QueueValue::Integer(value) => Some(*value),
            QueueValue::Node(_) => None,
        })
        .collect()
}

fn node_queue_values(queue: &StableQueue) -> Vec<Value> {
    queue
        .values()
        .filter_map(|value| match value {
            QueueValue::Node(value) => Some(handle_value(*value)),
            QueueValue::Integer(_) => None,
        })
        .collect()
}

fn is_unique(values: &[u32]) -> bool {
    values.iter().copied().collect::<BTreeSet<_>>().len() == values.len()
}

fn handle_value(handle: NodeHandle) -> Value {
    json!([handle.slot, handle.generation])
}

const fn lifecycle_name(value: NodeLifecycle) -> &'static str {
    match value {
        NodeLifecycle::Active => "active",
        NodeLifecycle::Merged => "merged",
        NodeLifecycle::Pruned => "pruned",
        NodeLifecycle::Retired => "retired",
    }
}

const fn sort_name(value: NodeSort) -> &'static str {
    match value {
        NodeSort::Object => "object",
        NodeSort::Data => "data",
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::blocking::{
        AssignmentChange, BlockingAssignment, BlockingError, BlockingStateMutate, BlockingStateRead,
    };

    #[test]
    fn stale_handle_never_revives_after_slot_reuse() -> NativeResult<()> {
        let mut kernel = TableauKernel::new();
        let first = kernel.create_node(NodeKind::Root, None, false, None, None, None)?;
        kernel.retire_node(first)?;
        let second = kernel.create_node(NodeKind::Root, None, false, None, None, None)?;
        assert_eq!(first.slot, second.slot);
        assert!(second.generation > first.generation);
        assert!(kernel.require_node(first).is_err());
        kernel.check_invariants()
    }

    #[test]
    fn branch_rollback_restores_multiple_supports_and_generations() -> NativeResult<()> {
        let mut kernel = TableauKernel::new();
        let node = kernel.create_node(NodeKind::Root, None, false, None, None, None)?;
        kernel.add_fact(1, vec![node], DependencySet::empty(), false, None)?;
        kernel.push_branch("merge".to_owned(), vec![1, 2], 0, DependencySet::empty())?;
        kernel.add_fact(2, vec![node], DependencySet::new(vec![0])?, true, None)?;
        let abandoned = kernel.create_node(NodeKind::Tree, Some(node), false, None, None, None)?;
        kernel.backtrack_to(0)?;
        let replacement =
            kernel.create_node(NodeKind::Tree, Some(node), false, None, None, None)?;
        assert_eq!(replacement.slot, abandoned.slot);
        assert_eq!(replacement.generation, 2);
        kernel.check_invariants()
    }

    #[test]
    fn invalid_merge_and_referenced_retirement_leave_state_unchanged() -> NativeResult<()> {
        let mut kernel = TableauKernel::new();
        let left = kernel.create_node(NodeKind::Root, None, false, None, None, None)?;
        let right = kernel.create_node(NodeKind::Root, None, false, None, None, None)?;
        kernel.add_fact(1, vec![left], DependencySet::empty(), false, None)?;
        kernel.push_branch("merge".to_owned(), vec![1, 2], 0, DependencySet::empty())?;
        let before = kernel.canonical_snapshot()?;

        assert!(kernel
            .merge_nodes(left, right, DependencySet::new(vec![1])?)
            .is_err());
        assert_eq!(kernel.canonical_snapshot()?, before);
        assert!(kernel.retire_node(left).is_err());
        assert_eq!(kernel.canonical_snapshot()?, before);
        Ok(())
    }

    #[test]
    fn predicate_and_position_indexes_track_creation_and_deactivation() -> NativeResult<()> {
        let mut kernel = TableauKernel::new();
        let left = kernel.create_node(NodeKind::Root, None, false, None, None, None)?;
        let right = kernel.create_node(NodeKind::Root, None, false, None, None, None)?;
        let first = kernel.add_fact(7, vec![left, right], DependencySet::empty(), false, None)?;
        let second = kernel.add_fact(7, vec![right, left], DependencySet::empty(), false, None)?;
        kernel.add_fact(8, vec![left], DependencySet::empty(), false, None)?;

        assert_eq!(
            kernel.candidate_fact_ids(7, &BTreeMap::new())?,
            vec![first, second]
        );
        assert_eq!(
            kernel.candidate_fact_ids(7, &BTreeMap::from([(0, left)]))?,
            vec![first]
        );
        assert_eq!(
            kernel.candidate_fact_ids(7, &BTreeMap::from([(1, left)]))?,
            vec![second]
        );
        assert!(kernel
            .candidate_fact_ids(8, &BTreeMap::from([(0, right)]))?
            .is_empty());

        kernel.deactivate_fact(first)?;
        assert_eq!(
            kernel.candidate_fact_ids(7, &BTreeMap::new())?,
            vec![second]
        );
        kernel.check_invariants()
    }

    #[test]
    fn stronger_disjunction_support_tracks_live_branch_and_rolls_back() -> NativeResult<()> {
        let mut kernel = TableauKernel::new();
        kernel.push_branch("merge".to_owned(), vec![10, 11], 90, DependencySet::empty())?;
        let disjunction_id = kernel.add_disjunction(vec![20, 21], DependencySet::new(vec![0])?)?;
        kernel.take_disjunction()?;
        kernel.push_branch(
            "ground_disjunction".to_owned(),
            vec![20, 21],
            disjunction_id,
            DependencySet::new(vec![0])?,
        )?;

        assert!(kernel.strengthen_disjunction(disjunction_id, DependencySet::empty())?);
        assert!(kernel.branch(1)?.base_dependency.as_slice().is_empty());
        assert_eq!(
            kernel.branch_choices_for_source(disjunction_id),
            vec![(1, 20)]
        );

        assert_eq!(kernel.advance_branch(1, DependencySet::empty())?, Some(21));
        assert_eq!(
            kernel
                .disjunction(disjunction_id)?
                .base_dependency
                .as_slice(),
            &[0]
        );
        assert_eq!(kernel.branch(1)?.base_dependency.as_slice(), &[0]);
        kernel.check_invariants()
    }

    #[test]
    fn ground_branch_advance_retains_non_disjunction_base_support() -> NativeResult<()> {
        let mut kernel = TableauKernel::new();
        kernel.push_branch("merge".to_owned(), vec![10, 11], 90, DependencySet::empty())?;
        let disjunction_id = kernel.add_disjunction(vec![20, 21, 22], DependencySet::empty())?;
        kernel.take_disjunction()?;
        kernel.push_branch(
            "ground_disjunction".to_owned(),
            vec![20, 21],
            disjunction_id,
            DependencySet::new(vec![0])?,
        )?;

        assert_eq!(kernel.advance_branch(1, DependencySet::empty())?, Some(21));
        assert_eq!(kernel.branch(1)?.base_dependency.as_slice(), &[0]);
        assert_eq!(kernel.branch(1)?.initial_base_dependency.as_slice(), &[0]);
        kernel.check_invariants()
    }

    #[test]
    fn blocking_adapter_projects_and_applies_generation_safe_deltas() -> NativeResult<()> {
        let mut kernel = TableauKernel::new();
        let root = kernel.create_node(NodeKind::Root, None, false, None, None, None)?;
        let child = kernel.create_node(NodeKind::Tree, Some(root), false, None, None, None)?;
        kernel.mark_existential(child, 8, true)?;
        let row_id = kernel.add_fact(7, vec![child], DependencySet::empty(), false, None)?;

        let nodes = BlockingStateRead::node_records(&kernel)
            .map_err(|error| NativeError::invariant(error.to_string()))?;
        let child_record = nodes
            .iter()
            .find(|record| record.node == child)
            .ok_or_else(|| NativeError::invariant("blocking projection omitted a live node"))?;
        assert_eq!(child_record.key.slot, child.slot);
        assert_eq!(child_record.key.generation, child.generation);
        assert!(child_record.has_pending_existentials);
        let facts = BlockingStateRead::active_fact_records(&kernel)
            .map_err(|error| NativeError::invariant(error.to_string()))?;
        assert_eq!(facts.len(), 1);
        assert_eq!(facts[0].arguments, vec![child]);

        BlockingStateMutate::apply_assignment_change(
            &mut kernel,
            &AssignmentChange {
                node: child,
                before: None,
                after: Some(BlockingAssignment::direct(child, root)),
            },
        )
        .map_err(|error| NativeError::invariant(error.to_string()))?;
        assert_eq!(kernel.active_node(child)?.blocker, Some(root));
        assert!(kernel.active_node(child)?.directly_blocked);
        BlockingStateMutate::promote_core_fact(&mut kernel, row_id)
            .map_err(|error| NativeError::invariant(error.to_string()))?;
        assert!(kernel.fact(row_id)?.core);
        BlockingStateMutate::reschedule_existentials(&mut kernel, child)
            .map_err(|error| NativeError::invariant(error.to_string()))?;
        assert_eq!(
            node_queue_values(&kernel.state.existential_candidates),
            vec![handle_value(child)]
        );

        BlockingStateMutate::apply_assignment_change(
            &mut kernel,
            &AssignmentChange {
                node: child,
                before: Some(BlockingAssignment::direct(child, root)),
                after: Some(BlockingAssignment::cached(child)),
            },
        )
        .map_err(|error| NativeError::invariant(error.to_string()))?;
        assert_eq!(kernel.active_node(child)?.blocker, None);
        assert!(!kernel.active_node(child)?.directly_blocked);
        assert!(BlockingStateRead::revision(&kernel) > 0);
        kernel.check_invariants()
    }

    #[test]
    fn blocking_adapter_atomic_error_restores_every_kernel_mutation() -> NativeResult<()> {
        let mut kernel = TableauKernel::new();
        let root = kernel.create_node(NodeKind::Root, None, false, None, None, None)?;
        let child = kernel.create_node(NodeKind::Tree, Some(root), false, None, None, None)?;
        let before = kernel.canonical_snapshot()?;
        let outcome: Result<(), BlockingError> =
            BlockingStateMutate::blocking_atomic(&mut kernel, |state| {
                BlockingStateMutate::apply_assignment_change(
                    state,
                    &AssignmentChange {
                        node: child,
                        before: None,
                        after: Some(BlockingAssignment::direct(child, root)),
                    },
                )?;
                Err(BlockingError::invariant("forced adapter rollback"))
            });
        assert!(outcome.is_err());
        assert_eq!(kernel.canonical_snapshot()?, before);
        Ok(())
    }
}
