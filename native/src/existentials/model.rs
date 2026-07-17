//! Stable expansion values and the native adapter contracts.
// SPDX-License-Identifier: LGPL-3.0-or-later

use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fmt;

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum NodeSort {
    Data,
    Object,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum NodeKind {
    Root,
    Tree,
    Ni,
    Concrete,
}

impl NodeKind {
    #[must_use]
    pub const fn sort(self) -> NodeSort {
        match self {
            Self::Concrete => NodeSort::Data,
            Self::Root | Self::Tree | Self::Ni => NodeSort::Object,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum ObligationKind {
    Object,
    Data,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ExpansionStrategy {
    CreationOrder,
    IndividualReuse,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ExpansionStatus {
    NoWork,
    Blocked,
    Satisfied,
    Expanded,
    Clashed,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExpansionResult<N> {
    pub status: ExpansionStatus,
    pub root: Option<N>,
    pub existential_id: Option<u32>,
    pub witnesses: Vec<N>,
}

impl<N> ExpansionResult<N> {
    #[must_use]
    pub const fn idle(status: ExpansionStatus) -> Self {
        Self {
            status,
            root: None,
            existential_id: None,
            witnesses: Vec::new(),
        }
    }

    #[must_use]
    pub const fn for_obligation(
        status: ExpansionStatus,
        root: N,
        existential_id: u32,
        witnesses: Vec<N>,
    ) -> Self {
        Self {
            status,
            root: Some(root),
            existential_id: Some(existential_id),
            witnesses,
        }
    }
}

/// Immutable canonical branching-level support.
#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct DependencySet(Vec<u32>);

impl DependencySet {
    pub fn new(levels: Vec<u32>) -> Result<Self, ExpansionError> {
        if levels.windows(2).any(|pair| pair[0] >= pair[1]) {
            return Err(ExpansionError::invalid(
                "dependency levels must be ascending and unique",
            ));
        }
        Ok(Self(levels))
    }

    #[must_use]
    pub const fn empty() -> Self {
        Self(Vec::new())
    }

    #[must_use]
    pub fn as_slice(&self) -> &[u32] {
        &self.0
    }

    #[must_use]
    pub fn maximum(&self) -> Option<u32> {
        self.0.last().copied()
    }

    #[must_use]
    pub fn add(&self, level: u32) -> Self {
        let mut levels = self.0.clone();
        match levels.binary_search(&level) {
            Ok(_) => Self(levels),
            Err(position) => {
                levels.insert(position, level);
                Self(levels)
            }
        }
    }

    #[must_use]
    pub fn without(&self, level: u32) -> Self {
        let mut levels = self.0.clone();
        if let Ok(position) = levels.binary_search(&level) {
            levels.remove(position);
        }
        Self(levels)
    }

    #[must_use]
    pub fn union(values: &[&Self]) -> Self {
        let mut levels = Vec::new();
        for value in values {
            levels.extend_from_slice(value.as_slice());
        }
        levels.sort_unstable();
        levels.dedup();
        Self(levels)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ExpansionLimits {
    pub max_witnesses_per_obligation: u32,
    pub max_distinct_search_steps: u64,
    pub cancellation_interval: u64,
}

impl ExpansionLimits {
    pub fn new(
        max_witnesses_per_obligation: u32,
        max_distinct_search_steps: u64,
        cancellation_interval: u64,
    ) -> Result<Self, ExpansionError> {
        if max_witnesses_per_obligation == 0
            || max_distinct_search_steps == 0
            || cancellation_interval == 0
        {
            return Err(ExpansionError::invalid(
                "expansion limits must be strictly positive",
            ));
        }
        Ok(Self {
            max_witnesses_per_obligation,
            max_distinct_search_steps,
            cancellation_interval,
        })
    }
}

impl Default for ExpansionLimits {
    fn default() -> Self {
        Self {
            max_witnesses_per_obligation: 1_000_000,
            max_distinct_search_steps: 10_000_000,
            cancellation_interval: 256,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ExpansionErrorKind {
    InvalidInput,
    Cancelled,
    Resource,
    Invariant,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExpansionError {
    pub kind: ExpansionErrorKind,
    pub message: String,
    pub limit: Option<&'static str>,
    pub observed: Option<u64>,
    pub allowed: Option<u64>,
}

impl ExpansionError {
    #[must_use]
    pub fn invalid(message: impl Into<String>) -> Self {
        Self::new(ExpansionErrorKind::InvalidInput, message)
    }

    #[must_use]
    pub fn cancelled(message: impl Into<String>) -> Self {
        Self::new(ExpansionErrorKind::Cancelled, message)
    }

    #[must_use]
    pub fn invariant(message: impl Into<String>) -> Self {
        Self::new(ExpansionErrorKind::Invariant, message)
    }

    #[must_use]
    pub fn resource(
        message: impl Into<String>,
        limit: &'static str,
        observed: u64,
        allowed: u64,
    ) -> Self {
        Self {
            kind: ExpansionErrorKind::Resource,
            message: message.into(),
            limit: Some(limit),
            observed: Some(observed),
            allowed: Some(allowed),
        }
    }

    fn new(kind: ExpansionErrorKind, message: impl Into<String>) -> Self {
        Self {
            kind,
            message: message.into(),
            limit: None,
            observed: None,
            allowed: None,
        }
    }
}

impl fmt::Display for ExpansionError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.message)
    }
}

impl Error for ExpansionError {}

/// Cooperative cancellation/work accounting used inside combinatorial search
/// and at every witness mutation boundary.
pub trait ExpansionControl {
    fn poll(&mut self) -> Result<(), ExpansionError>;

    fn add_work(&mut self, amount: u64) -> Result<(), ExpansionError> {
        let _ = amount;
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, Default)]
pub struct NeverCancel;

impl ExpansionControl for NeverCancel {
    fn poll(&mut self) -> Result<(), ExpansionError> {
        Ok(())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AtLeastPredicate {
    pub predicate_id: u32,
    pub kind: ObligationKind,
    pub cardinality: u32,
    pub role_ids: Vec<u32>,
    pub filler_predicate_id: u32,
    /// True only for a public, nongenerated atomic object-class filler.
    pub reusable_filler: bool,
}

impl AtLeastPredicate {
    #[must_use]
    pub fn object(
        predicate_id: u32,
        cardinality: u32,
        role_id: u32,
        filler_predicate_id: u32,
    ) -> Self {
        Self {
            predicate_id,
            kind: ObligationKind::Object,
            cardinality,
            role_ids: vec![role_id],
            filler_predicate_id,
            reusable_filler: false,
        }
    }

    #[must_use]
    pub const fn data(
        predicate_id: u32,
        cardinality: u32,
        role_ids: Vec<u32>,
        filler_predicate_id: u32,
    ) -> Self {
        Self {
            predicate_id,
            kind: ObligationKind::Data,
            cardinality,
            role_ids,
            filler_predicate_id,
            reusable_filler: false,
        }
    }

    #[must_use]
    pub const fn with_reusable_filler(mut self, reusable: bool) -> Self {
        self.reusable_filler = reusable;
        self
    }

    pub(crate) fn validate(&self) -> Result<(), ExpansionError> {
        match self.kind {
            ObligationKind::Object if self.role_ids.len() != 1 => Err(ExpansionError::invalid(
                "an object at-least predicate requires exactly one role",
            )),
            ObligationKind::Data if self.role_ids.is_empty() => Err(ExpansionError::invalid(
                "a data at-least predicate requires at least one role",
            )),
            ObligationKind::Data if self.role_ids.len() > 1 && self.cardinality != 1 => Err(
                ExpansionError::invalid("an n-ary data existential must have cardinality one"),
            ),
            _ => Ok(()),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RoleVocabulary {
    pub object_role_predicates: BTreeMap<u32, u32>,
    pub data_role_predicates: BTreeMap<u32, u32>,
    pub top_object_role_id: u32,
    pub bottom_object_role_id: u32,
    pub top_data_role_id: u32,
    pub bottom_data_role_id: u32,
    pub object_inequality_predicate_id: Option<u32>,
    pub data_inequality_predicate_id: Option<u32>,
}

impl RoleVocabulary {
    pub fn validate(&self) -> Result<(), ExpansionError> {
        if self.top_object_role_id == self.bottom_object_role_id
            || self.top_data_role_id == self.bottom_data_role_id
        {
            return Err(ExpansionError::invalid(
                "top and bottom roles must have distinct identifiers",
            ));
        }
        Ok(())
    }

    #[must_use]
    pub fn role_predicate(&self, sort: NodeSort, role_id: u32) -> Option<u32> {
        match sort {
            NodeSort::Object => self.object_role_predicates.get(&role_id).copied(),
            NodeSort::Data => self.data_role_predicates.get(&role_id).copied(),
        }
    }

    #[must_use]
    pub const fn inequality_predicate(&self, sort: NodeSort) -> Option<u32> {
        match sort {
            NodeSort::Object => self.object_inequality_predicate_id,
            NodeSort::Data => self.data_inequality_predicate_id,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExpansionProgram {
    obligations: BTreeMap<u32, AtLeastPredicate>,
    roles: RoleVocabulary,
}

impl ExpansionProgram {
    pub fn new(
        obligations: impl IntoIterator<Item = AtLeastPredicate>,
        roles: RoleVocabulary,
    ) -> Result<Self, ExpansionError> {
        roles.validate()?;
        let mut indexed = BTreeMap::new();
        for obligation in obligations {
            obligation.validate()?;
            let predicate_id = obligation.predicate_id;
            if indexed.insert(predicate_id, obligation).is_some() {
                return Err(ExpansionError::invalid(
                    "existential predicate identifiers must be unique",
                ));
            }
        }
        let program = Self {
            obligations: indexed,
            roles,
        };
        program.validate_role_links()?;
        Ok(program)
    }

    #[must_use]
    pub fn obligation(&self, predicate_id: u32) -> Option<&AtLeastPredicate> {
        self.obligations.get(&predicate_id)
    }

    #[must_use]
    pub const fn roles(&self) -> &RoleVocabulary {
        &self.roles
    }

    fn validate_role_links(&self) -> Result<(), ExpansionError> {
        for obligation in self.obligations.values() {
            let sort = match obligation.kind {
                ObligationKind::Object => NodeSort::Object,
                ObligationKind::Data => NodeSort::Data,
            };
            for role_id in &obligation.role_ids {
                let special = match sort {
                    NodeSort::Object => {
                        *role_id == self.roles.top_object_role_id
                            || *role_id == self.roles.bottom_object_role_id
                    }
                    NodeSort::Data => {
                        *role_id == self.roles.top_data_role_id
                            || *role_id == self.roles.bottom_data_role_id
                    }
                };
                if !special && self.roles.role_predicate(sort, *role_id).is_none() {
                    return Err(ExpansionError::invalid(
                        "an existential role has no extension predicate",
                    ));
                }
            }
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct CandidatePriority {
    pub creation_id: u32,
    pub slot: u32,
    pub generation: u32,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NodeRecord<N> {
    pub node: N,
    pub priority: CandidatePriority,
    pub kind: NodeKind,
    pub parent: Option<N>,
    pub pending_existentials: BTreeSet<u32>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CanonicalNode<N> {
    pub node: N,
    pub dependency: DependencySet,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct FactBinding<N> {
    pub position: u32,
    pub node: N,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FactRecord<N> {
    pub row_id: u32,
    pub predicate_id: u32,
    pub arguments: Vec<N>,
    pub supports: Vec<DependencySet>,
    pub core: bool,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct GroundAtom<N> {
    pub predicate_id: u32,
    pub arguments: Vec<N>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ClashKind {
    ImpossibleCardinality,
    EmptyHead,
    Other,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ClashRecord {
    pub kind: ClashKind,
    pub dependency: DependencySet,
    pub details: Vec<u32>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BranchRecord {
    pub level: u32,
    pub base_dependency: DependencySet,
    pub learned_dependency: DependencySet,
    pub current_alternative: u32,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReuseBranchRecord<N> {
    pub level: u32,
    pub root: N,
    pub predicate_id: u32,
    pub supports: Vec<DependencySet>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BranchTransition {
    NoWork,
    Unsat,
    Advanced,
    Exhausted,
}

/// Read-only state required by the expansion kernel.
///
/// `is_blocked` is deliberately a coarse semantic query.  Its runtime adapter
/// must combine a live kernel blocker with a cache-derived block retained by
/// the blocking manager.
pub trait ExpansionStateRead {
    type Node: Copy + fmt::Debug + Eq + Ord;

    fn candidate_count(&self) -> Result<usize, ExpansionError>;

    fn node_record(
        &self,
        node: Self::Node,
    ) -> Result<Option<NodeRecord<Self::Node>>, ExpansionError>;

    fn canonical_node(
        &self,
        node: Self::Node,
    ) -> Result<Option<CanonicalNode<Self::Node>>, ExpansionError>;

    fn active_nodes(&self) -> Result<Vec<NodeRecord<Self::Node>>, ExpansionError>;

    fn is_blocked(&self, node: Self::Node) -> Result<bool, ExpansionError>;

    fn facts(
        &self,
        predicate_id: u32,
        bindings: &[FactBinding<Self::Node>],
    ) -> Result<Vec<FactRecord<Self::Node>>, ExpansionError>;

    fn current_clash(&self) -> Result<Option<ClashRecord>, ExpansionError>;

    fn branch(&self, level: u32) -> Result<Option<BranchRecord>, ExpansionError>;

    fn reuse_branch(
        &self,
        level: u32,
    ) -> Result<Option<ReuseBranchRecord<Self::Node>>, ExpansionError>;

    fn reuse_node(&self, filler_predicate_id: u32) -> Result<Option<Self::Node>, ExpansionError>;

    fn reuse_disabled(&self, predicate_id: u32) -> Result<bool, ExpansionError>;
}

/// Trailed mutations required by expansion.  A checkpoint covers facts,
/// queues, nodes, branches, clashes, and all reuse maps queried above.
pub trait ExpansionStateMutation: ExpansionStateRead {
    type Checkpoint;

    fn checkpoint(&self) -> Result<Self::Checkpoint, ExpansionError>;

    fn restore(&mut self, checkpoint: Self::Checkpoint) -> Result<(), ExpansionError>;

    fn pop_candidate(&mut self) -> Result<Option<Self::Node>, ExpansionError>;

    fn enqueue_candidate(
        &mut self,
        node: Self::Node,
        priority: CandidatePriority,
    ) -> Result<(), ExpansionError>;

    fn create_node(
        &mut self,
        kind: NodeKind,
        parent: Option<Self::Node>,
    ) -> Result<Self::Node, ExpansionError>;

    fn mark_processed(&mut self, node: Self::Node, predicate_id: u32)
        -> Result<(), ExpansionError>;

    fn install_clash(&mut self, clash: ClashRecord) -> Result<(), ExpansionError>;

    /// Install the reuse record before taking the branch checkpoint, then push
    /// alternatives `[0, 1]`.  This makes the record survive branch advance.
    fn push_reuse_branch(
        &mut self,
        root: Self::Node,
        predicate_id: u32,
        supports: Vec<DependencySet>,
        base_dependency: DependencySet,
    ) -> Result<BranchRecord, ExpansionError>;

    fn advance_reuse_branch(
        &mut self,
        level: u32,
        learned_dependency: DependencySet,
    ) -> Result<Option<u32>, ExpansionError>;

    fn remove_reuse_branch(&mut self, level: u32) -> Result<(), ExpansionError>;

    fn set_reuse_node(
        &mut self,
        filler_predicate_id: u32,
        node: Self::Node,
    ) -> Result<(), ExpansionError>;

    fn remove_reuse_node(&mut self, filler_predicate_id: u32) -> Result<(), ExpansionError>;

    fn set_reuse_disabled(
        &mut self,
        predicate_id: u32,
        disabled: bool,
    ) -> Result<(), ExpansionError>;
}

/// Rule/datatype services kept separate from the tableau store.  Dispatch and
/// node registration mutate only `state`, so its checkpoint remains the single
/// rollback authority.
pub trait ExpansionRuleAccess<S: ExpansionStateMutation> {
    fn dispatch_ground_atom(
        &mut self,
        state: &mut S,
        atom: GroundAtom<S::Node>,
        dependency: DependencySet,
        core: bool,
    ) -> Result<bool, ExpansionError>;

    fn register_node(
        &mut self,
        state: &mut S,
        node: S::Node,
        dependency: DependencySet,
    ) -> Result<(), ExpansionError>;

    fn data_values_known_different(
        &self,
        state: &S,
        left: S::Node,
        right: S::Node,
    ) -> Result<bool, ExpansionError>;

    fn data_value_satisfies<C: ExpansionControl>(
        &mut self,
        state: &S,
        node: S::Node,
        predicate_id: u32,
        control: &mut C,
    ) -> Result<bool, ExpansionError>;
}
