//! Stable blocking values and the read-only tableau adapter contract.
// SPDX-License-Identifier: LGPL-3.0-or-later

use std::collections::BTreeSet;
use std::error::Error;
use std::fmt;

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum DirectCheckerKind {
    Single,
    Pairwise,
    ValidatedSingle,
    ValidatedPairwise,
}

impl DirectCheckerKind {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Single => "single",
            Self::Pairwise => "pairwise",
            Self::ValidatedSingle => "validated_single",
            Self::ValidatedPairwise => "validated_pairwise",
        }
    }

    #[must_use]
    pub const fn validated(self) -> bool {
        matches!(self, Self::ValidatedSingle | Self::ValidatedPairwise)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BlockingManagerKind {
    Ancestor,
    Anywhere,
    ValidatedAnywhere,
}

impl BlockingManagerKind {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Ancestor => "ancestor",
            Self::Anywhere => "anywhere",
            Self::ValidatedAnywhere => "validated_anywhere",
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CoreBlockingMode {
    None,
    Simple,
    Complex,
}

impl CoreBlockingMode {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::None => "none",
            Self::Simple => "simple",
            Self::Complex => "complex",
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BlockingMode {
    Auto,
    Ancestor,
    Anywhere,
    ValidatedAnywhere,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct BlockingRequirements {
    pub has_inverse_roles: bool,
    pub has_nominals: bool,
    pub requires_validated_core: bool,
    pub complex_core: bool,
    pub has_additional_ontology: bool,
    pub query_local_axioms: bool,
    pub direct_checker_kind: Option<DirectCheckerKind>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct BlockingPlan {
    pub manager_kind: BlockingManagerKind,
    pub direct_checker_kind: DirectCheckerKind,
    pub core_mode: CoreBlockingMode,
    pub cache_allowed: bool,
}

impl BlockingPlan {
    #[must_use]
    pub const fn validated(self) -> bool {
        matches!(self.manager_kind, BlockingManagerKind::ValidatedAnywhere)
    }
}

pub fn select_blocking_plan(
    mode: BlockingMode,
    requirements: BlockingRequirements,
) -> Result<BlockingPlan, BlockingError> {
    if requirements.complex_core && !requirements.requires_validated_core {
        return Err(BlockingError::invalid(
            "complex core blocking requires validated core blocking",
        ));
    }
    let validated = matches!(mode, BlockingMode::ValidatedAnywhere)
        || (matches!(mode, BlockingMode::Auto) && requirements.requires_validated_core);
    if validated {
        let direct_checker_kind = match requirements.direct_checker_kind {
            Some(DirectCheckerKind::Pairwise | DirectCheckerKind::ValidatedPairwise) => {
                DirectCheckerKind::ValidatedPairwise
            }
            _ => DirectCheckerKind::ValidatedSingle,
        };
        return Ok(BlockingPlan {
            manager_kind: BlockingManagerKind::ValidatedAnywhere,
            direct_checker_kind,
            core_mode: if requirements.complex_core {
                CoreBlockingMode::Complex
            } else {
                CoreBlockingMode::Simple
            },
            cache_allowed: false,
        });
    }
    if requirements
        .direct_checker_kind
        .is_some_and(DirectCheckerKind::validated)
    {
        return Err(BlockingError::invalid(
            "validated direct checkers require validated-anywhere blocking",
        ));
    }
    let direct_checker_kind =
        requirements
            .direct_checker_kind
            .unwrap_or(if requirements.has_inverse_roles {
                DirectCheckerKind::Pairwise
            } else {
                DirectCheckerKind::Single
            });
    Ok(BlockingPlan {
        manager_kind: if matches!(mode, BlockingMode::Ancestor) {
            BlockingManagerKind::Ancestor
        } else {
            BlockingManagerKind::Anywhere
        },
        direct_checker_kind,
        core_mode: CoreBlockingMode::None,
        cache_allowed: !requirements.has_nominals
            && !requirements.has_additional_ontology
            && !requirements.query_local_axioms,
    })
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct NodeKey {
    pub slot: u32,
    pub generation: u32,
}

impl NodeKey {
    #[must_use]
    pub const fn new(slot: u32, generation: u32) -> Self {
        Self { slot, generation }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NodeKind {
    Root,
    Tree,
    Ni,
    Concrete,
}

impl NodeKind {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Root => "root",
            Self::Tree => "tree",
            Self::Ni => "ni",
            Self::Concrete => "concrete",
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NodeLifecycle {
    Active,
    Merged,
    Pruned,
    Retired,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NodeRecord<N> {
    pub node: N,
    pub key: NodeKey,
    pub creation_id: u32,
    pub kind: NodeKind,
    pub lifecycle: NodeLifecycle,
    pub parent: Option<N>,
    pub has_pending_existentials: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FactRecord<N> {
    pub row_id: u32,
    pub predicate_id: u32,
    pub arguments: Vec<N>,
    pub core: bool,
    pub active: bool,
}

/// Read-only methods required from `TableauKernel`.
///
/// The adapter must return generation-safe handles, stable creation IDs, and
/// already-canonical active fact arguments.  Returning all arena records (not
/// only active records) lets the projection ignore merged/pruned/retired nodes
/// explicitly and makes stale-handle tests independent of kernel internals.
pub trait BlockingStateRead {
    type Node: Copy + fmt::Debug + Eq + Ord;

    fn revision(&self) -> u64;

    fn node_records(&self) -> Result<Vec<NodeRecord<Self::Node>>, BlockingError>;

    fn active_fact_records(&self) -> Result<Vec<FactRecord<Self::Node>>, BlockingError>;
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BlockingVocabulary {
    pub atomic_concepts: BTreeSet<u32>,
    pub atomic_object_roles: BTreeSet<u32>,
}

impl BlockingVocabulary {
    pub fn new(
        atomic_concepts: impl IntoIterator<Item = u32>,
        atomic_object_roles: impl IntoIterator<Item = u32>,
    ) -> Result<Self, BlockingError> {
        let atomic_concepts = atomic_concepts.into_iter().collect::<BTreeSet<_>>();
        let atomic_object_roles = atomic_object_roles.into_iter().collect::<BTreeSet<_>>();
        if !atomic_concepts.is_disjoint(&atomic_object_roles) {
            return Err(BlockingError::invalid(
                "concept and object-role predicate IDs must be disjoint",
            ));
        }
        Ok(Self {
            atomic_concepts,
            atomic_object_roles,
        })
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct BlockingAssignment<N> {
    pub node: N,
    pub blocker: Option<N>,
    pub directly: bool,
    pub from_cache: bool,
}

impl<N: Copy> BlockingAssignment<N> {
    #[must_use]
    pub const fn unblocked(node: N) -> Self {
        Self {
            node,
            blocker: None,
            directly: false,
            from_cache: false,
        }
    }

    #[must_use]
    pub const fn direct(node: N, blocker: N) -> Self {
        Self {
            node,
            blocker: Some(blocker),
            directly: true,
            from_cache: false,
        }
    }

    #[must_use]
    pub const fn indirect(node: N, parent: N) -> Self {
        Self {
            node,
            blocker: Some(parent),
            directly: false,
            from_cache: false,
        }
    }

    #[must_use]
    pub const fn cached(node: N) -> Self {
        Self {
            node,
            blocker: None,
            directly: true,
            from_cache: true,
        }
    }

    #[must_use]
    pub const fn blocked(self) -> bool {
        self.blocker.is_some() || self.from_cache
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BlockingErrorKind {
    InvalidInput,
    Cancelled,
    Resource,
    Invariant,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BlockingError {
    pub kind: BlockingErrorKind,
    pub message: String,
    pub limit: Option<&'static str>,
    pub observed: Option<u64>,
    pub allowed: Option<u64>,
}

impl BlockingError {
    #[must_use]
    pub fn invalid(message: impl Into<String>) -> Self {
        Self::new(BlockingErrorKind::InvalidInput, message)
    }

    #[must_use]
    pub fn cancelled(message: impl Into<String>) -> Self {
        Self::new(BlockingErrorKind::Cancelled, message)
    }

    #[must_use]
    pub fn invariant(message: impl Into<String>) -> Self {
        Self::new(BlockingErrorKind::Invariant, message)
    }

    #[must_use]
    pub fn resource(
        message: impl Into<String>,
        limit: &'static str,
        observed: u64,
        allowed: u64,
    ) -> Self {
        Self {
            kind: BlockingErrorKind::Resource,
            message: message.into(),
            limit: Some(limit),
            observed: Some(observed),
            allowed: Some(allowed),
        }
    }

    fn new(kind: BlockingErrorKind, message: impl Into<String>) -> Self {
        Self {
            kind,
            message: message.into(),
            limit: None,
            observed: None,
            allowed: None,
        }
    }
}

impl fmt::Display for BlockingError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.message)
    }
}

impl Error for BlockingError {}

pub trait BlockingControl {
    fn poll(&self) -> Result<(), BlockingError>;

    fn observe_memory(&self, _bytes: u64) -> Result<(), BlockingError> {
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, Default)]
pub struct NeverCancel;

impl BlockingControl for NeverCancel {
    fn poll(&self) -> Result<(), BlockingError> {
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct BlockingLimits {
    pub max_nodes: usize,
    pub max_facts: usize,
    pub max_candidate_checks: usize,
    pub max_validation_blocks: usize,
    pub cancellation_poll_interval: usize,
}

impl Default for BlockingLimits {
    fn default() -> Self {
        Self {
            max_nodes: 2_000_000,
            max_facts: 20_000_000,
            max_candidate_checks: 100_000_000,
            max_validation_blocks: 2_000_000,
            cancellation_poll_interval: 256,
        }
    }
}

impl BlockingLimits {
    pub fn validate(self) -> Result<Self, BlockingError> {
        if self.max_nodes == 0
            || self.max_facts == 0
            || self.max_candidate_checks == 0
            || self.max_validation_blocks == 0
            || self.cancellation_poll_interval == 0
        {
            return Err(BlockingError::invalid(
                "all blocking limits must be strictly positive",
            ));
        }
        Ok(self)
    }
}
