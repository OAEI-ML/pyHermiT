//! Python-independent minimum-cardinality satisfaction and witness expansion.
//!
//! This module intentionally depends only on `std` and three narrow adapter
//! traits.  WPR2 can therefore test the complete expansion algorithm against a
//! fake state before `TableauKernel`, `RuleEngine`, the datatype manager, and
//! the blocking manager are wired together.  All query-local reuse data lives
//! behind the state traits so a branch rollback restores strategy decisions as
//! well as tableau rows.
// SPDX-License-Identifier: LGPL-3.0-or-later

#![allow(
    clippy::manual_is_multiple_of,
    clippy::missing_errors_doc,
    clippy::module_name_repetitions,
    clippy::similar_names,
    clippy::too_many_lines
)]

mod distinct;
mod manager;
mod model;

pub use distinct::{pairwise_distinct_subset, DistinctSearchResult};
pub use manager::ExistentialExpansionManager;
pub use model::{
    AtLeastPredicate, BranchRecord, BranchTransition, CandidatePriority, CanonicalNode, ClashKind,
    ClashRecord, DependencySet, ExpansionControl, ExpansionError, ExpansionErrorKind,
    ExpansionLimits, ExpansionProgram, ExpansionResult, ExpansionRuleAccess,
    ExpansionStateMutation, ExpansionStateRead, ExpansionStatus, ExpansionStrategy, FactBinding,
    FactRecord, GroundAtom, NeverCancel, NodeKind, NodeRecord, NodeSort, ObligationKind,
    ReuseBranchRecord, RoleVocabulary,
};

#[cfg(test)]
mod tests;
