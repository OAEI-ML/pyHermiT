//! Python-independent tableau blocking.
//!
//! The module deliberately depends only on `std` and a narrow read-only state
//! trait.  This lets WPR2 exercise the complete blocking algorithm with a fake
//! state before `TableauKernel` owns the adapter.  Mutation is returned as
//! deterministic deltas; the eventual kernel adapter applies those deltas in
//! the same atomic operation as the manager checkpoint.
// SPDX-License-Identifier: LGPL-3.0-or-later

// Blocking terminology necessarily pairs names such as blocker/blockee, and
// immutable configuration records intentionally mirror boolean ontology
// feature flags. Error behavior is documented at the subsystem boundary.
#![allow(
    clippy::manual_is_multiple_of,
    clippy::missing_errors_doc,
    clippy::similar_names,
    clippy::struct_excessive_bools,
    clippy::too_many_lines
)]

mod cache;
mod checker;
mod compiled;
mod manager;
mod model;
mod projection;
mod sha256;
mod validation;

pub use cache::{
    BlockingCacheNamespace, BlockingSignatureCache, CachePromotion, CachePromotionContext,
};
pub use checker::DirectChecker;
pub(crate) use compiled::CompiledClauseBlockingValidator;
pub use manager::{
    full_recompute, AssignmentChange, BlockingCheckpoint, BlockingEvent, BlockingManager,
    BlockingStateMutate, BlockingTraceEvent, ComputeResult, ComputeStats,
};
pub use model::{
    select_blocking_plan, BlockingAssignment, BlockingControl, BlockingError, BlockingErrorKind,
    BlockingLimits, BlockingManagerKind, BlockingMode, BlockingPlan, BlockingRequirements,
    BlockingStateRead, BlockingVocabulary, CoreBlockingMode, DirectCheckerKind, FactRecord,
    NeverCancel, NodeKey, NodeKind, NodeLifecycle, NodeRecord,
};
pub use projection::{BlockingKey, BlockingProjection, BlockingSignature};
pub use validation::{BlockValidator, ValidationDecision, ValidationPassResult};

#[cfg(test)]
mod tests;
