//! Native coarse reasoning services built over the transactional tableau session.
// SPDX-License-Identifier: LGPL-3.0-or-later

mod classification;
mod realization;

pub use classification::{
    classify_ids, ClassificationLimits, ClassificationMode, ClassificationProblem,
    ClassificationResult, ClassificationStatistics, HierarchyIds,
};
pub use realization::{
    build_realization_ids, realize_cached, CompletedModelAccess, DataTargetFact, DifferentFromFact,
    DirectTypeFact, ModelIndividual, NamedIndividualRecord, ObjectTargetFact, RealizationCache,
    RealizationCacheDisposition, RealizationCacheKey, RealizationCacheOperation, RealizationIds,
    RealizationLimits, RealizationResult, RealizationStatistics,
};

#[cfg(test)]
mod realization_tests;
#[cfg(test)]
mod tests;
