//! Native coarse reasoning services built over the transactional tableau session.
// SPDX-License-Identifier: LGPL-3.0-or-later

mod classification;

pub use classification::{
    classify_ids, ClassificationLimits, ClassificationMode, ClassificationProblem,
    ClassificationResult, ClassificationStatistics, HierarchyIds,
};

#[cfg(test)]
mod tests;
