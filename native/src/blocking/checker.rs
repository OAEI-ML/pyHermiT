//! Exact single, pairwise, and validated direct blocking checkers.
// SPDX-License-Identifier: LGPL-3.0-or-later

use std::fmt;

use super::model::{BlockingError, BlockingVocabulary, DirectCheckerKind, NodeKind, NodeLifecycle};
use super::projection::{BlockingProjection, BlockingSignature};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DirectChecker {
    kind: DirectCheckerKind,
    vocabulary: BlockingVocabulary,
    has_inverses: bool,
}

impl DirectChecker {
    pub fn new(
        kind: DirectCheckerKind,
        vocabulary: BlockingVocabulary,
        has_inverses: bool,
    ) -> Result<Self, BlockingError> {
        if has_inverses && matches!(kind, DirectCheckerKind::Single) {
            return Err(BlockingError::invalid(
                "single direct blocking is unsound when inverse roles are enabled",
            ));
        }
        Ok(Self {
            kind,
            vocabulary,
            has_inverses,
        })
    }

    #[must_use]
    pub const fn kind(&self) -> DirectCheckerKind {
        self.kind
    }

    #[must_use]
    pub const fn has_inverses(&self) -> bool {
        self.has_inverses
    }

    #[must_use]
    pub const fn vocabulary(&self) -> &BlockingVocabulary {
        &self.vocabulary
    }

    #[must_use]
    pub fn can_be_blocker<N: Copy + fmt::Debug + Eq + Ord>(
        &self,
        projection: &BlockingProjection<N>,
        node: N,
    ) -> bool {
        self.eligible(projection, node)
    }

    #[must_use]
    pub fn can_be_blocked<N: Copy + fmt::Debug + Eq + Ord>(
        &self,
        projection: &BlockingProjection<N>,
        node: N,
    ) -> bool {
        self.eligible(projection, node)
    }

    pub fn signature<N: Copy + fmt::Debug + Eq + Ord>(
        &self,
        projection: &BlockingProjection<N>,
        node: N,
    ) -> Result<BlockingSignature, BlockingError> {
        if !self.can_be_blocked(projection, node) {
            return Err(BlockingError::invalid(
                "node is not eligible for the selected direct blocking checker",
            ));
        }
        let concepts = projection.concept_label(node, false).to_vec();
        match self.kind {
            DirectCheckerKind::Single => BlockingSignature::new(
                self.kind,
                concepts.clone(),
                Vec::new(),
                Vec::new(),
                Vec::new(),
                concepts,
                Vec::new(),
                Vec::new(),
                Vec::new(),
            ),
            DirectCheckerKind::Pairwise => {
                let parent = Self::parent(projection, node)?;
                let parent_concepts = projection.concept_label(parent, false).to_vec();
                let from_parent = projection.role_label(parent, node, false).to_vec();
                let to_parent = projection.role_label(node, parent, false).to_vec();
                BlockingSignature::new(
                    self.kind,
                    concepts.clone(),
                    parent_concepts.clone(),
                    from_parent.clone(),
                    to_parent.clone(),
                    concepts,
                    parent_concepts,
                    from_parent,
                    to_parent,
                )
            }
            DirectCheckerKind::ValidatedSingle => {
                let parent = Self::parent(projection, node)?;
                BlockingSignature::new(
                    self.kind,
                    projection.concept_label(node, true).to_vec(),
                    Vec::new(),
                    Vec::new(),
                    Vec::new(),
                    concepts,
                    projection.concept_label(parent, false).to_vec(),
                    projection.role_label(parent, node, false).to_vec(),
                    projection.role_label(node, parent, false).to_vec(),
                )
            }
            DirectCheckerKind::ValidatedPairwise => {
                let parent = Self::parent(projection, node)?;
                BlockingSignature::new(
                    self.kind,
                    projection.concept_label(node, true).to_vec(),
                    projection.concept_label(parent, true).to_vec(),
                    Vec::new(),
                    Vec::new(),
                    concepts,
                    projection.concept_label(parent, false).to_vec(),
                    projection.role_label(parent, node, false).to_vec(),
                    projection.role_label(node, parent, false).to_vec(),
                )
            }
        }
    }

    pub fn is_blocked_by<N: Copy + fmt::Debug + Eq + Ord>(
        &self,
        projection: &BlockingProjection<N>,
        blocker: N,
        blocked: N,
    ) -> Result<bool, BlockingError> {
        if !self.can_be_blocker(projection, blocker) || !self.can_be_blocked(projection, blocked) {
            return Ok(false);
        }
        let blocker_record = projection
            .node(blocker)
            .ok_or_else(|| BlockingError::invariant("eligible blocker is absent"))?;
        let blocked_record = projection
            .node(blocked)
            .ok_or_else(|| BlockingError::invariant("eligible blockee is absent"))?;
        if blocker_record.creation_id >= blocked_record.creation_id
            || projection.is_ancestor(blocked, blocker)
        {
            return Ok(false);
        }
        Ok(self
            .signature(projection, blocker)?
            .blocks(&self.signature(projection, blocked)?))
    }

    fn eligible<N: Copy + fmt::Debug + Eq + Ord>(
        &self,
        projection: &BlockingProjection<N>,
        node: N,
    ) -> bool {
        let Some(record) = projection.node(node) else {
            return false;
        };
        if record.lifecycle != NodeLifecycle::Active || record.kind != NodeKind::Tree {
            return false;
        }
        let needs_tree_parent = matches!(self.kind, DirectCheckerKind::Pairwise)
            || (self.kind.validated() && self.has_inverses);
        if !needs_tree_parent {
            return true;
        }
        record
            .parent
            .and_then(|parent| projection.node(parent))
            .is_some_and(|parent| {
                parent.lifecycle == NodeLifecycle::Active && parent.kind == NodeKind::Tree
            })
    }

    fn parent<N: Copy + fmt::Debug + Eq + Ord>(
        projection: &BlockingProjection<N>,
        node: N,
    ) -> Result<N, BlockingError> {
        projection
            .node(node)
            .and_then(|record| record.parent)
            .ok_or_else(|| BlockingError::invariant("tree blocking signature requires a parent"))
    }
}
