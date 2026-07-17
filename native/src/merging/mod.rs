//! Dependency-exact object/data node merging above the rollback-safe state kernel.
// SPDX-License-Identifier: LGPL-3.0-or-later

use std::collections::BTreeMap;

use crate::cancel::CancellationState;
use crate::error::{NativeError, NativeResult};
use crate::model::{DependencySet, NodeHandle, NodeSort};
use crate::rules::{PredicateKind, RuleProgram, TermSort};
use crate::store::TableauKernel;

/// Canonical result of one equality consequence.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MergeResult {
    pub representative: NodeHandle,
    pub merged: Option<NodeHandle>,
    pub pruned: Vec<NodeHandle>,
    pub clashed: bool,
}

/// Program-specific merge semantics. The mutable state remains entirely query-local.
#[derive(Clone, Debug)]
pub struct MergingManager {
    inequality_by_sort: BTreeMap<TermSort, u32>,
}

impl MergingManager {
    pub fn new(program: &RuleProgram) -> NativeResult<Self> {
        let mut inequality_by_sort = BTreeMap::new();
        for predicate in program
            .predicates()
            .iter()
            .filter(|predicate| predicate.kind == PredicateKind::Inequality)
        {
            let sort = *predicate
                .argument_sorts
                .first()
                .ok_or_else(|| NativeError::invariant("inequality predicate has no sort"))?;
            if inequality_by_sort
                .insert(sort, predicate.predicate_id)
                .is_some()
            {
                return Err(NativeError::wire(
                    "a rule program cannot contain two inequalities for one term sort",
                ));
            }
        }
        Ok(Self { inequality_by_sort })
    }

    /// Merge two representatives, including the higher-level `HermiT` mechanics that
    /// are intentionally not owned by the generic state arena. Every sub-mutation is
    /// covered by one checkpoint, including cancellation at a child-pruning boundary.
    pub fn merge(
        &self,
        kernel: &mut TableauKernel,
        left: NodeHandle,
        right: NodeHandle,
        dependency: DependencySet,
        cancellation: Option<&CancellationState>,
    ) -> NativeResult<MergeResult> {
        poll(cancellation)?;
        kernel.atomic(|kernel| {
            let result = self.merge_inner(kernel, left, right, dependency, cancellation)?;
            poll(cancellation)?;
            Ok(result)
        })
    }

    fn merge_inner(
        &self,
        kernel: &mut TableauKernel,
        left: NodeHandle,
        right: NodeHandle,
        dependency: DependencySet,
        cancellation: Option<&CancellationState>,
    ) -> NativeResult<MergeResult> {
        let (left_rep, left_path) = kernel.canonical_handle(left)?;
        let (right_rep, right_path) = kernel.canonical_handle(right)?;
        let support = DependencySet::union(&[&dependency, &left_path, &right_path]);
        if left_rep == right_rep {
            return Ok(MergeResult {
                representative: left_rep,
                merged: None,
                pruned: Vec::new(),
                clashed: false,
            });
        }
        let sort = kernel.node_sort(left_rep)?;
        if kernel.node_sort(right_rep)? != sort {
            return Err(NativeError::invariant(
                "cannot merge object and concrete nodes",
            ));
        }
        if let Some(result) = self.inequality_clash(kernel, left_rep, right_rep, sort, &support)? {
            return Ok(result);
        }

        let (target, source) = kernel.merge_orientation(left_rep, right_rep)?;
        let children = kernel.direct_children(source)?;
        let pending = kernel
            .active_node(source)?
            .unprocessed_existentials
            .iter()
            .copied()
            .collect::<Vec<_>>();
        let mut pruned = Vec::new();
        for child in children {
            poll(cancellation)?;
            pruned.extend(kernel.prune_subtree(child)?);
        }
        for existential_id in pending {
            kernel.mark_existential(target, existential_id, true)?;
        }
        let representative = kernel.merge_nodes(source, target, support)?;
        if representative != target {
            return Err(NativeError::invariant(
                "state merge orientation changed after it was selected",
            ));
        }
        let rank = kernel.node_rank(target)?;
        if !kernel
            .active_node(target)?
            .unprocessed_existentials
            .is_empty()
        {
            kernel.enqueue_node("existential_candidates", target, rank_priority(rank))?;
        }
        kernel.enqueue_node("blocking_invalidations", target, rank_priority(rank))?;
        Ok(MergeResult {
            representative,
            merged: Some(source),
            pruned,
            clashed: false,
        })
    }

    fn inequality_clash(
        &self,
        kernel: &mut TableauKernel,
        left: NodeHandle,
        right: NodeHandle,
        sort: NodeSort,
        support: &DependencySet,
    ) -> NativeResult<Option<MergeResult>> {
        let term_sort = match sort {
            NodeSort::Object => TermSort::Object,
            NodeSort::Data => TermSort::Data,
        };
        let Some(predicate_id) = self.inequality_by_sort.get(&term_sort).copied() else {
            return Ok(None);
        };
        let (first, second) = if kernel.node_rank(left)? <= kernel.node_rank(right)? {
            (left, right)
        } else {
            (right, left)
        };
        let bindings = BTreeMap::from([(0_u32, first), (1_u32, second)]);
        let rows = kernel.candidate_fact_ids(predicate_id, &bindings)?;
        if rows.is_empty() {
            return Ok(None);
        }
        let mut dependencies = Vec::new();
        for row_id in &rows {
            dependencies.extend(kernel.fact(*row_id)?.supports.iter().cloned());
        }
        let inequality = dependencies
            .iter()
            .min_by_key(|value| dependency_rank(value))
            .ok_or_else(|| NativeError::invariant("inequality row has no dependency support"))?;
        let mut participants = rows;
        participants.sort_unstable();
        participants.dedup();
        kernel.install_clash(
            "equality_inequality".to_owned(),
            DependencySet::union(&[support, inequality]),
            participants,
            None,
        )?;
        Ok(Some(MergeResult {
            representative: left,
            merged: None,
            pruned: Vec::new(),
            clashed: true,
        }))
    }
}

fn poll(cancellation: Option<&CancellationState>) -> NativeResult<()> {
    cancellation.map_or(Ok(()), CancellationState::poll)
}

fn rank_priority(rank: (u32, u32, u32)) -> Vec<i64> {
    vec![i64::from(rank.0), i64::from(rank.1), i64::from(rank.2)]
}

fn dependency_rank(value: &DependencySet) -> (usize, Option<u32>, Vec<u32>) {
    (
        value.as_slice().len(),
        value.maximum(),
        value.as_slice().iter().rev().copied().collect(),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cancel::CancellationHandle;
    use crate::model::NodeKind;
    use crate::rules::RulePredicate;

    fn program() -> NativeResult<RuleProgram> {
        RuleProgram::new(
            vec![
                RulePredicate::new(0, PredicateKind::Concept, vec![TermSort::Object])?
                    .with_symbol_id(0),
                RulePredicate::new(
                    1,
                    PredicateKind::Equality,
                    vec![TermSort::Object, TermSort::Object],
                )?
                .with_opposite(2),
                RulePredicate::new(
                    2,
                    PredicateKind::Inequality,
                    vec![TermSort::Object, TermSort::Object],
                )?
                .with_opposite(1),
            ],
            Vec::new(),
        )
    }

    fn root(kernel: &mut TableauKernel, named: bool) -> NativeResult<NodeHandle> {
        kernel.create_node(NodeKind::Root, None, named, named.then_some(0), None, None)
    }

    #[test]
    fn merge_prunes_source_children_transfers_work_and_rewrites_rows() -> NativeResult<()> {
        let manager = MergingManager::new(&program()?)?;
        let mut kernel = TableauKernel::new();
        let target = root(&mut kernel, true)?;
        let source = root(&mut kernel, false)?;
        let child = kernel.create_node(NodeKind::Tree, Some(source), false, None, None, None)?;
        let grandchild =
            kernel.create_node(NodeKind::Tree, Some(child), false, None, None, None)?;
        let blocked = root(&mut kernel, false)?;
        kernel.set_blocked(blocked, Some(source), true)?;
        kernel.mark_existential(source, 99, true)?;
        kernel.add_fact(0, vec![source], DependencySet::empty(), true, Some(7))?;

        let result = manager.merge(&mut kernel, source, target, DependencySet::empty(), None)?;
        assert_eq!(result.representative, target);
        assert_eq!(result.merged, Some(source));
        assert_eq!(result.pruned, vec![grandchild, child]);
        assert!(!result.clashed);
        assert_eq!(kernel.canonical_handle(source)?.0, target);
        assert!(kernel.active_node(child).is_err());
        assert!(kernel.active_node(grandchild).is_err());
        assert_eq!(kernel.active_node(blocked)?.blocker, None);
        assert!(kernel
            .active_node(target)?
            .unprocessed_existentials
            .contains(&99));
        let rows = kernel.facts_for_node(target)?;
        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0].key.arguments, vec![target]);
        assert!(rows[0].core);
        assert!(rows[0].provenance_ids.contains(&7));
        kernel.check_invariants()
    }

    #[test]
    fn explicit_inequality_clashes_without_mutating_representatives() -> NativeResult<()> {
        let manager = MergingManager::new(&program()?)?;
        let mut kernel = TableauKernel::new();
        let left = root(&mut kernel, false)?;
        let right = root(&mut kernel, false)?;
        kernel.add_fact(
            2,
            vec![left, right],
            DependencySet::empty(),
            false,
            Some(11),
        )?;

        let result = manager.merge(&mut kernel, left, right, DependencySet::empty(), None)?;
        assert!(result.clashed);
        assert_eq!(result.merged, None);
        assert_eq!(kernel.canonical_handle(left)?.0, left);
        assert_eq!(kernel.canonical_handle(right)?.0, right);
        let clash = kernel
            .clash()
            .ok_or_else(|| NativeError::invariant("inequality did not install a clash"))?;
        assert_eq!(clash.kind, "equality_inequality");
        assert_eq!(clash.participants, vec![0]);
        kernel.check_invariants()
    }

    #[test]
    fn cancellation_leaves_the_compound_merge_bit_exact() -> NativeResult<()> {
        let manager = MergingManager::new(&program()?)?;
        let mut kernel = TableauKernel::new();
        let left = root(&mut kernel, false)?;
        let right = root(&mut kernel, false)?;
        let cancellation = CancellationHandle::from_options(None, None)?;
        cancellation
            .state()
            .interrupt(Some("stop merge".to_owned()))?;
        let before = kernel.canonical_snapshot()?;
        assert!(manager
            .merge(
                &mut kernel,
                left,
                right,
                DependencySet::empty(),
                Some(&cancellation.state()),
            )
            .is_err());
        assert_eq!(kernel.canonical_snapshot()?, before);
        Ok(())
    }
}
