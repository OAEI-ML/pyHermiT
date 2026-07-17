//! Ground-disjunction choice, dependency learning, and nonchronological backjumping.
// SPDX-License-Identifier: LGPL-3.0-or-later

use crate::cancel::CancellationState;
use crate::error::{NativeError, NativeResult};
use crate::model::DependencySet;
use crate::store::TableauKernel;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BranchTransition {
    NoWork,
    Satisfied,
    Deterministic,
    Branched,
    Advanced,
    Exhausted,
    Unsat,
}

pub(crate) trait GroundAtomAccess {
    fn atom_is_satisfied(&self, kernel: &TableauKernel, atom_id: u32) -> NativeResult<bool>;

    fn atom_refutation_dependency(
        &self,
        kernel: &TableauKernel,
        atom_id: u32,
    ) -> NativeResult<Option<DependencySet>>;

    fn dispatch_atom(
        &mut self,
        kernel: &mut TableauKernel,
        atom_id: u32,
        dependency: DependencySet,
    ) -> NativeResult<bool>;
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct DisjunctionBrancher {
    learning: bool,
}

impl DisjunctionBrancher {
    #[must_use]
    pub(crate) const fn new(learning: bool) -> Self {
        Self { learning }
    }

    #[must_use]
    pub(crate) const fn learning(self) -> bool {
        self.learning
    }

    pub(crate) fn process_next(
        kernel: &mut TableauKernel,
        access: &mut impl GroundAtomAccess,
        cancellation: &CancellationState,
    ) -> NativeResult<BranchTransition> {
        let result = Self::process_next_inner(kernel, access, cancellation);
        recover_on_error(kernel, result)
    }

    fn process_next_inner(
        kernel: &mut TableauKernel,
        access: &mut impl GroundAtomAccess,
        cancellation: &CancellationState,
    ) -> NativeResult<BranchTransition> {
        cancellation.poll()?;
        let Some(disjunction_id) = kernel.take_disjunction()? else {
            cancellation.poll()?;
            return Ok(BranchTransition::NoWork);
        };
        let record = kernel.disjunction(disjunction_id)?.clone();
        for atom_id in &record.disjunct_ids {
            cancellation.poll()?;
            if access.atom_is_satisfied(kernel, *atom_id)? {
                cancellation.poll()?;
                return Ok(BranchTransition::Satisfied);
            }
        }

        let mut remaining = Vec::new();
        let mut dependencies = vec![record.base_dependency];
        for atom_id in record.disjunct_ids {
            cancellation.poll()?;
            if let Some(refutation) = access.atom_refutation_dependency(kernel, atom_id)? {
                dependencies.push(refutation);
            } else {
                remaining.push(atom_id);
            }
        }
        let dependency_refs: Vec<_> = dependencies.iter().collect();
        let combined = DependencySet::union(&dependency_refs);
        match remaining.as_slice() {
            [] => {
                kernel.install_clash(
                    "empty_head".to_owned(),
                    combined,
                    vec![disjunction_id],
                    None,
                )?;
                cancellation.poll()?;
                Ok(BranchTransition::Deterministic)
            }
            [atom_id] => {
                access.dispatch_atom(kernel, *atom_id, combined)?;
                cancellation.poll()?;
                Ok(BranchTransition::Deterministic)
            }
            _ => {
                let level = kernel.push_branch(
                    "ground_disjunction".to_owned(),
                    remaining.clone(),
                    disjunction_id,
                    combined.clone(),
                )?;
                access.dispatch_atom(kernel, remaining[0], combined.add(level))?;
                cancellation.poll()?;
                Ok(BranchTransition::Branched)
            }
        }
    }

    pub(crate) fn resolve_clash(
        self,
        kernel: &mut TableauKernel,
        access: &mut impl GroundAtomAccess,
        cancellation: &CancellationState,
    ) -> NativeResult<BranchTransition> {
        let result = self.resolve_clash_inner(kernel, access, cancellation);
        recover_on_error(kernel, result)
    }

    fn resolve_clash_inner(
        self,
        kernel: &mut TableauKernel,
        access: &mut impl GroundAtomAccess,
        cancellation: &CancellationState,
    ) -> NativeResult<BranchTransition> {
        cancellation.poll()?;
        let Some(clash) = kernel.clash().cloned() else {
            return Ok(BranchTransition::NoWork);
        };
        let target = if self.learning {
            clash.dependency.maximum()
        } else {
            kernel.highest_branch_level()
        };
        let Some(target) = target else {
            return Ok(BranchTransition::Unsat);
        };
        let branch = kernel.branch(target)?.clone();
        let restored_base = branch.initial_base_dependency.clone();
        let without_level = clash.dependency.without(target);
        let alternative = kernel.advance_branch(target, without_level.clone())?;
        cancellation.poll()?;
        if let Some(atom_id) = alternative {
            let current = kernel.branch(target)?;
            access.dispatch_atom(kernel, atom_id, current.base_dependency.clone().add(target))?;
            cancellation.poll()?;
            return Ok(BranchTransition::Advanced);
        }

        let learned = DependencySet::union(&[&branch.learned_dependency, &without_level]);
        let propagated = DependencySet::union(&[&restored_base, &learned, &without_level]);
        kernel.install_clash(
            "empty_head".to_owned(),
            propagated,
            vec![branch.source_id],
            None,
        )?;
        cancellation.poll()?;
        Ok(BranchTransition::Exhausted)
    }

    pub(crate) fn resolve_until_choice_or_unsat(
        self,
        kernel: &mut TableauKernel,
        access: &mut impl GroundAtomAccess,
        cancellation: &CancellationState,
    ) -> NativeResult<BranchTransition> {
        loop {
            let transition = self.resolve_clash(kernel, access, cancellation)?;
            if transition != BranchTransition::Exhausted {
                return Ok(transition);
            }
        }
    }
}

fn recover_on_error<T>(kernel: &mut TableauKernel, result: NativeResult<T>) -> NativeResult<T> {
    match result {
        Ok(value) => Ok(value),
        Err(error) => {
            kernel.reset_to_operation_root().map_err(|reset_error| {
                NativeError::invariant(format!(
                    "branch operation recovery failed after {}: {reset_error}",
                    error.code
                ))
            })?;
            Err(error)
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;
    use std::sync::Arc;

    use crate::cancel::CancellationHandle;
    use crate::error::ErrorKind;
    use crate::model::{NodeHandle, NodeKind};

    use super::*;

    struct FactAccess {
        node: NodeHandle,
        refutations: BTreeMap<u32, DependencySet>,
        cancel_on_dispatch: Option<Arc<CancellationState>>,
    }

    impl FactAccess {
        fn new(node: NodeHandle) -> Self {
            Self {
                node,
                refutations: BTreeMap::new(),
                cancel_on_dispatch: None,
            }
        }

        fn dependency(
            &self,
            kernel: &TableauKernel,
            atom_id: u32,
        ) -> NativeResult<Option<DependencySet>> {
            let bindings = BTreeMap::from([(0, self.node)]);
            let mut supports = Vec::new();
            for row_id in kernel.candidate_fact_ids(atom_id, &bindings)? {
                let row = kernel.fact(row_id)?;
                supports.extend(row.supports.iter());
            }
            Ok(supports
                .into_iter()
                .min_by_key(|value| dependency_rank(value))
                .cloned())
        }
    }

    impl GroundAtomAccess for FactAccess {
        fn atom_is_satisfied(&self, kernel: &TableauKernel, atom_id: u32) -> NativeResult<bool> {
            Ok(self.dependency(kernel, atom_id)?.is_some())
        }

        fn atom_refutation_dependency(
            &self,
            _kernel: &TableauKernel,
            atom_id: u32,
        ) -> NativeResult<Option<DependencySet>> {
            Ok(self.refutations.get(&atom_id).cloned())
        }

        fn dispatch_atom(
            &mut self,
            kernel: &mut TableauKernel,
            atom_id: u32,
            dependency: DependencySet,
        ) -> NativeResult<bool> {
            let outcome =
                kernel.add_fact_detailed(atom_id, vec![self.node], dependency, false, None)?;
            if let Some(cancellation) = self.cancel_on_dispatch.take() {
                cancellation.interrupt(Some("injected branch cancellation".to_owned()))?;
            }
            Ok(outcome.created || outcome.support_changed)
        }
    }

    fn live_cancellation() -> NativeResult<Arc<CancellationState>> {
        Ok(CancellationHandle::from_options(None, None)?.state())
    }

    fn dependency_rank(value: &DependencySet) -> (usize, Option<u32>, Vec<u32>) {
        (
            value.as_slice().len(),
            value.maximum(),
            value.as_slice().iter().rev().copied().collect(),
        )
    }

    #[test]
    fn branch_advance_then_exhaustion_propagates_unsat() -> NativeResult<()> {
        let mut kernel = TableauKernel::new();
        let node = kernel.create_node(NodeKind::Root, None, false, None, None, None)?;
        kernel.begin_operation()?;
        kernel.add_disjunction(vec![10, 20], DependencySet::empty())?;
        let cancellation = live_cancellation()?;
        let mut access = FactAccess::new(node);
        let brancher = DisjunctionBrancher::new(true);

        assert_eq!(
            DisjunctionBrancher::process_next(&mut kernel, &mut access, &cancellation)?,
            BranchTransition::Branched
        );
        assert!(access.dependency(&kernel, 10)?.is_some());
        kernel.install_clash(
            "empty_head".to_owned(),
            DependencySet::new(vec![0])?,
            vec![101],
            None,
        )?;
        assert_eq!(
            brancher.resolve_clash(&mut kernel, &mut access, &cancellation)?,
            BranchTransition::Advanced
        );
        assert!(access.dependency(&kernel, 10)?.is_none());
        assert!(access.dependency(&kernel, 20)?.is_some());
        kernel.install_clash(
            "empty_head".to_owned(),
            DependencySet::new(vec![0])?,
            vec![102],
            None,
        )?;
        assert_eq!(
            brancher.resolve_until_choice_or_unsat(&mut kernel, &mut access, &cancellation,)?,
            BranchTransition::Unsat
        );
        assert!(kernel.highest_branch_level().is_none());
        assert!(kernel
            .clash()
            .is_some_and(|value| value.dependency.as_slice().is_empty()));
        kernel.check_invariants()
    }

    #[test]
    fn satisfied_refuted_and_unit_disjunctions_are_deterministic() -> NativeResult<()> {
        let mut kernel = TableauKernel::new();
        let node = kernel.create_node(NodeKind::Root, None, false, None, None, None)?;
        kernel.begin_operation()?;
        let cancellation = live_cancellation()?;
        let mut access = FactAccess::new(node);
        access.dispatch_atom(&mut kernel, 1, DependencySet::empty())?;
        kernel.add_disjunction(vec![1, 2], DependencySet::empty())?;
        assert_eq!(
            DisjunctionBrancher::process_next(&mut kernel, &mut access, &cancellation)?,
            BranchTransition::Satisfied
        );

        access.refutations.insert(3, DependencySet::empty());
        kernel.add_disjunction(vec![3, 4], DependencySet::empty())?;
        assert_eq!(
            DisjunctionBrancher::process_next(&mut kernel, &mut access, &cancellation)?,
            BranchTransition::Deterministic
        );
        assert!(access.dependency(&kernel, 4)?.is_some());
        assert!(kernel.highest_branch_level().is_none());
        kernel.check_invariants()
    }

    #[test]
    fn learning_backjumps_over_irrelevant_newer_branches() -> NativeResult<()> {
        let mut kernel = TableauKernel::new();
        let node = kernel.create_node(NodeKind::Root, None, false, None, None, None)?;
        kernel.begin_operation()?;
        kernel.push_branch(
            "ground_disjunction".to_owned(),
            vec![10, 11],
            100,
            DependencySet::empty(),
        )?;
        kernel.push_branch(
            "ground_disjunction".to_owned(),
            vec![20, 21],
            200,
            DependencySet::new(vec![0])?,
        )?;
        kernel.push_branch(
            "ground_disjunction".to_owned(),
            vec![30, 31],
            300,
            DependencySet::new(vec![0, 1])?,
        )?;
        kernel.install_clash(
            "empty_head".to_owned(),
            DependencySet::new(vec![0])?,
            vec![999],
            None,
        )?;
        let cancellation = live_cancellation()?;
        let mut access = FactAccess::new(node);

        assert_eq!(
            DisjunctionBrancher::new(true).resolve_clash(
                &mut kernel,
                &mut access,
                &cancellation,
            )?,
            BranchTransition::Advanced
        );
        assert_eq!(kernel.highest_branch_level(), Some(0));
        assert!(access.dependency(&kernel, 11)?.is_some());
        kernel.check_invariants()
    }

    #[test]
    fn learning_disabled_advances_the_latest_branch_chronologically() -> NativeResult<()> {
        let mut kernel = TableauKernel::new();
        let node = kernel.create_node(NodeKind::Root, None, false, None, None, None)?;
        kernel.begin_operation()?;
        kernel.push_branch(
            "ground_disjunction".to_owned(),
            vec![10, 11],
            100,
            DependencySet::empty(),
        )?;
        kernel.push_branch(
            "ground_disjunction".to_owned(),
            vec![20, 21],
            200,
            DependencySet::new(vec![0])?,
        )?;
        kernel.push_branch(
            "ground_disjunction".to_owned(),
            vec![30, 31],
            300,
            DependencySet::new(vec![0, 1])?,
        )?;
        kernel.install_clash(
            "empty_head".to_owned(),
            DependencySet::new(vec![0])?,
            vec![999],
            None,
        )?;
        let cancellation = live_cancellation()?;
        let mut access = FactAccess::new(node);

        assert_eq!(
            DisjunctionBrancher::new(false).resolve_clash(
                &mut kernel,
                &mut access,
                &cancellation,
            )?,
            BranchTransition::Advanced
        );
        assert_eq!(kernel.highest_branch_level(), Some(2));
        assert!(access.dependency(&kernel, 31)?.is_some());
        kernel.check_invariants()
    }

    #[test]
    fn cancellation_after_choice_rolls_back_to_operation_root() -> NativeResult<()> {
        let mut kernel = TableauKernel::new();
        let node = kernel.create_node(NodeKind::Root, None, false, None, None, None)?;
        kernel.begin_operation()?;
        let baseline = kernel.canonical_snapshot()?;
        kernel.add_disjunction(vec![10, 20], DependencySet::empty())?;
        let cancellation = live_cancellation()?;
        let mut access = FactAccess::new(node);
        access.cancel_on_dispatch = Some(Arc::clone(&cancellation));

        let error = DisjunctionBrancher::process_next(&mut kernel, &mut access, &cancellation)
            .err()
            .ok_or_else(|| NativeError::invariant("injected cancellation unexpectedly passed"))?;
        assert_eq!(error.kind, ErrorKind::Cancelled);
        assert_eq!(kernel.canonical_snapshot()?, baseline);
        assert!(kernel.highest_branch_level().is_none());
        Ok(())
    }
}
