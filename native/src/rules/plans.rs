//! Deterministic semi-naive join-plan compilation.
// SPDX-License-Identifier: LGPL-3.0-or-later

use std::cmp::Reverse;
use std::collections::{BTreeMap, BTreeSet};

use crate::error::{NativeError, NativeResult};

use super::model::{PredicateKind, RuleAtom, RuleClause, RuleProgram, Term};

type PlanRank<'a> = (u8, Reverse<usize>, usize, usize, &'a RuleAtom);

/// One non-delta atom in its deterministic evaluation order.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct JoinStep {
    pub body_index: u32,
    pub bound_positions: Vec<u32>,
}

impl JoinStep {
    pub fn new(body_index: u32, bound_positions: Vec<u32>) -> NativeResult<Self> {
        if bound_positions.windows(2).any(|pair| pair[0] >= pair[1]) {
            return Err(NativeError::wire(
                "join-step bound positions must be sorted and unique",
            ));
        }
        Ok(Self {
            body_index,
            bound_positions,
        })
    }
}

/// One clause plan with exactly one designated delta body atom.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ClauseJoinPlan {
    pub clause_id: u32,
    pub delta_body_index: u32,
    pub steps: Vec<JoinStep>,
}

impl ClauseJoinPlan {
    pub fn new(clause_id: u32, delta_body_index: u32, steps: Vec<JoinStep>) -> NativeResult<Self> {
        let mut indices = BTreeSet::new();
        indices.insert(delta_body_index);
        if steps.iter().any(|step| !indices.insert(step.body_index)) {
            return Err(NativeError::wire("join-plan body indices must be unique"));
        }
        Ok(Self {
            clause_id,
            delta_body_index,
            steps,
        })
    }
}

/// All deterministic plans plus clauses without any physical trigger atom.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct JoinProgram {
    plans: Vec<ClauseJoinPlan>,
    unconditional_clause_ids: Vec<u32>,
    plans_by_predicate: BTreeMap<u32, Vec<usize>>,
}

impl JoinProgram {
    fn new(
        program: &RuleProgram,
        plans: Vec<ClauseJoinPlan>,
        unconditional_clause_ids: Vec<u32>,
    ) -> NativeResult<Self> {
        if plans.windows(2).any(|pair| {
            (pair[0].clause_id, pair[0].delta_body_index)
                >= (pair[1].clause_id, pair[1].delta_body_index)
        }) {
            return Err(NativeError::wire("join plans must be uniquely sorted"));
        }
        if unconditional_clause_ids
            .windows(2)
            .any(|pair| pair[0] >= pair[1])
        {
            return Err(NativeError::wire(
                "unconditional clause IDs must be sorted and unique",
            ));
        }

        let mut plans_by_predicate: BTreeMap<u32, Vec<usize>> = BTreeMap::new();
        for (plan_index, plan) in plans.iter().enumerate() {
            validate_plan(program, plan)?;
            let clause = program.clause(plan.clause_id)?;
            let delta_index = usize_from_u32(plan.delta_body_index, "delta body index")?;
            let predicate_id = clause.body[delta_index].predicate_id;
            plans_by_predicate
                .entry(predicate_id)
                .or_default()
                .push(plan_index);
        }
        for clause_id in &unconditional_clause_ids {
            let clause = program.clause(*clause_id)?;
            if clause.body.iter().any(|atom| {
                program
                    .predicate_kind(atom.predicate_id)
                    .is_ok_and(PredicateKind::can_trigger)
            }) {
                return Err(NativeError::wire(
                    "triggerable clause cannot be marked unconditional",
                ));
            }
        }
        Ok(Self {
            plans,
            unconditional_clause_ids,
            plans_by_predicate,
        })
    }

    #[must_use]
    pub fn plans(&self) -> &[ClauseJoinPlan] {
        &self.plans
    }

    #[must_use]
    pub fn unconditional_clause_ids(&self) -> &[u32] {
        &self.unconditional_clause_ids
    }

    #[must_use]
    pub fn for_predicate(&self, predicate_id: u32) -> Vec<&ClauseJoinPlan> {
        self.plans_by_predicate
            .get(&predicate_id)
            .map_or_else(Vec::new, |indices| {
                indices.iter().map(|index| &self.plans[*index]).collect()
            })
    }
}

/// Compile every legal delta designation using the Python WP09 ranking tuple.
pub fn compile_join_program(program: &RuleProgram) -> NativeResult<JoinProgram> {
    let mut plans = Vec::new();
    let mut unconditional = Vec::new();
    for clause in program.clauses() {
        let mut triggers = Vec::new();
        for (index, atom) in clause.body.iter().enumerate() {
            if program.predicate_kind(atom.predicate_id)?.can_trigger() {
                triggers.push(u32::try_from(index).map_err(|_| {
                    NativeError::wire("clause body index exceeds the u32 IR limit")
                })?);
            }
        }
        if triggers.is_empty() {
            unconditional.push(clause.clause_id);
            continue;
        }
        for trigger in triggers {
            plans.push(compile_clause_plan(program, clause, trigger)?);
        }
    }
    plans.sort_unstable_by_key(|plan| (plan.clause_id, plan.delta_body_index));
    JoinProgram::new(program, plans, unconditional)
}

fn compile_clause_plan(
    program: &RuleProgram,
    clause: &RuleClause,
    trigger: u32,
) -> NativeResult<ClauseJoinPlan> {
    let trigger_index = usize_from_u32(trigger, "delta body index")?;
    let trigger_atom = clause
        .body
        .get(trigger_index)
        .ok_or_else(|| NativeError::wire("delta body index is out of bounds"))?;
    let mut bound: BTreeSet<_> = trigger_atom
        .arguments
        .iter()
        .filter_map(Term::variable_key)
        .collect();
    let body_len = u32::try_from(clause.body.len())
        .map_err(|_| NativeError::wire("clause body exceeds u32 positions"))?;
    let mut remaining: BTreeSet<_> = (0..body_len).filter(|index| *index != trigger).collect();
    let mut steps = Vec::new();
    let mut join_rank = BTreeMap::new();
    for (rank, body_index) in clause.join_order.iter().copied().enumerate() {
        join_rank.insert(body_index, rank);
    }

    while !remaining.is_empty() {
        let mut selected: Option<(u32, PlanRank<'_>)> = None;
        for body_index in &remaining {
            let index = usize_from_u32(*body_index, "join body index")?;
            let atom = &clause.body[index];
            let predicate = program.predicate(atom.predicate_id)?;
            let variables: BTreeSet<_> = atom
                .arguments
                .iter()
                .filter_map(Term::variable_key)
                .collect();
            let bound_count = variables.intersection(&bound).count();
            let unbound_count = variables.difference(&bound).count();
            let rank = (
                u8::from(predicate.kind.is_virtual_filter() && unbound_count != 0),
                Reverse(bound_count),
                unbound_count,
                *join_rank.get(body_index).ok_or_else(|| {
                    NativeError::invariant("validated join order lost one body index")
                })?,
                atom,
            );
            if selected
                .as_ref()
                .is_none_or(|(_selected_index, selected_rank)| rank < *selected_rank)
            {
                selected = Some((*body_index, rank));
            }
        }
        let (body_index, _rank) = selected
            .ok_or_else(|| NativeError::invariant("join planner could not select an atom"))?;
        let atom = &clause.body[usize_from_u32(body_index, "join body index")?];
        let mut bound_positions = Vec::new();
        for (position, argument) in atom.arguments.iter().enumerate() {
            if argument
                .variable_key()
                .is_none_or(|variable| bound.contains(&variable))
            {
                bound_positions
                    .push(u32::try_from(position).map_err(|_| {
                        NativeError::wire("atom position exceeds the u32 IR limit")
                    })?);
            }
        }
        steps.push(JoinStep::new(body_index, bound_positions)?);
        bound.extend(atom.arguments.iter().filter_map(Term::variable_key));
        remaining.remove(&body_index);
    }
    ClauseJoinPlan::new(clause.clause_id, trigger, steps)
}

fn validate_plan(program: &RuleProgram, plan: &ClauseJoinPlan) -> NativeResult<()> {
    let clause = program.clause(plan.clause_id)?;
    let delta_index = usize_from_u32(plan.delta_body_index, "delta body index")?;
    let delta = clause
        .body
        .get(delta_index)
        .ok_or_else(|| NativeError::wire("delta body index is out of bounds"))?;
    if !program.predicate_kind(delta.predicate_id)?.can_trigger() {
        return Err(NativeError::wire(
            "ordering guards cannot designate a delta atom",
        ));
    }
    if plan.steps.len().checked_add(1) != Some(clause.body.len()) {
        return Err(NativeError::wire(
            "join plan must cover every body atom exactly once",
        ));
    }
    let mut indices = BTreeSet::from([plan.delta_body_index]);
    for step in &plan.steps {
        if !indices.insert(step.body_index) {
            return Err(NativeError::wire("join-plan body indices must be unique"));
        }
        let atom = clause
            .body
            .get(usize_from_u32(step.body_index, "join body index")?)
            .ok_or_else(|| NativeError::wire("join body index is out of bounds"))?;
        if step.bound_positions.iter().any(|position| {
            usize::try_from(*position).map_or(true, |index| index >= atom.arguments.len())
        }) {
            return Err(NativeError::wire(
                "join-step bound position is out of bounds",
            ));
        }
    }
    Ok(())
}

fn usize_from_u32(value: u32, name: &str) -> NativeResult<usize> {
    usize::try_from(value)
        .map_err(|_| NativeError::wire(format!("{name} cannot fit this platform")))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rules::model::{RulePredicate, TermSort};

    fn atom(predicate_id: u32, arguments: Vec<Term>) -> NativeResult<RuleAtom> {
        RuleAtom::new(predicate_id, arguments)
    }

    fn canonical(mut atoms: Vec<RuleAtom>) -> Vec<RuleAtom> {
        atoms.sort_by_cached_key(RuleAtom::canonical_bytes);
        atoms
    }

    #[test]
    fn planner_delays_unready_virtual_filters_and_is_stable() -> NativeResult<()> {
        let predicates = vec![
            RulePredicate::new(
                0,
                PredicateKind::ObjectRole,
                vec![TermSort::Object, TermSort::Object],
            )?,
            RulePredicate::new(1, PredicateKind::Concept, vec![TermSort::Object])?,
            RulePredicate::new(
                2,
                PredicateKind::Equality,
                vec![TermSort::Object, TermSort::Object],
            )?,
            RulePredicate::new(
                3,
                PredicateKind::OrderingGuard,
                vec![TermSort::Object, TermSort::Object],
            )?,
        ];
        let x0 = Term::variable(0, TermSort::Object);
        let x1 = Term::variable(1, TermSort::Object);
        let x2 = Term::variable(2, TermSort::Object);
        let clause = RuleClause::new(
            0,
            canonical(vec![
                atom(0, vec![x0.clone(), x1.clone()])?,
                atom(1, vec![x1.clone()])?,
                atom(2, vec![x1, x2.clone()])?,
                atom(3, vec![x0, x2])?,
            ]),
            Vec::new(),
            vec![0],
            vec![0, 2, 1, 3],
        )?;
        let program = RuleProgram::new(predicates, vec![clause])?;
        let first = compile_join_program(&program)?;
        let second = compile_join_program(&program)?;
        assert_eq!(first, second);
        assert_eq!(first.plans().len(), 3);
        assert_eq!(
            first.plans()[0]
                .steps
                .iter()
                .map(|step| step.body_index)
                .collect::<Vec<_>>(),
            vec![3, 2, 1]
        );
        assert_eq!(first.for_predicate(3).len(), 0);
        assert_eq!(first.for_predicate(0).len(), 1);
        Ok(())
    }

    #[test]
    fn empty_and_guard_only_bodies_are_unconditional() -> NativeResult<()> {
        let guard = RulePredicate::new(
            0,
            PredicateKind::OrderingGuard,
            vec![TermSort::Object, TermSort::Object],
        )?;
        let x0 = Term::variable(0, TermSort::Object);
        let x1 = Term::variable(1, TermSort::Object);
        let clauses = vec![
            RuleClause::new(0, Vec::new(), Vec::new(), vec![0], Vec::new())?,
            RuleClause::new(
                1,
                vec![atom(0, vec![x0, x1])?],
                Vec::new(),
                vec![1],
                vec![0],
            )?,
        ];
        let program = RuleProgram::new(vec![guard], clauses)?;
        let joins = compile_join_program(&program)?;
        assert!(joins.plans().is_empty());
        assert_eq!(joins.unconditional_clause_ids(), [0, 1]);
        Ok(())
    }
}
