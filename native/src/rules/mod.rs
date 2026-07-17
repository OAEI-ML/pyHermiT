//! Pure-Rust hyperresolution rule model, plans, and join evaluators.
// SPDX-License-Identifier: LGPL-3.0-or-later

mod engine;
mod joins;
mod model;
mod plans;

pub use crate::branching::BranchTransition;
pub use engine::RuleEngine;
pub use joins::{IndexedJoinEvaluator, NaiveJoinEvaluator};
pub use model::{
    GroundAtom, JoinMatch, PredicateKind, RuleAtom, RuleClause, RuleLimits, RulePredicate,
    RuleProgram, Term, TermSort, VariableBinding,
};
pub use plans::{compile_join_program, ClauseJoinPlan, JoinProgram, JoinStep};
