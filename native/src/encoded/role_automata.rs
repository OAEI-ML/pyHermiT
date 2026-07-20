//! Deterministic epsilon-NFA compilation for regular object-role inclusions.
//!
//! This phase mirrors the scalar role-language construction after role
//! regularity and simplicity analysis.  It retains canonical automata only for
//! the universal role, non-simple roles, and their dependencies.  The output
//! remains a private compiler fragment and does not advertise encoded-native
//! reasoning support.
// SPDX-License-Identifier: LGPL-3.0-or-later

#![forbid(unsafe_code)]

use std::cmp::Reverse;
use std::collections::{BinaryHeap, VecDeque};
use std::mem::size_of;

use serde::ser::SerializeSeq;
use serde::{Serialize, Serializer};

use super::complex_roles::ComplexRolePhase;
use super::object_role_hierarchy::ObjectRoleHierarchyPhase;
use super::object_roles::ObjectRolePhase;
use super::role_semantics::RoleSemanticsPhase;
use super::simple_roles::SimpleRolePhase;
use super::{EncodedResult, EncodedValidationError};
use crate::input_wire::SymbolKind;

const ROLE_AUTOMATA_SCHEMA_VERSION: u16 = 1;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RoleAutomataPhaseLimits {
    pub max_roles: usize,
    pub max_components: usize,
    pub max_automata: usize,
    pub max_states: usize,
    pub max_transitions: usize,
    pub max_word_length: usize,
    pub max_owned_bytes: usize,
    pub max_work: u64,
    pub max_manifest_bytes: usize,
}

impl Default for RoleAutomataPhaseLimits {
    fn default() -> Self {
        Self {
            max_roles: 1_000_000,
            max_components: 1_000_000,
            max_automata: 1_000_000,
            max_states: 5_000_000,
            max_transitions: 20_000_000,
            max_word_length: 1_000_000,
            max_owned_bytes: 512 * 1024 * 1024,
            max_work: 2_000_000_000,
            max_manifest_bytes: 512 * 1024 * 1024,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct NfaTransition {
    pub source_state: u32,
    pub target_state: u32,
    pub role_id: Option<u32>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RoleAutomaton {
    pub target_component_id: u32,
    pub state_count: u32,
    pub initial_state: u32,
    pub final_states: Vec<u32>,
    pub transitions: Vec<NfaTransition>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RoleAutomataPhase {
    pub automata: Vec<RoleAutomaton>,
    pub work: u64,
    pub owned_bytes: usize,
    role_count: usize,
    component_count: usize,
    bottom_role_id: u32,
    top_role_id: u32,
    max_word_length: usize,
    max_acceptance_work: u64,
    manifest_limit: usize,
}

impl RoleAutomataPhase {
    /// Canonical private manifest used for exact scalar differential checks.
    pub fn canonical_manifest_json(&self) -> EncodedResult<Vec<u8>> {
        validate_output(self)?;
        let encoded = serde_json::to_vec(&RoleAutomataManifest {
            schema_version: ROLE_AUTOMATA_SCHEMA_VERSION,
            family: "object_role_automata",
            automata: AutomataManifest(&self.automata),
        })
        .map_err(|_| {
            EncodedValidationError::invariant("object-role automata manifest serialization failed")
        })?;
        if encoded.len() > self.manifest_limit {
            return Err(EncodedValidationError::resource(
                "object-role automata manifest exceeds its byte limit",
            ));
        }
        Ok(encoded)
    }

    /// Evaluate a bounded role word with scalar-compatible built-in and fallback semantics.
    pub fn accepts(
        &self,
        hierarchy: &ObjectRoleHierarchyPhase,
        target_role_id: u32,
        word_role_ids: &[u32],
    ) -> EncodedResult<bool> {
        validate_output(self)?;
        validate_hierarchy_for_acceptance(self, hierarchy)?;
        validate_acceptance_id(target_role_id, self.role_count, "target role")?;
        if word_role_ids.len() > self.max_word_length {
            return Err(EncodedValidationError::resource(
                "object-role acceptance word exceeds its length limit",
            ));
        }
        for &role_id in word_role_ids {
            validate_acceptance_id(role_id, self.role_count, "word role")?;
        }
        if word_role_ids.contains(&self.bottom_role_id) {
            return Ok(true);
        }
        let target_component = hierarchy.object_component_by_role[usize_id(target_role_id)?];
        if let Ok(index) = self
            .automata
            .binary_search_by_key(&target_component, |automaton| automaton.target_component_id)
        {
            return automaton_accepts(
                &self.automata[index],
                word_role_ids,
                self.max_acceptance_work,
            );
        }
        if word_role_ids.len() != 1 {
            return Ok(false);
        }
        let sub_role_id = word_role_ids[0];
        if sub_role_id == self.bottom_role_id || target_role_id == self.top_role_id {
            return Ok(true);
        }
        let sub_component = hierarchy.object_component_by_role[usize_id(sub_role_id)?];
        Ok(hierarchy.object_super_components[usize_id(sub_component)?].contains(target_component))
    }
}

#[derive(Serialize)]
struct RoleAutomataManifest<'a> {
    schema_version: u16,
    family: &'static str,
    automata: AutomataManifest<'a>,
}

struct AutomataManifest<'a>(&'a [RoleAutomaton]);

impl Serialize for AutomataManifest<'_> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut sequence = serializer.serialize_seq(Some(self.0.len()))?;
        for automaton in self.0 {
            sequence.serialize_element(&AutomatonManifest {
                target_component_id: automaton.target_component_id,
                state_count: automaton.state_count,
                initial_state: automaton.initial_state,
                final_states: &automaton.final_states,
                transitions: TransitionsManifest(&automaton.transitions),
            })?;
        }
        sequence.end()
    }
}

#[derive(Serialize)]
struct AutomatonManifest<'a> {
    target_component_id: u32,
    state_count: u32,
    initial_state: u32,
    final_states: &'a [u32],
    transitions: TransitionsManifest<'a>,
}

struct TransitionsManifest<'a>(&'a [NfaTransition]);

impl Serialize for TransitionsManifest<'_> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut sequence = serializer.serialize_seq(Some(self.0.len()))?;
        for transition in self.0 {
            sequence.serialize_element(&(
                transition.source_state,
                transition.role_id,
                transition.target_state,
            ))?;
        }
        sequence.end()
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Production {
    target_component: u32,
    chain_components: Vec<u32>,
}

struct MutableNfa {
    state_count: usize,
    transitions: Vec<NfaTransition>,
}

impl MutableNfa {
    const fn new() -> Self {
        Self {
            state_count: 0,
            transitions: Vec::new(),
        }
    }

    fn state(&mut self, budget: &mut PhaseBudget) -> EncodedResult<u32> {
        let following = self
            .state_count
            .checked_add(1)
            .ok_or_else(|| EncodedValidationError::resource("role NFA state count overflowed"))?;
        if following > budget.limits.max_states {
            return Err(EncodedValidationError::resource(
                "role NFA state limit exceeded",
            ));
        }
        budget.claim_work(1)?;
        self.state_count = following;
        u32_id(following - 1)
    }

    fn transition(
        &mut self,
        source_state: u32,
        role_id: Option<u32>,
        target_state: u32,
        budget: &mut PhaseBudget,
    ) -> EncodedResult<()> {
        if self.transitions.len() >= budget.limits.max_transitions {
            return Err(EncodedValidationError::resource(
                "role NFA transition limit exceeded",
            ));
        }
        budget.claim_work(1)?;
        reserve_push(
            &mut self.transitions,
            NfaTransition {
                source_state,
                target_state,
                role_id,
            },
            "role NFA transition",
            budget,
        )
    }

    fn copy_between(
        &mut self,
        automaton: &RoleAutomaton,
        source: u32,
        target: u32,
        budget: &mut PhaseBudget,
    ) -> EncodedResult<()> {
        let state_count = usize_id(automaton.state_count)?;
        let mut mapping = reserved_u32(state_count, "copied role NFA state map", budget)?;
        for _ in 0..state_count {
            mapping.push(self.state(budget)?);
        }
        self.transition(
            source,
            None,
            mapping[usize_id(automaton.initial_state)?],
            budget,
        )?;
        for transition in &automaton.transitions {
            self.transition(
                mapping[usize_id(transition.source_state)?],
                transition.role_id,
                mapping[usize_id(transition.target_state)?],
                budget,
            )?;
        }
        for &final_state in &automaton.final_states {
            self.transition(mapping[usize_id(final_state)?], None, target, budget)?;
        }
        Ok(())
    }
}

struct PhaseBudget {
    limits: RoleAutomataPhaseLimits,
    work: u64,
    owned_bytes: usize,
}

impl PhaseBudget {
    const fn new(limits: RoleAutomataPhaseLimits) -> Self {
        Self {
            limits,
            work: 0,
            owned_bytes: 0,
        }
    }

    fn claim_work(&mut self, amount: usize) -> EncodedResult<()> {
        let amount = u64::try_from(amount)
            .map_err(|_| EncodedValidationError::resource("role-NFA work exceeds u64"))?;
        let following = self
            .work
            .checked_add(amount)
            .ok_or_else(|| EncodedValidationError::resource("role-NFA work overflowed"))?;
        if following > self.limits.max_work {
            return Err(EncodedValidationError::resource(
                "role-NFA compilation exceeds its work limit",
            ));
        }
        self.work = following;
        Ok(())
    }

    fn claim_owned(&mut self, amount: usize) -> EncodedResult<()> {
        let following = self.owned_bytes.checked_add(amount).ok_or_else(|| {
            EncodedValidationError::resource("role-NFA owned-byte count overflowed")
        })?;
        if following > self.limits.max_owned_bytes {
            return Err(EncodedValidationError::resource(
                "role-NFA compilation exceeds its owned-byte limit",
            ));
        }
        self.owned_bytes = following;
        Ok(())
    }
}

/// Compile the canonical scalar-compatible automata retained by the role model.
pub fn compile_role_automata_phase(
    roles: &ObjectRolePhase,
    simple: &SimpleRolePhase,
    complex: &ComplexRolePhase,
    hierarchy: &ObjectRoleHierarchyPhase,
    semantics: &RoleSemanticsPhase,
    limits: RoleAutomataPhaseLimits,
) -> EncodedResult<RoleAutomataPhase> {
    validate_inputs(roles, simple, complex, hierarchy, semantics, limits)?;
    let role_count = roles.object_role_domain.values.len();
    let component_count = hierarchy.object_components.len();
    let mut budget = PhaseBudget::new(limits);
    if !semantics.regularity_violations.is_empty() {
        return Ok(RoleAutomataPhase {
            automata: Vec::new(),
            work: 0,
            owned_bytes: 0,
            role_count,
            component_count,
            bottom_role_id: roles.bottom_object_role_id,
            top_role_id: roles.top_object_role_id,
            max_word_length: limits.max_word_length,
            max_acceptance_work: limits.max_work,
            manifest_limit: limits.max_manifest_bytes,
        });
    }

    let subrole_dependencies =
        compile_subrole_dependencies(simple, hierarchy, component_count, &mut budget)?;
    let productions = compile_productions(complex, hierarchy, &mut budget)?;
    let selected = select_components(hierarchy, semantics, &mut budget)?;
    let selected_count = selected.iter().filter(|&&value| value).count();
    if selected_count > limits.max_automata {
        return Err(EncodedValidationError::resource(
            "role automaton count exceeds its limit",
        ));
    }
    let order = topological_order(&semantics.dependencies, &mut budget)?;
    let mut automata = reserved_vec::<RoleAutomaton>(selected_count, "role automata", &mut budget)?;
    let mut complete = filled_usize(
        component_count,
        usize::MAX,
        "role automaton component index",
        &mut budget,
    )?;
    let mut total_states = 0_usize;
    let mut total_transitions = 0_usize;
    for component in order {
        let component_index = usize_id(component)?;
        if !selected[component_index] {
            continue;
        }
        let mut mutable = MutableNfa::new();
        let initial = mutable.state(&mut budget)?;
        let final_state = mutable.state(&mut budget)?;
        if component == hierarchy.top_component_id {
            for role_id in 0..role_count {
                mutable.transition(initial, Some(u32_id(role_id)?), final_state, &mut budget)?;
            }
            mutable.transition(final_state, None, initial, &mut budget)?;
        } else {
            for &role_id in &hierarchy.object_components[component_index] {
                mutable.transition(initial, Some(role_id), final_state, &mut budget)?;
            }
            for &dependency in &subrole_dependencies[component_index] {
                let dependency_index = complete[usize_id(dependency)?];
                let dependency_automaton = automata.get(dependency_index).ok_or_else(|| {
                    EncodedValidationError::invariant(
                        "simple role dependency lacks a completed automaton",
                    )
                })?;
                mutable.copy_between(dependency_automaton, initial, final_state, &mut budget)?;
            }
            for production in productions_for_target(&productions, component) {
                add_production(
                    &mut mutable,
                    &automata,
                    &complete,
                    component,
                    &production.chain_components,
                    initial,
                    final_state,
                    &mut budget,
                )?;
            }
        }
        let automaton = freeze_automaton(component, mutable, initial, final_state, &mut budget)?;
        total_states = total_states
            .checked_add(usize_id(automaton.state_count)?)
            .ok_or_else(|| {
                EncodedValidationError::resource("aggregate role NFA states overflowed")
            })?;
        total_transitions = total_transitions
            .checked_add(automaton.transitions.len())
            .ok_or_else(|| {
                EncodedValidationError::resource("aggregate role NFA transitions overflowed")
            })?;
        if total_states > limits.max_states {
            return Err(EncodedValidationError::resource(
                "aggregate role NFA state limit exceeded",
            ));
        }
        if total_transitions > limits.max_transitions {
            return Err(EncodedValidationError::resource(
                "aggregate role NFA transition limit exceeded",
            ));
        }
        complete[component_index] = automata.len();
        automata.push(automaton);
    }
    budget.claim_work(sort_work(automata.len()))?;
    automata.sort_unstable_by_key(|automaton| automaton.target_component_id);
    let phase = RoleAutomataPhase {
        automata,
        work: budget.work,
        owned_bytes: budget.owned_bytes,
        role_count,
        component_count,
        bottom_role_id: roles.bottom_object_role_id,
        top_role_id: roles.top_object_role_id,
        max_word_length: limits.max_word_length,
        max_acceptance_work: limits.max_work,
        manifest_limit: limits.max_manifest_bytes,
    };
    validate_output(&phase)?;
    Ok(phase)
}

fn compile_subrole_dependencies(
    simple: &SimpleRolePhase,
    hierarchy: &ObjectRoleHierarchyPhase,
    component_count: usize,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<Vec<u32>>> {
    let mut rows = empty_rows(component_count, "simple role dependency rows", budget)?;
    for inclusion in &simple.simple_inclusions {
        budget.claim_work(1)?;
        let dependency = hierarchy.object_component_by_role[usize_id(inclusion.sub_role_id)?];
        let consumer = hierarchy.object_component_by_role[usize_id(inclusion.super_role_id)?];
        if dependency != consumer {
            reserve_push(
                &mut rows[usize_id(consumer)?],
                dependency,
                "simple role dependency",
                budget,
            )?;
        }
    }
    for row in &mut rows {
        budget.claim_work(sort_work(row.len()))?;
        row.sort_unstable();
        row.dedup();
    }
    Ok(rows)
}

fn compile_productions(
    complex: &ComplexRolePhase,
    hierarchy: &ObjectRoleHierarchyPhase,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<Production>> {
    let mut productions =
        reserved_vec::<Production>(complex.complex_inclusions.len(), "role productions", budget)?;
    for inclusion in &complex.complex_inclusions {
        budget.claim_work(1)?;
        let mut chain = reserved_u32(
            inclusion.chain_role_ids.len(),
            "role production chain",
            budget,
        )?;
        for &role_id in &inclusion.chain_role_ids {
            budget.claim_work(1)?;
            chain.push(hierarchy.object_component_by_role[usize_id(role_id)?]);
        }
        productions.push(Production {
            target_component: hierarchy.object_component_by_role
                [usize_id(inclusion.super_role_id)?],
            chain_components: chain,
        });
    }
    budget.claim_work(sort_work(productions.len()))?;
    productions.sort_unstable();
    productions.dedup();
    Ok(productions)
}

fn productions_for_target(productions: &[Production], target: u32) -> &[Production] {
    let start = productions.partition_point(|production| production.target_component < target);
    let end = productions.partition_point(|production| production.target_component <= target);
    &productions[start..end]
}

fn select_components(
    hierarchy: &ObjectRoleHierarchyPhase,
    semantics: &RoleSemanticsPhase,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<bool>> {
    let component_count = hierarchy.object_components.len();
    let mut selected = filled_bool(component_count, false, "selected role components", budget)?;
    selected[usize_id(hierarchy.top_component_id)?] = true;
    let mut pending = reserved_u32(
        semantics.non_simple_components.len(),
        "pending role components",
        budget,
    )?;
    for &component in &semantics.non_simple_components {
        if component != hierarchy.top_component_id {
            pending.push(component);
        }
    }
    while let Some(component) = pending.pop() {
        budget.claim_work(1)?;
        let index = usize_id(component)?;
        if selected[index] {
            continue;
        }
        selected[index] = true;
        for &dependency in &semantics.dependencies[index] {
            reserve_push(&mut pending, dependency, "pending role dependency", budget)?;
        }
    }
    Ok(selected)
}

fn topological_order(
    dependencies: &[Vec<u32>],
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<u32>> {
    let component_count = dependencies.len();
    let mut indegree = reserved_usize(component_count, "role dependency indegrees", budget)?;
    let mut dependents = empty_rows(component_count, "role dependency dependents", budget)?;
    for (consumer, row) in dependencies.iter().enumerate() {
        indegree.push(row.len());
        for &dependency in row {
            budget.claim_work(1)?;
            reserve_push(
                &mut dependents[usize_id(dependency)?],
                u32_id(consumer)?,
                "role dependency dependent",
                budget,
            )?;
        }
    }
    let mut ready = BinaryHeap::new();
    ready
        .try_reserve(component_count)
        .map_err(|_| EncodedValidationError::resource("role dependency heap allocation failed"))?;
    budget.claim_owned(
        component_count
            .checked_mul(size_of::<Reverse<u32>>())
            .ok_or_else(|| {
                EncodedValidationError::resource("role dependency heap bytes overflowed")
            })?,
    )?;
    for (component, &degree) in indegree.iter().enumerate() {
        if degree == 0 {
            ready.push(Reverse(u32_id(component)?));
        }
    }
    let mut order = reserved_u32(component_count, "role dependency order", budget)?;
    while let Some(Reverse(component)) = ready.pop() {
        budget.claim_work(1)?;
        order.push(component);
        for &consumer in &dependents[usize_id(component)?] {
            let degree = &mut indegree[usize_id(consumer)?];
            *degree = degree.checked_sub(1).ok_or_else(|| {
                EncodedValidationError::invariant("role dependency indegree underflowed")
            })?;
            if *degree == 0 {
                ready.push(Reverse(consumer));
            }
        }
    }
    if order.len() != component_count {
        return Err(EncodedValidationError::invariant(
            "regular role dependency graph contains a cycle",
        ));
    }
    Ok(order)
}

#[allow(clippy::too_many_arguments)]
fn add_production(
    mutable: &mut MutableNfa,
    automata: &[RoleAutomaton],
    complete: &[usize],
    target_component: u32,
    chain: &[u32],
    initial: u32,
    final_state: u32,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    let mut positions = reserved_u32(chain.len(), "recursive role positions", budget)?;
    for (position, &component) in chain.iter().enumerate() {
        budget.claim_work(1)?;
        if component == target_component {
            positions.push(u32_id(position)?);
        }
    }
    if chain.len() == 2 && positions == [0, 1] {
        return mutable.transition(final_state, None, initial, budget);
    }
    if positions == [0] {
        return copy_sequence(
            mutable,
            automata,
            complete,
            &chain[1..],
            final_state,
            final_state,
            budget,
        );
    }
    if positions == [u32_id(chain.len().saturating_sub(1))?] {
        return copy_sequence(
            mutable,
            automata,
            complete,
            &chain[..chain.len().saturating_sub(1)],
            initial,
            initial,
            budget,
        );
    }
    if !positions.is_empty() {
        return Err(EncodedValidationError::invariant(
            "irregular recursive production reached role-NFA construction",
        ));
    }
    copy_sequence(
        mutable,
        automata,
        complete,
        chain,
        initial,
        final_state,
        budget,
    )
}

fn copy_sequence(
    mutable: &mut MutableNfa,
    automata: &[RoleAutomaton],
    complete: &[usize],
    components: &[u32],
    source: u32,
    target: u32,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    if components.is_empty() {
        return mutable.transition(source, None, target, budget);
    }
    let mut current = source;
    for (offset, &component) in components.iter().enumerate() {
        let following = if offset + 1 == components.len() {
            target
        } else {
            mutable.state(budget)?
        };
        let automaton_index = complete[usize_id(component)?];
        let automaton = automata.get(automaton_index).ok_or_else(|| {
            EncodedValidationError::invariant("complex role dependency lacks a completed automaton")
        })?;
        mutable.copy_between(automaton, current, following, budget)?;
        current = following;
    }
    Ok(())
}

fn freeze_automaton(
    component: u32,
    mut mutable: MutableNfa,
    initial: u32,
    final_state: u32,
    budget: &mut PhaseBudget,
) -> EncodedResult<RoleAutomaton> {
    budget.claim_work(sort_work(mutable.transitions.len()))?;
    mutable.transitions.sort_unstable_by(compare_transition);
    mutable.transitions.dedup();
    if mutable.transitions.len() > budget.limits.max_transitions {
        return Err(EncodedValidationError::resource(
            "role NFA transition limit exceeded",
        ));
    }
    let state_count = mutable.state_count;
    let mut reverse = clone_transitions(&mutable.transitions, "reverse role transitions", budget)?;
    budget.claim_work(sort_work(reverse.len()))?;
    reverse.sort_unstable_by(|left, right| {
        (
            left.target_state,
            left.source_state,
            role_sort_key(left.role_id),
        )
            .cmp(&(
                right.target_state,
                right.source_state,
                role_sort_key(right.role_id),
            ))
    });

    let mut reachable = filled_bool(state_count, false, "reachable role NFA states", budget)?;
    traverse_forward(initial, &mutable.transitions, &mut reachable, budget)?;
    let mut coreachable = filled_bool(state_count, false, "coreachable role NFA states", budget)?;
    traverse_reverse(final_state, &reverse, &mut coreachable, budget)?;
    let initial_index = usize_id(initial)?;
    let final_index = usize_id(final_state)?;
    if !reachable[initial_index]
        || !coreachable[initial_index]
        || !reachable[final_index]
        || !coreachable[final_index]
    {
        return Err(EncodedValidationError::invariant(
            "role NFA has no accepting path",
        ));
    }

    let mut mapping = filled_u32(
        state_count,
        u32::MAX,
        "canonical role NFA state map",
        budget,
    )?;
    let mut queue = VecDeque::new();
    queue.try_reserve(state_count).map_err(|_| {
        EncodedValidationError::resource("canonical role NFA queue allocation failed")
    })?;
    budget.claim_owned(
        state_count
            .checked_mul(size_of::<u32>())
            .ok_or_else(|| EncodedValidationError::resource("role NFA queue bytes overflowed"))?,
    )?;
    let mut order = reserved_u32(state_count, "canonical role NFA order", budget)?;
    mapping[initial_index] = 0;
    queue.push_back(initial);
    while let Some(state) = queue.pop_front() {
        budget.claim_work(1)?;
        order.push(state);
        for transition in transitions_from(&mutable.transitions, state) {
            let target = usize_id(transition.target_state)?;
            if reachable[target] && coreachable[target] && mapping[target] == u32::MAX {
                mapping[target] =
                    u32_id(order.len().checked_add(queue.len()).ok_or_else(|| {
                        EncodedValidationError::resource("canonical role NFA state ID overflowed")
                    })?)?;
                queue.push_back(transition.target_state);
            }
        }
    }
    let mut transitions = reserved_vec::<NfaTransition>(
        mutable.transitions.len(),
        "canonical role NFA transitions",
        budget,
    )?;
    for transition in mutable.transitions {
        let source = usize_id(transition.source_state)?;
        let target = usize_id(transition.target_state)?;
        if reachable[source] && coreachable[source] && reachable[target] && coreachable[target] {
            transitions.push(NfaTransition {
                source_state: mapping[source],
                target_state: mapping[target],
                role_id: transition.role_id,
            });
        }
    }
    budget.claim_work(sort_work(transitions.len()))?;
    transitions.sort_unstable_by(compare_transition);
    transitions.dedup();
    let mut final_states = reserved_u32(1, "canonical role NFA final states", budget)?;
    final_states.push(mapping[final_index]);
    let automaton = RoleAutomaton {
        target_component_id: component,
        state_count: u32_id(order.len())?,
        initial_state: mapping[initial_index],
        final_states,
        transitions,
    };
    validate_automaton(&automaton, usize::MAX, usize::MAX)?;
    Ok(automaton)
}

fn traverse_forward(
    start: u32,
    transitions: &[NfaTransition],
    reached: &mut [bool],
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    let mut pending = reserved_u32(reached.len(), "role NFA forward stack", budget)?;
    reached[usize_id(start)?] = true;
    pending.push(start);
    while let Some(state) = pending.pop() {
        budget.claim_work(1)?;
        for transition in transitions_from(transitions, state) {
            let target = usize_id(transition.target_state)?;
            if !reached[target] {
                reached[target] = true;
                pending.push(transition.target_state);
            }
        }
    }
    Ok(())
}

fn traverse_reverse(
    start: u32,
    transitions: &[NfaTransition],
    reached: &mut [bool],
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    let mut pending = reserved_u32(reached.len(), "role NFA reverse stack", budget)?;
    reached[usize_id(start)?] = true;
    pending.push(start);
    while let Some(state) = pending.pop() {
        budget.claim_work(1)?;
        let start_index = transitions.partition_point(|value| value.target_state < state);
        let end_index = transitions.partition_point(|value| value.target_state <= state);
        for transition in &transitions[start_index..end_index] {
            let source = usize_id(transition.source_state)?;
            if !reached[source] {
                reached[source] = true;
                pending.push(transition.source_state);
            }
        }
    }
    Ok(())
}

struct AcceptanceBudget {
    work: u64,
    limit: u64,
}

impl AcceptanceBudget {
    const fn new(limit: u64) -> Self {
        Self { work: 0, limit }
    }

    fn claim(&mut self, amount: usize) -> EncodedResult<()> {
        let amount = u64::try_from(amount)
            .map_err(|_| EncodedValidationError::resource("role acceptance work exceeds u64"))?;
        self.work = self
            .work
            .checked_add(amount)
            .ok_or_else(|| EncodedValidationError::resource("role acceptance work overflowed"))?;
        if self.work > self.limit {
            return Err(EncodedValidationError::resource(
                "role acceptance exceeds its work limit",
            ));
        }
        Ok(())
    }
}

fn automaton_accepts(
    automaton: &RoleAutomaton,
    word: &[u32],
    max_work: u64,
) -> EncodedResult<bool> {
    let state_count = usize_id(automaton.state_count)?;
    let mut budget = AcceptanceBudget::new(max_work);
    let mut current_marks = try_bool(state_count, false, "role acceptance state marks")?;
    let mut following_marks = try_bool(state_count, false, "role acceptance next-state marks")?;
    let mut current = try_reserved_u32(state_count, "role acceptance states")?;
    let mut following = try_reserved_u32(state_count, "role acceptance next states")?;
    current_marks[usize_id(automaton.initial_state)?] = true;
    current.push(automaton.initial_state);
    epsilon_closure(automaton, &mut current_marks, &mut current, &mut budget)?;
    for &role_id in word {
        for &state in &current {
            budget.claim(1)?;
            for transition in transitions_from(&automaton.transitions, state) {
                budget.claim(1)?;
                if transition.role_id == Some(role_id) {
                    let target = usize_id(transition.target_state)?;
                    if !following_marks[target] {
                        following_marks[target] = true;
                        following.push(transition.target_state);
                    }
                }
            }
        }
        if following.is_empty() {
            return Ok(false);
        }
        epsilon_closure(automaton, &mut following_marks, &mut following, &mut budget)?;
        for &state in &current {
            current_marks[usize_id(state)?] = false;
        }
        current.clear();
        std::mem::swap(&mut current, &mut following);
        std::mem::swap(&mut current_marks, &mut following_marks);
    }
    for &state in &automaton.final_states {
        budget.claim(1)?;
        if current_marks.get(usize_id(state)?).copied() == Some(true) {
            return Ok(true);
        }
    }
    Ok(false)
}

fn epsilon_closure(
    automaton: &RoleAutomaton,
    marks: &mut [bool],
    states: &mut Vec<u32>,
    budget: &mut AcceptanceBudget,
) -> EncodedResult<()> {
    let mut offset = 0_usize;
    while offset < states.len() {
        budget.claim(1)?;
        let state = states[offset];
        offset = offset.checked_add(1).ok_or_else(|| {
            EncodedValidationError::resource("role acceptance state offset overflowed")
        })?;
        for transition in transitions_from(&automaton.transitions, state) {
            budget.claim(1)?;
            if transition.role_id.is_none() {
                let target = usize_id(transition.target_state)?;
                if !marks[target] {
                    marks[target] = true;
                    states.push(transition.target_state);
                }
            }
        }
    }
    Ok(())
}

fn transitions_from(transitions: &[NfaTransition], state: u32) -> &[NfaTransition] {
    let start = transitions.partition_point(|value| value.source_state < state);
    let end = transitions.partition_point(|value| value.source_state <= state);
    &transitions[start..end]
}

fn compare_transition(left: &NfaTransition, right: &NfaTransition) -> std::cmp::Ordering {
    (
        left.source_state,
        role_sort_key(left.role_id),
        left.target_state,
    )
        .cmp(&(
            right.source_state,
            role_sort_key(right.role_id),
            right.target_state,
        ))
}

const fn role_sort_key(role_id: Option<u32>) -> (u8, u32) {
    match role_id {
        None => (0, 0),
        Some(value) => (1, value),
    }
}

fn validate_inputs(
    roles: &ObjectRolePhase,
    simple: &SimpleRolePhase,
    complex: &ComplexRolePhase,
    hierarchy: &ObjectRoleHierarchyPhase,
    semantics: &RoleSemanticsPhase,
    limits: RoleAutomataPhaseLimits,
) -> EncodedResult<()> {
    let role_count = roles.object_role_domain.values.len();
    let component_count = hierarchy.object_components.len();
    if roles.object_role_domain.kind != SymbolKind::ObjectRole
        || roles.inverse_role_ids.len() != role_count
        || hierarchy.object_component_by_role.len() != role_count
    {
        return Err(EncodedValidationError::invariant(
            "role-NFA input role domain has an invalid shape",
        ));
    }
    if role_count == 0 || role_count > limits.max_roles {
        return Err(EncodedValidationError::resource(
            "role-NFA role domain exceeds its limit",
        ));
    }
    if component_count == 0 || component_count > limits.max_components {
        return Err(EncodedValidationError::resource(
            "role-NFA component domain exceeds its limit",
        ));
    }
    if semantics.dependencies.len() != component_count {
        return Err(EncodedValidationError::invariant(
            "role-NFA dependency rows have the wrong length",
        ));
    }
    for (component, members) in hierarchy.object_components.iter().enumerate() {
        if members.is_empty() || members.windows(2).any(|pair| pair[0] >= pair[1]) {
            return Err(EncodedValidationError::invariant(
                "role-NFA component membership is not canonical",
            ));
        }
        for &role_id in members {
            validate_id(role_id, role_count, "role-NFA component member")?;
            if hierarchy.object_component_by_role[usize_id(role_id)?] != u32_id(component)? {
                return Err(EncodedValidationError::invariant(
                    "role-NFA role-to-component mapping is inconsistent",
                ));
            }
        }
    }
    for (component, row) in semantics.dependencies.iter().enumerate() {
        if row.windows(2).any(|pair| pair[0] >= pair[1]) {
            return Err(EncodedValidationError::invariant(
                "role-NFA dependency row is not canonical",
            ));
        }
        for &dependency in row {
            validate_id(dependency, component_count, "role-NFA dependency")?;
            if usize_id(dependency)? == component {
                return Err(EncodedValidationError::invariant(
                    "role-NFA dependency row contains a self edge",
                ));
            }
        }
    }
    for inclusion in &simple.simple_inclusions {
        validate_id(
            inclusion.sub_role_id,
            role_count,
            "role-NFA simple sub-role",
        )?;
        validate_id(
            inclusion.super_role_id,
            role_count,
            "role-NFA simple super-role",
        )?;
    }
    for inclusion in &complex.complex_inclusions {
        validate_id(
            inclusion.super_role_id,
            role_count,
            "role-NFA complex super-role",
        )?;
        if inclusion.chain_role_ids.len() < 2 {
            return Err(EncodedValidationError::invariant(
                "role-NFA complex inclusion has a short chain",
            ));
        }
        for &role_id in &inclusion.chain_role_ids {
            validate_id(role_id, role_count, "role-NFA complex chain role")?;
        }
    }
    validate_id(roles.top_object_role_id, role_count, "top object role")?;
    validate_id(
        roles.bottom_object_role_id,
        role_count,
        "bottom object role",
    )?;
    if hierarchy.object_component_by_role[usize_id(roles.top_object_role_id)?]
        != hierarchy.top_component_id
        || hierarchy.object_component_by_role[usize_id(roles.bottom_object_role_id)?]
            != hierarchy.bottom_component_id
    {
        return Err(EncodedValidationError::invariant(
            "role-NFA built-in components disagree with the role domain",
        ));
    }
    Ok(())
}

fn validate_output(phase: &RoleAutomataPhase) -> EncodedResult<()> {
    if phase.role_count == 0 || phase.component_count == 0 {
        return Err(EncodedValidationError::invariant(
            "role-NFA output has an empty domain",
        ));
    }
    validate_id(
        phase.bottom_role_id,
        phase.role_count,
        "role-NFA bottom role",
    )?;
    validate_id(phase.top_role_id, phase.role_count, "role-NFA top role")?;
    if phase
        .automata
        .windows(2)
        .any(|pair| pair[0].target_component_id >= pair[1].target_component_id)
    {
        return Err(EncodedValidationError::invariant(
            "role automata are not canonical by target component",
        ));
    }
    for automaton in &phase.automata {
        validate_automaton(automaton, phase.role_count, phase.component_count)?;
    }
    Ok(())
}

fn validate_automaton(
    automaton: &RoleAutomaton,
    role_count: usize,
    component_count: usize,
) -> EncodedResult<()> {
    if component_count != usize::MAX {
        validate_id(
            automaton.target_component_id,
            component_count,
            "role automaton target component",
        )?;
    }
    let state_count = usize_id(automaton.state_count)?;
    if state_count == 0 {
        return Err(EncodedValidationError::invariant(
            "role automaton has no states",
        ));
    }
    validate_id(
        automaton.initial_state,
        state_count,
        "role automaton initial state",
    )?;
    if automaton.final_states.is_empty()
        || automaton
            .final_states
            .windows(2)
            .any(|pair| pair[0] >= pair[1])
    {
        return Err(EncodedValidationError::invariant(
            "role automaton final states are empty or non-canonical",
        ));
    }
    for &state in &automaton.final_states {
        validate_id(state, state_count, "role automaton final state")?;
    }
    if automaton
        .transitions
        .windows(2)
        .any(|pair| compare_transition(&pair[0], &pair[1]).is_ge())
    {
        return Err(EncodedValidationError::invariant(
            "role automaton transitions are not canonical",
        ));
    }
    for transition in &automaton.transitions {
        validate_id(
            transition.source_state,
            state_count,
            "role automaton transition source",
        )?;
        validate_id(
            transition.target_state,
            state_count,
            "role automaton transition target",
        )?;
        if let Some(role_id) = transition.role_id {
            if role_count != usize::MAX {
                validate_id(role_id, role_count, "role automaton transition role")?;
            }
        }
    }
    Ok(())
}

fn validate_hierarchy_for_acceptance(
    phase: &RoleAutomataPhase,
    hierarchy: &ObjectRoleHierarchyPhase,
) -> EncodedResult<()> {
    if hierarchy.object_component_by_role.len() != phase.role_count
        || hierarchy.object_components.len() != phase.component_count
        || hierarchy.object_super_components.len() != phase.component_count
    {
        return Err(EncodedValidationError::invariant(
            "role acceptance hierarchy dimensions disagree with its automata",
        ));
    }
    Ok(())
}

fn clone_transitions(
    values: &[NfaTransition],
    name: &'static str,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<NfaTransition>> {
    let mut result = reserved_vec(values.len(), name, budget)?;
    result.extend_from_slice(values);
    Ok(result)
}

fn empty_rows(
    count: usize,
    name: &'static str,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<Vec<u32>>> {
    let mut rows = reserved_vec(count, name, budget)?;
    rows.resize_with(count, Vec::new);
    Ok(rows)
}

fn reserved_vec<T>(
    count: usize,
    name: &'static str,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<T>> {
    budget.claim_owned(count.checked_mul(size_of::<T>()).ok_or_else(|| {
        EncodedValidationError::resource(format!("{name} allocation overflowed"))
    })?)?;
    let mut values = Vec::new();
    values
        .try_reserve_exact(count)
        .map_err(|_| EncodedValidationError::resource(format!("{name} allocation failed")))?;
    Ok(values)
}

fn reserved_u32(
    count: usize,
    name: &'static str,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<u32>> {
    reserved_vec(count, name, budget)
}

fn reserved_usize(
    count: usize,
    name: &'static str,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<usize>> {
    reserved_vec(count, name, budget)
}

fn reserve_push<T>(
    target: &mut Vec<T>,
    value: T,
    name: &'static str,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    if target.len() == target.capacity() {
        let following_capacity = target.capacity().saturating_mul(2).max(4);
        let additional = following_capacity
            .checked_sub(target.capacity())
            .ok_or_else(|| {
                EncodedValidationError::resource(format!("{name} capacity overflowed"))
            })?;
        budget.claim_owned(additional.checked_mul(size_of::<T>()).ok_or_else(|| {
            EncodedValidationError::resource(format!("{name} allocation overflowed"))
        })?)?;
        target
            .try_reserve_exact(additional)
            .map_err(|_| EncodedValidationError::resource(format!("{name} allocation failed")))?;
    }
    target.push(value);
    Ok(())
}

fn filled_bool(
    count: usize,
    value: bool,
    name: &'static str,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<bool>> {
    let mut values = reserved_vec(count, name, budget)?;
    values.resize(count, value);
    Ok(values)
}

fn filled_u32(
    count: usize,
    value: u32,
    name: &'static str,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<u32>> {
    let mut values = reserved_u32(count, name, budget)?;
    values.resize(count, value);
    Ok(values)
}

fn filled_usize(
    count: usize,
    value: usize,
    name: &'static str,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<usize>> {
    let mut values = reserved_usize(count, name, budget)?;
    values.resize(count, value);
    Ok(values)
}

fn try_bool(count: usize, value: bool, name: &'static str) -> EncodedResult<Vec<bool>> {
    let mut values = Vec::new();
    values
        .try_reserve_exact(count)
        .map_err(|_| EncodedValidationError::resource(format!("{name} allocation failed")))?;
    values.resize(count, value);
    Ok(values)
}

fn try_reserved_u32(count: usize, name: &'static str) -> EncodedResult<Vec<u32>> {
    let mut values = Vec::new();
    values
        .try_reserve_exact(count)
        .map_err(|_| EncodedValidationError::resource(format!("{name} allocation failed")))?;
    Ok(values)
}

fn validate_id(value: u32, count: usize, name: &'static str) -> EncodedResult<()> {
    if usize_id(value)? >= count {
        Err(EncodedValidationError::invariant(format!(
            "{name} ID is dangling"
        )))
    } else {
        Ok(())
    }
}

fn validate_acceptance_id(value: u32, count: usize, name: &'static str) -> EncodedResult<()> {
    if usize_id(value)? >= count {
        Err(EncodedValidationError::protocol(format!(
            "object-role acceptance {name} ID is outside the role domain"
        )))
    } else {
        Ok(())
    }
}

fn usize_id(value: u32) -> EncodedResult<usize> {
    usize::try_from(value)
        .map_err(|_| EncodedValidationError::resource("role-NFA ID exceeds usize"))
}

fn u32_id(value: usize) -> EncodedResult<u32> {
    u32::try_from(value).map_err(|_| EncodedValidationError::resource("role-NFA ID exceeds u32"))
}

fn sort_work(count: usize) -> usize {
    if count < 2 {
        return count;
    }
    let comparisons = usize::BITS - (count - 1).leading_zeros();
    count.saturating_mul(usize::try_from(comparisons).unwrap_or(usize::MAX))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_budget() -> PhaseBudget {
        PhaseBudget::new(RoleAutomataPhaseLimits::default())
    }

    #[test]
    fn freeze_uses_scalar_breadth_first_state_order() -> EncodedResult<()> {
        let mut budget = test_budget();
        let mut mutable = MutableNfa::new();
        let initial = mutable.state(&mut budget)?;
        let final_state = mutable.state(&mut budget)?;
        let late = mutable.state(&mut budget)?;
        let early = mutable.state(&mut budget)?;
        mutable.transition(initial, Some(4), late, &mut budget)?;
        mutable.transition(initial, None, early, &mut budget)?;
        mutable.transition(early, Some(3), final_state, &mut budget)?;
        mutable.transition(late, Some(2), final_state, &mut budget)?;

        let frozen = freeze_automaton(7, mutable, initial, final_state, &mut budget)?;

        assert_eq!(frozen.state_count, 4);
        assert_eq!(frozen.initial_state, 0);
        assert_eq!(frozen.final_states, [3]);
        assert_eq!(
            frozen.transitions,
            [
                NfaTransition {
                    source_state: 0,
                    target_state: 1,
                    role_id: None,
                },
                NfaTransition {
                    source_state: 0,
                    target_state: 2,
                    role_id: Some(4),
                },
                NfaTransition {
                    source_state: 1,
                    target_state: 3,
                    role_id: Some(3),
                },
                NfaTransition {
                    source_state: 2,
                    target_state: 3,
                    role_id: Some(2),
                },
            ]
        );
        Ok(())
    }

    #[test]
    fn epsilon_nfa_acceptance_handles_transitive_loops() -> EncodedResult<()> {
        let automaton = RoleAutomaton {
            target_component_id: 0,
            state_count: 2,
            initial_state: 0,
            final_states: vec![1],
            transitions: vec![
                NfaTransition {
                    source_state: 0,
                    target_state: 1,
                    role_id: Some(2),
                },
                NfaTransition {
                    source_state: 1,
                    target_state: 0,
                    role_id: None,
                },
            ],
        };

        let limit = RoleAutomataPhaseLimits::default().max_work;
        assert!(!automaton_accepts(&automaton, &[], limit)?);
        assert!(automaton_accepts(&automaton, &[2], limit)?);
        assert!(automaton_accepts(&automaton, &[2, 2, 2], limit)?);
        assert!(!automaton_accepts(&automaton, &[2, 3], limit)?);
        assert_eq!(
            automaton_accepts(&automaton, &[2], 0)
                .err()
                .map(|error| error.code),
            Some("NATIVE_ENCODED_RESOURCE_LIMIT")
        );
        Ok(())
    }

    #[test]
    fn mutable_nfa_enforces_local_state_and_transition_limits() -> EncodedResult<()> {
        let limits = RoleAutomataPhaseLimits {
            max_states: 2,
            max_transitions: 1,
            ..RoleAutomataPhaseLimits::default()
        };
        let mut budget = PhaseBudget::new(limits);
        let mut mutable = MutableNfa::new();
        let initial = mutable.state(&mut budget)?;
        let final_state = mutable.state(&mut budget)?;
        assert_eq!(
            mutable.state(&mut budget).err().map(|error| error.code),
            Some("NATIVE_ENCODED_RESOURCE_LIMIT")
        );
        mutable.transition(initial, Some(0), final_state, &mut budget)?;
        assert_eq!(
            mutable
                .transition(final_state, None, initial, &mut budget)
                .err()
                .map(|error| error.code),
            Some("NATIVE_ENCODED_RESOURCE_LIMIT")
        );
        Ok(())
    }
}
