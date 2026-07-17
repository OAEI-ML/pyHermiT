//! Deterministic, Python-independent execution of compiled object-role epsilon NFAs.
//!
//! The Python compiler remains responsible for OWL 2 regularity and stable state
//! numbering.  This module validates the frozen result once, owns it, and provides a
//! streaming cursor used by native universal-restriction propagation.  No NFA is
//! determinized: doing so can expand regular role languages exponentially.
// SPDX-License-Identifier: LGPL-3.0-or-later

#![allow(
    clippy::missing_errors_doc,
    clippy::module_name_repetitions,
    clippy::too_many_lines
)]

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::error::Error;
use std::fmt;

use serde::{Deserialize, Serialize};

const POLL_STRIDE: usize = 1_024;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RoleErrorKind {
    Invalid,
    Resource,
    Cancelled,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RoleError {
    pub kind: RoleErrorKind,
    pub message: String,
    pub limit: Option<&'static str>,
    pub observed: Option<u64>,
    pub allowed: Option<u64>,
}

impl RoleError {
    #[must_use]
    pub fn invalid(message: impl Into<String>) -> Self {
        Self {
            kind: RoleErrorKind::Invalid,
            message: message.into(),
            limit: None,
            observed: None,
            allowed: None,
        }
    }

    #[must_use]
    pub fn resource(limit: &'static str, observed: u64, allowed: u64) -> Self {
        Self {
            kind: RoleErrorKind::Resource,
            message: format!("native role resource limit exceeded: {limit}"),
            limit: Some(limit),
            observed: Some(observed),
            allowed: Some(allowed),
        }
    }

    #[must_use]
    pub fn cancelled(message: impl Into<String>) -> Self {
        Self {
            kind: RoleErrorKind::Cancelled,
            message: message.into(),
            limit: None,
            observed: None,
            allowed: None,
        }
    }
}

impl fmt::Display for RoleError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.message)
    }
}

impl Error for RoleError {}

pub trait RoleControl {
    fn poll(&self) -> Result<(), RoleError>;

    fn observe_memory(&self, _bytes: u64) -> Result<(), RoleError> {
        self.poll()
    }
}

#[derive(Clone, Copy, Debug, Default)]
pub struct NeverCancel;

impl RoleControl for NeverCancel {
    fn poll(&self) -> Result<(), RoleError> {
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RoleLimits {
    pub max_roles: u32,
    pub max_automata: u32,
    pub max_states: u32,
    pub max_transitions: u32,
    pub max_word_length: u32,
    pub max_memory_bytes: u64,
}

impl Default for RoleLimits {
    fn default() -> Self {
        Self {
            max_roles: 1_000_000,
            max_automata: 1_000_000,
            max_states: 5_000_000,
            max_transitions: 20_000_000,
            max_word_length: 1_000_000,
            max_memory_bytes: 512 * 1024 * 1024,
        }
    }
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub struct RoleTransition {
    pub source_state: u32,
    pub target_state: u32,
    pub role_id: Option<u32>,
}

impl RoleTransition {
    #[must_use]
    pub const fn epsilon(source_state: u32, target_state: u32) -> Self {
        Self {
            source_state,
            target_state,
            role_id: None,
        }
    }

    #[must_use]
    pub const fn labelled(source_state: u32, role_id: u32, target_state: u32) -> Self {
        Self {
            source_state,
            target_state,
            role_id: Some(role_id),
        }
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct RoleAutomatonWire {
    pub component_id: u32,
    pub state_count: u32,
    pub initial_state: u32,
    pub final_states: Vec<u32>,
    pub transitions: Vec<RoleTransition>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RoleAutomaton {
    component_id: u32,
    state_count: u32,
    initial_state: u32,
    final_states: Vec<u32>,
    transitions: Vec<RoleTransition>,
    by_source: Vec<Vec<(Option<u32>, u32)>>,
}

impl RoleAutomaton {
    pub fn from_wire(
        wire: RoleAutomatonWire,
        role_count: u32,
        limits: RoleLimits,
        control: &impl RoleControl,
    ) -> Result<Self, RoleError> {
        control.poll()?;
        if wire.state_count == 0 {
            return Err(RoleError::invalid(
                "role automata require at least one state",
            ));
        }
        if wire.state_count > limits.max_states {
            return Err(RoleError::resource(
                "max_states",
                u64::from(wire.state_count),
                u64::from(limits.max_states),
            ));
        }
        if wire.initial_state >= wire.state_count {
            return Err(RoleError::invalid(
                "role automaton initial state is outside its state range",
            ));
        }
        if wire.final_states.is_empty() {
            return Err(RoleError::invalid(
                "role automata require at least one final state",
            ));
        }
        if wire.transitions.len() > usize::try_from(limits.max_transitions).unwrap_or(usize::MAX) {
            return Err(RoleError::resource(
                "max_transitions",
                u64::try_from(wire.transitions.len()).unwrap_or(u64::MAX),
                u64::from(limits.max_transitions),
            ));
        }

        let mut finals = wire.final_states;
        finals.sort_unstable();
        finals.dedup();
        if finals.iter().any(|state| *state >= wire.state_count) {
            return Err(RoleError::invalid(
                "role automaton final state is outside its state range",
            ));
        }

        let mut transitions = wire.transitions;
        transitions.sort_unstable();
        transitions.dedup();
        let state_count = usize::try_from(wire.state_count)
            .map_err(|_| RoleError::invalid("role automaton state count is not addressable"))?;
        let mut by_source = vec![Vec::new(); state_count];
        for (offset, transition) in transitions.iter().enumerate() {
            if offset % POLL_STRIDE == 0 {
                control.poll()?;
            }
            if transition.source_state >= wire.state_count
                || transition.target_state >= wire.state_count
            {
                return Err(RoleError::invalid(
                    "role automaton transition references an absent state",
                ));
            }
            if transition
                .role_id
                .is_some_and(|role_id| role_id >= role_count)
            {
                return Err(RoleError::invalid(
                    "role automaton transition references an absent role",
                ));
            }
            let source = usize::try_from(transition.source_state)
                .map_err(|_| RoleError::invalid("role source state is not addressable"))?;
            by_source[source].push((transition.role_id, transition.target_state));
        }
        let memory = estimate_automaton_bytes(wire.state_count, transitions.len())?;
        if memory > limits.max_memory_bytes {
            return Err(RoleError::resource(
                "max_memory_bytes",
                memory,
                limits.max_memory_bytes,
            ));
        }
        control.observe_memory(memory)?;
        let automaton = Self {
            component_id: wire.component_id,
            state_count: wire.state_count,
            initial_state: wire.initial_state,
            final_states: finals,
            transitions,
            by_source,
        };
        if !automaton.has_accepting_path(control)? {
            return Err(RoleError::invalid("role automaton has no accepting path"));
        }
        Ok(automaton)
    }

    #[must_use]
    pub const fn component_id(&self) -> u32 {
        self.component_id
    }

    #[must_use]
    pub const fn state_count(&self) -> u32 {
        self.state_count
    }

    #[must_use]
    pub fn transitions(&self) -> &[RoleTransition] {
        &self.transitions
    }

    pub fn cursor(&self, control: &impl RoleControl) -> Result<RoleCursor, RoleError> {
        let mut active = StateSet::new(self.state_count)?;
        active.insert(self.initial_state)?;
        self.epsilon_close(&mut active, control)?;
        Ok(RoleCursor {
            component_id: self.component_id,
            active,
        })
    }

    pub fn advance(
        &self,
        cursor: &mut RoleCursor,
        role_id: u32,
        role_count: u32,
        control: &impl RoleControl,
    ) -> Result<bool, RoleError> {
        if cursor.component_id != self.component_id || cursor.active.state_count != self.state_count
        {
            return Err(RoleError::invalid(
                "role cursor belongs to a different automaton",
            ));
        }
        if role_id >= role_count {
            return Err(RoleError::invalid("role word references an absent role"));
        }
        control.poll()?;
        let mut following = StateSet::new(self.state_count)?;
        let mut visited = 0_usize;
        for source in cursor.active.iter() {
            let source_index = usize::try_from(source)
                .map_err(|_| RoleError::invalid("active role state is not addressable"))?;
            for (label, target) in &self.by_source[source_index] {
                visited = visited.saturating_add(1);
                if visited % POLL_STRIDE == 0 {
                    control.poll()?;
                }
                if *label == Some(role_id) {
                    following.insert(*target)?;
                }
            }
        }
        if following.is_empty() {
            cursor.active = following;
            return Ok(false);
        }
        self.epsilon_close(&mut following, control)?;
        cursor.active = following;
        Ok(true)
    }

    pub fn accepts(
        &self,
        word: &[u32],
        role_count: u32,
        limits: RoleLimits,
        control: &impl RoleControl,
    ) -> Result<bool, RoleError> {
        if word.len() > usize::try_from(limits.max_word_length).unwrap_or(usize::MAX) {
            return Err(RoleError::resource(
                "max_word_length",
                u64::try_from(word.len()).unwrap_or(u64::MAX),
                u64::from(limits.max_word_length),
            ));
        }
        let mut cursor = self.cursor(control)?;
        for role_id in word {
            if !self.advance(&mut cursor, *role_id, role_count, control)? {
                return Ok(false);
            }
        }
        Ok(self.is_accepting(&cursor))
    }

    #[must_use]
    pub fn is_accepting(&self, cursor: &RoleCursor) -> bool {
        self.final_states
            .iter()
            .any(|state| cursor.active.contains(*state))
    }

    fn epsilon_close(
        &self,
        states: &mut StateSet,
        control: &impl RoleControl,
    ) -> Result<(), RoleError> {
        let mut pending: VecDeque<_> = states.iter().collect();
        let mut visited = 0_usize;
        while let Some(source) = pending.pop_front() {
            let source_index = usize::try_from(source)
                .map_err(|_| RoleError::invalid("epsilon source state is not addressable"))?;
            for (label, target) in &self.by_source[source_index] {
                visited = visited.saturating_add(1);
                if visited % POLL_STRIDE == 0 {
                    control.poll()?;
                }
                if label.is_none() && states.insert(*target)? {
                    pending.push_back(*target);
                }
            }
        }
        Ok(())
    }

    fn has_accepting_path(&self, control: &impl RoleControl) -> Result<bool, RoleError> {
        let mut reached = StateSet::new(self.state_count)?;
        reached.insert(self.initial_state)?;
        let mut pending = VecDeque::from([self.initial_state]);
        let mut visited = 0_usize;
        while let Some(source) = pending.pop_front() {
            if self.final_states.binary_search(&source).is_ok() {
                return Ok(true);
            }
            let source_index = usize::try_from(source)
                .map_err(|_| RoleError::invalid("reachable state is not addressable"))?;
            for (_label, target) in &self.by_source[source_index] {
                visited = visited.saturating_add(1);
                if visited % POLL_STRIDE == 0 {
                    control.poll()?;
                }
                if reached.insert(*target)? {
                    pending.push_back(*target);
                }
            }
        }
        Ok(false)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RoleCursor {
    component_id: u32,
    active: StateSet,
}

impl RoleCursor {
    #[must_use]
    pub fn active_states(&self) -> Vec<u32> {
        self.active.iter().collect()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct StateSet {
    words: Vec<u64>,
    state_count: u32,
}

impl StateSet {
    fn new(state_count: u32) -> Result<Self, RoleError> {
        let word_count = state_count
            .checked_add(63)
            .ok_or_else(|| RoleError::invalid("role state bitset length overflow"))?
            / 64;
        let word_count = usize::try_from(word_count)
            .map_err(|_| RoleError::invalid("role state bitset is not addressable"))?;
        Ok(Self {
            words: vec![0; word_count],
            state_count,
        })
    }

    fn insert(&mut self, state: u32) -> Result<bool, RoleError> {
        if state >= self.state_count {
            return Err(RoleError::invalid("role state is outside its state set"));
        }
        let word = usize::try_from(state / 64)
            .map_err(|_| RoleError::invalid("role state is not addressable"))?;
        let mask = 1_u64 << (state % 64);
        let present = self.words[word] & mask != 0;
        self.words[word] |= mask;
        Ok(!present)
    }

    #[must_use]
    fn contains(&self, state: u32) -> bool {
        if state >= self.state_count {
            return false;
        }
        usize::try_from(state / 64)
            .ok()
            .is_some_and(|word| self.words[word] & (1_u64 << (state % 64)) != 0)
    }

    #[must_use]
    fn is_empty(&self) -> bool {
        self.words.iter().all(|word| *word == 0)
    }

    fn iter(&self) -> impl Iterator<Item = u32> + '_ {
        self.words
            .iter()
            .enumerate()
            .flat_map(|(word_index, word)| {
                let mut remaining = *word;
                std::iter::from_fn(move || {
                    if remaining == 0 {
                        return None;
                    }
                    let bit = remaining.trailing_zeros();
                    remaining &= remaining - 1;
                    u32::try_from(word_index)
                        .ok()
                        .and_then(|index| index.checked_mul(64))
                        .and_then(|base| base.checked_add(bit))
                })
            })
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BuiltinRoleSemantics {
    Normal,
    Universal,
    Empty,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RoleRuntime {
    role_count: u32,
    inverse_role_ids: Vec<u32>,
    top_role_id: u32,
    bottom_role_id: u32,
    automata: BTreeMap<u32, RoleAutomaton>,
    limits: RoleLimits,
}

impl RoleRuntime {
    pub fn new(
        role_count: u32,
        inverse_role_ids: Vec<u32>,
        top_role_id: u32,
        bottom_role_id: u32,
        automata: Vec<RoleAutomatonWire>,
        limits: RoleLimits,
        control: &impl RoleControl,
    ) -> Result<Self, RoleError> {
        control.poll()?;
        if role_count == 0 {
            return Err(RoleError::invalid(
                "role runtimes require at least one role",
            ));
        }
        if role_count > limits.max_roles {
            return Err(RoleError::resource(
                "max_roles",
                u64::from(role_count),
                u64::from(limits.max_roles),
            ));
        }
        if inverse_role_ids.len()
            != usize::try_from(role_count)
                .map_err(|_| RoleError::invalid("role count is not addressable"))?
        {
            return Err(RoleError::invalid("inverse role map is incomplete"));
        }
        if top_role_id >= role_count || bottom_role_id >= role_count {
            return Err(RoleError::invalid("built-in role ID is dangling"));
        }
        for (role, inverse) in inverse_role_ids.iter().copied().enumerate() {
            let inverse_index = usize::try_from(inverse)
                .map_err(|_| RoleError::invalid("inverse role ID is not addressable"))?;
            if inverse >= role_count
                || inverse_role_ids
                    .get(inverse_index)
                    .copied()
                    .and_then(|value| usize::try_from(value).ok())
                    != Some(role)
            {
                return Err(RoleError::invalid("inverse role map must be an involution"));
            }
        }
        if inverse_role_ids[usize::try_from(top_role_id).unwrap_or_default()] != top_role_id
            || inverse_role_ids[usize::try_from(bottom_role_id).unwrap_or_default()]
                != bottom_role_id
        {
            return Err(RoleError::invalid(
                "top and bottom object roles must be self-inverse",
            ));
        }
        if automata.len() > usize::try_from(limits.max_automata).unwrap_or(usize::MAX) {
            return Err(RoleError::resource(
                "max_automata",
                u64::try_from(automata.len()).unwrap_or(u64::MAX),
                u64::from(limits.max_automata),
            ));
        }
        let mut compiled = BTreeMap::new();
        let mut total_states = 0_u64;
        let mut total_transitions = 0_u64;
        let mut total_memory = 0_u64;
        for (offset, wire) in automata.into_iter().enumerate() {
            if offset % POLL_STRIDE == 0 {
                control.poll()?;
            }
            let automaton = RoleAutomaton::from_wire(wire, role_count, limits, control)?;
            total_states = total_states
                .checked_add(u64::from(automaton.state_count()))
                .ok_or_else(|| RoleError::invalid("aggregate role state count overflow"))?;
            total_transitions = total_transitions
                .checked_add(u64::try_from(automaton.transitions().len()).unwrap_or(u64::MAX))
                .ok_or_else(|| RoleError::invalid("aggregate role transition count overflow"))?;
            total_memory = total_memory
                .checked_add(estimate_automaton_bytes(
                    automaton.state_count(),
                    automaton.transitions().len(),
                )?)
                .ok_or_else(|| RoleError::invalid("aggregate role memory estimate overflow"))?;
            if total_states > u64::from(limits.max_states) {
                return Err(RoleError::resource(
                    "max_states",
                    total_states,
                    u64::from(limits.max_states),
                ));
            }
            if total_transitions > u64::from(limits.max_transitions) {
                return Err(RoleError::resource(
                    "max_transitions",
                    total_transitions,
                    u64::from(limits.max_transitions),
                ));
            }
            if total_memory > limits.max_memory_bytes {
                return Err(RoleError::resource(
                    "max_memory_bytes",
                    total_memory,
                    limits.max_memory_bytes,
                ));
            }
            if compiled
                .insert(automaton.component_id(), automaton)
                .is_some()
            {
                return Err(RoleError::invalid(
                    "role automata must have unique component IDs",
                ));
            }
        }
        control.observe_memory(total_memory)?;
        Ok(Self {
            role_count,
            inverse_role_ids,
            top_role_id,
            bottom_role_id,
            automata: compiled,
            limits,
        })
    }

    #[must_use]
    pub fn automaton(&self, component_id: u32) -> Option<&RoleAutomaton> {
        self.automata.get(&component_id)
    }

    #[must_use]
    pub const fn builtin_semantics(&self, role_id: u32) -> Option<BuiltinRoleSemantics> {
        if role_id >= self.role_count {
            return None;
        }
        Some(if role_id == self.top_role_id {
            BuiltinRoleSemantics::Universal
        } else if role_id == self.bottom_role_id {
            BuiltinRoleSemantics::Empty
        } else {
            BuiltinRoleSemantics::Normal
        })
    }

    pub fn inverse_word(&self, word: &[u32]) -> Result<Vec<u32>, RoleError> {
        if word.len() > usize::try_from(self.limits.max_word_length).unwrap_or(usize::MAX) {
            return Err(RoleError::resource(
                "max_word_length",
                u64::try_from(word.len()).unwrap_or(u64::MAX),
                u64::from(self.limits.max_word_length),
            ));
        }
        word.iter()
            .rev()
            .map(|role_id| {
                let index = usize::try_from(*role_id)
                    .map_err(|_| RoleError::invalid("role word ID is not addressable"))?;
                self.inverse_role_ids
                    .get(index)
                    .copied()
                    .ok_or_else(|| RoleError::invalid("role word references an absent role"))
            })
            .collect()
    }

    pub fn accepts(
        &self,
        component_id: u32,
        word: &[u32],
        control: &impl RoleControl,
    ) -> Result<bool, RoleError> {
        if word.contains(&self.bottom_role_id) {
            // A relational composition containing the empty relation is empty and
            // is therefore included in every target role.
            return Ok(true);
        }
        let automaton = self
            .automata
            .get(&component_id)
            .ok_or_else(|| RoleError::invalid("requested role component has no automaton"))?;
        automaton.accepts(word, self.role_count, self.limits, control)
    }

    pub fn accepted_components(
        &self,
        word: &[u32],
        control: &impl RoleControl,
    ) -> Result<Vec<u32>, RoleError> {
        let mut result = Vec::new();
        for (offset, (component, automaton)) in self.automata.iter().enumerate() {
            if offset % POLL_STRIDE == 0 {
                control.poll()?;
            }
            if word.contains(&self.bottom_role_id)
                || automaton.accepts(word, self.role_count, self.limits, control)?
            {
                result.push(*component);
            }
        }
        Ok(result)
    }

    #[must_use]
    pub fn component_ids(&self) -> BTreeSet<u32> {
        self.automata.keys().copied().collect()
    }
}

fn estimate_automaton_bytes(state_count: u32, transition_count: usize) -> Result<u64, RoleError> {
    let states = u64::from(state_count)
        .checked_mul(32)
        .ok_or_else(|| RoleError::invalid("role state allocation estimate overflow"))?;
    let transitions = u64::try_from(transition_count)
        .unwrap_or(u64::MAX)
        .checked_mul(32)
        .ok_or_else(|| RoleError::invalid("role transition allocation estimate overflow"))?;
    states
        .checked_add(transitions)
        .ok_or_else(|| RoleError::invalid("role allocation estimate overflow"))
}

#[cfg(test)]
mod tests;
