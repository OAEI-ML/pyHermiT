//! Bounded symbolic automata for XML Schema regular expressions.
//!
//! This is deliberately not a wrapper around Rust's regex syntax. Patterns are
//! implicitly anchored and are parsed according to the XML Schema language used by
//! OWL datatype facets. Boolean language operations are represented with derivatives,
//! so intersection, complement, membership, emptiness, and bounded witnesses remain
//! exact over the XML character universe.
// SPDX-License-Identifier: LGPL-3.0-or-later

// `is_multiple_of` is newer than the crate's Rust 1.83 MSRV.
#![allow(clippy::manual_is_multiple_of)]

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::sync::{Arc, Mutex, MutexGuard, OnceLock};

use num_bigint::BigUint;
use num_traits::{One, ToPrimitive, Zero};

use super::value::{DatatypeControl, DatatypeError};
use super::xsd_unicode_3_2::{CATEGORY_CODE_NAMES, CATEGORY_RANGES_PACKED, PINNED_UNICODE_VERSION};

pub const XSD_REGEX_UNICODE_VERSION: &str = PINNED_UNICODE_VERSION;

const XML_INTERVALS: [(u32, u32); 5] = [
    (0x9, 0xA),
    (0xD, 0xD),
    (0x20, 0xD7FF),
    (0xE000, 0xFFFD),
    (0x0001_0000, 0x0010_FFFF),
];

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RegexLimits {
    pub max_lexical_characters: u64,
    pub max_enumeration_values: u64,
    pub max_pattern_states: u64,
    pub max_pattern_transitions: u64,
    pub max_pattern_depth: u64,
    pub cancellation_poll_stride: u64,
}

impl Default for RegexLimits {
    fn default() -> Self {
        Self {
            max_lexical_characters: 1_000_000,
            max_enumeration_values: 100_000,
            max_pattern_states: 20_000,
            max_pattern_transitions: 200_000,
            max_pattern_depth: 512,
            cancellation_poll_stride: 64,
        }
    }
}

impl RegexLimits {
    fn validate(self) -> Result<Self, DatatypeError> {
        let values = [
            ("max_lexical_characters", self.max_lexical_characters),
            ("max_enumeration_values", self.max_enumeration_values),
            ("max_pattern_states", self.max_pattern_states),
            ("max_pattern_transitions", self.max_pattern_transitions),
            ("max_pattern_depth", self.max_pattern_depth),
            ("cancellation_poll_stride", self.cancellation_poll_stride),
        ];
        if let Some((name, _)) = values.into_iter().find(|(_, value)| *value == 0) {
            return Err(DatatypeError::invalid(format!(
                "native XSD regex limit must be positive: {name}"
            )));
        }
        Ok(self)
    }
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CharSet {
    intervals: Vec<(u32, u32)>,
}

impl CharSet {
    pub fn new(intervals: Vec<(u32, u32)>) -> Result<Self, DatatypeError> {
        Self::normalize(intervals)
    }

    fn normalize(intervals: Vec<(u32, u32)>) -> Result<Self, DatatypeError> {
        for (lower, upper) in &intervals {
            if lower > upper || *upper > 0x0010_FFFF {
                return Err(DatatypeError::invalid(
                    "invalid native XSD regex character interval",
                ));
            }
        }
        Ok(Self::normalize_valid(intervals))
    }

    fn normalize_valid(mut intervals: Vec<(u32, u32)>) -> Self {
        intervals.sort_unstable();
        let mut output: Vec<(u32, u32)> = Vec::with_capacity(intervals.len());
        for (lower, upper) in intervals {
            if let Some(last) = output.last_mut() {
                if lower <= last.1.saturating_add(1) {
                    last.1 = last.1.max(upper);
                    continue;
                }
            }
            output.push((lower, upper));
        }
        Self { intervals: output }
    }

    const fn from_valid(intervals: Vec<(u32, u32)>) -> Self {
        Self { intervals }
    }

    pub fn one(codepoint: u32) -> Result<Self, DatatypeError> {
        Self::new(vec![(codepoint, codepoint)])
    }

    #[must_use]
    pub fn intervals(&self) -> &[(u32, u32)] {
        &self.intervals
    }

    #[must_use]
    pub fn contains(&self, codepoint: u32) -> bool {
        for (lower, upper) in &self.intervals {
            if codepoint < *lower {
                return false;
            }
            if codepoint <= *upper {
                return true;
            }
        }
        false
    }

    #[must_use]
    pub fn union(&self, other: &Self) -> Self {
        let mut intervals = self.intervals.clone();
        intervals.extend_from_slice(&other.intervals);
        Self::normalize_valid(intervals)
    }

    #[must_use]
    pub fn intersection(&self, other: &Self) -> Self {
        let mut output = Vec::new();
        let (mut left_index, mut right_index) = (0, 0);
        while left_index < self.intervals.len() && right_index < other.intervals.len() {
            let left = self.intervals[left_index];
            let right = other.intervals[right_index];
            let lower = left.0.max(right.0);
            let upper = left.1.min(right.1);
            if lower <= upper {
                output.push((lower, upper));
            }
            if left.1 < right.1 {
                left_index += 1;
            } else {
                right_index += 1;
            }
        }
        Self::from_valid(output)
    }

    #[must_use]
    pub fn difference(&self, other: &Self) -> Self {
        let mut output = Vec::new();
        for (lower, upper) in &self.intervals {
            let mut cursor = *lower;
            for (excluded_lower, excluded_upper) in &other.intervals {
                if *excluded_upper < cursor {
                    continue;
                }
                if *excluded_lower > *upper {
                    break;
                }
                if cursor < *excluded_lower {
                    output.push((cursor, (*upper).min(excluded_lower.saturating_sub(1))));
                }
                cursor = cursor.max(excluded_upper.saturating_add(1));
                if cursor > *upper {
                    break;
                }
            }
            if cursor <= *upper {
                output.push((cursor, *upper));
            }
        }
        Self::from_valid(output)
    }

    #[must_use]
    pub fn complement(&self) -> Self {
        xml_characters().difference(self)
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.intervals.is_empty()
    }

    #[must_use]
    pub fn cardinality(&self) -> u64 {
        self.intervals
            .iter()
            .map(|(lower, upper)| u64::from(*upper - *lower) + 1)
            .sum()
    }

    fn first_outside(&self, blocked: &BTreeSet<u32>) -> Option<u32> {
        for (lower, upper) in &self.intervals {
            let mut candidate = *lower;
            for blocked_codepoint in blocked.range(*lower..=*upper) {
                if candidate < *blocked_codepoint {
                    return Some(candidate);
                }
                candidate = blocked_codepoint.saturating_add(1);
            }
            if candidate <= *upper {
                return Some(candidate);
            }
        }
        None
    }
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Expr {
    Empty,
    Epsilon,
    Characters(CharSet),
    Alternative(BTreeSet<Self>),
    Sequence(Vec<Self>),
    Star(Box<Self>),
    Intersection(BTreeSet<Self>),
    Complement(Box<Self>),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct CachedMatchTransition {
    target: usize,
    derivative_work: u64,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct CachedNullability {
    value: bool,
    derivative_work: u64,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct CachedMatchPath {
    result: bool,
    transitions: u64,
    derivative_work: u64,
}

#[derive(Debug)]
struct MatchCache {
    states: Vec<Expr>,
    state_ids: BTreeMap<Expr, usize>,
    transitions: BTreeMap<(usize, u32), CachedMatchTransition>,
    nullability: BTreeMap<usize, CachedNullability>,
    expression_depth: u64,
}

impl MatchCache {
    fn new(expression: &Expr) -> Self {
        Self {
            states: vec![expression.clone()],
            state_ids: BTreeMap::from([(expression.clone(), 0)]),
            transitions: BTreeMap::new(),
            nullability: BTreeMap::new(),
            expression_depth: maximum_expression_depth(expression),
        }
    }

    fn validate_for(&self, limits: RegexLimits) -> Result<u64, DatatypeError> {
        let states = u64::try_from(self.states.len()).unwrap_or(u64::MAX);
        if states > limits.max_pattern_states {
            return Err(DatatypeError::resource(
                "max_pattern_states",
                states,
                limits.max_pattern_states,
            ));
        }
        let transitions = u64::try_from(self.transitions.len()).unwrap_or(u64::MAX);
        if transitions > limits.max_pattern_transitions {
            return Err(DatatypeError::resource(
                "max_pattern_transitions",
                transitions,
                limits.max_pattern_transitions,
            ));
        }
        let allowed_depth = limits.max_pattern_depth.saturating_mul(2);
        if self.expression_depth > allowed_depth {
            return Err(DatatypeError::resource(
                "max_pattern_depth",
                self.expression_depth,
                allowed_depth,
            ));
        }
        Ok(self.memory_bytes())
    }

    fn cached_path(&self, value: &str) -> Option<CachedMatchPath> {
        let mut state = 0_usize;
        let mut transitions = 0_u64;
        let mut derivative_work = 0_u64;
        for character in value.chars() {
            let cached = self.transitions.get(&(state, u32::from(character)))?;
            state = cached.target;
            transitions = transitions.saturating_add(1);
            derivative_work = derivative_work.saturating_add(cached.derivative_work);
        }
        let nullable = self.nullability.get(&state)?;
        Some(CachedMatchPath {
            result: nullable.value,
            transitions,
            derivative_work: derivative_work.saturating_add(nullable.derivative_work),
        })
    }

    fn memory_bytes(&self) -> u64 {
        Self::memory_bytes_for(
            self.states.len(),
            self.state_ids.len(),
            self.transitions.len(),
            self.nullability.len(),
        )
    }

    fn memory_bytes_for(
        state_count: usize,
        state_id_count: usize,
        transition_count: usize,
        nullability_count: usize,
    ) -> u64 {
        let states = u64::try_from(state_count)
            .unwrap_or(u64::MAX)
            .saturating_mul(u64::try_from(std::mem::size_of::<Expr>()).unwrap_or(u64::MAX));
        let state_ids = u64::try_from(state_id_count)
            .unwrap_or(u64::MAX)
            .saturating_mul(
                u64::try_from(std::mem::size_of::<(Expr, usize)>()).unwrap_or(u64::MAX),
            );
        let transitions = u64::try_from(transition_count)
            .unwrap_or(u64::MAX)
            .saturating_mul(
                u64::try_from(std::mem::size_of::<((usize, u32), CachedMatchTransition)>())
                    .unwrap_or(u64::MAX),
            );
        let nullability = u64::try_from(nullability_count)
            .unwrap_or(u64::MAX)
            .saturating_mul(
                u64::try_from(std::mem::size_of::<(usize, CachedNullability)>())
                    .unwrap_or(u64::MAX),
            );
        states
            .saturating_add(state_ids)
            .saturating_add(transitions)
            .saturating_add(nullability)
    }
}

#[derive(Clone, Debug)]
pub struct XsdRegex {
    expression: Expr,
    automaton: Arc<OnceLock<Dfa>>,
    matches: Arc<OnceLock<Mutex<MatchCache>>>,
}

impl PartialEq for XsdRegex {
    fn eq(&self, other: &Self) -> bool {
        self.expression == other.expression
    }
}

impl Eq for XsdRegex {}

impl XsdRegex {
    fn from_expression(expression: Expr) -> Self {
        Self {
            expression,
            automaton: Arc::new(OnceLock::new()),
            matches: Arc::new(OnceLock::new()),
        }
    }

    pub fn compile<C: DatatypeControl>(
        pattern: &str,
        limits: RegexLimits,
        control: &C,
    ) -> Result<Self, DatatypeError> {
        let limits = limits.validate()?;
        control.poll()?;
        let observed = bounded_character_count(pattern, limits.max_lexical_characters)?;
        if observed > limits.max_lexical_characters {
            return Err(DatatypeError::resource(
                "max_lexical_characters",
                observed,
                limits.max_lexical_characters,
            ));
        }
        let mut parser = Parser::new(pattern, limits, control)?;
        let expression = parser.parse()?;
        control.poll()?;
        Ok(Self::from_expression(expression))
    }

    pub fn compile_default(
        pattern: &str,
        control: &impl DatatypeControl,
    ) -> Result<Self, DatatypeError> {
        Self::compile(pattern, RegexLimits::default(), control)
    }

    #[must_use]
    pub fn all() -> Self {
        Self::from_expression(star(Expr::Characters(xml_characters())))
    }

    #[must_use]
    pub fn empty() -> Self {
        Self::from_expression(Expr::Empty)
    }

    #[must_use]
    pub fn characters(characters: CharSet) -> Self {
        Self::from_expression(Expr::Characters(characters))
    }

    pub fn length_range<C: DatatypeControl>(
        minimum: u64,
        maximum: Option<u64>,
        limits: RegexLimits,
        control: &C,
    ) -> Result<Self, DatatypeError> {
        let limits = limits.validate()?;
        control.poll()?;
        if maximum.is_some_and(|value| value < minimum) {
            return Err(DatatypeError::invalid(
                "maximum length must not be smaller than minimum length",
            ));
        }
        let expansion = maximum.unwrap_or(minimum);
        if expansion > limits.max_pattern_states {
            return Err(DatatypeError::resource(
                "max_pattern_states",
                expansion,
                limits.max_pattern_states,
            ));
        }
        let expansion_usize = usize::try_from(expansion)
            .map_err(|_| DatatypeError::resource("max_pattern_states", expansion, u64::MAX))?;
        let minimum_usize = usize::try_from(minimum)
            .map_err(|_| DatatypeError::resource("max_pattern_states", minimum, u64::MAX))?;
        let character = Expr::Characters(xml_characters());
        control.observe_memory(
            u64::try_from(expansion_usize)
                .unwrap_or(u64::MAX)
                .saturating_mul(u64::try_from(std::mem::size_of::<Expr>()).unwrap_or(u64::MAX)),
        )?;
        Ok(Self::from_expression(repeat_range(
            character,
            minimum_usize,
            maximum.map(|_| expansion_usize),
        )))
    }

    pub fn fullmatch<C: DatatypeControl>(
        &self,
        value: &str,
        limits: RegexLimits,
        control: &C,
    ) -> Result<bool, DatatypeError> {
        let limits = limits.validate()?;
        let observed = bounded_character_count(value, limits.max_lexical_characters)?;
        if observed > limits.max_lexical_characters {
            return Err(DatatypeError::resource(
                "max_lexical_characters",
                observed,
                limits.max_lexical_characters,
            ));
        }
        control.poll()?;
        if value
            .chars()
            .any(|character| !is_xml_codepoint(u32::from(character)))
        {
            return Ok(false);
        }
        if self.matches.get().is_none() {
            control.observe_memory(MatchCache::memory_bytes_for(1, 1, 0, 0))?;
        }
        let cached_path = {
            let cache = self.lock_match_cache()?;
            let memory_bytes = cache.validate_for(limits)?;
            let path = cache.cached_path(value);
            drop(cache);
            (memory_bytes, path)
        };
        control.observe_memory(cached_path.0)?;
        control.poll()?;
        let mut budget = Budget::new(limits, control)?;
        if let Some(path) = cached_path.1 {
            budget.cached_transitions(path.transitions)?;
            budget.cached_derivatives(path.derivative_work)?;
            budget.finish()?;
            return Ok(path.result);
        }
        let mut state = 0_usize;
        for character in value.chars() {
            state = self.match_transition(state, u32::from(character), &mut budget)?;
        }
        let result = self.match_nullable(state, &mut budget)?;
        budget.finish()?;
        Ok(result)
    }

    #[must_use]
    pub fn intersection(&self, other: &Self) -> Self {
        Self::from_expression(intersection([
            self.expression.clone(),
            other.expression.clone(),
        ]))
    }

    #[must_use]
    pub fn union(&self, other: &Self) -> Self {
        Self::from_expression(alternative([
            self.expression.clone(),
            other.expression.clone(),
        ]))
    }

    #[must_use]
    pub fn complement(&self) -> Self {
        Self::from_expression(complement(self.expression.clone()))
    }

    pub fn is_empty_exact<C: DatatypeControl>(
        &self,
        limits: RegexLimits,
        control: &C,
    ) -> Result<bool, DatatypeError> {
        let automaton = self.cached_automaton(limits, control)?;
        Ok(!productive_dfa_states(automaton)?.contains(&0))
    }

    pub fn finite_cardinality<C: DatatypeControl>(
        &self,
        limits: RegexLimits,
        control: &C,
    ) -> Result<Option<BigUint>, DatatypeError> {
        finite_dfa_cardinality(self.cached_automaton(limits, control)?)
    }

    pub fn cardinality_up_to<C: DatatypeControl>(
        &self,
        maximum: u64,
        limits: RegexLimits,
        control: &C,
    ) -> Result<u64, DatatypeError> {
        if maximum == 0 {
            return Ok(0);
        }
        dfa_cardinality_up_to(self.cached_automaton(limits, control)?, maximum)
    }

    pub fn cardinality_at_least<C: DatatypeControl>(
        &self,
        minimum: u64,
        limits: RegexLimits,
        control: &C,
    ) -> Result<bool, DatatypeError> {
        Ok(self.cardinality_up_to(minimum, limits, control)? == minimum)
    }

    pub fn enumerate_strings<C: DatatypeControl>(
        &self,
        limits: RegexLimits,
        control: &C,
    ) -> Result<Vec<String>, DatatypeError> {
        let limits = limits.validate()?;
        let automaton = self.cached_automaton(limits, control)?;
        let cardinality = finite_dfa_cardinality(automaton)?.ok_or_else(|| {
            DatatypeError::invalid("cannot enumerate an infinite XSD regex language")
        })?;
        let allowed = BigUint::from(limits.max_enumeration_values);
        if cardinality > allowed {
            return Err(DatatypeError::resource(
                "max_enumeration_values",
                cardinality.to_u64().unwrap_or(u64::MAX),
                limits.max_enumeration_values,
            ));
        }
        enumerate_dfa(automaton, &cardinality, limits, control)
    }

    pub fn first_string<C: DatatypeControl>(
        &self,
        excluding: &BTreeSet<String>,
        limits: RegexLimits,
        control: &C,
    ) -> Result<String, DatatypeError> {
        let limits = limits.validate()?;
        if u64::try_from(excluding.len()).unwrap_or(u64::MAX) > limits.max_enumeration_values {
            return Err(DatatypeError::resource(
                "max_enumeration_values",
                u64::try_from(excluding.len()).unwrap_or(u64::MAX),
                limits.max_enumeration_values,
            ));
        }
        let automaton = self.cached_automaton(limits, control)?;
        first_dfa_string(automaton, excluding, limits, control)
    }

    fn cached_automaton<C: DatatypeControl>(
        &self,
        limits: RegexLimits,
        control: &C,
    ) -> Result<&Dfa, DatatypeError> {
        let limits = limits.validate()?;
        control.poll()?;
        if self.automaton.get().is_none() {
            let built = determinize(&self.expression, limits, control)?;
            let _unused = self.automaton.set(built);
        }
        let automaton = self
            .automaton
            .get()
            .ok_or_else(|| DatatypeError::invalid("XSD regex automaton cache is absent"))?;
        automaton.validate_for(limits, control)?;
        Ok(automaton)
    }

    fn lock_match_cache(&self) -> Result<MutexGuard<'_, MatchCache>, DatatypeError> {
        self.matches
            .get_or_init(|| Mutex::new(MatchCache::new(&self.expression)))
            .lock()
            .map_err(|_| DatatypeError::invalid("XSD regex match cache lock is poisoned"))
    }

    fn match_transition<C: DatatypeControl>(
        &self,
        state: usize,
        codepoint: u32,
        budget: &mut Budget<'_, C>,
    ) -> Result<usize, DatatypeError> {
        let (cached, expression) = {
            let cache = self.lock_match_cache()?;
            let cached = cache.transitions.get(&(state, codepoint)).copied();
            let expression =
                cache.states.get(state).cloned().ok_or_else(|| {
                    DatatypeError::invalid("XSD regex lazy match state is absent")
                })?;
            drop(cache);
            (cached, expression)
        };
        if let Some(cached) = cached {
            budget.transition()?;
            budget.cached_derivatives(cached.derivative_work)?;
            return Ok(cached.target);
        }

        budget.transition()?;
        let work_before = budget.derivative_steps;
        let derivative = derive_uncached(&expression, codepoint, budget)?;
        let derivative_work = budget.derivative_steps.saturating_sub(work_before);

        let mut cache = self.lock_match_cache()?;
        if let Some(cached) = cache.transitions.get(&(state, codepoint)) {
            return Ok(cached.target);
        }
        let observed_transitions = u64::try_from(cache.transitions.len())
            .unwrap_or(u64::MAX)
            .saturating_add(1);
        if observed_transitions > budget.limits.max_pattern_transitions {
            return Err(DatatypeError::resource(
                "max_pattern_transitions",
                observed_transitions,
                budget.limits.max_pattern_transitions,
            ));
        }
        let existing_target = cache.state_ids.get(&derivative).copied();
        let target = if let Some(target) = existing_target {
            target
        } else {
            cache.states.len()
        };
        if existing_target.is_none() {
            let observed_states = u64::try_from(target).unwrap_or(u64::MAX).saturating_add(1);
            budget.state(observed_states)?;
            let next_depth = maximum_expression_depth(&derivative);
            let allowed_depth = budget.limits.max_pattern_depth.saturating_mul(2);
            if next_depth > allowed_depth {
                return Err(DatatypeError::resource(
                    "max_pattern_depth",
                    next_depth,
                    allowed_depth,
                ));
            }
            let memory_bytes = MatchCache::memory_bytes_for(
                cache.states.len().saturating_add(1),
                cache.state_ids.len().saturating_add(1),
                cache.transitions.len().saturating_add(1),
                cache.nullability.len(),
            );
            budget.control.observe_memory(memory_bytes)?;
            cache.expression_depth = cache.expression_depth.max(next_depth);
            cache.state_ids.insert(derivative.clone(), target);
            cache.states.push(derivative);
        } else {
            let memory_bytes = MatchCache::memory_bytes_for(
                cache.states.len(),
                cache.state_ids.len(),
                cache.transitions.len().saturating_add(1),
                cache.nullability.len(),
            );
            budget.control.observe_memory(memory_bytes)?;
        }
        cache.transitions.insert(
            (state, codepoint),
            CachedMatchTransition {
                target,
                derivative_work,
            },
        );
        drop(cache);
        Ok(target)
    }

    fn match_nullable<C: DatatypeControl>(
        &self,
        state: usize,
        budget: &mut Budget<'_, C>,
    ) -> Result<bool, DatatypeError> {
        let (cached, expression) = {
            let cache = self.lock_match_cache()?;
            let cached = cache.nullability.get(&state).copied();
            let expression =
                cache.states.get(state).cloned().ok_or_else(|| {
                    DatatypeError::invalid("XSD regex lazy match state is absent")
                })?;
            drop(cache);
            (cached, expression)
        };
        if let Some(cached) = cached {
            budget.cached_derivatives(cached.derivative_work)?;
            return Ok(cached.value);
        }
        let work_before = budget.derivative_steps;
        let value = nullable_uncached(&expression, budget)?;
        let derivative_work = budget.derivative_steps.saturating_sub(work_before);
        let mut cache = self.lock_match_cache()?;
        if let Some(cached) = cache.nullability.get(&state) {
            return Ok(cached.value);
        }
        let memory_bytes = MatchCache::memory_bytes_for(
            cache.states.len(),
            cache.state_ids.len(),
            cache.transitions.len(),
            cache.nullability.len().saturating_add(1),
        );
        budget.control.observe_memory(memory_bytes)?;
        cache.nullability.insert(
            state,
            CachedNullability {
                value,
                derivative_work,
            },
        );
        drop(cache);
        Ok(value)
    }
}

fn xml_characters() -> CharSet {
    CharSet::from_valid(XML_INTERVALS.to_vec())
}

fn xml_space() -> CharSet {
    CharSet::from_valid(vec![(0x9, 0xA), (0xD, 0xD), (0x20, 0x20)])
}

fn is_xml_codepoint(codepoint: u32) -> bool {
    XML_INTERVALS
        .iter()
        .any(|(lower, upper)| *lower <= codepoint && codepoint <= *upper)
}

fn bounded_character_count(value: &str, maximum: u64) -> Result<u64, DatatypeError> {
    let limit = maximum
        .checked_add(1)
        .ok_or_else(|| DatatypeError::invalid("XSD regex character limit overflow"))?;
    let take = usize::try_from(limit).unwrap_or(usize::MAX);
    Ok(u64::try_from(value.chars().take(take).count()).unwrap_or(u64::MAX))
}

struct Budget<'a, C> {
    limits: RegexLimits,
    control: &'a C,
    since_poll: u64,
    derivative_steps: u64,
    transitions: u64,
}

impl<'a, C: DatatypeControl> Budget<'a, C> {
    fn new(limits: RegexLimits, control: &'a C) -> Result<Self, DatatypeError> {
        control.poll()?;
        Ok(Self {
            limits,
            control,
            since_poll: 0,
            derivative_steps: 0,
            transitions: 0,
        })
    }

    fn work(&mut self, amount: u64) -> Result<(), DatatypeError> {
        self.since_poll = self
            .since_poll
            .checked_add(amount)
            .ok_or_else(|| DatatypeError::invalid("XSD regex work counter overflow"))?;
        if self.since_poll >= self.limits.cancellation_poll_stride {
            self.control.poll()?;
            self.since_poll %= self.limits.cancellation_poll_stride;
        }
        Ok(())
    }

    fn derivative(&mut self) -> Result<(), DatatypeError> {
        self.derivative_steps = self
            .derivative_steps
            .checked_add(1)
            .ok_or_else(|| DatatypeError::invalid("XSD regex derivative work counter overflow"))?;
        let allowed = self.limits.max_pattern_transitions;
        if self.derivative_steps > allowed {
            return Err(DatatypeError::resource(
                "max_pattern_transitions",
                self.derivative_steps,
                allowed,
            ));
        }
        self.work(1)
    }

    fn cached_derivatives(&mut self, amount: u64) -> Result<(), DatatypeError> {
        self.derivative_steps = self
            .derivative_steps
            .checked_add(amount)
            .ok_or_else(|| DatatypeError::invalid("XSD regex derivative work counter overflow"))?;
        if self.derivative_steps > self.limits.max_pattern_transitions {
            return Err(DatatypeError::resource(
                "max_pattern_transitions",
                self.derivative_steps,
                self.limits.max_pattern_transitions,
            ));
        }
        self.work(amount)
    }

    fn transition(&mut self) -> Result<(), DatatypeError> {
        self.transitions = self
            .transitions
            .checked_add(1)
            .ok_or_else(|| DatatypeError::invalid("XSD regex transition counter overflow"))?;
        if self.transitions > self.limits.max_pattern_transitions {
            return Err(DatatypeError::resource(
                "max_pattern_transitions",
                self.transitions,
                self.limits.max_pattern_transitions,
            ));
        }
        self.work(1)
    }

    fn cached_transitions(&mut self, amount: u64) -> Result<(), DatatypeError> {
        self.transitions = self
            .transitions
            .checked_add(amount)
            .ok_or_else(|| DatatypeError::invalid("XSD regex transition counter overflow"))?;
        if self.transitions > self.limits.max_pattern_transitions {
            return Err(DatatypeError::resource(
                "max_pattern_transitions",
                self.transitions,
                self.limits.max_pattern_transitions,
            ));
        }
        self.work(amount)
    }

    fn state(&mut self, observed: u64) -> Result<(), DatatypeError> {
        if observed > self.limits.max_pattern_states {
            return Err(DatatypeError::resource(
                "max_pattern_states",
                observed,
                self.limits.max_pattern_states,
            ));
        }
        self.work(1)
    }

    fn observe_automaton(
        &self,
        states: usize,
        pending: usize,
        cached: usize,
    ) -> Result<(), DatatypeError> {
        let items = states.saturating_add(pending).saturating_add(cached);
        let bytes = u64::try_from(items)
            .unwrap_or(u64::MAX)
            .saturating_mul(u64::try_from(std::mem::size_of::<Expr>()).unwrap_or(u64::MAX));
        self.control.observe_memory(bytes)
    }

    fn finish(&self) -> Result<(), DatatypeError> {
        self.control.poll()
    }
}

#[derive(Default)]
struct DerivativeEngine {
    derivatives: BTreeMap<(Expr, u32), Expr>,
    nullability: BTreeMap<Expr, bool>,
}

impl DerivativeEngine {
    fn cache_len(&self) -> usize {
        self.derivatives
            .len()
            .saturating_add(self.nullability.len())
    }

    fn nullable<C: DatatypeControl>(
        &mut self,
        expression: &Expr,
        budget: &mut Budget<'_, C>,
    ) -> Result<bool, DatatypeError> {
        if let Some(value) = self.nullability.get(expression) {
            return Ok(*value);
        }
        budget.derivative()?;
        let result = match expression {
            Expr::Empty | Expr::Characters(_) => false,
            Expr::Epsilon | Expr::Star(_) => true,
            Expr::Alternative(parts) => {
                let mut nullable = false;
                for part in parts {
                    if self.nullable(part, budget)? {
                        nullable = true;
                        break;
                    }
                }
                nullable
            }
            Expr::Sequence(parts) => {
                let mut nullable = true;
                for part in parts {
                    if !self.nullable(part, budget)? {
                        nullable = false;
                        break;
                    }
                }
                nullable
            }
            Expr::Intersection(parts) => {
                let mut nullable = true;
                for part in parts {
                    if !self.nullable(part, budget)? {
                        nullable = false;
                        break;
                    }
                }
                nullable
            }
            Expr::Complement(part) => !self.nullable(part, budget)?,
        };
        self.nullability.insert(expression.clone(), result);
        Ok(result)
    }

    fn derive<C: DatatypeControl>(
        &mut self,
        expression: &Expr,
        codepoint: u32,
        budget: &mut Budget<'_, C>,
    ) -> Result<Expr, DatatypeError> {
        let key = (expression.clone(), codepoint);
        if let Some(value) = self.derivatives.get(&key) {
            return Ok(value.clone());
        }
        budget.derivative()?;
        let result = match expression {
            Expr::Empty | Expr::Epsilon => Expr::Empty,
            Expr::Characters(characters) => {
                if characters.contains(codepoint) {
                    Expr::Epsilon
                } else {
                    Expr::Empty
                }
            }
            Expr::Alternative(parts) => {
                let mut derivatives = Vec::with_capacity(parts.len());
                for part in parts {
                    derivatives.push(self.derive(part, codepoint, budget)?);
                }
                alternative(derivatives)
            }
            Expr::Sequence(parts) => {
                let mut alternatives = Vec::new();
                for (index, part) in parts.iter().enumerate() {
                    let mut sequence_parts = Vec::with_capacity(parts.len() - index);
                    sequence_parts.push(self.derive(part, codepoint, budget)?);
                    sequence_parts.extend_from_slice(&parts[index + 1..]);
                    alternatives.push(sequence(sequence_parts));
                    if !self.nullable(part, budget)? {
                        break;
                    }
                }
                alternative(alternatives)
            }
            Expr::Star(part) => {
                sequence([self.derive(part, codepoint, budget)?, expression.clone()])
            }
            Expr::Intersection(parts) => {
                let mut derivatives = Vec::with_capacity(parts.len());
                for part in parts {
                    derivatives.push(self.derive(part, codepoint, budget)?);
                }
                intersection(derivatives)
            }
            Expr::Complement(part) => complement(self.derive(part, codepoint, budget)?),
        };
        self.derivatives.insert(key, result.clone());
        Ok(result)
    }
}

// A membership query normally visits only the derivatives selected by its input.
// Avoiding whole-expression map keys here is important for large Unicode character
// classes: cloning a quantified expression merely to probe a memo table costs much
// more than evaluating the selected derivative. Full DFA construction still uses
// `DerivativeEngine`, where cross-state memoization pays for itself.
fn nullable_uncached<C: DatatypeControl>(
    expression: &Expr,
    budget: &mut Budget<'_, C>,
) -> Result<bool, DatatypeError> {
    budget.derivative()?;
    match expression {
        Expr::Empty | Expr::Characters(_) => Ok(false),
        Expr::Epsilon | Expr::Star(_) => Ok(true),
        Expr::Alternative(parts) => {
            for part in parts {
                if nullable_uncached(part, budget)? {
                    return Ok(true);
                }
            }
            Ok(false)
        }
        Expr::Sequence(parts) => {
            for part in parts {
                if !nullable_uncached(part, budget)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        Expr::Intersection(parts) => {
            for part in parts {
                if !nullable_uncached(part, budget)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        Expr::Complement(part) => Ok(!nullable_uncached(part, budget)?),
    }
}

fn derive_uncached<C: DatatypeControl>(
    expression: &Expr,
    codepoint: u32,
    budget: &mut Budget<'_, C>,
) -> Result<Expr, DatatypeError> {
    budget.derivative()?;
    match expression {
        Expr::Empty | Expr::Epsilon => Ok(Expr::Empty),
        Expr::Characters(characters) => Ok(if characters.contains(codepoint) {
            Expr::Epsilon
        } else {
            Expr::Empty
        }),
        Expr::Alternative(parts) => {
            let mut derivatives = Vec::with_capacity(parts.len());
            for part in parts {
                derivatives.push(derive_uncached(part, codepoint, budget)?);
            }
            Ok(alternative(derivatives))
        }
        Expr::Sequence(parts) => {
            let mut alternatives = Vec::new();
            for (index, part) in parts.iter().enumerate() {
                let mut sequence_parts = Vec::with_capacity(parts.len() - index);
                sequence_parts.push(derive_uncached(part, codepoint, budget)?);
                sequence_parts.extend_from_slice(&parts[index + 1..]);
                alternatives.push(sequence(sequence_parts));
                if !nullable_uncached(part, budget)? {
                    break;
                }
            }
            Ok(alternative(alternatives))
        }
        Expr::Star(part) => Ok(sequence([
            derive_uncached(part, codepoint, budget)?,
            expression.clone(),
        ])),
        Expr::Intersection(parts) => {
            let mut derivatives = Vec::with_capacity(parts.len());
            for part in parts {
                derivatives.push(derive_uncached(part, codepoint, budget)?);
            }
            Ok(intersection(derivatives))
        }
        Expr::Complement(part) => Ok(complement(derive_uncached(part, codepoint, budget)?)),
    }
}

fn alternative(expressions: impl IntoIterator<Item = Expr>) -> Expr {
    let mut parts = BTreeSet::new();
    for expression in expressions {
        match expression {
            Expr::Empty => {}
            Expr::Alternative(nested) => parts.extend(nested),
            other => {
                parts.insert(other);
            }
        }
    }
    if parts.is_empty() {
        Expr::Empty
    } else if parts.len() == 1 {
        parts.into_iter().next().unwrap_or(Expr::Empty)
    } else {
        Expr::Alternative(parts)
    }
}

fn sequence(expressions: impl IntoIterator<Item = Expr>) -> Expr {
    let mut parts = Vec::new();
    for expression in expressions {
        match expression {
            Expr::Empty => return Expr::Empty,
            Expr::Epsilon => {}
            Expr::Sequence(nested) => parts.extend(nested),
            other => parts.push(other),
        }
    }
    if parts.is_empty() {
        Expr::Epsilon
    } else if parts.len() == 1 {
        parts.pop().unwrap_or(Expr::Epsilon)
    } else {
        Expr::Sequence(parts)
    }
}

fn star(expression: Expr) -> Expr {
    match expression {
        Expr::Empty | Expr::Epsilon => Expr::Epsilon,
        Expr::Star(_) => expression,
        other => Expr::Star(Box::new(other)),
    }
}

fn repeat_range(expression: Expr, minimum: usize, maximum: Option<usize>) -> Expr {
    let mut required = vec![expression.clone(); minimum];
    match maximum {
        None => required.push(star(expression)),
        Some(maximum) => {
            let mut optional_tail = Expr::Epsilon;
            for _ in minimum..maximum {
                optional_tail =
                    alternative([Expr::Epsilon, sequence([expression.clone(), optional_tail])]);
            }
            required.push(optional_tail);
        }
    }
    sequence(required)
}

fn intersection(expressions: impl IntoIterator<Item = Expr>) -> Expr {
    let mut parts = BTreeSet::new();
    for expression in expressions {
        match expression {
            Expr::Empty => return Expr::Empty,
            Expr::Intersection(nested) => parts.extend(nested),
            other => {
                parts.insert(other);
            }
        }
    }
    if parts.is_empty() {
        return complement(Expr::Empty);
    }
    if parts.len() == 1 {
        return parts.into_iter().next().unwrap_or(Expr::Empty);
    }
    if parts
        .iter()
        .any(|part| parts.contains(&complement(part.clone())))
    {
        Expr::Empty
    } else {
        Expr::Intersection(parts)
    }
}

fn complement(expression: Expr) -> Expr {
    match expression {
        Expr::Complement(part) => *part,
        other => Expr::Complement(Box::new(other)),
    }
}

struct Parser<'a, C> {
    pattern: Vec<char>,
    position: usize,
    limits: RegexLimits,
    control: &'a C,
    nodes: u64,
    since_poll: u64,
}

impl<'a, C: DatatypeControl> Parser<'a, C> {
    fn new(pattern: &str, limits: RegexLimits, control: &'a C) -> Result<Self, DatatypeError> {
        let characters: Vec<char> = pattern.chars().collect();
        control.observe_memory(
            u64::try_from(characters.len())
                .unwrap_or(u64::MAX)
                .saturating_mul(u64::try_from(std::mem::size_of::<char>()).unwrap_or(u64::MAX)),
        )?;
        Ok(Self {
            pattern: characters,
            position: 0,
            limits,
            control,
            nodes: 0,
            since_poll: 0,
        })
    }

    fn parse(&mut self) -> Result<Expr, DatatypeError> {
        let result = self.regular_expression(0)?;
        if self.position != self.pattern.len() {
            return Err(self.syntax("unexpected trailing pattern input"));
        }
        self.control.poll()?;
        Ok(result)
    }

    fn regular_expression(&mut self, depth: u64) -> Result<Expr, DatatypeError> {
        self.depth(depth)?;
        let mut branches = vec![self.branch(depth)?];
        while self.peek(0) == Some('|') {
            self.position += 1;
            branches.push(self.branch(depth)?);
        }
        Ok(alternative(branches))
    }

    fn branch(&mut self, depth: u64) -> Result<Expr, DatatypeError> {
        let mut parts = Vec::new();
        while self
            .peek(0)
            .is_some_and(|value| value != '|' && value != ')')
        {
            parts.push(self.piece(depth)?);
        }
        Ok(sequence(parts))
    }

    fn piece(&mut self, depth: u64) -> Result<Expr, DatatypeError> {
        let atom = self.atom(depth)?;
        match self.peek(0) {
            Some('?') => {
                self.position += 1;
                Ok(alternative([Expr::Epsilon, atom]))
            }
            Some('*') => {
                self.position += 1;
                Ok(star(atom))
            }
            Some('+') => {
                self.position += 1;
                Ok(sequence([atom.clone(), star(atom)]))
            }
            Some('{') => self.quantified(atom),
            _ => Ok(atom),
        }
    }

    fn atom(&mut self, depth: u64) -> Result<Expr, DatatypeError> {
        let selected = self
            .peek(0)
            .ok_or_else(|| self.syntax("expected a regular-expression atom"))?;
        self.node()?;
        match selected {
            '(' => {
                self.position += 1;
                let nested_depth = depth
                    .checked_add(1)
                    .ok_or_else(|| DatatypeError::invalid("XSD regex nesting depth overflow"))?;
                self.depth(nested_depth)?;
                let expression = self.regular_expression(nested_depth)?;
                if self.peek(0) != Some(')') {
                    return Err(self.syntax("unclosed regular-expression group"));
                }
                self.position += 1;
                Ok(expression)
            }
            '[' => Ok(Expr::Characters(self.character_class()?)),
            '.' => {
                self.position += 1;
                Ok(Expr::Characters(xml_characters()))
            }
            '\\' => Ok(Expr::Characters(self.escape()?)),
            '?' | '*' | '+' | '{' | '}' | ')' | ']' => {
                Err(self.syntax("metacharacter must be escaped"))
            }
            literal => {
                self.position += 1;
                Ok(Expr::Characters(CharSet::one(u32::from(literal))?))
            }
        }
    }

    fn quantified(&mut self, atom: Expr) -> Result<Expr, DatatypeError> {
        self.position += 1;
        let minimum = self.quantity()?;
        let maximum = if self.peek(0) == Some(',') {
            self.position += 1;
            if self.peek(0) == Some('}') {
                None
            } else {
                Some(self.quantity()?)
            }
        } else {
            Some(minimum)
        };
        if self.peek(0) != Some('}') {
            return Err(self.syntax("unclosed quantifier"));
        }
        self.position += 1;
        if maximum.is_some_and(|value| minimum > value) {
            return Err(self.syntax("quantifier minimum exceeds maximum"));
        }
        let expansion = maximum.unwrap_or(minimum);
        if expansion > self.limits.max_pattern_states {
            return Err(DatatypeError::resource(
                "max_pattern_states",
                expansion,
                self.limits.max_pattern_states,
            ));
        }
        let minimum_usize = usize::try_from(minimum).map_err(|_| {
            DatatypeError::resource(
                "max_pattern_states",
                minimum,
                self.limits.max_pattern_states,
            )
        })?;
        let expansion_usize = usize::try_from(expansion).map_err(|_| {
            DatatypeError::resource(
                "max_pattern_states",
                expansion,
                self.limits.max_pattern_states,
            )
        })?;
        self.control.observe_memory(
            u64::try_from(expansion_usize)
                .unwrap_or(u64::MAX)
                .saturating_mul(u64::try_from(std::mem::size_of::<Expr>()).unwrap_or(u64::MAX)),
        )?;
        Ok(repeat_range(
            atom,
            minimum_usize,
            maximum.map(|_| expansion_usize),
        ))
    }

    fn quantity(&mut self) -> Result<u64, DatatypeError> {
        let mut found = false;
        let mut value = 0_u64;
        while let Some(selected) = self.peek(0) {
            let Some(digit) = selected.to_digit(10) else {
                break;
            };
            if !selected.is_ascii_digit() {
                break;
            }
            found = true;
            self.position += 1;
            value = value
                .checked_mul(10)
                .and_then(|current| current.checked_add(u64::from(digit)))
                .ok_or_else(|| {
                    DatatypeError::resource(
                        "max_pattern_states",
                        self.limits.max_pattern_states.saturating_add(1),
                        self.limits.max_pattern_states,
                    )
                })?;
            if value > self.limits.max_pattern_states {
                return Err(DatatypeError::resource(
                    "max_pattern_states",
                    self.limits.max_pattern_states.saturating_add(1),
                    self.limits.max_pattern_states,
                ));
            }
        }
        if !found {
            return Err(self.syntax("quantifier requires a decimal integer"));
        }
        Ok(value)
    }

    fn character_class(&mut self) -> Result<CharSet, DatatypeError> {
        self.position += 1;
        let negative = self.peek(0) == Some('^');
        if negative {
            self.position += 1;
        }
        let mut result = CharSet::from_valid(Vec::new());
        let mut found = false;
        loop {
            let selected = self
                .peek(0)
                .ok_or_else(|| self.syntax("unclosed character class"))?;
            if selected == ']' {
                if !found {
                    return Err(self.syntax("empty character class"));
                }
                self.position += 1;
                break;
            }
            if selected == '-' && self.peek(1) == Some('[') {
                if !found {
                    return Err(self.syntax("character-class subtraction requires a left operand"));
                }
                self.position += 1;
                result = result.difference(&self.character_class()?);
                if self.peek(0) != Some(']') {
                    return Err(self.syntax("character-class subtraction must be final"));
                }
                self.position += 1;
                break;
            }
            let mut first = self.class_atom()?;
            found = true;
            if self.peek(0) == Some('-') && !matches!(self.peek(1), None | Some(']' | '[')) {
                self.position += 1;
                let second = self.class_atom()?;
                let lower = singleton(&first).ok_or_else(|| {
                    self.syntax("character range start must denote one character")
                })?;
                let upper = singleton(&second)
                    .ok_or_else(|| self.syntax("character range end must denote one character"))?;
                if lower > upper {
                    return Err(self.syntax("character range is reversed"));
                }
                first = CharSet::from_valid(vec![(lower, upper)]).intersection(&xml_characters());
            }
            result = result.union(&first);
        }
        Ok(if negative {
            result.complement()
        } else {
            result
        })
    }

    fn class_atom(&mut self) -> Result<CharSet, DatatypeError> {
        let selected = self
            .peek(0)
            .ok_or_else(|| self.syntax("expected character-class item"))?;
        if selected == ']' {
            return Err(self.syntax("expected character-class item"));
        }
        if selected == '\\' {
            return self.escape();
        }
        if selected == '[' {
            return Err(self.syntax("unescaped bracket in character class"));
        }
        self.position += 1;
        Ok(CharSet::one(u32::from(selected))?.intersection(&xml_characters()))
    }

    fn escape(&mut self) -> Result<CharSet, DatatypeError> {
        self.position += 1;
        let selected = self.peek(0).ok_or_else(|| self.syntax("trailing escape"))?;
        self.position += 1;
        let single = match selected {
            'n' => Some('\n'),
            'r' => Some('\r'),
            't' => Some('\t'),
            '\\' | '|' | '.' | '-' | '^' | '?' | '*' | '+' | '{' | '}' | '(' | ')' | '[' | ']' => {
                Some(selected)
            }
            _ => None,
        };
        if let Some(value) = single {
            return Ok(CharSet::one(u32::from(value))?.intersection(&xml_characters()));
        }
        match selected {
            's' => Ok(xml_space()),
            'S' => Ok(xml_space().complement()),
            'p' | 'P' => {
                if self.peek(0) != Some('{') {
                    return Err(self.syntax("Unicode category escape requires braces"));
                }
                self.position += 1;
                let start = self.position;
                while !matches!(self.peek(0), None | Some('}')) {
                    self.position += 1;
                }
                if self.peek(0) != Some('}') {
                    return Err(self.syntax("unclosed Unicode category escape"));
                }
                let property: String = self.pattern[start..self.position].iter().collect();
                self.position += 1;
                let category = category_set(&property, self.limits, self.control)?;
                Ok(if selected == 'P' {
                    category.complement()
                } else {
                    category
                })
            }
            'd' | 'D' => {
                let digits = category_set("Nd", self.limits, self.control)?;
                Ok(if selected == 'D' {
                    digits.complement()
                } else {
                    digits
                })
            }
            'w' | 'W' => {
                let excluded = category_set("P", self.limits, self.control)?
                    .union(&category_set("Z", self.limits, self.control)?)
                    .union(&category_set("C", self.limits, self.control)?);
                let word = excluded.complement();
                Ok(if selected == 'W' {
                    word.complement()
                } else {
                    word
                })
            }
            'i' | 'I' | 'c' | 'C' => {
                let characters = xml_name_characters(selected.eq_ignore_ascii_case(&'i'));
                Ok(if selected.is_ascii_uppercase() {
                    characters.complement()
                } else {
                    characters
                })
            }
            _ => Err(self.syntax("unknown XML Schema character escape")),
        }
    }

    fn node(&mut self) -> Result<(), DatatypeError> {
        self.nodes = self
            .nodes
            .checked_add(1)
            .ok_or_else(|| DatatypeError::invalid("XSD regex syntax node counter overflow"))?;
        if self.nodes > self.limits.max_pattern_states {
            return Err(DatatypeError::resource(
                "max_pattern_states",
                self.nodes,
                self.limits.max_pattern_states,
            ));
        }
        self.poll_work(1)
    }

    fn depth(&mut self, depth: u64) -> Result<(), DatatypeError> {
        if depth > self.limits.max_pattern_depth {
            return Err(DatatypeError::resource(
                "max_pattern_depth",
                depth,
                self.limits.max_pattern_depth,
            ));
        }
        self.poll_work(1)
    }

    fn poll_work(&mut self, amount: u64) -> Result<(), DatatypeError> {
        self.since_poll = self
            .since_poll
            .checked_add(amount)
            .ok_or_else(|| DatatypeError::invalid("XSD regex parser work counter overflow"))?;
        if self.since_poll >= self.limits.cancellation_poll_stride {
            self.control.poll()?;
            self.since_poll %= self.limits.cancellation_poll_stride;
        }
        Ok(())
    }

    fn peek(&self, offset: usize) -> Option<char> {
        self.position
            .checked_add(offset)
            .and_then(|position| self.pattern.get(position).copied())
    }

    fn syntax(&self, message: &str) -> DatatypeError {
        DatatypeError::invalid(format!(
            "invalid XML Schema regular expression at character {}: {message}",
            self.position
        ))
    }
}

fn singleton(characters: &CharSet) -> Option<u32> {
    match characters.intervals.as_slice() {
        [(lower, upper)] if lower == upper => Some(*lower),
        _ => None,
    }
}

fn category_set<C: DatatypeControl>(
    property: &str,
    limits: RegexLimits,
    control: &C,
) -> Result<CharSet, DatatypeError> {
    if property.starts_with("Is") {
        return Err(DatatypeError::invalid(
            "XML Schema Unicode block escapes are not supported by the pinned inventory",
        ));
    }
    let exact = CATEGORY_CODE_NAMES
        .iter()
        .position(|name| *name == property);
    let major = if property.len() == 1 {
        property.as_bytes().first().copied()
    } else {
        None
    };
    if exact.is_none() && !matches!(major, Some(b'L' | b'M' | b'N' | b'P' | b'Z' | b'S' | b'C')) {
        return Err(DatatypeError::invalid(
            "unknown XML Schema Unicode category",
        ));
    }
    let mut intervals = Vec::new();
    let mut work = 0_u64;
    for packed in CATEGORY_RANGES_PACKED {
        let category = usize::try_from(packed & 0x1F)
            .map_err(|_| DatatypeError::invalid("invalid generated Unicode category code"))?;
        let name = CATEGORY_CODE_NAMES
            .get(category)
            .ok_or_else(|| DatatypeError::invalid("invalid generated Unicode category code"))?;
        let selected = exact == Some(category)
            || major.is_some_and(|value| name.as_bytes().first().copied() == Some(value));
        if selected {
            let lower = u32::try_from(packed >> 26)
                .map_err(|_| DatatypeError::invalid("invalid generated Unicode range"))?;
            let upper = u32::try_from((packed >> 5) & 0x1F_FFFF)
                .map_err(|_| DatatypeError::invalid("invalid generated Unicode range"))?;
            intervals.push((lower, upper));
        }
        work += 1;
        if work == limits.cancellation_poll_stride.saturating_mul(64) {
            control.poll()?;
            work = 0;
        }
    }
    control.poll()?;
    CharSet::normalize(intervals)
}

fn xml_name_characters(start: bool) -> CharSet {
    let initial = CharSet::from_valid(vec![
        (0x3A, 0x3A),
        (0x41, 0x5A),
        (0x5F, 0x5F),
        (0x61, 0x7A),
        (0xC0, 0xD6),
        (0xD8, 0xF6),
        (0xF8, 0x2FF),
        (0x370, 0x37D),
        (0x37F, 0x1FFF),
        (0x200C, 0x200D),
        (0x2070, 0x218F),
        (0x2C00, 0x2FEF),
        (0x3001, 0xD7FF),
        (0xF900, 0xFDCF),
        (0xFDF0, 0xFFFD),
        (0x10000, 0xEFFFF),
    ])
    .intersection(&xml_characters());
    if start {
        initial
    } else {
        initial.union(&CharSet::from_valid(vec![
            (0x2D, 0x2E),
            (0x30, 0x39),
            (0xB7, 0xB7),
            (0x300, 0x36F),
            (0x203F, 0x2040),
        ]))
    }
}

fn representative_classes(
    expression: &Expr,
    maximum_depth: u64,
) -> Result<Vec<(u32, CharSet)>, DatatypeError> {
    let mut boundaries = BTreeSet::new();
    for (lower, upper) in XML_INTERVALS {
        boundaries.insert(lower);
        boundaries.insert(upper.saturating_add(1));
    }
    collect_boundaries(expression, &mut boundaries, 0, maximum_depth)?;
    let ordered: Vec<u32> = boundaries.into_iter().collect();
    let mut representatives = Vec::new();
    for pair in ordered.windows(2) {
        let [candidate, next] = pair else {
            continue;
        };
        if candidate < next && is_xml_codepoint(*candidate) {
            representatives.push((
                *candidate,
                CharSet::from_valid(vec![(*candidate, next.saturating_sub(1))])
                    .intersection(&xml_characters()),
            ));
        }
    }
    Ok(representatives)
}

fn collect_boundaries(
    expression: &Expr,
    output: &mut BTreeSet<u32>,
    depth: u64,
    maximum_depth: u64,
) -> Result<(), DatatypeError> {
    if depth > maximum_depth {
        return Err(DatatypeError::resource(
            "max_pattern_depth",
            depth,
            maximum_depth,
        ));
    }
    match expression {
        Expr::Characters(characters) => {
            for (lower, upper) in &characters.intervals {
                output.insert(*lower);
                output.insert(upper.saturating_add(1));
            }
        }
        Expr::Alternative(parts) | Expr::Intersection(parts) => {
            for part in parts {
                collect_boundaries(part, output, depth.saturating_add(1), maximum_depth)?;
            }
        }
        Expr::Sequence(parts) => {
            for part in parts {
                collect_boundaries(part, output, depth.saturating_add(1), maximum_depth)?;
            }
        }
        Expr::Star(part) | Expr::Complement(part) => {
            collect_boundaries(part, output, depth.saturating_add(1), maximum_depth)?;
        }
        Expr::Empty | Expr::Epsilon => {}
    }
    Ok(())
}

fn maximum_expression_depth(expression: &Expr) -> u64 {
    match expression {
        Expr::Alternative(parts) | Expr::Intersection(parts) => parts
            .iter()
            .map(maximum_expression_depth)
            .max()
            .unwrap_or(0)
            .saturating_add(1),
        Expr::Sequence(parts) => parts
            .iter()
            .map(maximum_expression_depth)
            .max()
            .unwrap_or(0)
            .saturating_add(1),
        Expr::Star(part) | Expr::Complement(part) => {
            maximum_expression_depth(part).saturating_add(1)
        }
        Expr::Empty | Expr::Epsilon | Expr::Characters(_) => 0,
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct DfaTransition {
    target: usize,
    characters: CharSet,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Dfa {
    transitions: Vec<Vec<DfaTransition>>,
    accepting: BTreeSet<usize>,
    transition_work: u64,
    expression_depth: u64,
    memory_bytes: u64,
}

impl Dfa {
    fn validate_for<C: DatatypeControl>(
        &self,
        limits: RegexLimits,
        control: &C,
    ) -> Result<(), DatatypeError> {
        let states = u64::try_from(self.transitions.len()).unwrap_or(u64::MAX);
        if states > limits.max_pattern_states {
            return Err(DatatypeError::resource(
                "max_pattern_states",
                states,
                limits.max_pattern_states,
            ));
        }
        if self.transition_work > limits.max_pattern_transitions {
            return Err(DatatypeError::resource(
                "max_pattern_transitions",
                self.transition_work,
                limits.max_pattern_transitions,
            ));
        }
        let allowed_depth = limits.max_pattern_depth.saturating_mul(2);
        if self.expression_depth > allowed_depth {
            return Err(DatatypeError::resource(
                "max_pattern_depth",
                self.expression_depth,
                allowed_depth,
            ));
        }
        control.observe_memory(self.memory_bytes)?;
        control.poll()
    }
}

fn determinize<C: DatatypeControl>(
    expression: &Expr,
    limits: RegexLimits,
    control: &C,
) -> Result<Dfa, DatatypeError> {
    let limits = limits.validate()?;
    let mut budget = Budget::new(limits, control)?;
    let mut engine = DerivativeEngine::default();
    let mut states = vec![expression.clone()];
    let mut state_ids = BTreeMap::from([(expression.clone(), 0_usize)]);
    let mut rows = Vec::new();
    let mut accepting = BTreeSet::new();
    let mut cursor = 0_usize;
    while cursor < states.len() {
        let state = states
            .get(cursor)
            .cloned()
            .ok_or_else(|| DatatypeError::invalid("invalid XSD regex DFA state cursor"))?;
        if engine.nullable(&state, &mut budget)? {
            accepting.insert(cursor);
        }
        let mut grouped: BTreeMap<usize, CharSet> = BTreeMap::new();
        for (representative, characters) in
            representative_classes(&state, limits.max_pattern_depth.saturating_mul(2))?
        {
            budget.transition()?;
            let derivative = engine.derive(&state, representative, &mut budget)?;
            if derivative == Expr::Empty {
                continue;
            }
            let target = if let Some(target) = state_ids.get(&derivative) {
                *target
            } else {
                let target = states.len();
                let observed = u64::try_from(target).unwrap_or(u64::MAX).saturating_add(1);
                budget.state(observed)?;
                state_ids.insert(derivative.clone(), target);
                states.push(derivative);
                target
            };
            grouped
                .entry(target)
                .and_modify(|prior| *prior = prior.union(&characters))
                .or_insert(characters);
        }
        rows.push(
            grouped
                .into_iter()
                .map(|(target, characters)| DfaTransition { target, characters })
                .collect(),
        );
        cursor += 1;
        budget.observe_automaton(states.len(), 0, engine.cache_len())?;
    }
    let transition_work = budget.transitions.max(budget.derivative_steps);
    budget.finish()?;
    let memory_bytes = estimate_dfa_bytes(&rows, &accepting);
    Ok(Dfa {
        transitions: rows,
        accepting,
        transition_work,
        expression_depth: maximum_expression_depth(expression),
        memory_bytes,
    })
}

fn estimate_dfa_bytes(transitions: &[Vec<DfaTransition>], accepting: &BTreeSet<usize>) -> u64 {
    let rows = u64::try_from(transitions.len())
        .unwrap_or(u64::MAX)
        .saturating_mul(
            u64::try_from(std::mem::size_of::<Vec<DfaTransition>>()).unwrap_or(u64::MAX),
        );
    let transition_bytes = transitions
        .iter()
        .flat_map(|row| row.iter())
        .map(|transition| {
            u64::try_from(std::mem::size_of::<DfaTransition>())
                .unwrap_or(u64::MAX)
                .saturating_add(
                    u64::try_from(transition.characters.intervals.len())
                        .unwrap_or(u64::MAX)
                        .saturating_mul(
                            u64::try_from(std::mem::size_of::<(u32, u32)>()).unwrap_or(u64::MAX),
                        ),
                )
        })
        .fold(0_u64, u64::saturating_add);
    let accepting_bytes = u64::try_from(accepting.len())
        .unwrap_or(u64::MAX)
        .saturating_mul(u64::try_from(std::mem::size_of::<usize>()).unwrap_or(u64::MAX));
    rows.saturating_add(transition_bytes)
        .saturating_add(accepting_bytes)
}

fn productive_dfa_states(automaton: &Dfa) -> Result<BTreeSet<usize>, DatatypeError> {
    let mut reverse = vec![BTreeSet::new(); automaton.transitions.len()];
    for (source, row) in automaton.transitions.iter().enumerate() {
        for transition in row {
            let predecessors = reverse.get_mut(transition.target).ok_or_else(|| {
                DatatypeError::invalid("XSD regex DFA transition target is absent")
            })?;
            predecessors.insert(source);
        }
    }
    let mut productive = automaton.accepting.clone();
    let mut pending: VecDeque<usize> = automaton.accepting.iter().copied().collect();
    while let Some(target) = pending.pop_front() {
        let predecessors = reverse
            .get(target)
            .ok_or_else(|| DatatypeError::invalid("XSD regex DFA accepting state is absent"))?;
        for source in predecessors {
            if productive.insert(*source) {
                pending.push_back(*source);
            }
        }
    }
    Ok(productive)
}

fn productive_topological_order(
    automaton: &Dfa,
    productive: &BTreeSet<usize>,
) -> Result<Option<Vec<usize>>, DatatypeError> {
    let mut indegree: BTreeMap<usize, usize> = productive.iter().map(|state| (*state, 0)).collect();
    for source in productive {
        let row = automaton
            .transitions
            .get(*source)
            .ok_or_else(|| DatatypeError::invalid("XSD regex productive DFA state is absent"))?;
        for transition in row {
            if productive.contains(&transition.target) {
                let degree = indegree.get_mut(&transition.target).ok_or_else(|| {
                    DatatypeError::invalid("XSD regex productive transition target is absent")
                })?;
                *degree = degree
                    .checked_add(1)
                    .ok_or_else(|| DatatypeError::invalid("XSD regex DFA indegree overflow"))?;
            }
        }
    }
    let mut ready: BTreeSet<usize> = indegree
        .iter()
        .filter_map(|(state, degree)| (*degree == 0).then_some(*state))
        .collect();
    let mut order = Vec::with_capacity(productive.len());
    while let Some(source) = ready.pop_first() {
        order.push(source);
        let row = automaton
            .transitions
            .get(source)
            .ok_or_else(|| DatatypeError::invalid("XSD regex topological DFA state is absent"))?;
        for transition in row {
            if !productive.contains(&transition.target) {
                continue;
            }
            let degree = indegree.get_mut(&transition.target).ok_or_else(|| {
                DatatypeError::invalid("XSD regex topological transition target is absent")
            })?;
            *degree = degree
                .checked_sub(1)
                .ok_or_else(|| DatatypeError::invalid("XSD regex DFA indegree underflow"))?;
            if *degree == 0 {
                ready.insert(transition.target);
            }
        }
    }
    Ok((order.len() == productive.len()).then_some(order))
}

fn finite_dfa_cardinality(automaton: &Dfa) -> Result<Option<BigUint>, DatatypeError> {
    let productive = productive_dfa_states(automaton)?;
    if !productive.contains(&0) {
        return Ok(Some(BigUint::zero()));
    }
    let Some(order) = productive_topological_order(automaton, &productive)? else {
        return Ok(None);
    };
    let mut counts: BTreeMap<usize, BigUint> = BTreeMap::new();
    for source in order.into_iter().rev() {
        let mut count = if automaton.accepting.contains(&source) {
            BigUint::one()
        } else {
            BigUint::zero()
        };
        let row = automaton
            .transitions
            .get(source)
            .ok_or_else(|| DatatypeError::invalid("XSD regex cardinality DFA state is absent"))?;
        for transition in row {
            if !productive.contains(&transition.target) {
                continue;
            }
            let target = counts.get(&transition.target).ok_or_else(|| {
                DatatypeError::invalid("XSD regex cardinality target is not ordered")
            })?;
            count += BigUint::from(transition.characters.cardinality()) * target;
        }
        counts.insert(source, count);
    }
    counts
        .remove(&0)
        .map(Some)
        .ok_or_else(|| DatatypeError::invalid("XSD regex initial cardinality is absent"))
}

fn dfa_cardinality_up_to(automaton: &Dfa, maximum: u64) -> Result<u64, DatatypeError> {
    let productive = productive_dfa_states(automaton)?;
    if !productive.contains(&0) {
        return Ok(0);
    }
    let Some(order) = productive_topological_order(automaton, &productive)? else {
        return Ok(maximum);
    };
    let mut counts = BTreeMap::new();
    for source in order.into_iter().rev() {
        let mut count = u64::from(automaton.accepting.contains(&source));
        let row = automaton.transitions.get(source).ok_or_else(|| {
            DatatypeError::invalid("XSD regex saturated cardinality state is absent")
        })?;
        for transition in row {
            if !productive.contains(&transition.target) {
                continue;
            }
            let target = counts.get(&transition.target).copied().ok_or_else(|| {
                DatatypeError::invalid("XSD regex saturated cardinality target is not ordered")
            })?;
            count =
                count.saturating_add(transition.characters.cardinality().saturating_mul(target));
            if count >= maximum {
                count = maximum;
                break;
            }
        }
        counts.insert(source, count);
    }
    counts
        .remove(&0)
        .ok_or_else(|| DatatypeError::invalid("XSD regex initial saturated cardinality is absent"))
}

fn enumerate_dfa<C: DatatypeControl>(
    automaton: &Dfa,
    cardinality: &BigUint,
    limits: RegexLimits,
    control: &C,
) -> Result<Vec<String>, DatatypeError> {
    let expected = cardinality.to_usize().ok_or_else(|| {
        DatatypeError::resource(
            "max_enumeration_values",
            u64::MAX,
            limits.max_enumeration_values,
        )
    })?;
    let productive = productive_dfa_states(automaton)?;
    let mut pending = VecDeque::from([(0_usize, String::new())]);
    let mut output = Vec::with_capacity(expected);
    let mut work = 0_u64;
    while let Some((state, prefix)) = pending.pop_front() {
        if automaton.accepting.contains(&state) {
            output.push(prefix.clone());
        }
        let row = automaton
            .transitions
            .get(state)
            .ok_or_else(|| DatatypeError::invalid("XSD regex enumeration state is absent"))?;
        for transition in row {
            if !productive.contains(&transition.target) {
                continue;
            }
            for (lower, upper) in transition.characters.intervals() {
                for codepoint in *lower..=*upper {
                    let character = char::from_u32(codepoint).ok_or_else(|| {
                        DatatypeError::invalid("XSD regex transition contains a non-scalar value")
                    })?;
                    let mut value = prefix.clone();
                    value.push(character);
                    pending.push_back((transition.target, value));
                    work = work.checked_add(1).ok_or_else(|| {
                        DatatypeError::invalid("XSD regex enumeration work counter overflow")
                    })?;
                    if work > limits.max_pattern_transitions {
                        return Err(DatatypeError::resource(
                            "max_pattern_transitions",
                            work,
                            limits.max_pattern_transitions,
                        ));
                    }
                    if work % limits.cancellation_poll_stride == 0 {
                        control.poll()?;
                    }
                }
            }
        }
        let items = pending.len().saturating_add(output.len());
        control.observe_memory(
            u64::try_from(items)
                .unwrap_or(u64::MAX)
                .saturating_mul(u64::try_from(std::mem::size_of::<String>()).unwrap_or(u64::MAX)),
        )?;
    }
    control.poll()?;
    if output.len() != expected {
        return Err(DatatypeError::invalid(
            "XSD regex DFA cardinality and enumeration disagree",
        ));
    }
    Ok(output)
}

#[derive(Clone, Debug, Default)]
struct TrieNode {
    terminal: bool,
    children: BTreeMap<u32, usize>,
}

fn first_dfa_string<C: DatatypeControl>(
    automaton: &Dfa,
    excluding: &BTreeSet<String>,
    limits: RegexLimits,
    control: &C,
) -> Result<String, DatatypeError> {
    let productive = productive_dfa_states(automaton)?;
    if !productive.contains(&0) {
        return Err(DatatypeError::invalid("XSD regex language is empty"));
    }
    let mut trie = vec![TrieNode::default()];
    let mut exclusion_characters = 0_u64;
    for value in excluding {
        let mut cursor = 0_usize;
        for character in value.chars() {
            exclusion_characters = exclusion_characters.checked_add(1).ok_or_else(|| {
                DatatypeError::invalid("XSD regex exclusion character counter overflow")
            })?;
            if exclusion_characters > limits.max_lexical_characters {
                return Err(DatatypeError::resource(
                    "max_lexical_characters",
                    exclusion_characters,
                    limits.max_lexical_characters,
                ));
            }
            let codepoint = u32::from(character);
            let existing = trie
                .get(cursor)
                .and_then(|node| node.children.get(&codepoint))
                .copied();
            cursor = if let Some(child) = existing {
                child
            } else {
                let child = trie.len();
                let node = trie.get_mut(cursor).ok_or_else(|| {
                    DatatypeError::invalid("XSD regex exclusion trie cursor is absent")
                })?;
                node.children.insert(codepoint, child);
                trie.push(TrieNode::default());
                child
            };
        }
        let node = trie
            .get_mut(cursor)
            .ok_or_else(|| DatatypeError::invalid("XSD regex exclusion trie terminal is absent"))?;
        node.terminal = true;
    }

    let mut pending = VecDeque::from([(0_usize, Some(0_usize), String::new())]);
    let mut visited = BTreeSet::new();
    let mut work = 0_u64;
    while let Some((state, trie_node, prefix)) = pending.pop_front() {
        if !visited.insert((state, trie_node)) {
            continue;
        }
        let excluded_terminal = trie_node
            .and_then(|node| trie.get(node))
            .is_some_and(|node| node.terminal);
        if automaton.accepting.contains(&state) && !excluded_terminal {
            control.poll()?;
            return Ok(prefix);
        }
        let mut candidates: Vec<(u32, usize, Option<usize>)> = Vec::new();
        let row = automaton
            .transitions
            .get(state)
            .ok_or_else(|| DatatypeError::invalid("XSD regex witness state is absent"))?;
        for transition in row {
            if !productive.contains(&transition.target) {
                continue;
            }
            let Some(node_index) = trie_node else {
                let codepoint = transition
                    .characters
                    .intervals()
                    .first()
                    .map(|interval| interval.0)
                    .ok_or_else(|| DatatypeError::invalid("empty XSD regex DFA transition"))?;
                candidates.push((codepoint, transition.target, None));
                continue;
            };
            let node = trie
                .get(node_index)
                .ok_or_else(|| DatatypeError::invalid("XSD regex witness trie node is absent"))?;
            let blocked: BTreeSet<u32> = node.children.keys().copied().collect();
            for (codepoint, child) in &node.children {
                if transition.characters.contains(*codepoint) {
                    candidates.push((*codepoint, transition.target, Some(*child)));
                }
            }
            if let Some(codepoint) = transition.characters.first_outside(&blocked) {
                candidates.push((codepoint, transition.target, None));
            }
        }
        candidates.sort_unstable();
        candidates.dedup();
        for (codepoint, target, child) in candidates {
            let character = char::from_u32(codepoint).ok_or_else(|| {
                DatatypeError::invalid("XSD regex witness contains a non-scalar value")
            })?;
            let mut value = prefix.clone();
            value.push(character);
            pending.push_back((target, child, value));
            work = work
                .checked_add(1)
                .ok_or_else(|| DatatypeError::invalid("XSD regex witness work counter overflow"))?;
            if work > limits.max_pattern_transitions {
                return Err(DatatypeError::resource(
                    "max_pattern_transitions",
                    work,
                    limits.max_pattern_transitions,
                ));
            }
            if work % limits.cancellation_poll_stride == 0 {
                control.poll()?;
            }
        }
    }
    Err(DatatypeError::invalid(
        "XSD regex language has no nonexcluded member",
    ))
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::{AtomicU64, Ordering};

    use serde::Deserialize;

    use super::*;
    use crate::datatypes::value::{DatatypeErrorKind, NeverCancel};

    const FIXTURE: &str = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../tests/data/datatypes/xsd-regex-native-v1.json"
    ));

    #[derive(Debug, Deserialize)]
    struct Fixture {
        schema: String,
        unicode_version: String,
        membership: Vec<LanguageCase>,
        algebra: Vec<AlgebraCase>,
        invalid: Vec<InvalidCase>,
    }

    #[derive(Debug, Deserialize)]
    struct Sample {
        matches: bool,
        value: String,
    }

    #[derive(Debug, Deserialize)]
    struct LanguageCase {
        name: String,
        pattern: String,
        samples: Vec<Sample>,
        finite: bool,
        cardinality: Option<String>,
        enumeration: Option<Vec<String>>,
    }

    #[derive(Debug, Deserialize)]
    struct AlgebraCase {
        name: String,
        left: String,
        right: Option<String>,
        operation: String,
        empty: bool,
        samples: Vec<Sample>,
        finite: bool,
        cardinality: Option<String>,
        enumeration: Option<Vec<String>>,
    }

    #[derive(Debug, Deserialize)]
    struct InvalidCase {
        name: String,
        pattern: String,
    }

    fn fixture() -> Result<Fixture, DatatypeError> {
        serde_json::from_str(FIXTURE)
            .map_err(|error| DatatypeError::invalid(format!("invalid XSD regex fixture: {error}")))
    }

    fn ensure(condition: bool, message: impl Into<String>) -> Result<(), DatatypeError> {
        if condition {
            Ok(())
        } else {
            Err(DatatypeError::invalid(message))
        }
    }

    fn verify_cardinality(
        name: &str,
        finite: bool,
        expected: Option<&str>,
        actual: Option<BigUint>,
    ) -> Result<(), DatatypeError> {
        ensure(
            finite == actual.is_some(),
            format!("finite-language mismatch for {name}"),
        )?;
        let rendered = actual.map(|value| value.to_string());
        ensure(
            expected == rendered.as_deref(),
            format!("cardinality mismatch for {name}: expected {expected:?}, got {rendered:?}"),
        )
    }

    fn verify_samples(
        name: &str,
        language: &XsdRegex,
        samples: &[Sample],
    ) -> Result<(), DatatypeError> {
        for sample in samples {
            let actual = language.fullmatch(&sample.value, RegexLimits::default(), &NeverCancel)?;
            ensure(
                actual == sample.matches,
                format!(
                    "membership mismatch for {name} and {:?}: expected {}, got {actual}",
                    sample.value, sample.matches
                ),
            )?;
        }
        Ok(())
    }

    fn algebra_language(case: &AlgebraCase) -> Result<XsdRegex, DatatypeError> {
        let left = XsdRegex::compile_default(&case.left, &NeverCancel)?;
        let right = case
            .right
            .as_deref()
            .map(|pattern| XsdRegex::compile_default(pattern, &NeverCancel))
            .transpose()?;
        match (case.operation.as_str(), right.as_ref()) {
            ("intersection", Some(selected)) => Ok(left.intersection(selected)),
            ("union", Some(selected)) => Ok(left.union(selected)),
            ("complement", None) => Ok(left.complement()),
            ("difference", Some(selected)) => Ok(left.intersection(&selected.complement())),
            _ => Err(DatatypeError::invalid(format!(
                "invalid XSD regex fixture operation for {}: {}",
                case.name, case.operation
            ))),
        }
    }

    #[test]
    fn python_fixture_membership_cardinality_and_enumeration_match() -> Result<(), DatatypeError> {
        let selected = fixture()?;
        ensure(
            selected.schema == "pyhermit.xsd-regex.native-parity.v1",
            "unexpected XSD regex fixture schema",
        )?;
        ensure(
            selected.unicode_version == XSD_REGEX_UNICODE_VERSION,
            "Python and Rust XSD regex Unicode versions differ",
        )?;
        for case in selected.membership {
            let language = XsdRegex::compile_default(&case.pattern, &NeverCancel)?;
            verify_samples(&case.name, &language, &case.samples)?;
            verify_cardinality(
                &case.name,
                case.finite,
                case.cardinality.as_deref(),
                language.finite_cardinality(RegexLimits::default(), &NeverCancel)?,
            )?;
            if let Some(expected) = case.enumeration {
                let actual = language.enumerate_strings(RegexLimits::default(), &NeverCancel)?;
                ensure(
                    actual == expected,
                    format!("enumeration mismatch for {}", case.name),
                )?;
            }
        }
        Ok(())
    }

    #[test]
    fn python_fixture_boolean_algebra_matches() -> Result<(), DatatypeError> {
        for case in fixture()?.algebra {
            let language = algebra_language(&case)?;
            ensure(
                language.is_empty_exact(RegexLimits::default(), &NeverCancel)? == case.empty,
                format!("emptiness mismatch for {}", case.name),
            )?;
            verify_samples(&case.name, &language, &case.samples)?;
            verify_cardinality(
                &case.name,
                case.finite,
                case.cardinality.as_deref(),
                language.finite_cardinality(RegexLimits::default(), &NeverCancel)?,
            )?;
            if let Some(expected) = case.enumeration {
                let actual = language.enumerate_strings(RegexLimits::default(), &NeverCancel)?;
                ensure(
                    actual == expected,
                    format!("enumeration mismatch for {}", case.name),
                )?;
            }
        }
        Ok(())
    }

    #[test]
    fn python_fixture_invalid_patterns_remain_invalid() -> Result<(), DatatypeError> {
        for case in fixture()?.invalid {
            let error = XsdRegex::compile_default(&case.pattern, &NeverCancel).err();
            ensure(
                error
                    .as_ref()
                    .is_some_and(|value| value.kind == DatatypeErrorKind::Invalid),
                format!(
                    "invalid fixture pattern compiled or returned the wrong error: {}",
                    case.name
                ),
            )?;
        }
        Ok(())
    }

    #[test]
    fn witness_is_shortest_then_codepoint_ordered() -> Result<(), DatatypeError> {
        let language = XsdRegex::compile_default("[ab]*", &NeverCancel)?;
        let mut excluded = BTreeSet::new();
        excluded.insert(String::new());
        excluded.insert(String::from("a"));
        ensure(
            language.first_string(&excluded, RegexLimits::default(), &NeverCancel)? == "b",
            "native XSD regex witness ordering changed",
        )?;
        ensure(
            language.cardinality_up_to(7, RegexLimits::default(), &NeverCancel)? == 7,
            "infinite-language cardinality saturation changed",
        )
    }

    fn limits() -> RegexLimits {
        RegexLimits {
            max_lexical_characters: 64,
            max_enumeration_values: 64,
            max_pattern_states: 64,
            max_pattern_transitions: 256,
            max_pattern_depth: 16,
            cancellation_poll_stride: 1,
        }
    }

    fn require_limit(
        result: Result<XsdRegex, DatatypeError>,
        expected: &'static str,
    ) -> Result<(), DatatypeError> {
        let error = result.err().ok_or_else(|| {
            DatatypeError::invalid(format!("expected resource limit: {expected}"))
        })?;
        ensure(
            error.kind == DatatypeErrorKind::Resource && error.limit == Some(expected),
            format!("expected {expected} resource error, got {error:?}"),
        )
    }

    #[test]
    fn hostile_parser_inputs_are_bounded() -> Result<(), DatatypeError> {
        let mut selected = limits();
        selected.max_lexical_characters = 3;
        require_limit(
            XsdRegex::compile("abcd", selected, &NeverCancel),
            "max_lexical_characters",
        )?;

        selected = limits();
        selected.max_pattern_states = 4;
        require_limit(
            XsdRegex::compile("abcdef", selected, &NeverCancel),
            "max_pattern_states",
        )?;
        require_limit(
            XsdRegex::compile("a{100}", selected, &NeverCancel),
            "max_pattern_states",
        )?;

        selected = limits();
        selected.max_pattern_depth = 2;
        require_limit(
            XsdRegex::compile("(((a)))", selected, &NeverCancel),
            "max_pattern_depth",
        )
    }

    #[test]
    fn hostile_determinization_is_transition_bounded() -> Result<(), DatatypeError> {
        let language = XsdRegex::compile_default("(a|b|c)*z", &NeverCancel)?;
        let mut selected = limits();
        selected.max_pattern_transitions = 1;
        let error = language
            .finite_cardinality(selected, &NeverCancel)
            .err()
            .ok_or_else(|| DatatypeError::invalid("expected transition resource limit"))?;
        ensure(
            error.kind == DatatypeErrorKind::Resource
                && error.limit == Some("max_pattern_transitions"),
            format!("expected transition resource error, got {error:?}"),
        )?;

        ensure(
            !language.fullmatch("abc", RegexLimits::default(), &NeverCancel)?,
            "cache setup match unexpectedly succeeded",
        )?;
        let error = language
            .fullmatch("abc", selected, &NeverCancel)
            .err()
            .ok_or_else(|| DatatypeError::invalid("expected cached transition resource limit"))?;
        ensure(
            error.kind == DatatypeErrorKind::Resource
                && error.limit == Some("max_pattern_transitions"),
            format!("cached DFA bypassed transition resource limit: {error:?}"),
        )
    }

    struct CancelAfter {
        polls: AtomicU64,
        allowed: u64,
    }

    impl DatatypeControl for CancelAfter {
        fn poll(&self) -> Result<(), DatatypeError> {
            let prior = self.polls.fetch_add(1, Ordering::Relaxed);
            if prior >= self.allowed {
                Err(DatatypeError::cancelled(
                    "native XSD regex test cancellation",
                ))
            } else {
                Ok(())
            }
        }
    }

    #[test]
    fn parser_cooperatively_cancels_during_hostile_input() -> Result<(), DatatypeError> {
        let control = CancelAfter {
            polls: AtomicU64::new(0),
            allowed: 3,
        };
        let error = XsdRegex::compile(&"a".repeat(60), limits(), &control)
            .err()
            .ok_or_else(|| DatatypeError::invalid("expected XSD regex cancellation"))?;
        ensure(
            error.kind == DatatypeErrorKind::Cancelled,
            format!("expected cancellation, got {error:?}"),
        )
    }

    struct RejectMemory;

    impl DatatypeControl for RejectMemory {
        fn poll(&self) -> Result<(), DatatypeError> {
            Ok(())
        }

        fn observe_memory(&self, bytes: u64) -> Result<(), DatatypeError> {
            if bytes > 4 {
                Err(DatatypeError::resource("memory_bytes", bytes, 4))
            } else {
                Ok(())
            }
        }
    }

    #[test]
    fn parser_reports_memory_pressure_before_allocation_growth() -> Result<(), DatatypeError> {
        let error = XsdRegex::compile("abc", limits(), &RejectMemory)
            .err()
            .ok_or_else(|| DatatypeError::invalid("expected XSD regex memory rejection"))?;
        ensure(
            error.kind == DatatypeErrorKind::Resource && error.limit == Some("memory_bytes"),
            format!("expected memory resource error, got {error:?}"),
        )
    }

    #[test]
    fn lazy_membership_reports_memory_pressure_before_cache_growth() -> Result<(), DatatypeError> {
        let language = XsdRegex::compile_default(r"\p{Lu}\p{Ll}{0,31}", &NeverCancel)?;
        let error = language
            .fullmatch("Δelta", RegexLimits::default(), &RejectMemory)
            .err()
            .ok_or_else(|| DatatypeError::invalid("expected lazy match memory rejection"))?;
        ensure(
            error.kind == DatatypeErrorKind::Resource && error.limit == Some("memory_bytes"),
            format!("expected lazy match memory resource error, got {error:?}"),
        )?;
        ensure(
            language.matches.get().is_none(),
            "lazy match cache grew before caller memory approval",
        )
    }

    #[test]
    fn unicode_membership_remains_lazy_and_clone_shared() -> Result<(), DatatypeError> {
        let language = XsdRegex::compile_default(r"\p{Lu}\p{Ll}{0,31}", &NeverCancel)?;
        let cloned = language.clone();
        let matched = std::thread::spawn(move || {
            cloned.fullmatch("Δelta", RegexLimits::default(), &NeverCancel)
        })
        .join()
        .map_err(|_| DatatypeError::invalid("lazy XSD regex worker panicked"))??;
        ensure(matched, "Unicode lazy membership failed")?;
        ensure(
            language.automaton.get().is_none(),
            "membership eagerly materialized the complete symbolic DFA",
        )?;
        ensure(
            language.matches.get().is_some(),
            "cloned regex did not share the lazy membership cache",
        )
    }
}
