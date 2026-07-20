//! Deterministic object-role equivalence and simple-hierarchy closure.
//!
//! This phase consumes the canonical role signature and provenance-bearing
//! simple inclusions. It computes exactly the scalar role model's object SCCs,
//! inverse component pairing, quotient DAG, and reflexive transitive closure.
//! Complex inclusions, regularity, simplicity, automata, and clausification
//! remain explicit later phases, so this owned fragment is not publishable.
// SPDX-License-Identifier: LGPL-3.0-or-later

#![forbid(unsafe_code)]

use std::cmp::Reverse;
use std::collections::BinaryHeap;
use std::mem::size_of;

use serde::ser::SerializeSeq;
use serde::{Serialize, Serializer};

use super::object_roles::ObjectRolePhase;
use super::simple_roles::SimpleRolePhase;
use super::{EncodedResult, EncodedValidationError};
use crate::input_wire::SymbolKind;

const OBJECT_ROLE_HIERARCHY_SCHEMA_VERSION: u16 = 1;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ObjectRoleHierarchyLimits {
    pub max_roles: usize,
    pub max_inclusions: usize,
    pub max_components: usize,
    pub max_owned_bytes: usize,
    pub max_work: u64,
    pub max_manifest_bytes: usize,
}

impl Default for ObjectRoleHierarchyLimits {
    fn default() -> Self {
        Self {
            max_roles: 1_000_000,
            max_inclusions: 100_000_000,
            max_components: 1_000_000,
            max_owned_bytes: 512 * 1024 * 1024,
            max_work: 2_000_000_000,
            max_manifest_bytes: 512 * 1024 * 1024,
        }
    }
}

/// Adaptive canonical reachability retained for one quotient component.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ComponentReachability {
    Sparse(Vec<u32>),
    Dense(Vec<u64>),
}

impl ComponentReachability {
    #[must_use]
    pub fn contains(&self, member: u32) -> bool {
        match self {
            Self::Sparse(values) => values.binary_search(&member).is_ok(),
            Self::Dense(words) => {
                let index = usize::try_from(member / 64).unwrap_or(usize::MAX);
                let bit = member % 64;
                words
                    .get(index)
                    .is_some_and(|word| word & (1_u64 << bit) != 0)
            }
        }
    }

    fn cardinality(&self) -> usize {
        match self {
            Self::Sparse(values) => values.len(),
            Self::Dense(words) => words.iter().fold(0_usize, |total, word| {
                total.saturating_add(usize::try_from(word.count_ones()).unwrap_or(usize::MAX))
            }),
        }
    }
}

impl Serialize for ComponentReachability {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut sequence = serializer.serialize_seq(Some(self.cardinality()))?;
        match self {
            Self::Sparse(values) => {
                for value in values {
                    sequence.serialize_element(value)?;
                }
            }
            Self::Dense(words) => {
                for (word_index, word) in words.iter().copied().enumerate() {
                    let mut remaining = word;
                    while remaining != 0 {
                        let offset = remaining.trailing_zeros();
                        let member = word_index
                            .checked_mul(64)
                            .and_then(|base| {
                                base.checked_add(usize::try_from(offset).unwrap_or(usize::MAX))
                            })
                            .and_then(|value| u32::try_from(value).ok())
                            .ok_or_else(|| {
                                serde::ser::Error::custom("dense reachability ID overflowed")
                            })?;
                        sequence.serialize_element(&member)?;
                        remaining &= remaining - 1;
                    }
                }
            }
        }
        sequence.end()
    }
}

/// Owned output of object-role SCC and simple-hierarchy compilation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ObjectRoleHierarchyPhase {
    pub object_components: Vec<Vec<u32>>,
    pub object_component_by_role: Vec<u32>,
    pub object_super_components: Vec<ComponentReachability>,
    pub inverse_component_ids: Vec<u32>,
    pub top_component_id: u32,
    pub bottom_component_id: u32,
    pub work: u64,
    pub owned_bytes: usize,
    manifest_limit: usize,
}

impl ObjectRoleHierarchyPhase {
    /// Canonical private manifest used for exact scalar differential checks.
    pub fn canonical_manifest_json(&self) -> EncodedResult<Vec<u8>> {
        validate_phase_shape(self, self.object_component_by_role.len())?;
        let encoded = serde_json::to_vec(&ObjectRoleHierarchyManifest {
            schema_version: OBJECT_ROLE_HIERARCHY_SCHEMA_VERSION,
            family: "object_role_hierarchy",
            object_components: &self.object_components,
            object_component_by_role: &self.object_component_by_role,
            object_super_components: &self.object_super_components,
            inverse_component_ids: &self.inverse_component_ids,
            top_component_id: self.top_component_id,
            bottom_component_id: self.bottom_component_id,
        })
        .map_err(|_| {
            EncodedValidationError::invariant("object-role hierarchy manifest serialization failed")
        })?;
        if encoded.len() > self.manifest_limit {
            return Err(EncodedValidationError::resource(
                "object-role hierarchy manifest exceeds its byte limit",
            ));
        }
        Ok(encoded)
    }
}

#[derive(Serialize)]
struct ObjectRoleHierarchyManifest<'a> {
    schema_version: u16,
    family: &'static str,
    object_components: &'a [Vec<u32>],
    object_component_by_role: &'a [u32],
    object_super_components: &'a [ComponentReachability],
    inverse_component_ids: &'a [u32],
    top_component_id: u32,
    bottom_component_id: u32,
}

struct PhaseBudget {
    limits: ObjectRoleHierarchyLimits,
    work: u64,
    owned_bytes: usize,
}

impl PhaseBudget {
    const fn new(limits: ObjectRoleHierarchyLimits) -> Self {
        Self {
            limits,
            work: 0,
            owned_bytes: 0,
        }
    }

    fn claim_work(&mut self, amount: usize) -> EncodedResult<()> {
        let amount = u64::try_from(amount).map_err(|_| {
            EncodedValidationError::resource("object-role hierarchy work exceeds u64")
        })?;
        let following = self.work.checked_add(amount).ok_or_else(|| {
            EncodedValidationError::resource("object-role hierarchy work overflowed")
        })?;
        if following > self.limits.max_work {
            return Err(EncodedValidationError::resource(
                "object-role hierarchy compilation exceeds its work limit",
            ));
        }
        self.work = following;
        Ok(())
    }

    fn claim_owned(&mut self, amount: usize) -> EncodedResult<()> {
        let following = self.owned_bytes.checked_add(amount).ok_or_else(|| {
            EncodedValidationError::resource("object-role hierarchy owned-byte count overflowed")
        })?;
        if following > self.limits.max_owned_bytes {
            return Err(EncodedValidationError::resource(
                "object-role hierarchy compilation exceeds its owned-byte limit",
            ));
        }
        self.owned_bytes = following;
        Ok(())
    }
}

/// Collapse the canonical simple role graph and compute its super-role closure.
pub fn compile_object_role_hierarchy_phase(
    roles: &ObjectRolePhase,
    simple: &SimpleRolePhase,
    limits: ObjectRoleHierarchyLimits,
) -> EncodedResult<ObjectRoleHierarchyPhase> {
    validate_inputs(roles, simple, limits)?;
    let edges = simple
        .simple_inclusions
        .iter()
        .map(|value| (value.sub_role_id, value.super_role_id));
    build_hierarchy(
        roles.object_role_domain.values.len(),
        &roles.inverse_role_ids,
        roles.top_object_role_id,
        roles.bottom_object_role_id,
        edges,
        limits,
    )
}

fn build_hierarchy<I>(
    role_count: usize,
    inverse_role_ids: &[u32],
    top_role_id: u32,
    bottom_role_id: u32,
    edges: I,
    limits: ObjectRoleHierarchyLimits,
) -> EncodedResult<ObjectRoleHierarchyPhase>
where
    I: Clone + ExactSizeIterator<Item = (u32, u32)>,
{
    if role_count == 0 || role_count > limits.max_roles {
        return Err(EncodedValidationError::resource(
            "object-role hierarchy role count exceeds its limit",
        ));
    }
    if edges.len() > limits.max_inclusions {
        return Err(EncodedValidationError::resource(
            "object-role hierarchy inclusion count exceeds its limit",
        ));
    }
    validate_inverse_ids(role_count, inverse_role_ids)?;
    validate_role_id(top_role_id, role_count, "top object role")?;
    validate_role_id(bottom_role_id, role_count, "bottom object role")?;
    let mut budget = PhaseBudget::new(limits);
    let mut outgoing = empty_rows(role_count, "outgoing role adjacency", &mut budget)?;
    let mut incoming = empty_rows(role_count, "incoming role adjacency", &mut budget)?;
    for (sub, sup) in edges.clone() {
        budget.claim_work(1)?;
        validate_role_id(sub, role_count, "simple sub-role")?;
        validate_role_id(sup, role_count, "simple super-role")?;
        push_u32(
            &mut outgoing[usize_id(sub)?],
            sup,
            "outgoing role adjacency",
            &mut budget,
        )?;
        push_u32(
            &mut incoming[usize_id(sup)?],
            sub,
            "incoming role adjacency",
            &mut budget,
        )?;
    }
    canonicalize_rows(&mut outgoing, &mut budget)?;
    canonicalize_rows(&mut incoming, &mut budget)?;

    let mut visited = zeroed_u8(role_count, "SCC visited set", &mut budget)?;
    let mut finish = reserved_u32(role_count, "SCC finish order", &mut budget)?;
    let mut depth = reserved_pairs(role_count, "SCC depth stack", &mut budget)?;
    for root in 0..role_count {
        if visited[root] != 0 {
            continue;
        }
        visited[root] = 1;
        depth.push((u32_id(root)?, 0));
        while let Some((node, offset)) = depth.last_mut() {
            budget.claim_work(1)?;
            let node_index = usize_id(*node)?;
            if *offset < outgoing[node_index].len() {
                let successor = outgoing[node_index][*offset];
                *offset = offset.checked_add(1).ok_or_else(|| {
                    EncodedValidationError::resource("SCC adjacency offset overflowed")
                })?;
                let successor_index = usize_id(successor)?;
                if visited[successor_index] == 0 {
                    visited[successor_index] = 1;
                    depth.push((successor, 0));
                }
            } else {
                finish.push(*node);
                depth.pop();
            }
        }
    }
    if finish.len() != role_count {
        return Err(EncodedValidationError::invariant(
            "object-role SCC traversal omitted a finish record",
        ));
    }

    let mut assigned = zeroed_u8(role_count, "SCC assigned set", &mut budget)?;
    let mut pending = reserved_u32(role_count, "SCC pending stack", &mut budget)?;
    let mut components = empty_rows(role_count, "object-role components", &mut budget)?;
    components.clear();
    for &root in finish.iter().rev() {
        let root_index = usize_id(root)?;
        if assigned[root_index] != 0 {
            continue;
        }
        let mut members = Vec::new();
        assigned[root_index] = 1;
        pending.push(root);
        while let Some(node) = pending.pop() {
            budget.claim_work(1)?;
            push_u32(&mut members, node, "object-role component", &mut budget)?;
            for &predecessor in incoming[usize_id(node)?].iter().rev() {
                let predecessor_index = usize_id(predecessor)?;
                if assigned[predecessor_index] == 0 {
                    assigned[predecessor_index] = 1;
                    pending.push(predecessor);
                }
            }
        }
        budget.claim_work(sort_work(members.len()))?;
        members.sort_unstable();
        components.push(members);
    }
    if components.len() > limits.max_components {
        return Err(EncodedValidationError::resource(
            "object-role hierarchy component count exceeds its limit",
        ));
    }
    budget.claim_work(sort_work(components.len()))?;
    components.sort_by_key(|members| members.first().copied().unwrap_or(u32::MAX));
    if components.iter().any(Vec::is_empty) {
        return Err(EncodedValidationError::invariant(
            "object-role SCC traversal produced an empty component",
        ));
    }

    let mut component_by_role = filled_u32(
        role_count,
        u32::MAX,
        "object component mapping",
        &mut budget,
    )?;
    for (component_index, members) in components.iter().enumerate() {
        let component_id = u32_id(component_index)?;
        for &role_id in members {
            budget.claim_work(1)?;
            let slot = component_by_role
                .get_mut(usize_id(role_id)?)
                .ok_or_else(|| {
                    EncodedValidationError::invariant("object-role component member is dangling")
                })?;
            if *slot != u32::MAX {
                return Err(EncodedValidationError::invariant(
                    "object role occurs in multiple SCCs",
                ));
            }
            *slot = component_id;
        }
    }
    if component_by_role.contains(&u32::MAX) {
        return Err(EncodedValidationError::invariant(
            "object-role SCC decomposition omitted a role",
        ));
    }

    let component_count = components.len();
    let mut quotient_edges = Vec::new();
    for (sub, sup) in edges {
        budget.claim_work(1)?;
        let sub_component = component_by_role[usize_id(sub)?];
        let super_component = component_by_role[usize_id(sup)?];
        if sub_component != super_component {
            push_pair(
                &mut quotient_edges,
                (sub_component, super_component),
                "object-role quotient edge",
                &mut budget,
            )?;
        }
    }
    budget.claim_work(sort_work(quotient_edges.len()))?;
    quotient_edges.sort_unstable();
    quotient_edges.dedup();
    let mut quotient = empty_rows(
        component_count,
        "object-role quotient adjacency",
        &mut budget,
    )?;
    let mut indegree = filled_u32(
        component_count,
        0,
        "object-role quotient indegree",
        &mut budget,
    )?;
    for &(sub, sup) in &quotient_edges {
        push_u32(
            &mut quotient[usize_id(sub)?],
            sup,
            "object-role quotient adjacency",
            &mut budget,
        )?;
        let degree = indegree.get_mut(usize_id(sup)?).ok_or_else(|| {
            EncodedValidationError::invariant("object-role quotient target is dangling")
        })?;
        *degree = degree.checked_add(1).ok_or_else(|| {
            EncodedValidationError::resource("object-role quotient indegree overflowed")
        })?;
    }

    let mut ready = BinaryHeap::new();
    budget.claim_owned(
        component_count
            .checked_mul(size_of::<Reverse<u32>>())
            .ok_or_else(|| EncodedValidationError::resource("topological heap overflowed"))?,
    )?;
    ready
        .try_reserve(component_count)
        .map_err(|_| EncodedValidationError::resource("topological heap allocation failed"))?;
    for (component, degree) in indegree.iter().copied().enumerate() {
        if degree == 0 {
            ready.push(Reverse(u32_id(component)?));
        }
    }
    let mut order = reserved_u32(
        component_count,
        "object-role topological order",
        &mut budget,
    )?;
    while let Some(Reverse(component)) = ready.pop() {
        budget.claim_work(1)?;
        order.push(component);
        for &successor in &quotient[usize_id(component)?] {
            let degree = indegree.get_mut(usize_id(successor)?).ok_or_else(|| {
                EncodedValidationError::invariant("object-role quotient successor is dangling")
            })?;
            *degree = degree.checked_sub(1).ok_or_else(|| {
                EncodedValidationError::invariant("object-role quotient indegree underflowed")
            })?;
            if *degree == 0 {
                ready.push(Reverse(successor));
            }
        }
    }
    if order.len() != component_count {
        return Err(EncodedValidationError::invariant(
            "object-role quotient graph contains a cycle",
        ));
    }

    let mut closure = empty_reachability(component_count, &mut budget)?;
    let mut markers = filled_u32(
        component_count,
        0,
        "object-role closure markers",
        &mut budget,
    )?;
    let mut touched = reserved_u32(
        component_count,
        "object-role closure accumulator",
        &mut budget,
    )?;
    for (epoch_index, &component) in order.iter().rev().enumerate() {
        let epoch = u32_id(epoch_index.checked_add(1).ok_or_else(|| {
            EncodedValidationError::resource("object-role closure epoch overflowed")
        })?)?;
        touched.clear();
        mark_member(component, epoch, &mut markers, &mut touched)?;
        for &successor in &quotient[usize_id(component)?] {
            let traversed = mark_reachability(
                &closure[usize_id(successor)?],
                epoch,
                &mut markers,
                &mut touched,
            )?;
            budget.claim_work(traversed)?;
        }
        budget.claim_work(sort_work(touched.len()))?;
        touched.sort_unstable();
        closure[usize_id(component)?] = encode_reachability(&touched, &mut budget)?;
    }

    let mut inverse_component_ids = reserved_u32(
        component_count,
        "inverse object-role components",
        &mut budget,
    )?;
    for members in &components {
        let representative = *members.first().ok_or_else(|| {
            EncodedValidationError::invariant("object-role component lost its representative")
        })?;
        let inverse_component = component_by_role[usize_id(
            *inverse_role_ids
                .get(usize_id(representative)?)
                .ok_or_else(|| {
                    EncodedValidationError::invariant("inverse object-role ID is dangling")
                })?,
        )?];
        for &member in members {
            budget.claim_work(1)?;
            let inverse = *inverse_role_ids.get(usize_id(member)?).ok_or_else(|| {
                EncodedValidationError::invariant("inverse object-role ID is dangling")
            })?;
            if component_by_role[usize_id(inverse)?] != inverse_component {
                return Err(EncodedValidationError::invariant(
                    "inverse roles from one SCC do not share an inverse SCC",
                ));
            }
        }
        inverse_component_ids.push(inverse_component);
    }
    for (component, inverse) in inverse_component_ids.iter().copied().enumerate() {
        if inverse_component_ids.get(usize_id(inverse)?).copied() != Some(u32_id(component)?) {
            return Err(EncodedValidationError::invariant(
                "inverse object-role component mapping is not involutive",
            ));
        }
    }

    let top_component_id = component_by_role[usize_id(top_role_id)?];
    let bottom_component_id = component_by_role[usize_id(bottom_role_id)?];
    let phase = ObjectRoleHierarchyPhase {
        object_components: components,
        object_component_by_role: component_by_role,
        object_super_components: closure,
        inverse_component_ids,
        top_component_id,
        bottom_component_id,
        work: budget.work,
        owned_bytes: budget.owned_bytes,
        manifest_limit: limits.max_manifest_bytes,
    };
    validate_phase_shape(&phase, role_count)?;
    Ok(phase)
}

fn validate_inputs(
    roles: &ObjectRolePhase,
    simple: &SimpleRolePhase,
    limits: ObjectRoleHierarchyLimits,
) -> EncodedResult<()> {
    if roles.object_role_domain.kind != SymbolKind::ObjectRole {
        return Err(EncodedValidationError::invariant(
            "object-role hierarchy received a non-role domain",
        ));
    }
    let role_count = roles.object_role_domain.values.len();
    if role_count == 0 || role_count > limits.max_roles {
        return Err(EncodedValidationError::resource(
            "object-role hierarchy role count exceeds its limit",
        ));
    }
    if roles.inverse_role_ids.len() != role_count
        || roles
            .object_role_domain
            .values
            .iter()
            .enumerate()
            .any(|(index, value)| usize::try_from(value.identifier).ok() != Some(index))
    {
        return Err(EncodedValidationError::invariant(
            "object-role hierarchy received a non-dense role domain",
        ));
    }
    validate_inverse_ids(role_count, &roles.inverse_role_ids)?;
    if simple.simple_inclusions.len() > limits.max_inclusions {
        return Err(EncodedValidationError::resource(
            "object-role hierarchy inclusion count exceeds its limit",
        ));
    }
    if simple.simple_inclusions.windows(2).any(|pair| {
        (pair[0].sub_role_id, pair[0].super_role_id) >= (pair[1].sub_role_id, pair[1].super_role_id)
    }) {
        return Err(EncodedValidationError::invariant(
            "object-role hierarchy received non-canonical simple inclusions",
        ));
    }
    for inclusion in &simple.simple_inclusions {
        validate_role_id(inclusion.sub_role_id, role_count, "simple sub-role")?;
        validate_role_id(inclusion.super_role_id, role_count, "simple super-role")?;
    }
    Ok(())
}

fn validate_inverse_ids(role_count: usize, inverse_role_ids: &[u32]) -> EncodedResult<()> {
    if inverse_role_ids.len() != role_count {
        return Err(EncodedValidationError::invariant(
            "object-role inverse mapping has the wrong length",
        ));
    }
    for (role, inverse) in inverse_role_ids.iter().copied().enumerate() {
        validate_role_id(inverse, role_count, "inverse object role")?;
        if inverse_role_ids.get(usize_id(inverse)?).copied() != Some(u32_id(role)?) {
            return Err(EncodedValidationError::invariant(
                "object-role inverse mapping is not involutive",
            ));
        }
    }
    Ok(())
}

fn validate_phase_shape(phase: &ObjectRoleHierarchyPhase, role_count: usize) -> EncodedResult<()> {
    let component_count = phase.object_components.len();
    if component_count == 0
        || phase.object_component_by_role.len() != role_count
        || phase.object_super_components.len() != component_count
        || phase.inverse_component_ids.len() != component_count
    {
        return Err(EncodedValidationError::invariant(
            "object-role hierarchy phase has inconsistent dimensions",
        ));
    }
    let mut expected_role = 0_usize;
    let mut previous_least = None;
    for (component, members) in phase.object_components.iter().enumerate() {
        let Some(&least) = members.first() else {
            return Err(EncodedValidationError::invariant(
                "object-role hierarchy contains an empty component",
            ));
        };
        if previous_least.is_some_and(|value| value >= least)
            || members.windows(2).any(|pair| pair[0] >= pair[1])
        {
            return Err(EncodedValidationError::invariant(
                "object-role hierarchy components are not canonical",
            ));
        }
        previous_least = Some(least);
        for &role in members {
            validate_role_id(role, role_count, "object-role component member")?;
            if phase.object_component_by_role[usize_id(role)?] != u32_id(component)? {
                return Err(EncodedValidationError::invariant(
                    "object-role component mapping disagrees with its partition",
                ));
            }
            expected_role = expected_role.checked_add(1).ok_or_else(|| {
                EncodedValidationError::resource("object-role partition size overflowed")
            })?;
        }
    }
    if expected_role != role_count {
        return Err(EncodedValidationError::invariant(
            "object-role hierarchy components do not partition the role domain",
        ));
    }
    for (component, reachable) in phase.object_super_components.iter().enumerate() {
        if !reachability_is_canonical(reachable, component_count)
            || !reachable.contains(u32_id(component)?)
        {
            return Err(EncodedValidationError::invariant(
                "object-role super-component closure is not canonical and reflexive",
            ));
        }
    }
    for (component, inverse) in phase.inverse_component_ids.iter().copied().enumerate() {
        validate_role_id(inverse, component_count, "inverse object-role component")?;
        if phase.inverse_component_ids.get(usize_id(inverse)?).copied() != Some(u32_id(component)?)
        {
            return Err(EncodedValidationError::invariant(
                "inverse object-role component mapping is not involutive",
            ));
        }
    }
    validate_role_id(
        phase.top_component_id,
        component_count,
        "top object-role component",
    )?;
    validate_role_id(
        phase.bottom_component_id,
        component_count,
        "bottom object-role component",
    )?;
    Ok(())
}

fn reachability_is_canonical(value: &ComponentReachability, component_count: usize) -> bool {
    match value {
        ComponentReachability::Sparse(values) => {
            !values.is_empty()
                && values.windows(2).all(|pair| pair[0] < pair[1])
                && values
                    .last()
                    .is_some_and(|last| usize::try_from(*last).is_ok_and(|id| id < component_count))
        }
        ComponentReachability::Dense(words) => {
            if words.is_empty() || words.last() == Some(&0) {
                return false;
            }
            let maximum_words = component_count.saturating_add(63) / 64;
            if words.len() > maximum_words {
                return false;
            }
            let remainder = component_count % 64;
            remainder == 0
                || words.len() < maximum_words
                || words.last().is_some_and(|word| *word >> remainder == 0)
        }
    }
}

fn mark_reachability(
    value: &ComponentReachability,
    epoch: u32,
    markers: &mut [u32],
    touched: &mut Vec<u32>,
) -> EncodedResult<usize> {
    let mut traversed = 0_usize;
    match value {
        ComponentReachability::Sparse(values) => {
            for &member in values {
                traversed = traversed.saturating_add(1);
                mark_member(member, epoch, markers, touched)?;
            }
        }
        ComponentReachability::Dense(words) => {
            for (word_index, word) in words.iter().copied().enumerate() {
                let mut remaining = word;
                while remaining != 0 {
                    traversed = traversed.saturating_add(1);
                    let offset = usize::try_from(remaining.trailing_zeros()).map_err(|_| {
                        EncodedValidationError::invariant("bit offset exceeds usize")
                    })?;
                    let member = word_index
                        .checked_mul(64)
                        .and_then(|base| base.checked_add(offset))
                        .and_then(|index| u32::try_from(index).ok())
                        .ok_or_else(|| {
                            EncodedValidationError::resource("dense reachability ID overflowed")
                        })?;
                    mark_member(member, epoch, markers, touched)?;
                    remaining &= remaining - 1;
                }
            }
        }
    }
    Ok(traversed)
}

fn mark_member(
    member: u32,
    epoch: u32,
    markers: &mut [u32],
    touched: &mut Vec<u32>,
) -> EncodedResult<()> {
    let marker = markers.get_mut(usize_id(member)?).ok_or_else(|| {
        EncodedValidationError::invariant("object-role closure member is dangling")
    })?;
    if *marker != epoch {
        *marker = epoch;
        if touched.len() == touched.capacity() {
            return Err(EncodedValidationError::resource(
                "object-role closure accumulator exceeded its reserved domain",
            ));
        }
        touched.push(member);
    }
    Ok(())
}

fn encode_reachability(
    members: &[u32],
    budget: &mut PhaseBudget,
) -> EncodedResult<ComponentReachability> {
    let maximum = usize_id(*members.last().ok_or_else(|| {
        EncodedValidationError::invariant("object-role closure cannot be empty")
    })?)?;
    let dense_words = maximum
        .checked_div(64)
        .and_then(|value| value.checked_add(1))
        .ok_or_else(|| EncodedValidationError::resource("dense closure size overflowed"))?;
    let dense_bytes = dense_words
        .checked_mul(size_of::<u64>())
        .ok_or_else(|| EncodedValidationError::resource("dense closure bytes overflowed"))?;
    let sparse_bytes = members
        .len()
        .checked_mul(size_of::<u32>())
        .ok_or_else(|| EncodedValidationError::resource("sparse closure bytes overflowed"))?;
    if dense_bytes <= sparse_bytes {
        budget.claim_owned(dense_bytes)?;
        let mut words = Vec::new();
        words
            .try_reserve_exact(dense_words)
            .map_err(|_| EncodedValidationError::resource("dense closure allocation failed"))?;
        words.resize(dense_words, 0_u64);
        for &member in members {
            let index = usize_id(member)?;
            words[index / 64] |= 1_u64 << (index % 64);
        }
        Ok(ComponentReachability::Dense(words))
    } else {
        budget.claim_owned(sparse_bytes)?;
        let mut values = Vec::new();
        values
            .try_reserve_exact(members.len())
            .map_err(|_| EncodedValidationError::resource("sparse closure allocation failed"))?;
        values.extend_from_slice(members);
        Ok(ComponentReachability::Sparse(values))
    }
}

fn canonicalize_rows(rows: &mut [Vec<u32>], budget: &mut PhaseBudget) -> EncodedResult<()> {
    for row in rows {
        budget.claim_work(sort_work(row.len()))?;
        row.sort_unstable();
        row.dedup();
    }
    Ok(())
}

fn empty_rows(
    count: usize,
    name: &'static str,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<Vec<u32>>> {
    budget.claim_owned(count.checked_mul(size_of::<Vec<u32>>()).ok_or_else(|| {
        EncodedValidationError::resource(format!("{name} outer allocation overflowed"))
    })?)?;
    let mut rows = Vec::new();
    rows.try_reserve_exact(count)
        .map_err(|_| EncodedValidationError::resource(format!("{name} allocation failed")))?;
    rows.resize_with(count, Vec::new);
    Ok(rows)
}

fn empty_reachability(
    count: usize,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<ComponentReachability>> {
    budget.claim_owned(
        count
            .checked_mul(size_of::<ComponentReachability>())
            .ok_or_else(|| {
                EncodedValidationError::resource("object-role closure outer allocation overflowed")
            })?,
    )?;
    let mut values = Vec::new();
    values.try_reserve_exact(count).map_err(|_| {
        EncodedValidationError::resource("object-role closure outer allocation failed")
    })?;
    values.resize_with(count, || ComponentReachability::Sparse(Vec::new()));
    Ok(values)
}

fn zeroed_u8(count: usize, name: &'static str, budget: &mut PhaseBudget) -> EncodedResult<Vec<u8>> {
    budget.claim_owned(count)?;
    let mut values = Vec::new();
    values
        .try_reserve_exact(count)
        .map_err(|_| EncodedValidationError::resource(format!("{name} allocation failed")))?;
    values.resize(count, 0);
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

fn reserved_u32(
    count: usize,
    name: &'static str,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<u32>> {
    budget.claim_owned(count.checked_mul(size_of::<u32>()).ok_or_else(|| {
        EncodedValidationError::resource(format!("{name} allocation overflowed"))
    })?)?;
    let mut values = Vec::new();
    values
        .try_reserve_exact(count)
        .map_err(|_| EncodedValidationError::resource(format!("{name} allocation failed")))?;
    Ok(values)
}

fn reserved_pairs(
    count: usize,
    name: &'static str,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<(u32, usize)>> {
    budget.claim_owned(
        count
            .checked_mul(size_of::<(u32, usize)>())
            .ok_or_else(|| {
                EncodedValidationError::resource(format!("{name} allocation overflowed"))
            })?,
    )?;
    let mut values = Vec::new();
    values
        .try_reserve_exact(count)
        .map_err(|_| EncodedValidationError::resource(format!("{name} allocation failed")))?;
    Ok(values)
}

fn push_u32(
    target: &mut Vec<u32>,
    value: u32,
    name: &'static str,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    budget.claim_owned(size_of::<u32>())?;
    target
        .try_reserve(1)
        .map_err(|_| EncodedValidationError::resource(format!("{name} allocation failed")))?;
    target.push(value);
    Ok(())
}

fn push_pair(
    target: &mut Vec<(u32, u32)>,
    value: (u32, u32),
    name: &'static str,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    budget.claim_owned(size_of::<(u32, u32)>())?;
    target
        .try_reserve(1)
        .map_err(|_| EncodedValidationError::resource(format!("{name} allocation failed")))?;
    target.push(value);
    Ok(())
}

fn validate_role_id(value: u32, count: usize, name: &'static str) -> EncodedResult<()> {
    if usize_id(value)? >= count {
        Err(EncodedValidationError::invariant(format!(
            "{name} ID is dangling"
        )))
    } else {
        Ok(())
    }
}

fn usize_id(value: u32) -> EncodedResult<usize> {
    usize::try_from(value)
        .map_err(|_| EncodedValidationError::resource("object-role graph ID exceeds usize"))
}

fn u32_id(value: usize) -> EncodedResult<u32> {
    u32::try_from(value)
        .map_err(|_| EncodedValidationError::resource("object-role graph ID exceeds u32"))
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

    #[test]
    fn sccs_inverse_components_and_transitive_closure_are_canonical() -> EncodedResult<()> {
        let phase = build_hierarchy(
            8,
            &[1, 0, 3, 2, 5, 4, 6, 7],
            6,
            7,
            [(0, 2), (1, 3), (2, 4), (3, 5), (4, 2), (5, 3)].into_iter(),
            ObjectRoleHierarchyLimits::default(),
        )?;
        assert_eq!(
            phase.object_components,
            vec![vec![0], vec![1], vec![2, 4], vec![3, 5], vec![6], vec![7]]
        );
        assert_eq!(phase.inverse_component_ids, vec![1, 0, 3, 2, 4, 5]);
        assert!(phase.object_super_components[0].contains(2));
        assert!(phase.object_super_components[1].contains(3));
        assert!(!phase.object_super_components[0].contains(3));
        assert_eq!(phase.top_component_id, 4);
        assert_eq!(phase.bottom_component_id, 5);
        Ok(())
    }

    #[test]
    fn edgeless_roles_remain_distinct_with_reflexive_sparse_closure() -> EncodedResult<()> {
        let phase = build_hierarchy(
            4,
            &[1, 0, 2, 3],
            2,
            3,
            [].into_iter(),
            ObjectRoleHierarchyLimits::default(),
        )?;
        assert_eq!(
            phase.object_components,
            vec![vec![0], vec![1], vec![2], vec![3]]
        );
        assert_eq!(
            phase.object_super_components,
            vec![
                ComponentReachability::Sparse(vec![0]),
                ComponentReachability::Sparse(vec![1]),
                ComponentReachability::Sparse(vec![2]),
                ComponentReachability::Sparse(vec![3]),
            ]
        );
        Ok(())
    }

    #[test]
    fn work_and_manifest_limits_fail_closed() -> EncodedResult<()> {
        let Err(error) = build_hierarchy(
            2,
            &[0, 1],
            0,
            1,
            [].into_iter(),
            ObjectRoleHierarchyLimits {
                max_work: 0,
                ..ObjectRoleHierarchyLimits::default()
            },
        ) else {
            return Err(EncodedValidationError::invariant(
                "zero hierarchy work limit unexpectedly succeeded",
            ));
        };
        assert_eq!(error.code, "NATIVE_ENCODED_RESOURCE_LIMIT");

        let phase = build_hierarchy(
            2,
            &[0, 1],
            0,
            1,
            [].into_iter(),
            ObjectRoleHierarchyLimits::default(),
        )?;
        let limited = ObjectRoleHierarchyPhase {
            manifest_limit: 1,
            ..phase
        };
        let Err(error) = limited.canonical_manifest_json() else {
            return Err(EncodedValidationError::invariant(
                "hierarchy manifest limit unexpectedly succeeded",
            ));
        };
        assert_eq!(error.code, "NATIVE_ENCODED_RESOURCE_LIMIT");
        Ok(())
    }
}
