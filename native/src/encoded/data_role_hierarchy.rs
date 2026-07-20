//! Deterministic data-property equivalence and hierarchy closure.
//!
//! This phase consumes the canonical data-property signature and direct
//! inclusions. It computes exactly the scalar role model's data-property SCCs,
//! quotient DAG, and reflexive transitive closure. Clausification and permanent
//! session publication remain later phases, so this owned fragment is not
//! publishable and does not advertise the encoded compiler capability.
// SPDX-License-Identifier: LGPL-3.0-or-later

#![forbid(unsafe_code)]

use std::cmp::Reverse;
use std::collections::BinaryHeap;
use std::mem::size_of;

use serde::Serialize;

use super::data_inclusions::DataInclusionPhase;
use super::data_roles::DataRolePhase;
use super::object_role_hierarchy::ComponentReachability;
use super::{EncodedResult, EncodedValidationError};
use crate::input_wire::SymbolKind;

const DATA_ROLE_HIERARCHY_SCHEMA_VERSION: u16 = 1;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct DataRoleHierarchyLimits {
    pub max_properties: usize,
    pub max_inclusions: usize,
    pub max_components: usize,
    pub max_owned_bytes: usize,
    pub max_work: u64,
    pub max_manifest_bytes: usize,
}

impl Default for DataRoleHierarchyLimits {
    fn default() -> Self {
        Self {
            max_properties: 1_000_000,
            max_inclusions: 100_000_000,
            max_components: 1_000_000,
            max_owned_bytes: 512 * 1024 * 1024,
            max_work: 2_000_000_000,
            max_manifest_bytes: 512 * 1024 * 1024,
        }
    }
}

/// Owned output of data-property SCC and hierarchy compilation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DataRoleHierarchyPhase {
    pub data_components: Vec<Vec<u32>>,
    pub data_component_by_property: Vec<u32>,
    pub data_super_components: Vec<ComponentReachability>,
    pub top_component_id: u32,
    pub bottom_component_id: u32,
    pub work: u64,
    pub owned_bytes: usize,
    manifest_limit: usize,
}

impl DataRoleHierarchyPhase {
    /// Canonical private manifest used for exact scalar differential checks.
    pub fn canonical_manifest_json(&self) -> EncodedResult<Vec<u8>> {
        validate_phase_shape(self, self.data_component_by_property.len())?;
        let encoded = serde_json::to_vec(&DataRoleHierarchyManifest {
            schema_version: DATA_ROLE_HIERARCHY_SCHEMA_VERSION,
            family: "data_property_hierarchy",
            data_components: &self.data_components,
            data_component_by_property: &self.data_component_by_property,
            data_super_components: &self.data_super_components,
            top_component_id: self.top_component_id,
            bottom_component_id: self.bottom_component_id,
        })
        .map_err(|_| {
            EncodedValidationError::invariant(
                "data-property hierarchy manifest serialization failed",
            )
        })?;
        if encoded.len() > self.manifest_limit {
            return Err(EncodedValidationError::resource(
                "data-property hierarchy manifest exceeds its byte limit",
            ));
        }
        Ok(encoded)
    }
}

#[derive(Serialize)]
struct DataRoleHierarchyManifest<'a> {
    schema_version: u16,
    family: &'static str,
    data_components: &'a [Vec<u32>],
    data_component_by_property: &'a [u32],
    data_super_components: &'a [ComponentReachability],
    top_component_id: u32,
    bottom_component_id: u32,
}

struct PhaseBudget {
    limits: DataRoleHierarchyLimits,
    work: u64,
    owned_bytes: usize,
}

impl PhaseBudget {
    const fn new(limits: DataRoleHierarchyLimits) -> Self {
        Self {
            limits,
            work: 0,
            owned_bytes: 0,
        }
    }

    fn claim_work(&mut self, amount: usize) -> EncodedResult<()> {
        let amount = u64::try_from(amount).map_err(|_| {
            EncodedValidationError::resource("data-property hierarchy work exceeds u64")
        })?;
        let following = self.work.checked_add(amount).ok_or_else(|| {
            EncodedValidationError::resource("data-property hierarchy work overflowed")
        })?;
        if following > self.limits.max_work {
            return Err(EncodedValidationError::resource(
                "data-property hierarchy compilation exceeds its work limit",
            ));
        }
        self.work = following;
        Ok(())
    }

    fn claim_owned(&mut self, amount: usize) -> EncodedResult<()> {
        let following = self.owned_bytes.checked_add(amount).ok_or_else(|| {
            EncodedValidationError::resource("data-property hierarchy owned-byte count overflowed")
        })?;
        if following > self.limits.max_owned_bytes {
            return Err(EncodedValidationError::resource(
                "data-property hierarchy compilation exceeds its owned-byte limit",
            ));
        }
        self.owned_bytes = following;
        Ok(())
    }
}

/// Collapse the canonical direct-inclusion graph and compute its super-property closure.
pub fn compile_data_role_hierarchy_phase(
    roles: &DataRolePhase,
    inclusions: &DataInclusionPhase,
    limits: DataRoleHierarchyLimits,
) -> EncodedResult<DataRoleHierarchyPhase> {
    validate_inputs(roles, inclusions, limits)?;
    let edges = inclusions
        .data_inclusions
        .iter()
        .map(|value| (value.sub_property_id, value.super_property_id));
    build_hierarchy(
        roles.data_property_domain.values.len(),
        roles.top_data_property_id,
        roles.bottom_data_property_id,
        edges,
        limits,
    )
}

fn build_hierarchy<I>(
    property_count: usize,
    top_property_id: u32,
    bottom_property_id: u32,
    edges: I,
    limits: DataRoleHierarchyLimits,
) -> EncodedResult<DataRoleHierarchyPhase>
where
    I: Clone + ExactSizeIterator<Item = (u32, u32)>,
{
    if property_count == 0 || property_count > limits.max_properties {
        return Err(EncodedValidationError::resource(
            "data-property hierarchy property count exceeds its limit",
        ));
    }
    let _ = u32_id(property_count.checked_sub(1).ok_or_else(|| {
        EncodedValidationError::invariant("data-property domain is unexpectedly empty")
    })?)?;
    if edges.len() > limits.max_inclusions {
        return Err(EncodedValidationError::resource(
            "data-property hierarchy inclusion count exceeds its limit",
        ));
    }
    validate_property_id(top_property_id, property_count, "top data property")?;
    validate_property_id(bottom_property_id, property_count, "bottom data property")?;

    let mut budget = PhaseBudget::new(limits);
    let mut outgoing = empty_rows(property_count, "outgoing data adjacency", &mut budget)?;
    let mut incoming = empty_rows(property_count, "incoming data adjacency", &mut budget)?;
    for (sub, sup) in edges.clone() {
        budget.claim_work(1)?;
        validate_property_id(sub, property_count, "data subproperty")?;
        validate_property_id(sup, property_count, "data superproperty")?;
        push_u32(
            &mut outgoing[usize_id(sub)?],
            sup,
            "outgoing data adjacency",
            &mut budget,
        )?;
        push_u32(
            &mut incoming[usize_id(sup)?],
            sub,
            "incoming data adjacency",
            &mut budget,
        )?;
    }
    canonicalize_rows(&mut outgoing, &mut budget)?;
    canonicalize_rows(&mut incoming, &mut budget)?;

    let mut visited = zeroed_u8(property_count, "data SCC visited set", &mut budget)?;
    let mut finish = reserved_u32(property_count, "data SCC finish order", &mut budget)?;
    let mut depth = reserved_pairs(property_count, "data SCC depth stack", &mut budget)?;
    for root in 0..property_count {
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
                    EncodedValidationError::resource("data SCC adjacency offset overflowed")
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
    if finish.len() != property_count {
        return Err(EncodedValidationError::invariant(
            "data-property SCC traversal omitted a finish record",
        ));
    }

    let mut assigned = zeroed_u8(property_count, "data SCC assigned set", &mut budget)?;
    let mut pending = reserved_u32(property_count, "data SCC pending stack", &mut budget)?;
    let mut components = empty_rows(property_count, "data-property components", &mut budget)?;
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
            push_u32(&mut members, node, "data-property component", &mut budget)?;
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
            "data-property hierarchy component count exceeds its limit",
        ));
    }
    budget.claim_work(sort_work(components.len()))?;
    components.sort_by_key(|members| members.first().copied().unwrap_or(u32::MAX));
    if components.iter().any(Vec::is_empty) {
        return Err(EncodedValidationError::invariant(
            "data-property SCC traversal produced an empty component",
        ));
    }

    let mut component_by_property = filled_u32(
        property_count,
        u32::MAX,
        "data component mapping",
        &mut budget,
    )?;
    for (component_index, members) in components.iter().enumerate() {
        let component_id = u32_id(component_index)?;
        for &property_id in members {
            budget.claim_work(1)?;
            let slot = component_by_property
                .get_mut(usize_id(property_id)?)
                .ok_or_else(|| {
                    EncodedValidationError::invariant("data-property component member is dangling")
                })?;
            if *slot != u32::MAX {
                return Err(EncodedValidationError::invariant(
                    "data property occurs in multiple SCCs",
                ));
            }
            *slot = component_id;
        }
    }
    if component_by_property.contains(&u32::MAX) {
        return Err(EncodedValidationError::invariant(
            "data-property SCC decomposition omitted a property",
        ));
    }

    let component_count = components.len();
    let mut quotient_edges = Vec::new();
    for (sub, sup) in edges {
        budget.claim_work(1)?;
        let sub_component = component_by_property[usize_id(sub)?];
        let super_component = component_by_property[usize_id(sup)?];
        if sub_component != super_component {
            push_pair(
                &mut quotient_edges,
                (sub_component, super_component),
                "data-property quotient edge",
                &mut budget,
            )?;
        }
    }
    budget.claim_work(sort_work(quotient_edges.len()))?;
    quotient_edges.sort_unstable();
    quotient_edges.dedup();

    let mut quotient = empty_rows(
        component_count,
        "data-property quotient adjacency",
        &mut budget,
    )?;
    let mut indegree = filled_u32(
        component_count,
        0,
        "data-property quotient indegree",
        &mut budget,
    )?;
    for &(sub, sup) in &quotient_edges {
        push_u32(
            &mut quotient[usize_id(sub)?],
            sup,
            "data-property quotient adjacency",
            &mut budget,
        )?;
        let degree = indegree.get_mut(usize_id(sup)?).ok_or_else(|| {
            EncodedValidationError::invariant("data-property quotient target is dangling")
        })?;
        *degree = degree.checked_add(1).ok_or_else(|| {
            EncodedValidationError::resource("data-property quotient indegree overflowed")
        })?;
    }

    let mut ready = BinaryHeap::new();
    budget.claim_owned(
        component_count
            .checked_mul(size_of::<Reverse<u32>>())
            .ok_or_else(|| {
                EncodedValidationError::resource("data-property topological heap overflowed")
            })?,
    )?;
    ready.try_reserve(component_count).map_err(|_| {
        EncodedValidationError::resource("data-property topological heap allocation failed")
    })?;
    for (component, degree) in indegree.iter().copied().enumerate() {
        if degree == 0 {
            ready.push(Reverse(u32_id(component)?));
        }
    }
    let mut order = reserved_u32(
        component_count,
        "data-property topological order",
        &mut budget,
    )?;
    while let Some(Reverse(component)) = ready.pop() {
        budget.claim_work(1)?;
        order.push(component);
        for &successor in &quotient[usize_id(component)?] {
            let degree = indegree.get_mut(usize_id(successor)?).ok_or_else(|| {
                EncodedValidationError::invariant("data-property quotient successor is dangling")
            })?;
            *degree = degree.checked_sub(1).ok_or_else(|| {
                EncodedValidationError::invariant("data-property quotient indegree underflowed")
            })?;
            if *degree == 0 {
                ready.push(Reverse(successor));
            }
        }
    }
    if order.len() != component_count {
        return Err(EncodedValidationError::invariant(
            "data-property quotient graph contains a cycle",
        ));
    }

    let mut closure = empty_reachability(component_count, &mut budget)?;
    let mut markers = filled_u32(
        component_count,
        0,
        "data-property closure markers",
        &mut budget,
    )?;
    let mut touched = reserved_u32(
        component_count,
        "data-property closure accumulator",
        &mut budget,
    )?;
    for (epoch_index, &component) in order.iter().rev().enumerate() {
        let epoch = u32_id(epoch_index.checked_add(1).ok_or_else(|| {
            EncodedValidationError::resource("data-property closure epoch overflowed")
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

    let top_component_id = component_by_property[usize_id(top_property_id)?];
    let bottom_component_id = component_by_property[usize_id(bottom_property_id)?];
    let phase = DataRoleHierarchyPhase {
        data_components: components,
        data_component_by_property: component_by_property,
        data_super_components: closure,
        top_component_id,
        bottom_component_id,
        work: budget.work,
        owned_bytes: budget.owned_bytes,
        manifest_limit: limits.max_manifest_bytes,
    };
    validate_phase_shape(&phase, property_count)?;
    Ok(phase)
}

fn validate_inputs(
    roles: &DataRolePhase,
    inclusions: &DataInclusionPhase,
    limits: DataRoleHierarchyLimits,
) -> EncodedResult<()> {
    if roles.data_property_domain.kind != SymbolKind::DataProperty {
        return Err(EncodedValidationError::invariant(
            "data-property hierarchy received a non-data-property domain",
        ));
    }
    let property_count = roles.data_property_domain.values.len();
    if property_count == 0 || property_count > limits.max_properties {
        return Err(EncodedValidationError::resource(
            "data-property hierarchy property count exceeds its limit",
        ));
    }
    if roles
        .data_property_domain
        .values
        .iter()
        .enumerate()
        .any(|(index, value)| usize::try_from(value.identifier).ok() != Some(index))
    {
        return Err(EncodedValidationError::invariant(
            "data-property hierarchy received a non-dense property domain",
        ));
    }
    if inclusions.data_inclusions.len() > limits.max_inclusions {
        return Err(EncodedValidationError::resource(
            "data-property hierarchy inclusion count exceeds its limit",
        ));
    }
    if inclusions.data_inclusions.windows(2).any(|pair| {
        (pair[0].sub_property_id, pair[0].super_property_id)
            >= (pair[1].sub_property_id, pair[1].super_property_id)
    }) {
        return Err(EncodedValidationError::invariant(
            "data-property hierarchy received non-canonical inclusions",
        ));
    }
    for inclusion in &inclusions.data_inclusions {
        validate_property_id(
            inclusion.sub_property_id,
            property_count,
            "data subproperty",
        )?;
        validate_property_id(
            inclusion.super_property_id,
            property_count,
            "data superproperty",
        )?;
    }
    Ok(())
}

fn validate_phase_shape(
    phase: &DataRoleHierarchyPhase,
    property_count: usize,
) -> EncodedResult<()> {
    let component_count = phase.data_components.len();
    if component_count == 0
        || phase.data_component_by_property.len() != property_count
        || phase.data_super_components.len() != component_count
    {
        return Err(EncodedValidationError::invariant(
            "data-property hierarchy phase has inconsistent dimensions",
        ));
    }
    let mut expected_properties = 0_usize;
    let mut previous_least = None;
    for (component, members) in phase.data_components.iter().enumerate() {
        let Some(&least) = members.first() else {
            return Err(EncodedValidationError::invariant(
                "data-property hierarchy contains an empty component",
            ));
        };
        if previous_least.is_some_and(|value| value >= least)
            || members.windows(2).any(|pair| pair[0] >= pair[1])
        {
            return Err(EncodedValidationError::invariant(
                "data-property hierarchy components are not canonical",
            ));
        }
        previous_least = Some(least);
        for &property_id in members {
            validate_property_id(property_id, property_count, "data component member")?;
            if phase.data_component_by_property[usize_id(property_id)?] != u32_id(component)? {
                return Err(EncodedValidationError::invariant(
                    "data-property component mapping disagrees with its partition",
                ));
            }
            expected_properties = expected_properties.checked_add(1).ok_or_else(|| {
                EncodedValidationError::resource("data-property partition size overflowed")
            })?;
        }
    }
    if expected_properties != property_count {
        return Err(EncodedValidationError::invariant(
            "data-property hierarchy components do not partition the property domain",
        ));
    }
    for (component, reachable) in phase.data_super_components.iter().enumerate() {
        if !reachability_is_canonical(reachable, component_count)
            || !reachable.contains(u32_id(component)?)
        {
            return Err(EncodedValidationError::invariant(
                "data-property super-component closure is not canonical and reflexive",
            ));
        }
    }
    validate_property_id(
        phase.top_component_id,
        component_count,
        "top data-property component",
    )?;
    validate_property_id(
        phase.bottom_component_id,
        component_count,
        "bottom data-property component",
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
                        EncodedValidationError::invariant("data closure bit offset exceeds usize")
                    })?;
                    let member = word_index
                        .checked_mul(64)
                        .and_then(|base| base.checked_add(offset))
                        .and_then(|index| u32::try_from(index).ok())
                        .ok_or_else(|| {
                            EncodedValidationError::resource(
                                "dense data reachability ID overflowed",
                            )
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
        EncodedValidationError::invariant("data-property closure member is dangling")
    })?;
    if *marker != epoch {
        *marker = epoch;
        if touched.len() == touched.capacity() {
            return Err(EncodedValidationError::resource(
                "data-property closure accumulator exceeded its reserved domain",
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
        EncodedValidationError::invariant("data-property closure cannot be empty")
    })?)?;
    let dense_words = maximum
        .checked_div(64)
        .and_then(|value| value.checked_add(1))
        .ok_or_else(|| EncodedValidationError::resource("dense data closure size overflowed"))?;
    let dense_bytes = dense_words
        .checked_mul(size_of::<u64>())
        .ok_or_else(|| EncodedValidationError::resource("dense data closure bytes overflowed"))?;
    let sparse_bytes = members
        .len()
        .checked_mul(size_of::<u32>())
        .ok_or_else(|| EncodedValidationError::resource("sparse data closure bytes overflowed"))?;
    if dense_bytes <= sparse_bytes {
        budget.claim_owned(dense_bytes)?;
        let mut words = Vec::new();
        words.try_reserve_exact(dense_words).map_err(|_| {
            EncodedValidationError::resource("dense data closure allocation failed")
        })?;
        words.resize(dense_words, 0_u64);
        for &member in members {
            let index = usize_id(member)?;
            words[index / 64] |= 1_u64 << (index % 64);
        }
        Ok(ComponentReachability::Dense(words))
    } else {
        budget.claim_owned(sparse_bytes)?;
        let mut values = Vec::new();
        values.try_reserve_exact(members.len()).map_err(|_| {
            EncodedValidationError::resource("sparse data closure allocation failed")
        })?;
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
                EncodedValidationError::resource(
                    "data-property closure outer allocation overflowed",
                )
            })?,
    )?;
    let mut values = Vec::new();
    values.try_reserve_exact(count).map_err(|_| {
        EncodedValidationError::resource("data-property closure outer allocation failed")
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

fn validate_property_id(value: u32, count: usize, name: &'static str) -> EncodedResult<()> {
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
        .map_err(|_| EncodedValidationError::resource("data-property graph ID exceeds usize"))
}

fn u32_id(value: usize) -> EncodedResult<u32> {
    u32::try_from(value)
        .map_err(|_| EncodedValidationError::resource("data-property graph ID exceeds u32"))
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
    fn sccs_and_transitive_closure_are_canonical() -> EncodedResult<()> {
        let phase = build_hierarchy(
            7,
            5,
            6,
            [(0, 1), (1, 2), (2, 1), (2, 3), (3, 4)].into_iter(),
            DataRoleHierarchyLimits::default(),
        )?;
        assert_eq!(
            phase.data_components,
            vec![vec![0], vec![1, 2], vec![3], vec![4], vec![5], vec![6]]
        );
        assert!(phase.data_super_components[0].contains(3));
        assert!(!phase.data_super_components[3].contains(0));
        assert_eq!(phase.top_component_id, 4);
        assert_eq!(phase.bottom_component_id, 5);
        Ok(())
    }

    #[test]
    fn edgeless_properties_remain_distinct_with_reflexive_closure() -> EncodedResult<()> {
        let phase = build_hierarchy(3, 1, 2, [].into_iter(), DataRoleHierarchyLimits::default())?;
        assert_eq!(phase.data_components, vec![vec![0], vec![1], vec![2]]);
        assert_eq!(
            phase.data_super_components,
            vec![
                ComponentReachability::Sparse(vec![0]),
                ComponentReachability::Sparse(vec![1]),
                ComponentReachability::Sparse(vec![2]),
            ]
        );
        Ok(())
    }

    #[test]
    fn resource_limits_fail_before_publishing_and_retry_is_exact() -> EncodedResult<()> {
        let edges = [(0, 1), (1, 2)];
        let baseline = build_hierarchy(
            3,
            1,
            2,
            edges.into_iter(),
            DataRoleHierarchyLimits::default(),
        )?;
        let baseline_manifest = baseline.canonical_manifest_json()?;

        let Err(error) = build_hierarchy(
            3,
            1,
            2,
            edges.into_iter(),
            DataRoleHierarchyLimits {
                max_inclusions: 1,
                ..DataRoleHierarchyLimits::default()
            },
        ) else {
            return Err(EncodedValidationError::invariant(
                "the inclusion limit accepted a data hierarchy",
            ));
        };
        assert_eq!(error.code, "NATIVE_ENCODED_RESOURCE_LIMIT");

        let Err(error) = build_hierarchy(
            3,
            1,
            2,
            edges.into_iter(),
            DataRoleHierarchyLimits {
                max_work: 0,
                ..DataRoleHierarchyLimits::default()
            },
        ) else {
            return Err(EncodedValidationError::invariant(
                "the work limit accepted a data hierarchy",
            ));
        };
        assert_eq!(error.code, "NATIVE_ENCODED_RESOURCE_LIMIT");

        let Err(error) = build_hierarchy(
            3,
            1,
            2,
            edges.into_iter(),
            DataRoleHierarchyLimits {
                max_owned_bytes: 0,
                ..DataRoleHierarchyLimits::default()
            },
        ) else {
            return Err(EncodedValidationError::invariant(
                "the ownership limit accepted a data hierarchy",
            ));
        };
        assert_eq!(error.code, "NATIVE_ENCODED_RESOURCE_LIMIT");

        let limited = DataRoleHierarchyPhase {
            manifest_limit: 1,
            ..baseline
        };
        let Err(error) = limited.canonical_manifest_json() else {
            return Err(EncodedValidationError::invariant(
                "the manifest limit accepted a data hierarchy",
            ));
        };
        assert_eq!(error.code, "NATIVE_ENCODED_RESOURCE_LIMIT");

        let retry = build_hierarchy(
            3,
            1,
            2,
            edges.into_iter(),
            DataRoleHierarchyLimits::default(),
        )?;
        assert_eq!(retry.canonical_manifest_json()?, baseline_manifest);
        Ok(())
    }
}
