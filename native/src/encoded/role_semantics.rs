//! Deterministic object-role regularity and non-simplicity analysis.
//!
//! This phase consumes the canonical object-role signature, simple hierarchy,
//! and complex inclusions. It preserves the scalar role builder's structured
//! regularity diagnostics and dependency graph, then propagates non-simple
//! status through the quotient super-role closure. Role automata and
//! clausification remain explicit later phases, so this fragment is not a
//! publishable reasoning session.
// SPDX-License-Identifier: LGPL-3.0-or-later

#![forbid(unsafe_code)]

use std::cmp::Ordering;
use std::mem::size_of;

use serde::Serialize;

use super::complex_roles::{ComplexRoleInclusion, ComplexRolePhase};
use super::object_role_hierarchy::{ComponentReachability, ObjectRoleHierarchyPhase};
use super::object_roles::ObjectRolePhase;
use super::simple_roles::SimpleRolePhase;
use super::{EncodedResult, EncodedValidationError};
use crate::input_wire::SymbolKind;

const ROLE_SEMANTICS_SCHEMA_VERSION: u16 = 1;
const RIA_INVERSE_RECURSION: &str = "RIA_INVERSE_RECURSION";
const RIA_NON_REGULAR_RECURSION: &str = "RIA_NON_REGULAR_RECURSION";
const RIA_DEPENDENCY_CYCLE: &str = "RIA_DEPENDENCY_CYCLE";
const INVERSE_RECURSION_MESSAGE: &str =
    "a complex subproperty chain contains the inverse of its super role";
const NON_REGULAR_RECURSION_MESSAGE: &str =
    "the super role occurs outside a legal chain boundary pattern";
const DEPENDENCY_CYCLE_MESSAGE: &str = "complex role inclusions create a strict dependency cycle";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RoleSemanticsPhaseLimits {
    pub max_roles: usize,
    pub max_components: usize,
    pub max_simple_inclusions: usize,
    pub max_complex_inclusions: usize,
    pub max_dependency_edges: usize,
    pub max_violations: usize,
    pub max_owned_bytes: usize,
    pub max_work: u64,
    pub max_manifest_bytes: usize,
}

impl Default for RoleSemanticsPhaseLimits {
    fn default() -> Self {
        Self {
            max_roles: 1_000_000,
            max_components: 1_000_000,
            max_simple_inclusions: 100_000_000,
            max_complex_inclusions: 1_000_000,
            max_dependency_edges: 100_000_000,
            max_violations: 10_000_000,
            max_owned_bytes: 512 * 1024 * 1024,
            max_work: 2_000_000_000,
            max_manifest_bytes: 512 * 1024 * 1024,
        }
    }
}

/// One scalar-compatible OWL 2 object-role regularity diagnostic.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RegularityViolation {
    pub code: &'static str,
    pub message: &'static str,
    pub super_role_id: u32,
    pub chain_role_ids: Vec<u32>,
    pub provenance_sha256: [u8; 32],
    pub position: Option<u32>,
    pub component_cycle: Vec<u32>,
}

/// Owned regularity, dependency, and simplicity output.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RoleSemanticsPhase {
    pub regularity_violations: Vec<RegularityViolation>,
    pub dependencies: Vec<Vec<u32>>,
    pub non_simple_components: Vec<u32>,
    pub work: u64,
    pub owned_bytes: usize,
    role_count: usize,
    component_count: usize,
    manifest_limit: usize,
}

impl RoleSemanticsPhase {
    /// Canonical private manifest used for exact scalar differential checks.
    pub fn canonical_manifest_json(&self) -> EncodedResult<Vec<u8>> {
        validate_output(self)?;
        let regularity_violations = self
            .regularity_violations
            .iter()
            .map(|violation| ViolationManifest {
                code: violation.code,
                message: violation.message,
                super_role_id: violation.super_role_id,
                chain_role_ids: &violation.chain_role_ids,
                provenance_sha256: crate::model::hex(&violation.provenance_sha256),
                position: violation.position,
                component_cycle: &violation.component_cycle,
            })
            .collect();
        let encoded = serde_json::to_vec(&RoleSemanticsManifest {
            schema_version: ROLE_SEMANTICS_SCHEMA_VERSION,
            family: "object_role_semantics",
            regularity_violations,
            dependencies: &self.dependencies,
            non_simple_components: &self.non_simple_components,
        })
        .map_err(|_| {
            EncodedValidationError::invariant("object-role semantics manifest serialization failed")
        })?;
        if encoded.len() > self.manifest_limit {
            return Err(EncodedValidationError::resource(
                "object-role semantics manifest exceeds its byte limit",
            ));
        }
        Ok(encoded)
    }
}

#[derive(Serialize)]
struct RoleSemanticsManifest<'a> {
    schema_version: u16,
    family: &'static str,
    regularity_violations: Vec<ViolationManifest<'a>>,
    dependencies: &'a [Vec<u32>],
    non_simple_components: &'a [u32],
}

#[derive(Serialize)]
struct ViolationManifest<'a> {
    code: &'static str,
    message: &'static str,
    super_role_id: u32,
    chain_role_ids: &'a [u32],
    provenance_sha256: String,
    position: Option<u32>,
    component_cycle: &'a [u32],
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct DependencyEdge {
    dependency: u32,
    consumer: u32,
    source_index: Option<usize>,
}

type ComponentRows = Vec<Vec<u32>>;

struct PhaseBudget {
    limits: RoleSemanticsPhaseLimits,
    work: u64,
    owned_bytes: usize,
}

impl PhaseBudget {
    const fn new(limits: RoleSemanticsPhaseLimits) -> Self {
        Self {
            limits,
            work: 0,
            owned_bytes: 0,
        }
    }

    fn claim_work(&mut self, amount: usize) -> EncodedResult<()> {
        let amount = u64::try_from(amount)
            .map_err(|_| EncodedValidationError::resource("role-semantics work exceeds u64"))?;
        let following = self
            .work
            .checked_add(amount)
            .ok_or_else(|| EncodedValidationError::resource("role-semantics work overflowed"))?;
        if following > self.limits.max_work {
            return Err(EncodedValidationError::resource(
                "role-semantics compilation exceeds its work limit",
            ));
        }
        self.work = following;
        Ok(())
    }

    fn claim_owned(&mut self, amount: usize) -> EncodedResult<()> {
        let following = self.owned_bytes.checked_add(amount).ok_or_else(|| {
            EncodedValidationError::resource("role-semantics owned-byte count overflowed")
        })?;
        if following > self.limits.max_owned_bytes {
            return Err(EncodedValidationError::resource(
                "role-semantics compilation exceeds its owned-byte limit",
            ));
        }
        self.owned_bytes = following;
        Ok(())
    }
}

/// Compute scalar-compatible role regularity, dependencies, and simplicity.
pub fn compile_role_semantics_phase(
    roles: &ObjectRolePhase,
    simple: &SimpleRolePhase,
    complex: &ComplexRolePhase,
    hierarchy: &ObjectRoleHierarchyPhase,
    limits: RoleSemanticsPhaseLimits,
) -> EncodedResult<RoleSemanticsPhase> {
    validate_inputs(roles, simple, complex, hierarchy, limits)?;
    let role_count = roles.object_role_domain.values.len();
    let component_count = hierarchy.object_components.len();
    let mut budget = PhaseBudget::new(limits);
    let mut violations = Vec::new();
    let maximum_raw_edges = simple
        .simple_inclusions
        .len()
        .checked_add(complex_chain_item_count(complex)?)
        .ok_or_else(|| EncodedValidationError::resource("role dependency edge count overflowed"))?;
    if maximum_raw_edges > limits.max_dependency_edges {
        return Err(EncodedValidationError::resource(
            "role dependency edge count exceeds its limit",
        ));
    }
    let mut edges = reserved_edges(maximum_raw_edges, &mut budget)?;

    for inclusion in &simple.simple_inclusions {
        budget.claim_work(1)?;
        let dependency = hierarchy.object_component_by_role[usize_id(inclusion.sub_role_id)?];
        let consumer = hierarchy.object_component_by_role[usize_id(inclusion.super_role_id)?];
        if dependency != consumer {
            edges.push(DependencyEdge {
                dependency,
                consumer,
                source_index: None,
            });
        }
    }

    for (source_index, inclusion) in complex.complex_inclusions.iter().enumerate() {
        budget.claim_work(1)?;
        if inclusion.super_role_id == roles.top_object_role_id {
            continue;
        }
        let target = hierarchy.object_component_by_role[usize_id(inclusion.super_role_id)?];
        let inverse_role = roles.inverse_role_ids[usize_id(inclusion.super_role_id)?];
        let inverse_target = hierarchy.object_component_by_role[usize_id(inverse_role)?];
        let mut target_positions = Vec::new();
        budget.claim_owned(
            inclusion
                .chain_role_ids
                .len()
                .checked_mul(size_of::<u32>())
                .ok_or_else(|| {
                    EncodedValidationError::resource(
                        "regularity target-position allocation overflowed",
                    )
                })?,
        )?;
        target_positions
            .try_reserve_exact(inclusion.chain_role_ids.len())
            .map_err(|_| {
                EncodedValidationError::resource("regularity target-position allocation failed")
            })?;
        for (position, role_id) in inclusion.chain_role_ids.iter().copied().enumerate() {
            budget.claim_work(1)?;
            let component = hierarchy.object_component_by_role[usize_id(role_id)?];
            if component == target {
                target_positions.push(u32_id(position)?);
            }
            if component == inverse_target && inverse_target != target {
                push_violation(
                    &mut violations,
                    RIA_INVERSE_RECURSION,
                    INVERSE_RECURSION_MESSAGE,
                    inclusion,
                    Some(u32_id(position)?),
                    &[],
                    &mut budget,
                )?;
            }
            if component != target {
                edges.push(DependencyEdge {
                    dependency: component,
                    consumer: target,
                    source_index: Some(source_index),
                });
            }
        }
        if !valid_recursive_positions(&target_positions, inclusion.chain_role_ids.len()) {
            push_violation(
                &mut violations,
                RIA_NON_REGULAR_RECURSION,
                NON_REGULAR_RECURSION_MESSAGE,
                inclusion,
                target_positions.first().copied(),
                &[],
                &mut budget,
            )?;
        }
    }

    budget.claim_work(sort_work(edges.len()))?;
    edges.sort_unstable_by(|left, right| {
        (left.dependency, left.consumer, left.source_index).cmp(&(
            right.dependency,
            right.consumer,
            right.source_index,
        ))
    });
    let canonical_edges = canonicalize_edges(&edges, limits.max_dependency_edges, &mut budget)?;
    let (dependencies, adjacency) =
        dependency_rows(component_count, &canonical_edges, &mut budget)?;

    if let Some(cycle) = shortest_cycle(&adjacency, &mut budget)? {
        let source_index = cycle
            .windows(2)
            .find_map(|pair| edge_source(&canonical_edges, pair[0], pair[1]))
            .or_else(|| (!complex.complex_inclusions.is_empty()).then_some(0));
        if let Some(source_index) = source_index {
            let source = complex
                .complex_inclusions
                .get(source_index)
                .ok_or_else(|| {
                    EncodedValidationError::invariant("regularity cycle source is dangling")
                })?;
            push_violation(
                &mut violations,
                RIA_DEPENDENCY_CYCLE,
                DEPENDENCY_CYCLE_MESSAGE,
                source,
                None,
                &cycle,
                &mut budget,
            )?;
        }
    }
    canonicalize_violations(&mut violations, &mut budget)?;

    let non_simple =
        compile_non_simple_components(roles, complex, hierarchy, component_count, &mut budget)?;
    let phase = RoleSemanticsPhase {
        regularity_violations: violations,
        dependencies,
        non_simple_components: non_simple,
        work: budget.work,
        owned_bytes: budget.owned_bytes,
        role_count,
        component_count,
        manifest_limit: limits.max_manifest_bytes,
    };
    validate_output_for_domain(&phase, role_count, component_count)?;
    Ok(phase)
}

fn valid_recursive_positions(positions: &[u32], chain_length: usize) -> bool {
    positions.is_empty()
        || positions == [0]
        || positions == [u32::try_from(chain_length.saturating_sub(1)).unwrap_or(u32::MAX)]
        || (chain_length == 2 && positions == [0, 1])
}

fn complex_chain_item_count(complex: &ComplexRolePhase) -> EncodedResult<usize> {
    complex
        .complex_inclusions
        .iter()
        .try_fold(0_usize, |total, inclusion| {
            total
                .checked_add(inclusion.chain_role_ids.len())
                .ok_or_else(|| {
                    EncodedValidationError::resource("complex role chain item count overflowed")
                })
        })
}

fn canonicalize_edges(
    edges: &[DependencyEdge],
    maximum: usize,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<DependencyEdge>> {
    let mut canonical = reserved_edges(edges.len(), budget)?;
    let mut offset = 0_usize;
    while offset < edges.len() {
        budget.claim_work(1)?;
        let dependency = edges[offset].dependency;
        let consumer = edges[offset].consumer;
        let mut source_index = edges[offset].source_index;
        offset = offset
            .checked_add(1)
            .ok_or_else(|| EncodedValidationError::resource("role dependency offset overflowed"))?;
        while offset < edges.len()
            && (edges[offset].dependency, edges[offset].consumer) == (dependency, consumer)
        {
            budget.claim_work(1)?;
            if let Some(candidate) = edges[offset].source_index {
                source_index = Some(source_index.map_or(candidate, |known| known.min(candidate)));
            }
            offset = offset.checked_add(1).ok_or_else(|| {
                EncodedValidationError::resource("role dependency offset overflowed")
            })?;
        }
        canonical.push(DependencyEdge {
            dependency,
            consumer,
            source_index,
        });
        if canonical.len() > maximum {
            return Err(EncodedValidationError::resource(
                "role dependency edge count exceeds its limit",
            ));
        }
    }
    Ok(canonical)
}

fn dependency_rows(
    component_count: usize,
    edges: &[DependencyEdge],
    budget: &mut PhaseBudget,
) -> EncodedResult<(ComponentRows, ComponentRows)> {
    let mut dependencies = empty_rows(component_count, "role dependency rows", budget)?;
    let mut adjacency = empty_rows(component_count, "role cycle adjacency", budget)?;
    for edge in edges {
        budget.claim_work(1)?;
        push_u32(
            &mut dependencies[usize_id(edge.consumer)?],
            edge.dependency,
            "role dependency row",
            budget,
        )?;
        push_u32(
            &mut adjacency[usize_id(edge.dependency)?],
            edge.consumer,
            "role cycle adjacency row",
            budget,
        )?;
    }
    for row in &mut dependencies {
        budget.claim_work(sort_work(row.len()))?;
        row.sort_unstable();
        row.dedup();
    }
    for row in &mut adjacency {
        budget.claim_work(sort_work(row.len()))?;
        row.sort_unstable();
        row.dedup();
    }
    Ok((dependencies, adjacency))
}

fn shortest_cycle(
    adjacency: &[Vec<u32>],
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<Vec<u32>>> {
    let component_count = adjacency.len();
    let mut seen = filled_u32(component_count, u32::MAX, "cycle seen epochs", budget)?;
    let mut parents = filled_u32(component_count, u32::MAX, "cycle parent map", budget)?;
    let mut queue = reserved_u32(component_count, "cycle BFS queue", budget)?;
    let mut best: Option<Vec<u32>> = None;
    for start in 0..component_count {
        budget.claim_work(1)?;
        let epoch = u32_id(start)?;
        queue.clear();
        queue.push(epoch);
        seen[start] = epoch;
        parents[start] = u32::MAX;
        let mut offset = 0_usize;
        let mut found = None;
        while offset < queue.len() && found.is_none() {
            budget.claim_work(1)?;
            let node = queue[offset];
            offset = offset
                .checked_add(1)
                .ok_or_else(|| EncodedValidationError::resource("cycle BFS offset overflowed"))?;
            for &successor in &adjacency[usize_id(node)?] {
                budget.claim_work(1)?;
                if successor == epoch {
                    found = Some(node);
                    break;
                }
                let successor_index = usize_id(successor)?;
                if seen[successor_index] != epoch {
                    seen[successor_index] = epoch;
                    parents[successor_index] = node;
                    if queue.len() == queue.capacity() {
                        return Err(EncodedValidationError::resource(
                            "cycle BFS queue exceeded its component domain",
                        ));
                    }
                    queue.push(successor);
                }
            }
        }
        if let Some(last) = found {
            let candidate = reconstruct_cycle(epoch, last, &parents, budget)?;
            if best.as_ref().is_none_or(|known| {
                (candidate.len(), candidate.as_slice()) < (known.len(), known.as_slice())
            }) {
                best = Some(candidate);
            }
        }
    }
    Ok(best)
}

fn reconstruct_cycle(
    start: u32,
    mut last: u32,
    parents: &[u32],
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<u32>> {
    let mut reverse = Vec::new();
    loop {
        push_u32(&mut reverse, last, "cycle witness", budget)?;
        if last == start {
            break;
        }
        last = *parents
            .get(usize_id(last)?)
            .ok_or_else(|| EncodedValidationError::invariant("cycle witness parent is dangling"))?;
        if last == u32::MAX {
            return Err(EncodedValidationError::invariant(
                "cycle witness parent chain is incomplete",
            ));
        }
    }
    budget.claim_work(reverse.len())?;
    reverse.reverse();
    push_u32(&mut reverse, start, "cycle witness", budget)?;
    Ok(reverse)
}

fn edge_source(edges: &[DependencyEdge], dependency: u32, consumer: u32) -> Option<usize> {
    edges
        .binary_search_by_key(&(dependency, consumer), |edge| {
            (edge.dependency, edge.consumer)
        })
        .ok()
        .and_then(|index| edges[index].source_index)
}

fn compile_non_simple_components(
    roles: &ObjectRolePhase,
    complex: &ComplexRolePhase,
    hierarchy: &ObjectRoleHierarchyPhase,
    component_count: usize,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<u32>> {
    let mut seeds = filled_u8(component_count, 0, "non-simple seed set", budget)?;
    seeds[usize_id(hierarchy.top_component_id)?] = 1;
    seeds[usize_id(hierarchy.bottom_component_id)?] = 1;
    for inclusion in &complex.complex_inclusions {
        budget.claim_work(1)?;
        let component = hierarchy.object_component_by_role[usize_id(inclusion.super_role_id)?];
        seeds[usize_id(component)?] = 1;
    }
    let mut marked = filled_u8(component_count, 0, "non-simple component set", budget)?;
    for (seed, selected) in seeds.iter().copied().enumerate() {
        if selected == 0 {
            continue;
        }
        let closure = hierarchy.object_super_components.get(seed).ok_or_else(|| {
            EncodedValidationError::invariant("non-simple seed closure is dangling")
        })?;
        visit_reachability(closure, component_count, |member| {
            budget.claim_work(1)?;
            marked[usize_id(member)?] = 1;
            Ok(())
        })?;
    }
    let count = marked.iter().filter(|value| **value != 0).count();
    let mut result = reserved_u32(count, "non-simple components", budget)?;
    for (component, selected) in marked.into_iter().enumerate() {
        budget.claim_work(1)?;
        if selected != 0 {
            result.push(u32_id(component)?);
        }
    }
    let top_component = hierarchy.object_component_by_role[usize_id(roles.top_object_role_id)?];
    let bottom_component =
        hierarchy.object_component_by_role[usize_id(roles.bottom_object_role_id)?];
    if result.binary_search(&top_component).is_err()
        || result.binary_search(&bottom_component).is_err()
    {
        return Err(EncodedValidationError::invariant(
            "built-in object roles lost non-simple status",
        ));
    }
    Ok(result)
}

fn visit_reachability(
    value: &ComponentReachability,
    component_count: usize,
    mut visitor: impl FnMut(u32) -> EncodedResult<()>,
) -> EncodedResult<()> {
    match value {
        ComponentReachability::Sparse(values) => {
            for &member in values {
                validate_id(member, component_count, "super-role component")?;
                visitor(member)?;
            }
        }
        ComponentReachability::Dense(words) => {
            for (word_index, word) in words.iter().copied().enumerate() {
                let mut remaining = word;
                while remaining != 0 {
                    let offset = usize::try_from(remaining.trailing_zeros()).map_err(|_| {
                        EncodedValidationError::invariant("dense reachability offset exceeds usize")
                    })?;
                    let member = word_index
                        .checked_mul(64)
                        .and_then(|base| base.checked_add(offset))
                        .ok_or_else(|| {
                            EncodedValidationError::resource("dense reachability member overflowed")
                        })?;
                    if member >= component_count {
                        return Err(EncodedValidationError::invariant(
                            "dense super-role closure contains a dangling component",
                        ));
                    }
                    visitor(u32_id(member)?)?;
                    remaining &= remaining - 1;
                }
            }
        }
    }
    Ok(())
}

fn push_violation(
    target: &mut Vec<RegularityViolation>,
    code: &'static str,
    message: &'static str,
    inclusion: &ComplexRoleInclusion,
    position: Option<u32>,
    component_cycle: &[u32],
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    if target.len() >= budget.limits.max_violations {
        return Err(EncodedValidationError::resource(
            "role regularity violation count exceeds its limit",
        ));
    }
    budget.claim_owned(size_of::<RegularityViolation>())?;
    target.try_reserve(1).map_err(|_| {
        EncodedValidationError::resource("role regularity violation allocation failed")
    })?;
    target.push(RegularityViolation {
        code,
        message,
        super_role_id: inclusion.super_role_id,
        chain_role_ids: clone_u32(&inclusion.chain_role_ids, "regularity chain", budget)?,
        provenance_sha256: inclusion.provenance_sha256,
        position,
        component_cycle: clone_u32(component_cycle, "regularity component cycle", budget)?,
    });
    Ok(())
}

fn canonicalize_violations(
    violations: &mut Vec<RegularityViolation>,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    budget.claim_work(sort_work(violations.len()))?;
    violations.sort_by(compare_violation);
    violations.dedup();
    Ok(())
}

fn compare_violation(left: &RegularityViolation, right: &RegularityViolation) -> Ordering {
    (
        left.code,
        left.super_role_id,
        left.chain_role_ids.as_slice(),
        left.position.map_or(-1_i64, i64::from),
        left.provenance_sha256,
    )
        .cmp(&(
            right.code,
            right.super_role_id,
            right.chain_role_ids.as_slice(),
            right.position.map_or(-1_i64, i64::from),
            right.provenance_sha256,
        ))
}

fn validate_inputs(
    roles: &ObjectRolePhase,
    simple: &SimpleRolePhase,
    complex: &ComplexRolePhase,
    hierarchy: &ObjectRoleHierarchyPhase,
    limits: RoleSemanticsPhaseLimits,
) -> EncodedResult<()> {
    let role_count = roles.object_role_domain.values.len();
    let component_count = hierarchy.object_components.len();
    if roles.object_role_domain.kind != SymbolKind::ObjectRole
        || roles.inverse_role_ids.len() != role_count
    {
        return Err(EncodedValidationError::invariant(
            "role-semantics role domain has an invalid shape",
        ));
    }
    if role_count == 0 || role_count > limits.max_roles {
        return Err(EncodedValidationError::resource(
            "role-semantics role domain exceeds its limit",
        ));
    }
    if component_count == 0 {
        return Err(EncodedValidationError::invariant(
            "role-semantics component domain is empty",
        ));
    }
    if component_count > limits.max_components {
        return Err(EncodedValidationError::resource(
            "role-semantics component domain exceeds its limit",
        ));
    }
    if simple.simple_inclusions.len() > limits.max_simple_inclusions
        || complex.complex_inclusions.len() > limits.max_complex_inclusions
    {
        return Err(EncodedValidationError::resource(
            "role-semantics inclusion count exceeds its limit",
        ));
    }
    validate_id(roles.top_object_role_id, role_count, "top object role")?;
    validate_id(
        roles.bottom_object_role_id,
        role_count,
        "bottom object role",
    )?;
    for (index, role) in roles.object_role_domain.values.iter().enumerate() {
        if usize::try_from(role.identifier).ok() != Some(index)
            || (index > 0 && roles.object_role_domain.values[index - 1].key >= role.key)
        {
            return Err(EncodedValidationError::invariant(
                "role-semantics role domain is not dense and canonical",
            ));
        }
        let inverse = *roles.inverse_role_ids.get(index).ok_or_else(|| {
            EncodedValidationError::invariant("role-semantics inverse mapping is incomplete")
        })?;
        validate_id(inverse, role_count, "inverse object role")?;
        if roles.inverse_role_ids.get(usize_id(inverse)?).copied() != Some(u32_id(index)?) {
            return Err(EncodedValidationError::invariant(
                "role-semantics inverse mapping is not involutive",
            ));
        }
    }
    if hierarchy.object_component_by_role.len() != role_count
        || hierarchy.object_super_components.len() != component_count
        || hierarchy.inverse_component_ids.len() != component_count
    {
        return Err(EncodedValidationError::invariant(
            "role-semantics hierarchy dimensions are inconsistent",
        ));
    }
    for &component in &hierarchy.object_component_by_role {
        validate_id(component, component_count, "object-role component")?;
    }
    if hierarchy.object_component_by_role[usize_id(roles.top_object_role_id)?]
        != hierarchy.top_component_id
        || hierarchy.object_component_by_role[usize_id(roles.bottom_object_role_id)?]
            != hierarchy.bottom_component_id
    {
        return Err(EncodedValidationError::invariant(
            "role-semantics built-in components disagree with the role domain",
        ));
    }
    for inclusion in &simple.simple_inclusions {
        validate_id(inclusion.sub_role_id, role_count, "simple sub-role")?;
        validate_id(inclusion.super_role_id, role_count, "simple super-role")?;
    }
    if simple.simple_inclusions.windows(2).any(|pair| {
        (pair[0].sub_role_id, pair[0].super_role_id) >= (pair[1].sub_role_id, pair[1].super_role_id)
    }) {
        return Err(EncodedValidationError::invariant(
            "role-semantics simple inclusions are not canonical",
        ));
    }
    for inclusion in &complex.complex_inclusions {
        validate_id(inclusion.super_role_id, role_count, "complex super-role")?;
        if inclusion.chain_role_ids.len() < 2 {
            return Err(EncodedValidationError::invariant(
                "role-semantics complex inclusion has a short chain",
            ));
        }
        for &role_id in &inclusion.chain_role_ids {
            validate_id(role_id, role_count, "complex chain role")?;
        }
    }
    if complex.complex_inclusions.windows(2).any(|pair| {
        (
            pair[0].super_role_id,
            pair[0].chain_role_ids.as_slice(),
            pair[0].inverse_generated,
        ) >= (
            pair[1].super_role_id,
            pair[1].chain_role_ids.as_slice(),
            pair[1].inverse_generated,
        )
    }) {
        return Err(EncodedValidationError::invariant(
            "role-semantics complex inclusions are not canonical",
        ));
    }
    Ok(())
}

fn validate_output(phase: &RoleSemanticsPhase) -> EncodedResult<()> {
    validate_output_for_domain(phase, phase.role_count, phase.component_count)
}

fn validate_output_for_domain(
    phase: &RoleSemanticsPhase,
    role_count: usize,
    component_count: usize,
) -> EncodedResult<()> {
    if phase.dependencies.len() != component_count {
        return Err(EncodedValidationError::invariant(
            "role-semantics dependency rows have the wrong length",
        ));
    }
    for row in &phase.dependencies {
        if row.windows(2).any(|pair| pair[0] >= pair[1]) {
            return Err(EncodedValidationError::invariant(
                "role-semantics dependency row is not canonical",
            ));
        }
        for &component in row {
            validate_id(component, component_count, "role dependency")?;
        }
    }
    if phase
        .non_simple_components
        .windows(2)
        .any(|pair| pair[0] >= pair[1])
    {
        return Err(EncodedValidationError::invariant(
            "non-simple role components are not canonical",
        ));
    }
    for &component in &phase.non_simple_components {
        validate_id(component, component_count, "non-simple role component")?;
    }
    if phase
        .regularity_violations
        .windows(2)
        .any(|pair| compare_violation(&pair[0], &pair[1]) != Ordering::Less)
    {
        return Err(EncodedValidationError::invariant(
            "role regularity violations are not canonical",
        ));
    }
    for violation in &phase.regularity_violations {
        if !matches!(
            (violation.code, violation.message),
            (RIA_INVERSE_RECURSION, INVERSE_RECURSION_MESSAGE)
                | (RIA_NON_REGULAR_RECURSION, NON_REGULAR_RECURSION_MESSAGE)
                | (RIA_DEPENDENCY_CYCLE, DEPENDENCY_CYCLE_MESSAGE)
        ) {
            return Err(EncodedValidationError::invariant(
                "role regularity violation has an unknown code or message",
            ));
        }
        validate_id(violation.super_role_id, role_count, "regularity super-role")?;
        if violation.chain_role_ids.len() < 2 {
            return Err(EncodedValidationError::invariant(
                "role regularity violation has a short chain",
            ));
        }
        for &role_id in &violation.chain_role_ids {
            validate_id(role_id, role_count, "regularity chain role")?;
        }
        for &component in &violation.component_cycle {
            validate_id(component, component_count, "regularity component cycle")?;
        }
        if violation.position.is_some_and(|position| {
            !usize::try_from(position).is_ok_and(|value| value < violation.chain_role_ids.len())
        }) {
            return Err(EncodedValidationError::invariant(
                "role regularity violation position is outside its chain",
            ));
        }
        if violation.code == RIA_DEPENDENCY_CYCLE
            && (violation.position.is_some()
                || violation.component_cycle.len() < 2
                || violation.component_cycle.first() != violation.component_cycle.last())
        {
            return Err(EncodedValidationError::invariant(
                "role dependency-cycle violation has an invalid witness",
            ));
        }
        if violation.code != RIA_DEPENDENCY_CYCLE && !violation.component_cycle.is_empty() {
            return Err(EncodedValidationError::invariant(
                "recursive regularity violation unexpectedly has a component cycle",
            ));
        }
        if matches!(
            violation.code,
            RIA_INVERSE_RECURSION | RIA_NON_REGULAR_RECURSION
        ) && violation.position.is_none()
        {
            return Err(EncodedValidationError::invariant(
                "recursive regularity violation lost its chain position",
            ));
        }
    }
    Ok(())
}

fn reserved_edges(count: usize, budget: &mut PhaseBudget) -> EncodedResult<Vec<DependencyEdge>> {
    budget.claim_owned(
        count
            .checked_mul(size_of::<DependencyEdge>())
            .ok_or_else(|| EncodedValidationError::resource("dependency edge bytes overflowed"))?,
    )?;
    let mut values = Vec::new();
    values
        .try_reserve_exact(count)
        .map_err(|_| EncodedValidationError::resource("role dependency edge allocation failed"))?;
    Ok(values)
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

fn clone_u32(
    values: &[u32],
    name: &'static str,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<u32>> {
    let mut result = reserved_u32(values.len(), name, budget)?;
    result.extend_from_slice(values);
    Ok(result)
}

fn filled_u8(
    count: usize,
    value: u8,
    name: &'static str,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<u8>> {
    budget.claim_owned(count)?;
    let mut values = Vec::new();
    values
        .try_reserve_exact(count)
        .map_err(|_| EncodedValidationError::resource(format!("{name} allocation failed")))?;
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

fn validate_id(value: u32, count: usize, name: &'static str) -> EncodedResult<()> {
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
        .map_err(|_| EncodedValidationError::resource("role-semantics ID exceeds usize"))
}

fn u32_id(value: usize) -> EncodedResult<u32> {
    u32::try_from(value)
        .map_err(|_| EncodedValidationError::resource("role-semantics ID exceeds u32"))
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
    use crate::input_wire::{DecodedSymbolDomain, DecodedSymbolValue};

    fn reference_shortest_cycle(adjacency: &[Vec<u32>]) -> Vec<u32> {
        let mut candidates = Vec::new();
        for start in 0..adjacency.len() {
            let start_id = u32::try_from(start).unwrap_or(u32::MAX);
            let mut queue = vec![(start_id, vec![start_id])];
            let mut seen = vec![false; adjacency.len()];
            seen[start] = true;
            let mut offset = 0_usize;
            while offset < queue.len() {
                let (node, path) = queue[offset].clone();
                offset = offset.saturating_add(1);
                for &successor in &adjacency[usize::try_from(node).unwrap_or(usize::MAX)] {
                    if successor == start_id {
                        let mut cycle = path;
                        cycle.push(start_id);
                        candidates.push(cycle);
                        offset = queue.len();
                        break;
                    }
                    let successor_index = usize::try_from(successor).unwrap_or(usize::MAX);
                    if !seen[successor_index] {
                        seen[successor_index] = true;
                        let mut successor_path = path.clone();
                        successor_path.push(successor);
                        queue.push((successor, successor_path));
                    }
                }
            }
        }
        candidates
            .into_iter()
            .min_by(|left, right| {
                (left.len(), left.as_slice()).cmp(&(right.len(), right.as_slice()))
            })
            .unwrap_or_default()
    }

    fn roles() -> ObjectRolePhase {
        ObjectRolePhase {
            object_role_domain: DecodedSymbolDomain {
                kind: SymbolKind::ObjectRole,
                values: (0..6)
                    .map(|identifier| DecodedSymbolValue {
                        identifier,
                        key: vec![u8::try_from(identifier).unwrap_or(u8::MAX)],
                        display: format!("role:{identifier}"),
                        generated: false,
                        query_local: false,
                    })
                    .collect(),
            },
            inverse_role_ids: vec![1, 0, 3, 2, 4, 5],
            top_object_role_id: 4,
            bottom_object_role_id: 5,
            work: 0,
            owned_bytes: 0,
            manifest_limit: 1,
        }
    }

    fn simple(inclusions: &[(u32, u32)]) -> SimpleRolePhase {
        SimpleRolePhase {
            simple_inclusions: inclusions
                .iter()
                .map(|&(sub_role_id, super_role_id)| {
                    super::super::simple_roles::SimpleRoleInclusion {
                        sub_role_id,
                        super_role_id,
                        provenance_sha256: [0; 32],
                        builtin: false,
                    }
                })
                .collect(),
            compiled_roots: 0,
            work: 0,
            owned_bytes: 0,
            compiled_statement_digests: Vec::new(),
            manifest_limit: 1,
        }
    }

    fn complex(inclusions: &[(Vec<u32>, u32, [u8; 32], bool)]) -> ComplexRolePhase {
        ComplexRolePhase {
            complex_inclusions: inclusions
                .iter()
                .map(
                    |(chain_role_ids, super_role_id, provenance_sha256, inverse_generated)| {
                        ComplexRoleInclusion {
                            chain_role_ids: chain_role_ids.clone(),
                            super_role_id: *super_role_id,
                            provenance_sha256: *provenance_sha256,
                            inverse_generated: *inverse_generated,
                            statement_order_key: vec![1],
                            builtin: false,
                        }
                    },
                )
                .collect(),
            compiled_roots: 0,
            work: 0,
            owned_bytes: 0,
            compiled_statement_digests: Vec::new(),
            manifest_limit: 1,
        }
    }

    fn hierarchy(simple: &SimpleRolePhase) -> EncodedResult<ObjectRoleHierarchyPhase> {
        super::super::object_role_hierarchy::compile_object_role_hierarchy_phase(
            &roles(),
            simple,
            super::super::object_role_hierarchy::ObjectRoleHierarchyLimits::default(),
        )
    }

    #[test]
    fn recursion_diagnostics_and_non_simple_propagation_are_exact() -> EncodedResult<()> {
        let roles = roles();
        let simple = simple(&[(0, 2), (1, 3), (2, 4), (3, 4)]);
        let hierarchy = hierarchy(&simple)?;
        let complex = complex(&[(vec![1, 0, 2], 0, [7; 32], false)]);
        let phase = compile_role_semantics_phase(
            &roles,
            &simple,
            &complex,
            &hierarchy,
            RoleSemanticsPhaseLimits::default(),
        )?;
        assert!(phase
            .regularity_violations
            .iter()
            .any(|value| value.code == RIA_INVERSE_RECURSION));
        assert!(phase
            .regularity_violations
            .iter()
            .any(|value| value.code == RIA_NON_REGULAR_RECURSION));
        assert!(phase
            .non_simple_components
            .contains(&hierarchy.top_component_id));
        assert!(phase
            .non_simple_components
            .contains(&hierarchy.bottom_component_id));
        Ok(())
    }

    #[test]
    fn strict_dependency_cycle_uses_shortest_lexicographic_witness() -> EncodedResult<()> {
        let roles = roles();
        let simple = simple(&[]);
        let hierarchy = hierarchy(&simple)?;
        let complex = complex(&[
            (vec![2, 5], 0, [1; 32], false),
            (vec![0, 5], 2, [2; 32], false),
        ]);
        let phase = compile_role_semantics_phase(
            &roles,
            &simple,
            &complex,
            &hierarchy,
            RoleSemanticsPhaseLimits::default(),
        )?;
        let violation = phase
            .regularity_violations
            .iter()
            .find(|value| value.code == RIA_DEPENDENCY_CYCLE)
            .ok_or_else(|| EncodedValidationError::invariant("cycle violation disappeared"))?;
        assert_eq!(
            violation.component_cycle.first(),
            violation.component_cycle.last()
        );
        assert_eq!(violation.component_cycle.len(), 3);
        Ok(())
    }

    #[test]
    fn semantic_limits_fail_closed() -> EncodedResult<()> {
        let roles = roles();
        let simple = simple(&[]);
        let hierarchy = hierarchy(&simple)?;
        let complex = complex(&[(vec![1, 0, 2], 0, [7; 32], false)]);
        let result = compile_role_semantics_phase(
            &roles,
            &simple,
            &complex,
            &hierarchy,
            RoleSemanticsPhaseLimits {
                max_violations: 0,
                ..RoleSemanticsPhaseLimits::default()
            },
        );
        let Err(error) = result else {
            return Err(EncodedValidationError::invariant(
                "zero violation limit unexpectedly succeeded",
            ));
        };
        assert_eq!(error.code, "NATIVE_ENCODED_RESOURCE_LIMIT");
        Ok(())
    }

    #[test]
    fn shortest_cycle_matches_the_scalar_breadth_first_oracle_exhaustively() -> EncodedResult<()> {
        const COMPONENTS: usize = 4;
        let edge_domain: Vec<(usize, u32)> = (0..COMPONENTS)
            .flat_map(|source| {
                (0..COMPONENTS)
                    .filter(move |&target| source != target)
                    .map(move |target| (source, u32::try_from(target).unwrap_or(u32::MAX)))
            })
            .collect();
        for mask in 0_usize..(1_usize << edge_domain.len()) {
            let mut adjacency = vec![Vec::new(); COMPONENTS];
            for (edge, &(source, target)) in edge_domain.iter().enumerate() {
                if mask & (1_usize << edge) != 0 {
                    adjacency[source].push(target);
                }
            }
            let mut budget = PhaseBudget::new(RoleSemanticsPhaseLimits::default());
            let actual = shortest_cycle(&adjacency, &mut budget)?.unwrap_or_default();
            assert_eq!(actual, reference_shortest_cycle(&adjacency));
        }
        Ok(())
    }
}
