//! Provenance-bearing complex object-role inclusion expansion.
//!
//! This phase mirrors the scalar role builder for object property chains,
//! transitivity, inverse-generated chains, and the built-in top-role
//! transitivity production. SCC regularity, non-simplicity propagation,
//! automata, and clausification remain explicit later phases; this owned
//! fragment is not publishable.
// SPDX-License-Identifier: LGPL-3.0-or-later

#![forbid(unsafe_code)]

use std::cmp::Ordering;
use std::mem::size_of;

use serde::Serialize;
use sha2::{Digest, Sha256};

use super::model::{ComponentValue, NodeId, NodeRef, ValidatedModel};
use super::object_roles::ObjectRolePhase;
use super::symbols::{RootHandler, SymbolPhase};
use super::{ByteSource, EncodedResult, EncodedValidationError};
use crate::input_wire::{DecodedSymbolDomain, SymbolKind};

const COMPLEX_ROLE_PHASE_SCHEMA_VERSION: u16 = 1;
const ENTITY_TAG: u16 = 2;
const OBJECT_INVERSE_OF_TAG: u16 = 10;
const OBJECT_PROPERTY_CHAIN_TAG: u16 = 11;
const SUB_OBJECT_PROPERTY_TAG: u16 = 70;
const TRANSITIVE_OBJECT_PROPERTY_TAG: u16 = 82;
const BUILTIN_TOP_TRANSITIVITY_SEED: &[u8] = b"pyhermit:role-model:builtin-top-transitivity:v1";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ComplexRolePhaseLimits {
    pub max_slices: usize,
    pub max_inclusions: usize,
    pub max_compiled_roots: usize,
    pub max_owned_bytes: usize,
    pub max_work: u64,
    pub max_manifest_bytes: usize,
}

impl Default for ComplexRolePhaseLimits {
    fn default() -> Self {
        Self {
            max_slices: 32_769,
            max_inclusions: 1_000_000,
            max_compiled_roots: 10_000_000,
            max_owned_bytes: 512 * 1024 * 1024,
            max_work: 2_000_000_000,
            max_manifest_bytes: 512 * 1024 * 1024,
        }
    }
}

/// One canonical complex role inclusion retained for later regularity/NFA work.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ComplexRoleInclusion {
    pub chain_role_ids: Vec<u32>,
    pub super_role_id: u32,
    pub provenance_sha256: [u8; 32],
    pub inverse_generated: bool,
    pub(super) statement_order_key: Vec<u8>,
    pub(super) builtin: bool,
}

/// Owned output of complex object-role inclusion preprocessing.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ComplexRolePhase {
    pub complex_inclusions: Vec<ComplexRoleInclusion>,
    pub compiled_roots: usize,
    pub work: u64,
    pub owned_bytes: usize,
    pub(super) compiled_statement_digests: Vec<[u8; 32]>,
    pub(super) manifest_limit: usize,
}

impl ComplexRolePhase {
    /// Canonical private manifest used for exact scalar differential checks.
    pub fn canonical_manifest_json(&self) -> EncodedResult<Vec<u8>> {
        validate_phase_shape(self)?;
        let complex_inclusions = self
            .complex_inclusions
            .iter()
            .map(|inclusion| InclusionManifest {
                chain_role_ids: &inclusion.chain_role_ids,
                super_role_id: inclusion.super_role_id,
                provenance_sha256: crate::model::hex(&inclusion.provenance_sha256),
                inverse_generated: inclusion.inverse_generated,
            })
            .collect();
        let encoded = serde_json::to_vec(&ComplexRoleManifest {
            schema_version: COMPLEX_ROLE_PHASE_SCHEMA_VERSION,
            family: "complex_object_role_inclusions",
            compiled_roots: self.compiled_roots,
            complex_inclusions,
        })
        .map_err(|_| {
            EncodedValidationError::invariant("complex-role manifest serialization failed")
        })?;
        if encoded.len() > self.manifest_limit {
            return Err(EncodedValidationError::resource(
                "complex-role manifest exceeds its byte limit",
            ));
        }
        Ok(encoded)
    }
}

#[derive(Serialize)]
struct ComplexRoleManifest<'a> {
    schema_version: u16,
    family: &'static str,
    compiled_roots: usize,
    complex_inclusions: Vec<InclusionManifest<'a>>,
}

#[derive(Serialize)]
struct InclusionManifest<'a> {
    chain_role_ids: &'a [u32],
    super_role_id: u32,
    provenance_sha256: String,
    inverse_generated: bool,
}

#[derive(Debug, Eq, PartialEq)]
struct RawChain {
    chain_role_ids: Vec<u32>,
    super_role_id: u32,
    provenance_sha256: [u8; 32],
    inverse_generated: bool,
    statement_order_key: Vec<u8>,
    builtin: bool,
}

#[derive(Debug, Eq, PartialEq)]
struct RoleExpression {
    role_id: u32,
    structural_key: Vec<u8>,
}

struct PhaseBudget {
    limits: ComplexRolePhaseLimits,
    work: u64,
    owned_bytes: usize,
}

impl PhaseBudget {
    const fn new(limits: ComplexRolePhaseLimits) -> Self {
        Self {
            limits,
            work: 0,
            owned_bytes: 0,
        }
    }

    fn claim_work(&mut self, amount: usize) -> EncodedResult<()> {
        let amount = u64::try_from(amount)
            .map_err(|_| EncodedValidationError::resource("complex-role work exceeds u64"))?;
        let following = self
            .work
            .checked_add(amount)
            .ok_or_else(|| EncodedValidationError::resource("complex-role work overflowed"))?;
        if following > self.limits.max_work {
            return Err(EncodedValidationError::resource(
                "complex-role compilation exceeds its work limit",
            ));
        }
        self.work = following;
        Ok(())
    }

    fn claim_owned(&mut self, amount: usize) -> EncodedResult<()> {
        let following = self.owned_bytes.checked_add(amount).ok_or_else(|| {
            EncodedValidationError::resource("complex-role owned-byte count overflowed")
        })?;
        if following > self.limits.max_owned_bytes {
            return Err(EncodedValidationError::resource(
                "complex-role compilation exceeds its owned-byte limit",
            ));
        }
        self.owned_bytes = following;
        Ok(())
    }

    fn inclusions(&self, count: usize) -> EncodedResult<()> {
        if count > self.limits.max_inclusions {
            Err(EncodedValidationError::resource(
                "complex object-role inclusion count exceeds its limit",
            ))
        } else {
            Ok(())
        }
    }

    fn roots(&self, count: usize) -> EncodedResult<()> {
        if count > self.limits.max_compiled_roots {
            Err(EncodedValidationError::resource(
                "complex object-role compiled-root count exceeds its limit",
            ))
        } else {
            Ok(())
        }
    }
}

/// Expand source complex-role constructors and built-in top transitivity.
pub fn compile_complex_role_phase<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    roles: &ObjectRolePhase,
    limits: ComplexRolePhaseLimits,
) -> EncodedResult<ComplexRolePhase> {
    validate_role_domain(roles)?;
    let mut budget = PhaseBudget::new(limits);
    let mut inclusions = Vec::new();
    let mut compiled_statement_digests = Vec::new();
    for root in &symbols.roots {
        budget.claim_work(1)?;
        let compiled = match root.handler {
            RootHandler::SubObjectPropertyOf => compile_sub_object_property(
                model,
                symbols,
                roles,
                root.node,
                &mut inclusions,
                &mut budget,
            )?,
            RootHandler::TransitiveObjectProperty => Some(compile_transitive_object_property(
                model,
                symbols,
                roles,
                root.node,
                &mut inclusions,
                &mut budget,
            )?),
            _ => None,
        };
        if let Some(digest) = compiled {
            push_digest(
                &mut compiled_statement_digests,
                digest,
                "compiled statement",
                &mut budget,
            )?;
        }
    }
    add_builtin_top_transitivity(roles, &mut inclusions, &mut budget)?;
    freeze_phase(inclusions, compiled_statement_digests, budget)
}

/// Merge source-local complex inclusions through merged canonical role keys.
pub fn merge_complex_role_phases(
    source_roles: &[ObjectRolePhase],
    source_phases: &[ComplexRolePhase],
    merged_roles: &ObjectRolePhase,
    limits: ComplexRolePhaseLimits,
) -> EncodedResult<ComplexRolePhase> {
    if source_phases.is_empty() || source_phases.len() != source_roles.len() {
        return Err(EncodedValidationError::protocol(
            "complex-role program merge requires aligned nonempty slices",
        ));
    }
    if source_phases.len() > limits.max_slices {
        return Err(EncodedValidationError::resource(
            "complex-role slice count exceeds its limit",
        ));
    }
    validate_role_domain(merged_roles)?;
    let mut budget = PhaseBudget::new(limits);
    for phase in source_phases {
        validate_phase_shape(phase)?;
        budget.claim_work(usize::try_from(phase.work).unwrap_or(usize::MAX))?;
        budget.claim_owned(phase.owned_bytes)?;
    }
    let mut inclusions = Vec::new();
    let mut compiled_statement_digests = Vec::new();
    for (roles, phase) in source_roles.iter().zip(source_phases) {
        validate_role_domain(roles)?;
        for inclusion in &phase.complex_inclusions {
            budget.claim_work(1)?;
            let mut chain_role_ids = Vec::new();
            reserve_u32(
                &mut chain_role_ids,
                inclusion.chain_role_ids.len(),
                "merged complex-role chain",
                &mut budget,
            )?;
            for &role_id in &inclusion.chain_role_ids {
                budget.claim_work(1)?;
                chain_role_ids.push(remap_role(roles, merged_roles, role_id, &mut budget)?);
            }
            let super_role_id =
                remap_role(roles, merged_roles, inclusion.super_role_id, &mut budget)?;
            let statement_order_key = clone_bytes(
                &inclusion.statement_order_key,
                "merged complex-role statement key",
                &mut budget,
            )?;
            push_raw(
                &mut inclusions,
                RawChain {
                    chain_role_ids,
                    super_role_id,
                    provenance_sha256: inclusion.provenance_sha256,
                    inverse_generated: inclusion.inverse_generated,
                    statement_order_key,
                    builtin: inclusion.builtin,
                },
                &mut budget,
            )?;
        }
        for digest in &phase.compiled_statement_digests {
            push_digest(
                &mut compiled_statement_digests,
                *digest,
                "merged compiled statement",
                &mut budget,
            )?;
        }
    }
    freeze_phase(inclusions, compiled_statement_digests, budget)
}

fn compile_sub_object_property<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    roles: &ObjectRolePhase,
    root: NodeId,
    inclusions: &mut Vec<RawChain>,
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<[u8; 32]>> {
    let node = require_root(
        model,
        root,
        SUB_OBJECT_PROPERTY_TAG,
        3,
        "sub-object-property",
    )?;
    let sub_node = node_field(model, node, 0, "sub-object-property subproperty")?;
    if model.node(sub_node)?.tag() != OBJECT_PROPERTY_CHAIN_TAG {
        return Ok(None);
    }
    let expressions = role_chain(model, symbols, roles, sub_node, budget)?;
    let sup = role_expression(
        model,
        symbols,
        roles,
        node_field(model, node, 1, "sub-object-property superproperty")?,
        budget,
    )?;
    let chain_key = chain_structural_key(&expressions, budget)?;
    let statement_order_key = node_axiom_key(
        SUB_OBJECT_PROPERTY_TAG,
        &[&chain_key, &sup.structural_key],
        budget,
    )?;
    let provenance_sha256 = statement_digest(&statement_order_key, budget)?;
    let mut chain_role_ids = Vec::new();
    reserve_u32(
        &mut chain_role_ids,
        expressions.len(),
        "complex-role source chain",
        budget,
    )?;
    chain_role_ids.extend(expressions.iter().map(|expression| expression.role_id));
    add_chain(
        roles,
        inclusions,
        chain_role_ids,
        sup.role_id,
        provenance_sha256,
        statement_order_key,
        false,
        budget,
    )?;
    Ok(Some(provenance_sha256))
}

fn compile_transitive_object_property<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    roles: &ObjectRolePhase,
    root: NodeId,
    inclusions: &mut Vec<RawChain>,
    budget: &mut PhaseBudget,
) -> EncodedResult<[u8; 32]> {
    let node = require_root(
        model,
        root,
        TRANSITIVE_OBJECT_PROPERTY_TAG,
        2,
        "transitive-object-property",
    )?;
    let role = role_expression(
        model,
        symbols,
        roles,
        node_field(model, node, 0, "transitive-object-property role")?,
        budget,
    )?;
    let statement_order_key = node_axiom_key(
        TRANSITIVE_OBJECT_PROPERTY_TAG,
        &[&role.structural_key],
        budget,
    )?;
    let provenance_sha256 = statement_digest(&statement_order_key, budget)?;
    let mut chain_role_ids = Vec::new();
    reserve_u32(
        &mut chain_role_ids,
        2,
        "transitive object-role chain",
        budget,
    )?;
    chain_role_ids.extend([role.role_id, role.role_id]);
    add_chain(
        roles,
        inclusions,
        chain_role_ids,
        role.role_id,
        provenance_sha256,
        statement_order_key,
        false,
        budget,
    )?;
    Ok(provenance_sha256)
}

#[allow(clippy::too_many_arguments)]
fn add_chain(
    roles: &ObjectRolePhase,
    target: &mut Vec<RawChain>,
    chain_role_ids: Vec<u32>,
    super_role_id: u32,
    provenance_sha256: [u8; 32],
    statement_order_key: Vec<u8>,
    builtin: bool,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    if chain_role_ids.len() < 2 {
        return Err(EncodedValidationError::invariant(
            "complex object-role chain has fewer than two members",
        ));
    }
    let mut inverse_chain = Vec::new();
    reserve_u32(
        &mut inverse_chain,
        chain_role_ids.len(),
        "inverse-generated complex-role chain",
        budget,
    )?;
    for role_id in chain_role_ids.iter().rev().copied() {
        budget.claim_work(1)?;
        inverse_chain.push(inverse_role_id(roles, role_id)?);
    }
    let inverse_super = inverse_role_id(roles, super_role_id)?;
    let needs_inverse = inverse_chain != chain_role_ids || inverse_super != super_role_id;
    let inverse_statement_key = if needs_inverse {
        Some(clone_bytes(
            &statement_order_key,
            "inverse-generated statement key",
            budget,
        )?)
    } else {
        None
    };
    push_raw(
        target,
        RawChain {
            chain_role_ids,
            super_role_id,
            provenance_sha256,
            inverse_generated: false,
            statement_order_key,
            builtin,
        },
        budget,
    )?;
    if let Some(statement_order_key) = inverse_statement_key {
        push_raw(
            target,
            RawChain {
                chain_role_ids: inverse_chain,
                super_role_id: inverse_super,
                provenance_sha256,
                inverse_generated: true,
                statement_order_key,
                builtin,
            },
            budget,
        )?;
    }
    Ok(())
}

fn add_builtin_top_transitivity(
    roles: &ObjectRolePhase,
    target: &mut Vec<RawChain>,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    let mut chain_role_ids = Vec::new();
    reserve_u32(
        &mut chain_role_ids,
        2,
        "built-in top transitivity chain",
        budget,
    )?;
    chain_role_ids.extend([roles.top_object_role_id, roles.top_object_role_id]);
    add_chain(
        roles,
        target,
        chain_role_ids,
        roles.top_object_role_id,
        Sha256::digest(BUILTIN_TOP_TRANSITIVITY_SEED).into(),
        Vec::new(),
        true,
        budget,
    )
}

fn freeze_phase(
    mut raw: Vec<RawChain>,
    mut compiled_statement_digests: Vec<[u8; 32]>,
    mut budget: PhaseBudget,
) -> EncodedResult<ComplexRolePhase> {
    budget.claim_work(sort_work(raw.len()))?;
    raw.sort_by(compare_raw);
    budget.claim_owned(
        raw.len()
            .checked_mul(size_of::<ComplexRoleInclusion>())
            .ok_or_else(|| {
                EncodedValidationError::resource("complex-role result allocation overflowed")
            })?,
    )?;
    let mut complex_inclusions: Vec<ComplexRoleInclusion> = Vec::new();
    complex_inclusions
        .try_reserve_exact(raw.len())
        .map_err(|_| EncodedValidationError::resource("complex-role result allocation failed"))?;
    for candidate in raw {
        let value = ComplexRoleInclusion {
            chain_role_ids: candidate.chain_role_ids,
            super_role_id: candidate.super_role_id,
            provenance_sha256: candidate.provenance_sha256,
            inverse_generated: candidate.inverse_generated,
            statement_order_key: candidate.statement_order_key,
            builtin: candidate.builtin,
        };
        if complex_inclusions
            .last()
            .is_some_and(|previous| same_semantic_inclusion(previous, &value))
        {
            let last = complex_inclusions.last_mut().ok_or_else(|| {
                EncodedValidationError::invariant("complex-role deduplication lost its last value")
            })?;
            *last = value;
        } else {
            complex_inclusions.push(value);
        }
    }
    budget.inclusions(complex_inclusions.len())?;
    budget.claim_work(sort_work(compiled_statement_digests.len()))?;
    compiled_statement_digests.sort_unstable();
    compiled_statement_digests.dedup();
    budget.roots(compiled_statement_digests.len())?;
    let phase = ComplexRolePhase {
        complex_inclusions,
        compiled_roots: compiled_statement_digests.len(),
        work: budget.work,
        owned_bytes: budget.owned_bytes,
        compiled_statement_digests,
        manifest_limit: budget.limits.max_manifest_bytes,
    };
    validate_phase_shape(&phase)?;
    Ok(phase)
}

fn compare_raw(left: &RawChain, right: &RawChain) -> Ordering {
    left.super_role_id
        .cmp(&right.super_role_id)
        .then_with(|| left.chain_role_ids.cmp(&right.chain_role_ids))
        .then_with(|| left.inverse_generated.cmp(&right.inverse_generated))
        .then_with(|| left.builtin.cmp(&right.builtin))
        .then_with(|| left.statement_order_key.cmp(&right.statement_order_key))
}

fn same_semantic_inclusion(left: &ComplexRoleInclusion, right: &ComplexRoleInclusion) -> bool {
    left.super_role_id == right.super_role_id
        && left.chain_role_ids == right.chain_role_ids
        && left.inverse_generated == right.inverse_generated
}

fn role_chain<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    roles: &ObjectRolePhase,
    identifier: NodeId,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<RoleExpression>> {
    let node = model.node(identifier)?;
    if node.tag() != OBJECT_PROPERTY_CHAIN_TAG || node.field_count() != 1 {
        return Err(EncodedValidationError::invariant(
            "object-property chain no longer has schema-1 shape",
        ));
    }
    let component = required_component(
        model.field(node.fields().start)?,
        "object-property chain members",
    )?;
    let ComponentValue::Collection(collection) = model.resolve(component)? else {
        return Err(EncodedValidationError::invariant(
            "object-property chain members are not a collection",
        ));
    };
    if collection.len() < 2 {
        return Err(EncodedValidationError::invariant(
            "object-property chain has fewer than two members",
        ));
    }
    budget.claim_owned(
        collection
            .len()
            .checked_mul(size_of::<RoleExpression>())
            .ok_or_else(|| {
                EncodedValidationError::resource("object-property chain allocation overflowed")
            })?,
    )?;
    let mut expressions = Vec::new();
    expressions
        .try_reserve_exact(collection.len())
        .map_err(|_| EncodedValidationError::resource("object-property chain allocation failed"))?;
    for item_index in collection.items() {
        budget.claim_work(1)?;
        let item = required_component(model.item(item_index)?, "object-property chain member")?;
        let ComponentValue::Node(role_node) = model.resolve(item)? else {
            return Err(EncodedValidationError::invariant(
                "object-property chain member is not a node",
            ));
        };
        expressions.push(role_expression(model, symbols, roles, role_node, budget)?);
    }
    Ok(expressions)
}

fn role_expression<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    roles: &ObjectRolePhase,
    identifier: NodeId,
    budget: &mut PhaseBudget,
) -> EncodedResult<RoleExpression> {
    let node = model.node(identifier)?;
    if node.tag() == ENTITY_TAG {
        let entity_id = symbols.entity_symbol_for_node(identifier).ok_or_else(|| {
            EncodedValidationError::invariant(
                "object-property expression is absent from the entity seed",
            )
        })?;
        let entity = symbols
            .entity_domain
            .values
            .get(usize::try_from(entity_id).map_err(|_| {
                EncodedValidationError::invariant("object-property entity ID exceeds usize")
            })?)
            .ok_or_else(|| {
                EncodedValidationError::invariant("object-property entity ID is dangling")
            })?;
        if !entity.display.starts_with("object_property:") {
            return Err(EncodedValidationError::invariant(
                "object-property expression resolved to a different entity kind",
            ));
        }
        budget.claim_owned(entity.key.len())?;
        Ok(RoleExpression {
            role_id: role_id_by_key(&roles.object_role_domain, &entity.key, budget)?,
            structural_key: entity.key.clone(),
        })
    } else if node.tag() == OBJECT_INVERSE_OF_TAG {
        if node.field_count() != 1 {
            return Err(EncodedValidationError::invariant(
                "object-inverse expression no longer has schema-1 shape",
            ));
        }
        let property = role_expression(
            model,
            symbols,
            roles,
            node_field(model, node, 0, "object-inverse property")?,
            budget,
        )?;
        Ok(RoleExpression {
            role_id: inverse_role_id(roles, property.role_id)?,
            structural_key: inverse_structural_key(&property.structural_key, budget)?,
        })
    } else {
        Err(EncodedValidationError::invariant(
            "complex role field is not an object-property expression",
        ))
    }
}

fn require_root<B: ByteSource>(
    model: &ValidatedModel<B>,
    root: NodeId,
    tag: u16,
    fields: usize,
    name: &'static str,
) -> EncodedResult<NodeRef> {
    let node = model.node(root)?;
    if node.tag() != tag || node.field_count() != fields {
        Err(EncodedValidationError::invariant(format!(
            "{name} root no longer has schema-1 shape"
        )))
    } else {
        Ok(node)
    }
}

fn node_field<B: ByteSource>(
    model: &ValidatedModel<B>,
    node: NodeRef,
    offset: usize,
    name: &'static str,
) -> EncodedResult<NodeId> {
    let index = node
        .fields()
        .start
        .checked_add(offset)
        .ok_or_else(|| EncodedValidationError::invariant(format!("{name} index overflowed")))?;
    let component = required_component(model.field(index)?, name)?;
    let ComponentValue::Node(identifier) = model.resolve(component)? else {
        return Err(EncodedValidationError::invariant(format!(
            "{name} is not a node"
        )));
    };
    Ok(identifier)
}

fn inverse_role_id(roles: &ObjectRolePhase, identifier: u32) -> EncodedResult<u32> {
    roles
        .inverse_role_ids
        .get(
            usize::try_from(identifier)
                .map_err(|_| EncodedValidationError::invariant("object-role ID exceeds usize"))?,
        )
        .copied()
        .ok_or_else(|| EncodedValidationError::invariant("object-role ID is dangling"))
}

fn role_id_by_key(
    domain: &DecodedSymbolDomain,
    key: &[u8],
    budget: &mut PhaseBudget,
) -> EncodedResult<u32> {
    budget.claim_work(binary_search_work(domain.values.len()))?;
    let index = domain
        .values
        .binary_search_by(|candidate| candidate.key.as_slice().cmp(key))
        .map_err(|_| EncodedValidationError::invariant("object-role symbol key is absent"))?;
    u32::try_from(index)
        .map_err(|_| EncodedValidationError::resource("object-role symbol ID exceeds u32"))
}

fn remap_role(
    source: &ObjectRolePhase,
    merged: &ObjectRolePhase,
    identifier: u32,
    budget: &mut PhaseBudget,
) -> EncodedResult<u32> {
    let key = source
        .object_role_domain
        .values
        .get(usize::try_from(identifier).map_err(|_| {
            EncodedValidationError::invariant("source object-role ID exceeds usize")
        })?)
        .map(|value| value.key.as_slice())
        .ok_or_else(|| EncodedValidationError::invariant("source object-role ID is dangling"))?;
    role_id_by_key(&merged.object_role_domain, key, budget)
}

fn chain_structural_key(
    expressions: &[RoleExpression],
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<u8>> {
    let mut encoded = Vec::new();
    push_varint(&mut encoded, u64::from(OBJECT_PROPERTY_CHAIN_TAG), budget)?;
    push_byte(&mut encoded, 7, budget)?;
    push_varint(
        &mut encoded,
        u64::try_from(expressions.len())
            .map_err(|_| EncodedValidationError::resource("role chain arity exceeds u64"))?,
        budget,
    )?;
    for expression in expressions {
        push_byte(&mut encoded, 1, budget)?;
        push_frame(&mut encoded, &expression.structural_key, budget)?;
    }
    Ok(encoded)
}

fn node_axiom_key(tag: u16, fields: &[&[u8]], budget: &mut PhaseBudget) -> EncodedResult<Vec<u8>> {
    let mut encoded = Vec::new();
    push_varint(&mut encoded, u64::from(tag), budget)?;
    for field in fields {
        push_byte(&mut encoded, 1, budget)?;
        push_frame(&mut encoded, field, budget)?;
    }
    push_empty_set(&mut encoded, budget)?;
    Ok(encoded)
}

fn statement_digest(value: &[u8], budget: &mut PhaseBudget) -> EncodedResult<[u8; 32]> {
    budget.claim_work(value.len())?;
    Ok(Sha256::digest(value).into())
}

fn inverse_structural_key(property: &[u8], budget: &mut PhaseBudget) -> EncodedResult<Vec<u8>> {
    let mut key = Vec::new();
    push_varint(&mut key, u64::from(OBJECT_INVERSE_OF_TAG), budget)?;
    push_byte(&mut key, 1, budget)?;
    push_frame(&mut key, property, budget)?;
    Ok(key)
}

fn push_empty_set(target: &mut Vec<u8>, budget: &mut PhaseBudget) -> EncodedResult<()> {
    push_byte(target, 6, budget)?;
    push_varint(target, 0, budget)
}

fn push_frame(target: &mut Vec<u8>, value: &[u8], budget: &mut PhaseBudget) -> EncodedResult<()> {
    let length = u64::try_from(value.len())
        .map_err(|_| EncodedValidationError::resource("canonical frame length exceeds u64"))?;
    push_varint(target, length, budget)?;
    push_bytes(target, value, budget)
}

fn push_varint(
    target: &mut Vec<u8>,
    mut value: u64,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    loop {
        let payload = u8::try_from(value & 0x7f)
            .map_err(|_| EncodedValidationError::invariant("canonical varint exceeds u8"))?;
        value >>= 7;
        push_byte(target, payload | if value == 0 { 0 } else { 0x80 }, budget)?;
        if value == 0 {
            return Ok(());
        }
    }
}

fn push_byte(target: &mut Vec<u8>, value: u8, budget: &mut PhaseBudget) -> EncodedResult<()> {
    budget.claim_owned(1)?;
    target
        .try_reserve(1)
        .map_err(|_| EncodedValidationError::resource("canonical role axiom allocation failed"))?;
    target.push(value);
    Ok(())
}

fn push_bytes(target: &mut Vec<u8>, value: &[u8], budget: &mut PhaseBudget) -> EncodedResult<()> {
    budget.claim_owned(value.len())?;
    target
        .try_reserve(value.len())
        .map_err(|_| EncodedValidationError::resource("canonical role axiom allocation failed"))?;
    target.extend_from_slice(value);
    Ok(())
}

fn clone_bytes(
    value: &[u8],
    name: &'static str,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<u8>> {
    budget.claim_owned(value.len())?;
    let mut cloned = Vec::new();
    cloned
        .try_reserve_exact(value.len())
        .map_err(|_| EncodedValidationError::resource(format!("{name} allocation failed")))?;
    cloned.extend_from_slice(value);
    Ok(cloned)
}

fn reserve_u32(
    target: &mut Vec<u32>,
    count: usize,
    name: &'static str,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    budget.claim_owned(count.checked_mul(size_of::<u32>()).ok_or_else(|| {
        EncodedValidationError::resource(format!("{name} allocation overflowed"))
    })?)?;
    target
        .try_reserve_exact(count)
        .map_err(|_| EncodedValidationError::resource(format!("{name} allocation failed")))
}

fn push_raw(
    target: &mut Vec<RawChain>,
    value: RawChain,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    budget.claim_owned(size_of::<RawChain>())?;
    target.try_reserve(1).map_err(|_| {
        EncodedValidationError::resource("complex-role inclusion allocation failed")
    })?;
    target.push(value);
    Ok(())
}

fn push_digest(
    target: &mut Vec<[u8; 32]>,
    value: [u8; 32],
    name: &'static str,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    budget.claim_owned(size_of::<[u8; 32]>())?;
    target.try_reserve(1).map_err(|_| {
        EncodedValidationError::resource(format!("complex-role {name} allocation failed"))
    })?;
    target.push(value);
    Ok(())
}

fn validate_role_domain(roles: &ObjectRolePhase) -> EncodedResult<()> {
    if roles.object_role_domain.kind != SymbolKind::ObjectRole
        || roles.inverse_role_ids.len() != roles.object_role_domain.values.len()
    {
        return Err(EncodedValidationError::invariant(
            "complex-role source domain has an invalid shape",
        ));
    }
    for (index, value) in roles.object_role_domain.values.iter().enumerate() {
        if usize::try_from(value.identifier).ok() != Some(index)
            || (index > 0 && roles.object_role_domain.values[index - 1].key >= value.key)
        {
            return Err(EncodedValidationError::invariant(
                "complex-role source domain is not dense and canonical",
            ));
        }
        let inverse = usize::try_from(roles.inverse_role_ids[index]).map_err(|_| {
            EncodedValidationError::invariant("complex-role inverse ID exceeds usize")
        })?;
        if roles
            .inverse_role_ids
            .get(inverse)
            .and_then(|value| usize::try_from(*value).ok())
            != Some(index)
        {
            return Err(EncodedValidationError::invariant(
                "complex-role inverse mapping is not involutive",
            ));
        }
    }
    Ok(())
}

fn validate_phase_shape(phase: &ComplexRolePhase) -> EncodedResult<()> {
    if phase.compiled_roots != phase.compiled_statement_digests.len()
        || phase
            .compiled_statement_digests
            .windows(2)
            .any(|pair| pair[0] >= pair[1])
    {
        return Err(EncodedValidationError::invariant(
            "complex-role compiled-root identities are not canonical",
        ));
    }
    for inclusion in &phase.complex_inclusions {
        if inclusion.chain_role_ids.len() < 2
            || (inclusion.builtin && inclusion.inverse_generated)
            || (inclusion.builtin && !inclusion.statement_order_key.is_empty())
            || (!inclusion.builtin && inclusion.statement_order_key.is_empty())
        {
            return Err(EncodedValidationError::invariant(
                "complex-role inclusion has an invalid shape",
            ));
        }
    }
    if phase.complex_inclusions.windows(2).any(|pair| {
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
            "complex-role inclusions are not uniquely canonical",
        ));
    }
    Ok(())
}

fn required_component<T>(value: Option<T>, name: &'static str) -> EncodedResult<T> {
    value.ok_or_else(|| {
        EncodedValidationError::invariant(format!("validated {name} component disappeared"))
    })
}

fn binary_search_work(count: usize) -> usize {
    if count < 2 {
        1
    } else {
        usize::try_from(usize::BITS - (count - 1).leading_zeros())
            .unwrap_or(usize::MAX)
            .saturating_add(1)
    }
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
    use crate::input_wire::DecodedSymbolValue;

    fn role_phase() -> ObjectRolePhase {
        ObjectRolePhase {
            object_role_domain: DecodedSymbolDomain {
                kind: SymbolKind::ObjectRole,
                values: (0..4)
                    .map(|identifier| DecodedSymbolValue {
                        identifier,
                        key: vec![u8::try_from(identifier).unwrap_or(u8::MAX)],
                        display: format!("role:{identifier}"),
                        generated: false,
                        query_local: false,
                    })
                    .collect(),
            },
            inverse_role_ids: vec![1, 0, 2, 3],
            top_object_role_id: 2,
            bottom_object_role_id: 3,
            work: 0,
            owned_bytes: 0,
            manifest_limit: 1,
        }
    }

    #[test]
    fn inverse_generation_and_last_statement_priority_are_exact() -> EncodedResult<()> {
        let roles = role_phase();
        let mut budget = PhaseBudget::new(ComplexRolePhaseLimits::default());
        let mut raw = Vec::new();
        add_chain(
            &roles,
            &mut raw,
            vec![0, 2],
            0,
            [1; 32],
            vec![1],
            false,
            &mut budget,
        )?;
        add_chain(
            &roles,
            &mut raw,
            vec![0, 2],
            0,
            [9; 32],
            vec![9],
            false,
            &mut budget,
        )?;
        add_builtin_top_transitivity(&roles, &mut raw, &mut budget)?;
        let phase = freeze_phase(raw, vec![[1; 32], [9; 32]], budget)?;
        let source = phase
            .complex_inclusions
            .iter()
            .find(|value| value.chain_role_ids == [0, 2] && !value.inverse_generated)
            .ok_or_else(|| EncodedValidationError::invariant("source chain disappeared"))?;
        assert_eq!(source.provenance_sha256, [9; 32]);
        assert!(phase
            .complex_inclusions
            .iter()
            .any(|value| value.chain_role_ids == [2, 1] && value.inverse_generated));
        Ok(())
    }

    #[test]
    fn builtin_top_transitivity_overwrites_explicit_semantic_duplicate() -> EncodedResult<()> {
        let roles = role_phase();
        let mut budget = PhaseBudget::new(ComplexRolePhaseLimits::default());
        let mut raw = Vec::new();
        add_chain(
            &roles,
            &mut raw,
            vec![2, 2],
            2,
            [1; 32],
            vec![255],
            false,
            &mut budget,
        )?;
        add_builtin_top_transitivity(&roles, &mut raw, &mut budget)?;
        let phase = freeze_phase(raw, vec![[1; 32]], budget)?;
        assert_eq!(phase.complex_inclusions.len(), 1);
        let builtin_digest: [u8; 32] = Sha256::digest(BUILTIN_TOP_TRANSITIVITY_SEED).into();
        assert_eq!(
            phase.complex_inclusions[0].provenance_sha256,
            builtin_digest
        );
        assert!(phase.complex_inclusions[0].builtin);
        Ok(())
    }

    #[test]
    fn semantic_and_manifest_limits_fail_closed() -> EncodedResult<()> {
        let roles = role_phase();
        let mut budget = PhaseBudget::new(ComplexRolePhaseLimits {
            max_inclusions: 1,
            ..ComplexRolePhaseLimits::default()
        });
        let mut raw = Vec::new();
        add_chain(
            &roles,
            &mut raw,
            vec![0, 0],
            0,
            [1; 32],
            vec![1],
            false,
            &mut budget,
        )?;
        add_builtin_top_transitivity(&roles, &mut raw, &mut budget)?;
        let Err(error) = freeze_phase(raw, vec![[1; 32]], budget) else {
            return Err(EncodedValidationError::invariant(
                "complex-role inclusion limit unexpectedly succeeded",
            ));
        };
        assert_eq!(error.code, "NATIVE_ENCODED_RESOURCE_LIMIT");

        let mut budget = PhaseBudget::new(ComplexRolePhaseLimits::default());
        let mut raw = Vec::new();
        add_builtin_top_transitivity(&roles, &mut raw, &mut budget)?;
        let phase = freeze_phase(raw, Vec::new(), budget)?;
        let limited = ComplexRolePhase {
            manifest_limit: 1,
            ..phase
        };
        let Err(error) = limited.canonical_manifest_json() else {
            return Err(EncodedValidationError::invariant(
                "complex-role manifest limit unexpectedly succeeded",
            ));
        };
        assert_eq!(error.code, "NATIVE_ENCODED_RESOURCE_LIMIT");
        Ok(())
    }
}
