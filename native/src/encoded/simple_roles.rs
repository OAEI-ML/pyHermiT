//! Provenance-bearing simple object-role inclusion expansion.
//!
//! This phase mirrors the scalar role builder for simple subproperty,
//! equivalent-property, inverse-property, and symmetric-property axioms. Role
//! chains, SCC closure, regularity, simplicity, automata, and clausification
//! remain explicit later phases; this owned fragment is not publishable.
// SPDX-License-Identifier: LGPL-3.0-or-later

#![forbid(unsafe_code)]

use std::mem::size_of;

use serde::Serialize;
use sha2::{Digest, Sha256};

use super::model::{ComponentValue, NodeId, NodeRef, ValidatedModel};
use super::object_roles::ObjectRolePhase;
use super::symbols::{RootHandler, SymbolPhase};
use super::{ByteSource, EncodedResult, EncodedValidationError};
use crate::input_wire::{DecodedSymbolDomain, SymbolKind};

const SIMPLE_ROLE_PHASE_SCHEMA_VERSION: u16 = 1;
const ENTITY_TAG: u16 = 2;
const OBJECT_INVERSE_OF_TAG: u16 = 10;
const OBJECT_PROPERTY_CHAIN_TAG: u16 = 11;
const SUB_OBJECT_PROPERTY_TAG: u16 = 70;
const EQUIVALENT_OBJECT_PROPERTIES_TAG: u16 = 71;
const INVERSE_OBJECT_PROPERTIES_TAG: u16 = 73;
const SYMMETRIC_OBJECT_PROPERTY_TAG: u16 = 80;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SimpleRolePhaseLimits {
    pub max_slices: usize,
    pub max_inclusions: usize,
    pub max_compiled_roots: usize,
    pub max_owned_bytes: usize,
    pub max_work: u64,
    pub max_manifest_bytes: usize,
}

impl Default for SimpleRolePhaseLimits {
    fn default() -> Self {
        Self {
            max_slices: 32_769,
            max_inclusions: 100_000_000,
            max_compiled_roots: 10_000_000,
            max_owned_bytes: 512 * 1024 * 1024,
            max_work: 2_000_000_000,
            max_manifest_bytes: 512 * 1024 * 1024,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SimpleRoleInclusion {
    pub sub_role_id: u32,
    pub super_role_id: u32,
    pub provenance_sha256: [u8; 32],
    pub builtin: bool,
}

/// Owned output of simple object-role preprocessing.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SimpleRolePhase {
    pub simple_inclusions: Vec<SimpleRoleInclusion>,
    pub compiled_roots: usize,
    pub work: u64,
    pub owned_bytes: usize,
    compiled_statement_digests: Vec<[u8; 32]>,
    manifest_limit: usize,
}

impl SimpleRolePhase {
    /// Canonical private manifest used for scalar differential checks.
    pub fn canonical_manifest_json(&self) -> EncodedResult<Vec<u8>> {
        validate_phase_shape(self)?;
        let simple_inclusions = self
            .simple_inclusions
            .iter()
            .map(|inclusion| InclusionManifest {
                sub_role_id: inclusion.sub_role_id,
                super_role_id: inclusion.super_role_id,
                provenance_sha256: crate::model::hex(&inclusion.provenance_sha256),
                builtin: inclusion.builtin,
            })
            .collect();
        let encoded = serde_json::to_vec(&SimpleRoleManifest {
            schema_version: SIMPLE_ROLE_PHASE_SCHEMA_VERSION,
            family: "simple_object_role_inclusions",
            compiled_roots: self.compiled_roots,
            simple_inclusions,
        })
        .map_err(|_| {
            EncodedValidationError::invariant("simple-role manifest serialization failed")
        })?;
        if encoded.len() > self.manifest_limit {
            return Err(EncodedValidationError::resource(
                "simple-role manifest exceeds its byte limit",
            ));
        }
        Ok(encoded)
    }
}

#[derive(Serialize)]
struct SimpleRoleManifest {
    schema_version: u16,
    family: &'static str,
    compiled_roots: usize,
    simple_inclusions: Vec<InclusionManifest>,
}

#[derive(Serialize)]
struct InclusionManifest {
    sub_role_id: u32,
    super_role_id: u32,
    provenance_sha256: String,
    builtin: bool,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct RawInclusion {
    sub_role_id: u32,
    super_role_id: u32,
    provenance_sha256: [u8; 32],
    builtin: bool,
}

#[derive(Debug, Eq, PartialEq)]
struct RoleExpression {
    role_id: u32,
    structural_key: Vec<u8>,
}

struct PhaseBudget {
    limits: SimpleRolePhaseLimits,
    work: u64,
    owned_bytes: usize,
}

impl PhaseBudget {
    const fn new(limits: SimpleRolePhaseLimits) -> Self {
        Self {
            limits,
            work: 0,
            owned_bytes: 0,
        }
    }

    fn claim_work(&mut self, amount: usize) -> EncodedResult<()> {
        let amount = u64::try_from(amount)
            .map_err(|_| EncodedValidationError::resource("simple-role work exceeds u64"))?;
        let following = self
            .work
            .checked_add(amount)
            .ok_or_else(|| EncodedValidationError::resource("simple-role work overflowed"))?;
        if following > self.limits.max_work {
            return Err(EncodedValidationError::resource(
                "simple-role compilation exceeds its work limit",
            ));
        }
        self.work = following;
        Ok(())
    }

    fn claim_owned(&mut self, amount: usize) -> EncodedResult<()> {
        let following = self.owned_bytes.checked_add(amount).ok_or_else(|| {
            EncodedValidationError::resource("simple-role owned-byte count overflowed")
        })?;
        if following > self.limits.max_owned_bytes {
            return Err(EncodedValidationError::resource(
                "simple-role compilation exceeds its owned-byte limit",
            ));
        }
        self.owned_bytes = following;
        Ok(())
    }

    fn inclusions(&self, count: usize) -> EncodedResult<()> {
        if count > self.limits.max_inclusions {
            Err(EncodedValidationError::resource(
                "simple object-role inclusion count exceeds its limit",
            ))
        } else {
            Ok(())
        }
    }

    fn roots(&self, count: usize) -> EncodedResult<()> {
        if count > self.limits.max_compiled_roots {
            Err(EncodedValidationError::resource(
                "simple object-role compiled-root count exceeds its limit",
            ))
        } else {
            Ok(())
        }
    }
}

/// Expand the simple role constructors selected in one validated source slice.
pub fn compile_simple_role_phase<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    roles: &ObjectRolePhase,
    limits: SimpleRolePhaseLimits,
) -> EncodedResult<SimpleRolePhase> {
    validate_role_domain(roles)?;
    let mut budget = PhaseBudget::new(limits);
    let mut inclusions = Vec::new();
    let mut compiled_statement_digests = Vec::new();
    for root in &symbols.roots {
        budget.claim_work(1)?;
        let digest = match root.handler {
            RootHandler::SubObjectPropertyOf => compile_sub_object_property(
                model,
                symbols,
                roles,
                root.node,
                &mut inclusions,
                &mut budget,
            )?,
            RootHandler::EquivalentObjectProperties => Some(compile_equivalent_object_properties(
                model,
                symbols,
                roles,
                root.node,
                &mut inclusions,
                &mut budget,
            )?),
            RootHandler::InverseObjectProperties => Some(compile_inverse_object_properties(
                model,
                symbols,
                roles,
                root.node,
                &mut inclusions,
                &mut budget,
            )?),
            RootHandler::SymmetricObjectProperty => Some(compile_symmetric_object_property(
                model,
                symbols,
                roles,
                root.node,
                &mut inclusions,
                &mut budget,
            )?),
            _ => None,
        };
        if let Some(digest) = digest {
            push_digest(
                &mut compiled_statement_digests,
                digest,
                "compiled statement",
                &mut budget,
            )?;
        }
    }
    freeze_phase(inclusions, compiled_statement_digests, budget)
}

/// Merge source-local simple role graphs through the merged role-domain keys.
pub fn merge_simple_role_phases(
    source_roles: &[ObjectRolePhase],
    source_phases: &[SimpleRolePhase],
    merged_roles: &ObjectRolePhase,
    limits: SimpleRolePhaseLimits,
) -> EncodedResult<SimpleRolePhase> {
    if source_phases.is_empty() || source_phases.len() != source_roles.len() {
        return Err(EncodedValidationError::protocol(
            "simple-role program merge requires aligned nonempty slices",
        ));
    }
    if source_phases.len() > limits.max_slices {
        return Err(EncodedValidationError::resource(
            "simple-role slice count exceeds its limit",
        ));
    }
    validate_role_domain(merged_roles)?;
    let mut budget = PhaseBudget::new(limits);
    let _inclusion_total = source_phases.iter().try_fold(0_usize, |total, phase| {
        validate_phase_shape(phase)?;
        budget.claim_work(usize::try_from(phase.work).unwrap_or(usize::MAX))?;
        budget.claim_owned(phase.owned_bytes)?;
        total
            .checked_add(phase.simple_inclusions.len())
            .ok_or_else(|| EncodedValidationError::resource("merged inclusion count overflowed"))
    })?;
    let _digest_total = source_phases.iter().try_fold(0_usize, |total, phase| {
        total
            .checked_add(phase.compiled_statement_digests.len())
            .ok_or_else(|| EncodedValidationError::resource("merged root count overflowed"))
    })?;
    let mut inclusions = Vec::new();
    let mut compiled_statement_digests = Vec::new();
    for (roles, phase) in source_roles.iter().zip(source_phases) {
        validate_role_domain(roles)?;
        for inclusion in &phase.simple_inclusions {
            budget.claim_work(1)?;
            let sub_role_id = remap_role(roles, merged_roles, inclusion.sub_role_id, &mut budget)?;
            let super_role_id =
                remap_role(roles, merged_roles, inclusion.super_role_id, &mut budget)?;
            push_raw(
                &mut inclusions,
                RawInclusion {
                    sub_role_id,
                    super_role_id,
                    provenance_sha256: inclusion.provenance_sha256,
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
    inclusions: &mut Vec<RawInclusion>,
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
    if model.node(sub_node)?.tag() == OBJECT_PROPERTY_CHAIN_TAG {
        return Ok(None);
    }
    let sub = role_expression(model, symbols, roles, sub_node, budget)?;
    let sup = role_expression(
        model,
        symbols,
        roles,
        node_field(model, node, 1, "sub-object-property superproperty")?,
        budget,
    )?;
    let digest = node_axiom_digest(
        SUB_OBJECT_PROPERTY_TAG,
        &[&sub.structural_key, &sup.structural_key],
        budget,
    )?;
    add_simple(roles, inclusions, sub.role_id, sup.role_id, digest, budget)?;
    Ok(Some(digest))
}

fn compile_equivalent_object_properties<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    roles: &ObjectRolePhase,
    root: NodeId,
    inclusions: &mut Vec<RawInclusion>,
    budget: &mut PhaseBudget,
) -> EncodedResult<[u8; 32]> {
    let node = require_root(
        model,
        root,
        EQUIVALENT_OBJECT_PROPERTIES_TAG,
        2,
        "equivalent-object-properties",
    )?;
    let component = required_component(
        model.field(node.fields().start)?,
        "equivalent-object-properties members",
    )?;
    let ComponentValue::Collection(collection) = model.resolve(component)? else {
        return Err(EncodedValidationError::invariant(
            "equivalent-object-properties members are not a collection",
        ));
    };
    if collection.len() < 2 {
        return Err(EncodedValidationError::invariant(
            "equivalent-object-properties has fewer than two members",
        ));
    }
    budget.claim_owned(
        collection
            .len()
            .checked_mul(size_of::<RoleExpression>())
            .ok_or_else(|| {
                EncodedValidationError::resource(
                    "equivalent-object-properties member allocation overflowed",
                )
            })?,
    )?;
    let mut expressions = Vec::new();
    expressions
        .try_reserve_exact(collection.len())
        .map_err(|_| {
            EncodedValidationError::resource(
                "equivalent-object-properties member allocation failed",
            )
        })?;
    for item_index in collection.items() {
        budget.claim_work(1)?;
        let item = required_component(
            model.item(item_index)?,
            "equivalent-object-properties member",
        )?;
        let ComponentValue::Node(identifier) = model.resolve(item)? else {
            return Err(EncodedValidationError::invariant(
                "equivalent-object-properties member is not a node",
            ));
        };
        expressions.push(role_expression(model, symbols, roles, identifier, budget)?);
    }
    let digest = set_axiom_digest(EQUIVALENT_OBJECT_PROPERTIES_TAG, &expressions, budget)?;
    let first = expressions[0].role_id;
    for other in expressions.iter().skip(1) {
        add_simple(roles, inclusions, first, other.role_id, digest, budget)?;
        add_simple(roles, inclusions, other.role_id, first, digest, budget)?;
    }
    Ok(digest)
}

fn compile_inverse_object_properties<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    roles: &ObjectRolePhase,
    root: NodeId,
    inclusions: &mut Vec<RawInclusion>,
    budget: &mut PhaseBudget,
) -> EncodedResult<[u8; 32]> {
    let node = require_root(
        model,
        root,
        INVERSE_OBJECT_PROPERTIES_TAG,
        3,
        "inverse-object-properties",
    )?;
    let first = role_expression(
        model,
        symbols,
        roles,
        node_field(model, node, 0, "inverse-object-properties first")?,
        budget,
    )?;
    let second = role_expression(
        model,
        symbols,
        roles,
        node_field(model, node, 1, "inverse-object-properties second")?,
        budget,
    )?;
    let digest = node_axiom_digest(
        INVERSE_OBJECT_PROPERTIES_TAG,
        &[&first.structural_key, &second.structural_key],
        budget,
    )?;
    let inverse_second = inverse_role_id(roles, second.role_id)?;
    add_simple(
        roles,
        inclusions,
        first.role_id,
        inverse_second,
        digest,
        budget,
    )?;
    add_simple(
        roles,
        inclusions,
        inverse_second,
        first.role_id,
        digest,
        budget,
    )?;
    Ok(digest)
}

fn compile_symmetric_object_property<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    roles: &ObjectRolePhase,
    root: NodeId,
    inclusions: &mut Vec<RawInclusion>,
    budget: &mut PhaseBudget,
) -> EncodedResult<[u8; 32]> {
    let node = require_root(
        model,
        root,
        SYMMETRIC_OBJECT_PROPERTY_TAG,
        2,
        "symmetric-object-property",
    )?;
    let role = role_expression(
        model,
        symbols,
        roles,
        node_field(model, node, 0, "symmetric-object-property role")?,
        budget,
    )?;
    let digest = node_axiom_digest(
        SYMMETRIC_OBJECT_PROPERTY_TAG,
        &[&role.structural_key],
        budget,
    )?;
    let inverse = inverse_role_id(roles, role.role_id)?;
    add_simple(roles, inclusions, role.role_id, inverse, digest, budget)?;
    add_simple(roles, inclusions, inverse, role.role_id, digest, budget)?;
    Ok(digest)
}

fn add_simple(
    roles: &ObjectRolePhase,
    target: &mut Vec<RawInclusion>,
    sub_role_id: u32,
    super_role_id: u32,
    provenance_sha256: [u8; 32],
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    push_raw(
        target,
        RawInclusion {
            sub_role_id,
            super_role_id,
            provenance_sha256,
            builtin: false,
        },
        budget,
    )?;
    push_raw(
        target,
        RawInclusion {
            sub_role_id: inverse_role_id(roles, sub_role_id)?,
            super_role_id: inverse_role_id(roles, super_role_id)?,
            provenance_sha256,
            builtin: false,
        },
        budget,
    )
}

fn freeze_phase(
    mut raw: Vec<RawInclusion>,
    mut compiled_statement_digests: Vec<[u8; 32]>,
    mut budget: PhaseBudget,
) -> EncodedResult<SimpleRolePhase> {
    budget.claim_work(sort_work(raw.len()))?;
    raw.sort_by_key(|inclusion| {
        (
            inclusion.sub_role_id,
            inclusion.super_role_id,
            inclusion.builtin,
            inclusion.provenance_sha256,
        )
    });
    let mut simple_inclusions: Vec<SimpleRoleInclusion> = Vec::new();
    budget.claim_owned(
        raw.len()
            .checked_mul(size_of::<SimpleRoleInclusion>())
            .ok_or_else(|| {
                EncodedValidationError::resource("simple-role result allocation overflowed")
            })?,
    )?;
    simple_inclusions
        .try_reserve_exact(raw.len())
        .map_err(|_| EncodedValidationError::resource("simple-role result allocation failed"))?;
    for inclusion in raw {
        if simple_inclusions.last().is_some_and(|previous| {
            previous.sub_role_id == inclusion.sub_role_id
                && previous.super_role_id == inclusion.super_role_id
        }) {
            continue;
        }
        simple_inclusions.push(SimpleRoleInclusion {
            sub_role_id: inclusion.sub_role_id,
            super_role_id: inclusion.super_role_id,
            provenance_sha256: inclusion.provenance_sha256,
            builtin: inclusion.builtin,
        });
    }
    budget.inclusions(simple_inclusions.len())?;
    budget.claim_work(sort_work(compiled_statement_digests.len()))?;
    compiled_statement_digests.sort_unstable();
    compiled_statement_digests.dedup();
    budget.roots(compiled_statement_digests.len())?;
    let phase = SimpleRolePhase {
        simple_inclusions,
        compiled_roots: compiled_statement_digests.len(),
        work: budget.work,
        owned_bytes: budget.owned_bytes,
        compiled_statement_digests,
        manifest_limit: budget.limits.max_manifest_bytes,
    };
    validate_phase_shape(&phase)?;
    Ok(phase)
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
            "simple role field is not an object-property expression",
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

fn node_axiom_digest(
    tag: u16,
    fields: &[&[u8]],
    budget: &mut PhaseBudget,
) -> EncodedResult<[u8; 32]> {
    let mut encoded = Vec::new();
    push_varint(&mut encoded, u64::from(tag), budget)?;
    for field in fields {
        push_byte(&mut encoded, 1, budget)?;
        push_frame(&mut encoded, field, budget)?;
    }
    push_empty_set(&mut encoded, budget)?;
    budget.claim_work(encoded.len())?;
    Ok(Sha256::digest(encoded).into())
}

fn set_axiom_digest(
    tag: u16,
    members: &[RoleExpression],
    budget: &mut PhaseBudget,
) -> EncodedResult<[u8; 32]> {
    let mut encoded = Vec::new();
    push_varint(&mut encoded, u64::from(tag), budget)?;
    push_byte(&mut encoded, 6, budget)?;
    push_varint(
        &mut encoded,
        u64::try_from(members.len())
            .map_err(|_| EncodedValidationError::resource("role set arity exceeds u64"))?,
        budget,
    )?;
    for member in members {
        push_frame(&mut encoded, &member.structural_key, budget)?;
    }
    push_empty_set(&mut encoded, budget)?;
    budget.claim_work(encoded.len())?;
    Ok(Sha256::digest(encoded).into())
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

fn push_raw(
    target: &mut Vec<RawInclusion>,
    value: RawInclusion,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    budget.claim_owned(size_of::<RawInclusion>())?;
    target
        .try_reserve(1)
        .map_err(|_| EncodedValidationError::resource("simple-role inclusion allocation failed"))?;
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
        EncodedValidationError::resource(format!("simple-role {name} allocation failed"))
    })?;
    target.push(value);
    Ok(())
}

fn validate_role_domain(roles: &ObjectRolePhase) -> EncodedResult<()> {
    if roles.object_role_domain.kind != SymbolKind::ObjectRole
        || roles.inverse_role_ids.len() != roles.object_role_domain.values.len()
    {
        return Err(EncodedValidationError::invariant(
            "simple-role source domain has an invalid shape",
        ));
    }
    for (index, value) in roles.object_role_domain.values.iter().enumerate() {
        if usize::try_from(value.identifier).ok() != Some(index)
            || (index > 0 && roles.object_role_domain.values[index - 1].key >= value.key)
        {
            return Err(EncodedValidationError::invariant(
                "simple-role source domain is not dense and canonical",
            ));
        }
        let inverse = usize::try_from(roles.inverse_role_ids[index]).map_err(|_| {
            EncodedValidationError::invariant("simple-role inverse ID exceeds usize")
        })?;
        if roles
            .inverse_role_ids
            .get(inverse)
            .and_then(|value| usize::try_from(*value).ok())
            != Some(index)
        {
            return Err(EncodedValidationError::invariant(
                "simple-role inverse mapping is not involutive",
            ));
        }
    }
    Ok(())
}

fn validate_phase_shape(phase: &SimpleRolePhase) -> EncodedResult<()> {
    if phase.compiled_roots != phase.compiled_statement_digests.len()
        || phase
            .compiled_statement_digests
            .windows(2)
            .any(|pair| pair[0] >= pair[1])
    {
        return Err(EncodedValidationError::invariant(
            "simple-role compiled-root identities are not canonical",
        ));
    }
    if phase.simple_inclusions.windows(2).any(|pair| {
        (pair[0].sub_role_id, pair[0].super_role_id) >= (pair[1].sub_role_id, pair[1].super_role_id)
    }) {
        return Err(EncodedValidationError::invariant(
            "simple-role inclusions are not uniquely canonical",
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

    fn inverse_ids() -> Vec<u32> {
        vec![2, 3, 0, 1]
    }

    #[test]
    fn simple_expansion_adds_inverse_edges_and_prefers_lowest_provenance() -> EncodedResult<()> {
        let roles = ObjectRolePhase {
            object_role_domain: DecodedSymbolDomain {
                kind: SymbolKind::ObjectRole,
                values: Vec::new(),
            },
            inverse_role_ids: inverse_ids(),
            top_object_role_id: 0,
            bottom_object_role_id: 1,
            work: 0,
            owned_bytes: 0,
            manifest_limit: 1,
        };
        let mut budget = PhaseBudget::new(SimpleRolePhaseLimits::default());
        let mut raw = Vec::new();
        add_simple(&roles, &mut raw, 0, 1, [9; 32], &mut budget)?;
        add_simple(&roles, &mut raw, 0, 1, [1; 32], &mut budget)?;
        let phase = freeze_phase(raw, vec![[9; 32], [1; 32]], budget)?;
        assert_eq!(phase.simple_inclusions.len(), 2);
        assert_eq!(phase.simple_inclusions[0].provenance_sha256, [1; 32]);
        assert_eq!(phase.simple_inclusions[1].sub_role_id, 2);
        assert_eq!(phase.simple_inclusions[1].super_role_id, 3);
        assert_eq!(phase.compiled_roots, 2);
        Ok(())
    }

    #[test]
    fn duplicate_candidates_do_not_consume_the_semantic_inclusion_limit() -> EncodedResult<()> {
        let mut budget = PhaseBudget::new(SimpleRolePhaseLimits {
            max_inclusions: 1,
            ..SimpleRolePhaseLimits::default()
        });
        let mut raw = Vec::new();
        push_raw(
            &mut raw,
            RawInclusion {
                sub_role_id: 0,
                super_role_id: 1,
                provenance_sha256: [2; 32],
                builtin: false,
            },
            &mut budget,
        )?;
        push_raw(
            &mut raw,
            RawInclusion {
                sub_role_id: 0,
                super_role_id: 1,
                provenance_sha256: [1; 32],
                builtin: false,
            },
            &mut budget,
        )?;
        let phase = freeze_phase(raw, vec![[1; 32]], budget)?;
        assert_eq!(phase.simple_inclusions.len(), 1);
        assert_eq!(phase.simple_inclusions[0].provenance_sha256, [1; 32]);
        Ok(())
    }

    #[test]
    fn semantic_inclusion_and_manifest_limits_fail_transactionally() -> EncodedResult<()> {
        let budget = PhaseBudget::new(SimpleRolePhaseLimits {
            max_inclusions: 1,
            ..SimpleRolePhaseLimits::default()
        });
        let raw = vec![
            RawInclusion {
                sub_role_id: 0,
                super_role_id: 1,
                provenance_sha256: [1; 32],
                builtin: false,
            },
            RawInclusion {
                sub_role_id: 1,
                super_role_id: 0,
                provenance_sha256: [1; 32],
                builtin: false,
            },
        ];
        let Err(error) = freeze_phase(raw, vec![[1; 32]], budget) else {
            return Err(EncodedValidationError::invariant(
                "simple-role inclusion limit unexpectedly succeeded",
            ));
        };
        assert_eq!(error.code, "NATIVE_ENCODED_RESOURCE_LIMIT");

        let phase = freeze_phase(
            Vec::new(),
            Vec::new(),
            PhaseBudget::new(SimpleRolePhaseLimits::default()),
        )?;
        let limited = SimpleRolePhase {
            manifest_limit: 1,
            ..phase
        };
        let Err(error) = limited.canonical_manifest_json() else {
            return Err(EncodedValidationError::invariant(
                "simple-role manifest limit unexpectedly succeeded",
            ));
        };
        assert_eq!(error.code, "NATIVE_ENCODED_RESOURCE_LIMIT");
        Ok(())
    }
}
