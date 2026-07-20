//! Provenance-bearing data-property inclusion compilation.
//!
//! This phase mirrors the scalar role builder for sub-data-property and
//! equivalent-data-property axioms. SCC closure, predicates, clauses, and
//! property characteristics remain explicit later phases.
// SPDX-License-Identifier: LGPL-3.0-or-later

#![forbid(unsafe_code)]

use std::mem::size_of;

use serde::Serialize;
use sha2::{Digest, Sha256};

use super::data_roles::DataRolePhase;
use super::model::{ComponentValue, NodeId, NodeRef, ValidatedModel};
use super::symbols::{RootHandler, SymbolPhase};
use super::{ByteSource, EncodedResult, EncodedValidationError};
use crate::input_wire::{DecodedSymbolDomain, SymbolKind};

const DATA_INCLUSION_PHASE_SCHEMA_VERSION: u16 = 1;
const ENTITY_TAG: u16 = 2;
const SUB_DATA_PROPERTY_TAG: u16 = 90;
const EQUIVALENT_DATA_PROPERTIES_TAG: u16 = 91;
const DATA_PROPERTY_PREFIX: &str = "data_property:";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct DataInclusionPhaseLimits {
    pub max_slices: usize,
    pub max_inclusions: usize,
    pub max_compiled_roots: usize,
    pub max_owned_bytes: usize,
    pub max_work: u64,
    pub max_manifest_bytes: usize,
}

impl Default for DataInclusionPhaseLimits {
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
pub struct DataRoleInclusion {
    pub sub_property_id: u32,
    pub super_property_id: u32,
    pub provenance_sha256: [u8; 32],
    pub builtin: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DataInclusionPhase {
    pub data_inclusions: Vec<DataRoleInclusion>,
    pub compiled_roots: usize,
    pub work: u64,
    pub owned_bytes: usize,
    pub(super) compiled_statement_digests: Vec<[u8; 32]>,
    pub(super) manifest_limit: usize,
}

impl DataInclusionPhase {
    /// Canonical private manifest used for exact scalar differential checks.
    pub fn canonical_manifest_json(&self) -> EncodedResult<Vec<u8>> {
        validate_phase_shape(self)?;
        let data_inclusions = self
            .data_inclusions
            .iter()
            .map(|inclusion| InclusionManifest {
                sub_property_id: inclusion.sub_property_id,
                super_property_id: inclusion.super_property_id,
                provenance_sha256: crate::model::hex(&inclusion.provenance_sha256),
                builtin: inclusion.builtin,
            })
            .collect();
        let encoded = serde_json::to_vec(&DataInclusionManifest {
            schema_version: DATA_INCLUSION_PHASE_SCHEMA_VERSION,
            family: "data_property_inclusions",
            compiled_roots: self.compiled_roots,
            data_inclusions,
        })
        .map_err(|_| {
            EncodedValidationError::invariant(
                "data-property inclusion manifest serialization failed",
            )
        })?;
        if encoded.len() > self.manifest_limit {
            return Err(EncodedValidationError::resource(
                "data-property inclusion manifest exceeds its byte limit",
            ));
        }
        Ok(encoded)
    }
}

#[derive(Serialize)]
struct DataInclusionManifest {
    schema_version: u16,
    family: &'static str,
    compiled_roots: usize,
    data_inclusions: Vec<InclusionManifest>,
}

#[derive(Serialize)]
struct InclusionManifest {
    sub_property_id: u32,
    super_property_id: u32,
    provenance_sha256: String,
    builtin: bool,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct RawInclusion {
    sub_property_id: u32,
    super_property_id: u32,
    provenance_sha256: [u8; 32],
    builtin: bool,
}

#[derive(Debug, Eq, PartialEq)]
struct DataPropertyExpression {
    property_id: u32,
    structural_key: Vec<u8>,
}

struct PhaseBudget {
    limits: DataInclusionPhaseLimits,
    work: u64,
    owned_bytes: usize,
}

impl PhaseBudget {
    const fn new(limits: DataInclusionPhaseLimits) -> Self {
        Self {
            limits,
            work: 0,
            owned_bytes: 0,
        }
    }

    fn claim_work(&mut self, amount: usize) -> EncodedResult<()> {
        let amount = u64::try_from(amount).map_err(|_| {
            EncodedValidationError::resource("data-property inclusion work exceeds u64")
        })?;
        let following = self.work.checked_add(amount).ok_or_else(|| {
            EncodedValidationError::resource("data-property inclusion work overflowed")
        })?;
        if following > self.limits.max_work {
            return Err(EncodedValidationError::resource(
                "data-property inclusion compilation exceeds its work limit",
            ));
        }
        self.work = following;
        Ok(())
    }

    fn claim_owned(&mut self, amount: usize) -> EncodedResult<()> {
        let following = self.owned_bytes.checked_add(amount).ok_or_else(|| {
            EncodedValidationError::resource("data-property inclusion owned bytes overflowed")
        })?;
        if following > self.limits.max_owned_bytes {
            return Err(EncodedValidationError::resource(
                "data-property inclusion compilation exceeds its owned-byte limit",
            ));
        }
        self.owned_bytes = following;
        Ok(())
    }

    fn validate_counts(&self, inclusion_count: usize, root_count: usize) -> EncodedResult<()> {
        if inclusion_count > self.limits.max_inclusions {
            return Err(EncodedValidationError::resource(
                "data-property inclusion count exceeds its limit",
            ));
        }
        if root_count > self.limits.max_compiled_roots {
            return Err(EncodedValidationError::resource(
                "data-property inclusion compiled-root count exceeds its limit",
            ));
        }
        Ok(())
    }
}

/// Compile selected data-property inclusion roots from one source slice.
pub fn compile_data_inclusion_phase<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    roles: &DataRolePhase,
    limits: DataInclusionPhaseLimits,
) -> EncodedResult<DataInclusionPhase> {
    validate_role_domain(roles)?;
    let mut budget = PhaseBudget::new(limits);
    let mut inclusions = Vec::new();
    let mut compiled_statement_digests = Vec::new();
    for root in &symbols.roots {
        budget.claim_work(1)?;
        let digest = match root.handler {
            RootHandler::SubDataPropertyOf => Some(compile_sub_data_property(
                model,
                symbols,
                roles,
                root.node,
                &mut inclusions,
                &mut budget,
            )?),
            RootHandler::EquivalentDataProperties => Some(compile_equivalent_data_properties(
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
            push_digest(&mut compiled_statement_digests, digest, &mut budget)?;
        }
    }
    freeze_phase(inclusions, compiled_statement_digests, budget)
}

/// Remap and merge source-local inclusions through canonical property keys.
pub fn merge_data_inclusion_phases(
    source_roles: &[DataRolePhase],
    source_phases: &[DataInclusionPhase],
    merged_roles: &DataRolePhase,
    limits: DataInclusionPhaseLimits,
) -> EncodedResult<DataInclusionPhase> {
    if source_phases.is_empty() || source_phases.len() != source_roles.len() {
        return Err(EncodedValidationError::protocol(
            "data-property inclusion merge requires aligned nonempty slices",
        ));
    }
    if source_phases.len() > limits.max_slices {
        return Err(EncodedValidationError::resource(
            "data-property inclusion slice count exceeds its limit",
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
        for inclusion in &phase.data_inclusions {
            budget.claim_work(1)?;
            push_raw(
                &mut inclusions,
                RawInclusion {
                    sub_property_id: remap_property(
                        roles,
                        merged_roles,
                        inclusion.sub_property_id,
                        &mut budget,
                    )?,
                    super_property_id: remap_property(
                        roles,
                        merged_roles,
                        inclusion.super_property_id,
                        &mut budget,
                    )?,
                    provenance_sha256: inclusion.provenance_sha256,
                    builtin: inclusion.builtin,
                },
                &mut budget,
            )?;
        }
        for digest in &phase.compiled_statement_digests {
            push_digest(&mut compiled_statement_digests, *digest, &mut budget)?;
        }
    }
    freeze_phase(inclusions, compiled_statement_digests, budget)
}

fn compile_sub_data_property<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    roles: &DataRolePhase,
    root: NodeId,
    inclusions: &mut Vec<RawInclusion>,
    budget: &mut PhaseBudget,
) -> EncodedResult<[u8; 32]> {
    let node = require_root(model, root, SUB_DATA_PROPERTY_TAG, 3, "sub-data-property")?;
    let sub = data_property_expression(
        model,
        symbols,
        roles,
        node_field(model, node, 0, "sub-data-property subproperty")?,
        budget,
    )?;
    let sup = data_property_expression(
        model,
        symbols,
        roles,
        node_field(model, node, 1, "sub-data-property superproperty")?,
        budget,
    )?;
    let digest = node_axiom_digest(
        SUB_DATA_PROPERTY_TAG,
        &[&sub.structural_key, &sup.structural_key],
        budget,
    )?;
    add_inclusion(inclusions, sub.property_id, sup.property_id, digest, budget)?;
    Ok(digest)
}

fn compile_equivalent_data_properties<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    roles: &DataRolePhase,
    root: NodeId,
    inclusions: &mut Vec<RawInclusion>,
    budget: &mut PhaseBudget,
) -> EncodedResult<[u8; 32]> {
    let node = require_root(
        model,
        root,
        EQUIVALENT_DATA_PROPERTIES_TAG,
        2,
        "equivalent-data-properties",
    )?;
    let component = required_component(
        model.field(node.fields().start)?,
        "equivalent-data-properties members",
    )?;
    let ComponentValue::Collection(collection) = model.resolve(component)? else {
        return Err(EncodedValidationError::invariant(
            "equivalent-data-properties members are not a collection",
        ));
    };
    if collection.len() < 2 {
        return Err(EncodedValidationError::invariant(
            "equivalent-data-properties has fewer than two members",
        ));
    }
    budget.claim_owned(
        collection
            .len()
            .checked_mul(size_of::<DataPropertyExpression>())
            .ok_or_else(|| {
                EncodedValidationError::resource(
                    "equivalent-data-properties member allocation overflowed",
                )
            })?,
    )?;
    let mut expressions = Vec::new();
    expressions
        .try_reserve_exact(collection.len())
        .map_err(|_| {
            EncodedValidationError::resource("equivalent-data-properties member allocation failed")
        })?;
    for item_index in collection.items() {
        budget.claim_work(1)?;
        let item =
            required_component(model.item(item_index)?, "equivalent-data-properties member")?;
        let ComponentValue::Node(identifier) = model.resolve(item)? else {
            return Err(EncodedValidationError::invariant(
                "equivalent-data-properties member is not a node",
            ));
        };
        expressions.push(data_property_expression(
            model, symbols, roles, identifier, budget,
        )?);
    }
    let digest = set_axiom_digest(EQUIVALENT_DATA_PROPERTIES_TAG, &expressions, budget)?;
    let first = expressions[0].property_id;
    for other in expressions.iter().skip(1) {
        add_inclusion(inclusions, first, other.property_id, digest, budget)?;
        add_inclusion(inclusions, other.property_id, first, digest, budget)?;
    }
    Ok(digest)
}

fn add_inclusion(
    target: &mut Vec<RawInclusion>,
    sub_property_id: u32,
    super_property_id: u32,
    provenance_sha256: [u8; 32],
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    push_raw(
        target,
        RawInclusion {
            sub_property_id,
            super_property_id,
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
) -> EncodedResult<DataInclusionPhase> {
    budget.claim_work(sort_work(raw.len()))?;
    raw.sort_by_key(|inclusion| {
        (
            inclusion.sub_property_id,
            inclusion.super_property_id,
            inclusion.builtin,
            inclusion.provenance_sha256,
        )
    });
    budget.claim_owned(
        raw.len()
            .checked_mul(size_of::<DataRoleInclusion>())
            .ok_or_else(|| {
                EncodedValidationError::resource(
                    "data-property inclusion result allocation overflowed",
                )
            })?,
    )?;
    let mut data_inclusions: Vec<DataRoleInclusion> = Vec::new();
    data_inclusions.try_reserve_exact(raw.len()).map_err(|_| {
        EncodedValidationError::resource("data-property inclusion result allocation failed")
    })?;
    for inclusion in raw {
        if data_inclusions.last().is_some_and(|previous| {
            previous.sub_property_id == inclusion.sub_property_id
                && previous.super_property_id == inclusion.super_property_id
        }) {
            continue;
        }
        data_inclusions.push(DataRoleInclusion {
            sub_property_id: inclusion.sub_property_id,
            super_property_id: inclusion.super_property_id,
            provenance_sha256: inclusion.provenance_sha256,
            builtin: inclusion.builtin,
        });
    }
    budget.claim_work(sort_work(compiled_statement_digests.len()))?;
    compiled_statement_digests.sort_unstable();
    compiled_statement_digests.dedup();
    budget.validate_counts(data_inclusions.len(), compiled_statement_digests.len())?;
    let phase = DataInclusionPhase {
        data_inclusions,
        compiled_roots: compiled_statement_digests.len(),
        work: budget.work,
        owned_bytes: budget.owned_bytes,
        compiled_statement_digests,
        manifest_limit: budget.limits.max_manifest_bytes,
    };
    validate_phase_shape(&phase)?;
    Ok(phase)
}

fn data_property_expression<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    roles: &DataRolePhase,
    identifier: NodeId,
    budget: &mut PhaseBudget,
) -> EncodedResult<DataPropertyExpression> {
    let node = model.node(identifier)?;
    if node.tag() != ENTITY_TAG {
        return Err(EncodedValidationError::invariant(
            "data-property field is not an entity",
        ));
    }
    let entity_id = symbols.entity_symbol_for_node(identifier).ok_or_else(|| {
        EncodedValidationError::invariant("data-property expression is absent from the entity seed")
    })?;
    let entity = symbols
        .entity_domain
        .values
        .get(usize::try_from(entity_id).map_err(|_| {
            EncodedValidationError::invariant("data-property entity ID exceeds usize")
        })?)
        .ok_or_else(|| EncodedValidationError::invariant("data-property entity ID is dangling"))?;
    if !entity.display.starts_with(DATA_PROPERTY_PREFIX) {
        return Err(EncodedValidationError::invariant(
            "data-property expression resolved to a different entity kind",
        ));
    }
    budget.claim_owned(entity.key.len())?;
    Ok(DataPropertyExpression {
        property_id: property_id_by_key(&roles.data_property_domain, &entity.key, budget)?,
        structural_key: entity.key.clone(),
    })
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

fn property_id_by_key(
    domain: &DecodedSymbolDomain,
    key: &[u8],
    budget: &mut PhaseBudget,
) -> EncodedResult<u32> {
    budget.claim_work(binary_search_work(domain.values.len()))?;
    let index = domain
        .values
        .binary_search_by(|candidate| candidate.key.as_slice().cmp(key))
        .map_err(|_| EncodedValidationError::invariant("data-property symbol key is absent"))?;
    u32::try_from(index)
        .map_err(|_| EncodedValidationError::resource("data-property symbol ID exceeds u32"))
}

fn remap_property(
    source: &DataRolePhase,
    merged: &DataRolePhase,
    identifier: u32,
    budget: &mut PhaseBudget,
) -> EncodedResult<u32> {
    let key = source
        .data_property_domain
        .values
        .get(usize::try_from(identifier).map_err(|_| {
            EncodedValidationError::invariant("source data-property ID exceeds usize")
        })?)
        .map(|value| value.key.as_slice())
        .ok_or_else(|| EncodedValidationError::invariant("source data-property ID is dangling"))?;
    property_id_by_key(&merged.data_property_domain, key, budget)
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
    members: &[DataPropertyExpression],
    budget: &mut PhaseBudget,
) -> EncodedResult<[u8; 32]> {
    let mut encoded = Vec::new();
    push_varint(&mut encoded, u64::from(tag), budget)?;
    push_byte(&mut encoded, 6, budget)?;
    push_varint(
        &mut encoded,
        u64::try_from(members.len())
            .map_err(|_| EncodedValidationError::resource("data-property set arity exceeds u64"))?,
        budget,
    )?;
    for member in members {
        push_frame(&mut encoded, &member.structural_key, budget)?;
    }
    push_empty_set(&mut encoded, budget)?;
    budget.claim_work(encoded.len())?;
    Ok(Sha256::digest(encoded).into())
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
    target.try_reserve(1).map_err(|_| {
        EncodedValidationError::resource("canonical data-property axiom allocation failed")
    })?;
    target.push(value);
    Ok(())
}

fn push_bytes(target: &mut Vec<u8>, value: &[u8], budget: &mut PhaseBudget) -> EncodedResult<()> {
    budget.claim_owned(value.len())?;
    target.try_reserve(value.len()).map_err(|_| {
        EncodedValidationError::resource("canonical data-property axiom allocation failed")
    })?;
    target.extend_from_slice(value);
    Ok(())
}

fn push_raw(
    target: &mut Vec<RawInclusion>,
    value: RawInclusion,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    budget.claim_owned(size_of::<RawInclusion>())?;
    target.try_reserve(1).map_err(|_| {
        EncodedValidationError::resource("data-property inclusion allocation failed")
    })?;
    target.push(value);
    Ok(())
}

fn push_digest(
    target: &mut Vec<[u8; 32]>,
    value: [u8; 32],
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    budget.claim_owned(size_of::<[u8; 32]>())?;
    target.try_reserve(1).map_err(|_| {
        EncodedValidationError::resource("data-property compiled statement allocation failed")
    })?;
    target.push(value);
    Ok(())
}

fn validate_role_domain(roles: &DataRolePhase) -> EncodedResult<()> {
    if roles.data_property_domain.kind != SymbolKind::DataProperty {
        return Err(EncodedValidationError::invariant(
            "data-property inclusion source domain has an invalid kind",
        ));
    }
    for (index, value) in roles.data_property_domain.values.iter().enumerate() {
        if usize::try_from(value.identifier).ok() != Some(index)
            || (index > 0 && roles.data_property_domain.values[index - 1].key >= value.key)
        {
            return Err(EncodedValidationError::invariant(
                "data-property inclusion source domain is not dense and canonical",
            ));
        }
    }
    Ok(())
}

fn validate_phase_shape(phase: &DataInclusionPhase) -> EncodedResult<()> {
    if phase.compiled_roots != phase.compiled_statement_digests.len()
        || phase
            .compiled_statement_digests
            .windows(2)
            .any(|pair| pair[0] >= pair[1])
    {
        return Err(EncodedValidationError::invariant(
            "data-property compiled-root identities are not canonical",
        ));
    }
    if phase.data_inclusions.windows(2).any(|pair| {
        (pair[0].sub_property_id, pair[0].super_property_id)
            >= (pair[1].sub_property_id, pair[1].super_property_id)
    }) {
        return Err(EncodedValidationError::invariant(
            "data-property inclusions are not uniquely canonical",
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

    #[test]
    fn duplicate_edges_prefer_lowest_provenance() -> EncodedResult<()> {
        let mut budget = PhaseBudget::new(DataInclusionPhaseLimits::default());
        let mut raw = Vec::new();
        add_inclusion(&mut raw, 0, 1, [9; 32], &mut budget)?;
        add_inclusion(&mut raw, 0, 1, [1; 32], &mut budget)?;
        let phase = freeze_phase(raw, vec![[9; 32], [1; 32]], budget)?;
        assert_eq!(phase.data_inclusions.len(), 1);
        assert_eq!(phase.data_inclusions[0].provenance_sha256, [1; 32]);
        assert_eq!(phase.compiled_roots, 2);
        Ok(())
    }

    #[test]
    fn duplicate_candidates_do_not_consume_the_semantic_limit() -> EncodedResult<()> {
        let mut budget = PhaseBudget::new(DataInclusionPhaseLimits {
            max_inclusions: 1,
            ..DataInclusionPhaseLimits::default()
        });
        let mut raw = Vec::new();
        add_inclusion(&mut raw, 0, 1, [2; 32], &mut budget)?;
        add_inclusion(&mut raw, 0, 1, [1; 32], &mut budget)?;
        let phase = freeze_phase(raw, vec![[1; 32]], budget)?;
        assert_eq!(phase.data_inclusions.len(), 1);
        assert_eq!(phase.data_inclusions[0].provenance_sha256, [1; 32]);
        Ok(())
    }

    #[test]
    fn semantic_and_manifest_limits_fail_transactionally() -> EncodedResult<()> {
        let mut budget = PhaseBudget::new(DataInclusionPhaseLimits {
            max_inclusions: 1,
            ..DataInclusionPhaseLimits::default()
        });
        let mut raw = Vec::new();
        add_inclusion(&mut raw, 0, 1, [1; 32], &mut budget)?;
        add_inclusion(&mut raw, 1, 0, [1; 32], &mut budget)?;
        let error = freeze_phase(raw, vec![[1; 32]], budget)
            .err()
            .ok_or_else(|| {
                EncodedValidationError::invariant(
                    "data-property inclusion limit unexpectedly succeeded",
                )
            })?;
        assert_eq!(error.code, "NATIVE_ENCODED_RESOURCE_LIMIT");

        let phase = freeze_phase(
            Vec::new(),
            Vec::new(),
            PhaseBudget::new(DataInclusionPhaseLimits::default()),
        )?;
        let limited = DataInclusionPhase {
            manifest_limit: 1,
            ..phase
        };
        let error = limited.canonical_manifest_json().err().ok_or_else(|| {
            EncodedValidationError::invariant(
                "data-property inclusion manifest limit unexpectedly succeeded",
            )
        })?;
        assert_eq!(error.code, "NATIVE_ENCODED_RESOURCE_LIMIT");
        Ok(())
    }
}
