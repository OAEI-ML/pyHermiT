//! Transactional object-role signature construction for encoded-native input.
//!
//! This phase owns only the scalar-compatible object-role symbol domain and its
//! canonical inverse/top/bottom mapping. Object-property hierarchy axioms,
//! regularity, automata, predicates, clauses, and assertions remain deferred to
//! later phases, so this fragment is never publishable as a reasoning session.
// SPDX-License-Identifier: LGPL-3.0-or-later

#![forbid(unsafe_code)]

use std::mem::size_of;

use serde::Serialize;

use super::symbols::SymbolPhase;
use super::{EncodedResult, EncodedValidationError};
use crate::input_wire::{DecodedSymbolDomain, DecodedSymbolValue, SymbolKind};

const OBJECT_ROLE_PHASE_SCHEMA_VERSION: u16 = 1;
const OBJECT_INVERSE_OF_TAG: u8 = 10;
const NODE_COMPONENT: u8 = 1;
const OBJECT_PROPERTY_PREFIX: &str = "object_property:";
const INVERSE_OBJECT_PROPERTY_PREFIX: &str = "inverse_object_property:";
const TOP_OBJECT_IRI: &str = "http://www.w3.org/2002/07/owl#topObjectProperty";
const BOTTOM_OBJECT_IRI: &str = "http://www.w3.org/2002/07/owl#bottomObjectProperty";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ObjectRolePhaseLimits {
    pub max_slices: usize,
    pub max_roles: usize,
    pub max_owned_bytes: usize,
    pub max_work: u64,
    pub max_manifest_bytes: usize,
}

impl Default for ObjectRolePhaseLimits {
    fn default() -> Self {
        Self {
            max_slices: 32_769,
            max_roles: 1_000_000,
            max_owned_bytes: 512 * 1024 * 1024,
            max_work: 2_000_000_000,
            max_manifest_bytes: 512 * 1024 * 1024,
        }
    }
}

/// Owned output of the object-role signature transaction.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ObjectRolePhase {
    pub object_role_domain: DecodedSymbolDomain,
    pub inverse_role_ids: Vec<u32>,
    pub top_object_role_id: u32,
    pub bottom_object_role_id: u32,
    pub work: u64,
    pub owned_bytes: usize,
    pub(super) manifest_limit: usize,
}

impl ObjectRolePhase {
    /// Canonical private manifest used for exact scalar differential checks.
    pub fn canonical_manifest_json(&self) -> EncodedResult<Vec<u8>> {
        validate_phase(self)?;
        let object_role_symbols = self
            .object_role_domain
            .values
            .iter()
            .map(|value| SymbolManifest {
                identifier: value.identifier,
                key_hex: crate::model::hex(&value.key),
                display: &value.display,
                generated: value.generated,
                query_local: value.query_local,
            })
            .collect();
        let encoded = serde_json::to_vec(&ObjectRoleManifest {
            schema_version: OBJECT_ROLE_PHASE_SCHEMA_VERSION,
            family: "object_role_signature",
            object_role_symbols,
            inverse_role_ids: &self.inverse_role_ids,
            top_object_role_id: self.top_object_role_id,
            bottom_object_role_id: self.bottom_object_role_id,
        })
        .map_err(|_| {
            EncodedValidationError::invariant("object-role manifest serialization failed")
        })?;
        if encoded.len() > self.manifest_limit {
            return Err(EncodedValidationError::resource(
                "object-role manifest exceeds its byte limit",
            ));
        }
        Ok(encoded)
    }
}

#[derive(Serialize)]
struct ObjectRoleManifest<'a> {
    schema_version: u16,
    family: &'static str,
    object_role_symbols: Vec<SymbolManifest<'a>>,
    inverse_role_ids: &'a [u32],
    top_object_role_id: u32,
    bottom_object_role_id: u32,
}

#[derive(Serialize)]
struct SymbolManifest<'a> {
    identifier: u32,
    key_hex: String,
    display: &'a str,
    generated: bool,
    query_local: bool,
}

struct PhaseBudget {
    limits: ObjectRolePhaseLimits,
    work: u64,
    owned_bytes: usize,
}

impl PhaseBudget {
    const fn new(limits: ObjectRolePhaseLimits) -> Self {
        Self {
            limits,
            work: 0,
            owned_bytes: 0,
        }
    }

    fn claim_work(&mut self, amount: usize) -> EncodedResult<()> {
        let amount = u64::try_from(amount)
            .map_err(|_| EncodedValidationError::resource("object-role work exceeds u64"))?;
        let following = self
            .work
            .checked_add(amount)
            .ok_or_else(|| EncodedValidationError::resource("object-role work overflowed"))?;
        if following > self.limits.max_work {
            return Err(EncodedValidationError::resource(
                "object-role compilation exceeds its work limit",
            ));
        }
        self.work = following;
        Ok(())
    }

    fn claim_owned(&mut self, amount: usize) -> EncodedResult<()> {
        let following = self.owned_bytes.checked_add(amount).ok_or_else(|| {
            EncodedValidationError::resource("object-role owned-byte count overflowed")
        })?;
        if following > self.limits.max_owned_bytes {
            return Err(EncodedValidationError::resource(
                "object-role compilation exceeds its owned-byte limit",
            ));
        }
        self.owned_bytes = following;
        Ok(())
    }

    fn roles(&self, count: usize) -> EncodedResult<()> {
        if count > self.limits.max_roles {
            Err(EncodedValidationError::resource(
                "object-role symbol count exceeds its limit",
            ))
        } else {
            Ok(())
        }
    }
}

/// Build the canonical role domain from the already-owned semantic entity seed.
pub fn compile_object_role_phase(
    symbols: &SymbolPhase,
    limits: ObjectRolePhaseLimits,
) -> EncodedResult<ObjectRolePhase> {
    compile_object_role_domain(&symbols.entity_domain, limits)
}

fn compile_object_role_domain(
    entity_domain: &DecodedSymbolDomain,
    limits: ObjectRolePhaseLimits,
) -> EncodedResult<ObjectRolePhase> {
    validate_dense_domain(entity_domain, SymbolKind::Entity, "entity")?;
    let mut budget = PhaseBudget::new(limits);
    let mut candidates = Vec::new();
    for value in &entity_domain.values {
        budget.claim_work(1)?;
        let Some(iri) = value.display.strip_prefix(OBJECT_PROPERTY_PREFIX) else {
            continue;
        };
        let expected = object_property_key(iri, &mut budget)?;
        if expected != value.key {
            return Err(EncodedValidationError::invariant(
                "object-property entity key disagrees with its display",
            ));
        }
        push_role_clone(&mut candidates, value, &mut budget)?;
        if !is_builtin(iri) {
            let inverse = inverse_symbol(value, iri, &mut budget)?;
            push_role(&mut candidates, inverse, &mut budget)?;
        }
    }
    push_builtin(&mut candidates, TOP_OBJECT_IRI, &mut budget)?;
    push_builtin(&mut candidates, BOTTOM_OBJECT_IRI, &mut budget)?;
    freeze_roles(candidates, budget)
}

/// Merge source-local role domains through their stable canonical keys.
pub fn merge_object_role_phases(
    phases: &[ObjectRolePhase],
    limits: ObjectRolePhaseLimits,
) -> EncodedResult<ObjectRolePhase> {
    if phases.is_empty() {
        return Err(EncodedValidationError::protocol(
            "object-role program merge requires at least one slice",
        ));
    }
    if phases.len() > limits.max_slices {
        return Err(EncodedValidationError::resource(
            "object-role slice count exceeds its limit",
        ));
    }
    let mut budget = PhaseBudget::new(limits);
    let total = phases.iter().try_fold(0_usize, |count, phase| {
        validate_phase(phase)?;
        budget.claim_work(usize::try_from(phase.work).unwrap_or(usize::MAX))?;
        budget.claim_owned(phase.owned_bytes)?;
        count
            .checked_add(phase.object_role_domain.values.len())
            .ok_or_else(|| EncodedValidationError::resource("merged object-role count overflowed"))
    })?;
    let mut candidates = Vec::new();
    candidates
        .try_reserve_exact(total)
        .map_err(|_| EncodedValidationError::resource("merged object-role allocation failed"))?;
    for phase in phases {
        for value in &phase.object_role_domain.values {
            budget.claim_work(1)?;
            push_role_clone(&mut candidates, value, &mut budget)?;
        }
    }
    freeze_roles(candidates, budget)
}

fn freeze_roles(
    mut candidates: Vec<DecodedSymbolValue>,
    mut budget: PhaseBudget,
) -> EncodedResult<ObjectRolePhase> {
    budget.claim_work(sort_work(candidates.len()))?;
    candidates.sort_by(|left, right| left.key.cmp(&right.key));
    let mut values: Vec<DecodedSymbolValue> = Vec::new();
    values
        .try_reserve_exact(candidates.len())
        .map_err(|_| EncodedValidationError::resource("object-role result allocation failed"))?;
    for mut candidate in candidates {
        if let Some(previous) = values.last() {
            if previous.key == candidate.key {
                if previous.display != candidate.display
                    || previous.generated != candidate.generated
                    || previous.query_local != candidate.query_local
                {
                    return Err(EncodedValidationError::invariant(
                        "object-role key has conflicting symbol metadata",
                    ));
                }
                continue;
            }
        }
        candidate.identifier = u32::try_from(values.len())
            .map_err(|_| EncodedValidationError::resource("object-role symbol ID exceeds u32"))?;
        values.push(candidate);
    }
    budget.roles(values.len())?;

    let top_key = object_property_key(TOP_OBJECT_IRI, &mut budget)?;
    let bottom_key = object_property_key(BOTTOM_OBJECT_IRI, &mut budget)?;
    let top_object_role_id = role_id_by_key(&values, &top_key, &mut budget)?;
    let bottom_object_role_id = role_id_by_key(&values, &bottom_key, &mut budget)?;
    let mut inverse_role_ids = Vec::new();
    budget.claim_owned(
        values
            .len()
            .checked_mul(size_of::<u32>())
            .ok_or_else(|| EncodedValidationError::resource("inverse-role output overflowed"))?,
    )?;
    inverse_role_ids
        .try_reserve_exact(values.len())
        .map_err(|_| EncodedValidationError::resource("inverse-role output allocation failed"))?;
    for value in &values {
        budget.claim_work(1)?;
        let inverse_key = counterpart_key(value, &mut budget)?;
        inverse_role_ids.push(role_id_by_key(&values, &inverse_key, &mut budget)?);
    }
    let phase = ObjectRolePhase {
        object_role_domain: DecodedSymbolDomain {
            kind: SymbolKind::ObjectRole,
            values,
        },
        inverse_role_ids,
        top_object_role_id,
        bottom_object_role_id,
        work: budget.work,
        owned_bytes: budget.owned_bytes,
        manifest_limit: budget.limits.max_manifest_bytes,
    };
    validate_phase(&phase)?;
    Ok(phase)
}

fn push_builtin(
    target: &mut Vec<DecodedSymbolValue>,
    iri: &str,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    let key = object_property_key(iri, budget)?;
    let display = owned_display(OBJECT_PROPERTY_PREFIX, iri, budget)?;
    push_role(
        target,
        DecodedSymbolValue {
            identifier: 0,
            key,
            display,
            generated: false,
            query_local: false,
        },
        budget,
    )
}

fn inverse_symbol(
    forward: &DecodedSymbolValue,
    iri: &str,
    budget: &mut PhaseBudget,
) -> EncodedResult<DecodedSymbolValue> {
    Ok(DecodedSymbolValue {
        identifier: 0,
        key: object_inverse_key(&forward.key, budget)?,
        display: owned_display(INVERSE_OBJECT_PROPERTY_PREFIX, iri, budget)?,
        generated: forward.generated,
        query_local: forward.query_local,
    })
}

fn push_role(
    target: &mut Vec<DecodedSymbolValue>,
    value: DecodedSymbolValue,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    budget.claim_owned(size_of::<DecodedSymbolValue>())?;
    budget.claim_owned(value.key.len().saturating_add(value.display.len()))?;
    target
        .try_reserve(1)
        .map_err(|_| EncodedValidationError::resource("object-role allocation failed"))?;
    target.push(value);
    Ok(())
}

fn push_role_clone(
    target: &mut Vec<DecodedSymbolValue>,
    value: &DecodedSymbolValue,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    budget.claim_owned(size_of::<DecodedSymbolValue>())?;
    budget.claim_owned(value.key.len().saturating_add(value.display.len()))?;
    target
        .try_reserve(1)
        .map_err(|_| EncodedValidationError::resource("object-role allocation failed"))?;
    target.push(value.clone());
    Ok(())
}

fn counterpart_key(value: &DecodedSymbolValue, budget: &mut PhaseBudget) -> EncodedResult<Vec<u8>> {
    if let Some(iri) = value.display.strip_prefix(OBJECT_PROPERTY_PREFIX) {
        let expected = object_property_key(iri, budget)?;
        if expected != value.key {
            return Err(EncodedValidationError::invariant(
                "object-role key disagrees with its forward display",
            ));
        }
        if is_builtin(iri) {
            budget.claim_owned(value.key.len())?;
            return Ok(value.key.clone());
        }
        object_inverse_key(&value.key, budget)
    } else if let Some(iri) = value.display.strip_prefix(INVERSE_OBJECT_PROPERTY_PREFIX) {
        if is_builtin(iri) {
            return Err(EncodedValidationError::invariant(
                "self-inverse builtin was wrapped as an inverse role",
            ));
        }
        let forward = object_property_key(iri, budget)?;
        let expected = object_inverse_key(&forward, budget)?;
        if expected != value.key {
            return Err(EncodedValidationError::invariant(
                "object-role key disagrees with its inverse display",
            ));
        }
        Ok(forward)
    } else {
        Err(EncodedValidationError::invariant(
            "object-role display has an unsupported form",
        ))
    }
}

fn role_id_by_key(
    values: &[DecodedSymbolValue],
    key: &[u8],
    budget: &mut PhaseBudget,
) -> EncodedResult<u32> {
    budget.claim_work(binary_search_work(values.len()))?;
    let index = values
        .binary_search_by(|candidate| candidate.key.as_slice().cmp(key))
        .map_err(|_| EncodedValidationError::invariant("inverse object role disappeared"))?;
    u32::try_from(index)
        .map_err(|_| EncodedValidationError::resource("object-role symbol ID exceeds u32"))
}

fn object_property_key(iri: &str, budget: &mut PhaseBudget) -> EncodedResult<Vec<u8>> {
    let mut iri_key = Vec::new();
    push_varint(&mut iri_key, 1, budget)?;
    push_byte(&mut iri_key, 2, budget)?;
    push_frame(&mut iri_key, iri.as_bytes(), budget)?;

    let mut entity_key = Vec::new();
    push_varint(&mut entity_key, 2, budget)?;
    push_byte(&mut entity_key, 5, budget)?;
    push_frame(&mut entity_key, b"object_property", budget)?;
    push_byte(&mut entity_key, NODE_COMPONENT, budget)?;
    push_frame(&mut entity_key, &iri_key, budget)?;
    Ok(entity_key)
}

fn object_inverse_key(forward: &[u8], budget: &mut PhaseBudget) -> EncodedResult<Vec<u8>> {
    let mut key = Vec::new();
    push_varint(&mut key, u64::from(OBJECT_INVERSE_OF_TAG), budget)?;
    push_byte(&mut key, NODE_COMPONENT, budget)?;
    push_frame(&mut key, forward, budget)?;
    Ok(key)
}

fn owned_display(prefix: &str, iri: &str, budget: &mut PhaseBudget) -> EncodedResult<String> {
    let length = prefix
        .len()
        .checked_add(iri.len())
        .ok_or_else(|| EncodedValidationError::resource("object-role display overflowed"))?;
    budget.claim_owned(length)?;
    let mut display = String::new();
    display
        .try_reserve_exact(length)
        .map_err(|_| EncodedValidationError::resource("object-role display allocation failed"))?;
    display.push_str(prefix);
    display.push_str(iri);
    Ok(display)
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
        .map_err(|_| EncodedValidationError::resource("canonical role key allocation failed"))?;
    target.push(value);
    Ok(())
}

fn push_bytes(target: &mut Vec<u8>, value: &[u8], budget: &mut PhaseBudget) -> EncodedResult<()> {
    budget.claim_owned(value.len())?;
    target
        .try_reserve(value.len())
        .map_err(|_| EncodedValidationError::resource("canonical role key allocation failed"))?;
    target.extend_from_slice(value);
    Ok(())
}

fn validate_phase(phase: &ObjectRolePhase) -> EncodedResult<()> {
    validate_dense_domain(
        &phase.object_role_domain,
        SymbolKind::ObjectRole,
        "object-role",
    )?;
    let values = &phase.object_role_domain.values;
    if phase.inverse_role_ids.len() != values.len() {
        return Err(EncodedValidationError::invariant(
            "inverse-role mapping no longer covers its domain",
        ));
    }
    for (role, inverse) in phase.inverse_role_ids.iter().copied().enumerate() {
        let inverse = usize::try_from(inverse)
            .map_err(|_| EncodedValidationError::invariant("inverse-role ID exceeds usize"))?;
        let reverse = phase
            .inverse_role_ids
            .get(inverse)
            .copied()
            .ok_or_else(|| EncodedValidationError::invariant("inverse-role ID is dangling"))?;
        if usize::try_from(reverse).ok() != Some(role) {
            return Err(EncodedValidationError::invariant(
                "inverse-role mapping is not involutive",
            ));
        }
    }
    for (identifier, expected) in [
        (phase.top_object_role_id, TOP_OBJECT_IRI),
        (phase.bottom_object_role_id, BOTTOM_OBJECT_IRI),
    ] {
        let index = usize::try_from(identifier).map_err(|_| {
            EncodedValidationError::invariant("builtin object-role ID exceeds usize")
        })?;
        let value = values.get(index).ok_or_else(|| {
            EncodedValidationError::invariant("builtin object-role ID is dangling")
        })?;
        if value.display != format!("{OBJECT_PROPERTY_PREFIX}{expected}") {
            return Err(EncodedValidationError::invariant(
                "builtin object-role ID has the wrong identity",
            ));
        }
        if phase.inverse_role_ids.get(index).copied() != Some(identifier) {
            return Err(EncodedValidationError::invariant(
                "builtin object role is not self-inverse",
            ));
        }
    }
    Ok(())
}

fn validate_dense_domain(
    domain: &DecodedSymbolDomain,
    kind: SymbolKind,
    name: &'static str,
) -> EncodedResult<()> {
    if domain.kind != kind {
        return Err(EncodedValidationError::invariant(format!(
            "{name} symbol domain changed kind"
        )));
    }
    for (index, value) in domain.values.iter().enumerate() {
        if usize::try_from(value.identifier).ok() != Some(index) {
            return Err(EncodedValidationError::invariant(format!(
                "{name} symbol IDs are not dense"
            )));
        }
        if index > 0 && domain.values[index - 1].key >= value.key {
            return Err(EncodedValidationError::invariant(format!(
                "{name} symbol keys are not canonical"
            )));
        }
    }
    Ok(())
}

fn is_builtin(iri: &str) -> bool {
    matches!(iri, TOP_OBJECT_IRI | BOTTOM_OBJECT_IRI)
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

    fn entity_domain(iris: &[&str]) -> EncodedResult<DecodedSymbolDomain> {
        let mut budget = PhaseBudget::new(ObjectRolePhaseLimits::default());
        let mut values = Vec::new();
        for iri in iris {
            values.push(DecodedSymbolValue {
                identifier: 0,
                key: object_property_key(iri, &mut budget)?,
                display: format!("{OBJECT_PROPERTY_PREFIX}{iri}"),
                generated: false,
                query_local: false,
            });
        }
        values.sort_by(|left, right| left.key.cmp(&right.key));
        for (index, value) in values.iter_mut().enumerate() {
            value.identifier = u32::try_from(index).map_err(|_| {
                EncodedValidationError::resource("test entity symbol ID exceeds u32")
            })?;
        }
        Ok(DecodedSymbolDomain {
            kind: SymbolKind::Entity,
            values,
        })
    }

    fn role_id(phase: &ObjectRolePhase, display: &str) -> EncodedResult<u32> {
        phase
            .object_role_domain
            .values
            .iter()
            .find(|value| value.display == display)
            .map(|value| value.identifier)
            .ok_or_else(|| EncodedValidationError::invariant("test object role is absent"))
    }

    #[test]
    fn object_role_domain_uses_scalar_keys_and_involutive_inverse_ids() -> EncodedResult<()> {
        let phase = compile_object_role_domain(
            &entity_domain(&["urn:p", "urn:q"])?,
            ObjectRolePhaseLimits::default(),
        )?;
        let p = role_id(&phase, "object_property:urn:p")?;
        let inverse_p = role_id(&phase, "inverse_object_property:urn:p")?;
        let p_index = usize::try_from(p)
            .map_err(|_| EncodedValidationError::invariant("test role ID exceeds usize"))?;
        let inverse_p_index = usize::try_from(inverse_p)
            .map_err(|_| EncodedValidationError::invariant("test inverse ID exceeds usize"))?;
        assert_eq!(phase.inverse_role_ids[p_index], inverse_p);
        assert_eq!(phase.inverse_role_ids[inverse_p_index], p);
        assert_eq!(
            phase.object_role_domain.values[p_index].key.as_slice(),
            &[
                0x02, 0x05, 0x0f, b'o', b'b', b'j', b'e', b'c', b't', b'_', b'p', b'r', b'o', b'p',
                b'e', b'r', b't', b'y', 0x01, 0x08, 0x01, 0x02, 0x05, b'u', b'r', b'n', b':', b'p',
            ]
        );
        let top_index = usize::try_from(phase.top_object_role_id)
            .map_err(|_| EncodedValidationError::invariant("test top role ID exceeds usize"))?;
        let bottom_index = usize::try_from(phase.bottom_object_role_id)
            .map_err(|_| EncodedValidationError::invariant("test bottom role ID exceeds usize"))?;
        assert_eq!(phase.inverse_role_ids[top_index], phase.top_object_role_id);
        assert_eq!(
            phase.inverse_role_ids[bottom_index],
            phase.bottom_object_role_id
        );
        assert_eq!(phase.object_role_domain.values.len(), 6);
        Ok(())
    }

    #[test]
    fn source_local_domains_merge_canonically_and_deduplicate_roles() -> EncodedResult<()> {
        let left = compile_object_role_domain(
            &entity_domain(&["urn:p"])?,
            ObjectRolePhaseLimits::default(),
        )?;
        let right = compile_object_role_domain(
            &entity_domain(&["urn:p", "urn:q"])?,
            ObjectRolePhaseLimits::default(),
        )?;
        let limits = ObjectRolePhaseLimits {
            max_roles: 6,
            ..ObjectRolePhaseLimits::default()
        };
        let merged = merge_object_role_phases(&[left, right], limits)?;
        assert_eq!(merged.object_role_domain.values.len(), 6);
        assert!(merged
            .object_role_domain
            .values
            .iter()
            .any(|value| value.display == "inverse_object_property:urn:q"));
        validate_phase(&merged)
    }

    #[test]
    fn hostile_entity_key_and_role_limit_fail_without_reusing_partial_output() -> EncodedResult<()>
    {
        let mut hostile = entity_domain(&["urn:p"])?;
        hostile.values[0].key.push(0);
        let Err(error) = compile_object_role_domain(&hostile, ObjectRolePhaseLimits::default())
        else {
            return Err(EncodedValidationError::invariant(
                "hostile entity key unexpectedly succeeded",
            ));
        };
        assert_eq!(error.code, "NATIVE_ENCODED_INVARIANT");

        let limits = ObjectRolePhaseLimits {
            max_roles: 3,
            ..ObjectRolePhaseLimits::default()
        };
        let Err(error) = compile_object_role_domain(&entity_domain(&["urn:p"])?, limits) else {
            return Err(EncodedValidationError::invariant(
                "object-role limit unexpectedly succeeded",
            ));
        };
        assert_eq!(error.code, "NATIVE_ENCODED_RESOURCE_LIMIT");

        let retry = compile_object_role_domain(
            &entity_domain(&["urn:p"])?,
            ObjectRolePhaseLimits::default(),
        )?;
        validate_phase(&retry)
    }

    #[test]
    fn manifest_is_bounded_and_identifies_the_signature_only_phase() -> EncodedResult<()> {
        let phase = compile_object_role_domain(
            &entity_domain(&["urn:p"])?,
            ObjectRolePhaseLimits::default(),
        )?;
        let manifest = String::from_utf8(phase.canonical_manifest_json()?)
            .map_err(|_| EncodedValidationError::invariant("object-role manifest is not UTF-8"))?;
        assert!(manifest.contains("\"family\":\"object_role_signature\""));

        let limited = ObjectRolePhase {
            manifest_limit: 1,
            ..phase
        };
        let Err(error) = limited.canonical_manifest_json() else {
            return Err(EncodedValidationError::invariant(
                "object-role manifest limit unexpectedly succeeded",
            ));
        };
        assert_eq!(error.code, "NATIVE_ENCODED_RESOURCE_LIMIT");
        Ok(())
    }
}
