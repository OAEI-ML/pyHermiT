//! Transactional data-property signature construction for encoded-native input.
//!
//! This phase owns the scalar-compatible data-property symbol domain and its
//! canonical top/bottom identifiers. Data-property inclusions, hierarchy,
//! predicates, clauses, and assertions remain explicit later phases.
// SPDX-License-Identifier: LGPL-3.0-or-later

#![forbid(unsafe_code)]

use std::mem::size_of;

use serde::Serialize;

use super::symbols::SymbolPhase;
use super::{EncodedResult, EncodedValidationError};
use crate::input_wire::{DecodedSymbolDomain, DecodedSymbolValue, SymbolKind};

const DATA_ROLE_PHASE_SCHEMA_VERSION: u16 = 1;
const NODE_COMPONENT: u8 = 1;
const DATA_PROPERTY_PREFIX: &str = "data_property:";
const TOP_DATA_IRI: &str = "http://www.w3.org/2002/07/owl#topDataProperty";
const BOTTOM_DATA_IRI: &str = "http://www.w3.org/2002/07/owl#bottomDataProperty";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct DataRolePhaseLimits {
    pub max_slices: usize,
    pub max_properties: usize,
    pub max_owned_bytes: usize,
    pub max_work: u64,
    pub max_manifest_bytes: usize,
}

impl Default for DataRolePhaseLimits {
    fn default() -> Self {
        Self {
            max_slices: 32_769,
            max_properties: 1_000_000,
            max_owned_bytes: 512 * 1024 * 1024,
            max_work: 2_000_000_000,
            max_manifest_bytes: 512 * 1024 * 1024,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DataRolePhase {
    pub data_property_domain: DecodedSymbolDomain,
    pub top_data_property_id: u32,
    pub bottom_data_property_id: u32,
    pub work: u64,
    pub owned_bytes: usize,
    pub(super) manifest_limit: usize,
}

impl DataRolePhase {
    /// Canonical private manifest used for exact scalar differential checks.
    pub fn canonical_manifest_json(&self) -> EncodedResult<Vec<u8>> {
        validate_phase(self)?;
        let data_property_symbols = self
            .data_property_domain
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
        let encoded = serde_json::to_vec(&DataRoleManifest {
            schema_version: DATA_ROLE_PHASE_SCHEMA_VERSION,
            family: "data_property_signature",
            data_property_symbols,
            top_data_property_id: self.top_data_property_id,
            bottom_data_property_id: self.bottom_data_property_id,
        })
        .map_err(|_| {
            EncodedValidationError::invariant("data-property manifest serialization failed")
        })?;
        if encoded.len() > self.manifest_limit {
            return Err(EncodedValidationError::resource(
                "data-property manifest exceeds its byte limit",
            ));
        }
        Ok(encoded)
    }
}

#[derive(Serialize)]
struct DataRoleManifest<'a> {
    schema_version: u16,
    family: &'static str,
    data_property_symbols: Vec<SymbolManifest<'a>>,
    top_data_property_id: u32,
    bottom_data_property_id: u32,
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
    limits: DataRolePhaseLimits,
    work: u64,
    owned_bytes: usize,
}

impl PhaseBudget {
    const fn new(limits: DataRolePhaseLimits) -> Self {
        Self {
            limits,
            work: 0,
            owned_bytes: 0,
        }
    }

    fn claim_work(&mut self, amount: usize) -> EncodedResult<()> {
        let amount = u64::try_from(amount)
            .map_err(|_| EncodedValidationError::resource("data-property work exceeds u64"))?;
        let following = self
            .work
            .checked_add(amount)
            .ok_or_else(|| EncodedValidationError::resource("data-property work overflowed"))?;
        if following > self.limits.max_work {
            return Err(EncodedValidationError::resource(
                "data-property compilation exceeds its work limit",
            ));
        }
        self.work = following;
        Ok(())
    }

    fn claim_owned(&mut self, amount: usize) -> EncodedResult<()> {
        let following = self.owned_bytes.checked_add(amount).ok_or_else(|| {
            EncodedValidationError::resource("data-property owned-byte count overflowed")
        })?;
        if following > self.limits.max_owned_bytes {
            return Err(EncodedValidationError::resource(
                "data-property compilation exceeds its owned-byte limit",
            ));
        }
        self.owned_bytes = following;
        Ok(())
    }
}

/// Build the canonical data-property domain from the semantic entity seed.
pub fn compile_data_role_phase(
    symbols: &SymbolPhase,
    limits: DataRolePhaseLimits,
) -> EncodedResult<DataRolePhase> {
    compile_data_role_domain(&symbols.entity_domain, limits)
}

/// Merge source-local data-property domains through stable canonical keys.
pub fn merge_data_role_phases(
    phases: &[DataRolePhase],
    limits: DataRolePhaseLimits,
) -> EncodedResult<DataRolePhase> {
    if phases.is_empty() {
        return Err(EncodedValidationError::protocol(
            "data-property program merge requires at least one slice",
        ));
    }
    if phases.len() > limits.max_slices {
        return Err(EncodedValidationError::resource(
            "data-property slice count exceeds its limit",
        ));
    }
    let mut budget = PhaseBudget::new(limits);
    let total = phases.iter().try_fold(0_usize, |count, phase| {
        validate_phase(phase)?;
        budget.claim_work(usize::try_from(phase.work).unwrap_or(usize::MAX))?;
        budget.claim_owned(phase.owned_bytes)?;
        count
            .checked_add(phase.data_property_domain.values.len())
            .ok_or_else(|| {
                EncodedValidationError::resource("merged data-property count overflowed")
            })
    })?;
    let mut candidates = Vec::new();
    candidates
        .try_reserve_exact(total)
        .map_err(|_| EncodedValidationError::resource("merged data-property allocation failed"))?;
    for phase in phases {
        for value in &phase.data_property_domain.values {
            budget.claim_work(1)?;
            push_clone(&mut candidates, value, &mut budget)?;
        }
    }
    freeze_properties(candidates, budget)
}

fn compile_data_role_domain(
    entity_domain: &DecodedSymbolDomain,
    limits: DataRolePhaseLimits,
) -> EncodedResult<DataRolePhase> {
    validate_dense_domain(entity_domain, SymbolKind::Entity, "entity")?;
    let mut budget = PhaseBudget::new(limits);
    let mut candidates = Vec::new();
    for value in &entity_domain.values {
        budget.claim_work(1)?;
        let Some(iri) = value.display.strip_prefix(DATA_PROPERTY_PREFIX) else {
            continue;
        };
        let expected = data_property_key(iri, &mut budget)?;
        if expected != value.key {
            return Err(EncodedValidationError::invariant(
                "data-property entity key disagrees with its display",
            ));
        }
        push_clone(&mut candidates, value, &mut budget)?;
    }
    push_builtin(&mut candidates, TOP_DATA_IRI, &mut budget)?;
    push_builtin(&mut candidates, BOTTOM_DATA_IRI, &mut budget)?;
    freeze_properties(candidates, budget)
}

fn freeze_properties(
    mut candidates: Vec<DecodedSymbolValue>,
    mut budget: PhaseBudget,
) -> EncodedResult<DataRolePhase> {
    budget.claim_work(sort_work(candidates.len()))?;
    candidates.sort_by(|left, right| left.key.cmp(&right.key));
    let mut values: Vec<DecodedSymbolValue> = Vec::new();
    values
        .try_reserve_exact(candidates.len())
        .map_err(|_| EncodedValidationError::resource("data-property result allocation failed"))?;
    for mut candidate in candidates {
        if let Some(previous) = values.last() {
            if previous.key == candidate.key {
                if previous.display != candidate.display
                    || previous.generated != candidate.generated
                    || previous.query_local != candidate.query_local
                {
                    return Err(EncodedValidationError::invariant(
                        "data-property key has conflicting symbol metadata",
                    ));
                }
                continue;
            }
        }
        candidate.identifier = u32::try_from(values.len())
            .map_err(|_| EncodedValidationError::resource("data-property symbol ID exceeds u32"))?;
        values.push(candidate);
    }
    if values.len() > budget.limits.max_properties {
        return Err(EncodedValidationError::resource(
            "data-property symbol count exceeds its limit",
        ));
    }
    let top_key = data_property_key(TOP_DATA_IRI, &mut budget)?;
    let bottom_key = data_property_key(BOTTOM_DATA_IRI, &mut budget)?;
    let top_data_property_id = property_id_by_key(&values, &top_key, &mut budget)?;
    let bottom_data_property_id = property_id_by_key(&values, &bottom_key, &mut budget)?;
    let phase = DataRolePhase {
        data_property_domain: DecodedSymbolDomain {
            kind: SymbolKind::DataProperty,
            values,
        },
        top_data_property_id,
        bottom_data_property_id,
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
    let key = data_property_key(iri, budget)?;
    let display = owned_display(iri, budget)?;
    push_value(
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

fn push_value(
    target: &mut Vec<DecodedSymbolValue>,
    value: DecodedSymbolValue,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    budget.claim_owned(size_of::<DecodedSymbolValue>())?;
    budget.claim_owned(value.key.len().saturating_add(value.display.len()))?;
    target
        .try_reserve(1)
        .map_err(|_| EncodedValidationError::resource("data-property allocation failed"))?;
    target.push(value);
    Ok(())
}

fn push_clone(
    target: &mut Vec<DecodedSymbolValue>,
    value: &DecodedSymbolValue,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    budget.claim_owned(size_of::<DecodedSymbolValue>())?;
    budget.claim_owned(value.key.len().saturating_add(value.display.len()))?;
    target
        .try_reserve(1)
        .map_err(|_| EncodedValidationError::resource("data-property allocation failed"))?;
    target.push(value.clone());
    Ok(())
}

fn property_id_by_key(
    values: &[DecodedSymbolValue],
    key: &[u8],
    budget: &mut PhaseBudget,
) -> EncodedResult<u32> {
    budget.claim_work(binary_search_work(values.len()))?;
    let index = values
        .binary_search_by(|candidate| candidate.key.as_slice().cmp(key))
        .map_err(|_| EncodedValidationError::invariant("builtin data property disappeared"))?;
    u32::try_from(index)
        .map_err(|_| EncodedValidationError::resource("data-property symbol ID exceeds u32"))
}

fn data_property_key(iri: &str, budget: &mut PhaseBudget) -> EncodedResult<Vec<u8>> {
    let mut iri_key = Vec::new();
    push_varint(&mut iri_key, 1, budget)?;
    push_byte(&mut iri_key, 2, budget)?;
    push_frame(&mut iri_key, iri.as_bytes(), budget)?;

    let mut entity_key = Vec::new();
    push_varint(&mut entity_key, 2, budget)?;
    push_byte(&mut entity_key, 5, budget)?;
    push_frame(&mut entity_key, b"data_property", budget)?;
    push_byte(&mut entity_key, NODE_COMPONENT, budget)?;
    push_frame(&mut entity_key, &iri_key, budget)?;
    Ok(entity_key)
}

fn owned_display(iri: &str, budget: &mut PhaseBudget) -> EncodedResult<String> {
    let length = DATA_PROPERTY_PREFIX
        .len()
        .checked_add(iri.len())
        .ok_or_else(|| EncodedValidationError::resource("data-property display overflowed"))?;
    budget.claim_owned(length)?;
    let mut display = String::new();
    display
        .try_reserve_exact(length)
        .map_err(|_| EncodedValidationError::resource("data-property display allocation failed"))?;
    display.push_str(DATA_PROPERTY_PREFIX);
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
    target.try_reserve(1).map_err(|_| {
        EncodedValidationError::resource("canonical data-property key allocation failed")
    })?;
    target.push(value);
    Ok(())
}

fn push_bytes(target: &mut Vec<u8>, value: &[u8], budget: &mut PhaseBudget) -> EncodedResult<()> {
    budget.claim_owned(value.len())?;
    target.try_reserve(value.len()).map_err(|_| {
        EncodedValidationError::resource("canonical data-property key allocation failed")
    })?;
    target.extend_from_slice(value);
    Ok(())
}

fn validate_phase(phase: &DataRolePhase) -> EncodedResult<()> {
    validate_dense_domain(
        &phase.data_property_domain,
        SymbolKind::DataProperty,
        "data-property",
    )?;
    for (identifier, expected) in [
        (phase.top_data_property_id, TOP_DATA_IRI),
        (phase.bottom_data_property_id, BOTTOM_DATA_IRI),
    ] {
        let index = usize::try_from(identifier).map_err(|_| {
            EncodedValidationError::invariant("builtin data-property ID exceeds usize")
        })?;
        let value = phase
            .data_property_domain
            .values
            .get(index)
            .ok_or_else(|| {
                EncodedValidationError::invariant("builtin data-property ID is dangling")
            })?;
        if value.display != format!("{DATA_PROPERTY_PREFIX}{expected}") {
            return Err(EncodedValidationError::invariant(
                "builtin data-property ID has the wrong identity",
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
        let mut budget = PhaseBudget::new(DataRolePhaseLimits::default());
        let mut values = Vec::new();
        for iri in iris {
            values.push(DecodedSymbolValue {
                identifier: 0,
                key: data_property_key(iri, &mut budget)?,
                display: format!("{DATA_PROPERTY_PREFIX}{iri}"),
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

    #[test]
    fn data_property_domain_is_canonical_and_includes_builtins() -> EncodedResult<()> {
        let phase = compile_data_role_domain(
            &entity_domain(&["urn:p", "urn:q"])?,
            DataRolePhaseLimits::default(),
        )?;
        assert_eq!(phase.data_property_domain.values.len(), 4);
        assert!(phase
            .data_property_domain
            .values
            .iter()
            .any(|value| value.display == "data_property:urn:p"));
        validate_phase(&phase)
    }

    #[test]
    fn source_local_domains_merge_and_limits_fail_transactionally() -> EncodedResult<()> {
        let left =
            compile_data_role_domain(&entity_domain(&["urn:p"])?, DataRolePhaseLimits::default())?;
        let right = compile_data_role_domain(
            &entity_domain(&["urn:p", "urn:q"])?,
            DataRolePhaseLimits::default(),
        )?;
        let merged = merge_data_role_phases(
            &[left, right],
            DataRolePhaseLimits {
                max_properties: 4,
                ..DataRolePhaseLimits::default()
            },
        )?;
        assert_eq!(merged.data_property_domain.values.len(), 4);

        let error = compile_data_role_domain(
            &entity_domain(&["urn:p"])?,
            DataRolePhaseLimits {
                max_properties: 2,
                ..DataRolePhaseLimits::default()
            },
        )
        .err()
        .ok_or_else(|| {
            EncodedValidationError::invariant("data-property limit unexpectedly succeeded")
        })?;
        assert_eq!(error.code, "NATIVE_ENCODED_RESOURCE_LIMIT");
        validate_phase(&merged)
    }

    #[test]
    fn hostile_key_and_manifest_limit_leave_valid_retry_available() -> EncodedResult<()> {
        let mut hostile = entity_domain(&["urn:p"])?;
        hostile.values[0].key.push(0);
        let error = compile_data_role_domain(&hostile, DataRolePhaseLimits::default())
            .err()
            .ok_or_else(|| {
                EncodedValidationError::invariant("hostile data-property key unexpectedly passed")
            })?;
        assert_eq!(error.code, "NATIVE_ENCODED_INVARIANT");

        let phase =
            compile_data_role_domain(&entity_domain(&["urn:p"])?, DataRolePhaseLimits::default())?;
        let manifest = String::from_utf8(phase.canonical_manifest_json()?).map_err(|_| {
            EncodedValidationError::invariant("data-property manifest is not UTF-8")
        })?;
        assert!(manifest.contains("\"family\":\"data_property_signature\""));
        let limited = DataRolePhase {
            manifest_limit: 1,
            ..phase
        };
        let error = limited.canonical_manifest_json().err().ok_or_else(|| {
            EncodedValidationError::invariant("data-property manifest limit unexpectedly passed")
        })?;
        assert_eq!(error.code, "NATIVE_ENCODED_RESOURCE_LIMIT");
        Ok(())
    }
}
