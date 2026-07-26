//! Canonical owned role-model IR assembly.
//!
//! This transaction freezes the independently verified object/data-property
//! phases into the exact language-neutral `DecodedRoleModel` consumed by the
//! native permanent-session bridge.  It performs no session publication and
//! does not advertise the encoded compiler capability.
// SPDX-License-Identifier: LGPL-3.0-or-later

#![forbid(unsafe_code)]

use std::cmp::Ordering;
use std::mem::size_of;

use serde::ser::SerializeSeq;
use serde::{Serialize, Serializer};

use super::complex_roles::ComplexRolePhase;
use super::data_inclusions::DataInclusionPhase;
use super::data_roles::DataRolePhase;
use super::object_role_hierarchy::ObjectRoleHierarchyPhase;
use super::object_roles::ObjectRolePhase;
use super::role_automata::RoleAutomataPhase;
use super::role_semantics::RoleSemanticsPhase;
use super::simple_roles::SimpleRolePhase;
use super::{EncodedResult, EncodedValidationError};
use crate::input_wire::{
    DecodedRoleAutomaton, DecodedRoleModel, DecodedRoleTransition, SymbolKind,
};
use crate::model::IR_SCHEMA_VERSION;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RoleModelPhaseLimits {
    pub max_object_roles: usize,
    pub max_data_properties: usize,
    pub max_components: usize,
    pub max_simple_inclusions: usize,
    pub max_data_inclusions: usize,
    pub max_complex_inclusions: usize,
    pub max_chain_items: usize,
    pub max_automata: usize,
    pub max_states: usize,
    pub max_transitions: usize,
    pub max_owned_bytes: usize,
    pub max_work: u64,
    pub max_manifest_bytes: usize,
}

impl Default for RoleModelPhaseLimits {
    fn default() -> Self {
        Self {
            max_object_roles: 1_000_000,
            max_data_properties: 1_000_000,
            max_components: 1_000_000,
            max_simple_inclusions: 100_000_000,
            max_data_inclusions: 100_000_000,
            max_complex_inclusions: 1_000_000,
            max_chain_items: 100_000_000,
            max_automata: 1_000_000,
            max_states: 5_000_000,
            max_transitions: 20_000_000,
            max_owned_bytes: 512 * 1024 * 1024,
            max_work: 2_000_000_000,
            max_manifest_bytes: 512 * 1024 * 1024,
        }
    }
}

/// Complete owned role fragment in native input-IR form.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RoleModelPhase {
    pub role_model: DecodedRoleModel,
    pub work: u64,
    pub owned_bytes: usize,
    component_count: usize,
    manifest_limit: usize,
}

impl RoleModelPhase {
    /// Serialize byte-for-byte as scalar `RoleModelIR.canonical_bytes()`.
    pub fn canonical_manifest_json(&self) -> EncodedResult<Vec<u8>> {
        validate_role_model(&self.role_model, self.component_count)?;
        let transition_orders =
            canonical_transition_orders(&self.role_model.automata, self.manifest_limit)?;
        let encoded = serde_json::to_vec(&CanonicalRoleModel::new(
            &self.role_model,
            &transition_orders,
        ))
        .map_err(|_| EncodedValidationError::invariant("role-model serialization failed"))?;
        if encoded.len() > self.manifest_limit {
            return Err(EncodedValidationError::resource(
                "role-model manifest exceeds its byte limit",
            ));
        }
        Ok(encoded)
    }
}

#[derive(Serialize)]
pub(crate) struct CanonicalRoleModel<'a> {
    automata: AutomataManifest<'a>,
    bottom_data_property_id: u32,
    bottom_object_role_id: u32,
    complex_inclusions: &'a [(Vec<u32>, u32)],
    data_inclusions: &'a [(u32, u32)],
    data_property_count: u32,
    inverse_role_ids: &'a [u32],
    non_simple_components: &'a [u32],
    object_role_count: u32,
    schema_version: u16,
    simple_inclusions: &'a [(u32, u32)],
    top_data_property_id: u32,
    top_object_role_id: u32,
    #[serde(rename = "type")]
    record_type: &'static str,
}

impl<'a> CanonicalRoleModel<'a> {
    pub(crate) fn new(value: &'a DecodedRoleModel, transition_orders: &'a [Vec<usize>]) -> Self {
        Self {
            automata: AutomataManifest {
                values: &value.automata,
                transition_orders,
            },
            bottom_data_property_id: value.bottom_data_property_id,
            bottom_object_role_id: value.bottom_object_role_id,
            complex_inclusions: &value.complex_inclusions,
            data_inclusions: &value.data_inclusions,
            data_property_count: value.data_property_count,
            inverse_role_ids: &value.inverse_role_ids,
            non_simple_components: &value.non_simple_components,
            object_role_count: value.object_role_count,
            schema_version: IR_SCHEMA_VERSION,
            simple_inclusions: &value.simple_inclusions,
            top_data_property_id: value.top_data_property_id,
            top_object_role_id: value.top_object_role_id,
            record_type: "RoleModelIR",
        }
    }
}

struct AutomataManifest<'a> {
    values: &'a [DecodedRoleAutomaton],
    transition_orders: &'a [Vec<usize>],
}

impl Serialize for AutomataManifest<'_> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        if self.values.len() != self.transition_orders.len() {
            return Err(serde::ser::Error::custom(
                "canonical role automata order has the wrong length",
            ));
        }
        let mut sequence = serializer.serialize_seq(Some(self.values.len()))?;
        for (automaton, order) in self.values.iter().zip(self.transition_orders) {
            sequence.serialize_element(&AutomatonManifest {
                component_id: automaton.component_id,
                final_states: &automaton.final_states,
                initial_state: automaton.initial_state,
                schema_version: IR_SCHEMA_VERSION,
                state_count: automaton.state_count,
                transitions: TransitionsManifest {
                    values: &automaton.transitions,
                    order,
                },
                record_type: "RoleAutomatonIR",
            })?;
        }
        sequence.end()
    }
}

#[derive(Serialize)]
struct AutomatonManifest<'a> {
    component_id: u32,
    final_states: &'a [u32],
    initial_state: u32,
    schema_version: u16,
    state_count: u32,
    transitions: TransitionsManifest<'a>,
    #[serde(rename = "type")]
    record_type: &'static str,
}

struct TransitionsManifest<'a> {
    values: &'a [DecodedRoleTransition],
    order: &'a [usize],
}

impl Serialize for TransitionsManifest<'_> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        if self.values.len() != self.order.len() {
            return Err(serde::ser::Error::custom(
                "canonical role transition order has the wrong length",
            ));
        }
        let mut sequence = serializer.serialize_seq(Some(self.order.len()))?;
        for &index in self.order {
            let transition = self.values.get(index).ok_or_else(|| {
                serde::ser::Error::custom("canonical role transition order is dangling")
            })?;
            sequence.serialize_element(&TransitionManifest {
                role_id: transition.role_id,
                schema_version: IR_SCHEMA_VERSION,
                source_state: transition.source_state,
                target_state: transition.target_state,
                record_type: "RoleTransitionIR",
            })?;
        }
        sequence.end()
    }
}

#[derive(Serialize)]
struct TransitionManifest {
    role_id: Option<u32>,
    schema_version: u16,
    source_state: u32,
    target_state: u32,
    #[serde(rename = "type")]
    record_type: &'static str,
}

struct PhaseBudget {
    limits: RoleModelPhaseLimits,
    work: u64,
    owned_bytes: usize,
}

impl PhaseBudget {
    const fn new(limits: RoleModelPhaseLimits) -> Self {
        Self {
            limits,
            work: 0,
            owned_bytes: 0,
        }
    }

    fn claim_work(&mut self, amount: usize) -> EncodedResult<()> {
        let amount = u64::try_from(amount)
            .map_err(|_| EncodedValidationError::resource("role-model work exceeds u64"))?;
        let following = self
            .work
            .checked_add(amount)
            .ok_or_else(|| EncodedValidationError::resource("role-model work overflowed"))?;
        if following > self.limits.max_work {
            return Err(EncodedValidationError::resource(
                "role-model assembly exceeds its work limit",
            ));
        }
        self.work = following;
        Ok(())
    }

    fn claim_owned(&mut self, amount: usize) -> EncodedResult<()> {
        let following = self.owned_bytes.checked_add(amount).ok_or_else(|| {
            EncodedValidationError::resource("role-model owned-byte count overflowed")
        })?;
        if following > self.limits.max_owned_bytes {
            return Err(EncodedValidationError::resource(
                "role-model assembly exceeds its owned-byte limit",
            ));
        }
        self.owned_bytes = following;
        Ok(())
    }
}

/// Freeze the complete scalar-compatible role IR without publishing a session.
#[allow(clippy::too_many_arguments)]
pub fn compile_role_model_phase(
    object_roles: &ObjectRolePhase,
    data_roles: &DataRolePhase,
    simple: &SimpleRolePhase,
    data: &DataInclusionPhase,
    complex: &ComplexRolePhase,
    hierarchy: &ObjectRoleHierarchyPhase,
    semantics: &RoleSemanticsPhase,
    automata: &RoleAutomataPhase,
    limits: RoleModelPhaseLimits,
) -> EncodedResult<RoleModelPhase> {
    validate_inputs(
        object_roles,
        data_roles,
        simple,
        data,
        complex,
        hierarchy,
        semantics,
        automata,
        limits,
    )?;
    let mut budget = PhaseBudget::new(limits);
    let object_role_count = u32_id(object_roles.object_role_domain.values.len())?;
    let data_property_count = u32_id(data_roles.data_property_domain.values.len())?;
    let inverse_role_ids = copy_u32(
        &object_roles.inverse_role_ids,
        "inverse role map",
        &mut budget,
    )?;
    let simple_inclusions = copy_pairs(
        simple
            .simple_inclusions
            .iter()
            .map(|value| (value.sub_role_id, value.super_role_id)),
        "simple role inclusions",
        &mut budget,
    )?;
    let data_inclusions = copy_pairs(
        data.data_inclusions
            .iter()
            .map(|value| (value.sub_property_id, value.super_property_id)),
        "data-property inclusions",
        &mut budget,
    )?;
    let complex_inclusions = freeze_complex_inclusions(complex, &mut budget)?;
    let non_simple_components = copy_u32(
        &semantics.non_simple_components,
        "non-simple components",
        &mut budget,
    )?;
    let frozen_automata = freeze_automata(automata, &mut budget)?;
    let role_model = DecodedRoleModel {
        object_role_count,
        data_property_count,
        inverse_role_ids,
        simple_inclusions,
        data_inclusions,
        complex_inclusions,
        non_simple_components,
        automata: frozen_automata,
        top_object_role_id: object_roles.top_object_role_id,
        bottom_object_role_id: object_roles.bottom_object_role_id,
        top_data_property_id: data_roles.top_data_property_id,
        bottom_data_property_id: data_roles.bottom_data_property_id,
    };
    validate_role_model(&role_model, hierarchy.object_components.len())?;
    Ok(RoleModelPhase {
        role_model,
        work: budget.work,
        owned_bytes: budget.owned_bytes,
        component_count: hierarchy.object_components.len(),
        manifest_limit: limits.max_manifest_bytes,
    })
}

#[allow(clippy::too_many_arguments)]
fn validate_inputs(
    object_roles: &ObjectRolePhase,
    data_roles: &DataRolePhase,
    simple: &SimpleRolePhase,
    data: &DataInclusionPhase,
    complex: &ComplexRolePhase,
    hierarchy: &ObjectRoleHierarchyPhase,
    semantics: &RoleSemanticsPhase,
    automata: &RoleAutomataPhase,
    limits: RoleModelPhaseLimits,
) -> EncodedResult<()> {
    if object_roles.object_role_domain.kind != SymbolKind::ObjectRole
        || data_roles.data_property_domain.kind != SymbolKind::DataProperty
    {
        return Err(EncodedValidationError::invariant(
            "role-model assembly received a wrong symbol domain",
        ));
    }
    let object_count = object_roles.object_role_domain.values.len();
    let data_count = data_roles.data_property_domain.values.len();
    if object_count == 0 || object_count > limits.max_object_roles {
        return Err(EncodedValidationError::resource(
            "role-model object-role count exceeds its limit",
        ));
    }
    if data_count == 0 || data_count > limits.max_data_properties {
        return Err(EncodedValidationError::resource(
            "role-model data-property count exceeds its limit",
        ));
    }
    let component_count = hierarchy.object_components.len();
    if component_count == 0 || component_count > limits.max_components {
        return Err(EncodedValidationError::resource(
            "role-model component count exceeds its limit",
        ));
    }
    count_limit(
        simple.simple_inclusions.len(),
        limits.max_simple_inclusions,
        "simple inclusion",
    )?;
    count_limit(
        data.data_inclusions.len(),
        limits.max_data_inclusions,
        "data inclusion",
    )?;
    count_limit(
        complex.complex_inclusions.len(),
        limits.max_complex_inclusions,
        "complex inclusion",
    )?;
    count_limit(automata.automata.len(), limits.max_automata, "automaton")?;
    if object_roles.inverse_role_ids.len() != object_count {
        return Err(EncodedValidationError::invariant(
            "role-model inverse map is incomplete",
        ));
    }
    for (role, &inverse) in object_roles.inverse_role_ids.iter().enumerate() {
        let inverse_index = usize_id(inverse)?;
        if inverse_index >= object_count
            || object_roles.inverse_role_ids[inverse_index] != u32_id(role)?
        {
            return Err(EncodedValidationError::invariant(
                "role-model inverse map is not an in-range involution",
            ));
        }
    }
    validate_id(
        object_roles.top_object_role_id,
        object_count,
        "top object role",
    )?;
    validate_id(
        object_roles.bottom_object_role_id,
        object_count,
        "bottom object role",
    )?;
    validate_id(
        data_roles.top_data_property_id,
        data_count,
        "top data property",
    )?;
    validate_id(
        data_roles.bottom_data_property_id,
        data_count,
        "bottom data property",
    )?;
    if hierarchy.object_component_by_role.len() != object_count {
        return Err(EncodedValidationError::invariant(
            "role-model hierarchy does not cover the object-role domain",
        ));
    }
    if semantics
        .non_simple_components
        .iter()
        .any(|&value| id_is_dangling(value, component_count))
    {
        return Err(EncodedValidationError::invariant(
            "role-model non-simple component is dangling",
        ));
    }
    if !semantics.regularity_violations.is_empty() && !automata.automata.is_empty() {
        return Err(EncodedValidationError::invariant(
            "non-regular role model retained automata",
        ));
    }
    Ok(())
}

fn freeze_complex_inclusions(
    phase: &ComplexRolePhase,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<(Vec<u32>, u32)>> {
    let chain_items = phase
        .complex_inclusions
        .iter()
        .try_fold(0_usize, |total, value| {
            total
                .checked_add(value.chain_role_ids.len())
                .ok_or_else(|| {
                    EncodedValidationError::resource("role-model chain-item count overflowed")
                })
        })?;
    count_limit(chain_items, budget.limits.max_chain_items, "chain item")?;
    budget.claim_owned(
        phase
            .complex_inclusions
            .len()
            .checked_mul(size_of::<(Vec<u32>, u32)>())
            .ok_or_else(|| {
                EncodedValidationError::resource("role-model complex output overflowed")
            })?,
    )?;
    let mut values = Vec::new();
    values
        .try_reserve_exact(phase.complex_inclusions.len())
        .map_err(|_| EncodedValidationError::resource("role-model complex allocation failed"))?;
    for inclusion in &phase.complex_inclusions {
        budget.claim_work(1)?;
        let chain = copy_u32(
            &inclusion.chain_role_ids,
            "role-model complex chain",
            budget,
        )?;
        values.push((chain, inclusion.super_role_id));
    }
    budget.claim_work(sort_work(values.len()))?;
    values.sort_unstable();
    values.dedup();
    Ok(values)
}

fn freeze_automata(
    phase: &RoleAutomataPhase,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<DecodedRoleAutomaton>> {
    let (state_count, transition_count) =
        phase
            .automata
            .iter()
            .try_fold((0_usize, 0_usize), |(states, transitions), value| {
                Ok((
                    states
                        .checked_add(usize_id(value.state_count)?)
                        .ok_or_else(|| {
                            EncodedValidationError::resource("role-model state count overflowed")
                        })?,
                    transitions
                        .checked_add(value.transitions.len())
                        .ok_or_else(|| {
                            EncodedValidationError::resource(
                                "role-model transition count overflowed",
                            )
                        })?,
                ))
            })?;
    count_limit(state_count, budget.limits.max_states, "automaton state")?;
    count_limit(
        transition_count,
        budget.limits.max_transitions,
        "automaton transition",
    )?;
    budget.claim_owned(
        phase
            .automata
            .len()
            .checked_mul(size_of::<DecodedRoleAutomaton>())
            .ok_or_else(|| EncodedValidationError::resource("role automata output overflowed"))?,
    )?;
    let mut output = Vec::new();
    output
        .try_reserve_exact(phase.automata.len())
        .map_err(|_| EncodedValidationError::resource("role-model automata allocation failed"))?;
    for automaton in &phase.automata {
        budget.claim_work(1)?;
        let final_states = copy_u32(&automaton.final_states, "role-model final states", budget)?;
        budget.claim_owned(
            automaton
                .transitions
                .len()
                .checked_mul(size_of::<DecodedRoleTransition>())
                .ok_or_else(|| {
                    EncodedValidationError::resource("role-model transition output overflowed")
                })?,
        )?;
        let mut transitions = Vec::new();
        transitions
            .try_reserve_exact(automaton.transitions.len())
            .map_err(|_| {
                EncodedValidationError::resource("role-model transition allocation failed")
            })?;
        for transition in &automaton.transitions {
            budget.claim_work(1)?;
            transitions.push(DecodedRoleTransition {
                source_state: transition.source_state,
                target_state: transition.target_state,
                role_id: transition.role_id,
            });
        }
        budget.claim_work(sort_work(transitions.len()))?;
        transitions.sort_unstable_by_key(transition_wire_key);
        if transitions
            .windows(2)
            .any(|pair| transition_wire_key(&pair[0]) >= transition_wire_key(&pair[1]))
        {
            return Err(EncodedValidationError::invariant(
                "role-model automaton transitions are not unique",
            ));
        }
        output.push(DecodedRoleAutomaton {
            component_id: automaton.target_component_id,
            state_count: automaton.state_count,
            initial_state: automaton.initial_state,
            final_states,
            transitions,
        });
    }
    budget.claim_work(sort_work(output.len()))?;
    output.sort_unstable_by_key(|value| value.component_id);
    if output
        .windows(2)
        .any(|pair| pair[0].component_id >= pair[1].component_id)
    {
        return Err(EncodedValidationError::invariant(
            "role-model automata are not uniquely keyed by component",
        ));
    }
    Ok(output)
}

fn copy_u32(
    source: &[u32],
    name: &'static str,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<u32>> {
    budget.claim_owned(source.len().checked_mul(size_of::<u32>()).ok_or_else(|| {
        EncodedValidationError::resource(format!("{name} allocation overflowed"))
    })?)?;
    budget.claim_work(source.len())?;
    let mut output = Vec::new();
    output
        .try_reserve_exact(source.len())
        .map_err(|_| EncodedValidationError::resource(format!("{name} allocation failed")))?;
    output.extend_from_slice(source);
    Ok(output)
}

fn copy_pairs<I>(
    source: I,
    name: &'static str,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<(u32, u32)>>
where
    I: ExactSizeIterator<Item = (u32, u32)>,
{
    let count = source.len();
    budget.claim_owned(
        count
            .checked_mul(size_of::<(u32, u32)>())
            .ok_or_else(|| EncodedValidationError::resource(format!("{name} overflowed")))?,
    )?;
    budget.claim_work(count)?;
    let mut output = Vec::new();
    output
        .try_reserve_exact(count)
        .map_err(|_| EncodedValidationError::resource(format!("{name} allocation failed")))?;
    output.extend(source);
    if output.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err(EncodedValidationError::invariant(format!(
            "{name} are not sorted and unique"
        )));
    }
    Ok(output)
}

fn validate_role_model(model: &DecodedRoleModel, component_count: usize) -> EncodedResult<()> {
    let object_count = usize_id(model.object_role_count)?;
    let data_count = usize_id(model.data_property_count)?;
    if object_count == 0 || data_count == 0 || model.inverse_role_ids.len() != object_count {
        return Err(EncodedValidationError::invariant(
            "role-model domain dimensions are inconsistent",
        ));
    }
    for (role, &inverse) in model.inverse_role_ids.iter().enumerate() {
        let inverse_index = usize_id(inverse)?;
        if inverse_index >= object_count || model.inverse_role_ids[inverse_index] != u32_id(role)? {
            return Err(EncodedValidationError::invariant(
                "role-model inverse map is not an involution",
            ));
        }
    }
    validate_pairs(
        &model.simple_inclusions,
        object_count,
        "object-role inclusion",
    )?;
    validate_pairs(
        &model.data_inclusions,
        data_count,
        "data-property inclusion",
    )?;
    if model
        .complex_inclusions
        .windows(2)
        .any(|pair| pair[0] >= pair[1])
    {
        return Err(EncodedValidationError::invariant(
            "complex role-model inclusions are not canonical",
        ));
    }
    for (chain, target) in &model.complex_inclusions {
        if chain.len() < 2
            || id_is_dangling(*target, object_count)
            || chain.iter().any(|&role| id_is_dangling(role, object_count))
        {
            return Err(EncodedValidationError::invariant(
                "complex role-model inclusion is dangling",
            ));
        }
    }
    if model
        .non_simple_components
        .windows(2)
        .any(|pair| pair[0] >= pair[1])
        || model
            .non_simple_components
            .iter()
            .any(|&value| id_is_dangling(value, component_count))
    {
        return Err(EncodedValidationError::invariant(
            "role-model non-simple components are not canonical",
        ));
    }
    validate_id(model.top_object_role_id, object_count, "top object role")?;
    validate_id(
        model.bottom_object_role_id,
        object_count,
        "bottom object role",
    )?;
    validate_id(model.top_data_property_id, data_count, "top data property")?;
    validate_id(
        model.bottom_data_property_id,
        data_count,
        "bottom data property",
    )?;
    if model
        .automata
        .windows(2)
        .any(|pair| pair[0].component_id >= pair[1].component_id)
    {
        return Err(EncodedValidationError::invariant(
            "role-model automata are not canonical",
        ));
    }
    for automaton in &model.automata {
        validate_automaton(automaton, object_count, component_count)?;
    }
    Ok(())
}

fn validate_pairs(values: &[(u32, u32)], count: usize, name: &'static str) -> EncodedResult<()> {
    if values.windows(2).any(|pair| pair[0] >= pair[1])
        || values
            .iter()
            .any(|&(left, right)| id_is_dangling(left, count) || id_is_dangling(right, count))
    {
        Err(EncodedValidationError::invariant(format!(
            "{name}s are not canonical"
        )))
    } else {
        Ok(())
    }
}

fn validate_automaton(
    value: &DecodedRoleAutomaton,
    role_count: usize,
    component_count: usize,
) -> EncodedResult<()> {
    let state_count = usize_id(value.state_count)?;
    if usize_id(value.component_id)? >= component_count
        || state_count == 0
        || usize_id(value.initial_state)? >= state_count
        || value.final_states.is_empty()
        || value.final_states.windows(2).any(|pair| pair[0] >= pair[1])
        || value
            .final_states
            .iter()
            .any(|&state| id_is_dangling(state, state_count))
    {
        return Err(EncodedValidationError::invariant(
            "role-model automaton header is invalid",
        ));
    }
    if value
        .transitions
        .windows(2)
        .any(|pair| transition_wire_key(&pair[0]) >= transition_wire_key(&pair[1]))
    {
        return Err(EncodedValidationError::invariant(
            "role-model automaton transitions are not canonical",
        ));
    }
    for transition in &value.transitions {
        if usize_id(transition.source_state)? >= state_count
            || usize_id(transition.target_state)? >= state_count
            || transition
                .role_id
                .is_some_and(|role| id_is_dangling(role, role_count))
        {
            return Err(EncodedValidationError::invariant(
                "role-model automaton transition is dangling",
            ));
        }
    }
    Ok(())
}

fn canonical_transition_orders(
    automata: &[DecodedRoleAutomaton],
    manifest_limit: usize,
) -> EncodedResult<Vec<Vec<usize>>> {
    let transition_count = automata.iter().try_fold(0_usize, |total, value| {
        total.checked_add(value.transitions.len()).ok_or_else(|| {
            EncodedValidationError::resource("role-model manifest transition count overflowed")
        })
    })?;
    let workspace = automata
        .len()
        .checked_mul(size_of::<Vec<usize>>())
        .and_then(|outer| {
            transition_count
                .checked_mul(size_of::<usize>())
                .and_then(|inner| outer.checked_add(inner))
        })
        .ok_or_else(|| {
            EncodedValidationError::resource("role-model manifest workspace overflowed")
        })?;
    if workspace > manifest_limit {
        return Err(EncodedValidationError::resource(
            "role-model manifest workspace exceeds its byte limit",
        ));
    }
    let mut orders = Vec::new();
    orders.try_reserve_exact(automata.len()).map_err(|_| {
        EncodedValidationError::resource("role-model manifest order allocation failed")
    })?;
    for automaton in automata {
        let mut order = Vec::new();
        order
            .try_reserve_exact(automaton.transitions.len())
            .map_err(|_| {
                EncodedValidationError::resource(
                    "role-model manifest transition-order allocation failed",
                )
            })?;
        order.extend(0..automaton.transitions.len());
        order.sort_unstable_by(|&left, &right| {
            transition_ir_cmp(&automaton.transitions[left], &automaton.transitions[right])
        });
        orders.push(order);
    }
    Ok(orders)
}

pub(crate) fn transition_ir_cmp(
    left: &DecodedRoleTransition,
    right: &DecodedRoleTransition,
) -> Ordering {
    compare_optional_decimal(left.role_id, right.role_id)
        .then_with(|| compare_decimal(left.source_state, right.source_state))
        .then_with(|| compare_decimal(left.target_state, right.target_state))
}

fn compare_optional_decimal(left: Option<u32>, right: Option<u32>) -> Ordering {
    match (left, right) {
        (Some(left), Some(right)) => compare_decimal(left, right),
        (Some(_), None) => Ordering::Less,
        (None, Some(_)) => Ordering::Greater,
        (None, None) => Ordering::Equal,
    }
}

fn compare_decimal(left: u32, right: u32) -> Ordering {
    let (left_bytes, left_start) = decimal_bytes(left);
    let (right_bytes, right_start) = decimal_bytes(right);
    left_bytes[left_start..].cmp(&right_bytes[right_start..])
}

fn decimal_bytes(mut value: u32) -> ([u8; 10], usize) {
    let mut output = [0_u8; 10];
    let mut cursor = output.len();
    loop {
        cursor -= 1;
        output[cursor] = b'0' + u8::try_from(value % 10).unwrap_or(0);
        value /= 10;
        if value == 0 {
            return (output, cursor);
        }
    }
}

fn transition_wire_key(value: &DecodedRoleTransition) -> (u32, u32, u32) {
    (
        value.source_state,
        value.role_id.unwrap_or(u32::MAX),
        value.target_state,
    )
}

fn count_limit(observed: usize, allowed: usize, name: &'static str) -> EncodedResult<()> {
    if observed > allowed {
        Err(EncodedValidationError::resource(format!(
            "role-model {name} count exceeds its limit"
        )))
    } else {
        Ok(())
    }
}

fn validate_id(value: u32, count: usize, name: &'static str) -> EncodedResult<()> {
    if usize_id(value)? >= count {
        Err(EncodedValidationError::invariant(format!(
            "role-model {name} ID is dangling"
        )))
    } else {
        Ok(())
    }
}

fn id_is_dangling(value: u32, count: usize) -> bool {
    usize::try_from(value).map_or(true, |identifier| identifier >= count)
}

fn usize_id(value: u32) -> EncodedResult<usize> {
    usize::try_from(value)
        .map_err(|_| EncodedValidationError::resource("role-model ID exceeds usize"))
}

fn u32_id(value: usize) -> EncodedResult<u32> {
    u32::try_from(value)
        .map_err(|_| EncodedValidationError::resource("role-model count exceeds u32"))
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

    fn sample_phase() -> RoleModelPhase {
        RoleModelPhase {
            role_model: DecodedRoleModel {
                object_role_count: 3,
                data_property_count: 2,
                inverse_role_ids: vec![1, 0, 2],
                simple_inclusions: vec![(0, 2)],
                data_inclusions: vec![(0, 1)],
                complex_inclusions: vec![(vec![0, 1], 2)],
                non_simple_components: vec![2],
                automata: vec![DecodedRoleAutomaton {
                    component_id: 2,
                    state_count: 3,
                    initial_state: 0,
                    final_states: vec![2],
                    transitions: vec![
                        DecodedRoleTransition {
                            source_state: 0,
                            target_state: 1,
                            role_id: Some(2),
                        },
                        DecodedRoleTransition {
                            source_state: 1,
                            target_state: 2,
                            role_id: Some(0),
                        },
                        DecodedRoleTransition {
                            source_state: 2,
                            target_state: 0,
                            role_id: None,
                        },
                    ],
                }],
                top_object_role_id: 1,
                bottom_object_role_id: 2,
                top_data_property_id: 0,
                bottom_data_property_id: 1,
            },
            work: 0,
            owned_bytes: 0,
            component_count: 3,
            manifest_limit: 1024 * 1024,
        }
    }

    #[test]
    fn canonical_manifest_matches_compiled_ir_json_order() -> EncodedResult<()> {
        let phase = sample_phase();
        let encoded = phase.canonical_manifest_json()?;
        let expected = concat!(
            "{\"automata\":[{\"component_id\":2,\"final_states\":[2],",
            "\"initial_state\":0,\"schema_version\":1,\"state_count\":3,",
            "\"transitions\":[",
            "{\"role_id\":0,\"schema_version\":1,\"source_state\":1,",
            "\"target_state\":2,\"type\":\"RoleTransitionIR\"},",
            "{\"role_id\":2,\"schema_version\":1,\"source_state\":0,",
            "\"target_state\":1,\"type\":\"RoleTransitionIR\"},",
            "{\"role_id\":null,\"schema_version\":1,\"source_state\":2,",
            "\"target_state\":0,\"type\":\"RoleTransitionIR\"}],",
            "\"type\":\"RoleAutomatonIR\"}],\"bottom_data_property_id\":1,",
            "\"bottom_object_role_id\":2,\"complex_inclusions\":[[[0,1],2]],",
            "\"data_inclusions\":[[0,1]],\"data_property_count\":2,",
            "\"inverse_role_ids\":[1,0,2],\"non_simple_components\":[2],",
            "\"object_role_count\":3,\"schema_version\":1,",
            "\"simple_inclusions\":[[0,2]],\"top_data_property_id\":0,",
            "\"top_object_role_id\":1,\"type\":\"RoleModelIR\"}"
        );
        assert_eq!(encoded, expected.as_bytes());
        Ok(())
    }

    #[test]
    fn manifest_limit_fails_without_damaging_retry() -> EncodedResult<()> {
        let phase = sample_phase();
        let expected = phase.canonical_manifest_json()?;
        let limited = RoleModelPhase {
            manifest_limit: 1,
            ..phase.clone()
        };
        let Err(error) = limited.canonical_manifest_json() else {
            return Err(EncodedValidationError::invariant(
                "role-model manifest limit unexpectedly succeeded",
            ));
        };
        assert_eq!(error.code, "NATIVE_ENCODED_RESOURCE_LIMIT");
        assert_eq!(phase.canonical_manifest_json()?, expected);
        Ok(())
    }

    #[test]
    fn malformed_owned_role_model_is_rejected() -> EncodedResult<()> {
        let mut phase = sample_phase();
        phase.role_model.inverse_role_ids[0] = 0;
        let Err(error) = phase.canonical_manifest_json() else {
            return Err(EncodedValidationError::invariant(
                "malformed inverse map unexpectedly serialized",
            ));
        };
        assert_eq!(error.code, "NATIVE_ENCODED_INVARIANT");
        Ok(())
    }
}
