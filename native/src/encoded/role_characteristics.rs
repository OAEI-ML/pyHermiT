//! Provenance-bearing role-characteristic clashes.
//!
//! This bounded source phase owns the scalar-compatible clauses contributed by
//! disjoint, irreflexive, and asymmetric object properties and by disjoint data
//! properties.  Annotated roots remain explicitly deferred until the general
//! annotation canonicalizer is native.  The phase is not publishable and does
//! not advertise the encoded compiler capability.
// SPDX-License-Identifier: LGPL-3.0-or-later

#![forbid(unsafe_code)]

use std::mem::size_of;

use serde::Serialize;
use sha2::{Digest, Sha256};

use super::data_roles::DataRolePhase;
use super::model::{ComponentValue, NodeId, NodeRef, ValidatedModel};
use super::object_roles::ObjectRolePhase;
use super::symbols::{RootHandler, SymbolPhase};
use super::{ByteSource, EncodedResult, EncodedValidationError};
use crate::input_wire::{DecodedSymbolDomain, SymbolKind};

const ROLE_CHARACTERISTIC_PHASE_SCHEMA_VERSION: u16 = 1;
const ENTITY_TAG: u16 = 2;
const OBJECT_INVERSE_OF_TAG: u16 = 10;
const DISJOINT_OBJECT_PROPERTIES_TAG: u16 = 72;
const IRREFLEXIVE_OBJECT_PROPERTY_TAG: u16 = 79;
const ASYMMETRIC_OBJECT_PROPERTY_TAG: u16 = 81;
const DISJOINT_DATA_PROPERTIES_TAG: u16 = 92;
const DATA_PROPERTY_PREFIX: &str = "data_property:";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RoleCharacteristicPhaseLimits {
    pub max_slices: usize,
    pub max_clashes: usize,
    pub max_compiled_roots: usize,
    pub max_deferred_roots: usize,
    pub max_owned_bytes: usize,
    pub max_work: u64,
    pub max_manifest_bytes: usize,
}

impl Default for RoleCharacteristicPhaseLimits {
    fn default() -> Self {
        Self {
            max_slices: 32_769,
            max_clashes: 100_000_000,
            max_compiled_roots: 10_000_000,
            max_deferred_roots: 10_000_000,
            max_owned_bytes: 512 * 1024 * 1024,
            max_work: 2_000_000_000,
            max_manifest_bytes: 512 * 1024 * 1024,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum RoleClashKind {
    DisjointObject,
    IrreflexiveObject,
    AsymmetricObject,
    DisjointData,
}

impl RoleClashKind {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::DisjointObject => "disjoint_object",
            Self::IrreflexiveObject => "irreflexive_object",
            Self::AsymmetricObject => "asymmetric_object",
            Self::DisjointData => "disjoint_data",
        }
    }

    #[must_use]
    pub const fn is_object(self) -> bool {
        !matches!(self, Self::DisjointData)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RoleClash {
    pub kind: RoleClashKind,
    pub first_role_id: u32,
    pub second_role_id: Option<u32>,
    pub provenance_sha256: [u8; 32],
}

/// Owned output of the pure role-characteristic source transaction.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RoleCharacteristicPhase {
    pub clashes: Vec<RoleClash>,
    pub compiled_roots: usize,
    pub deferred_roots: usize,
    pub work: u64,
    pub owned_bytes: usize,
    compiled_statement_digests: Vec<[u8; 32]>,
    manifest_limit: usize,
}

impl RoleCharacteristicPhase {
    /// Serialize the canonical test-only differential manifest.
    pub fn canonical_manifest_json(&self) -> EncodedResult<Vec<u8>> {
        validate_phase_shape(self)?;
        let clashes = self
            .clashes
            .iter()
            .map(|clash| ClashManifest {
                kind: clash.kind.as_str(),
                first_role_id: clash.first_role_id,
                second_role_id: clash.second_role_id,
                provenance_sha256: crate::model::hex(&clash.provenance_sha256),
            })
            .collect();
        let encoded = serde_json::to_vec(&RoleCharacteristicManifest {
            schema_version: ROLE_CHARACTERISTIC_PHASE_SCHEMA_VERSION,
            family: "role_characteristic_clashes",
            compiled_roots: self.compiled_roots,
            deferred_roots: self.deferred_roots,
            clashes,
        })
        .map_err(|_| {
            EncodedValidationError::invariant("role-characteristic manifest serialization failed")
        })?;
        if encoded.len() > self.manifest_limit {
            return Err(EncodedValidationError::resource(
                "role-characteristic manifest exceeds its byte limit",
            ));
        }
        Ok(encoded)
    }
}

#[derive(Serialize)]
struct RoleCharacteristicManifest {
    schema_version: u16,
    family: &'static str,
    compiled_roots: usize,
    deferred_roots: usize,
    clashes: Vec<ClashManifest>,
}

#[derive(Serialize)]
struct ClashManifest {
    kind: &'static str,
    first_role_id: u32,
    second_role_id: Option<u32>,
    provenance_sha256: String,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct RawClash {
    kind: RoleClashKind,
    first_role_id: u32,
    second_role_id: Option<u32>,
    provenance_sha256: [u8; 32],
}

#[derive(Debug, Eq, PartialEq)]
struct RoleExpression {
    role_id: u32,
    structural_key: Vec<u8>,
}

#[derive(Debug, Eq, PartialEq)]
struct DataPropertyExpression {
    property_id: u32,
    structural_key: Vec<u8>,
}

struct PhaseBudget {
    limits: RoleCharacteristicPhaseLimits,
    work: u64,
    owned_bytes: usize,
}

impl PhaseBudget {
    const fn new(limits: RoleCharacteristicPhaseLimits) -> Self {
        Self {
            limits,
            work: 0,
            owned_bytes: 0,
        }
    }

    fn claim_work(&mut self, amount: usize) -> EncodedResult<()> {
        let amount = u64::try_from(amount).map_err(|_| {
            EncodedValidationError::resource("role-characteristic work exceeds u64")
        })?;
        let following = self.work.checked_add(amount).ok_or_else(|| {
            EncodedValidationError::resource("role-characteristic work overflowed")
        })?;
        if following > self.limits.max_work {
            return Err(EncodedValidationError::resource(
                "role-characteristic compilation exceeds its work limit",
            ));
        }
        self.work = following;
        Ok(())
    }

    fn claim_owned(&mut self, amount: usize) -> EncodedResult<()> {
        let following = self.owned_bytes.checked_add(amount).ok_or_else(|| {
            EncodedValidationError::resource("role-characteristic owned bytes overflowed")
        })?;
        if following > self.limits.max_owned_bytes {
            return Err(EncodedValidationError::resource(
                "role-characteristic compilation exceeds its owned-byte limit",
            ));
        }
        self.owned_bytes = following;
        Ok(())
    }

    fn count(observed: usize, allowed: usize, name: &'static str) -> EncodedResult<()> {
        if observed > allowed {
            Err(EncodedValidationError::resource(format!(
                "role-characteristic {name} exceeds its limit"
            )))
        } else {
            Ok(())
        }
    }
}

/// Compile the supported role-characteristic roots in one validated slice.
pub fn compile_role_characteristic_phase<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    object_roles: &ObjectRolePhase,
    data_roles: &DataRolePhase,
    limits: RoleCharacteristicPhaseLimits,
) -> EncodedResult<RoleCharacteristicPhase> {
    validate_domains(object_roles, data_roles)?;
    let mut budget = PhaseBudget::new(limits);
    let mut raw = Vec::new();
    let mut compiled_statement_digests = Vec::new();
    let mut deferred_roots = 0_usize;
    for root in &symbols.roots {
        budget.claim_work(1)?;
        let digest = match root.handler {
            RootHandler::DisjointObjectProperties => compile_disjoint_object_properties(
                model,
                symbols,
                object_roles,
                root.node,
                &mut raw,
                &mut budget,
            )?,
            RootHandler::IrreflexiveObjectProperty => compile_single_object_characteristic(
                model,
                symbols,
                object_roles,
                root.node,
                IRREFLEXIVE_OBJECT_PROPERTY_TAG,
                RoleClashKind::IrreflexiveObject,
                "irreflexive-object-property",
                &mut raw,
                &mut budget,
            )?,
            RootHandler::AsymmetricObjectProperty => compile_single_object_characteristic(
                model,
                symbols,
                object_roles,
                root.node,
                ASYMMETRIC_OBJECT_PROPERTY_TAG,
                RoleClashKind::AsymmetricObject,
                "asymmetric-object-property",
                &mut raw,
                &mut budget,
            )?,
            RootHandler::DisjointDataProperties => compile_disjoint_data_properties(
                model,
                symbols,
                data_roles,
                root.node,
                &mut raw,
                &mut budget,
            )?,
            _ => continue,
        };
        if let Some(digest) = digest {
            push_digest(&mut compiled_statement_digests, digest, &mut budget)?;
        } else {
            deferred_roots = deferred_roots.checked_add(1).ok_or_else(|| {
                EncodedValidationError::resource(
                    "role-characteristic deferred-root count overflowed",
                )
            })?;
            PhaseBudget::count(
                deferred_roots,
                budget.limits.max_deferred_roots,
                "deferred-root count",
            )?;
        }
    }
    freeze_phase(raw, compiled_statement_digests, deferred_roots, budget)
}

/// Remap and merge source-local clashes through both frozen role domains.
pub fn merge_role_characteristic_phases(
    source_object_roles: &[ObjectRolePhase],
    source_data_roles: &[DataRolePhase],
    source_phases: &[RoleCharacteristicPhase],
    merged_object_roles: &ObjectRolePhase,
    merged_data_roles: &DataRolePhase,
    limits: RoleCharacteristicPhaseLimits,
) -> EncodedResult<RoleCharacteristicPhase> {
    if source_phases.is_empty()
        || source_phases.len() != source_object_roles.len()
        || source_phases.len() != source_data_roles.len()
    {
        return Err(EncodedValidationError::protocol(
            "role-characteristic merge requires aligned nonempty slices",
        ));
    }
    if source_phases.len() > limits.max_slices {
        return Err(EncodedValidationError::resource(
            "role-characteristic slice count exceeds its limit",
        ));
    }
    validate_domains(merged_object_roles, merged_data_roles)?;
    let mut budget = PhaseBudget::new(limits);
    let mut deferred_roots = 0_usize;
    for phase in source_phases {
        validate_phase_shape(phase)?;
        budget.claim_work(usize::try_from(phase.work).unwrap_or(usize::MAX))?;
        budget.claim_owned(phase.owned_bytes)?;
        deferred_roots = deferred_roots
            .checked_add(phase.deferred_roots)
            .ok_or_else(|| {
                EncodedValidationError::resource(
                    "merged role-characteristic deferred-root count overflowed",
                )
            })?;
    }
    PhaseBudget::count(
        deferred_roots,
        budget.limits.max_deferred_roots,
        "deferred-root count",
    )?;
    let mut raw = Vec::new();
    let mut compiled_statement_digests = Vec::new();
    for ((object_roles, data_roles), phase) in source_object_roles
        .iter()
        .zip(source_data_roles)
        .zip(source_phases)
    {
        validate_domains(object_roles, data_roles)?;
        for clash in &phase.clashes {
            budget.claim_work(1)?;
            let (first_role_id, second_role_id) = if clash.kind.is_object() {
                (
                    remap_role(
                        &object_roles.object_role_domain,
                        &merged_object_roles.object_role_domain,
                        clash.first_role_id,
                        "object-role",
                        &mut budget,
                    )?,
                    clash
                        .second_role_id
                        .map(|identifier| {
                            remap_role(
                                &object_roles.object_role_domain,
                                &merged_object_roles.object_role_domain,
                                identifier,
                                "object-role",
                                &mut budget,
                            )
                        })
                        .transpose()?,
                )
            } else {
                (
                    remap_role(
                        &data_roles.data_property_domain,
                        &merged_data_roles.data_property_domain,
                        clash.first_role_id,
                        "data-property",
                        &mut budget,
                    )?,
                    clash
                        .second_role_id
                        .map(|identifier| {
                            remap_role(
                                &data_roles.data_property_domain,
                                &merged_data_roles.data_property_domain,
                                identifier,
                                "data-property",
                                &mut budget,
                            )
                        })
                        .transpose()?,
                )
            };
            push_raw(
                &mut raw,
                RawClash {
                    kind: clash.kind,
                    first_role_id,
                    second_role_id,
                    provenance_sha256: clash.provenance_sha256,
                },
                &mut budget,
            )?;
        }
        for digest in &phase.compiled_statement_digests {
            push_digest(&mut compiled_statement_digests, *digest, &mut budget)?;
        }
    }
    freeze_phase(raw, compiled_statement_digests, deferred_roots, budget)
}

fn compile_disjoint_object_properties<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    roles: &ObjectRolePhase,
    root: NodeId,
    target: &mut Vec<RawClash>,
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<[u8; 32]>> {
    let node = require_root(
        model,
        root,
        DISJOINT_OBJECT_PROPERTIES_TAG,
        2,
        "disjoint-object-properties",
    )?;
    if !annotations_are_empty(model, node, 1)? {
        return Ok(None);
    }
    let collection = collection_field(model, node, 0, "disjoint-object-properties members")?;
    if collection.len() < 2 {
        return Err(EncodedValidationError::invariant(
            "disjoint-object-properties has fewer than two members",
        ));
    }
    budget.claim_owned(
        collection
            .len()
            .checked_mul(size_of::<RoleExpression>())
            .ok_or_else(|| {
                EncodedValidationError::resource(
                    "disjoint-object-properties member allocation overflowed",
                )
            })?,
    )?;
    let mut expressions = Vec::new();
    expressions
        .try_reserve_exact(collection.len())
        .map_err(|_| {
            EncodedValidationError::resource("disjoint-object-properties member allocation failed")
        })?;
    for item_index in collection.items() {
        budget.claim_work(1)?;
        let item = required_component(model.item(item_index)?, "disjoint-object-property member")?;
        let ComponentValue::Node(identifier) = model.resolve(item)? else {
            return Err(EncodedValidationError::invariant(
                "disjoint-object-property member is not a node",
            ));
        };
        expressions.push(role_expression(model, symbols, roles, identifier, budget)?);
    }
    validate_expression_order(
        expressions
            .iter()
            .map(|value| value.structural_key.as_slice()),
        "disjoint-object-properties",
    )?;
    let digest = object_set_axiom_digest(DISJOINT_OBJECT_PROPERTIES_TAG, &expressions, budget)?;
    append_object_pairs(target, &expressions, digest, budget)?;
    Ok(Some(digest))
}

#[allow(clippy::too_many_arguments)]
fn compile_single_object_characteristic<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    roles: &ObjectRolePhase,
    root: NodeId,
    tag: u16,
    kind: RoleClashKind,
    name: &'static str,
    target: &mut Vec<RawClash>,
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<[u8; 32]>> {
    let node = require_root(model, root, tag, 2, name)?;
    if !annotations_are_empty(model, node, 1)? {
        return Ok(None);
    }
    let expression = role_expression(
        model,
        symbols,
        roles,
        node_field(model, node, 0, name)?,
        budget,
    )?;
    let digest = node_axiom_digest(tag, &expression.structural_key, budget)?;
    push_raw(
        target,
        RawClash {
            kind,
            first_role_id: expression.role_id,
            second_role_id: None,
            provenance_sha256: digest,
        },
        budget,
    )?;
    Ok(Some(digest))
}

fn compile_disjoint_data_properties<B: ByteSource>(
    model: &ValidatedModel<B>,
    symbols: &SymbolPhase,
    roles: &DataRolePhase,
    root: NodeId,
    target: &mut Vec<RawClash>,
    budget: &mut PhaseBudget,
) -> EncodedResult<Option<[u8; 32]>> {
    let node = require_root(
        model,
        root,
        DISJOINT_DATA_PROPERTIES_TAG,
        2,
        "disjoint-data-properties",
    )?;
    if !annotations_are_empty(model, node, 1)? {
        return Ok(None);
    }
    let collection = collection_field(model, node, 0, "disjoint-data-properties members")?;
    if collection.len() < 2 {
        return Err(EncodedValidationError::invariant(
            "disjoint-data-properties has fewer than two members",
        ));
    }
    budget.claim_owned(
        collection
            .len()
            .checked_mul(size_of::<DataPropertyExpression>())
            .ok_or_else(|| {
                EncodedValidationError::resource(
                    "disjoint-data-properties member allocation overflowed",
                )
            })?,
    )?;
    let mut expressions = Vec::new();
    expressions
        .try_reserve_exact(collection.len())
        .map_err(|_| {
            EncodedValidationError::resource("disjoint-data-properties member allocation failed")
        })?;
    for item_index in collection.items() {
        budget.claim_work(1)?;
        let item = required_component(model.item(item_index)?, "disjoint-data-property member")?;
        let ComponentValue::Node(identifier) = model.resolve(item)? else {
            return Err(EncodedValidationError::invariant(
                "disjoint-data-property member is not a node",
            ));
        };
        expressions.push(data_property_expression(
            model, symbols, roles, identifier, budget,
        )?);
    }
    validate_expression_order(
        expressions
            .iter()
            .map(|value| value.structural_key.as_slice()),
        "disjoint-data-properties",
    )?;
    let digest = data_set_axiom_digest(DISJOINT_DATA_PROPERTIES_TAG, &expressions, budget)?;
    append_data_pairs(target, &expressions, digest, budget)?;
    Ok(Some(digest))
}

fn append_object_pairs(
    target: &mut Vec<RawClash>,
    expressions: &[RoleExpression],
    provenance_sha256: [u8; 32],
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    let pair_count = pair_count(expressions.len())?;
    let following = target
        .len()
        .checked_add(pair_count)
        .ok_or_else(|| EncodedValidationError::resource("object clash count overflowed"))?;
    PhaseBudget::count(following, budget.limits.max_clashes, "source clash count")?;
    budget.claim_work(pair_count)?;
    for left in 0..expressions.len() - 1 {
        for right in left + 1..expressions.len() {
            push_raw(
                target,
                RawClash {
                    kind: RoleClashKind::DisjointObject,
                    first_role_id: expressions[left].role_id,
                    second_role_id: Some(expressions[right].role_id),
                    provenance_sha256,
                },
                budget,
            )?;
        }
    }
    Ok(())
}

fn append_data_pairs(
    target: &mut Vec<RawClash>,
    expressions: &[DataPropertyExpression],
    provenance_sha256: [u8; 32],
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    let pair_count = pair_count(expressions.len())?;
    let following = target
        .len()
        .checked_add(pair_count)
        .ok_or_else(|| EncodedValidationError::resource("data clash count overflowed"))?;
    PhaseBudget::count(following, budget.limits.max_clashes, "source clash count")?;
    budget.claim_work(pair_count)?;
    for left in 0..expressions.len() - 1 {
        for right in left + 1..expressions.len() {
            push_raw(
                target,
                RawClash {
                    kind: RoleClashKind::DisjointData,
                    first_role_id: expressions[left].property_id,
                    second_role_id: Some(expressions[right].property_id),
                    provenance_sha256,
                },
                budget,
            )?;
        }
    }
    Ok(())
}

fn pair_count(count: usize) -> EncodedResult<usize> {
    let lesser = count.checked_sub(1).ok_or_else(|| {
        EncodedValidationError::invariant("role-characteristic pair arity underflowed")
    })?;
    let (left, right) = if count % 2 == 0 {
        (count / 2, lesser)
    } else {
        (count, lesser / 2)
    };
    left.checked_mul(right).ok_or_else(|| {
        EncodedValidationError::resource("role-characteristic pair count overflowed")
    })
}

fn freeze_phase(
    mut raw: Vec<RawClash>,
    mut compiled_statement_digests: Vec<[u8; 32]>,
    deferred_roots: usize,
    mut budget: PhaseBudget,
) -> EncodedResult<RoleCharacteristicPhase> {
    budget.claim_work(sort_work(raw.len()))?;
    raw.sort_by_key(|clash| {
        (
            clash.kind,
            clash.first_role_id,
            clash.second_role_id,
            clash.provenance_sha256,
        )
    });
    raw.dedup();
    PhaseBudget::count(raw.len(), budget.limits.max_clashes, "clash count")?;
    budget.claim_owned(
        raw.len()
            .checked_mul(size_of::<RoleClash>())
            .ok_or_else(|| EncodedValidationError::resource("role clash output overflowed"))?,
    )?;
    let mut clashes = Vec::new();
    clashes.try_reserve_exact(raw.len()).map_err(|_| {
        EncodedValidationError::resource("role-characteristic clash output allocation failed")
    })?;
    clashes.extend(raw.into_iter().map(|clash| RoleClash {
        kind: clash.kind,
        first_role_id: clash.first_role_id,
        second_role_id: clash.second_role_id,
        provenance_sha256: clash.provenance_sha256,
    }));
    budget.claim_work(sort_work(compiled_statement_digests.len()))?;
    compiled_statement_digests.sort_unstable();
    compiled_statement_digests.dedup();
    PhaseBudget::count(
        compiled_statement_digests.len(),
        budget.limits.max_compiled_roots,
        "compiled-root count",
    )?;
    PhaseBudget::count(
        deferred_roots,
        budget.limits.max_deferred_roots,
        "deferred-root count",
    )?;
    let phase = RoleCharacteristicPhase {
        clashes,
        compiled_roots: compiled_statement_digests.len(),
        deferred_roots,
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
                "role-characteristic object property is absent from the entity seed",
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
                "role-characteristic object expression resolved to another entity kind",
            ));
        }
        budget.claim_owned(entity.key.len())?;
        Ok(RoleExpression {
            role_id: role_id_by_key(
                &roles.object_role_domain,
                &entity.key,
                "object-role",
                budget,
            )?,
            structural_key: entity.key.clone(),
        })
    } else if node.tag() == OBJECT_INVERSE_OF_TAG {
        if node.field_count() != 1 {
            return Err(EncodedValidationError::invariant(
                "role-characteristic inverse expression no longer has schema-1 shape",
            ));
        }
        let property = role_expression(
            model,
            symbols,
            roles,
            node_field(model, node, 0, "object-inverse property")?,
            budget,
        )?;
        let inverse =
            roles
                .inverse_role_ids
                .get(usize::try_from(property.role_id).map_err(|_| {
                    EncodedValidationError::invariant("object-role ID exceeds usize")
                })?)
                .copied()
                .ok_or_else(|| EncodedValidationError::invariant("object-role ID is dangling"))?;
        Ok(RoleExpression {
            role_id: inverse,
            structural_key: inverse_structural_key(&property.structural_key, budget)?,
        })
    } else {
        Err(EncodedValidationError::invariant(
            "role-characteristic field is not an object-property expression",
        ))
    }
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
            "role-characteristic data property is not an entity",
        ));
    }
    let entity_id = symbols.entity_symbol_for_node(identifier).ok_or_else(|| {
        EncodedValidationError::invariant(
            "role-characteristic data property is absent from the entity seed",
        )
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
            "role-characteristic data expression resolved to another entity kind",
        ));
    }
    budget.claim_owned(entity.key.len())?;
    Ok(DataPropertyExpression {
        property_id: role_id_by_key(
            &roles.data_property_domain,
            &entity.key,
            "data-property",
            budget,
        )?,
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
    let component = required_component(
        model.field(node.fields().start.checked_add(offset).ok_or_else(|| {
            EncodedValidationError::invariant(format!("{name} field index overflowed"))
        })?)?,
        name,
    )?;
    let ComponentValue::Node(identifier) = model.resolve(component)? else {
        return Err(EncodedValidationError::invariant(format!(
            "{name} field is not a node"
        )));
    };
    Ok(identifier)
}

fn collection_field<B: ByteSource>(
    model: &ValidatedModel<B>,
    node: NodeRef,
    offset: usize,
    name: &'static str,
) -> EncodedResult<super::model::CollectionRef> {
    let component = required_component(
        model.field(node.fields().start.checked_add(offset).ok_or_else(|| {
            EncodedValidationError::invariant(format!("{name} field index overflowed"))
        })?)?,
        name,
    )?;
    let ComponentValue::Collection(collection) = model.resolve(component)? else {
        return Err(EncodedValidationError::invariant(format!(
            "{name} is not a collection"
        )));
    };
    Ok(collection)
}

fn annotations_are_empty<B: ByteSource>(
    model: &ValidatedModel<B>,
    node: NodeRef,
    offset: usize,
) -> EncodedResult<bool> {
    Ok(collection_field(model, node, offset, "axiom annotations")?.is_empty())
}

fn validate_expression_order<'a>(
    values: impl Iterator<Item = &'a [u8]>,
    name: &'static str,
) -> EncodedResult<()> {
    let mut previous: Option<&[u8]> = None;
    for value in values {
        if previous.is_some_and(|known| known >= value) {
            return Err(EncodedValidationError::invariant(format!(
                "{name} members are not in canonical set order"
            )));
        }
        previous = Some(value);
    }
    Ok(())
}

fn role_id_by_key(
    domain: &DecodedSymbolDomain,
    key: &[u8],
    name: &'static str,
    budget: &mut PhaseBudget,
) -> EncodedResult<u32> {
    budget.claim_work(binary_search_work(domain.values.len()))?;
    let index = domain
        .values
        .binary_search_by(|candidate| candidate.key.as_slice().cmp(key))
        .map_err(|_| EncodedValidationError::invariant(format!("{name} symbol key is absent")))?;
    u32::try_from(index)
        .map_err(|_| EncodedValidationError::resource(format!("{name} symbol ID exceeds u32")))
}

fn remap_role(
    source: &DecodedSymbolDomain,
    merged: &DecodedSymbolDomain,
    identifier: u32,
    name: &'static str,
    budget: &mut PhaseBudget,
) -> EncodedResult<u32> {
    let key = source
        .values
        .get(usize::try_from(identifier).map_err(|_| {
            EncodedValidationError::invariant(format!("source {name} ID exceeds usize"))
        })?)
        .map(|value| value.key.as_slice())
        .ok_or_else(|| {
            EncodedValidationError::invariant(format!("source {name} ID is dangling"))
        })?;
    role_id_by_key(merged, key, name, budget)
}

fn node_axiom_digest(tag: u16, field: &[u8], budget: &mut PhaseBudget) -> EncodedResult<[u8; 32]> {
    let mut encoded = Vec::new();
    push_varint(&mut encoded, u64::from(tag), budget)?;
    push_byte(&mut encoded, 1, budget)?;
    push_frame(&mut encoded, field, budget)?;
    push_empty_set(&mut encoded, budget)?;
    budget.claim_work(encoded.len())?;
    Ok(Sha256::digest(encoded).into())
}

fn object_set_axiom_digest(
    tag: u16,
    members: &[RoleExpression],
    budget: &mut PhaseBudget,
) -> EncodedResult<[u8; 32]> {
    set_axiom_digest(
        tag,
        members.iter().map(|value| value.structural_key.as_slice()),
        members.len(),
        budget,
    )
}

fn data_set_axiom_digest(
    tag: u16,
    members: &[DataPropertyExpression],
    budget: &mut PhaseBudget,
) -> EncodedResult<[u8; 32]> {
    set_axiom_digest(
        tag,
        members.iter().map(|value| value.structural_key.as_slice()),
        members.len(),
        budget,
    )
}

fn set_axiom_digest<'a>(
    tag: u16,
    members: impl Iterator<Item = &'a [u8]>,
    count: usize,
    budget: &mut PhaseBudget,
) -> EncodedResult<[u8; 32]> {
    let mut encoded = Vec::new();
    push_varint(&mut encoded, u64::from(tag), budget)?;
    push_byte(&mut encoded, 6, budget)?;
    push_varint(
        &mut encoded,
        u64::try_from(count)
            .map_err(|_| EncodedValidationError::resource("role set arity exceeds u64"))?,
        budget,
    )?;
    for member in members {
        push_frame(&mut encoded, member, budget)?;
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
    target.try_reserve(1).map_err(|_| {
        EncodedValidationError::resource("canonical role-characteristic allocation failed")
    })?;
    target.push(value);
    Ok(())
}

fn push_bytes(target: &mut Vec<u8>, value: &[u8], budget: &mut PhaseBudget) -> EncodedResult<()> {
    budget.claim_owned(value.len())?;
    target.try_reserve(value.len()).map_err(|_| {
        EncodedValidationError::resource("canonical role-characteristic allocation failed")
    })?;
    target.extend_from_slice(value);
    Ok(())
}

fn push_raw(
    target: &mut Vec<RawClash>,
    value: RawClash,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    budget.claim_owned(size_of::<RawClash>())?;
    target.try_reserve(1).map_err(|_| {
        EncodedValidationError::resource("role-characteristic clash allocation failed")
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
        EncodedValidationError::resource("role-characteristic root allocation failed")
    })?;
    target.push(value);
    Ok(())
}

fn validate_domains(
    object_roles: &ObjectRolePhase,
    data_roles: &DataRolePhase,
) -> EncodedResult<()> {
    validate_domain(
        &object_roles.object_role_domain,
        SymbolKind::ObjectRole,
        "object-role",
    )?;
    validate_domain(
        &data_roles.data_property_domain,
        SymbolKind::DataProperty,
        "data-property",
    )?;
    if object_roles.inverse_role_ids.len() != object_roles.object_role_domain.values.len() {
        return Err(EncodedValidationError::invariant(
            "role-characteristic inverse mapping has the wrong length",
        ));
    }
    for (index, inverse) in object_roles.inverse_role_ids.iter().copied().enumerate() {
        let inverse = usize::try_from(inverse).map_err(|_| {
            EncodedValidationError::invariant("role-characteristic inverse ID exceeds usize")
        })?;
        if object_roles
            .inverse_role_ids
            .get(inverse)
            .and_then(|value| usize::try_from(*value).ok())
            != Some(index)
        {
            return Err(EncodedValidationError::invariant(
                "role-characteristic inverse mapping is not involutive",
            ));
        }
    }
    Ok(())
}

fn validate_domain(
    domain: &DecodedSymbolDomain,
    kind: SymbolKind,
    name: &'static str,
) -> EncodedResult<()> {
    if domain.kind != kind {
        return Err(EncodedValidationError::invariant(format!(
            "role-characteristic {name} domain has the wrong kind"
        )));
    }
    for (index, value) in domain.values.iter().enumerate() {
        if usize::try_from(value.identifier).ok() != Some(index)
            || (index > 0 && domain.values[index - 1].key >= value.key)
        {
            return Err(EncodedValidationError::invariant(format!(
                "role-characteristic {name} domain is not dense and canonical"
            )));
        }
    }
    Ok(())
}

pub(super) fn validate_phase_shape(phase: &RoleCharacteristicPhase) -> EncodedResult<()> {
    if phase.compiled_roots != phase.compiled_statement_digests.len()
        || phase
            .compiled_statement_digests
            .windows(2)
            .any(|pair| pair[0] >= pair[1])
    {
        return Err(EncodedValidationError::invariant(
            "role-characteristic compiled-root identities are not canonical",
        ));
    }
    for (index, clash) in phase.clashes.iter().enumerate() {
        let expects_second = matches!(
            clash.kind,
            RoleClashKind::DisjointObject | RoleClashKind::DisjointData
        );
        if expects_second != clash.second_role_id.is_some() {
            return Err(EncodedValidationError::invariant(
                "role-characteristic clash has the wrong arity",
            ));
        }
        if index > 0 {
            let previous = &phase.clashes[index - 1];
            if (
                previous.kind,
                previous.first_role_id,
                previous.second_role_id,
                previous.provenance_sha256,
            ) >= (
                clash.kind,
                clash.first_role_id,
                clash.second_role_id,
                clash.provenance_sha256,
            ) {
                return Err(EncodedValidationError::invariant(
                    "role-characteristic clashes are not uniquely canonical",
                ));
            }
        }
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
    fn clashes_preserve_distinct_statement_provenance() -> EncodedResult<()> {
        let mut budget = PhaseBudget::new(RoleCharacteristicPhaseLimits::default());
        let mut raw = Vec::new();
        push_raw(
            &mut raw,
            RawClash {
                kind: RoleClashKind::DisjointObject,
                first_role_id: 1,
                second_role_id: Some(2),
                provenance_sha256: [2; 32],
            },
            &mut budget,
        )?;
        push_raw(
            &mut raw,
            RawClash {
                kind: RoleClashKind::DisjointObject,
                first_role_id: 1,
                second_role_id: Some(2),
                provenance_sha256: [1; 32],
            },
            &mut budget,
        )?;
        let phase = freeze_phase(raw, vec![[2; 32], [1; 32]], 0, budget)?;
        assert_eq!(phase.clashes.len(), 2);
        assert_eq!(phase.compiled_roots, 2);
        assert_eq!(phase.clashes[0].provenance_sha256, [1; 32]);
        Ok(())
    }

    #[test]
    fn semantic_and_manifest_limits_fail_transactionally() -> EncodedResult<()> {
        let mut budget = PhaseBudget::new(RoleCharacteristicPhaseLimits {
            max_clashes: 1,
            ..RoleCharacteristicPhaseLimits::default()
        });
        let mut raw = Vec::new();
        for role in 0..2 {
            push_raw(
                &mut raw,
                RawClash {
                    kind: RoleClashKind::IrreflexiveObject,
                    first_role_id: role,
                    second_role_id: None,
                    provenance_sha256: [u8::try_from(role).unwrap_or(0); 32],
                },
                &mut budget,
            )?;
        }
        let error = freeze_phase(raw, vec![[1; 32]], 0, budget)
            .err()
            .ok_or_else(|| {
                EncodedValidationError::invariant(
                    "role-characteristic clash limit unexpectedly succeeded",
                )
            })?;
        assert_eq!(error.code, "NATIVE_ENCODED_RESOURCE_LIMIT");

        let phase = freeze_phase(
            Vec::new(),
            Vec::new(),
            0,
            PhaseBudget::new(RoleCharacteristicPhaseLimits::default()),
        )?;
        let limited = RoleCharacteristicPhase {
            manifest_limit: 1,
            ..phase
        };
        let error = limited.canonical_manifest_json().err().ok_or_else(|| {
            EncodedValidationError::invariant(
                "role-characteristic manifest limit unexpectedly succeeded",
            )
        })?;
        assert_eq!(error.code, "NATIVE_ENCODED_RESOURCE_LIMIT");
        Ok(())
    }
}
