//! Canonical clausification of the owned role graph.
//!
//! This transaction turns the previously frozen object/data role phases into
//! the exact positive-role predicate and clause fragment emitted by the scalar
//! compiler.  Fragment-local IDs are dense and canonical, so later complete
//! program assembly can remap them once without reconstructing Python clause
//! objects.  The fragment is not independently publishable and does not
//! advertise the encoded compiler capability.
// SPDX-License-Identifier: LGPL-3.0-or-later

#![forbid(unsafe_code)]

use std::cmp::Ordering;
use std::mem::size_of;

use serde::Serialize;
use sha2::{Digest, Sha256};

use super::complex_roles::ComplexRolePhase;
use super::data_inclusions::DataInclusionPhase;
use super::data_roles::DataRolePhase;
use super::object_roles::ObjectRolePhase;
use super::role_characteristics::{RoleCharacteristicPhase, RoleClashKind};
use super::role_model::RoleModelPhase;
use super::simple_roles::SimpleRolePhase;
use super::{EncodedResult, EncodedValidationError};
use crate::input_wire::{
    DecodedAtom, DecodedClause, DecodedPredicate, DecodedProvenanceEntry, DecodedTerm,
    PredicateKind, SymbolKind, TermSort,
};

const ROLE_CLAUSE_PHASE_SCHEMA_VERSION: u16 = 1;
const BUILTIN_PROVENANCE_INPUT: &[u8] = b"pyhermit:clausification:builtins:v1";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RoleClausePhaseLimits {
    pub max_predicates: usize,
    pub max_clauses: usize,
    pub max_atoms: usize,
    pub max_provenance: usize,
    pub max_owned_bytes: usize,
    pub max_work: u64,
    pub max_manifest_bytes: usize,
}

impl Default for RoleClausePhaseLimits {
    fn default() -> Self {
        Self {
            max_predicates: 2_000_000,
            max_clauses: 4_000_000,
            max_atoms: 100_000_000,
            max_provenance: 10_000_000,
            max_owned_bytes: 512 * 1024 * 1024,
            max_work: 2_000_000_000,
            max_manifest_bytes: 512 * 1024 * 1024,
        }
    }
}

/// Owned positive-role predicate/rule fragment in native input-IR form.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RoleClausePhase {
    pub predicates: Vec<DecodedPredicate>,
    pub clauses: Vec<DecodedClause>,
    pub provenance: Vec<DecodedProvenanceEntry>,
    pub work: u64,
    pub owned_bytes: usize,
    manifest_limit: usize,
}

impl RoleClausePhase {
    /// Serialize the canonical test-only scalar differential manifest.
    pub fn canonical_manifest_json(&self) -> EncodedResult<Vec<u8>> {
        validate_output(self)?;
        let predicates = self.predicates.iter().map(predicate_manifest).collect();
        let clauses = self.clauses.iter().map(clause_manifest).collect();
        let provenance = self
            .provenance
            .iter()
            .map(|entry| ProvenanceManifest {
                provenance_id: entry.provenance_id,
                source_sha256: entry
                    .source_sha256
                    .iter()
                    .map(|digest| crate::model::hex(digest))
                    .collect(),
                generated: entry.generated,
            })
            .collect();
        let encoded = serde_json::to_vec(&RoleClauseManifest {
            schema_version: ROLE_CLAUSE_PHASE_SCHEMA_VERSION,
            family: "role_graph_clauses",
            predicates,
            clauses,
            provenance,
        })
        .map_err(|_| EncodedValidationError::invariant("role-clause serialization failed"))?;
        if encoded.len() > self.manifest_limit {
            return Err(EncodedValidationError::resource(
                "role-clause manifest exceeds its byte limit",
            ));
        }
        Ok(encoded)
    }
}

#[derive(Serialize)]
struct RoleClauseManifest<'a> {
    schema_version: u16,
    family: &'static str,
    predicates: Vec<PredicateManifest<'a>>,
    clauses: Vec<ClauseManifest<'a>>,
    provenance: Vec<ProvenanceManifest>,
}

#[derive(Serialize)]
struct PredicateManifest<'a> {
    predicate_id: u32,
    kind: &'static str,
    argument_sorts: Vec<&'static str>,
    symbol_id: Option<u32>,
    role_id: Option<u32>,
    cardinality: Option<u32>,
    filler_predicate_id: Option<u32>,
    annotation: &'a [u32],
    internal_key: Option<&'a str>,
}

#[derive(Serialize)]
struct ClauseManifest<'a> {
    clause_id: u32,
    body: Vec<AtomManifest>,
    head: Vec<AtomManifest>,
    provenance_ids: &'a [u32],
    join_order: &'a [u32],
}

#[derive(Serialize)]
struct AtomManifest {
    predicate_id: u32,
    arguments: Vec<TermManifest>,
}

#[derive(Serialize)]
#[serde(untagged)]
enum TermManifest {
    Variable {
        index: u32,
        sort: &'static str,
    },
    Individual {
        individual_id: u32,
    },
    Data {
        source_literal_id: u32,
        data_identity_id: u32,
    },
}

#[derive(Serialize)]
struct ProvenanceManifest {
    provenance_id: u32,
    source_sha256: Vec<String>,
    generated: bool,
}

fn predicate_manifest(predicate: &DecodedPredicate) -> PredicateManifest<'_> {
    PredicateManifest {
        predicate_id: predicate.predicate_id,
        kind: predicate_kind_name(predicate.kind),
        argument_sorts: predicate
            .argument_sorts
            .iter()
            .copied()
            .map(term_sort_name)
            .collect(),
        symbol_id: predicate.symbol_id,
        role_id: predicate.role_id,
        cardinality: predicate.cardinality,
        filler_predicate_id: predicate.filler_predicate_id,
        annotation: &predicate.annotation,
        internal_key: predicate.internal_key.as_deref(),
    }
}

fn clause_manifest(clause: &DecodedClause) -> ClauseManifest<'_> {
    ClauseManifest {
        clause_id: clause.clause_id,
        body: clause.body.iter().map(atom_manifest).collect(),
        head: clause.head.iter().map(atom_manifest).collect(),
        provenance_ids: &clause.provenance_ids,
        join_order: &clause.join_order,
    }
}

fn atom_manifest(atom: &DecodedAtom) -> AtomManifest {
    AtomManifest {
        predicate_id: atom.predicate_id,
        arguments: atom
            .arguments
            .iter()
            .map(|term| match term {
                DecodedTerm::Variable { index, sort } => TermManifest::Variable {
                    index: *index,
                    sort: term_sort_name(*sort),
                },
                DecodedTerm::Individual { individual_id } => TermManifest::Individual {
                    individual_id: *individual_id,
                },
                DecodedTerm::Data {
                    source_literal_id,
                    data_identity_id,
                } => TermManifest::Data {
                    source_literal_id: *source_literal_id,
                    data_identity_id: *data_identity_id,
                },
            })
            .collect(),
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ProvenanceKey {
    source_sha256: Vec<[u8; 32]>,
    generated: bool,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum PredicateOwner {
    Object(u32),
    Data(u32),
}

#[derive(Debug, Eq, PartialEq)]
struct PendingPredicate {
    key: Vec<u8>,
    owner: PredicateOwner,
}

#[derive(Debug, Eq, PartialEq)]
struct PendingClause {
    body: Vec<DecodedAtom>,
    head: Vec<DecodedAtom>,
    provenance: ProvenanceKey,
}

#[derive(Debug, Eq, PartialEq)]
struct MergedClause {
    key: Vec<u8>,
    body: Vec<DecodedAtom>,
    head: Vec<DecodedAtom>,
    provenance: Vec<ProvenanceKey>,
}

type FrozenPredicates = (Vec<DecodedPredicate>, Vec<u32>, Vec<Option<u32>>);
type JoinRank<'a> = (u8, u8, usize, usize, &'a [u8]);

struct PhaseBudget {
    limits: RoleClausePhaseLimits,
    work: u64,
    owned_bytes: usize,
}

impl PhaseBudget {
    const fn new(limits: RoleClausePhaseLimits) -> Self {
        Self {
            limits,
            work: 0,
            owned_bytes: 0,
        }
    }

    fn claim_work(&mut self, amount: usize) -> EncodedResult<()> {
        let amount = u64::try_from(amount)
            .map_err(|_| EncodedValidationError::resource("role-clause work exceeds u64"))?;
        let following = self
            .work
            .checked_add(amount)
            .ok_or_else(|| EncodedValidationError::resource("role-clause work overflowed"))?;
        if following > self.limits.max_work {
            return Err(EncodedValidationError::resource(
                "role-clause compilation exceeds its work limit",
            ));
        }
        self.work = following;
        Ok(())
    }

    fn claim_owned(&mut self, amount: usize) -> EncodedResult<()> {
        let following = self.owned_bytes.checked_add(amount).ok_or_else(|| {
            EncodedValidationError::resource("role-clause owned-byte count overflowed")
        })?;
        if following > self.limits.max_owned_bytes {
            return Err(EncodedValidationError::resource(
                "role-clause compilation exceeds its owned-byte limit",
            ));
        }
        self.owned_bytes = following;
        Ok(())
    }

    fn count(observed: usize, allowed: usize, name: &'static str) -> EncodedResult<()> {
        if observed > allowed {
            Err(EncodedValidationError::resource(format!(
                "role-clause {name} exceeds its limit"
            )))
        } else {
            Ok(())
        }
    }
}

/// Compile the scalar-compatible positive-role clause fragment.
#[allow(clippy::too_many_arguments)]
pub fn compile_role_clause_phase(
    object_roles: &ObjectRolePhase,
    data_roles: &DataRolePhase,
    simple_roles: &SimpleRolePhase,
    data_inclusions: &DataInclusionPhase,
    complex_roles: &ComplexRolePhase,
    role_characteristics: &RoleCharacteristicPhase,
    role_model: &RoleModelPhase,
    limits: RoleClausePhaseLimits,
) -> EncodedResult<RoleClausePhase> {
    validate_inputs(
        object_roles,
        data_roles,
        simple_roles,
        data_inclusions,
        complex_roles,
        role_characteristics,
        role_model,
    )?;
    let mut budget = PhaseBudget::new(limits);
    let (predicates, object_predicates, data_predicates) = freeze_predicates(
        object_roles,
        data_roles,
        data_inclusions,
        role_characteristics,
        &mut budget,
    )?;
    let pending = compile_clauses(
        object_roles,
        data_roles,
        simple_roles,
        data_inclusions,
        complex_roles,
        role_characteristics,
        &object_predicates,
        &data_predicates,
        &mut budget,
    )?;
    let merged = merge_clauses(pending, &mut budget)?;
    let (provenance, provenance_keys) = freeze_provenance(&merged, &mut budget)?;
    let clauses = freeze_clauses(merged, &provenance_keys, &predicates, &mut budget)?;
    let phase = RoleClausePhase {
        predicates,
        clauses,
        provenance,
        work: budget.work,
        owned_bytes: budget.owned_bytes,
        manifest_limit: budget.limits.max_manifest_bytes,
    };
    validate_output(&phase)?;
    Ok(phase)
}

fn validate_inputs(
    object_roles: &ObjectRolePhase,
    data_roles: &DataRolePhase,
    simple_roles: &SimpleRolePhase,
    data_inclusions: &DataInclusionPhase,
    complex_roles: &ComplexRolePhase,
    role_characteristics: &RoleCharacteristicPhase,
    role_model: &RoleModelPhase,
) -> EncodedResult<()> {
    if object_roles.object_role_domain.kind != SymbolKind::ObjectRole
        || data_roles.data_property_domain.kind != SymbolKind::DataProperty
    {
        return Err(EncodedValidationError::invariant(
            "role-clause input domains have the wrong kinds",
        ));
    }
    let model = &role_model.role_model;
    let object_count = object_roles.object_role_domain.values.len();
    let data_count = data_roles.data_property_domain.values.len();
    if usize::try_from(model.object_role_count).ok() != Some(object_count)
        || usize::try_from(model.data_property_count).ok() != Some(data_count)
        || model.inverse_role_ids != object_roles.inverse_role_ids
        || model.top_object_role_id != object_roles.top_object_role_id
        || model.bottom_object_role_id != object_roles.bottom_object_role_id
        || model.top_data_property_id != data_roles.top_data_property_id
        || model.bottom_data_property_id != data_roles.bottom_data_property_id
    {
        return Err(EncodedValidationError::invariant(
            "role-clause inputs diverge from the frozen role model",
        ));
    }
    let simple_pairs: Vec<_> = simple_roles
        .simple_inclusions
        .iter()
        .map(|value| (value.sub_role_id, value.super_role_id))
        .collect();
    let data_pairs: Vec<_> = data_inclusions
        .data_inclusions
        .iter()
        .map(|value| (value.sub_property_id, value.super_property_id))
        .collect();
    let mut complex_pairs: Vec<_> = complex_roles
        .complex_inclusions
        .iter()
        .map(|value| (value.chain_role_ids.clone(), value.super_role_id))
        .collect();
    complex_pairs.sort_unstable();
    complex_pairs.dedup();
    if model.simple_inclusions != simple_pairs
        || model.data_inclusions != data_pairs
        || model.complex_inclusions != complex_pairs
    {
        return Err(EncodedValidationError::invariant(
            "role-clause inclusion inputs diverge from the frozen role model",
        ));
    }
    validate_dense_domain(&object_roles.object_role_domain.values, "object-role")?;
    validate_dense_domain(&data_roles.data_property_domain.values, "data-property")?;
    super::role_characteristics::validate_phase_shape(role_characteristics)?;
    for clash in &role_characteristics.clashes {
        let count = if clash.kind.is_object() {
            object_count
        } else {
            data_count
        };
        checked_index(clash.first_role_id, count, "role-characteristic first role")?;
        if let Some(identifier) = clash.second_role_id {
            checked_index(identifier, count, "role-characteristic second role")?;
        }
        let expects_second = matches!(
            clash.kind,
            RoleClashKind::DisjointObject | RoleClashKind::DisjointData
        );
        if expects_second != clash.second_role_id.is_some() {
            return Err(EncodedValidationError::invariant(
                "role-clause characteristic input has the wrong arity",
            ));
        }
    }
    Ok(())
}

fn validate_dense_domain(
    values: &[crate::input_wire::DecodedSymbolValue],
    name: &'static str,
) -> EncodedResult<()> {
    for (index, value) in values.iter().enumerate() {
        if usize::try_from(value.identifier).ok() != Some(index) {
            return Err(EncodedValidationError::invariant(format!(
                "role-clause {name} IDs are not dense"
            )));
        }
    }
    Ok(())
}

fn freeze_predicates(
    object_roles: &ObjectRolePhase,
    data_roles: &DataRolePhase,
    data_inclusions: &DataInclusionPhase,
    role_characteristics: &RoleCharacteristicPhase,
    budget: &mut PhaseBudget,
) -> EncodedResult<FrozenPredicates> {
    let object_count = object_roles.object_role_domain.values.len();
    let data_count = data_roles.data_property_domain.values.len();
    let mut retained_data = Vec::new();
    budget.claim_owned(data_count)?;
    retained_data.try_reserve_exact(data_count).map_err(|_| {
        EncodedValidationError::resource("role-clause data index allocation failed")
    })?;
    retained_data.resize(data_count, false);
    let bottom_data = checked_index(
        data_roles.bottom_data_property_id,
        data_count,
        "bottom data property",
    )?;
    retained_data[bottom_data] = true;
    for inclusion in &data_inclusions.data_inclusions {
        budget.claim_work(1)?;
        if inclusion.sub_property_id == inclusion.super_property_id {
            continue;
        }
        let sub = checked_index(
            inclusion.sub_property_id,
            data_count,
            "data inclusion subproperty",
        )?;
        let sup = checked_index(
            inclusion.super_property_id,
            data_count,
            "data inclusion superproperty",
        )?;
        retained_data[sub] = true;
        retained_data[sup] = true;
    }
    for clash in &role_characteristics.clashes {
        if clash.kind != RoleClashKind::DisjointData {
            continue;
        }
        budget.claim_work(1)?;
        let first = checked_index(
            clash.first_role_id,
            data_count,
            "disjoint data first property",
        )?;
        let second = checked_index(
            clash.second_role_id.ok_or_else(|| {
                EncodedValidationError::invariant(
                    "disjoint data characteristic lost its second property",
                )
            })?,
            data_count,
            "disjoint data second property",
        )?;
        retained_data[first] = true;
        retained_data[second] = true;
    }
    let data_retained = retained_data.iter().filter(|value| **value).count();
    let total = object_count.checked_add(data_retained).ok_or_else(|| {
        EncodedValidationError::resource("role-clause predicate count overflowed")
    })?;
    PhaseBudget::count(total, budget.limits.max_predicates, "predicate count")?;
    let mut pending = Vec::new();
    pending
        .try_reserve_exact(total)
        .map_err(|_| EncodedValidationError::resource("role-clause predicate allocation failed"))?;
    for role_id in 0..object_count {
        let role_id = u32::try_from(role_id).map_err(|_| {
            EncodedValidationError::resource("object-role predicate ID exceeds u32")
        })?;
        let key = predicate_key(PredicateKind::ObjectRole, role_id);
        budget.claim_owned(size_of::<PendingPredicate>() + key.len())?;
        pending.push(PendingPredicate {
            key,
            owner: PredicateOwner::Object(role_id),
        });
    }
    for (role_id, retained) in retained_data.into_iter().enumerate() {
        if !retained {
            continue;
        }
        let role_id = u32::try_from(role_id)
            .map_err(|_| EncodedValidationError::resource("data-role predicate ID exceeds u32"))?;
        let key = predicate_key(PredicateKind::DataRole, role_id);
        budget.claim_owned(size_of::<PendingPredicate>() + key.len())?;
        pending.push(PendingPredicate {
            key,
            owner: PredicateOwner::Data(role_id),
        });
    }
    budget.claim_work(sort_work(pending.len()))?;
    pending.sort_by(|left, right| left.key.cmp(&right.key));

    budget.claim_owned(
        total
            .checked_mul(size_of::<DecodedPredicate>() + 2 * size_of::<TermSort>())
            .ok_or_else(|| {
                EncodedValidationError::resource("role-clause predicate output overflowed")
            })?,
    )?;
    budget.claim_owned(
        object_count
            .checked_mul(size_of::<u32>())
            .and_then(|value| value.checked_add(data_count.checked_mul(size_of::<Option<u32>>())?))
            .ok_or_else(|| {
                EncodedValidationError::resource("role-clause predicate index overflowed")
            })?,
    )?;
    let mut predicates = Vec::new();
    predicates.try_reserve_exact(total).map_err(|_| {
        EncodedValidationError::resource("role-clause predicate output allocation failed")
    })?;
    let mut object_index = Vec::new();
    object_index.try_reserve_exact(object_count).map_err(|_| {
        EncodedValidationError::resource("object predicate index allocation failed")
    })?;
    object_index.resize(object_count, u32::MAX);
    let mut data_index = Vec::new();
    data_index
        .try_reserve_exact(data_count)
        .map_err(|_| EncodedValidationError::resource("data predicate index allocation failed"))?;
    data_index.resize(data_count, None);
    for (identifier, pending) in pending.into_iter().enumerate() {
        let predicate_id = u32::try_from(identifier).map_err(|_| {
            EncodedValidationError::resource("role-clause predicate ID exceeds u32")
        })?;
        let (kind, role_id, sorts) = match pending.owner {
            PredicateOwner::Object(role_id) => {
                object_index[checked_index(role_id, object_count, "object predicate role")?] =
                    predicate_id;
                (
                    PredicateKind::ObjectRole,
                    role_id,
                    vec![TermSort::Object, TermSort::Object],
                )
            }
            PredicateOwner::Data(role_id) => {
                data_index[checked_index(role_id, data_count, "data predicate role")?] =
                    Some(predicate_id);
                (
                    PredicateKind::DataRole,
                    role_id,
                    vec![TermSort::Object, TermSort::Data],
                )
            }
        };
        predicates.push(DecodedPredicate {
            predicate_id,
            kind,
            argument_sorts: sorts,
            symbol_id: None,
            role_id: Some(role_id),
            cardinality: None,
            filler_predicate_id: None,
            annotation: Vec::new(),
            internal_key: None,
        });
    }
    if object_index.contains(&u32::MAX) {
        return Err(EncodedValidationError::invariant(
            "role-clause object predicate index is incomplete",
        ));
    }
    Ok((predicates, object_index, data_index))
}

#[allow(clippy::too_many_arguments)]
fn compile_clauses(
    object_roles: &ObjectRolePhase,
    data_roles: &DataRolePhase,
    simple_roles: &SimpleRolePhase,
    data_inclusions: &DataInclusionPhase,
    complex_roles: &ComplexRolePhase,
    role_characteristics: &RoleCharacteristicPhase,
    object_predicates: &[u32],
    data_predicates: &[Option<u32>],
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<PendingClause>> {
    let inverse_count = object_roles
        .inverse_role_ids
        .iter()
        .enumerate()
        .filter(|(role, inverse)| u32::try_from(*role).is_ok_and(|role| role <= **inverse))
        .map(|(role, inverse)| usize::from(u32::try_from(role).ok() != Some(*inverse)) + 1)
        .sum::<usize>();
    let maximum = inverse_count
        .checked_add(simple_roles.simple_inclusions.len())
        .and_then(|value| value.checked_add(data_inclusions.data_inclusions.len()))
        .and_then(|value| value.checked_add(complex_roles.complex_inclusions.len()))
        .and_then(|value| value.checked_add(role_characteristics.clashes.len()))
        .and_then(|value| value.checked_add(2))
        .ok_or_else(|| EncodedValidationError::resource("role-clause source count overflowed"))?;
    PhaseBudget::count(maximum, budget.limits.max_clauses, "source clause count")?;
    let mut clauses = Vec::new();
    clauses
        .try_reserve_exact(maximum)
        .map_err(|_| EncodedValidationError::resource("role-clause source allocation failed"))?;
    let builtin = builtin_provenance();
    for (role, &inverse) in object_roles.inverse_role_ids.iter().enumerate() {
        budget.claim_work(1)?;
        let role_id = u32::try_from(role)
            .map_err(|_| EncodedValidationError::resource("object role ID exceeds u32"))?;
        if role_id > inverse {
            continue;
        }
        let role_predicate = object_predicate(object_predicates, role_id)?;
        let inverse_predicate = object_predicate(object_predicates, inverse)?;
        push_clause(
            &mut clauses,
            vec![object_atom(role_predicate, 0, 1)],
            vec![object_atom(inverse_predicate, 1, 0)],
            builtin.clone(),
            budget,
        )?;
        if role_id != inverse {
            push_clause(
                &mut clauses,
                vec![object_atom(inverse_predicate, 0, 1)],
                vec![object_atom(role_predicate, 1, 0)],
                builtin.clone(),
                budget,
            )?;
        }
    }
    for inclusion in &simple_roles.simple_inclusions {
        budget.claim_work(1)?;
        if inclusion.sub_role_id == inclusion.super_role_id {
            continue;
        }
        push_clause(
            &mut clauses,
            vec![object_atom(
                object_predicate(object_predicates, inclusion.sub_role_id)?,
                0,
                1,
            )],
            vec![object_atom(
                object_predicate(object_predicates, inclusion.super_role_id)?,
                0,
                1,
            )],
            inclusion_provenance(inclusion.provenance_sha256, inclusion.builtin),
            budget,
        )?;
    }
    for inclusion in &data_inclusions.data_inclusions {
        budget.claim_work(1)?;
        if inclusion.sub_property_id == inclusion.super_property_id {
            continue;
        }
        push_clause(
            &mut clauses,
            vec![data_atom(
                data_predicate(data_predicates, inclusion.sub_property_id)?,
                0,
                1,
            )],
            vec![data_atom(
                data_predicate(data_predicates, inclusion.super_property_id)?,
                0,
                1,
            )],
            inclusion_provenance(inclusion.provenance_sha256, inclusion.builtin),
            budget,
        )?;
    }
    for inclusion in &complex_roles.complex_inclusions {
        budget.claim_work(inclusion.chain_role_ids.len().saturating_add(1))?;
        let mut body = Vec::new();
        body.try_reserve_exact(inclusion.chain_role_ids.len())
            .map_err(|_| {
                EncodedValidationError::resource("complex role-clause body allocation failed")
            })?;
        for (index, role_id) in inclusion.chain_role_ids.iter().copied().enumerate() {
            let left = u32::try_from(index).map_err(|_| {
                EncodedValidationError::resource("complex role-clause variable exceeds u32")
            })?;
            let right = left.checked_add(1).ok_or_else(|| {
                EncodedValidationError::resource("complex role-clause variable overflowed")
            })?;
            body.push(object_atom(
                object_predicate(object_predicates, role_id)?,
                left,
                right,
            ));
        }
        let last = u32::try_from(inclusion.chain_role_ids.len()).map_err(|_| {
            EncodedValidationError::resource("complex role-clause variable exceeds u32")
        })?;
        push_clause(
            &mut clauses,
            body,
            vec![object_atom(
                object_predicate(object_predicates, inclusion.super_role_id)?,
                0,
                last,
            )],
            inclusion_provenance(inclusion.provenance_sha256, inclusion.builtin),
            budget,
        )?;
    }
    for clash in &role_characteristics.clashes {
        budget.claim_work(1)?;
        let provenance = source_provenance(clash.provenance_sha256);
        match clash.kind {
            RoleClashKind::DisjointObject => {
                let second = clash.second_role_id.ok_or_else(|| {
                    EncodedValidationError::invariant(
                        "disjoint object characteristic lost its second role",
                    )
                })?;
                push_clause(
                    &mut clauses,
                    vec![
                        object_atom(
                            object_predicate(object_predicates, clash.first_role_id)?,
                            0,
                            1,
                        ),
                        object_atom(object_predicate(object_predicates, second)?, 0, 1),
                    ],
                    Vec::new(),
                    provenance,
                    budget,
                )?;
            }
            RoleClashKind::IrreflexiveObject => {
                push_clause(
                    &mut clauses,
                    vec![object_atom(
                        object_predicate(object_predicates, clash.first_role_id)?,
                        0,
                        0,
                    )],
                    Vec::new(),
                    provenance,
                    budget,
                )?;
            }
            RoleClashKind::AsymmetricObject => {
                let predicate = object_predicate(object_predicates, clash.first_role_id)?;
                push_clause(
                    &mut clauses,
                    vec![object_atom(predicate, 0, 1), object_atom(predicate, 1, 0)],
                    Vec::new(),
                    provenance,
                    budget,
                )?;
            }
            RoleClashKind::DisjointData => {
                let second = clash.second_role_id.ok_or_else(|| {
                    EncodedValidationError::invariant(
                        "disjoint data characteristic lost its second role",
                    )
                })?;
                push_clause(
                    &mut clauses,
                    vec![
                        data_atom(data_predicate(data_predicates, clash.first_role_id)?, 0, 1),
                        data_atom(data_predicate(data_predicates, second)?, 0, 1),
                    ],
                    Vec::new(),
                    provenance,
                    budget,
                )?;
            }
        }
    }
    push_clause(
        &mut clauses,
        vec![object_atom(
            object_predicate(object_predicates, object_roles.bottom_object_role_id)?,
            0,
            1,
        )],
        Vec::new(),
        builtin.clone(),
        budget,
    )?;
    push_clause(
        &mut clauses,
        vec![data_atom(
            data_predicate(data_predicates, data_roles.bottom_data_property_id)?,
            0,
            1,
        )],
        Vec::new(),
        builtin,
        budget,
    )?;
    Ok(clauses)
}

fn push_clause(
    target: &mut Vec<PendingClause>,
    body: Vec<DecodedAtom>,
    head: Vec<DecodedAtom>,
    provenance: ProvenanceKey,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    let atom_count = body
        .len()
        .checked_add(head.len())
        .ok_or_else(|| EncodedValidationError::resource("role-clause atom count overflowed"))?;
    PhaseBudget::count(atom_count, budget.limits.max_atoms, "per-clause atom count")?;
    budget.claim_owned(size_of::<PendingClause>())?;
    budget.claim_owned(
        atom_count
            .checked_mul(size_of::<DecodedAtom>() + 2 * size_of::<DecodedTerm>())
            .and_then(|value| value.checked_add(size_of::<[u8; 32]>()))
            .ok_or_else(|| EncodedValidationError::resource("role-clause payload overflowed"))?,
    )?;
    let (body, head) = canonicalize_clause(body, head, budget)?;
    if body.iter().any(|atom| head.contains(atom)) {
        return Ok(());
    }
    target
        .try_reserve(1)
        .map_err(|_| EncodedValidationError::resource("role-clause allocation failed"))?;
    target.push(PendingClause {
        body,
        head,
        provenance,
    });
    Ok(())
}

fn canonicalize_clause(
    mut body: Vec<DecodedAtom>,
    mut head: Vec<DecodedAtom>,
    budget: &mut PhaseBudget,
) -> EncodedResult<(Vec<DecodedAtom>, Vec<DecodedAtom>)> {
    body.sort_by(alpha_skeleton_compare);
    body.dedup();
    head.sort_by(alpha_skeleton_compare);
    head.dedup();
    let term_count = body.iter().chain(&head).try_fold(0_usize, |count, atom| {
        count.checked_add(atom.arguments.len()).ok_or_else(|| {
            EncodedValidationError::resource("role-clause variable count overflowed")
        })
    })?;
    budget.claim_owned(
        term_count
            .checked_mul(size_of::<(u32, TermSort)>())
            .ok_or_else(|| {
                EncodedValidationError::resource("role-clause variable index overflowed")
            })?,
    )?;
    let mut variables = Vec::new();
    variables.try_reserve_exact(term_count).map_err(|_| {
        EncodedValidationError::resource("role-clause variable index allocation failed")
    })?;
    for atom in body.iter().chain(&head) {
        for term in &atom.arguments {
            let DecodedTerm::Variable { index, sort } = term else {
                return Err(EncodedValidationError::invariant(
                    "role-clause source atom is not variable-only",
                ));
            };
            if !variables.contains(&(*index, *sort)) {
                variables.push((*index, *sort));
            }
        }
    }
    let passes = variables
        .len()
        .checked_add(2)
        .map_or(usize::MAX, |value| value.max(2));
    for _ in 0..passes {
        budget.claim_work(
            body.len()
                .saturating_add(head.len())
                .saturating_add(variables.len()),
        )?;
        let mut mapping = Vec::new();
        budget.claim_owned(
            variables
                .len()
                .checked_mul(size_of::<(u32, TermSort, u32)>())
                .ok_or_else(|| {
                    EncodedValidationError::resource("role-clause variable map overflowed")
                })?,
        )?;
        mapping.try_reserve_exact(variables.len()).map_err(|_| {
            EncodedValidationError::resource("role-clause variable map allocation failed")
        })?;
        for atom in body.iter().chain(&head) {
            for term in &atom.arguments {
                let DecodedTerm::Variable { index, sort } = term else {
                    return Err(EncodedValidationError::invariant(
                        "role-clause atom lost variable-only shape",
                    ));
                };
                if !mapping
                    .iter()
                    .any(|(old, old_sort, _)| old == index && old_sort == sort)
                {
                    let replacement = u32::try_from(mapping.len()).map_err(|_| {
                        EncodedValidationError::resource("role-clause variable map exceeds u32")
                    })?;
                    mapping.push((*index, *sort, replacement));
                }
            }
        }
        let identity = mapping
            .iter()
            .all(|(source, _sort, target)| source == target);
        if identity && atoms_are_canonical(&body)? && atoms_are_canonical(&head)? {
            return Ok((body, head));
        }
        rename_atoms(&mut body, &mapping)?;
        rename_atoms(&mut head, &mapping)?;
        canonical_sort_atoms(&mut body, budget)?;
        canonical_sort_atoms(&mut head, budget)?;
    }
    Err(EncodedValidationError::invariant(
        "role-clause alpha ordering exceeded its bounded passes",
    ))
}

fn rename_atoms(atoms: &mut [DecodedAtom], mapping: &[(u32, TermSort, u32)]) -> EncodedResult<()> {
    for atom in atoms {
        for term in &mut atom.arguments {
            let DecodedTerm::Variable { index, sort } = term else {
                return Err(EncodedValidationError::invariant(
                    "role-clause atom lost variable-only shape",
                ));
            };
            *index = mapping
                .iter()
                .find(|(old, old_sort, _)| old == index && old_sort == sort)
                .map(|(_, _, replacement)| *replacement)
                .ok_or_else(|| {
                    EncodedValidationError::invariant("role-clause variable map is incomplete")
                })?;
        }
    }
    Ok(())
}

fn canonical_sort_atoms(
    atoms: &mut Vec<DecodedAtom>,
    budget: &mut PhaseBudget,
) -> EncodedResult<()> {
    let mut keyed = Vec::new();
    keyed
        .try_reserve_exact(atoms.len())
        .map_err(|_| EncodedValidationError::resource("role atom ordering allocation failed"))?;
    for atom in atoms.drain(..) {
        let key = canonical_atom_key(&atom)?;
        budget.claim_owned(size_of::<(Vec<u8>, DecodedAtom)>() + key.len())?;
        keyed.push((key, atom));
    }
    budget.claim_work(sort_work(keyed.len()))?;
    keyed.sort_by(|left, right| left.0.cmp(&right.0));
    keyed.dedup_by(|left, right| left.0 == right.0);
    atoms.extend(keyed.into_iter().map(|(_, atom)| atom));
    Ok(())
}

fn atoms_are_canonical(atoms: &[DecodedAtom]) -> EncodedResult<bool> {
    let mut previous: Option<Vec<u8>> = None;
    for atom in atoms {
        let key = canonical_atom_key(atom)?;
        if previous.as_ref().is_some_and(|previous| previous >= &key) {
            return Ok(false);
        }
        previous = Some(key);
    }
    Ok(true)
}

fn alpha_skeleton_compare(left: &DecodedAtom, right: &DecodedAtom) -> Ordering {
    left.predicate_id
        .cmp(&right.predicate_id)
        .then_with(|| compare_term_skeletons(&left.arguments, &right.arguments))
}

fn compare_term_skeletons(left: &[DecodedTerm], right: &[DecodedTerm]) -> Ordering {
    for (left, right) in left.iter().zip(right) {
        let ordering = term_skeleton(left).cmp(&term_skeleton(right));
        if ordering != Ordering::Equal {
            return ordering;
        }
    }
    left.len().cmp(&right.len())
}

const fn term_skeleton(term: &DecodedTerm) -> (&'static str, u32, u32) {
    match term {
        DecodedTerm::Variable { index, sort } => (
            match sort {
                TermSort::Object => "0:object",
                TermSort::Data => "0:data",
            },
            0,
            *index,
        ),
        DecodedTerm::Individual { individual_id } => ("1:object", *individual_id, 0),
        DecodedTerm::Data {
            source_literal_id,
            data_identity_id,
        } => ("2:data", *data_identity_id, *source_literal_id),
    }
}

fn merge_clauses(
    pending: Vec<PendingClause>,
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<MergedClause>> {
    let mut keyed = Vec::new();
    keyed
        .try_reserve_exact(pending.len())
        .map_err(|_| EncodedValidationError::resource("role-clause merge allocation failed"))?;
    for clause in pending {
        let key = rule_key(&clause.body, &clause.head)?;
        budget.claim_owned(key.len() + size_of::<(Vec<u8>, PendingClause)>())?;
        keyed.push((key, clause));
    }
    budget.claim_work(sort_work(keyed.len()))?;
    keyed.sort_by(|left, right| {
        left.0
            .cmp(&right.0)
            .then_with(|| left.1.provenance.cmp(&right.1.provenance))
    });
    let mut merged: Vec<MergedClause> = Vec::new();
    for (key, clause) in keyed {
        budget.claim_work(1)?;
        if let Some(previous) = merged.last_mut() {
            if previous.key == key {
                if previous.provenance.last() != Some(&clause.provenance) {
                    budget.claim_owned(size_of::<ProvenanceKey>() + size_of::<[u8; 32]>())?;
                    previous.provenance.try_reserve(1).map_err(|_| {
                        EncodedValidationError::resource(
                            "role-clause provenance merge allocation failed",
                        )
                    })?;
                    previous.provenance.push(clause.provenance);
                }
                continue;
            }
        }
        budget.claim_owned(size_of::<MergedClause>() + size_of::<ProvenanceKey>())?;
        merged.try_reserve(1).map_err(|_| {
            EncodedValidationError::resource("role-clause merged output allocation failed")
        })?;
        merged.push(MergedClause {
            key,
            body: clause.body,
            head: clause.head,
            provenance: vec![clause.provenance],
        });
    }
    PhaseBudget::count(merged.len(), budget.limits.max_clauses, "clause count")?;
    Ok(merged)
}

fn freeze_provenance(
    clauses: &[MergedClause],
    budget: &mut PhaseBudget,
) -> EncodedResult<(Vec<DecodedProvenanceEntry>, Vec<ProvenanceKey>)> {
    let mut keys = Vec::new();
    for clause in clauses {
        for key in &clause.provenance {
            budget.claim_work(1)?;
            budget.claim_owned(size_of::<ProvenanceKey>() + key.source_sha256.len() * 32)?;
            keys.try_reserve(1).map_err(|_| {
                EncodedValidationError::resource("role-clause provenance allocation failed")
            })?;
            keys.push(key.clone());
        }
    }
    budget.claim_work(sort_work(keys.len()))?;
    keys.sort();
    keys.dedup();
    PhaseBudget::count(keys.len(), budget.limits.max_provenance, "provenance count")?;
    budget.claim_owned(
        keys.len()
            .checked_mul(size_of::<DecodedProvenanceEntry>() + size_of::<[u8; 32]>())
            .ok_or_else(|| EncodedValidationError::resource("role provenance output overflowed"))?,
    )?;
    let mut entries = Vec::new();
    entries.try_reserve_exact(keys.len()).map_err(|_| {
        EncodedValidationError::resource("role provenance output allocation failed")
    })?;
    for (identifier, key) in keys.iter().enumerate() {
        entries.push(DecodedProvenanceEntry {
            provenance_id: u32::try_from(identifier)
                .map_err(|_| EncodedValidationError::resource("role provenance ID exceeds u32"))?,
            source_sha256: key.source_sha256.clone(),
            generated: key.generated,
        });
    }
    Ok((entries, keys))
}

fn freeze_clauses(
    merged: Vec<MergedClause>,
    provenance_keys: &[ProvenanceKey],
    predicates: &[DecodedPredicate],
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<DecodedClause>> {
    let atom_count = merged.iter().try_fold(0_usize, |count, clause| {
        count
            .checked_add(clause.body.len())
            .and_then(|value| value.checked_add(clause.head.len()))
            .ok_or_else(|| EncodedValidationError::resource("role-clause atom count overflowed"))
    })?;
    PhaseBudget::count(atom_count, budget.limits.max_atoms, "atom count")?;
    budget.claim_owned(
        merged
            .len()
            .checked_mul(size_of::<DecodedClause>())
            .and_then(|value| {
                atom_count
                    .checked_mul(size_of::<DecodedAtom>() + 2 * size_of::<DecodedTerm>())
                    .and_then(|atoms| value.checked_add(atoms))
            })
            .ok_or_else(|| EncodedValidationError::resource("role-clause output overflowed"))?,
    )?;
    let mut clauses = Vec::new();
    clauses
        .try_reserve_exact(merged.len())
        .map_err(|_| EncodedValidationError::resource("role-clause output allocation failed"))?;
    for (identifier, clause) in merged.into_iter().enumerate() {
        let mut provenance_ids = Vec::new();
        provenance_ids
            .try_reserve_exact(clause.provenance.len())
            .map_err(|_| EncodedValidationError::resource("clause provenance allocation failed"))?;
        budget.claim_owned(clause.provenance.len() * size_of::<u32>())?;
        for key in &clause.provenance {
            budget.claim_work(binary_search_work(provenance_keys.len()))?;
            let index = provenance_keys.binary_search(key).map_err(|_| {
                EncodedValidationError::invariant("role-clause provenance entry disappeared")
            })?;
            provenance_ids.push(u32::try_from(index).map_err(|_| {
                EncodedValidationError::resource("role-clause provenance ID exceeds u32")
            })?);
        }
        let join_order = plan_join_order(&clause.body, predicates, budget)?;
        budget.claim_owned(join_order.len() * size_of::<u32>())?;
        clauses.push(DecodedClause {
            clause_id: u32::try_from(identifier)
                .map_err(|_| EncodedValidationError::resource("role-clause ID exceeds u32"))?,
            body: clause.body,
            head: clause.head,
            provenance_ids,
            join_order,
        });
    }
    Ok(clauses)
}

fn plan_join_order(
    body: &[DecodedAtom],
    predicates: &[DecodedPredicate],
    budget: &mut PhaseBudget,
) -> EncodedResult<Vec<u32>> {
    budget.claim_owned(body.len())?;
    let mut remaining = Vec::new();
    remaining
        .try_reserve_exact(body.len())
        .map_err(|_| EncodedValidationError::resource("join remaining-set allocation failed"))?;
    remaining.resize(body.len(), true);
    let max_variable = body
        .iter()
        .flat_map(|atom| &atom.arguments)
        .filter_map(|term| match term {
            DecodedTerm::Variable { index, .. } => Some(*index),
            DecodedTerm::Individual { .. } | DecodedTerm::Data { .. } => None,
        })
        .max()
        .map_or(0_usize, |value| {
            usize::try_from(value)
                .unwrap_or(usize::MAX)
                .saturating_add(1)
        });
    if max_variable == usize::MAX {
        return Err(EncodedValidationError::resource(
            "role-clause join variable count exceeds usize",
        ));
    }
    budget.claim_owned(max_variable.saturating_mul(size_of::<[bool; 2]>()))?;
    let mut bound = Vec::new();
    bound
        .try_reserve_exact(max_variable)
        .map_err(|_| EncodedValidationError::resource("join binding allocation failed"))?;
    bound.resize(max_variable, [false; 2]);
    let mut atom_keys = Vec::new();
    atom_keys
        .try_reserve_exact(body.len())
        .map_err(|_| EncodedValidationError::resource("join-key allocation failed"))?;
    for atom in body {
        let key = canonical_atom_key(atom)?;
        budget.claim_owned(size_of::<Vec<u8>>() + key.len())?;
        atom_keys.push(key);
    }
    let mut result = Vec::new();
    result
        .try_reserve_exact(body.len())
        .map_err(|_| EncodedValidationError::resource("join-order allocation failed"))?;
    while result.len() < body.len() {
        let mut selected: Option<(usize, JoinRank<'_>)> = None;
        for (index, atom) in body.iter().enumerate() {
            if !remaining[index] {
                continue;
            }
            budget.claim_work(1)?;
            let predicate = predicates
                .get(checked_index(
                    atom.predicate_id,
                    predicates.len(),
                    "join predicate",
                )?)
                .ok_or_else(|| EncodedValidationError::invariant("join predicate disappeared"))?;
            let mut shared = 0_usize;
            let mut new = 0_usize;
            for term in &atom.arguments {
                if let DecodedTerm::Variable { index, sort } = term {
                    let slot = bound
                        .get(usize::try_from(*index).map_err(|_| {
                            EncodedValidationError::resource("join variable exceeds usize")
                        })?)
                        .ok_or_else(|| {
                            EncodedValidationError::invariant("join variable is dangling")
                        })?[sort_index(*sort)];
                    if slot {
                        shared += 1;
                    } else {
                        new += 1;
                    }
                }
            }
            let is_filter = matches!(
                predicate.kind,
                PredicateKind::Equality | PredicateKind::Inequality | PredicateKind::OrderingGuard
            );
            let rank = (
                u8::from(is_filter && new > 0),
                u8::from(shared == 0),
                new,
                atom.arguments.len(),
                atom_keys[index].as_slice(),
            );
            if selected.as_ref().is_none_or(|(_, known)| rank < *known) {
                selected = Some((index, rank));
            }
        }
        let index = selected
            .map(|(index, _)| index)
            .ok_or_else(|| EncodedValidationError::invariant("join planning lost an atom"))?;
        remaining[index] = false;
        result.push(
            u32::try_from(index)
                .map_err(|_| EncodedValidationError::resource("join-order index exceeds u32"))?,
        );
        for term in &body[index].arguments {
            if let DecodedTerm::Variable {
                index: variable,
                sort,
            } = term
            {
                let slot = bound
                    .get_mut(usize::try_from(*variable).map_err(|_| {
                        EncodedValidationError::resource("join variable exceeds usize")
                    })?)
                    .ok_or_else(|| {
                        EncodedValidationError::invariant("join variable is dangling")
                    })?;
                slot[sort_index(*sort)] = true;
            }
        }
    }
    Ok(result)
}

fn validate_output(phase: &RoleClausePhase) -> EncodedResult<()> {
    for (identifier, predicate) in phase.predicates.iter().enumerate() {
        if usize::try_from(predicate.predicate_id).ok() != Some(identifier)
            || !matches!(
                predicate.kind,
                PredicateKind::ObjectRole | PredicateKind::DataRole
            )
            || predicate.symbol_id.is_some()
            || predicate.role_id.is_none()
            || predicate.cardinality.is_some()
            || predicate.filler_predicate_id.is_some()
            || !predicate.annotation.is_empty()
            || predicate.internal_key.is_some()
        {
            return Err(EncodedValidationError::invariant(
                "role-clause predicate output has an invalid shape",
            ));
        }
    }
    for (identifier, entry) in phase.provenance.iter().enumerate() {
        if usize::try_from(entry.provenance_id).ok() != Some(identifier)
            || entry.source_sha256.is_empty()
        {
            return Err(EncodedValidationError::invariant(
                "role-clause provenance output has an invalid shape",
            ));
        }
        if identifier > 0 {
            let previous = &phase.provenance[identifier - 1];
            if (previous.source_sha256.as_slice(), previous.generated)
                >= (entry.source_sha256.as_slice(), entry.generated)
            {
                return Err(EncodedValidationError::invariant(
                    "role-clause provenance output is not canonical",
                ));
            }
        }
    }
    let mut previous_key: Option<Vec<u8>> = None;
    for (identifier, clause) in phase.clauses.iter().enumerate() {
        if usize::try_from(clause.clause_id).ok() != Some(identifier)
            || clause.body.is_empty()
            || clause.provenance_ids.is_empty()
            || clause
                .provenance_ids
                .windows(2)
                .any(|pair| pair[0] >= pair[1])
            || clause.provenance_ids.iter().any(|value| {
                usize::try_from(*value)
                    .ok()
                    .is_none_or(|value| value >= phase.provenance.len())
            })
        {
            return Err(EncodedValidationError::invariant(
                "role-clause output has invalid IDs",
            ));
        }
        validate_atom_list(&clause.body, &phase.predicates)?;
        validate_atom_list(&clause.head, &phase.predicates)?;
        if clause.body.iter().any(|atom| clause.head.contains(atom)) {
            return Err(EncodedValidationError::invariant(
                "role-clause output contains a tautology",
            ));
        }
        let mut join = clause.join_order.clone();
        join.sort_unstable();
        if join
            != (0..u32::try_from(clause.body.len()).map_err(|_| {
                EncodedValidationError::resource("role-clause body length exceeds u32")
            })?)
                .collect::<Vec<_>>()
        {
            return Err(EncodedValidationError::invariant(
                "role-clause join order is not a permutation",
            ));
        }
        let key = rule_key(&clause.body, &clause.head)?;
        if previous_key
            .as_ref()
            .is_some_and(|previous| previous >= &key)
        {
            return Err(EncodedValidationError::invariant(
                "role-clause output is not canonically ordered",
            ));
        }
        previous_key = Some(key);
    }
    Ok(())
}

fn validate_atom_list(atoms: &[DecodedAtom], predicates: &[DecodedPredicate]) -> EncodedResult<()> {
    let mut previous: Option<Vec<u8>> = None;
    for atom in atoms {
        let predicate = predicates
            .get(checked_index(
                atom.predicate_id,
                predicates.len(),
                "atom predicate",
            )?)
            .ok_or_else(|| EncodedValidationError::invariant("atom predicate disappeared"))?;
        if atom.arguments.len() != predicate.argument_sorts.len() {
            return Err(EncodedValidationError::invariant(
                "role-clause atom arity is invalid",
            ));
        }
        for (term, expected) in atom.arguments.iter().zip(&predicate.argument_sorts) {
            if !matches!(term, DecodedTerm::Variable { sort, .. } if sort == expected) {
                return Err(EncodedValidationError::invariant(
                    "role-clause atom term sort is invalid",
                ));
            }
        }
        let key = canonical_atom_key(atom)?;
        if previous.as_ref().is_some_and(|previous| previous >= &key) {
            return Err(EncodedValidationError::invariant(
                "role-clause atoms are not canonical",
            ));
        }
        previous = Some(key);
    }
    Ok(())
}

fn predicate_key(kind: PredicateKind, role_id: u32) -> Vec<u8> {
    let (sorts, name) = match kind {
        PredicateKind::ObjectRole => ("\"object\",\"object\"", "object_role"),
        PredicateKind::DataRole => ("\"object\",\"data\"", "data_role"),
        _ => ("", "invalid"),
    };
    format!(
        "{{\"annotation\":[],\"argument_sorts\":[{sorts}],\"cardinality\":null,\"filler\":null,\"internal_key\":null,\"kind\":\"{name}\",\"role_id\":{role_id},\"symbol_id\":null}}"
    )
    .into_bytes()
}

fn canonical_atom_key(atom: &DecodedAtom) -> EncodedResult<Vec<u8>> {
    let arguments = atom
        .arguments
        .iter()
        .map(term_json)
        .collect::<EncodedResult<Vec<_>>>()?
        .join(",");
    Ok(format!(
        "{{\"arguments\":[{arguments}],\"predicate_id\":{},\"schema_version\":1,\"type\":\"Atom\"}}",
        atom.predicate_id
    )
    .into_bytes())
}

fn term_json(term: &DecodedTerm) -> EncodedResult<String> {
    match term {
        DecodedTerm::Variable { index, sort } => Ok(format!(
            "{{\"index\":{index},\"schema_version\":1,\"sort\":\"{}\",\"type\":\"Variable\"}}",
            term_sort_name(*sort)
        )),
        DecodedTerm::Individual { .. } | DecodedTerm::Data { .. } => Err(
            EncodedValidationError::invariant("role-clause canonical atom is not variable-only"),
        ),
    }
}

fn rule_key(body: &[DecodedAtom], head: &[DecodedAtom]) -> EncodedResult<Vec<u8>> {
    let body = body
        .iter()
        .map(canonical_atom_key)
        .collect::<EncodedResult<Vec<_>>>()?
        .into_iter()
        .map(|value| {
            String::from_utf8(value)
                .map_err(|_| EncodedValidationError::invariant("canonical role atom is not UTF-8"))
        })
        .collect::<EncodedResult<Vec<_>>>()?
        .join(",");
    let head = head
        .iter()
        .map(canonical_atom_key)
        .collect::<EncodedResult<Vec<_>>>()?
        .into_iter()
        .map(|value| {
            String::from_utf8(value)
                .map_err(|_| EncodedValidationError::invariant("canonical role atom is not UTF-8"))
        })
        .collect::<EncodedResult<Vec<_>>>()?
        .join(",");
    Ok(format!("{{\"body\":[{body}],\"head\":[{head}]}}").into_bytes())
}

fn object_atom(predicate_id: u32, left: u32, right: u32) -> DecodedAtom {
    DecodedAtom {
        predicate_id,
        arguments: vec![
            DecodedTerm::Variable {
                index: left,
                sort: TermSort::Object,
            },
            DecodedTerm::Variable {
                index: right,
                sort: TermSort::Object,
            },
        ],
    }
}

fn data_atom(predicate_id: u32, left: u32, right: u32) -> DecodedAtom {
    DecodedAtom {
        predicate_id,
        arguments: vec![
            DecodedTerm::Variable {
                index: left,
                sort: TermSort::Object,
            },
            DecodedTerm::Variable {
                index: right,
                sort: TermSort::Data,
            },
        ],
    }
}

fn object_predicate(index: &[u32], role_id: u32) -> EncodedResult<u32> {
    index
        .get(checked_index(role_id, index.len(), "object role")?)
        .copied()
        .ok_or_else(|| EncodedValidationError::invariant("object predicate disappeared"))
}

fn data_predicate(index: &[Option<u32>], role_id: u32) -> EncodedResult<u32> {
    index
        .get(checked_index(role_id, index.len(), "data role")?)
        .copied()
        .flatten()
        .ok_or_else(|| EncodedValidationError::invariant("data predicate is not retained"))
}

fn checked_index(identifier: u32, count: usize, name: &'static str) -> EncodedResult<usize> {
    let index = usize::try_from(identifier)
        .map_err(|_| EncodedValidationError::invariant(format!("{name} ID exceeds usize")))?;
    if index >= count {
        Err(EncodedValidationError::invariant(format!(
            "{name} ID is dangling"
        )))
    } else {
        Ok(index)
    }
}

fn builtin_provenance() -> ProvenanceKey {
    ProvenanceKey {
        source_sha256: vec![Sha256::digest(BUILTIN_PROVENANCE_INPUT).into()],
        generated: true,
    }
}

fn inclusion_provenance(source: [u8; 32], builtin: bool) -> ProvenanceKey {
    if builtin {
        builtin_provenance()
    } else {
        ProvenanceKey {
            source_sha256: vec![source],
            generated: false,
        }
    }
}

fn source_provenance(source: [u8; 32]) -> ProvenanceKey {
    ProvenanceKey {
        source_sha256: vec![source],
        generated: false,
    }
}

const fn sort_index(sort: TermSort) -> usize {
    match sort {
        TermSort::Object => 0,
        TermSort::Data => 1,
    }
}

const fn term_sort_name(sort: TermSort) -> &'static str {
    match sort {
        TermSort::Object => "object",
        TermSort::Data => "data",
    }
}

const fn predicate_kind_name(kind: PredicateKind) -> &'static str {
    match kind {
        PredicateKind::Concept => "concept",
        PredicateKind::NegatedConcept => "negated_concept",
        PredicateKind::Nominal => "nominal",
        PredicateKind::NegatedNominal => "negated_nominal",
        PredicateKind::ObjectRole => "object_role",
        PredicateKind::NegatedObjectRole => "negated_object_role",
        PredicateKind::DataRole => "data_role",
        PredicateKind::NegatedDataRole => "negated_data_role",
        PredicateKind::DataRange => "data_range",
        PredicateKind::NegatedDataRange => "negated_data_range",
        PredicateKind::Equality => "equality",
        PredicateKind::Inequality => "inequality",
        PredicateKind::AtLeastObject => "at_least_object",
        PredicateKind::AtLeastData => "at_least_data",
        PredicateKind::AnnotatedEquality => "annotated_equality",
        PredicateKind::AutomatonState => "automaton_state",
        PredicateKind::DisjointGuard => "disjoint_guard",
        PredicateKind::OrderingGuard => "ordering_guard",
        PredicateKind::NamedIndividual => "named_individual",
    }
}

fn binary_search_work(count: usize) -> usize {
    if count <= 1 {
        return count;
    }
    usize::try_from(usize::BITS - (count - 1).leading_zeros()).unwrap_or(usize::MAX)
}

fn sort_work(count: usize) -> usize {
    if count <= 1 {
        return count;
    }
    let comparisons = usize::BITS - (count - 1).leading_zeros();
    count.saturating_mul(usize::try_from(comparisons).unwrap_or(usize::MAX))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn predicate_keys_preserve_scalar_lexical_numeric_order() {
        let mut values = [
            predicate_key(PredicateKind::ObjectRole, 2),
            predicate_key(PredicateKind::ObjectRole, 10),
            predicate_key(PredicateKind::DataRole, 2),
        ];
        values.sort();
        assert!(String::from_utf8_lossy(&values[0]).contains("data_role"));
        assert!(String::from_utf8_lossy(&values[1]).contains("role_id\":10"));
        assert!(String::from_utf8_lossy(&values[2]).contains("role_id\":2"));
    }

    #[test]
    fn inverse_clause_alpha_canonicalization_matches_scalar_shape() -> EncodedResult<()> {
        let mut budget = PhaseBudget::new(RoleClausePhaseLimits::default());
        let (body, head) = canonicalize_clause(
            vec![object_atom(3, 0, 1)],
            vec![object_atom(7, 1, 0)],
            &mut budget,
        )?;
        assert_eq!(body, vec![object_atom(3, 0, 1)]);
        assert_eq!(head, vec![object_atom(7, 1, 0)]);
        Ok(())
    }
}
