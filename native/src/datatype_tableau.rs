//! Production tableau adapter for the exact semantic datatype solver.
// SPDX-License-Identifier: LGPL-3.0-or-later

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use sha2::{Digest, Sha256};

use crate::cancel::CancellationState;
use crate::datatypes::{
    decode_datatype_range_model, decode_literal_semantic, solve_semantic_component, DatatypeLimits,
    DecodedLiteral, NativeDatatypeRangeModel, OpaqueRangePolicy, RangeWireLimits,
    SemanticDatatypeConstraintComponent, SemanticFixedValueConstraint,
    SemanticInequalityConstraint, SemanticRangeConstraint, SemanticSolverLimits,
};
use crate::error::{NativeError, NativeResult};
use crate::existentials::NativeDatatypeExpansion;
use crate::input_wire::{DecodedPredicate, DecodedProgram, PredicateKind, TermSort};
use crate::model::{DependencySet, NodeHandle, NodeSort};
use crate::operation_bridge::{datatype_error_to_native, OperationControlBridge};
use crate::session::{DatatypePhaseResult, OperationControl};
use crate::store::TableauKernel;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct RangePredicate {
    data_range_id: u32,
    positive: bool,
}

#[derive(Clone, Debug)]
struct ProjectedRange {
    node: NodeHandle,
    constraint: SemanticRangeConstraint,
    participant_id: u32,
}

#[derive(Clone, Debug)]
struct ProjectedInequality {
    left: NodeHandle,
    right: NodeHandle,
    constraint: SemanticInequalityConstraint,
    participant_id: u32,
}

#[derive(Clone, Debug)]
struct ProjectedComponent {
    component: SemanticDatatypeConstraintComponent,
    participants: Vec<u32>,
}

#[derive(Clone, Debug)]
struct DatatypeProjection {
    signature: [u8; 32],
    components: Vec<ProjectedComponent>,
}

/// Decoded source registries are retained once across query-local tableau states.
struct DatatypeRegistries {
    ranges: NativeDatatypeRangeModel,
    literal_payloads: BTreeMap<u32, Vec<DecodedLiteral>>,
    range_predicates: BTreeMap<u32, RangePredicate>,
    data_inequality_predicates: BTreeSet<u32>,
    source_predicate_count: usize,
    source_data_identity_count: usize,
}

#[derive(Clone, Default)]
struct QueryPredicates {
    ids: BTreeSet<u32>,
    ranges: BTreeMap<u32, RangePredicate>,
    inequalities: BTreeSet<u32>,
}

/// Shared semantic registries and operation-local nodes, predicates and signature cache.
pub struct TableauDatatypeRuntime {
    enabled: bool,
    registries: Arc<DatatypeRegistries>,
    data_nodes: Vec<NodeHandle>,
    query_predicates: QueryPredicates,
    last_satisfiable_signature: Option<[u8; 32]>,
}

impl TableauDatatypeRuntime {
    pub fn from_program(
        program: &DecodedProgram,
        data_nodes: Vec<NodeHandle>,
        cancellation: &CancellationState,
    ) -> NativeResult<Self> {
        let source = &program.datatype_model;
        let ranges = decode_datatype_range_model(
            source.semantic_payload_json.as_bytes(),
            RangeWireLimits::default(),
            OpaqueRangePolicy::Preserve,
            cancellation,
        )
        .map_err(datatype_error_to_native)?;
        let literal_limits = DatatypeLimits::default();
        let mut literal_payloads = BTreeMap::<u32, Vec<DecodedLiteral>>::new();
        let mut semantic_identities = BTreeMap::new();
        for literal in &source.literal_identities {
            cancellation.poll()?;
            let decoded = decode_literal_semantic(
                literal.source_literal_id,
                literal.semantic_payload_json.as_bytes(),
                literal_limits,
                cancellation,
            )
            .map_err(datatype_error_to_native)?;
            if let DecodedLiteral::Semantic(value) = &decoded {
                if let Some(previous) = semantic_identities
                    .insert(literal.data_identity_id, value.data_identity.clone())
                {
                    if previous != value.data_identity {
                        return Err(NativeError::wire(
                            "one data identity maps to conflicting semantic literals",
                        ));
                    }
                }
            }
            literal_payloads
                .entry(literal.data_identity_id)
                .or_default()
                .push(decoded);
        }
        let mut range_predicates = BTreeMap::new();
        let mut data_inequality_predicates = BTreeSet::new();
        for predicate in &program.predicates {
            match predicate.kind {
                PredicateKind::DataRange | PredicateKind::NegatedDataRange => {
                    let data_range_id = predicate.symbol_id.ok_or_else(|| {
                        NativeError::wire("datatype predicate has no semantic range ID")
                    })?;
                    range_predicates.insert(
                        predicate.predicate_id,
                        RangePredicate {
                            data_range_id,
                            positive: predicate.kind == PredicateKind::DataRange,
                        },
                    );
                }
                PredicateKind::Inequality
                    if predicate.argument_sorts.first() == Some(&TermSort::Data) =>
                {
                    data_inequality_predicates.insert(predicate.predicate_id);
                }
                _ => {}
            }
        }
        Ok(Self {
            enabled: program.expressivity.datatypes,
            registries: Arc::new(DatatypeRegistries {
                ranges,
                literal_payloads,
                range_predicates,
                data_inequality_predicates,
                source_predicate_count: program.predicates.len(),
                source_data_identity_count: data_nodes.len(),
            }),
            data_nodes,
            query_predicates: QueryPredicates::default(),
            last_satisfiable_signature: None,
        })
    }

    /// Fork without decoding or cloning source registries. Existing data identity IDs
    /// retain their positions in `data_nodes`; appended nodes are symbolic witnesses.
    /// New literal identities or semantic ranges require a full native rebuild.
    pub fn fork_for_query(
        &self,
        data_nodes: Vec<NodeHandle>,
        query_predicates: &[DecodedPredicate],
        enable_datatypes: bool,
        cancellation: &CancellationState,
    ) -> NativeResult<Self> {
        cancellation.poll()?;
        if data_nodes.len() < self.registries.source_data_identity_count {
            return Err(NativeError::wire("query omits source data identities"));
        }
        let mut additions = self.query_predicates.clone();
        for predicate in query_predicates {
            cancellation.poll()?;
            if usize::try_from(predicate.predicate_id)
                .map_err(|_| NativeError::wire("query predicate ID cannot fit this platform"))?
                < self.registries.source_predicate_count
                || !additions.ids.insert(predicate.predicate_id)
            {
                return Err(NativeError::wire("query predicate replaces an existing ID"));
            }
            match predicate.kind {
                PredicateKind::DataRange | PredicateKind::NegatedDataRange => {
                    let range_id = predicate.symbol_id.ok_or_else(|| {
                        NativeError::wire("query datatype predicate has no semantic range ID")
                    })?;
                    if predicate.argument_sorts != [TermSort::Data]
                        || usize::try_from(range_id)
                            .map_or(true, |id| id >= self.registries.ranges.range_count())
                    {
                        return Err(NativeError::wire("invalid query datatype range predicate"));
                    }
                    additions.ranges.insert(
                        predicate.predicate_id,
                        RangePredicate {
                            data_range_id: range_id,
                            positive: predicate.kind == PredicateKind::DataRange,
                        },
                    );
                }
                PredicateKind::Inequality if predicate.argument_sorts.contains(&TermSort::Data) => {
                    if predicate.argument_sorts != [TermSort::Data, TermSort::Data] {
                        return Err(NativeError::wire("invalid query data inequality predicate"));
                    }
                    additions.inequalities.insert(predicate.predicate_id);
                }
                _ => {}
            }
        }
        cancellation.poll()?;
        Ok(Self {
            enabled: self.enabled || enable_datatypes,
            registries: Arc::clone(&self.registries),
            data_nodes,
            query_predicates: additions,
            last_satisfiable_signature: None,
        })
    }

    fn range_predicate(&self, predicate_id: u32) -> Option<RangePredicate> {
        self.query_predicates
            .ranges
            .get(&predicate_id)
            .or_else(|| self.registries.range_predicates.get(&predicate_id))
            .copied()
    }

    #[must_use]
    pub const fn signature_checkpoint(&self) -> Option<[u8; 32]> {
        self.last_satisfiable_signature
    }

    pub const fn restore_signature(&mut self, signature: Option<[u8; 32]>) {
        self.last_satisfiable_signature = signature;
    }

    pub const fn invalidate(&mut self) {
        self.last_satisfiable_signature = None;
    }

    pub fn check(
        &mut self,
        kernel: &mut TableauKernel,
        control: &dyn OperationControl,
    ) -> NativeResult<DatatypePhaseResult> {
        control.poll()?;
        while kernel.take_integer("datatype_components")?.is_some() {}
        if !self.enabled {
            return Ok(DatatypePhaseResult::default());
        }
        let projection = self.project(kernel)?;
        if self.last_satisfiable_signature == Some(projection.signature) {
            return Ok(DatatypePhaseResult::default());
        }
        let mut checked_components = 0_u64;
        for projected in projection.components {
            control.poll()?;
            let bridge = OperationControlBridge::new(control);
            let result = solve_semantic_component(
                &self.registries.ranges,
                &projected.component,
                SemanticSolverLimits::default(),
                &bridge,
            );
            let result = bridge.finish_datatype(result)?;
            checked_components = checked_components
                .checked_add(1)
                .ok_or_else(|| NativeError::invariant("datatype component counter overflow"))?;
            if result.satisfiable {
                continue;
            }
            let clash = result.clash.ok_or_else(|| {
                NativeError::invariant("unsatisfiable datatype result has no clash")
            })?;
            kernel.install_clash(
                "datatype_unsatisfiable".to_owned(),
                clash.dependencies,
                projected.participants,
                None,
            )?;
            return Ok(DatatypePhaseResult {
                checked_components,
                changed: true,
                clashed: true,
            });
        }
        self.last_satisfiable_signature = Some(projection.signature);
        Ok(DatatypePhaseResult {
            checked_components,
            changed: true,
            clashed: false,
        })
    }

    fn project(&self, kernel: &TableauKernel) -> NativeResult<DatatypeProjection> {
        let mut digest = Sha256::new();
        digest.update(b"pyhermit:native-datatype-state:v1\0");
        let mut handles = BTreeSet::new();
        let mut ranges = Vec::new();
        let mut inequalities = Vec::new();
        let mut adjacency = BTreeMap::<NodeHandle, BTreeSet<NodeHandle>>::new();
        for row_id in kernel.active_fact_ids() {
            let row = kernel.fact(row_id)?;
            let range = self.range_predicate(row.key.predicate_id);
            let inequality = self
                .registries
                .data_inequality_predicates
                .contains(&row.key.predicate_id)
                || self
                    .query_predicates
                    .inequalities
                    .contains(&row.key.predicate_id);
            if range.is_none() && !inequality {
                continue;
            }
            update_u32(&mut digest, row.row_id);
            update_u32(&mut digest, row.key.predicate_id);
            update_u32(
                &mut digest,
                u32::try_from(row.key.arguments.len())
                    .map_err(|_| NativeError::invariant("datatype row arity exceeds u32"))?,
            );
            update_u32(
                &mut digest,
                u32::try_from(row.supports.len()).map_err(|_| {
                    NativeError::invariant("datatype row support count exceeds u32")
                })?,
            );
            for support in &row.supports {
                update_u32(
                    &mut digest,
                    u32::try_from(support.as_slice().len()).map_err(|_| {
                        NativeError::invariant("datatype dependency count exceeds u32")
                    })?,
                );
                for level in support.as_slice() {
                    update_u32(&mut digest, *level);
                }
            }
            if let Some(predicate) = range {
                let source =
                    *row.key.arguments.first().ok_or_else(|| {
                        NativeError::invariant("unary datatype row has no argument")
                    })?;
                let node = canonical_data_node(kernel, source)?;
                update_handle(&mut digest, node);
                let variable = kernel.node_rank(node)?.0;
                ranges.push(ProjectedRange {
                    node,
                    constraint: SemanticRangeConstraint {
                        variable,
                        data_range_id: predicate.data_range_id,
                        positive: predicate.positive,
                        dependencies: row.minimal_dependency()?.clone(),
                    },
                    participant_id: row.row_id,
                });
                handles.insert(node);
                adjacency.entry(node).or_default();
            } else {
                let left = canonical_data_node(kernel, row.key.arguments[0])?;
                let right = canonical_data_node(kernel, row.key.arguments[1])?;
                update_handle(&mut digest, left);
                update_handle(&mut digest, right);
                inequalities.push(ProjectedInequality {
                    left,
                    right,
                    constraint: SemanticInequalityConstraint {
                        left: kernel.node_rank(left)?.0,
                        right: kernel.node_rank(right)?.0,
                        dependencies: row.minimal_dependency()?.clone(),
                    },
                    participant_id: row.row_id,
                });
                handles.extend([left, right]);
                adjacency.entry(left).or_default().insert(right);
                adjacency.entry(right).or_default().insert(left);
            }
        }
        let mut fixed = Vec::new();
        for (identity_id, payloads) in &self.registries.literal_payloads {
            let source = self
                .data_nodes
                .get(usize::try_from(*identity_id).map_err(|_| {
                    NativeError::invariant("data identity ID cannot fit this platform")
                })?)
                .copied()
                .ok_or_else(|| {
                    NativeError::invariant("literal data identity has no source node")
                })?;
            let node = canonical_data_node(kernel, source)?;
            if !handles.contains(&node) {
                continue;
            }
            let Some(payload) = payloads.first() else {
                continue;
            };
            let identity = match payload {
                DecodedLiteral::Semantic(value) => &value.data_identity,
                DecodedLiteral::Opaque(value) => {
                    return Err(NativeError::unsupported_datatype(
                        format!(
                            "opaque literal semantics cannot constrain a datatype component: {}",
                            value.source.datatype_iri
                        ),
                        value.source.datatype_iri.clone(),
                    ));
                }
            };
            update_u32(&mut digest, *identity_id);
            update_handle(&mut digest, node);
            fixed.push((
                node,
                SemanticFixedValueConstraint {
                    variable: kernel.node_rank(node)?.0,
                    value: identity.clone(),
                    dependencies: DependencySet::empty(),
                },
            ));
        }
        let components =
            build_components(kernel, handles, &adjacency, ranges, fixed, inequalities)?;
        Ok(DatatypeProjection {
            signature: digest.finalize().into(),
            components,
        })
    }

    fn identity_ids_for_node(
        &self,
        kernel: &TableauKernel,
        node: NodeHandle,
    ) -> NativeResult<Vec<u32>> {
        let node = canonical_data_node(kernel, node)?;
        let mut result = Vec::new();
        for (identity_id, source) in self
            .data_nodes
            .iter()
            .copied()
            .take(self.registries.source_data_identity_count)
            .enumerate()
        {
            if kernel.canonical_handle(source)?.0 == node {
                result.push(
                    u32::try_from(identity_id)
                        .map_err(|_| NativeError::invariant("data identity index exceeds u32"))?,
                );
            }
        }
        Ok(result)
    }
}

impl NativeDatatypeExpansion for TableauDatatypeRuntime {
    fn values_known_different(
        &self,
        kernel: &TableauKernel,
        left: NodeHandle,
        right: NodeHandle,
    ) -> NativeResult<bool> {
        let left = self
            .identity_ids_for_node(kernel, left)?
            .into_iter()
            .collect::<BTreeSet<_>>();
        let right = self
            .identity_ids_for_node(kernel, right)?
            .into_iter()
            .collect::<BTreeSet<_>>();
        Ok(!left.is_empty() && !right.is_empty() && left.is_disjoint(&right))
    }

    fn value_satisfies(
        &mut self,
        kernel: &TableauKernel,
        node: NodeHandle,
        predicate_id: u32,
        control: &dyn OperationControl,
    ) -> NativeResult<bool> {
        let predicate = self
            .range_predicate(predicate_id)
            .ok_or_else(|| NativeError::wire("predicate is not a unary data range"))?;
        for identity_id in self.identity_ids_for_node(kernel, node)? {
            let Some(payload) = self
                .registries
                .literal_payloads
                .get(&identity_id)
                .and_then(|payloads| payloads.first())
            else {
                continue;
            };
            let identity = match payload {
                DecodedLiteral::Semantic(value) => &value.data_identity,
                DecodedLiteral::Opaque(value) => {
                    return Err(NativeError::unsupported_datatype(
                        format!(
                            "opaque literal semantics cannot be evaluated: {}",
                            value.source.datatype_iri
                        ),
                        value.source.datatype_iri.clone(),
                    ));
                }
            };
            let bridge = OperationControlBridge::new(control);
            let result = self
                .registries
                .ranges
                .compile_range(predicate.data_range_id, &bridge)
                .and_then(|range| range.contains(identity, RangeWireLimits::default(), &bridge));
            let contained = bridge.finish_datatype(result)?;
            return Ok(if predicate.positive {
                contained
            } else {
                !contained
            });
        }
        Ok(false)
    }
}

fn build_components(
    kernel: &TableauKernel,
    handles: BTreeSet<NodeHandle>,
    adjacency: &BTreeMap<NodeHandle, BTreeSet<NodeHandle>>,
    ranges: Vec<ProjectedRange>,
    fixed: Vec<(NodeHandle, SemanticFixedValueConstraint)>,
    inequalities: Vec<ProjectedInequality>,
) -> NativeResult<Vec<ProjectedComponent>> {
    let mut unseen = handles;
    let mut components = Vec::new();
    while !unseen.is_empty() {
        let mut first = None;
        for handle in &unseen {
            let rank = kernel.node_rank(*handle)?;
            if first.is_none_or(|(known_rank, _known)| rank < known_rank) {
                first = Some((rank, *handle));
            }
        }
        let first = first
            .map(|(_rank, handle)| handle)
            .ok_or_else(|| NativeError::invariant("datatype component seed is absent"))?;
        let mut pending = vec![first];
        let mut members = BTreeSet::new();
        while let Some(current) = pending.pop() {
            if !members.insert(current) {
                continue;
            }
            unseen.remove(&current);
            if let Some(neighbours) = adjacency.get(&current) {
                pending.extend(neighbours.difference(&members).copied());
            }
        }
        let mut variables = members
            .iter()
            .map(|handle| kernel.node_rank(*handle).map(|rank| rank.0))
            .collect::<NativeResult<Vec<_>>>()?;
        variables.sort_unstable();
        variables.dedup();
        let component_ranges = ranges
            .iter()
            .filter(|value| members.contains(&value.node))
            .map(|value| value.constraint.clone())
            .collect();
        let component_fixed = fixed
            .iter()
            .filter(|(node, _constraint)| members.contains(node))
            .map(|(_node, constraint)| constraint.clone())
            .collect();
        let component_inequalities = inequalities
            .iter()
            .filter(|value| members.contains(&value.left) && members.contains(&value.right))
            .map(|value| value.constraint.clone())
            .collect();
        let mut participants = ranges
            .iter()
            .filter(|value| members.contains(&value.node))
            .map(|value| value.participant_id)
            .chain(
                inequalities
                    .iter()
                    .filter(|value| members.contains(&value.left) && members.contains(&value.right))
                    .map(|value| value.participant_id),
            )
            .collect::<Vec<_>>();
        participants.sort_unstable();
        participants.dedup();
        components.push(ProjectedComponent {
            component: SemanticDatatypeConstraintComponent {
                variables,
                ranges: component_ranges,
                fixed_values: component_fixed,
                equalities: Vec::new(),
                inequalities: component_inequalities,
                cardinalities: Vec::new(),
            },
            participants,
        });
    }
    Ok(components)
}

fn canonical_data_node(kernel: &TableauKernel, handle: NodeHandle) -> NativeResult<NodeHandle> {
    let representative = kernel.canonical_handle(handle)?.0;
    if kernel.node_sort(representative)? != NodeSort::Data {
        return Err(NativeError::wire(
            "datatype constraints require active concrete nodes",
        ));
    }
    Ok(representative)
}

fn update_u32(digest: &mut Sha256, value: u32) {
    digest.update(value.to_le_bytes());
}

fn update_handle(digest: &mut Sha256, handle: NodeHandle) {
    update_u32(digest, handle.slot);
    update_u32(digest, handle.generation);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cancel::CancellationHandle;
    use crate::error::ErrorKind;
    use crate::input_wire::{decode_ontology, DecodeLimits, DecodedLiteralIdentity};
    use crate::model::NodeKind;
    use crate::session::NeverAbort;
    use serde_json::{json, Value};

    fn literal(value: u32) -> Value {
        json!({
            "comparison": ["ordered-numeric-rational-hex-v1", format!("+{value:x}"), "+1"],
            "compatibility": "owl2",
            "data_identity": ["numeric-rational-hex-v1", format!("+{value:x}"), "+1"],
            "datatype_iri": "http://www.w3.org/2001/XMLSchema#integer",
            "language": null, "lexical_form": value.to_string(),
            "record": "literal_semantic", "schema_version": 1,
        })
    }

    fn range(datatype: &str) -> Value {
        json!({
            "datatype_iri": format!("http://www.w3.org/2001/XMLSchema#{datatype}"),
            "facets": [], "kind": "datatype", "operands": [],
            "record": "data_range_semantic", "schema_version": 1, "values": [],
        })
    }

    fn predicate(id: u32, kind: PredicateKind, range_id: Option<u32>) -> DecodedPredicate {
        DecodedPredicate {
            predicate_id: id,
            kind,
            argument_sorts: vec![
                TermSort::Data;
                if kind == PredicateKind::Inequality {
                    2
                } else {
                    1
                }
            ],
            symbol_id: range_id,
            role_id: None,
            cardinality: None,
            filler_predicate_id: None,
            annotation: Vec::new(),
            internal_key: None,
        }
    }

    fn program() -> NativeResult<DecodedProgram> {
        let fixture: Value =
            serde_json::from_str(include_str!("../../tests/data/native-input-v1.json"))
                .map_err(|error| NativeError::wire(error.to_string()))?;
        let hex = fixture["documents"]["ontology"]["hex"]
            .as_str()
            .ok_or_else(|| NativeError::wire("missing golden ontology"))?;
        let bytes = hex
            .as_bytes()
            .chunks_exact(2)
            .map(|pair| {
                std::str::from_utf8(pair)
                    .ok()
                    .and_then(|text| u8::from_str_radix(text, 16).ok())
                    .ok_or_else(|| NativeError::wire("invalid golden ontology hex"))
            })
            .collect::<NativeResult<Vec<_>>>()?;
        let mut program = decode_ontology(bytes, &DecodeLimits::default())
            .map_err(|error| NativeError::wire(error.message))?
            .program;
        let mut bounded = range("integer");
        bounded["kind"] = json!("restriction");
        bounded["facets"] = json!([{
            "facet_iri": "http://www.w3.org/2001/XMLSchema#maxInclusive",
            "record": "facet_semantic", "schema_version": 1, "value": literal(1),
        }]);
        program.datatype_model.semantic_payload_json = json!({
            "data_ranges": [range("integer"), range("string"), bounded],
            "definitions": [], "record": "datatype_semantic_model", "schema_version": 1,
        })
        .to_string();
        program.datatype_model.literal_identities = (0..2)
            .map(|id| DecodedLiteralIdentity {
                source_literal_id: id,
                data_identity_id: id,
                comparison_key: format!("value-{id}"),
                semantic_payload_json: literal(id + 1).to_string(),
            })
            .collect();
        program.predicates = vec![predicate(0, PredicateKind::DataRange, Some(0))];
        program.expressivity.datatypes = true;
        Ok(program)
    }

    fn nodes(kernel: &mut TableauKernel, count: usize) -> NativeResult<Vec<NodeHandle>> {
        (0..count)
            .map(|_| kernel.create_node(NodeKind::Concrete, None, false, None, None, None))
            .collect()
    }

    #[test]
    fn fork_shares_source_registry_and_retains_it_after_source_drop() -> NativeResult<()> {
        let cancellation = CancellationHandle::from_options(None, None)?.state();
        let mut kernel = TableauKernel::new();
        let data = nodes(&mut kernel, 2)?;
        let mut base =
            TableauDatatypeRuntime::from_program(&program()?, data.clone(), &cancellation)?;
        base.restore_signature(Some([7; 32]));
        let mut fork = base.fork_for_query(data, &[], false, &cancellation)?;
        assert!(Arc::ptr_eq(&base.registries, &fork.registries));
        assert_eq!(Arc::strong_count(&base.registries), 2);
        assert_eq!(fork.signature_checkpoint(), None);
        fork.restore_signature(Some([9; 32]));
        assert_eq!(base.signature_checkpoint(), Some([7; 32]));
        assert!(fork.enabled);
        drop(base);
        assert_eq!(Arc::strong_count(&fork.registries), 1);
        assert!(fork.value_satisfies(&kernel, fork.data_nodes[0], 0, &NeverAbort)?);
        Ok(())
    }

    #[test]
    fn fork_only_owns_predicate_delta_with_large_unrelated_source_registry() -> NativeResult<()> {
        let cancellation = CancellationHandle::from_options(None, None)?.state();
        for unrelated in [0, 1_000] {
            let mut source = program()?;
            for id in 1..=unrelated {
                source
                    .predicates
                    .push(predicate(id, PredicateKind::DataRange, Some(0)));
            }
            let mut kernel = TableauKernel::new();
            let data = nodes(&mut kernel, 2)?;
            let base = TableauDatatypeRuntime::from_program(&source, data.clone(), &cancellation)?;
            let fork = base.fork_for_query(
                data,
                &[predicate(
                    unrelated + 1,
                    PredicateKind::NegatedDataRange,
                    Some(1),
                )],
                false,
                &cancellation,
            )?;
            assert!(Arc::ptr_eq(&base.registries, &fork.registries));
            assert_eq!(fork.query_predicates.ids.len(), 1);
            assert_eq!(fork.query_predicates.ranges.len(), 1);
            assert_eq!(fork.query_predicates.inequalities.len(), 0);
            assert_eq!(
                fork.registries.range_predicates.len(),
                source.predicates.len()
            );
        }
        Ok(())
    }

    #[test]
    fn fork_range_facets_negation_and_inequality_match_full_native_rebuild() -> NativeResult<()> {
        let cancellation = CancellationHandle::from_options(None, None)?.state();
        let program = program()?;
        for (kind, range_id, identity, clashed) in [
            (PredicateKind::DataRange, Some(0), 0, false),
            (PredicateKind::NegatedDataRange, Some(0), 0, true),
            (PredicateKind::NegatedDataRange, Some(1), 0, false),
            (PredicateKind::DataRange, Some(2), 0, false),
            (PredicateKind::DataRange, Some(2), 1, true),
            (PredicateKind::Inequality, None, 0, true),
        ] {
            let mut fork_kernel = TableauKernel::new();
            let fork_nodes = nodes(&mut fork_kernel, 2)?;
            let base =
                TableauDatatypeRuntime::from_program(&program, fork_nodes.clone(), &cancellation)?;
            let addition = predicate(1, kind, range_id);
            let mut fork = base.fork_for_query(
                fork_nodes.clone(),
                std::slice::from_ref(&addition),
                false,
                &cancellation,
            )?;
            let mut rebuilt_program = program.clone();
            rebuilt_program.predicates.push(addition);
            let mut rebuilt_kernel = TableauKernel::new();
            let rebuilt_nodes = nodes(&mut rebuilt_kernel, 2)?;
            let mut rebuilt = TableauDatatypeRuntime::from_program(
                &rebuilt_program,
                rebuilt_nodes.clone(),
                &cancellation,
            )?;
            let arity = if kind == PredicateKind::Inequality {
                2
            } else {
                1
            };
            fork_kernel.add_fact(
                1,
                vec![fork_nodes[identity]; arity],
                DependencySet::empty(),
                false,
                None,
            )?;
            rebuilt_kernel.add_fact(
                1,
                vec![rebuilt_nodes[identity]; arity],
                DependencySet::empty(),
                false,
                None,
            )?;
            let result = fork.check(&mut fork_kernel, &NeverAbort)?;
            assert_eq!(result, rebuilt.check(&mut rebuilt_kernel, &NeverAbort)?);
            assert_eq!(result.clashed, clashed);
            assert_eq!(
                fork_kernel.canonical_snapshot()?,
                rebuilt_kernel.canonical_snapshot()?
            );
            assert_eq!(base.range_predicate(1), None);
        }
        Ok(())
    }

    #[test]
    fn symbolic_query_nodes_do_not_become_distinct_literal_identities() -> NativeResult<()> {
        let cancellation = CancellationHandle::from_options(None, None)?.state();
        let mut kernel = TableauKernel::new();
        let data = nodes(&mut kernel, 4)?;
        let base =
            TableauDatatypeRuntime::from_program(&program()?, data[..2].to_vec(), &cancellation)?;
        let mut fork = base.fork_for_query(data.clone(), &[], false, &cancellation)?;
        assert!(fork.values_known_different(&kernel, data[0], data[1])?);
        assert!(!fork.values_known_different(&kernel, data[2], data[3])?);
        assert!(!fork.values_known_different(&kernel, data[0], data[2])?);
        assert!(!fork.value_satisfies(&kernel, data[2], 0, &NeverAbort)?);
        kernel.merge_nodes(data[2], data[0], DependencySet::empty())?;
        assert!(fork.value_satisfies(&kernel, data[2], 0, &NeverAbort)?);
        assert!(fork.values_known_different(&kernel, data[2], data[1])?);
        Ok(())
    }

    #[test]
    fn invalid_query_predicates_and_truncated_identity_maps_are_rejected() -> NativeResult<()> {
        let cancellation = CancellationHandle::from_options(None, None)?.state();
        let mut kernel = TableauKernel::new();
        let data = nodes(&mut kernel, 2)?;
        let base = TableauDatatypeRuntime::from_program(&program()?, data.clone(), &cancellation)?;
        let mut mixed = predicate(1, PredicateKind::Inequality, None);
        mixed.argument_sorts[1] = TermSort::Object;
        let mut wrong_sort = predicate(1, PredicateKind::DataRange, Some(0));
        wrong_sort.argument_sorts[0] = TermSort::Object;
        for invalid in [
            predicate(0, PredicateKind::DataRange, Some(0)),
            predicate(1, PredicateKind::DataRange, Some(3)),
            predicate(1, PredicateKind::DataRange, None),
            mixed,
            wrong_sort,
        ] {
            assert!(base
                .fork_for_query(data.clone(), &[invalid], false, &cancellation)
                .is_err());
        }
        let addition = predicate(1, PredicateKind::DataRange, Some(0));
        assert!(base
            .fork_for_query(
                data.clone(),
                &[addition.clone(), addition.clone()],
                false,
                &cancellation
            )
            .is_err());
        assert!(base
            .fork_for_query(data[..1].to_vec(), &[], false, &cancellation)
            .is_err());
        let first = base.fork_for_query(
            data.clone(),
            std::slice::from_ref(&addition),
            false,
            &cancellation,
        )?;
        assert!(first
            .fork_for_query(data.clone(), &[addition], false, &cancellation)
            .is_err());
        let second = first.fork_for_query(
            data,
            &[predicate(2, PredicateKind::NegatedDataRange, Some(1))],
            false,
            &cancellation,
        )?;
        assert!(Arc::ptr_eq(&base.registries, &second.registries));
        assert_eq!(second.range_predicate(1), first.range_predicate(1));
        assert_eq!(first.range_predicate(2), None);
        assert!(base.query_predicates.ids.is_empty());
        Ok(())
    }

    #[test]
    fn empty_query_fork_checks_cancellation_and_can_enable_datatypes() -> NativeResult<()> {
        let cancellation = CancellationHandle::from_options(None, None)?.state();
        let mut kernel = TableauKernel::new();
        let data = nodes(&mut kernel, 2)?;
        let mut source = program()?;
        source.expressivity.datatypes = false;
        let base = TableauDatatypeRuntime::from_program(&source, data.clone(), &cancellation)?;
        assert!(
            base.fork_for_query(data.clone(), &[], true, &cancellation)?
                .enabled
        );
        cancellation.interrupt(None)?;
        let error = base
            .fork_for_query(data, &[], false, &cancellation)
            .err()
            .ok_or_else(|| NativeError::invariant("cancelled fork unexpectedly succeeded"))?;
        assert_eq!(error.kind, ErrorKind::Cancelled);
        Ok(())
    }
}
