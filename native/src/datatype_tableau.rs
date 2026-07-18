//! Production tableau adapter for the exact semantic datatype solver.
// SPDX-License-Identifier: LGPL-3.0-or-later

use std::collections::{BTreeMap, BTreeSet};

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
use crate::input_wire::{DecodedProgram, PredicateKind, TermSort};
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

/// Immutable semantic registries plus the one operation-local satisfiable-signature cache.
pub struct TableauDatatypeRuntime {
    enabled: bool,
    ranges: NativeDatatypeRangeModel,
    literal_payloads: BTreeMap<u32, Vec<DecodedLiteral>>,
    data_nodes: Vec<NodeHandle>,
    range_predicates: BTreeMap<u32, RangePredicate>,
    data_inequality_predicates: BTreeSet<u32>,
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
            ranges,
            literal_payloads,
            data_nodes,
            range_predicates,
            data_inequality_predicates,
            last_satisfiable_signature: None,
        })
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
                &self.ranges,
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
            let range = self.range_predicates.get(&row.key.predicate_id).copied();
            let inequality = self
                .data_inequality_predicates
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
        for (identity_id, payloads) in &self.literal_payloads {
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
        for (identity_id, source) in self.data_nodes.iter().copied().enumerate() {
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
            .range_predicates
            .get(&predicate_id)
            .copied()
            .ok_or_else(|| NativeError::wire("predicate is not a unary data range"))?;
        for identity_id in self.identity_ids_for_node(kernel, node)? {
            let Some(payload) = self
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
