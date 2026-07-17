//! Immutable relevant-label projection and canonical blocking signatures.
// SPDX-License-Identifier: LGPL-3.0-or-later

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use super::model::{
    BlockingControl, BlockingError, BlockingLimits, BlockingStateRead, BlockingVocabulary,
    DirectCheckerKind, FactRecord, NodeKey, NodeKind, NodeLifecycle, NodeRecord,
};
use super::sha256::{hex, Sha256};

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct BlockingKey {
    pub kind: DirectCheckerKind,
    pub node_concepts: Vec<u32>,
    pub parent_concepts: Vec<u32>,
    pub from_parent_roles: Vec<u32>,
    pub to_parent_roles: Vec<u32>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BlockingSignature {
    pub kind: DirectCheckerKind,
    pub blocking_node_concepts: Vec<u32>,
    pub blocking_parent_concepts: Vec<u32>,
    pub blocking_from_parent_roles: Vec<u32>,
    pub blocking_to_parent_roles: Vec<u32>,
    pub full_node_concepts: Vec<u32>,
    pub full_parent_concepts: Vec<u32>,
    pub full_from_parent_roles: Vec<u32>,
    pub full_to_parent_roles: Vec<u32>,
}

impl BlockingSignature {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        kind: DirectCheckerKind,
        blocking_node_concepts: Vec<u32>,
        blocking_parent_concepts: Vec<u32>,
        blocking_from_parent_roles: Vec<u32>,
        blocking_to_parent_roles: Vec<u32>,
        full_node_concepts: Vec<u32>,
        full_parent_concepts: Vec<u32>,
        full_from_parent_roles: Vec<u32>,
        full_to_parent_roles: Vec<u32>,
    ) -> Result<Self, BlockingError> {
        for (name, values) in [
            ("blocking_node_concepts", &blocking_node_concepts),
            ("blocking_parent_concepts", &blocking_parent_concepts),
            ("blocking_from_parent_roles", &blocking_from_parent_roles),
            ("blocking_to_parent_roles", &blocking_to_parent_roles),
            ("full_node_concepts", &full_node_concepts),
            ("full_parent_concepts", &full_parent_concepts),
            ("full_from_parent_roles", &full_from_parent_roles),
            ("full_to_parent_roles", &full_to_parent_roles),
        ] {
            if values.windows(2).any(|pair| pair[0] >= pair[1]) {
                return Err(BlockingError::invalid(format!(
                    "{name} must be sorted and unique"
                )));
            }
        }
        Ok(Self {
            kind,
            blocking_node_concepts,
            blocking_parent_concepts,
            blocking_from_parent_roles,
            blocking_to_parent_roles,
            full_node_concepts,
            full_parent_concepts,
            full_from_parent_roles,
            full_to_parent_roles,
        })
    }

    #[must_use]
    pub fn blocking_key(&self) -> BlockingKey {
        BlockingKey {
            kind: self.kind,
            node_concepts: self.blocking_node_concepts.clone(),
            parent_concepts: self.blocking_parent_concepts.clone(),
            from_parent_roles: self.blocking_from_parent_roles.clone(),
            to_parent_roles: self.blocking_to_parent_roles.clone(),
        }
    }

    #[must_use]
    pub fn blocks(&self, other: &Self) -> bool {
        self.kind == other.kind
            && self.blocking_node_concepts == other.blocking_node_concepts
            && self.blocking_parent_concepts == other.blocking_parent_concepts
            && self.blocking_from_parent_roles == other.blocking_from_parent_roles
            && self.blocking_to_parent_roles == other.blocking_to_parent_roles
    }

    #[must_use]
    pub fn canonical_bytes(&self) -> Vec<u8> {
        let mut output = Vec::new();
        output.extend_from_slice(b"PYHBLK1\0");
        output.extend_from_slice(self.kind.as_str().as_bytes());
        output.push(0);
        for values in [
            &self.blocking_node_concepts,
            &self.blocking_parent_concepts,
            &self.blocking_from_parent_roles,
            &self.blocking_to_parent_roles,
            &self.full_node_concepts,
            &self.full_parent_concepts,
            &self.full_from_parent_roles,
            &self.full_to_parent_roles,
        ] {
            let length = u32::try_from(values.len()).unwrap_or(u32::MAX);
            output.extend_from_slice(&length.to_le_bytes());
            for value in values {
                output.extend_from_slice(&value.to_le_bytes());
            }
        }
        output
    }

    #[must_use]
    pub fn sha256(&self) -> String {
        let mut digest = Sha256::new();
        digest.update(&self.canonical_bytes());
        hex(&digest.finalize())
    }

    /// Canonical cross-language diagnostic serialization.
    #[must_use]
    pub fn canonical_debug(&self) -> String {
        format!(
            concat!(
                "{{\"blocking_from_parent_roles\":{},",
                "\"blocking_node_concepts\":{},",
                "\"blocking_parent_concepts\":{},",
                "\"blocking_to_parent_roles\":{},",
                "\"full_from_parent_roles\":{},",
                "\"full_node_concepts\":{},",
                "\"full_parent_concepts\":{},",
                "\"full_to_parent_roles\":{},",
                "\"kind\":\"{}\",\"sha256\":\"{}\"}}"
            ),
            json_ids(&self.blocking_from_parent_roles),
            json_ids(&self.blocking_node_concepts),
            json_ids(&self.blocking_parent_concepts),
            json_ids(&self.blocking_to_parent_roles),
            json_ids(&self.full_from_parent_roles),
            json_ids(&self.full_node_concepts),
            json_ids(&self.full_parent_concepts),
            json_ids(&self.full_to_parent_roles),
            self.kind.as_str(),
            self.sha256(),
        )
    }
}

fn json_ids(values: &[u32]) -> String {
    let mut output = String::from("[");
    for (index, value) in values.iter().enumerate() {
        if index != 0 {
            output.push(',');
        }
        output.push_str(&value.to_string());
    }
    output.push(']');
    output
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BlockingProjection<N> {
    pub revision: u64,
    pub ordered_nodes: Vec<N>,
    pub nodes: BTreeMap<N, NodeRecord<N>>,
    pub concepts: BTreeMap<N, Vec<u32>>,
    pub core_concepts: BTreeMap<N, Vec<u32>>,
    pub roles: BTreeMap<(N, N), Vec<u32>>,
    pub core_roles: BTreeMap<(N, N), Vec<u32>>,
    state_digest: [u8; 32],
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct RelevantFact<N> {
    predicate_id: u32,
    argument_keys: Vec<NodeKey>,
    arguments: Vec<N>,
    core: bool,
}

impl<N: Copy + fmt::Debug + Eq + Ord> BlockingProjection<N> {
    pub fn from_state<S: BlockingStateRead<Node = N>, C: BlockingControl>(
        state: &S,
        vocabulary: &BlockingVocabulary,
        limits: BlockingLimits,
        control: &C,
    ) -> Result<Self, BlockingError> {
        let limits = limits.validate()?;
        control.poll()?;
        let records = state.node_records()?;
        check_limit(
            records.len(),
            limits.max_nodes,
            "blocking_nodes",
            "blocking node projection limit exceeded",
        )?;
        let mut key_owners = BTreeMap::new();
        let mut creation_owners = BTreeMap::new();
        let mut nodes = BTreeMap::new();
        for (index, record) in records.into_iter().enumerate() {
            if index % limits.cancellation_poll_interval == 0 {
                control.poll()?;
            }
            if record.lifecycle != NodeLifecycle::Active {
                continue;
            }
            if key_owners.insert(record.key, record.node).is_some() {
                return Err(BlockingError::invariant(
                    "two active nodes share a generation-safe blocking key",
                ));
            }
            if creation_owners
                .insert(record.creation_id, record.node)
                .is_some()
            {
                return Err(BlockingError::invariant(
                    "two active nodes share a blocking creation ID",
                ));
            }
            if nodes.insert(record.node, record).is_some() {
                return Err(BlockingError::invariant(
                    "duplicate active node in blocking projection",
                ));
            }
        }
        for record in nodes.values() {
            if record.kind == NodeKind::Tree {
                let parent = record.parent.ok_or_else(|| {
                    BlockingError::invariant("active tree blocking node has no parent")
                })?;
                if !nodes.contains_key(&parent) {
                    return Err(BlockingError::invariant(
                        "active tree blocking node has no active parent",
                    ));
                }
            } else if record.parent.is_some() {
                return Err(BlockingError::invariant(
                    "non-tree node unexpectedly has a blocking parent",
                ));
            }
        }
        let mut ordered_nodes = nodes.keys().copied().collect::<Vec<_>>();
        ordered_nodes.sort_by_key(|node| {
            let record = &nodes[node];
            (record.creation_id, record.key)
        });

        let facts = state.active_fact_records()?;
        check_limit(
            facts.len(),
            limits.max_facts,
            "blocking_facts",
            "blocking fact projection limit exceeded",
        )?;
        let mut relevant = Vec::new();
        for (index, fact) in facts.into_iter().enumerate() {
            if index % limits.cancellation_poll_interval == 0 {
                control.poll()?;
            }
            if !fact.active {
                continue;
            }
            let arity_matches = (fact.arguments.len() == 1
                && vocabulary.atomic_concepts.contains(&fact.predicate_id))
                || (fact.arguments.len() == 2
                    && vocabulary.atomic_object_roles.contains(&fact.predicate_id));
            if !arity_matches || fact.arguments.iter().any(|node| !nodes.contains_key(node)) {
                continue;
            }
            relevant.push(relevant_fact(fact, &nodes)?);
        }
        relevant.sort();
        relevant.dedup();

        let mut concept_sets: BTreeMap<N, BTreeSet<u32>> = BTreeMap::new();
        let mut core_concept_sets: BTreeMap<N, BTreeSet<u32>> = BTreeMap::new();
        let mut role_sets: BTreeMap<(N, N), BTreeSet<u32>> = BTreeMap::new();
        let mut core_role_sets: BTreeMap<(N, N), BTreeSet<u32>> = BTreeMap::new();
        for fact in &relevant {
            if fact.arguments.len() == 1 {
                concept_sets
                    .entry(fact.arguments[0])
                    .or_default()
                    .insert(fact.predicate_id);
                if fact.core {
                    core_concept_sets
                        .entry(fact.arguments[0])
                        .or_default()
                        .insert(fact.predicate_id);
                }
            } else {
                let edge = (fact.arguments[0], fact.arguments[1]);
                role_sets.entry(edge).or_default().insert(fact.predicate_id);
                if fact.core {
                    core_role_sets
                        .entry(edge)
                        .or_default()
                        .insert(fact.predicate_id);
                }
            }
        }
        let state_digest = state_digest(&ordered_nodes, &nodes, &relevant, vocabulary)?;
        let estimated = estimate_bytes(nodes.len(), relevant.len());
        control.observe_memory(estimated)?;
        control.poll()?;
        Ok(Self {
            revision: state.revision(),
            ordered_nodes,
            nodes,
            concepts: freeze(concept_sets),
            core_concepts: freeze(core_concept_sets),
            roles: freeze(role_sets),
            core_roles: freeze(core_role_sets),
            state_digest,
        })
    }

    #[must_use]
    pub const fn state_digest(&self) -> [u8; 32] {
        self.state_digest
    }

    #[must_use]
    pub fn state_digest_hex(&self) -> String {
        hex(&self.state_digest)
    }

    #[must_use]
    pub fn node(&self, node: N) -> Option<&NodeRecord<N>> {
        self.nodes.get(&node)
    }

    #[must_use]
    pub fn concept_label(&self, node: N, core_only: bool) -> &[u32] {
        let source = if core_only {
            &self.core_concepts
        } else {
            &self.concepts
        };
        source.get(&node).map_or(&[], Vec::as_slice)
    }

    #[must_use]
    pub fn role_label(&self, source: N, target: N, core_only: bool) -> &[u32] {
        let roles = if core_only {
            &self.core_roles
        } else {
            &self.roles
        };
        roles.get(&(source, target)).map_or(&[], Vec::as_slice)
    }

    #[must_use]
    pub fn earliest_difference(&self, other: &Self) -> Option<u32> {
        let mut changed = Vec::new();
        for node in self.nodes.keys().chain(other.nodes.keys()) {
            let before = self.nodes.get(node);
            let after = other.nodes.get(node);
            if !same_blocking_node(before, after) {
                if let Some(value) = before {
                    changed.push(value.creation_id);
                }
                if let Some(value) = after {
                    changed.push(value.creation_id);
                }
            }
            if self.concepts.get(node) != other.concepts.get(node)
                || self.core_concepts.get(node) != other.core_concepts.get(node)
            {
                if let Some(value) = before.or(after) {
                    changed.push(value.creation_id);
                }
            }
        }
        for edge in self.roles.keys().chain(other.roles.keys()) {
            if self.roles.get(edge) != other.roles.get(edge)
                || self.core_roles.get(edge) != other.core_roles.get(edge)
            {
                for node in [edge.0, edge.1] {
                    if let Some(record) = self.nodes.get(&node).or_else(|| other.nodes.get(&node)) {
                        changed.push(record.creation_id);
                    }
                }
            }
        }
        changed.into_iter().min()
    }

    #[must_use]
    pub fn is_ancestor(&self, ancestor: N, mut node: N) -> bool {
        let mut remaining = self.nodes.len();
        while remaining != 0 {
            let Some(parent) = self.nodes.get(&node).and_then(|value| value.parent) else {
                return false;
            };
            if parent == ancestor {
                return true;
            }
            node = parent;
            remaining -= 1;
        }
        false
    }
}

impl BlockingVocabulary {
    #[must_use]
    pub fn fingerprint(&self) -> String {
        hex(&self.fingerprint_bytes())
    }

    fn fingerprint_bytes(&self) -> [u8; 32] {
        let mut digest = Sha256::new();
        digest.update(b"pyhermit:blocking-vocabulary:v1\0");
        for values in [&self.atomic_concepts, &self.atomic_object_roles] {
            let length = u32::try_from(values.len()).unwrap_or(u32::MAX);
            digest.update(&length.to_le_bytes());
            for value in values {
                digest.update(&value.to_le_bytes());
            }
        }
        digest.finalize()
    }
}

fn relevant_fact<N: Copy + fmt::Debug + Eq + Ord>(
    fact: FactRecord<N>,
    nodes: &BTreeMap<N, NodeRecord<N>>,
) -> Result<RelevantFact<N>, BlockingError> {
    let mut argument_keys = Vec::with_capacity(fact.arguments.len());
    for argument in &fact.arguments {
        let record = nodes.get(argument).ok_or_else(|| {
            BlockingError::invariant("relevant blocking fact refers to an inactive node")
        })?;
        argument_keys.push(record.key);
    }
    Ok(RelevantFact {
        predicate_id: fact.predicate_id,
        argument_keys,
        arguments: fact.arguments,
        core: fact.core,
    })
}

fn state_digest<N: Copy + fmt::Debug + Eq + Ord>(
    ordered_nodes: &[N],
    nodes: &BTreeMap<N, NodeRecord<N>>,
    facts: &[RelevantFact<N>],
    vocabulary: &BlockingVocabulary,
) -> Result<[u8; 32], BlockingError> {
    let mut digest = Sha256::new();
    digest.update(b"pyhermit:blocking-label-state:v1\0");
    digest.update(&vocabulary.fingerprint_bytes());
    for node in ordered_nodes {
        let record = nodes
            .get(node)
            .ok_or_else(|| BlockingError::invariant("ordered blocking node is missing"))?;
        digest.update(&record.key.slot.to_le_bytes());
        digest.update(&record.key.generation.to_le_bytes());
        digest.update(&u64::from(record.creation_id).to_le_bytes());
        digest.update(record.kind.as_str().as_bytes());
        digest.update(&[0]);
        match record.parent {
            None => digest.update(b"N"),
            Some(parent) => {
                let parent = nodes.get(&parent).ok_or_else(|| {
                    BlockingError::invariant("blocking node parent is missing from projection")
                })?;
                digest.update(b"P");
                digest.update(&parent.key.slot.to_le_bytes());
                digest.update(&parent.key.generation.to_le_bytes());
            }
        }
    }
    for fact in facts {
        digest.update(&fact.predicate_id.to_le_bytes());
        let arity = u8::try_from(fact.argument_keys.len()).map_err(|_| {
            BlockingError::invariant("relevant blocking fact arity exceeds one byte")
        })?;
        digest.update(&[arity]);
        for key in &fact.argument_keys {
            digest.update(&key.slot.to_le_bytes());
            digest.update(&key.generation.to_le_bytes());
        }
        digest.update(if fact.core { b"1" } else { b"0" });
    }
    Ok(digest.finalize())
}

fn same_blocking_node<N: Eq>(left: Option<&NodeRecord<N>>, right: Option<&NodeRecord<N>>) -> bool {
    match (left, right) {
        (None, None) => true,
        (Some(left), Some(right)) => {
            left.node == right.node
                && left.key == right.key
                && left.creation_id == right.creation_id
                && left.kind == right.kind
                && left.lifecycle == right.lifecycle
                && left.parent == right.parent
        }
        _ => false,
    }
}

fn freeze<K: Ord>(source: BTreeMap<K, BTreeSet<u32>>) -> BTreeMap<K, Vec<u32>> {
    source
        .into_iter()
        .map(|(key, values)| (key, values.into_iter().collect()))
        .collect()
}

fn check_limit(
    observed: usize,
    allowed: usize,
    limit: &'static str,
    message: &'static str,
) -> Result<(), BlockingError> {
    if observed > allowed {
        return Err(BlockingError::resource(
            message,
            limit,
            u64::try_from(observed).unwrap_or(u64::MAX),
            u64::try_from(allowed).unwrap_or(u64::MAX),
        ));
    }
    Ok(())
}

fn estimate_bytes(nodes: usize, facts: usize) -> u64 {
    let value = nodes
        .saturating_mul(256)
        .saturating_add(facts.saturating_mul(96));
    u64::try_from(value).unwrap_or(u64::MAX)
}
