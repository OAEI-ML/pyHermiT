//! Deterministic batched hierarchy construction over compiled entity IDs.
// SPDX-License-Identifier: LGPL-3.0-or-later

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::mem::size_of;

use crate::error::{ErrorKind, NativeError, NativeResult};
use crate::session::OperationControl;

/// Classification strategy. Both modes are semantically identical.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ClassificationMode {
    Deterministic,
    QuasiOrder,
}

/// Bounded resources for one taxonomy operation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ClassificationLimits {
    pub max_elements: u32,
    pub max_seed_relations: u64,
    pub max_semantic_tests: u64,
    pub max_memory_bytes: u64,
}

impl Default for ClassificationLimits {
    fn default() -> Self {
        Self {
            max_elements: 5_000_000,
            max_seed_relations: 20_000_000,
            max_semantic_tests: 100_000_000,
            max_memory_bytes: 2 * 1024 * 1024 * 1024,
        }
    }
}

impl ClassificationLimits {
    fn validate(self) -> NativeResult<Self> {
        if self.max_elements < 2 {
            return Err(NativeError::wire(
                "classification max_elements must retain top and bottom",
            ));
        }
        if self.max_seed_relations == 0
            || self.max_semantic_tests == 0
            || self.max_memory_bytes == 0
        {
            return Err(NativeError::wire(
                "classification resource limits must be strictly positive",
            ));
        }
        Ok(self)
    }
}

/// Canonical finite hierarchy. Edges are the transitive reduction and point child to parent.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HierarchyIds {
    pub nodes: Vec<Vec<u32>>,
    pub edges: Vec<(u32, u32)>,
    pub top_node: u32,
    pub bottom_node: u32,
}

impl HierarchyIds {
    /// Validate the same invariants as Python's backend-neutral `HierarchyIds` contract.
    pub fn validate(&self) -> NativeResult<()> {
        if self.nodes.is_empty() || self.nodes.iter().any(Vec::is_empty) {
            return Err(NativeError::invariant(
                "classification hierarchy contains an empty node or no nodes",
            ));
        }
        if self.nodes.windows(2).any(|pair| pair[0] >= pair[1]) {
            return Err(NativeError::invariant(
                "classification hierarchy nodes are not canonical",
            ));
        }
        let mut members = BTreeSet::new();
        for node in &self.nodes {
            if node.windows(2).any(|pair| pair[0] >= pair[1]) {
                return Err(NativeError::invariant(
                    "classification hierarchy node members are not canonical",
                ));
            }
            if node.iter().any(|member| !members.insert(*member)) {
                return Err(NativeError::invariant(
                    "classification hierarchy nodes do not partition their members",
                ));
            }
        }
        let count = u32::try_from(self.nodes.len()).map_err(|_| {
            NativeError::invariant("classification hierarchy node count exceeds u32")
        })?;
        if self.top_node >= count || self.bottom_node >= count {
            return Err(NativeError::invariant(
                "classification top or bottom references an absent node",
            ));
        }
        if self.edges.windows(2).any(|pair| pair[0] >= pair[1]) {
            return Err(NativeError::invariant(
                "classification hierarchy edges are not canonical",
            ));
        }
        let count_usize = self.nodes.len();
        let mut successors = vec![Vec::new(); count_usize];
        let mut incoming = vec![0_u32; count_usize];
        for edge in &self.edges {
            if edge.0 >= count || edge.1 >= count || edge.0 == edge.1 {
                return Err(NativeError::invariant(
                    "classification hierarchy contains an invalid edge",
                ));
            }
            let child = usize::try_from(edge.0)
                .map_err(|_| NativeError::invariant("hierarchy child cannot fit usize"))?;
            let parent = usize::try_from(edge.1)
                .map_err(|_| NativeError::invariant("hierarchy parent cannot fit usize"))?;
            successors[child].push(parent);
            incoming[parent] = incoming[parent]
                .checked_add(1)
                .ok_or_else(|| NativeError::invariant("hierarchy in-degree overflow"))?;
        }

        let mut frontier = incoming
            .iter()
            .enumerate()
            .filter_map(|(node, degree)| (*degree == 0).then_some(node))
            .collect::<VecDeque<_>>();
        let mut processed = 0_usize;
        while let Some(node) = frontier.pop_front() {
            processed = processed.saturating_add(1);
            for &successor in &successors[node] {
                incoming[successor] = incoming[successor].checked_sub(1).ok_or_else(|| {
                    NativeError::invariant("hierarchy in-degree accounting underflow")
                })?;
                if incoming[successor] == 0 {
                    frontier.push_back(successor);
                }
            }
        }
        if processed != count_usize {
            return Err(NativeError::invariant(
                "classification hierarchy contains a cycle",
            ));
        }

        // An edge is redundant exactly when another direct parent of its child reaches the same
        // target. Taxonomies normally have tiny direct-parent sets; chains require no searches.
        for direct in &successors {
            if direct.len() < 2 {
                continue;
            }
            for &target in direct {
                let mut search = direct
                    .iter()
                    .copied()
                    .filter(|candidate| *candidate != target)
                    .collect::<Vec<_>>();
                let mut seen = vec![false; count_usize];
                while let Some(current) = search.pop() {
                    if current == target {
                        return Err(NativeError::invariant(
                            "classification hierarchy edges are not transitively reduced",
                        ));
                    }
                    if seen[current] {
                        continue;
                    }
                    seen[current] = true;
                    search.extend(successors[current].iter().copied());
                }
            }
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct ClassificationStatistics {
    pub elements: u32,
    pub semantic_tests: u64,
    pub batches: u64,
    pub cache_hits: u64,
    pub known_subsumptions: u64,
    pub possible_subsumptions: u64,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ClassificationResult {
    pub hierarchy: HierarchyIds,
    pub statistics: ClassificationStatistics,
}

/// Immutable inputs for one class or property taxonomy operation.
#[derive(Clone, Copy, Debug)]
pub struct ClassificationProblem<'a> {
    pub elements: &'a [u32],
    pub top: u32,
    pub bottom: u32,
    pub known: &'a [(u32, u32)],
    /// The told relation is semantically complete and can be collapsed without tableau checks.
    pub known_complete: bool,
    pub mode: ClassificationMode,
    pub limits: ClassificationLimits,
}

/// Build an exact taxonomy using batched semantic subsumption checks.
///
/// `elements` and `known` are required to be canonical so malformed IR cannot silently change
/// classification order. The tester receives missing `(child, parent)` pairs in deterministic
/// order and must return one Boolean per pair. Compiled IDs already follow canonical entity order,
/// so numeric order is the language-neutral equivalent of Python's structural-key order.
pub fn classify_ids<F>(
    problem: ClassificationProblem<'_>,
    control: &dyn OperationControl,
    mut tester: F,
) -> NativeResult<ClassificationResult>
where
    F: FnMut(&[(u32, u32)], &dyn OperationControl) -> NativeResult<Vec<bool>>,
{
    control.poll()?;
    let limits = problem.limits.validate()?;
    validate_inputs(
        problem.elements,
        problem.top,
        problem.bottom,
        problem.known,
        limits,
    )?;
    let elements = problem.elements;
    if problem.known_complete {
        let hierarchy = build_complete_hierarchy(
            elements,
            problem.top,
            problem.bottom,
            problem.known,
            limits,
            control,
        )?;
        return Ok(ClassificationResult {
            hierarchy,
            statistics: ClassificationStatistics {
                elements: u32::try_from(elements.len()).map_err(|_| {
                    NativeError::invariant("classification element count exceeds u32")
                })?,
                semantic_tests: 0,
                batches: 0,
                cache_hits: 0,
                known_subsumptions: usize_to_u64(problem.known.len()),
                possible_subsumptions: 0,
            },
        });
    }
    let mut seed = problem.known.iter().copied().collect::<BTreeSet<_>>();
    for &element in elements {
        seed.insert((problem.bottom, element));
        seed.insert((element, problem.top));
        seed.insert((element, element));
    }
    check_count(
        "max_seed_relations",
        usize_to_u64(seed.len()),
        limits.max_seed_relations,
    )?;

    let estimated = estimate_initial_memory(elements.len(), seed.len());
    check_count("max_memory_bytes", estimated, limits.max_memory_bytes)?;
    control.observe_memory(estimated)?;

    let mut oracle = Oracle::new(elements, seed, problem.mode, limits, control, &mut tester)?;
    let known_counts = oracle.child_counts();
    let mut ordered = elements
        .iter()
        .copied()
        .filter(|value| *value != problem.top && *value != problem.bottom)
        .collect::<Vec<_>>();
    ordered.sort_unstable_by_key(|value| {
        (known_counts.get(value).copied().unwrap_or_default(), *value)
    });

    let mut hierarchy = MutableHierarchy::new(problem.top, problem.bottom);
    for (offset, element) in ordered.into_iter().enumerate() {
        if offset % 1_024 == 0 {
            control.poll()?;
        }
        hierarchy.insert(element, &mut oracle)?;
    }
    let frozen = hierarchy.freeze()?;
    frozen.validate()?;
    let statistics = ClassificationStatistics {
        elements: u32::try_from(elements.len())
            .map_err(|_| NativeError::invariant("classification element count exceeds u32"))?,
        semantic_tests: oracle.semantic_tests,
        batches: oracle.batches,
        cache_hits: oracle.cache_hits,
        known_subsumptions: usize_to_u64(oracle.known.len()),
        possible_subsumptions: usize_to_u64(oracle.possible.len()),
    };
    Ok(ClassificationResult {
        hierarchy: frozen,
        statistics,
    })
}

fn validate_inputs(
    elements: &[u32],
    top: u32,
    bottom: u32,
    known: &[(u32, u32)],
    limits: ClassificationLimits,
) -> NativeResult<()> {
    if elements.len() < 2 || elements.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err(NativeError::wire(
            "classification elements must be sorted, unique, and contain top and bottom",
        ));
    }
    check_count(
        "max_elements",
        usize_to_u64(elements.len()),
        u64::from(limits.max_elements),
    )?;
    if top == bottom
        || elements.binary_search(&top).is_err()
        || elements.binary_search(&bottom).is_err()
    {
        return Err(NativeError::wire(
            "classification requires distinct top and bottom IDs from the element domain",
        ));
    }
    if known.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err(NativeError::wire(
            "known classification relations must be sorted and unique",
        ));
    }
    if known.iter().any(|&(child, parent)| {
        elements.binary_search(&child).is_err() || elements.binary_search(&parent).is_err()
    }) {
        return Err(NativeError::wire(
            "known classification relation references an absent element",
        ));
    }
    Ok(())
}

fn build_complete_hierarchy(
    elements: &[u32],
    top: u32,
    bottom: u32,
    semantic_edges: &[(u32, u32)],
    limits: ClassificationLimits,
    control: &dyn OperationControl,
) -> NativeResult<HierarchyIds> {
    let count = elements.len();
    let index_by_id = elements
        .iter()
        .enumerate()
        .map(|(index, value)| (*value, index))
        .collect::<BTreeMap<_, _>>();
    let top_index = *index_by_id
        .get(&top)
        .ok_or_else(|| NativeError::invariant("classification top disappeared"))?;
    let bottom_index = *index_by_id
        .get(&bottom)
        .ok_or_else(|| NativeError::invariant("classification bottom disappeared"))?;

    let mut successor_sets = vec![BTreeSet::new(); count];
    for &(child, parent) in semantic_edges {
        let child_index = *index_by_id
            .get(&child)
            .ok_or_else(|| NativeError::invariant("classification child disappeared"))?;
        let parent_index = *index_by_id
            .get(&parent)
            .ok_or_else(|| NativeError::invariant("classification parent disappeared"))?;
        successor_sets[child_index].insert(parent_index);
    }
    for index in 0..count {
        successor_sets[index].insert(index);
        successor_sets[bottom_index].insert(index);
        successor_sets[index].insert(top_index);
    }
    let successor_count = successor_sets.iter().map(BTreeSet::len).sum::<usize>();
    let estimated = estimate_initial_memory(count, successor_count);
    check_count("max_memory_bytes", estimated, limits.max_memory_bytes)?;
    control.observe_memory(estimated)?;
    let successors = successor_sets
        .into_iter()
        .map(|values| values.into_iter().collect::<Vec<_>>())
        .collect::<Vec<_>>();

    // Iterative Kosaraju matches the Python hierarchy builder without recursion limits.
    let mut visited = vec![false; count];
    let mut finish_order = Vec::with_capacity(count);
    let mut steps = 0_u64;
    for start in 0..count {
        if visited[start] {
            continue;
        }
        visited[start] = true;
        let mut stack = vec![(start, 0_usize)];
        while let Some((node, offset)) = stack.last_mut() {
            poll_graph_step(control, &mut steps)?;
            if *offset < successors[*node].len() {
                let successor = successors[*node][*offset];
                *offset = offset.saturating_add(1);
                if !visited[successor] {
                    visited[successor] = true;
                    stack.push((successor, 0));
                }
            } else {
                finish_order.push(*node);
                stack.pop();
            }
        }
    }

    let mut predecessors = vec![Vec::new(); count];
    for (child, parents) in successors.iter().enumerate() {
        for &parent in parents {
            predecessors[parent].push(child);
        }
    }
    let mut assigned = vec![false; count];
    let mut components = Vec::<BTreeSet<u32>>::new();
    let mut component_by_index = vec![usize::MAX; count];
    for &start in finish_order.iter().rev() {
        if assigned[start] {
            continue;
        }
        let component_id = components.len();
        let mut component = BTreeSet::new();
        let mut stack = vec![start];
        assigned[start] = true;
        while let Some(node) = stack.pop() {
            poll_graph_step(control, &mut steps)?;
            component.insert(elements[node]);
            component_by_index[node] = component_id;
            for &predecessor in predecessors[node].iter().rev() {
                if !assigned[predecessor] {
                    assigned[predecessor] = true;
                    stack.push(predecessor);
                }
            }
        }
        components.push(component);
    }
    if component_by_index.contains(&usize::MAX) {
        return Err(NativeError::invariant(
            "classification SCC traversal omitted an element",
        ));
    }

    let bottom_component = component_by_index[bottom_index];
    let top_component = component_by_index[top_index];
    let mut quotient = BTreeSet::new();
    for &(child, parent) in semantic_edges {
        let child_index = *index_by_id
            .get(&child)
            .ok_or_else(|| NativeError::invariant("classification child disappeared"))?;
        let parent_index = *index_by_id
            .get(&parent)
            .ok_or_else(|| NativeError::invariant("classification parent disappeared"))?;
        let child_component = component_by_index[child_index];
        let parent_component = component_by_index[parent_index];
        if child_component != parent_component
            && child_component != bottom_component
            && parent_component != top_component
        {
            quotient.insert((child_component, parent_component));
        }
    }
    let has_incoming = quotient
        .iter()
        .map(|(_, parent)| *parent)
        .collect::<BTreeSet<_>>();
    let has_outgoing = quotient
        .iter()
        .map(|(child, _)| *child)
        .collect::<BTreeSet<_>>();
    for component in 0..components.len() {
        if component == bottom_component || component == top_component {
            continue;
        }
        if !has_incoming.contains(&component) {
            quotient.insert((bottom_component, component));
        }
        if !has_outgoing.contains(&component) {
            quotient.insert((component, top_component));
        }
    }
    if bottom_component != top_component && quotient.is_empty() {
        quotient.insert((bottom_component, top_component));
    }
    let reduced = reduce_quotient(components.len(), &quotient, control, &mut steps)?;
    freeze_partition(components, reduced, top_component, bottom_component)
}

fn reduce_quotient(
    node_count: usize,
    edges: &BTreeSet<(usize, usize)>,
    control: &dyn OperationControl,
    steps: &mut u64,
) -> NativeResult<BTreeSet<(usize, usize)>> {
    let mut successors = vec![BTreeSet::new(); node_count];
    let mut incoming = vec![0_u32; node_count];
    for &(child, parent) in edges {
        if child >= node_count || parent >= node_count || child == parent {
            return Err(NativeError::invariant(
                "classification quotient contains an invalid edge",
            ));
        }
        successors[child].insert(parent);
        incoming[parent] = incoming[parent]
            .checked_add(1)
            .ok_or_else(|| NativeError::invariant("classification quotient in-degree overflow"))?;
    }
    let mut frontier = incoming
        .iter()
        .enumerate()
        .filter_map(|(node, degree)| (*degree == 0).then_some(node))
        .collect::<VecDeque<_>>();
    let mut processed = 0_usize;
    while let Some(node) = frontier.pop_front() {
        poll_graph_step(control, steps)?;
        processed = processed.saturating_add(1);
        for &parent in &successors[node] {
            incoming[parent] = incoming[parent]
                .checked_sub(1)
                .ok_or_else(|| NativeError::invariant("classification in-degree underflow"))?;
            if incoming[parent] == 0 {
                frontier.push_back(parent);
            }
        }
    }
    if processed != node_count {
        return Err(NativeError::invariant(
            "classification quotient relation contains a cycle",
        ));
    }

    for &(child, parent) in edges {
        successors[child].remove(&parent);
        if !reachable_indices(&successors, child, parent, control, steps)? {
            successors[child].insert(parent);
        }
    }
    Ok(successors
        .into_iter()
        .enumerate()
        .flat_map(|(child, parents)| parents.into_iter().map(move |parent| (child, parent)))
        .collect())
}

fn reachable_indices(
    successors: &[BTreeSet<usize>],
    start: usize,
    target: usize,
    control: &dyn OperationControl,
    steps: &mut u64,
) -> NativeResult<bool> {
    let mut frontier = successors[start].iter().copied().collect::<Vec<_>>();
    let mut seen = vec![false; successors.len()];
    seen[start] = true;
    while let Some(current) = frontier.pop() {
        poll_graph_step(control, steps)?;
        if current == target {
            return Ok(true);
        }
        if seen[current] {
            continue;
        }
        seen[current] = true;
        frontier.extend(
            successors[current]
                .iter()
                .rev()
                .filter(|candidate| !seen[**candidate])
                .copied(),
        );
    }
    Ok(false)
}

fn freeze_partition(
    components: Vec<BTreeSet<u32>>,
    edges: BTreeSet<(usize, usize)>,
    top_component: usize,
    bottom_component: usize,
) -> NativeResult<HierarchyIds> {
    let mut ordered = components.into_iter().enumerate().collect::<Vec<_>>();
    ordered.sort_unstable_by(|left, right| left.1.cmp(&right.1));
    let mut remap = vec![0_u32; ordered.len()];
    for (new, (old, _)) in ordered.iter().enumerate() {
        remap[*old] = u32::try_from(new).map_err(|_| {
            NativeError::invariant("classification hierarchy node count exceeds u32")
        })?;
    }
    let mut remapped_edges = edges
        .into_iter()
        .map(|(child, parent)| (remap[child], remap[parent]))
        .collect::<Vec<_>>();
    remapped_edges.sort_unstable();
    let hierarchy = HierarchyIds {
        nodes: ordered
            .into_iter()
            .map(|(_, members)| members.into_iter().collect())
            .collect(),
        edges: remapped_edges,
        top_node: remap[top_component],
        bottom_node: remap[bottom_component],
    };
    hierarchy.validate()?;
    Ok(hierarchy)
}

fn poll_graph_step(control: &dyn OperationControl, steps: &mut u64) -> NativeResult<()> {
    *steps = steps
        .checked_add(1)
        .ok_or_else(|| NativeError::invariant("classification graph-step counter overflow"))?;
    if *steps % 1_024 == 0 {
        control.poll()?;
    }
    Ok(())
}

struct Oracle<'a, F> {
    elements: &'a [u32],
    known: BTreeSet<(u32, u32)>,
    successors: BTreeMap<u32, BTreeSet<u32>>,
    cache: BTreeMap<(u32, u32), bool>,
    possible: BTreeSet<(u32, u32)>,
    mode: ClassificationMode,
    limits: ClassificationLimits,
    control: &'a dyn OperationControl,
    tester: &'a mut F,
    semantic_tests: u64,
    batches: u64,
    cache_hits: u64,
}

impl<'a, F> Oracle<'a, F>
where
    F: FnMut(&[(u32, u32)], &dyn OperationControl) -> NativeResult<Vec<bool>>,
{
    fn new(
        elements: &'a [u32],
        known: BTreeSet<(u32, u32)>,
        mode: ClassificationMode,
        limits: ClassificationLimits,
        control: &'a dyn OperationControl,
        tester: &'a mut F,
    ) -> NativeResult<Self> {
        let mut successors = elements
            .iter()
            .map(|value| (*value, BTreeSet::new()))
            .collect::<BTreeMap<_, _>>();
        for &(child, parent) in &known {
            successors
                .get_mut(&child)
                .ok_or_else(|| NativeError::invariant("known child is absent"))?
                .insert(parent);
        }
        let cache = known.iter().map(|relation| (*relation, true)).collect();
        Ok(Self {
            elements,
            known,
            successors,
            cache,
            possible: BTreeSet::new(),
            mode,
            limits,
            control,
            tester,
            semantic_tests: 0,
            batches: 0,
            cache_hits: 0,
        })
    }

    fn child_counts(&self) -> BTreeMap<u32, u64> {
        let mut result = self
            .elements
            .iter()
            .map(|element| (*element, 0_u64))
            .collect::<BTreeMap<_, _>>();
        for &(child, _) in &self.known {
            if let Some(count) = result.get_mut(&child) {
                *count = count.saturating_add(1);
            }
        }
        result
    }

    fn evaluate(&mut self, relations: &[(u32, u32)]) -> NativeResult<Vec<bool>> {
        self.control.poll()?;
        let mut missing = Vec::new();
        let mut missing_set = BTreeSet::new();
        for &relation in relations {
            if self.cache.contains_key(&relation) {
                self.cache_hits = self.cache_hits.saturating_add(1);
            } else if self.is_known(relation.0, relation.1)? {
                self.cache.insert(relation, true);
                self.cache_hits = self.cache_hits.saturating_add(1);
            } else if missing_set.insert(relation) {
                missing.push(relation);
            }
        }
        if !missing.is_empty() {
            let observed = self
                .semantic_tests
                .checked_add(usize_to_u64(missing.len()))
                .ok_or_else(|| NativeError::invariant("semantic-test counter overflow"))?;
            check_count(
                "max_semantic_tests",
                observed,
                self.limits.max_semantic_tests,
            )?;
            if self.mode == ClassificationMode::QuasiOrder {
                self.possible.extend(missing.iter().copied());
            }
            let outcomes = (self.tester)(&missing, self.control)?;
            if outcomes.len() != missing.len() {
                return Err(NativeError::invariant(
                    "classification tester returned the wrong result count",
                ));
            }
            self.semantic_tests = observed;
            self.batches = self
                .batches
                .checked_add(1)
                .ok_or_else(|| NativeError::invariant("classification batch counter overflow"))?;
            for (relation, entailed) in missing.into_iter().zip(outcomes) {
                self.cache.insert(relation, entailed);
                self.possible.remove(&relation);
                if entailed {
                    self.add_known(relation)?;
                }
            }
            let memory =
                estimate_oracle_memory(self.known.len(), self.cache.len(), self.possible.len());
            check_count("max_memory_bytes", memory, self.limits.max_memory_bytes)?;
            self.control.observe_memory(memory)?;
            self.control.poll()?;
        }
        relations
            .iter()
            .map(|relation| {
                self.cache.get(relation).copied().ok_or_else(|| {
                    NativeError::invariant("classification oracle failed to cache a result")
                })
            })
            .collect()
    }

    fn add_known(&mut self, relation: (u32, u32)) -> NativeResult<()> {
        if self.cache.get(&relation) == Some(&false) {
            return Err(NativeError::invariant(
                "classification tester returned contradictory subsumption results",
            ));
        }
        self.known.insert(relation);
        self.successors
            .get_mut(&relation.0)
            .ok_or_else(|| NativeError::invariant("classification child disappeared"))?
            .insert(relation.1);
        self.possible.remove(&relation);
        self.cache.insert(relation, true);
        Ok(())
    }

    fn is_known(&self, child: u32, parent: u32) -> NativeResult<bool> {
        let mut frontier = vec![child];
        let mut visited = BTreeSet::new();
        let mut steps = 0_usize;
        while let Some(current) = frontier.pop() {
            if current == parent {
                return Ok(true);
            }
            if !visited.insert(current) {
                continue;
            }
            steps = steps.saturating_add(1);
            if steps % 1_024 == 0 {
                self.control.poll()?;
            }
            let successors = self.successors.get(&current).ok_or_else(|| {
                NativeError::invariant("classification closure reached an absent element")
            })?;
            frontier.extend(
                successors
                    .iter()
                    .rev()
                    .filter(|value| !visited.contains(value)),
            );
        }
        Ok(false)
    }
}

struct MutableHierarchy {
    top_node: usize,
    bottom_node: usize,
    members: Vec<BTreeSet<u32>>,
    edges: BTreeSet<(usize, usize)>,
}

impl MutableHierarchy {
    fn new(top: u32, bottom: u32) -> Self {
        Self {
            top_node: 0,
            bottom_node: 1,
            members: vec![BTreeSet::from([top]), BTreeSet::from([bottom])],
            edges: BTreeSet::from([(1, 0)]),
        }
    }

    fn insert<F>(&mut self, element: u32, oracle: &mut Oracle<'_, F>) -> NativeResult<()>
    where
        F: FnMut(&[(u32, u32)], &dyn OperationControl) -> NativeResult<Vec<bool>>,
    {
        let parents = self.boundary(self.top_node, false, element, oracle)?;
        let children = self.boundary(self.bottom_node, true, element, oracle)?;
        let common = parents.intersection(&children).copied().collect::<Vec<_>>();
        if !common.is_empty() {
            if parents != children || common.len() != 1 {
                return Err(NativeError::invariant(
                    "subsumption relation violated hierarchy-search invariants",
                ));
            }
            self.members
                .get_mut(common[0])
                .ok_or_else(|| NativeError::invariant("classification node disappeared"))?
                .insert(element);
            return Ok(());
        }
        let node = self.members.len();
        self.members.push(BTreeSet::from([element]));
        for &child in &children {
            for &parent in &parents {
                self.edges.remove(&(child, parent));
            }
        }
        self.edges
            .extend(children.iter().map(|child| (*child, node)));
        self.edges
            .extend(parents.iter().map(|parent| (node, *parent)));
        Ok(())
    }

    fn boundary<F>(
        &self,
        start: usize,
        upward: bool,
        element: u32,
        oracle: &mut Oracle<'_, F>,
    ) -> NativeResult<BTreeSet<usize>>
    where
        F: FnMut(&[(u32, u32)], &dyn OperationControl) -> NativeResult<Vec<bool>>,
    {
        let mut frontier = BTreeSet::from([start]);
        let mut visited = BTreeSet::new();
        let mut proven_true = BTreeSet::from([start]);
        let mut boundary = BTreeSet::new();
        while !frontier.is_empty() {
            oracle.control.poll()?;
            let ordered_frontier = frontier.iter().copied().collect::<Vec<_>>();
            let candidates_by_node = ordered_frontier
                .iter()
                .map(|node| {
                    let candidates = self
                        .edges
                        .iter()
                        .filter_map(|&(child, parent)| {
                            if upward && child == *node {
                                Some(parent)
                            } else if !upward && parent == *node {
                                Some(child)
                            } else {
                                None
                            }
                        })
                        .collect::<BTreeSet<_>>();
                    (*node, candidates)
                })
                .collect::<Vec<_>>();
            let candidates = candidates_by_node
                .iter()
                .flat_map(|(_, values)| values.iter().copied())
                .filter(|value| !visited.contains(value))
                .collect::<BTreeSet<_>>();
            let candidate_nodes = candidates.iter().copied().collect::<Vec<_>>();
            let relations = candidate_nodes
                .iter()
                .map(|candidate| {
                    self.representative(*candidate).map(|representative| {
                        if upward {
                            (representative, element)
                        } else {
                            (element, representative)
                        }
                    })
                })
                .collect::<NativeResult<Vec<_>>>()?;
            let outcomes = oracle.evaluate(&relations)?;
            let true_candidates = candidate_nodes
                .into_iter()
                .zip(outcomes)
                .filter_map(|(candidate, outcome)| outcome.then_some(candidate))
                .collect::<BTreeSet<_>>();
            proven_true.extend(true_candidates.iter().copied());
            for (node, node_candidates) in candidates_by_node {
                if node_candidates.is_disjoint(&proven_true) {
                    boundary.insert(node);
                }
            }
            visited.extend(ordered_frontier);
            frontier = true_candidates.difference(&visited).copied().collect();
        }
        Ok(boundary)
    }

    fn representative(&self, node: usize) -> NativeResult<u32> {
        self.members
            .get(node)
            .and_then(BTreeSet::first)
            .copied()
            .ok_or_else(|| NativeError::invariant("classification hierarchy node is empty"))
    }

    fn freeze(self) -> NativeResult<HierarchyIds> {
        let mut ordered = self
            .members
            .into_iter()
            .enumerate()
            .map(|(old, members)| (old, members.into_iter().collect::<Vec<_>>()))
            .collect::<Vec<_>>();
        ordered.sort_unstable_by(|left, right| left.1.cmp(&right.1));
        let mut remap = vec![0_u32; ordered.len()];
        for (new, (old, _)) in ordered.iter().enumerate() {
            remap[*old] = u32::try_from(new).map_err(|_| {
                NativeError::invariant("classification hierarchy node count exceeds u32")
            })?;
        }
        let mut edges = self
            .edges
            .into_iter()
            .map(|(child, parent)| (remap[child], remap[parent]))
            .collect::<Vec<_>>();
        edges.sort_unstable();
        Ok(HierarchyIds {
            nodes: ordered.into_iter().map(|(_, members)| members).collect(),
            edges,
            top_node: remap[self.top_node],
            bottom_node: remap[self.bottom_node],
        })
    }
}

fn estimate_initial_memory(elements: usize, relations: usize) -> u64 {
    usize_to_u64(elements)
        .saturating_mul(usize_to_u64(size_of::<u32>() + size_of::<BTreeSet<u32>>()))
        .saturating_add(
            usize_to_u64(relations).saturating_mul(usize_to_u64(size_of::<(u32, u32)>() * 4)),
        )
}

fn estimate_oracle_memory(known: usize, cache: usize, possible: usize) -> u64 {
    usize_to_u64(known)
        .saturating_mul(usize_to_u64(size_of::<(u32, u32)>() * 2))
        .saturating_add(
            usize_to_u64(cache).saturating_mul(usize_to_u64(size_of::<((u32, u32), bool)>() * 2)),
        )
        .saturating_add(
            usize_to_u64(possible).saturating_mul(usize_to_u64(size_of::<(u32, u32)>() * 2)),
        )
}

fn usize_to_u64(value: usize) -> u64 {
    u64::try_from(value).unwrap_or(u64::MAX)
}

fn check_count(limit: &'static str, observed: u64, allowed: u64) -> NativeResult<()> {
    if observed > allowed {
        return Err(NativeError::new(
            ErrorKind::Resource,
            "RESOURCE_LIMIT",
            format!("native classification resource limit exceeded: {limit}"),
        )
        .with_context("limit", limit)
        .with_context("observed", observed.to_string())
        .with_context("allowed", allowed.to_string()));
    }
    Ok(())
}
