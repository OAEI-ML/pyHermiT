//! Canonical named-individual realization over one completed tableau model.
// SPDX-License-Identifier: LGPL-3.0-or-later

use std::collections::{BTreeMap, BTreeSet};
use std::mem::size_of;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

use crate::error::{ErrorKind, NativeError, NativeResult};
use crate::result_wire::RealizationWireResult;
use crate::session::OperationControl;

type SameAsBuild = (Vec<Vec<u32>>, BTreeMap<u32, u32>);

/// A model-side individual reference. Non-named nodes can affect reasoning but never answers.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ModelIndividual {
    Named(u32),
    Anonymous(u64),
    Internal(u64),
}

/// One named source individual and the completed model equality class containing it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct NamedIndividualRecord {
    pub individual_id: u32,
    pub equality_key: u64,
}

/// A direct class-node membership from the completed model.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct DirectTypeFact {
    pub subject: ModelIndividual,
    pub class_node_id: u32,
}

/// An entailed object-property target from the completed model.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ObjectTargetFact {
    pub subject: ModelIndividual,
    pub property_id: u32,
    pub target: ModelIndividual,
}

/// An entailed finite source-literal answer from the completed model.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct DataTargetFact {
    pub subject: ModelIndividual,
    pub property_id: u32,
    pub source_literal_id: u32,
}

/// An entailed different-from relation from the completed model.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct DifferentFromFact {
    pub left: ModelIndividual,
    pub right: ModelIndividual,
}

/// Identity of the permanent completed model used to invalidate realization results.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RealizationCacheKey {
    pub ontology_fingerprint: [u8; 32],
    pub model_revision: u64,
}

impl RealizationCacheKey {
    #[must_use]
    pub const fn new(ontology_fingerprint: [u8; 32], model_revision: u64) -> Self {
        Self {
            ontology_fingerprint,
            model_revision,
        }
    }
}

/// Zero-copy read access required from an already completed, consistent tableau model.
///
/// The access implementation performs no Python callback and must expose *entailed* direct class,
/// object, data, and different-from facts after role, datatype, and equality reasoning. This
/// component canonicalizes and validates those answers; it deliberately does not perform missing
/// tableau reasoning or infer directness.
pub trait CompletedModelAccess: Send + Sync {
    fn cache_key(&self) -> RealizationCacheKey;
    fn named_individuals(&self) -> &[NamedIndividualRecord];
    fn class_node_count(&self) -> u32;
    fn object_property_ids(&self) -> &[u32];
    fn data_property_ids(&self) -> &[u32];
    fn source_literal_ids(&self) -> &[u32];
    fn direct_type_facts(&self) -> &[DirectTypeFact];
    fn object_target_facts(&self) -> &[ObjectTargetFact];
    fn data_target_facts(&self) -> &[DataTargetFact];
    fn different_from_facts(&self) -> &[DifferentFromFact];
}

/// Per-operation bounds for canonical realization construction.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RealizationLimits {
    pub max_named_individuals: u32,
    pub max_class_nodes: u32,
    pub max_property_ids: u32,
    pub max_source_literals: u32,
    pub max_facts: u64,
    pub max_result_rows: u64,
    pub max_result_values: u64,
    pub max_memory_bytes: u64,
    pub poll_stride: u32,
}

impl Default for RealizationLimits {
    fn default() -> Self {
        Self {
            max_named_individuals: 5_000_000,
            max_class_nodes: 5_000_000,
            max_property_ids: 10_000_000,
            max_source_literals: 20_000_000,
            max_facts: 200_000_000,
            max_result_rows: 100_000_000,
            max_result_values: 400_000_000,
            max_memory_bytes: 2 * 1024 * 1024 * 1024,
            poll_stride: 1_024,
        }
    }
}

impl RealizationLimits {
    fn validate(self) -> NativeResult<Self> {
        if self.max_named_individuals == 0
            || self.max_class_nodes == 0
            || self.max_property_ids == 0
            || self.max_source_literals == 0
            || self.max_facts == 0
            || self.max_result_rows == 0
            || self.max_result_values == 0
            || self.max_memory_bytes == 0
            || self.poll_stride == 0
        {
            return Err(NativeError::wire(
                "realization resource limits and polling stride must be strictly positive",
            ));
        }
        Ok(self)
    }
}

/// Deterministic work and result-size accounting for one realization operation.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct RealizationStatistics {
    pub named_individuals: u32,
    pub same_as_groups: u32,
    pub source_literals: u32,
    pub facts_scanned: u64,
    pub excluded_non_named_facts: u64,
    pub result_rows: u64,
    pub result_values: u64,
    pub estimated_memory_bytes: u64,
    pub cache_hit: bool,
}

/// An immutable canonical counterpart of Python's `RealizationIds`.
///
/// Fields stay private so a validated result cannot subsequently be made noncanonical. Accessors
/// borrow the compact vectors, and consuming conversion to [`RealizationWireResult`] moves those
/// vectors without a semantic remapping or another allocation.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct RealizationIds {
    same_as: Vec<Vec<u32>>,
    direct_types: Vec<(u32, Vec<u32>)>,
    object_targets: Vec<(u32, u32, Vec<u32>)>,
    data_targets: Vec<(u32, u32, Vec<u32>)>,
    different_from: Vec<(u32, u32)>,
}

impl RealizationIds {
    #[must_use]
    pub fn same_as(&self) -> &[Vec<u32>] {
        &self.same_as
    }

    #[must_use]
    pub fn direct_types(&self) -> &[(u32, Vec<u32>)] {
        &self.direct_types
    }

    #[must_use]
    pub fn object_targets(&self) -> &[(u32, u32, Vec<u32>)] {
        &self.object_targets
    }

    #[must_use]
    pub fn data_targets(&self) -> &[(u32, u32, Vec<u32>)] {
        &self.data_targets
    }

    #[must_use]
    pub fn different_from(&self) -> &[(u32, u32)] {
        &self.different_from
    }

    #[must_use]
    pub fn estimated_memory_bytes(&self) -> u64 {
        estimate_result_memory(self)
    }

    /// Clone the already canonical IDs into the current owned result-wire container.
    #[must_use]
    pub fn to_wire_result(&self) -> RealizationWireResult {
        self.into()
    }

    /// Move canonical vectors into the current result-wire container without reallocating them.
    #[must_use]
    pub fn into_wire_result(self) -> RealizationWireResult {
        self.into()
    }
}

impl From<RealizationIds> for RealizationWireResult {
    fn from(value: RealizationIds) -> Self {
        Self {
            same_as: value.same_as,
            direct_types: value.direct_types,
            object_targets: value.object_targets,
            data_targets: value.data_targets,
            different_from: value.different_from,
        }
    }
}

impl From<&RealizationIds> for RealizationWireResult {
    fn from(value: &RealizationIds) -> Self {
        Self {
            same_as: value.same_as.clone(),
            direct_types: value.direct_types.clone(),
            object_targets: value.object_targets.clone(),
            data_targets: value.data_targets.clone(),
            different_from: value.different_from.clone(),
        }
    }
}

/// One immutable realization result and its nonsemantic operation statistics.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RealizationResult {
    ids: Arc<RealizationIds>,
    statistics: RealizationStatistics,
}

impl RealizationResult {
    #[must_use]
    pub const fn ids(&self) -> &Arc<RealizationIds> {
        &self.ids
    }

    #[must_use]
    pub fn into_ids(self) -> Arc<RealizationIds> {
        self.ids
    }

    #[must_use]
    pub const fn statistics(&self) -> RealizationStatistics {
        self.statistics
    }

    #[must_use]
    pub fn to_wire_result(&self) -> RealizationWireResult {
        self.ids.to_wire_result()
    }

    fn cached(entry: &CacheEntry) -> Self {
        let mut statistics = entry.statistics;
        statistics.cache_hit = true;
        Self {
            ids: Arc::clone(&entry.ids),
            statistics,
        }
    }
}

/// Build a complete canonical result without caching it.
pub fn build_realization_ids(
    model: &(dyn CompletedModelAccess + '_),
    limits: RealizationLimits,
    control: &dyn OperationControl,
) -> NativeResult<RealizationResult> {
    control.poll()?;
    let limits = limits.validate()?;
    validate_input_counts(model, limits)?;

    let object_properties = canonical_domain(
        model.object_property_ids(),
        "object-property ID domain",
        limits.max_property_ids,
    )?;
    let data_properties = canonical_domain(
        model.data_property_ids(),
        "data-property ID domain",
        limits.max_property_ids,
    )?;
    let source_literals = canonical_domain(
        model.source_literal_ids(),
        "source-literal ID domain",
        limits.max_source_literals,
    )?;
    if model.class_node_count() > limits.max_class_nodes {
        return Err(resource_error(
            "max_class_nodes",
            u64::from(model.class_node_count()),
            u64::from(limits.max_class_nodes),
        ));
    }

    let (same_as, group_by_individual) = build_same_as(model, limits, control)?;
    let mut direct: BTreeMap<u32, BTreeSet<u32>> = BTreeMap::new();
    let mut objects: BTreeMap<(u32, u32), BTreeSet<u32>> = BTreeMap::new();
    let mut data: BTreeMap<(u32, u32), BTreeSet<u32>> = BTreeMap::new();
    let mut different = BTreeSet::new();
    let mut facts_scanned = 0_u64;
    let mut excluded = 0_u64;

    for fact in model.direct_type_facts() {
        scan_checkpoint(&mut facts_scanned, limits, control)?;
        let Some(group) = public_group(fact.subject, &group_by_individual, "direct type")? else {
            excluded = checked_increment(excluded, "excluded-fact counter")?;
            continue;
        };
        if fact.class_node_id >= model.class_node_count() {
            return Err(NativeError::invariant(
                "completed realization direct type references an absent class node",
            ));
        }
        direct.entry(group).or_default().insert(fact.class_node_id);
    }
    observe_working_memory(&same_as, direct.len(), 0, facts_scanned, limits, control)?;

    for fact in model.object_target_facts() {
        scan_checkpoint(&mut facts_scanned, limits, control)?;
        let subject = public_group(fact.subject, &group_by_individual, "object target subject")?;
        let target = public_group(fact.target, &group_by_individual, "object target object")?;
        let (Some(subject), Some(target)) = (subject, target) else {
            excluded = checked_increment(excluded, "excluded-fact counter")?;
            continue;
        };
        if !object_properties.contains(&fact.property_id) {
            return Err(NativeError::invariant(
                "completed realization object fact references an absent property",
            ));
        }
        objects
            .entry((subject, fact.property_id))
            .or_default()
            .insert(target);
    }
    observe_working_memory(
        &same_as,
        direct.len(),
        objects.len(),
        facts_scanned,
        limits,
        control,
    )?;

    for fact in model.data_target_facts() {
        scan_checkpoint(&mut facts_scanned, limits, control)?;
        let Some(subject) =
            public_group(fact.subject, &group_by_individual, "data target subject")?
        else {
            excluded = checked_increment(excluded, "excluded-fact counter")?;
            continue;
        };
        if !data_properties.contains(&fact.property_id) {
            return Err(NativeError::invariant(
                "completed realization data fact references an absent property",
            ));
        }
        if !source_literals.contains(&fact.source_literal_id) {
            return Err(NativeError::invariant(
                "completed realization data fact references an absent source literal",
            ));
        }
        data.entry((subject, fact.property_id))
            .or_default()
            .insert(fact.source_literal_id);
    }

    for fact in model.different_from_facts() {
        scan_checkpoint(&mut facts_scanned, limits, control)?;
        let left = public_group(fact.left, &group_by_individual, "different-from left")?;
        let right = public_group(fact.right, &group_by_individual, "different-from right")?;
        let (Some(left), Some(right)) = (left, right) else {
            excluded = checked_increment(excluded, "excluded-fact counter")?;
            continue;
        };
        if left == right {
            return Err(NativeError::invariant(
                "completed model entails different-from inside one same-as group",
            ));
        }
        different.insert(if left < right {
            (left, right)
        } else {
            (right, left)
        });
    }

    let direct_types = direct
        .into_iter()
        .map(|(group, values)| (group, values.into_iter().collect()))
        .collect::<Vec<_>>();
    let object_targets = objects
        .into_iter()
        .map(|((subject, property), values)| (subject, property, values.into_iter().collect()))
        .collect::<Vec<_>>();
    let data_targets = data
        .into_iter()
        .map(|((subject, property), values)| (subject, property, values.into_iter().collect()))
        .collect::<Vec<_>>();
    let different_from = different.into_iter().collect::<Vec<_>>();
    let ids = RealizationIds {
        same_as,
        direct_types,
        object_targets,
        data_targets,
        different_from,
    };
    let (result_rows, result_values) = result_counts(&ids)?;
    check_count("max_result_rows", result_rows, limits.max_result_rows)?;
    check_count("max_result_values", result_values, limits.max_result_values)?;
    let estimated_memory_bytes = ids.estimated_memory_bytes();
    check_count(
        "max_memory_bytes",
        estimated_memory_bytes,
        limits.max_memory_bytes,
    )?;
    control.observe_memory(estimated_memory_bytes)?;
    control.poll()?;

    let named_individuals = u32::try_from(model.named_individuals().len())
        .map_err(|_| NativeError::invariant("named-individual count exceeds u32"))?;
    let same_as_groups = u32::try_from(ids.same_as.len())
        .map_err(|_| NativeError::invariant("same-as group count exceeds u32"))?;
    let source_literal_count = u32::try_from(source_literals.len())
        .map_err(|_| NativeError::invariant("source-literal count exceeds u32"))?;
    Ok(RealizationResult {
        ids: Arc::new(ids),
        statistics: RealizationStatistics {
            named_individuals,
            same_as_groups,
            source_literals: source_literal_count,
            facts_scanned,
            excluded_non_named_facts: excluded,
            result_rows,
            result_values,
            estimated_memory_bytes,
            cache_hit: false,
        },
    })
}

/// How an operation-local staged cache entry is finalized.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RealizationCacheDisposition {
    Promote,
    Rollback,
}

/// Owner-stamped token preventing cross-cache or stale transaction finalization.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RealizationCacheOperation {
    owner: u64,
    sequence: u64,
}

#[derive(Clone, Debug)]
struct CacheEntry {
    key: RealizationCacheKey,
    ids: Arc<RealizationIds>,
    statistics: RealizationStatistics,
}

#[derive(Clone, Debug)]
struct ActiveCacheOperation {
    token: RealizationCacheOperation,
    key: RealizationCacheKey,
    staged: Option<CacheEntry>,
}

static NEXT_CACHE_OWNER: AtomicU64 = AtomicU64::new(1);

/// A permanent-result cache with explicit operation-local staging.
///
/// `lookup` never exposes `active.staged`. Promotion replaces the committed entry in one
/// assignment; rollback preserves the previous committed entry even after a failed rebuild.
#[derive(Debug)]
pub struct RealizationCache {
    owner: u64,
    next_sequence: u64,
    committed: Option<CacheEntry>,
    active: Option<ActiveCacheOperation>,
}

impl Default for RealizationCache {
    fn default() -> Self {
        Self::new()
    }
}

impl RealizationCache {
    #[must_use]
    pub fn new() -> Self {
        let owner = NEXT_CACHE_OWNER.fetch_add(1, Ordering::Relaxed);
        Self {
            owner,
            next_sequence: 1,
            committed: None,
            active: None,
        }
    }

    #[must_use]
    pub fn lookup(&self, key: RealizationCacheKey) -> Option<Arc<RealizationIds>> {
        self.committed
            .as_ref()
            .filter(|entry| entry.key == key)
            .map(|entry| Arc::clone(&entry.ids))
    }

    pub fn begin_operation(
        &mut self,
        key: RealizationCacheKey,
    ) -> NativeResult<RealizationCacheOperation> {
        if self.active.is_some() {
            return Err(NativeError::new(
                ErrorKind::Busy,
                "CONCURRENT_MUTATION",
                "a realization cache operation is already active",
            ));
        }
        let sequence = self.next_sequence;
        self.next_sequence = self
            .next_sequence
            .checked_add(1)
            .ok_or_else(|| NativeError::invariant("realization cache sequence overflow"))?;
        let token = RealizationCacheOperation {
            owner: self.owner,
            sequence,
        };
        self.active = Some(ActiveCacheOperation {
            token,
            key,
            staged: None,
        });
        Ok(token)
    }

    pub fn stage(
        &mut self,
        token: RealizationCacheOperation,
        result: RealizationResult,
    ) -> NativeResult<()> {
        let active = self.require_active_mut(token)?;
        if active.staged.is_some() {
            return Err(NativeError::invariant(
                "realization cache operation already has a staged result",
            ));
        }
        active.staged = Some(CacheEntry {
            key: active.key,
            ids: result.ids,
            statistics: result.statistics,
        });
        Ok(())
    }

    pub fn finish_operation(
        &mut self,
        token: RealizationCacheOperation,
        disposition: RealizationCacheDisposition,
    ) -> NativeResult<()> {
        let active = self.require_active(token)?;
        if disposition == RealizationCacheDisposition::Promote && active.staged.is_none() {
            return Err(NativeError::invariant(
                "cannot promote a realization cache operation without a complete result",
            ));
        }
        let mut active = self
            .active
            .take()
            .ok_or_else(|| NativeError::invariant("realization cache operation disappeared"))?;
        if disposition == RealizationCacheDisposition::Promote {
            self.committed = active.staged.take();
        }
        Ok(())
    }

    pub fn invalidate(&mut self) -> NativeResult<()> {
        if self.active.is_some() {
            return Err(NativeError::new(
                ErrorKind::Busy,
                "CONCURRENT_MUTATION",
                "cannot invalidate a realization cache during an active operation",
            ));
        }
        self.committed = None;
        Ok(())
    }

    fn cached_result(&self, key: RealizationCacheKey) -> Option<RealizationResult> {
        self.committed
            .as_ref()
            .filter(|entry| entry.key == key)
            .map(RealizationResult::cached)
    }

    fn require_active(
        &self,
        token: RealizationCacheOperation,
    ) -> NativeResult<&ActiveCacheOperation> {
        if token.owner != self.owner {
            return Err(NativeError::invariant(
                "realization cache operation belongs to another cache",
            ));
        }
        self.active
            .as_ref()
            .filter(|active| active.token == token)
            .ok_or_else(|| NativeError::invariant("realization cache operation token is stale"))
    }

    fn require_active_mut(
        &mut self,
        token: RealizationCacheOperation,
    ) -> NativeResult<&mut ActiveCacheOperation> {
        if token.owner != self.owner {
            return Err(NativeError::invariant(
                "realization cache operation belongs to another cache",
            ));
        }
        self.active
            .as_mut()
            .filter(|active| active.token == token)
            .ok_or_else(|| NativeError::invariant("realization cache operation token is stale"))
    }
}

/// Return a committed result or build and atomically promote a complete replacement.
pub fn realize_cached(
    model: &(dyn CompletedModelAccess + '_),
    cache: &mut RealizationCache,
    limits: RealizationLimits,
    control: &dyn OperationControl,
) -> NativeResult<RealizationResult> {
    control.poll()?;
    let key = model.cache_key();
    if let Some(result) = cache.cached_result(key) {
        control.observe_memory(result.statistics.estimated_memory_bytes)?;
        control.poll()?;
        return Ok(result);
    }

    let operation = cache.begin_operation(key)?;
    let built = match build_realization_ids(model, limits, control) {
        Ok(result) => result,
        Err(error) => {
            return Err(rollback_after_error(cache, operation, error));
        }
    };
    let returned = built.clone();
    if let Err(error) = cache.stage(operation, built) {
        return Err(rollback_after_error(cache, operation, error));
    }
    // The builder's final poll is the operation publication checkpoint. From staging through
    // promotion there are intentionally no cancellation points or other fallible model work.
    cache.finish_operation(operation, RealizationCacheDisposition::Promote)?;
    Ok(returned)
}

fn rollback_after_error(
    cache: &mut RealizationCache,
    operation: RealizationCacheOperation,
    original: NativeError,
) -> NativeError {
    match cache.finish_operation(operation, RealizationCacheDisposition::Rollback) {
        Ok(()) => original,
        Err(rollback) => rollback
            .with_context("original_code", original.code)
            .with_context("original_message", original.message),
    }
}

fn validate_input_counts(
    model: &(dyn CompletedModelAccess + '_),
    limits: RealizationLimits,
) -> NativeResult<()> {
    check_count(
        "max_named_individuals",
        usize_to_u64(model.named_individuals().len()),
        u64::from(limits.max_named_individuals),
    )?;
    let facts = [
        model.direct_type_facts().len(),
        model.object_target_facts().len(),
        model.data_target_facts().len(),
        model.different_from_facts().len(),
    ]
    .into_iter()
    .try_fold(0_u64, |total, count| {
        total
            .checked_add(usize_to_u64(count))
            .ok_or_else(|| NativeError::invariant("realization fact count overflow"))
    })?;
    check_count("max_facts", facts, limits.max_facts)
}

fn canonical_domain(values: &[u32], label: &str, allowed: u32) -> NativeResult<BTreeSet<u32>> {
    check_count(
        if label == "source-literal ID domain" {
            "max_source_literals"
        } else {
            "max_property_ids"
        },
        usize_to_u64(values.len()),
        u64::from(allowed),
    )?;
    let result = values.iter().copied().collect::<BTreeSet<_>>();
    if result.len() != values.len() {
        return Err(NativeError::invariant(format!(
            "completed realization {label} contains duplicate IDs"
        )));
    }
    Ok(result)
}

fn build_same_as(
    model: &(dyn CompletedModelAccess + '_),
    limits: RealizationLimits,
    control: &dyn OperationControl,
) -> NativeResult<SameAsBuild> {
    let mut by_key: BTreeMap<u64, Vec<u32>> = BTreeMap::new();
    let mut seen = BTreeSet::new();
    for (offset, record) in model.named_individuals().iter().enumerate() {
        poll_offset(offset, limits.poll_stride, control)?;
        if !seen.insert(record.individual_id) {
            return Err(NativeError::invariant(
                "completed realization contains a duplicate named-individual ID",
            ));
        }
        by_key
            .entry(record.equality_key)
            .or_default()
            .push(record.individual_id);
    }
    let mut groups = by_key.into_values().collect::<Vec<_>>();
    for group in &mut groups {
        group.sort_unstable();
    }
    groups.sort();
    let mut group_by_individual = BTreeMap::new();
    for (index, group) in groups.iter().enumerate() {
        let group_id = u32::try_from(index)
            .map_err(|_| NativeError::invariant("same-as group ID exceeds u32"))?;
        for individual in group {
            group_by_individual.insert(*individual, group_id);
        }
    }
    observe_working_memory(&groups, 0, 0, 0, limits, control)?;
    Ok((groups, group_by_individual))
}

fn public_group(
    individual: ModelIndividual,
    groups: &BTreeMap<u32, u32>,
    label: &str,
) -> NativeResult<Option<u32>> {
    match individual {
        ModelIndividual::Named(individual_id) => groups
            .get(&individual_id)
            .copied()
            .map(Some)
            .ok_or_else(|| {
                NativeError::invariant(format!(
                    "completed realization {label} references an absent named individual"
                ))
            }),
        ModelIndividual::Anonymous(_) | ModelIndividual::Internal(_) => Ok(None),
    }
}

fn scan_checkpoint(
    scanned: &mut u64,
    limits: RealizationLimits,
    control: &dyn OperationControl,
) -> NativeResult<()> {
    *scanned = checked_increment(*scanned, "realization fact counter")?;
    if *scanned % u64::from(limits.poll_stride) == 0 {
        control.poll()?;
    }
    Ok(())
}

fn poll_offset(offset: usize, stride: u32, control: &dyn OperationControl) -> NativeResult<()> {
    if usize_to_u64(offset) % u64::from(stride) == 0 {
        control.poll()?;
    }
    Ok(())
}

fn observe_working_memory(
    same_as: &[Vec<u32>],
    direct_rows: usize,
    property_rows: usize,
    facts_scanned: u64,
    limits: RealizationLimits,
    control: &dyn OperationControl,
) -> NativeResult<()> {
    let members = same_as.iter().fold(0_u64, |total, group| {
        total.saturating_add(usize_to_u64(group.len()))
    });
    let bytes = members
        .saturating_mul(usize_to_u64(size_of::<u32>() * 4))
        .saturating_add(
            usize_to_u64(same_as.len()).saturating_mul(usize_to_u64(size_of::<Vec<u32>>() * 4)),
        )
        .saturating_add(usize_to_u64(direct_rows.saturating_add(property_rows)).saturating_mul(128))
        .saturating_add(facts_scanned.saturating_mul(16));
    check_count("max_memory_bytes", bytes, limits.max_memory_bytes)?;
    control.observe_memory(bytes)?;
    control.poll()
}

fn result_counts(result: &RealizationIds) -> NativeResult<(u64, u64)> {
    let rows = usize_to_u64(result.same_as.len())
        .checked_add(usize_to_u64(result.direct_types.len()))
        .and_then(|value| value.checked_add(usize_to_u64(result.object_targets.len())))
        .and_then(|value| value.checked_add(usize_to_u64(result.data_targets.len())))
        .and_then(|value| value.checked_add(usize_to_u64(result.different_from.len())))
        .ok_or_else(|| NativeError::invariant("realization result row count overflow"))?;
    let values = result
        .same_as
        .iter()
        .map(Vec::len)
        .chain(result.direct_types.iter().map(|(_, values)| values.len()))
        .chain(
            result
                .object_targets
                .iter()
                .map(|(_, _, values)| values.len()),
        )
        .chain(
            result
                .data_targets
                .iter()
                .map(|(_, _, values)| values.len()),
        )
        .try_fold(0_u64, |total, count| {
            total
                .checked_add(usize_to_u64(count))
                .ok_or_else(|| NativeError::invariant("realization result value count overflow"))
        })?
        .checked_add(usize_to_u64(result.different_from.len()).saturating_mul(2))
        .ok_or_else(|| NativeError::invariant("realization result value count overflow"))?;
    Ok((rows, values))
}

fn estimate_result_memory(result: &RealizationIds) -> u64 {
    let (_, values) = result_counts(result).unwrap_or((u64::MAX, u64::MAX));
    let rows = usize_to_u64(result.same_as.len())
        .saturating_add(usize_to_u64(result.direct_types.len()))
        .saturating_add(usize_to_u64(result.object_targets.len()))
        .saturating_add(usize_to_u64(result.data_targets.len()))
        .saturating_add(usize_to_u64(result.different_from.len()));
    usize_to_u64(size_of::<RealizationIds>())
        .saturating_add(rows.saturating_mul(usize_to_u64(size_of::<Vec<u32>>() + 16)))
        .saturating_add(values.saturating_mul(usize_to_u64(size_of::<u32>())))
}

fn checked_increment(value: u64, label: &str) -> NativeResult<u64> {
    value
        .checked_add(1)
        .ok_or_else(|| NativeError::invariant(format!("{label} overflow")))
}

fn usize_to_u64(value: usize) -> u64 {
    u64::try_from(value).unwrap_or(u64::MAX)
}

fn check_count(limit: &'static str, observed: u64, allowed: u64) -> NativeResult<()> {
    if observed > allowed {
        return Err(resource_error(limit, observed, allowed));
    }
    Ok(())
}

fn resource_error(limit: &'static str, observed: u64, allowed: u64) -> NativeError {
    NativeError::new(
        ErrorKind::Resource,
        "RESOURCE_LIMIT",
        format!("native realization resource limit exceeded: {limit}"),
    )
    .with_context("limit", limit)
    .with_context("observed", observed.to_string())
    .with_context("allowed", allowed.to_string())
}
