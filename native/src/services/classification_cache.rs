//! Operation-local publication and zero-copy retention for native taxonomies.
// SPDX-License-Identifier: LGPL-3.0-or-later

use std::collections::BTreeMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

use crate::error::{ErrorKind, NativeError, NativeResult};
use crate::session::OperationControl;

use super::{
    classify_ids, ClassificationProblem, ClassificationResult, ClassificationStatistics,
    HierarchyIds,
};

/// Separate compiled-ID domains that may have independent committed taxonomies.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ClassificationDomain {
    Classes,
    ObjectProperties,
    DataProperties,
}

/// Identity of the permanent semantics used to compute one taxonomy.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ClassificationCacheKey {
    pub ontology_fingerprint: [u8; 32],
    pub model_revision: u64,
    pub domain: ClassificationDomain,
}

impl ClassificationCacheKey {
    #[must_use]
    pub const fn new(
        ontology_fingerprint: [u8; 32],
        model_revision: u64,
        domain: ClassificationDomain,
    ) -> Self {
        Self {
            ontology_fingerprint,
            model_revision,
            domain,
        }
    }
}

/// A taxonomy answer whose large immutable graph is shared with the committed cache.
#[derive(Clone, Debug)]
pub struct CachedClassificationResult {
    pub hierarchy: Arc<HierarchyIds>,
    pub statistics: ClassificationStatistics,
    pub cache_hit: bool,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ClassificationCacheDisposition {
    Promote,
    Rollback,
}

/// Owner-stamped token preventing foreign or stale publication.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ClassificationCacheOperation {
    owner: u64,
    sequence: u64,
}

#[derive(Clone, Debug)]
struct CacheEntry {
    key: ClassificationCacheKey,
    hierarchy: Arc<HierarchyIds>,
    statistics: ClassificationStatistics,
    estimated_bytes: u64,
}

#[derive(Clone, Debug)]
struct ActiveOperation {
    token: ClassificationCacheOperation,
    key: ClassificationCacheKey,
    staged: Option<CacheEntry>,
}

static NEXT_CACHE_OWNER: AtomicU64 = AtomicU64::new(1);

/// Bounded-by-domain permanent taxonomy cache with operation-local staging.
#[derive(Debug)]
pub struct ClassificationCache {
    owner: u64,
    next_sequence: u64,
    committed: BTreeMap<ClassificationDomain, CacheEntry>,
    active: Option<ActiveOperation>,
}

impl Default for ClassificationCache {
    fn default() -> Self {
        Self::new()
    }
}

impl ClassificationCache {
    #[must_use]
    pub fn new() -> Self {
        Self {
            owner: NEXT_CACHE_OWNER.fetch_add(1, Ordering::Relaxed),
            next_sequence: 1,
            committed: BTreeMap::new(),
            active: None,
        }
    }

    #[must_use]
    pub fn lookup(&self, key: ClassificationCacheKey) -> Option<Arc<HierarchyIds>> {
        self.entry(key).map(|entry| Arc::clone(&entry.hierarchy))
    }

    pub fn begin_operation(
        &mut self,
        key: ClassificationCacheKey,
    ) -> NativeResult<ClassificationCacheOperation> {
        if self.active.is_some() {
            return Err(NativeError::new(
                ErrorKind::Busy,
                "CONCURRENT_MUTATION",
                "a classification cache operation is already active",
            ));
        }
        let sequence = self.next_sequence;
        self.next_sequence = sequence
            .checked_add(1)
            .ok_or_else(|| NativeError::invariant("classification cache sequence overflow"))?;
        let token = ClassificationCacheOperation {
            owner: self.owner,
            sequence,
        };
        self.active = Some(ActiveOperation {
            token,
            key,
            staged: None,
        });
        Ok(token)
    }

    pub fn stage(
        &mut self,
        token: ClassificationCacheOperation,
        result: ClassificationResult,
    ) -> NativeResult<Arc<HierarchyIds>> {
        let active = self.require_active_mut(token)?;
        if active.staged.is_some() {
            return Err(NativeError::invariant(
                "classification cache operation already has a staged result",
            ));
        }
        let estimated_bytes = estimate_hierarchy_bytes(&result.hierarchy)?;
        let hierarchy = Arc::new(result.hierarchy);
        active.staged = Some(CacheEntry {
            key: active.key,
            hierarchy: Arc::clone(&hierarchy),
            statistics: result.statistics,
            estimated_bytes,
        });
        Ok(hierarchy)
    }

    pub fn finish_operation(
        &mut self,
        token: ClassificationCacheOperation,
        disposition: ClassificationCacheDisposition,
    ) -> NativeResult<()> {
        let active = self.require_active(token)?;
        if disposition == ClassificationCacheDisposition::Promote && active.staged.is_none() {
            return Err(NativeError::invariant(
                "cannot promote a classification cache operation without a complete result",
            ));
        }
        let mut active = self
            .active
            .take()
            .ok_or_else(|| NativeError::invariant("classification cache operation disappeared"))?;
        if disposition == ClassificationCacheDisposition::Promote {
            let entry = active.staged.take().ok_or_else(|| {
                NativeError::invariant("validated classification result disappeared")
            })?;
            self.committed.insert(entry.key.domain, entry);
        }
        Ok(())
    }

    pub fn invalidate(&mut self) -> NativeResult<()> {
        if self.active.is_some() {
            return Err(NativeError::new(
                ErrorKind::Busy,
                "CONCURRENT_MUTATION",
                "cannot invalidate classification caches during an active operation",
            ));
        }
        self.committed.clear();
        Ok(())
    }

    fn entry(&self, key: ClassificationCacheKey) -> Option<&CacheEntry> {
        self.committed
            .get(&key.domain)
            .filter(|entry| entry.key == key)
    }

    fn cached_result(&self, key: ClassificationCacheKey) -> Option<CachedClassificationResult> {
        self.entry(key).map(|entry| CachedClassificationResult {
            hierarchy: Arc::clone(&entry.hierarchy),
            statistics: ClassificationStatistics {
                cache_hits: entry.statistics.cache_hits.saturating_add(1),
                ..entry.statistics
            },
            cache_hit: true,
        })
    }

    fn require_active(
        &self,
        token: ClassificationCacheOperation,
    ) -> NativeResult<&ActiveOperation> {
        if token.owner != self.owner {
            return Err(NativeError::invariant(
                "classification cache operation belongs to another cache",
            ));
        }
        self.active
            .as_ref()
            .filter(|active| active.token == token)
            .ok_or_else(|| NativeError::invariant("classification cache operation token is stale"))
    }

    fn require_active_mut(
        &mut self,
        token: ClassificationCacheOperation,
    ) -> NativeResult<&mut ActiveOperation> {
        if token.owner != self.owner {
            return Err(NativeError::invariant(
                "classification cache operation belongs to another cache",
            ));
        }
        self.active
            .as_mut()
            .filter(|active| active.token == token)
            .ok_or_else(|| NativeError::invariant("classification cache operation token is stale"))
    }
}

/// Return a committed taxonomy or build and atomically promote a complete replacement.
pub fn classify_cached<F>(
    key: ClassificationCacheKey,
    problem: ClassificationProblem<'_>,
    cache: &mut ClassificationCache,
    control: &dyn OperationControl,
    tester: F,
) -> NativeResult<CachedClassificationResult>
where
    F: FnMut(&[(u32, u32)], &dyn OperationControl) -> NativeResult<Vec<bool>>,
{
    control.poll()?;
    if let Some(result) = cache.cached_result(key) {
        let bytes = cache.entry(key).map_or(0, |entry| entry.estimated_bytes);
        control.observe_memory(bytes)?;
        control.poll()?;
        return Ok(result);
    }

    let operation = cache.begin_operation(key)?;
    let result = match classify_ids(problem, control, tester) {
        Ok(value) => value,
        Err(error) => return Err(rollback_after_error(cache, operation, error)),
    };
    if let Err(error) = control.poll() {
        return Err(rollback_after_error(cache, operation, error));
    }
    let statistics = result.statistics;
    let hierarchy = match cache.stage(operation, result) {
        Ok(value) => value,
        Err(error) => return Err(rollback_after_error(cache, operation, error)),
    };
    cache.finish_operation(operation, ClassificationCacheDisposition::Promote)?;
    Ok(CachedClassificationResult {
        hierarchy,
        statistics,
        cache_hit: false,
    })
}

fn rollback_after_error(
    cache: &mut ClassificationCache,
    operation: ClassificationCacheOperation,
    original: NativeError,
) -> NativeError {
    match cache.finish_operation(operation, ClassificationCacheDisposition::Rollback) {
        Ok(()) => original,
        Err(rollback) => rollback
            .with_context("original_code", original.code)
            .with_context("original_message", original.message),
    }
}

fn estimate_hierarchy_bytes(hierarchy: &HierarchyIds) -> NativeResult<u64> {
    let node_values = hierarchy.nodes.iter().try_fold(0_u64, |total, node| {
        total
            .checked_add(u64::try_from(node.len()).unwrap_or(u64::MAX))
            .ok_or_else(|| NativeError::invariant("hierarchy value count overflow"))
    })?;
    let nodes = u64::try_from(hierarchy.nodes.len()).unwrap_or(u64::MAX);
    let edges = u64::try_from(hierarchy.edges.len()).unwrap_or(u64::MAX);
    node_values
        .checked_mul(4)
        .and_then(|value| value.checked_add(nodes.saturating_mul(32)))
        .and_then(|value| value.checked_add(edges.saturating_mul(8)))
        .ok_or_else(|| NativeError::invariant("hierarchy cache byte estimate overflow"))
}
