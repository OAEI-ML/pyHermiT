use std::collections::BTreeSet;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

use crate::error::{ErrorKind, NativeError, NativeResult};
use crate::session::{NeverAbort, OperationControl};

use super::{
    classify_cached, ClassificationCache, ClassificationCacheDisposition, ClassificationCacheKey,
    ClassificationDomain, ClassificationLimits, ClassificationMode, ClassificationProblem,
};

fn key(revision: u64, domain: ClassificationDomain) -> ClassificationCacheKey {
    ClassificationCacheKey::new([7; 32], revision, domain)
}

fn elements() -> [u32; 6] {
    [0, 1, 2, 3, 4, 5]
}

fn true_relations() -> BTreeSet<(u32, u32)> {
    let values = elements();
    let mut relations = values
        .iter()
        .flat_map(|value| [(0, *value), (*value, 5), (*value, *value)])
        .collect::<BTreeSet<_>>();
    relations.extend([(1, 2), (2, 1), (1, 3), (2, 3), (3, 4), (1, 4), (2, 4)]);
    relations
}

fn problem(values: &[u32]) -> ClassificationProblem<'_> {
    ClassificationProblem {
        elements: values,
        top: 5,
        bottom: 0,
        known: &[],
        known_complete: false,
        mode: ClassificationMode::QuasiOrder,
        limits: ClassificationLimits::default(),
    }
}

#[test]
fn committed_hit_reuses_the_exact_hierarchy_allocation() -> NativeResult<()> {
    let mut cache = ClassificationCache::new();
    let values = elements();
    let entailed = true_relations();
    let calls = AtomicU64::new(0);
    let first = classify_cached(
        key(1, ClassificationDomain::Classes),
        problem(&values),
        &mut cache,
        &NeverAbort,
        |queries, _control| {
            calls.fetch_add(1, Ordering::Relaxed);
            Ok(queries
                .iter()
                .map(|query| entailed.contains(query))
                .collect())
        },
    )?;
    let calls_after_build = calls.load(Ordering::Relaxed);
    let second = classify_cached(
        key(1, ClassificationDomain::Classes),
        problem(&values),
        &mut cache,
        &NeverAbort,
        |_queries, _control| {
            calls.fetch_add(1, Ordering::Relaxed);
            Err(NativeError::invariant(
                "cache hit invoked the semantic tester",
            ))
        },
    )?;

    assert!(!first.cache_hit);
    assert!(second.cache_hit);
    assert!(Arc::ptr_eq(&first.hierarchy, &second.hierarchy));
    assert_eq!(calls.load(Ordering::Relaxed), calls_after_build);
    assert_eq!(
        second.statistics.cache_hits,
        first.statistics.cache_hits + 1
    );
    Ok(())
}

#[derive(Debug)]
struct BoundedControl {
    polls: AtomicU64,
    allowed: u64,
}

impl OperationControl for BoundedControl {
    fn poll(&self) -> NativeResult<()> {
        let observed = self.polls.fetch_add(1, Ordering::Relaxed) + 1;
        if observed > self.allowed {
            return Err(NativeError::new(
                ErrorKind::Cancelled,
                "REASONER_INTERRUPTED",
                "classification cache test interrupted",
            ));
        }
        Ok(())
    }

    fn observe_memory(&self, _bytes: u64) -> NativeResult<()> {
        self.poll()
    }
}

#[test]
fn failed_replacement_preserves_the_previous_revision() -> NativeResult<()> {
    let mut cache = ClassificationCache::new();
    let values = elements();
    let entailed = true_relations();
    let old_key = key(1, ClassificationDomain::Classes);
    classify_cached(
        old_key,
        problem(&values),
        &mut cache,
        &NeverAbort,
        |queries, _control| {
            Ok(queries
                .iter()
                .map(|query| entailed.contains(query))
                .collect())
        },
    )?;
    let retained = cache
        .lookup(old_key)
        .ok_or_else(|| NativeError::invariant("committed taxonomy is absent"))?;
    let cancelled = classify_cached(
        key(2, ClassificationDomain::Classes),
        problem(&values),
        &mut cache,
        &BoundedControl {
            polls: AtomicU64::new(0),
            allowed: 2,
        },
        |queries, _control| Ok(vec![false; queries.len()]),
    );
    assert_eq!(
        cancelled.err().map(|error| error.kind),
        Some(ErrorKind::Cancelled)
    );
    let after = cache
        .lookup(old_key)
        .ok_or_else(|| NativeError::invariant("failed rebuild removed prior taxonomy"))?;
    assert!(Arc::ptr_eq(&retained, &after));
    Ok(())
}

#[test]
fn owner_tokens_domains_and_invalidation_fail_closed() -> NativeResult<()> {
    let class_key = key(3, ClassificationDomain::Classes);
    let object_key = key(3, ClassificationDomain::ObjectProperties);
    let mut first = ClassificationCache::new();
    let mut second = ClassificationCache::new();
    let token = first.begin_operation(class_key)?;
    let foreign = second.begin_operation(object_key)?;
    assert!(first
        .finish_operation(foreign, ClassificationCacheDisposition::Rollback)
        .is_err());
    assert!(first.invalidate().is_err());
    first.finish_operation(token, ClassificationCacheDisposition::Rollback)?;
    assert!(first
        .finish_operation(token, ClassificationCacheDisposition::Rollback)
        .is_err());
    second.finish_operation(foreign, ClassificationCacheDisposition::Rollback)?;
    first.invalidate()?;
    Ok(())
}
