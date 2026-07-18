use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

use crate::error::{ErrorKind, NativeError, NativeResult};
use crate::result_wire::{encode_realization, encode_realization_ids, RealizationWireResult};
use crate::session::{NeverAbort, OperationControl};

use super::{
    build_realization_ids, realize_cached, CompletedModelAccess, DataTargetFact, DifferentFromFact,
    DirectTypeFact, ModelIndividual, NamedIndividualRecord, ObjectTargetFact, RealizationCache,
    RealizationCacheDisposition, RealizationCacheKey, RealizationLimits,
};

#[derive(Clone, Debug)]
struct Fixture {
    key: RealizationCacheKey,
    named: Vec<NamedIndividualRecord>,
    class_node_count: u32,
    object_properties: Vec<u32>,
    data_properties: Vec<u32>,
    literals: Vec<u32>,
    direct: Vec<DirectTypeFact>,
    objects: Vec<ObjectTargetFact>,
    data: Vec<DataTargetFact>,
    different: Vec<DifferentFromFact>,
}

impl CompletedModelAccess for Fixture {
    fn cache_key(&self) -> RealizationCacheKey {
        self.key
    }

    fn named_individuals(&self) -> &[NamedIndividualRecord] {
        &self.named
    }

    fn class_node_count(&self) -> u32 {
        self.class_node_count
    }

    fn object_property_ids(&self) -> &[u32] {
        &self.object_properties
    }

    fn data_property_ids(&self) -> &[u32] {
        &self.data_properties
    }

    fn source_literal_ids(&self) -> &[u32] {
        &self.literals
    }

    fn direct_type_facts(&self) -> &[DirectTypeFact] {
        &self.direct
    }

    fn object_target_facts(&self) -> &[ObjectTargetFact] {
        &self.objects
    }

    fn data_target_facts(&self) -> &[DataTargetFact] {
        &self.data
    }

    fn different_from_facts(&self) -> &[DifferentFromFact] {
        &self.different
    }
}

fn fixture() -> Fixture {
    Fixture {
        key: RealizationCacheKey::new([7; 32], 11),
        named: vec![
            NamedIndividualRecord {
                individual_id: 9,
                equality_key: 20,
            },
            NamedIndividualRecord {
                individual_id: 5,
                equality_key: 10,
            },
            NamedIndividualRecord {
                individual_id: 7,
                equality_key: 30,
            },
            NamedIndividualRecord {
                individual_id: 1,
                equality_key: 10,
            },
        ],
        class_node_count: 8,
        object_properties: vec![44, 42],
        data_properties: vec![50],
        literals: vec![101, 100],
        direct: vec![
            DirectTypeFact {
                subject: ModelIndividual::Named(5),
                class_node_id: 4,
            },
            DirectTypeFact {
                subject: ModelIndividual::Internal(600),
                class_node_id: 2,
            },
            DirectTypeFact {
                subject: ModelIndividual::Named(1),
                class_node_id: 3,
            },
            DirectTypeFact {
                subject: ModelIndividual::Named(5),
                class_node_id: 3,
            },
            DirectTypeFact {
                subject: ModelIndividual::Named(9),
                class_node_id: 6,
            },
        ],
        objects: vec![
            ObjectTargetFact {
                subject: ModelIndividual::Named(5),
                property_id: 42,
                target: ModelIndividual::Named(9),
            },
            ObjectTargetFact {
                subject: ModelIndividual::Named(1),
                property_id: 42,
                target: ModelIndividual::Named(7),
            },
            ObjectTargetFact {
                subject: ModelIndividual::Named(5),
                property_id: 42,
                target: ModelIndividual::Named(9),
            },
            ObjectTargetFact {
                subject: ModelIndividual::Anonymous(700),
                property_id: 42,
                target: ModelIndividual::Named(9),
            },
            ObjectTargetFact {
                subject: ModelIndividual::Named(7),
                property_id: 44,
                target: ModelIndividual::Internal(701),
            },
        ],
        data: vec![
            DataTargetFact {
                subject: ModelIndividual::Named(5),
                property_id: 50,
                source_literal_id: 101,
            },
            DataTargetFact {
                subject: ModelIndividual::Named(1),
                property_id: 50,
                source_literal_id: 100,
            },
            DataTargetFact {
                subject: ModelIndividual::Named(5),
                property_id: 50,
                source_literal_id: 101,
            },
            DataTargetFact {
                subject: ModelIndividual::Internal(702),
                property_id: 50,
                source_literal_id: 100,
            },
        ],
        different: vec![
            DifferentFromFact {
                left: ModelIndividual::Named(9),
                right: ModelIndividual::Named(5),
            },
            DifferentFromFact {
                left: ModelIndividual::Named(1),
                right: ModelIndividual::Named(9),
            },
            DifferentFromFact {
                left: ModelIndividual::Anonymous(703),
                right: ModelIndividual::Named(7),
            },
        ],
    }
}

#[test]
fn canonical_builder_groups_equality_and_excludes_non_named_witnesses() -> NativeResult<()> {
    let result = build_realization_ids(&fixture(), RealizationLimits::default(), &NeverAbort)?;
    assert_eq!(result.ids().same_as(), &[vec![1, 5], vec![7], vec![9]]);
    assert_eq!(
        result.ids().direct_types(),
        &[(0, vec![3, 4]), (2, vec![6])]
    );
    // Target values are canonical same-as group IDs, never individual symbol IDs.
    assert_eq!(result.ids().object_targets(), &[(0, 42, vec![1, 2])]);
    assert_eq!(result.ids().data_targets(), &[(0, 50, vec![100, 101])]);
    assert_eq!(result.ids().different_from(), &[(0, 2)]);
    assert_eq!(result.statistics().named_individuals, 4);
    assert_eq!(result.statistics().same_as_groups, 3);
    assert_eq!(result.statistics().excluded_non_named_facts, 5);
    assert!(!result.statistics().cache_hit);
    Ok(())
}

#[test]
fn conversion_to_result_wire_is_exact_and_consuming_path_is_zero_copy() -> NativeResult<()> {
    let result = build_realization_ids(&fixture(), RealizationLimits::default(), &NeverAbort)?;
    let direct_encoding = encode_realization_ids(result.ids().as_ref())?;
    let cloned_wire = result.to_wire_result();
    assert_eq!(cloned_wire.object_targets, vec![(0, 42, vec![1, 2])]);
    assert_eq!(encode_realization(&cloned_wire)?, direct_encoding);

    let owned = Arc::try_unwrap(result.into_ids())
        .map_err(|_| NativeError::invariant("test realization unexpectedly remained shared"))?;
    let group_pointer = owned.same_as()[0].as_ptr();
    let wire: RealizationWireResult = owned.into_wire_result();
    assert_eq!(group_pointer, wire.same_as[0].as_ptr());
    assert!(!encode_realization(&wire)?.is_empty());
    Ok(())
}

#[test]
fn relation_and_domain_corruption_fail_closed() -> NativeResult<()> {
    let mut duplicate_name = fixture();
    duplicate_name.named.push(duplicate_name.named[0]);
    assert_eq!(build_error(&duplicate_name)?.kind, ErrorKind::Invariant);

    let mut unknown_name = fixture();
    unknown_name.direct.push(DirectTypeFact {
        subject: ModelIndividual::Named(99),
        class_node_id: 1,
    });
    assert_eq!(build_error(&unknown_name)?.kind, ErrorKind::Invariant);

    let mut absent_node = fixture();
    absent_node.direct[0].class_node_id = absent_node.class_node_count;
    assert_eq!(build_error(&absent_node)?.kind, ErrorKind::Invariant);

    let mut absent_property = fixture();
    absent_property.objects[0].property_id = 999;
    assert_eq!(build_error(&absent_property)?.kind, ErrorKind::Invariant);

    let mut absent_literal = fixture();
    absent_literal.data[0].source_literal_id = 999;
    assert_eq!(build_error(&absent_literal)?.kind, ErrorKind::Invariant);

    let mut contradiction = fixture();
    contradiction.different.push(DifferentFromFact {
        left: ModelIndividual::Named(1),
        right: ModelIndividual::Named(5),
    });
    assert_eq!(build_error(&contradiction)?.kind, ErrorKind::Invariant);

    let mut duplicate_domain = fixture();
    duplicate_domain.object_properties.push(42);
    assert_eq!(build_error(&duplicate_domain)?.kind, ErrorKind::Invariant);
    Ok(())
}

#[test]
fn every_input_permutation_has_identical_canonical_output() -> NativeResult<()> {
    let original = fixture();
    let expected = build_realization_ids(&original, RealizationLimits::default(), &NeverAbort)?;
    let mut permuted = original;
    permuted.named.reverse();
    permuted.object_properties.reverse();
    permuted.data_properties.reverse();
    permuted.literals.reverse();
    permuted.direct.reverse();
    permuted.objects.reverse();
    permuted.data.reverse();
    permuted.different.reverse();
    let actual = build_realization_ids(&permuted, RealizationLimits::default(), &NeverAbort)?;
    assert_eq!(actual.ids(), expected.ids());
    assert_eq!(actual.statistics(), expected.statistics());
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
                "realization interrupted by test control",
            ));
        }
        Ok(())
    }

    fn observe_memory(&self, _bytes: u64) -> NativeResult<()> {
        self.poll()
    }
}

#[test]
fn cancellation_and_component_limits_return_no_result() -> NativeResult<()> {
    let control = BoundedControl {
        polls: AtomicU64::new(0),
        allowed: 2,
    };
    let cancelled = build_realization_ids(
        &fixture(),
        RealizationLimits {
            poll_stride: 1,
            ..RealizationLimits::default()
        },
        &control,
    );
    let Err(error) = cancelled else {
        return Err(NativeError::invariant(
            "bounded realization unexpectedly completed",
        ));
    };
    assert_eq!(error.kind, ErrorKind::Cancelled);

    let limited = build_realization_ids(
        &fixture(),
        RealizationLimits {
            max_facts: 1,
            ..RealizationLimits::default()
        },
        &NeverAbort,
    );
    let Err(resource) = limited else {
        return Err(NativeError::invariant(
            "fact-bounded realization unexpectedly completed",
        ));
    };
    assert_eq!(resource.kind, ErrorKind::Resource);
    assert_eq!(
        resource.context.get("limit").map(String::as_str),
        Some("max_facts")
    );
    Ok(())
}

#[test]
fn cache_promotes_atomically_hits_by_key_and_rolls_back_replacements() -> NativeResult<()> {
    let original = fixture();
    let mut cache = RealizationCache::new();
    let first = realize_cached(
        &original,
        &mut cache,
        RealizationLimits::default(),
        &NeverAbort,
    )?;
    let hit = realize_cached(
        &original,
        &mut cache,
        RealizationLimits::default(),
        &NeverAbort,
    )?;
    assert!(hit.statistics().cache_hit);
    assert!(Arc::ptr_eq(first.ids(), hit.ids()));

    let mut replacement = original.clone();
    replacement.key = RealizationCacheKey::new([8; 32], 12);
    let replacement_result =
        build_realization_ids(&replacement, RealizationLimits::default(), &NeverAbort)?;
    let operation = cache.begin_operation(replacement.key)?;
    cache.stage(operation, replacement_result)?;
    assert!(cache.lookup(replacement.key).is_none());
    assert!(cache.lookup(original.key).is_some());
    cache.finish_operation(operation, RealizationCacheDisposition::Rollback)?;
    assert!(cache.lookup(replacement.key).is_none());
    assert!(cache.lookup(original.key).is_some());
    Ok(())
}

#[test]
fn failed_rebuild_and_foreign_tokens_cannot_damage_committed_cache() -> NativeResult<()> {
    let original = fixture();
    let mut cache = RealizationCache::new();
    realize_cached(
        &original,
        &mut cache,
        RealizationLimits::default(),
        &NeverAbort,
    )?;

    let mut broken = original.clone();
    broken.key = RealizationCacheKey::new([9; 32], 13);
    broken.data[0].source_literal_id = 99_999;
    let failed = realize_cached(
        &broken,
        &mut cache,
        RealizationLimits::default(),
        &NeverAbort,
    );
    let Err(error) = failed else {
        return Err(NativeError::invariant(
            "malformed cache replacement unexpectedly completed",
        ));
    };
    assert_eq!(error.kind, ErrorKind::Invariant);
    assert!(cache.lookup(original.key).is_some());
    assert!(cache.lookup(broken.key).is_none());

    let operation = cache.begin_operation(broken.key)?;
    let mut foreign = RealizationCache::new();
    let result = build_realization_ids(&original, RealizationLimits::default(), &NeverAbort)?;
    let foreign_stage = foreign.stage(operation, result);
    let Err(foreign_error) = foreign_stage else {
        return Err(NativeError::invariant(
            "foreign cache operation unexpectedly staged a result",
        ));
    };
    assert_eq!(foreign_error.kind, ErrorKind::Invariant);
    cache.finish_operation(operation, RealizationCacheDisposition::Rollback)?;
    assert!(cache.lookup(original.key).is_some());
    Ok(())
}

#[test]
fn cancelled_rebuild_preserves_previous_committed_entry() -> NativeResult<()> {
    let original = fixture();
    let mut cache = RealizationCache::new();
    realize_cached(
        &original,
        &mut cache,
        RealizationLimits::default(),
        &NeverAbort,
    )?;
    let mut replacement = original.clone();
    replacement.key = RealizationCacheKey::new([10; 32], 14);
    let control = BoundedControl {
        polls: AtomicU64::new(0),
        allowed: 3,
    };
    let cancelled = realize_cached(
        &replacement,
        &mut cache,
        RealizationLimits {
            poll_stride: 1,
            ..RealizationLimits::default()
        },
        &control,
    );
    let Err(error) = cancelled else {
        return Err(NativeError::invariant(
            "cancelled cache replacement unexpectedly completed",
        ));
    };
    assert_eq!(error.kind, ErrorKind::Cancelled);
    assert!(cache.lookup(original.key).is_some());
    assert!(cache.lookup(replacement.key).is_none());
    Ok(())
}

#[test]
fn large_abox_construction_is_linear_in_exposed_facts() -> NativeResult<()> {
    const COUNT: u32 = 40_000;
    let named = (0..COUNT)
        .map(|individual_id| NamedIndividualRecord {
            individual_id,
            equality_key: u64::from(individual_id),
        })
        .collect::<Vec<_>>();
    let direct = (0..COUNT)
        .map(|individual_id| DirectTypeFact {
            subject: ModelIndividual::Named(individual_id),
            class_node_id: 1,
        })
        .collect::<Vec<_>>();
    let objects = (0..COUNT - 1)
        .map(|individual_id| ObjectTargetFact {
            subject: ModelIndividual::Named(individual_id),
            property_id: 7,
            target: ModelIndividual::Named(individual_id + 1),
        })
        .collect::<Vec<_>>();
    let model = Fixture {
        key: RealizationCacheKey::new([11; 32], 1),
        named,
        class_node_count: 2,
        object_properties: vec![7],
        data_properties: Vec::new(),
        literals: Vec::new(),
        direct,
        objects,
        data: Vec::new(),
        different: Vec::new(),
    };
    let result = build_realization_ids(&model, RealizationLimits::default(), &NeverAbort)?;
    let count = usize::try_from(COUNT)
        .map_err(|_| NativeError::invariant("large-ABox count cannot fit usize"))?;
    let edge_count = usize::try_from(COUNT - 1)
        .map_err(|_| NativeError::invariant("large-ABox edge count cannot fit usize"))?;
    assert_eq!(result.ids().same_as().len(), count);
    assert_eq!(result.ids().direct_types().len(), count);
    assert_eq!(result.ids().object_targets().len(), edge_count);
    assert_eq!(
        result.statistics().facts_scanned,
        u64::from(COUNT) + u64::from(COUNT - 1)
    );
    Ok(())
}

fn build_error(model: &Fixture) -> NativeResult<NativeError> {
    match build_realization_ids(model, RealizationLimits::default(), &NeverAbort) {
        Err(error) => Ok(error),
        Ok(_) => Err(NativeError::invariant(
            "malformed completed model unexpectedly produced a result",
        )),
    }
}
