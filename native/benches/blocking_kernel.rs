// SPDX-License-Identifier: LGPL-3.0-or-later

#![allow(clippy::similar_names, clippy::too_many_lines)]

use std::collections::{BTreeMap, BTreeSet};
use std::time::Duration;

use _native::blocking::{
    select_blocking_plan, AssignmentChange, BlockValidator, BlockingAssignment,
    BlockingCacheNamespace, BlockingControl, BlockingError, BlockingLimits, BlockingManager,
    BlockingMode, BlockingProjection, BlockingRequirements, BlockingSignature,
    BlockingSignatureCache, BlockingStateMutate, BlockingStateRead, BlockingVocabulary,
    CachePromotionContext, DirectChecker, DirectCheckerKind, FactRecord, NeverCancel, NodeKey,
    NodeKind, NodeLifecycle, NodeRecord, ValidationDecision,
};
use criterion::{black_box, criterion_group, criterion_main, BatchSize, Criterion, Throughput};

const ROLE_FROM_PARENT_BASE: u32 = 10_000;
const ROLE_TO_PARENT_BASE: u32 = 10_004;
const ROLE_CYCLE: u32 = 10_008;
const CACHE_BYTES: usize = 8 * 1024 * 1024;

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct FakeState {
    revision: u64,
    nodes: Vec<NodeRecord<u32>>,
    facts: Vec<FactRecord<u32>>,
    assignments: BTreeMap<u32, BlockingAssignment<u32>>,
    promoted: BTreeSet<u32>,
    rescheduled: BTreeSet<u32>,
}

impl FakeState {
    fn create(&mut self, kind: NodeKind, parent: Option<u32>) -> Result<u32, BlockingError> {
        let node = u32::try_from(self.nodes.len()).map_err(|_error| {
            BlockingError::resource(
                "too many fake nodes",
                "nodes",
                u64::MAX,
                u64::from(u32::MAX),
            )
        })?;
        self.nodes.push(NodeRecord {
            node,
            key: NodeKey::new(node, 1),
            creation_id: node,
            kind,
            lifecycle: NodeLifecycle::Active,
            parent,
            has_pending_existentials: false,
        });
        self.revision = self.revision.saturating_add(1);
        Ok(node)
    }

    fn add_fact(
        &mut self,
        predicate_id: u32,
        arguments: Vec<u32>,
        core: bool,
    ) -> Result<u32, BlockingError> {
        let row_id = u32::try_from(self.facts.len()).map_err(|_error| {
            BlockingError::resource(
                "too many fake facts",
                "facts",
                u64::MAX,
                u64::from(u32::MAX),
            )
        })?;
        self.facts.push(FactRecord {
            row_id,
            predicate_id,
            arguments,
            core,
            active: true,
        });
        self.revision = self.revision.saturating_add(1);
        Ok(row_id)
    }

    fn set_pending(&mut self, node: u32) -> Result<(), BlockingError> {
        let record = self
            .nodes
            .iter_mut()
            .find(|record| record.node == node)
            .ok_or_else(|| BlockingError::invalid("fake pending node is unavailable"))?;
        record.has_pending_existentials = true;
        self.revision = self.revision.saturating_add(1);
        Ok(())
    }

    fn fact(&self, row_id: u32) -> Result<&FactRecord<u32>, BlockingError> {
        self.facts
            .iter()
            .find(|fact| fact.row_id == row_id)
            .ok_or_else(|| BlockingError::invalid("fake fact row is unavailable"))
    }
}

impl BlockingStateRead for FakeState {
    type Node = u32;

    fn revision(&self) -> u64 {
        self.revision
    }

    fn node_records(&self) -> Result<Vec<NodeRecord<Self::Node>>, BlockingError> {
        Ok(self.nodes.clone())
    }

    fn active_fact_records(&self) -> Result<Vec<FactRecord<Self::Node>>, BlockingError> {
        Ok(self.facts.clone())
    }
}

impl BlockingStateMutate for FakeState {
    fn blocking_atomic<T, F>(&mut self, operation: F) -> Result<T, BlockingError>
    where
        F: FnOnce(&mut Self) -> Result<T, BlockingError>,
    {
        let before = self.clone();
        let outcome = operation(self);
        if outcome.is_err() {
            *self = before;
        }
        outcome
    }

    fn apply_assignment_change(
        &mut self,
        change: &AssignmentChange<Self::Node>,
    ) -> Result<(), BlockingError> {
        match change.after {
            Some(assignment) => {
                self.assignments.insert(change.node, assignment);
            }
            None => {
                self.assignments.remove(&change.node);
            }
        }
        Ok(())
    }

    fn promote_core_fact(&mut self, row_id: u32) -> Result<(), BlockingError> {
        let fact = self
            .facts
            .iter_mut()
            .find(|fact| fact.row_id == row_id && fact.active)
            .ok_or_else(|| BlockingError::invalid("fake core fact is unavailable"))?;
        if !fact.core {
            fact.core = true;
            self.revision = self.revision.saturating_add(1);
        }
        self.promoted.insert(row_id);
        Ok(())
    }

    fn reschedule_existentials(&mut self, node: Self::Node) -> Result<(), BlockingError> {
        self.rescheduled.insert(node);
        Ok(())
    }
}

#[derive(Clone, Debug)]
struct BlockingFixture {
    state: FakeState,
    vocabulary: BlockingVocabulary,
    eligible_nodes: Vec<u32>,
}

#[derive(Clone, Debug)]
struct ValidatedFixture {
    state: FakeState,
    vocabulary: BlockingVocabulary,
    rejected_node: u32,
    promote_row: u32,
}

#[derive(Clone, Copy, Debug, Default)]
struct AcceptValidator;

impl BlockValidator<FakeState> for AcceptValidator {
    fn validate_block<C: BlockingControl>(
        &mut self,
        _state: &FakeState,
        _projection: &BlockingProjection<u32>,
        _blocked: u32,
        _blocker: u32,
        _signature: &BlockingSignature,
        control: &C,
    ) -> Result<ValidationDecision<u32>, BlockingError> {
        control.poll()?;
        Ok(ValidationDecision::valid())
    }
}

#[derive(Clone, Copy, Debug)]
struct RejectValidator {
    promote_row: u32,
    reschedule_node: u32,
}

impl BlockValidator<FakeState> for RejectValidator {
    fn validate_block<C: BlockingControl>(
        &mut self,
        _state: &FakeState,
        _projection: &BlockingProjection<u32>,
        _blocked: u32,
        _blocker: u32,
        _signature: &BlockingSignature,
        control: &C,
    ) -> Result<ValidationDecision<u32>, BlockingError> {
        control.poll()?;
        ValidationDecision::invalid(vec![self.promote_row], vec![self.reschedule_node], vec![7])
    }
}

fn pairwise_fixture(
    node_count: u32,
    concept_buckets: u32,
    cyclic_roles: bool,
) -> Result<BlockingFixture, BlockingError> {
    if node_count == 0 || concept_buckets == 0 {
        return Err(BlockingError::invalid(
            "blocking benchmark fixture sizes must be nonzero",
        ));
    }
    let mut state = FakeState::default();
    let root = state.create(NodeKind::Root, None)?;
    let parent = state.create(NodeKind::Tree, Some(root))?;
    state.add_fact(concept_buckets.saturating_add(1), vec![parent], true)?;
    let mut eligible_nodes = Vec::with_capacity(
        usize::try_from(node_count)
            .map_err(|_error| BlockingError::invalid("node count exceeds address space"))?,
    );
    for index in 0..node_count {
        let node = state.create(NodeKind::Tree, Some(parent))?;
        state.add_fact(1 + index % concept_buckets, vec![node], index % 2 == 0)?;
        state.add_fact(
            ROLE_FROM_PARENT_BASE + index % 4,
            vec![parent, node],
            index % 3 == 0,
        )?;
        state.add_fact(
            ROLE_TO_PARENT_BASE + index % 4,
            vec![node, parent],
            index % 5 == 0,
        )?;
        eligible_nodes.push(node);
    }
    if cyclic_roles {
        for (index, node) in eligible_nodes.iter().copied().enumerate() {
            let next_index = (index + 1) % eligible_nodes.len();
            state.add_fact(ROLE_CYCLE, vec![node, eligible_nodes[next_index]], false)?;
        }
    }
    let concepts = 1..=concept_buckets.saturating_add(1);
    let roles = ROLE_FROM_PARENT_BASE..=ROLE_CYCLE;
    Ok(BlockingFixture {
        state,
        vocabulary: BlockingVocabulary::new(concepts, roles)?,
        eligible_nodes,
    })
}

fn validated_fixture(node_count: u32) -> Result<ValidatedFixture, BlockingError> {
    if node_count < 2 {
        return Err(BlockingError::invalid(
            "validated benchmark requires at least two blockable nodes",
        ));
    }
    let mut state = FakeState::default();
    let root = state.create(NodeKind::Root, None)?;
    let parent = state.create(NodeKind::Tree, Some(root))?;
    state.add_fact(1, vec![parent], true)?;
    let mut rejected_node = None;
    let mut promote_row = None;
    for index in 0..node_count {
        let node = state.create(NodeKind::Tree, Some(parent))?;
        state.set_pending(node)?;
        state.add_fact(2, vec![node], true)?;
        let row_id = state.add_fact(3 + index % 16, vec![node], false)?;
        state.add_fact(ROLE_FROM_PARENT_BASE, vec![parent, node], false)?;
        if index == 1 {
            rejected_node = Some(node);
            promote_row = Some(row_id);
        }
    }
    Ok(ValidatedFixture {
        state,
        vocabulary: BlockingVocabulary::new(1..=18, [ROLE_FROM_PARENT_BASE])?,
        rejected_node: rejected_node
            .ok_or_else(|| BlockingError::invariant("validated rejected node is absent"))?,
        promote_row: promote_row
            .ok_or_else(|| BlockingError::invariant("validated promotion row is absent"))?,
    })
}

fn pairwise_plan() -> Result<_native::blocking::BlockingPlan, BlockingError> {
    select_blocking_plan(
        BlockingMode::Anywhere,
        BlockingRequirements {
            has_inverse_roles: true,
            ..BlockingRequirements::default()
        },
    )
}

fn validated_plan() -> Result<_native::blocking::BlockingPlan, BlockingError> {
    select_blocking_plan(
        BlockingMode::ValidatedAnywhere,
        BlockingRequirements {
            requires_validated_core: true,
            ..BlockingRequirements::default()
        },
    )
}

fn checker(
    kind: DirectCheckerKind,
    vocabulary: BlockingVocabulary,
    has_inverses: bool,
) -> Result<DirectChecker, BlockingError> {
    DirectChecker::new(kind, vocabulary, has_inverses)
}

fn manager(
    vocabulary: BlockingVocabulary,
    validated: bool,
    cache: Option<BlockingSignatureCache>,
) -> Result<BlockingManager<u32>, BlockingError> {
    let plan = if validated {
        validated_plan()?
    } else {
        pairwise_plan()?
    };
    BlockingManager::new(
        plan,
        checker(plan.direct_checker_kind, vocabulary, !validated)?,
        cache,
        BlockingLimits::default(),
        64,
    )
}

fn projection(fixture: &BlockingFixture) -> Result<BlockingProjection<u32>, BlockingError> {
    BlockingProjection::from_state(
        &fixture.state,
        &fixture.vocabulary,
        BlockingLimits::default(),
        &NeverCancel,
    )
}

fn signatures(
    projection: &BlockingProjection<u32>,
    nodes: &[u32],
    checker: &DirectChecker,
) -> Result<Vec<BlockingSignature>, BlockingError> {
    nodes
        .iter()
        .copied()
        .filter(|node| checker.can_be_blocked(projection, *node))
        .map(|node| checker.signature(projection, node))
        .collect()
}

fn cache(
    vocabulary: &BlockingVocabulary,
    max_entries: usize,
) -> Result<BlockingSignatureCache, BlockingError> {
    let namespace = BlockingCacheNamespace::new(
        "blocking-benchmark-ontology-v1",
        vocabulary.fingerprint(),
        DirectCheckerKind::Pairwise,
        _native::blocking::CoreBlockingMode::None,
        "blocking-benchmark-config-v1",
    )?;
    BlockingSignatureCache::new(namespace, max_entries, CACHE_BYTES)
}

const fn promotion_context() -> CachePromotionContext {
    CachePromotionContext {
        satisfiable: true,
        completed: true,
        has_nominals: false,
        has_additional_ontology: false,
        query_local_axioms: false,
        aborted: false,
    }
}

fn ensure(condition: bool, message: &'static str) -> Result<(), BlockingError> {
    if condition {
        Ok(())
    } else {
        Err(BlockingError::invariant(message))
    }
}

fn require<T>(result: Result<T, BlockingError>) -> T {
    result.unwrap_or_else(|error| {
        eprintln!("blocking benchmark setup failed: {error}");
        std::process::abort();
    })
}

fn verify_cache(
    vocabulary: &BlockingVocabulary,
    signatures: &[BlockingSignature],
) -> Result<BlockingSignatureCache, BlockingError> {
    let mut value = cache(vocabulary, signatures.len().saturating_mul(2))?;
    for signature in signatures {
        value.add(signature.clone())?;
    }
    ensure(
        value.entry_count() == signatures.len(),
        "cache benchmark signatures must be unique",
    )?;
    ensure(
        signatures
            .iter()
            .map(|signature| value.contains(signature))
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .all(|hit| hit),
        "preloaded cache must hit every signature",
    )?;
    Ok(value)
}

fn verify_incremental_parity(
    state: &FakeState,
    incremental: &BlockingManager<u32>,
) -> Result<(), BlockingError> {
    let mut incremental = incremental.clone();
    let mut forced = incremental.clone();
    let incremental_result = incremental.compute(state, &NeverCancel, false)?;
    let forced_result = forced.compute(state, &NeverCancel, true)?;
    ensure(
        incremental.canonical_snapshot() == forced.canonical_snapshot(),
        "incremental and forced blocking snapshots differ",
    )?;
    ensure(
        incremental_result.state_digest == forced_result.state_digest,
        "incremental and forced blocking digests differ",
    )
}

fn benchmark_projection_and_signatures(criterion: &mut Criterion) {
    let fixture = require(pairwise_fixture(512, 512, true));
    let projected = require(projection(&fixture));
    let direct_checker = require(checker(
        DirectCheckerKind::Pairwise,
        fixture.vocabulary.clone(),
        true,
    ));
    let expected_signatures = require(signatures(
        &projected,
        &fixture.eligible_nodes,
        &direct_checker,
    ));
    require(ensure(
        expected_signatures.len() == 512,
        "signature probe lost eligible nodes",
    ));

    let mut group = criterion.benchmark_group("wpr2_blocking_projection_signature");
    group.throughput(Throughput::Elements(512));
    group.bench_function("projection_512", |bencher| {
        bencher.iter(|| {
            black_box(BlockingProjection::from_state(
                black_box(&fixture.state),
                black_box(&fixture.vocabulary),
                BlockingLimits::default(),
                &NeverCancel,
            ))
        });
    });
    group.bench_function("pairwise_signatures_512", |bencher| {
        bencher.iter(|| {
            black_box(signatures(
                black_box(&projected),
                black_box(&fixture.eligible_nodes),
                black_box(&direct_checker),
            ))
        });
    });
    group.finish();
}

fn benchmark_cache(criterion: &mut Criterion) {
    let fixture = require(pairwise_fixture(512, 512, false));
    let projected = require(projection(&fixture));
    let direct_checker = require(checker(
        DirectCheckerKind::Pairwise,
        fixture.vocabulary.clone(),
        true,
    ));
    let signatures = require(signatures(
        &projected,
        &fixture.eligible_nodes,
        &direct_checker,
    ));
    let mut lookup_cache = require(verify_cache(&fixture.vocabulary, &signatures));
    let mut promoted = require(cache(&fixture.vocabulary, 1_024));
    let promotion =
        require(promoted.promote_model(signatures.clone(), promotion_context(), &NeverCancel));
    require(ensure(
        promotion.inserted == signatures.len() && promotion.entry_count == signatures.len(),
        "sound cache promotion did not retain every unique signature",
    ));

    let mut group = criterion.benchmark_group("wpr2_blocking_cache");
    group.throughput(Throughput::Elements(512));
    group.bench_function("lookup_hits_512", |bencher| {
        bencher.iter(|| {
            let result = signatures.iter().try_fold(0_usize, |hits, signature| {
                Ok::<usize, BlockingError>(hits + usize::from(lookup_cache.contains(signature)?))
            });
            black_box(result)
        });
    });
    group.bench_function("sound_promotion_512", |bencher| {
        bencher.iter_batched(
            || cache(&fixture.vocabulary, 1_024).map(|value| (value, signatures.clone())),
            |input| {
                let result = input.and_then(|(mut value, values)| {
                    value.promote_model(values, promotion_context(), &NeverCancel)
                });
                black_box(result)
            },
            BatchSize::SmallInput,
        );
    });
    group.finish();
}

fn benchmark_incremental(criterion: &mut Criterion) {
    let fixture = require(pairwise_fixture(1_024, 128, true));
    let mut warmed = require(manager(fixture.vocabulary.clone(), false, None));
    let initial = require(warmed.compute(&fixture.state, &NeverCancel, true));
    require(ensure(
        initial.stats.nodes_visited == 1_026,
        "initial incremental fixture node count differs",
    ));
    let clean_manager = warmed.clone();
    let mut dirty_state = fixture.state.clone();
    let dirty_node = fixture
        .eligible_nodes
        .last()
        .copied()
        .unwrap_or_else(|| require(Err(BlockingError::invariant("dirty node is absent"))));
    let row_id = require(dirty_state.add_fact(129, vec![dirty_node], true));
    let dirty_fact = require(dirty_state.fact(row_id)).clone();
    warmed.notify_fact_change(&dirty_fact);
    require(verify_incremental_parity(&dirty_state, &warmed));

    let mut incremental_check = warmed.clone();
    let incremental_result = require(incremental_check.compute(&dirty_state, &NeverCancel, false));
    require(ensure(
        incremental_result.earliest_recomputed_creation_id == Some(dirty_node),
        "dirty incremental probe did not retain the precise invalidation frontier",
    ));

    let mut group = criterion.benchmark_group("wpr2_blocking_incremental_vs_full");
    group.throughput(Throughput::Elements(1_024));
    group.bench_function("clean_incremental_1024", |bencher| {
        bencher.iter_batched(
            || clean_manager.clone(),
            |mut value| black_box(value.compute(&fixture.state, &NeverCancel, false)),
            BatchSize::SmallInput,
        );
    });
    group.bench_function("dirty_incremental_1024", |bencher| {
        bencher.iter_batched(
            || warmed.clone(),
            |mut value| black_box(value.compute(&dirty_state, &NeverCancel, false)),
            BatchSize::SmallInput,
        );
    });
    group.bench_function("dirty_forced_full_1024", |bencher| {
        bencher.iter_batched(
            || warmed.clone(),
            |mut value| black_box(value.compute(&dirty_state, &NeverCancel, true)),
            BatchSize::SmallInput,
        );
    });
    group.finish();
}

fn benchmark_validation(criterion: &mut Criterion) {
    let fixture = require(validated_fixture(256));
    let mut baseline_state = fixture.state.clone();
    let mut baseline_manager = require(manager(fixture.vocabulary.clone(), true, None));
    require(baseline_manager.compute_and_apply(&mut baseline_state, &NeverCancel, true));
    require(ensure(
        baseline_manager.is_directly_blocked(fixture.rejected_node),
        "validated repair node is not provisionally blocked",
    ));

    let mut accepted_state = baseline_state.clone();
    let mut accepted_manager = baseline_manager.clone();
    let mut accept_validator = AcceptValidator;
    let (_compute, accepted) = require(accepted_manager.validation_and_apply(
        &mut accepted_state,
        &mut accept_validator,
        &NeverCancel,
        false,
    ));
    require(ensure(
        accepted.valid
            && accepted.checked_blocks > 0
            && accepted_manager.ready_for_sat(&accepted_state, &NeverCancel) == Ok(true),
        "accepted validated pass did not open the SAT gate",
    ));

    let rejecting = RejectValidator {
        promote_row: fixture.promote_row,
        reschedule_node: fixture.rejected_node,
    };
    let mut repaired_state = baseline_state.clone();
    let mut repaired_manager = baseline_manager.clone();
    let mut repair_validator = rejecting;
    let (_compute, repaired) = require(repaired_manager.validation_and_apply(
        &mut repaired_state,
        &mut repair_validator,
        &NeverCancel,
        false,
    ));
    require(ensure(
        !repaired.valid
            && repaired.invalidated_blocks == 1
            && repaired_state
                .fact(fixture.promote_row)
                .is_ok_and(|fact| fact.core)
            && repaired_state.promoted.contains(&fixture.promote_row)
            && repaired_state.rescheduled.contains(&fixture.rejected_node),
        "validated repair did not promote core and reschedule atomically",
    ));

    let mut group = criterion.benchmark_group("wpr2_blocking_validation");
    group.throughput(Throughput::Elements(256));
    group.bench_function("accept_pass_256", |bencher| {
        bencher.iter_batched(
            || {
                (
                    baseline_state.clone(),
                    baseline_manager.clone(),
                    AcceptValidator,
                )
            },
            |(mut state, mut value, mut validator)| {
                black_box(value.validation_and_apply(
                    &mut state,
                    &mut validator,
                    &NeverCancel,
                    false,
                ))
            },
            BatchSize::SmallInput,
        );
    });
    group.bench_function("first_block_repair_256", |bencher| {
        bencher.iter_batched(
            || (baseline_state.clone(), baseline_manager.clone(), rejecting),
            |(mut state, mut value, mut validator)| {
                black_box(value.validation_and_apply(
                    &mut state,
                    &mut validator,
                    &NeverCancel,
                    false,
                ))
            },
            BatchSize::SmallInput,
        );
    });
    group.finish();
}

fn benchmark_anywhere_cyclic_5000(criterion: &mut Criterion) {
    let fixture = require(pairwise_fixture(5_000, 64, true));
    let mut semantic_manager = require(manager(fixture.vocabulary.clone(), false, None));
    let semantic_result = require(semantic_manager.compute(&fixture.state, &NeverCancel, true));
    require(ensure(
        semantic_result.stats.nodes_visited == 5_002,
        "5k anywhere probe lost projected nodes",
    ));
    require(ensure(
        semantic_result.stats.candidate_checks <= 5_000,
        "5k anywhere candidate work is not linear",
    ));
    require(semantic_manager.check_invariants(&NeverCancel));

    let mut group = criterion.benchmark_group("wpr2_blocking_anywhere_cyclic");
    group.throughput(Throughput::Elements(5_000));
    group.bench_function("pairwise_5000", |bencher| {
        bencher.iter_batched(
            || manager(fixture.vocabulary.clone(), false, None),
            |input| {
                let result =
                    input.and_then(|mut value| value.compute(&fixture.state, &NeverCancel, true));
                black_box(result)
            },
            BatchSize::LargeInput,
        );
    });
    group.finish();
}

fn blocking_kernel(criterion: &mut Criterion) {
    benchmark_projection_and_signatures(criterion);
    benchmark_cache(criterion);
    benchmark_incremental(criterion);
    benchmark_validation(criterion);
    benchmark_anywhere_cyclic_5000(criterion);
}

fn criterion_config() -> Criterion {
    Criterion::default()
        .warm_up_time(Duration::from_millis(100))
        .measurement_time(Duration::from_millis(250))
        .sample_size(10)
}

criterion_group! {
    name = benches;
    config = criterion_config();
    targets = blocking_kernel
}
criterion_main!(benches);
