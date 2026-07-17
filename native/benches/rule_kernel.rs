// SPDX-License-Identifier: LGPL-3.0-or-later

use std::collections::BTreeMap;
use std::sync::Arc;

use _native::error::NativeResult;
use _native::merging::MergingManager;
use _native::model::{DependencySet, NodeKind};
use _native::nominals::NominalIntroductionManager;
use _native::rules::{
    GroundAtom, PredicateKind, RuleAtom, RuleClause, RuleEngine, RulePredicate, RuleProgram, Term,
    TermSort,
};
use _native::store::TableauKernel;
use _native::{CancellationHandle, CancellationState};
use criterion::{black_box, criterion_group, criterion_main, BatchSize, Criterion};

fn cancellation() -> NativeResult<Arc<CancellationState>> {
    Ok(CancellationHandle::from_options(None, None)?.state())
}

fn concept(predicate_id: u32) -> NativeResult<RulePredicate> {
    Ok(
        RulePredicate::new(predicate_id, PredicateKind::Concept, vec![TermSort::Object])?
            .with_symbol_id(predicate_id),
    )
}

fn saturation_input() -> NativeResult<(TableauKernel, RuleEngine, Arc<CancellationState>)> {
    let variable = Term::variable(0, TermSort::Object);
    let clause = RuleClause::new(
        0,
        vec![RuleAtom::new(0, vec![variable.clone()])?],
        vec![RuleAtom::new(1, vec![variable])?],
        vec![0],
        vec![0],
    )?;
    let program = RuleProgram::new(vec![concept(0)?, concept(1)?], vec![clause])?;
    let mut engine = RuleEngine::new(program, BTreeMap::new(), BTreeMap::new(), true)?;
    let mut kernel = TableauKernel::new();
    for identifier in 0..512_u32 {
        let node = kernel.create_node(NodeKind::Root, None, false, Some(identifier), None, None)?;
        engine.dispatch_ground_atom(
            &mut kernel,
            GroundAtom::new(0, vec![node])?,
            DependencySet::empty(),
            true,
            &[identifier],
        )?;
    }
    let control = cancellation()?;
    engine.initialize(&mut kernel, Arc::clone(&control))?;
    Ok((kernel, engine, control))
}

fn branch_input() -> NativeResult<(TableauKernel, RuleEngine, Arc<CancellationState>)> {
    let program = RuleProgram::new(vec![concept(0)?, concept(1)?], Vec::new())?;
    let mut engine = RuleEngine::new(program, BTreeMap::new(), BTreeMap::new(), true)?;
    let mut kernel = TableauKernel::new();
    let node = kernel.create_node(NodeKind::Root, None, false, None, None, None)?;
    kernel.begin_operation()?;
    engine.apply_ground_head(
        &mut kernel,
        vec![
            GroundAtom::new(0, vec![node])?,
            GroundAtom::new(1, vec![node])?,
        ],
        DependencySet::empty(),
        &[],
        &[],
    )?;
    Ok((kernel, engine, cancellation()?))
}

type MergeInput = (
    TableauKernel,
    MergingManager,
    _native::model::NodeHandle,
    _native::model::NodeHandle,
    Arc<CancellationState>,
);

fn merge_input() -> NativeResult<MergeInput> {
    const FACT_COUNT: u32 = 512;
    let mut predicates = (0..FACT_COUNT)
        .map(concept)
        .collect::<NativeResult<Vec<_>>>()?;
    predicates.push(
        RulePredicate::new(
            FACT_COUNT,
            PredicateKind::Equality,
            vec![TermSort::Object, TermSort::Object],
        )?
        .with_opposite(FACT_COUNT + 1),
    );
    predicates.push(
        RulePredicate::new(
            FACT_COUNT + 1,
            PredicateKind::Inequality,
            vec![TermSort::Object, TermSort::Object],
        )?
        .with_opposite(FACT_COUNT),
    );
    let program = RuleProgram::new(predicates, Vec::new())?;
    let manager = MergingManager::new(&program)?;
    let mut kernel = TableauKernel::new();
    let target = kernel.create_node(NodeKind::Root, None, true, Some(0), None, None)?;
    let source = kernel.create_node(NodeKind::Root, None, false, None, None, None)?;
    for predicate_id in 0..FACT_COUNT {
        kernel.add_fact(
            predicate_id,
            vec![source],
            DependencySet::empty(),
            predicate_id % 2 == 0,
            Some(predicate_id),
        )?;
    }
    kernel.begin_operation()?;
    Ok((kernel, manager, source, target, cancellation()?))
}

fn nominal_input() -> NativeResult<(
    TableauKernel,
    RuleEngine,
    NominalIntroductionManager,
    Arc<CancellationState>,
)> {
    let predicates = vec![
        concept(0)?,
        RulePredicate::new(
            1,
            PredicateKind::Equality,
            vec![TermSort::Object, TermSort::Object],
        )?
        .with_opposite(2),
        RulePredicate::new(
            2,
            PredicateKind::Inequality,
            vec![TermSort::Object, TermSort::Object],
        )?
        .with_opposite(1),
        RulePredicate::new(
            3,
            PredicateKind::AnnotatedEquality,
            vec![TermSort::Object; 3],
        )?
        .with_cardinality(4, 7, 0),
    ];
    let mut engine = RuleEngine::new(
        RuleProgram::new(predicates, Vec::new())?,
        BTreeMap::new(),
        BTreeMap::new(),
        true,
    )?;
    let mut kernel = TableauKernel::new();
    let root = kernel.create_node(NodeKind::Root, None, false, None, None, None)?;
    let direct = kernel.create_node(NodeKind::Tree, Some(root), false, None, None, None)?;
    let nested = kernel.create_node(NodeKind::Tree, Some(direct), false, None, None, None)?;
    engine.dispatch_ground_atom(
        &mut kernel,
        GroundAtom::new(3, vec![direct, nested, root])?,
        DependencySet::empty(),
        false,
        &[],
    )?;
    kernel.begin_operation()?;
    Ok((
        kernel,
        engine,
        NominalIntroductionManager::default(),
        cancellation()?,
    ))
}

fn rule_kernel(criterion: &mut Criterion) {
    let dependencies = [
        DependencySet::empty().add(0).add(2).add(4).add(6),
        DependencySet::empty().add(1).add(3).add(5).add(7),
    ];
    criterion.bench_function("wpr1_dependency_union_8", |bencher| {
        bencher.iter(|| black_box(DependencySet::union(&[&dependencies[0], &dependencies[1]])));
    });
    criterion.bench_function("wpr1_indexed_delta_512", |bencher| {
        bencher.iter_batched(
            saturation_input,
            |input| {
                let result = input.and_then(|(mut kernel, mut engine, control)| {
                    engine.saturate_hyperresolution(&mut kernel, control)
                });
                black_box(result)
            },
            BatchSize::SmallInput,
        );
    });
    criterion.bench_function("wpr1_branch_advance_rollback", |bencher| {
        bencher.iter_batched(
            branch_input,
            |input| {
                let result = input.and_then(|(mut kernel, mut engine, control)| {
                    engine.process_next_disjunction(&mut kernel, &control)?;
                    kernel.install_clash(
                        "empty_head".to_owned(),
                        DependencySet::new(vec![0])?,
                        vec![0],
                        None,
                    )?;
                    engine.resolve_clash(&mut kernel, &control)
                });
                black_box(result)
            },
            BatchSize::SmallInput,
        );
    });
    criterion.bench_function("wpr2_merge_copy_512", |bencher| {
        bencher.iter_batched(
            merge_input,
            |input| {
                let result =
                    input.and_then(|(mut kernel, manager, source, target, cancellation)| {
                        manager.merge(
                            &mut kernel,
                            source,
                            target,
                            DependencySet::empty(),
                            Some(&cancellation),
                        )
                    });
                black_box(result)
            },
            BatchSize::SmallInput,
        );
    });
    criterion.bench_function("wpr2_nominal_cardinality_4", |bencher| {
        bencher.iter_batched(
            nominal_input,
            |input| {
                let result =
                    input.and_then(|(mut kernel, mut engine, mut manager, cancellation)| {
                        manager.process_next(&mut kernel, &mut engine, &cancellation)
                    });
                black_box(result)
            },
            BatchSize::SmallInput,
        );
    });
}

criterion_group!(benches, rule_kernel);
criterion_main!(benches);
