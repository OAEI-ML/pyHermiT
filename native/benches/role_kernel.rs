// SPDX-License-Identifier: LGPL-3.0-or-later

use _native::roles::{
    NeverCancel, RoleAutomatonWire, RoleError, RoleLimits, RoleRuntime, RoleTransition,
};
use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};

fn transitive_runtime() -> RoleRuntime {
    require(RoleRuntime::new(
        8,
        vec![0, 1, 3, 2, 5, 4, 7, 6],
        0,
        1,
        vec![RoleAutomatonWire {
            component_id: 2,
            state_count: 2,
            initial_state: 0,
            final_states: vec![1],
            transitions: vec![
                RoleTransition::labelled(0, 2, 1),
                RoleTransition::epsilon(1, 0),
            ],
        }],
        RoleLimits::default(),
        &NeverCancel,
    ))
}

fn branching_runtime(branches: u32) -> RoleRuntime {
    let mut transitions = Vec::new();
    for branch in 0..branches {
        let state = branch + 1;
        transitions.push(RoleTransition::epsilon(0, state));
        transitions.push(RoleTransition::labelled(state, 2, branches + 1));
    }
    require(RoleRuntime::new(
        4,
        vec![0, 1, 3, 2],
        0,
        1,
        vec![RoleAutomatonWire {
            component_id: 2,
            state_count: branches + 2,
            initial_state: 0,
            final_states: vec![branches + 1],
            transitions,
        }],
        RoleLimits::default(),
        &NeverCancel,
    ))
}

fn require<T>(result: Result<T, RoleError>) -> T {
    result.unwrap_or_else(|error| {
        eprintln!("role benchmark setup or execution failed: {error}");
        std::process::abort();
    })
}

fn role_benchmarks(criterion: &mut Criterion) {
    let runtime = transitive_runtime();
    {
        let mut group = criterion.benchmark_group("role_nfa_transitive");
        for length in [1_usize, 8, 64, 512] {
            let word = vec![2_u32; length];
            group.throughput(Throughput::Elements(
                u64::try_from(length).unwrap_or(u64::MAX),
            ));
            group.bench_with_input(
                BenchmarkId::from_parameter(length),
                &word,
                |bencher, input| {
                    bencher.iter(|| {
                        black_box(require(runtime.accepts(2, black_box(input), &NeverCancel)))
                    });
                },
            );
        }
        group.finish();
    }

    {
        let mut group = criterion.benchmark_group("role_nfa_epsilon_fanout");
        for branches in [8_u32, 64, 512] {
            let runtime = branching_runtime(branches);
            group.throughput(Throughput::Elements(u64::from(branches)));
            group.bench_with_input(
                BenchmarkId::from_parameter(branches),
                &branches,
                |bencher, _input| {
                    bencher.iter(|| {
                        black_box(require(runtime.accepts(2, black_box(&[2]), &NeverCancel)))
                    });
                },
            );
        }
        group.finish();
    }
}

criterion_group!(benches, role_benchmarks);
criterion_main!(benches);
