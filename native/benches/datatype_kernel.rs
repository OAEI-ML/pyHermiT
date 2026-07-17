use std::collections::BTreeSet;
use std::hint::black_box;

use _native::datatypes::{
    solve_component, ConstraintComponent, DataIdentity, DatatypeError, DomainConstraint,
    DomainKind, EqualityConstraint, ExactRational, InequalityConstraint, NeverCancel, SolverLimits,
};
use _native::model::DependencySet;
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use num_bigint::BigInt;

fn require<T>(result: Result<T, DatatypeError>) -> T {
    result.unwrap_or_else(|error| {
        eprintln!("datatype benchmark setup or execution failed: {error}");
        std::process::abort();
    })
}

fn identity(value: u32) -> DataIdentity {
    DataIdentity::Numeric(require(ExactRational::new(
        BigInt::from(value),
        BigInt::from(1_u8),
    )))
}

fn finite(values: u32) -> DomainKind {
    DomainKind::Finite((0..values).map(identity).collect::<BTreeSet<_>>())
}

fn chain(size: u32, colours: u32) -> ConstraintComponent {
    let variables = (0..size).collect::<Vec<_>>();
    let domains = variables
        .iter()
        .map(|variable| DomainConstraint {
            variable: *variable,
            domain: finite(colours),
            dependencies: DependencySet::empty(),
        })
        .collect();
    let inequalities = (1..size)
        .map(|right| InequalityConstraint {
            left: right - 1,
            right,
            dependencies: DependencySet::empty(),
        })
        .collect();
    ConstraintComponent {
        variables,
        domains,
        fixed_values: Vec::new(),
        equalities: Vec::new(),
        inequalities,
        cardinalities: Vec::new(),
    }
}

fn equality_chain(size: u32) -> ConstraintComponent {
    let variables = (0..size).collect::<Vec<_>>();
    let equalities = (1..size)
        .map(|right| EqualityConstraint {
            left: right - 1,
            right,
            dependencies: DependencySet::empty(),
        })
        .collect();
    ConstraintComponent {
        variables,
        domains: Vec::new(),
        fixed_values: Vec::new(),
        equalities,
        inequalities: Vec::new(),
        cardinalities: Vec::new(),
    }
}

fn triangle(colours: u32) -> ConstraintComponent {
    let mut component = chain(3, colours);
    component.inequalities.push(InequalityConstraint {
        left: 0,
        right: 2,
        dependencies: DependencySet::empty(),
    });
    component
}

fn datatype_solver(c: &mut Criterion) {
    let mut group = c.benchmark_group("datatype_component_solver");
    for size in [32_u32, 128, 512] {
        let component = chain(size, 3);
        group.bench_with_input(BenchmarkId::new("eliminated_chain", size), &size, |b, _| {
            b.iter(|| {
                black_box(require(solve_component(
                    black_box(&component),
                    SolverLimits::default(),
                    &NeverCancel,
                )))
            });
        });
    }
    let equalities = equality_chain(1_024);
    group.bench_function("equality_collapse/1024", |b| {
        b.iter(|| {
            black_box(require(solve_component(
                black_box(&equalities),
                SolverLimits::default(),
                &NeverCancel,
            )))
        });
    });
    let unsatisfiable = triangle(2);
    group.bench_function("unsatisfiable_triangle/2", |b| {
        b.iter(|| {
            black_box(require(solve_component(
                black_box(&unsatisfiable),
                SolverLimits::default(),
                &NeverCancel,
            )))
        });
    });
    group.finish();
}

criterion_group!(benches, datatype_solver);
criterion_main!(benches);
