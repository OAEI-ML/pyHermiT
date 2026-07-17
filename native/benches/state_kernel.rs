// SPDX-License-Identifier: LGPL-3.0-or-later

use _native::error::NativeResult;
use _native::model::{DependencySet, NodeHandle, NodeKind};
use _native::store::TableauKernel;
use criterion::{black_box, criterion_group, criterion_main, BatchSize, Criterion};

fn populated_kernel() -> NativeResult<TableauKernel> {
    let mut kernel = TableauKernel::new();
    let root = kernel.create_node(NodeKind::Root, None, true, Some(0), None, None)?;
    for identifier in 0..512_u32 {
        let node = kernel.create_node(NodeKind::Tree, Some(root), false, None, None, None)?;
        kernel.add_fact(
            identifier % 31,
            vec![node],
            DependencySet::empty(),
            identifier % 7 == 0,
            None,
        )?;
    }
    kernel.check_invariants()?;
    Ok(kernel)
}

fn state_kernel(criterion: &mut Criterion) {
    criterion.bench_function("wpr0_create_index_and_check_512", |bencher| {
        bencher.iter(|| black_box(populated_kernel()));
    });
    criterion.bench_function("wpr0_branch_mutate_rollback_512", |bencher| {
        bencher.iter_batched(
            populated_kernel,
            |kernel| {
                let result = kernel.and_then(|mut kernel| {
                    kernel.push_branch(
                        "merge".to_owned(),
                        vec![1, 2],
                        0,
                        DependencySet::empty(),
                    )?;
                    for identifier in 0..64_u32 {
                        kernel.add_fact(
                            64 + identifier,
                            vec![NodeHandle::new(identifier + 1, 1)],
                            DependencySet::new(vec![0])?,
                            false,
                            None,
                        )?;
                    }
                    kernel.backtrack_to(0)?;
                    kernel.check_invariants()
                });
                black_box(result)
            },
            BatchSize::SmallInput,
        );
    });
}

criterion_group!(benches, state_kernel);
criterion_main!(benches);
