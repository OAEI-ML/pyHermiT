use std::sync::atomic::{AtomicU64, Ordering};

use crate::error::{ErrorKind, NativeError, NativeResult};
use crate::session::OperationControl;

use super::{
    classify_ids, ClassificationLimits, ClassificationMode, ClassificationProblem,
    ClassificationResult,
};

fn relation_fixture() -> (Vec<u32>, Vec<(u32, u32)>) {
    let elements = vec![0, 1, 2, 3, 4, 5];
    let mut true_relations = elements
        .iter()
        .flat_map(|value| [(0, *value), (*value, 5), (*value, *value)])
        .collect::<Vec<_>>();
    true_relations.extend([(1, 2), (2, 1), (1, 3), (2, 3), (3, 4), (1, 4), (2, 4)]);
    true_relations.sort_unstable();
    true_relations.dedup();
    (elements, true_relations)
}

fn classify_fixture(mode: ClassificationMode) -> NativeResult<ClassificationResult> {
    let (elements, true_relations) = relation_fixture();
    classify_ids(
        ClassificationProblem {
            elements: &elements,
            top: 5,
            bottom: 0,
            known: &[],
            known_complete: false,
            mode,
            limits: ClassificationLimits::default(),
        },
        &crate::session::NeverAbort,
        |relations, _control| {
            Ok(relations
                .iter()
                .map(|relation| true_relations.binary_search(relation).is_ok())
                .collect())
        },
    )
}

#[test]
fn incremental_modes_match_exact_partition_and_reduction() -> NativeResult<()> {
    let deterministic = classify_fixture(ClassificationMode::Deterministic)?;
    let quasi = classify_fixture(ClassificationMode::QuasiOrder)?;
    assert_eq!(deterministic.hierarchy, quasi.hierarchy);
    assert_eq!(
        deterministic.hierarchy.nodes,
        vec![vec![0], vec![1, 2], vec![3], vec![4], vec![5]]
    );
    assert_eq!(
        deterministic.hierarchy.edges,
        vec![(0, 1), (1, 2), (2, 3), (3, 4)]
    );
    assert_eq!(deterministic.hierarchy.bottom_node, 0);
    assert_eq!(deterministic.hierarchy.top_node, 4);
    assert!(deterministic.statistics.semantic_tests < 36);
    assert_eq!(quasi.statistics.possible_subsumptions, 0);
    Ok(())
}

#[test]
fn shared_visited_descendant_does_not_create_a_false_boundary() -> NativeResult<()> {
    // 1 is unsatisfiable (equivalent to bottom 0). The told graph has two branches whose
    // downward searches share bottom: 1 -> 2 -> 4 -> 5 and 1 -> 3. A node reached through one
    // branch must remain visible as a proven neighbour when the other branch is visited.
    let elements = vec![0, 1, 2, 3, 4, 5, 6];
    let known = vec![(1, 2), (1, 3), (2, 4), (4, 5)];
    let mut true_relations = elements
        .iter()
        .flat_map(|value| [(0, *value), (*value, 6), (*value, *value)])
        .collect::<Vec<_>>();
    true_relations.extend(elements.iter().map(|parent| (1, *parent)));
    true_relations.extend([(2, 4), (2, 5), (4, 5)]);
    true_relations.sort_unstable();
    true_relations.dedup();

    for mode in [
        ClassificationMode::Deterministic,
        ClassificationMode::QuasiOrder,
    ] {
        let result = classify_ids(
            ClassificationProblem {
                elements: &elements,
                top: 6,
                bottom: 0,
                known: &known,
                known_complete: false,
                mode,
                limits: ClassificationLimits::default(),
            },
            &crate::session::NeverAbort,
            |relations, _control| {
                Ok(relations
                    .iter()
                    .map(|relation| true_relations.binary_search(relation).is_ok())
                    .collect())
            },
        )?;
        assert_eq!(
            result.hierarchy.nodes,
            vec![vec![0, 1], vec![2], vec![3], vec![4], vec![5], vec![6]]
        );
        assert_eq!(
            result.hierarchy.edges,
            vec![(0, 1), (0, 2), (1, 3), (2, 5), (3, 4), (4, 5)]
        );
    }
    Ok(())
}

#[test]
fn complete_relation_collapses_sccs_and_removes_redundant_edges() -> NativeResult<()> {
    let known = vec![(1, 2), (1, 3), (1, 4), (2, 1), (2, 3), (2, 4), (3, 4)];
    let calls = AtomicU64::new(0);
    let result = classify_ids(
        ClassificationProblem {
            elements: &[0, 1, 2, 3, 4, 5],
            top: 5,
            bottom: 0,
            known: &known,
            known_complete: true,
            mode: ClassificationMode::Deterministic,
            limits: ClassificationLimits::default(),
        },
        &crate::session::NeverAbort,
        |_relations, _control| {
            calls.fetch_add(1, Ordering::Relaxed);
            Ok(Vec::new())
        },
    )?;
    assert_eq!(
        result.hierarchy.nodes,
        vec![vec![0], vec![1, 2], vec![3], vec![4], vec![5]]
    );
    assert_eq!(result.hierarchy.edges, vec![(0, 1), (1, 2), (2, 3), (3, 4)]);
    assert_eq!(result.statistics.semantic_tests, 0);
    assert_eq!(calls.load(Ordering::Relaxed), 0);
    Ok(())
}

#[test]
fn complete_known_chain_is_linear_at_biomedical_depth() -> NativeResult<()> {
    let size = 10_000_u32;
    let elements = (0..size).collect::<Vec<_>>();
    let known = (0..size - 1)
        .map(|value| (value, value + 1))
        .collect::<Vec<_>>();
    let calls = AtomicU64::new(0);
    let result = classify_ids(
        ClassificationProblem {
            elements: &elements,
            top: size - 1,
            bottom: 0,
            known: &known,
            known_complete: true,
            mode: ClassificationMode::Deterministic,
            limits: ClassificationLimits::default(),
        },
        &crate::session::NeverAbort,
        |_relations, _control| {
            calls.fetch_add(1, Ordering::Relaxed);
            Ok(Vec::new())
        },
    )?;
    assert_eq!(
        result.hierarchy.nodes.len(),
        usize::try_from(size).unwrap_or(usize::MAX)
    );
    assert_eq!(
        result.hierarchy.edges.len(),
        usize::try_from(size - 1).unwrap_or(usize::MAX)
    );
    assert_eq!(result.statistics.semantic_tests, 0);
    assert_eq!(calls.load(Ordering::Relaxed), 0);
    Ok(())
}

#[test]
fn malformed_inputs_and_wrong_tester_cardinality_fail_closed() -> NativeResult<()> {
    let limits = ClassificationLimits::default();
    let control = crate::session::NeverAbort;
    let noop = |_relations: &[(u32, u32)], _control: &dyn OperationControl| Ok(Vec::new());
    assert!(classify_ids(
        ClassificationProblem {
            elements: &[0, 2, 1],
            top: 2,
            bottom: 0,
            known: &[],
            known_complete: false,
            mode: ClassificationMode::Deterministic,
            limits,
        },
        &control,
        noop,
    )
    .is_err());
    assert!(classify_ids(
        ClassificationProblem {
            elements: &[0, 1, 2],
            top: 2,
            bottom: 0,
            known: &[(1, 3)],
            known_complete: false,
            mode: ClassificationMode::Deterministic,
            limits,
        },
        &control,
        noop,
    )
    .is_err());
    let result = classify_ids(
        ClassificationProblem {
            elements: &[0, 1, 2],
            top: 2,
            bottom: 0,
            known: &[],
            known_complete: false,
            mode: ClassificationMode::Deterministic,
            limits,
        },
        &control,
        |_relations, _control| Ok(Vec::new()),
    );
    let Err(error) = result else {
        return Err(NativeError::invariant(
            "a truncated semantic batch did not fail",
        ));
    };
    assert_eq!(error.kind, ErrorKind::Invariant);
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
                "classification interrupted",
            ));
        }
        Ok(())
    }

    fn observe_memory(&self, _bytes: u64) -> NativeResult<()> {
        self.poll()
    }
}

#[test]
fn cancellation_and_limits_interrupt_without_a_partial_result() -> NativeResult<()> {
    let control = BoundedControl {
        polls: AtomicU64::new(0),
        allowed: 2,
    };
    let cancelled_result = classify_ids(
        ClassificationProblem {
            elements: &[0, 1, 2, 3],
            top: 3,
            bottom: 0,
            known: &[],
            known_complete: false,
            mode: ClassificationMode::QuasiOrder,
            limits: ClassificationLimits::default(),
        },
        &control,
        |relations, _control| Ok(vec![false; relations.len()]),
    );
    let Err(cancelled) = cancelled_result else {
        return Err(NativeError::invariant("bounded control did not interrupt"));
    };
    assert_eq!(cancelled.kind, ErrorKind::Cancelled);

    let limited_result = classify_ids(
        ClassificationProblem {
            elements: &[0, 1, 2, 3],
            top: 3,
            bottom: 0,
            known: &[],
            known_complete: false,
            mode: ClassificationMode::Deterministic,
            limits: ClassificationLimits {
                max_semantic_tests: 1,
                ..ClassificationLimits::default()
            },
        },
        &crate::session::NeverAbort,
        |relations, _control| Ok(vec![false; relations.len()]),
    );
    let Err(limited) = limited_result else {
        return Err(NativeError::invariant(
            "semantic work limit was not enforced",
        ));
    };
    assert_eq!(limited.kind, ErrorKind::Resource);
    assert_eq!(
        limited.context.get("limit").map(String::as_str),
        Some("max_semantic_tests")
    );
    Ok(())
}

#[test]
fn complete_graph_path_obeys_cancellation_and_memory_limits() -> NativeResult<()> {
    let elements = (0..10_000).collect::<Vec<_>>();
    let known = (0..9_999)
        .map(|value| (value, value + 1))
        .collect::<Vec<_>>();
    let control = BoundedControl {
        polls: AtomicU64::new(0),
        allowed: 2,
    };
    let cancelled_result = classify_ids(
        ClassificationProblem {
            elements: &elements,
            top: 9_999,
            bottom: 0,
            known: &known,
            known_complete: true,
            mode: ClassificationMode::Deterministic,
            limits: ClassificationLimits::default(),
        },
        &control,
        |_relations, _control| Ok(Vec::new()),
    );
    let Err(cancelled) = cancelled_result else {
        return Err(NativeError::invariant(
            "complete graph classification did not poll cancellation",
        ));
    };
    assert_eq!(cancelled.kind, ErrorKind::Cancelled);

    let memory_result = classify_ids(
        ClassificationProblem {
            elements: &[0, 1, 2],
            top: 2,
            bottom: 0,
            known: &[(0, 1), (1, 2)],
            known_complete: true,
            mode: ClassificationMode::Deterministic,
            limits: ClassificationLimits {
                max_memory_bytes: 1,
                ..ClassificationLimits::default()
            },
        },
        &crate::session::NeverAbort,
        |_relations, _control| Ok(Vec::new()),
    );
    let Err(memory) = memory_result else {
        return Err(NativeError::invariant(
            "complete graph classification ignored its memory limit",
        ));
    };
    assert_eq!(memory.kind, ErrorKind::Resource);
    assert_eq!(
        memory.context.get("limit").map(String::as_str),
        Some("max_memory_bytes")
    );
    Ok(())
}

#[test]
fn output_is_canonical_when_top_and_bottom_ids_are_not_extrema() -> NativeResult<()> {
    let result = classify_ids(
        ClassificationProblem {
            elements: &[3, 7, 9],
            top: 7,
            bottom: 9,
            known: &[],
            known_complete: false,
            mode: ClassificationMode::Deterministic,
            limits: ClassificationLimits::default(),
        },
        &crate::session::NeverAbort,
        |relations, _control| Ok(vec![false; relations.len()]),
    )?;
    assert_eq!(result.hierarchy.nodes, vec![vec![3], vec![7], vec![9]]);
    assert_eq!(result.hierarchy.top_node, 1);
    assert_eq!(result.hierarchy.bottom_node, 2);
    assert_eq!(result.hierarchy.edges, vec![(0, 1), (2, 0)]);
    Ok(())
}

#[test]
fn indexed_adjacency_matches_complete_relation_oracle_under_relabeling() -> NativeResult<()> {
    let size = 12_u32;
    let fixtures = [
        (1..size - 2).map(|id| (id, id + 1)).collect::<Vec<_>>(),
        (2..size - 1).map(|id| (1, id)).collect(),
        vec![(1, 2), (1, 3), (2, 4), (3, 4), (4, 5), (2, 6)],
        vec![(1, 2), (2, 1), (2, 3), (3, 4), (5, 6), (6, 5)],
        Vec::new(),
    ];
    let elements = (0..size).collect::<Vec<_>>();
    for edges in fixtures {
        for reverse in [false, true] {
            let remap = |id: u32| if reverse { size - 1 - id } else { id };
            let mut closure = vec![vec![false; size as usize]; size as usize];
            for (id, row) in closure.iter_mut().enumerate() {
                row[id] = true;
                row[size as usize - 1] = true;
            }
            closure[0].fill(true);
            for &(child, parent) in &edges {
                closure[remap(child) as usize][remap(parent) as usize] = true;
            }
            for middle in 0..size as usize {
                for child in 0..size as usize {
                    for parent in 0..size as usize {
                        closure[child][parent] |= closure[child][middle] && closure[middle][parent];
                    }
                }
            }
            let mut known = Vec::new();
            for (child, parents) in closure.iter().enumerate() {
                for (parent, entailed) in parents.iter().enumerate() {
                    if *entailed {
                        known.push((
                            u32::try_from(child)
                                .map_err(|_| NativeError::invariant("test child exceeds u32"))?,
                            u32::try_from(parent)
                                .map_err(|_| NativeError::invariant("test parent exceeds u32"))?,
                        ));
                    }
                }
            }
            let expected = classify_ids(
                ClassificationProblem {
                    elements: &elements,
                    top: size - 1,
                    bottom: 0,
                    known: &known,
                    known_complete: true,
                    mode: ClassificationMode::Deterministic,
                    limits: ClassificationLimits::default(),
                },
                &crate::session::NeverAbort,
                |_queries, _control| {
                    Err(NativeError::invariant("complete relation must not query"))
                },
            )?;
            for mode in [
                ClassificationMode::Deterministic,
                ClassificationMode::QuasiOrder,
            ] {
                let actual = classify_ids(
                    ClassificationProblem {
                        elements: &elements,
                        top: size - 1,
                        bottom: 0,
                        known: &[],
                        known_complete: false,
                        mode,
                        limits: ClassificationLimits::default(),
                    },
                    &crate::session::NeverAbort,
                    |queries, _control| {
                        Ok(queries
                            .iter()
                            .map(|&(child, parent)| closure[child as usize][parent as usize])
                            .collect())
                    },
                )?;
                assert_eq!(actual.hierarchy, expected.hierarchy);
                assert!(actual.statistics.hierarchy_neighbor_visits > 0);
            }
        }
    }
    Ok(())
}

#[test]
fn unrelated_classes_enumerate_adjacency_not_all_edges_per_node() -> NativeResult<()> {
    let size = 64_u32;
    let elements = (0..size).collect::<Vec<_>>();
    let result = classify_ids(
        ClassificationProblem {
            elements: &elements,
            top: size - 1,
            bottom: 0,
            known: &[],
            known_complete: false,
            mode: ClassificationMode::Deterministic,
            limits: ClassificationLimits::default(),
        },
        &crate::session::NeverAbort,
        |queries, _control| {
            Ok(queries
                .iter()
                .map(|&(child, parent)| child == 0 || parent == size - 1 || child == parent)
                .collect())
        },
    )?;
    assert_eq!(result.hierarchy.nodes.len(), size as usize);
    assert_eq!(result.hierarchy.edges.len(), 2 * (size as usize - 2));
    assert!(result.statistics.hierarchy_neighbor_visits <= 4 * u64::from(size).pow(2));
    Ok(())
}
