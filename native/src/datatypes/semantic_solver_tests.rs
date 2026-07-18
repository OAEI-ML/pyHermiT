// SPDX-License-Identifier: LGPL-3.0-or-later

#![allow(
    clippy::expect_used,
    clippy::field_reassign_with_default,
    clippy::panic,
    clippy::unwrap_used
)]

use std::cell::Cell;
use std::collections::{BTreeMap, BTreeSet};

use serde::Deserialize;
use serde_json::Value;

use super::*;
use crate::datatypes::{
    decode_datatype_range_model, decode_literal_semantic, DatatypeErrorKind, DecodedLiteral,
    NativeDataValueFamily, NeverCancel, OpaqueRangePolicy,
};

const ORACLE: &str =
    include_str!("../../../tests/data/datatypes/wpr3-native-semantic-solver-v1.json");

#[derive(Deserialize)]
struct Oracle {
    case_count: usize,
    cases: Vec<OracleCase>,
    literals: Vec<OracleLiteral>,
    model_json: String,
    rollback_checks: Vec<RollbackCheck>,
    schema_version: u32,
}

#[derive(Deserialize)]
struct OracleLiteral {
    payload_json: String,
    source_literal_id: u32,
}

#[derive(Clone, Deserialize)]
struct OracleCase {
    cardinalities: Vec<OracleCardinality>,
    equalities: Vec<OracleBinary>,
    exhaustive: bool,
    expected: OracleExpected,
    fixed_values: Vec<OracleFixed>,
    inequalities: Vec<OracleBinary>,
    name: String,
    ranges: Vec<OracleRange>,
    variables: Vec<u32>,
}

#[derive(Clone, Deserialize)]
struct OracleRange {
    data_range_id: u32,
    dependencies: Vec<u32>,
    positive: bool,
    variable: u32,
}

#[derive(Clone, Deserialize)]
struct OracleFixed {
    dependencies: Vec<u32>,
    literal_id: usize,
    variable: u32,
}

#[derive(Clone, Deserialize)]
struct OracleBinary {
    dependencies: Vec<u32>,
    left: u32,
    right: u32,
}

#[derive(Clone, Deserialize)]
struct OracleCardinality {
    dependencies: Vec<u32>,
    minimum: u64,
    variable: u32,
}

#[derive(Clone, Deserialize)]
struct OracleExpected {
    assignments: Vec<OracleAssignment>,
    clash: Option<OracleClash>,
    satisfiable: bool,
}

#[derive(Clone, Deserialize)]
struct OracleAssignment {
    value: OracleWitness,
    variable: u32,
}

#[derive(Clone, Deserialize)]
#[serde(tag = "kind", rename_all = "lowercase")]
enum OracleWitness {
    Concrete {
        identity: Value,
    },
    Symbolic {
        domain_digest: String,
        family: String,
        ordinal: u64,
    },
}

#[derive(Clone, Deserialize)]
struct OracleClash {
    dependencies: Vec<u32>,
    kind: String,
    variables: Vec<u32>,
}

#[derive(Deserialize)]
struct RollbackCheck {
    baseline: String,
    transient: String,
}

fn dependency_set(values: &[u32]) -> DependencySet {
    DependencySet::new(values.to_vec()).expect("canonical dependency set")
}

fn decode_oracle() -> (Oracle, NativeDatatypeRangeModel, Vec<DataIdentity>) {
    let oracle: Oracle = serde_json::from_str(ORACLE).expect("semantic solver oracle");
    let limits = SemanticSolverLimits::default();
    let model = decode_datatype_range_model(
        oracle.model_json.as_bytes(),
        limits.range_wire,
        OpaqueRangePolicy::Reject,
        &NeverCancel,
    )
    .expect("canonical semantic model");
    let identities = oracle
        .literals
        .iter()
        .map(|literal| {
            match decode_literal_semantic(
                literal.source_literal_id,
                literal.payload_json.as_bytes(),
                limits.range_wire.values,
                &NeverCancel,
            )
            .expect("canonical fixed literal")
            {
                DecodedLiteral::Semantic(value) => value.data_identity,
                DecodedLiteral::Opaque(_) => panic!("oracle fixed literal cannot be opaque"),
            }
        })
        .collect();
    (oracle, model, identities)
}

fn component(
    case: &OracleCase,
    identities: &[DataIdentity],
) -> SemanticDatatypeConstraintComponent {
    SemanticDatatypeConstraintComponent {
        variables: case.variables.clone(),
        ranges: case
            .ranges
            .iter()
            .map(|value| SemanticRangeConstraint {
                variable: value.variable,
                data_range_id: value.data_range_id,
                positive: value.positive,
                dependencies: dependency_set(&value.dependencies),
            })
            .collect(),
        fixed_values: case
            .fixed_values
            .iter()
            .map(|value| SemanticFixedValueConstraint {
                variable: value.variable,
                value: identities[value.literal_id].clone(),
                dependencies: dependency_set(&value.dependencies),
            })
            .collect(),
        equalities: case
            .equalities
            .iter()
            .map(|value| SemanticEqualityConstraint {
                left: value.left,
                right: value.right,
                dependencies: dependency_set(&value.dependencies),
            })
            .collect(),
        inequalities: case
            .inequalities
            .iter()
            .map(|value| SemanticInequalityConstraint {
                left: value.left,
                right: value.right,
                dependencies: dependency_set(&value.dependencies),
            })
            .collect(),
        cardinalities: case
            .cardinalities
            .iter()
            .map(|value| SemanticCardinalityConstraint {
                variable: value.variable,
                minimum: value.minimum,
                dependencies: dependency_set(&value.dependencies),
            })
            .collect(),
    }
}

#[test]
fn production_python_oracle_matches_dense_ranges_clashes_and_witnesses() {
    let (oracle, model, identities) = decode_oracle();
    assert_eq!(oracle.schema_version, 1);
    assert_eq!(oracle.case_count, oracle.cases.len());
    let limits = SemanticSolverLimits::default();
    for case in &oracle.cases {
        let source = component(case, &identities);
        let compiled = compile_datatype_constraint_component(&model, &source, limits, &NeverCancel)
            .unwrap_or_else(|error| panic!("{} did not compile: {error}", case.name));
        let unique_ranges = source
            .ranges
            .iter()
            .map(|value| value.data_range_id)
            .collect::<BTreeSet<_>>()
            .len();
        assert_eq!(
            compiled.compiled_range_count(),
            unique_ranges,
            "{}",
            case.name
        );
        let first = solve_compiled_semantic_component(&compiled, limits, &NeverCancel)
            .unwrap_or_else(|error| panic!("{} did not solve: {error}", case.name));
        let second = solve_compiled_semantic_component(&compiled, limits, &NeverCancel).unwrap();
        assert_eq!(first, second, "{} is nondeterministic", case.name);
        assert_expected(&first, &case.expected, &case.name);
        assert_certificate(&first, &source, &compiled, limits, &case.name);
        if case.exhaustive {
            let exhaustive =
                solve_compiled_semantic_component_exhaustive(&compiled, limits, &NeverCancel)
                    .unwrap_or_else(|error| panic!("{} exhaustive failed: {error}", case.name));
            assert_eq!(
                first.satisfiable, exhaustive.satisfiable,
                "{} optimized/exhaustive disagreement",
                case.name
            );
            assert_eq!(
                first.clash, exhaustive.clash,
                "{} clash mismatch",
                case.name
            );
        }
    }
}

#[test]
fn cancellation_and_step_limits_are_operation_local() {
    let (oracle, model, identities) = decode_oracle();
    let case = oracle
        .cases
        .iter()
        .find(|value| value.name == "infinite-integer-clique-elimination")
        .unwrap();
    let limits = SemanticSolverLimits::default();
    let compiled = compile_datatype_constraint_component(
        &model,
        &component(case, &identities),
        limits,
        &NeverCancel,
    )
    .unwrap();
    let baseline = solve_compiled_semantic_component(&compiled, limits, &NeverCancel).unwrap();

    let compile_cancellation = CancelAfter::new(4);
    let error = compile_datatype_constraint_component(
        &model,
        &component(case, &identities),
        limits,
        &compile_cancellation,
    )
    .unwrap_err();
    assert_eq!(error.kind, DatatypeErrorKind::Cancelled);
    assert!(compile_datatype_constraint_component(
        &model,
        &component(case, &identities),
        limits,
        &NeverCancel,
    )
    .is_ok());

    let mut compile_limited = limits;
    compile_limited.max_compile_steps = 1;
    let error = compile_datatype_constraint_component(
        &model,
        &component(case, &identities),
        compile_limited,
        &NeverCancel,
    )
    .unwrap_err();
    assert_eq!(error.kind, DatatypeErrorKind::Resource);
    assert_eq!(error.limit, Some("max_semantic_compile_steps"));

    let cancellation = CancelAfter::new(4);
    let error = solve_compiled_semantic_component(&compiled, limits, &cancellation).unwrap_err();
    assert_eq!(error.kind, DatatypeErrorKind::Cancelled);
    assert_eq!(
        solve_compiled_semantic_component(&compiled, limits, &NeverCancel).unwrap(),
        baseline
    );

    let mut constrained = limits;
    constrained.max_solver_steps = 1;
    let error =
        solve_compiled_semantic_component(&compiled, constrained, &NeverCancel).unwrap_err();
    assert_eq!(error.kind, DatatypeErrorKind::Resource);
    assert_eq!(error.limit, Some("max_semantic_solver_steps"));
    assert_eq!(
        solve_compiled_semantic_component(&compiled, limits, &NeverCancel).unwrap(),
        baseline
    );
}

#[test]
fn rollback_order_and_dense_range_compilation_are_stable() {
    let (oracle, model, identities) = decode_oracle();
    let limits = SemanticSolverLimits::default();
    for check in &oracle.rollback_checks {
        let baseline_case = oracle
            .cases
            .iter()
            .find(|value| value.name == check.baseline)
            .unwrap();
        let transient_case = oracle
            .cases
            .iter()
            .find(|value| value.name == check.transient)
            .unwrap();
        let baseline = compile_datatype_constraint_component(
            &model,
            &component(baseline_case, &identities),
            limits,
            &NeverCancel,
        )
        .unwrap();
        let transient = compile_datatype_constraint_component(
            &model,
            &component(transient_case, &identities),
            limits,
            &NeverCancel,
        )
        .unwrap();
        let before = solve_compiled_semantic_component(&baseline, limits, &NeverCancel).unwrap();
        let branch = solve_compiled_semantic_component(&transient, limits, &NeverCancel).unwrap();
        let after = solve_compiled_semantic_component(&baseline, limits, &NeverCancel).unwrap();
        assert_eq!(before, after);
        assert!(!branch.satisfiable);
    }

    let repeated = oracle
        .cases
        .iter()
        .find(|value| value.name == "finite-two-colour-triangle")
        .unwrap();
    let compiled = compile_datatype_constraint_component(
        &model,
        &component(repeated, &identities),
        limits,
        &NeverCancel,
    )
    .unwrap();
    assert_eq!(compiled.compiled_range_count(), 1);
}

#[test]
fn invalid_ids_references_and_compile_limits_fail_closed() {
    let (oracle, model, identities) = decode_oracle();
    let case = oracle
        .cases
        .iter()
        .find(|value| value.name == "negative-range-selects-false")
        .unwrap();
    let limits = SemanticSolverLimits::default();

    let mut dangling = component(case, &identities);
    dangling.ranges[0].data_range_id = u32::MAX;
    let error =
        compile_datatype_constraint_component(&model, &dangling, limits, &NeverCancel).unwrap_err();
    assert_eq!(error.kind, DatatypeErrorKind::Invalid);

    let mut outside = component(case, &identities);
    outside.fixed_values[0].variable = 99;
    let error =
        compile_datatype_constraint_component(&model, &outside, limits, &NeverCancel).unwrap_err();
    assert_eq!(error.kind, DatatypeErrorKind::Invalid);

    let mut constrained = limits;
    constrained.max_compiled_ranges = 1;
    let error = compile_datatype_constraint_component(
        &model,
        &component(case, &identities),
        constrained,
        &NeverCancel,
    )
    .unwrap_err();
    assert_eq!(error.kind, DatatypeErrorKind::Resource);
    assert_eq!(error.limit, Some("max_compiled_ranges"));
}

fn assert_expected(result: &SemanticSolveResult, expected: &OracleExpected, name: &str) {
    assert_eq!(result.satisfiable, expected.satisfiable, "{name}");
    match (&result.clash, &expected.clash) {
        (Some(actual), Some(wanted)) => {
            assert_eq!(actual.kind.as_str(), wanted.kind, "{name}");
            assert_eq!(
                actual.dependencies.as_slice(),
                wanted.dependencies,
                "{name}"
            );
            assert_eq!(actual.variables, wanted.variables, "{name}");
            assert!(result.assignments.is_empty(), "{name}");
        }
        (None, None) => {
            assert_eq!(
                result.assignments.len(),
                expected.assignments.len(),
                "{name}"
            );
            for ((variable, value), wanted) in result.assignments.iter().zip(&expected.assignments)
            {
                assert_eq!(*variable, wanted.variable, "{name}");
                assert_witness_shape(value, &wanted.value, name);
            }
        }
        _ => panic!("{name}: clash presence differs"),
    }
}

fn assert_witness_shape(actual: &NativeDataWitness, expected: &OracleWitness, name: &str) {
    match (actual, expected) {
        (NativeDataWitness::Concrete(_value), OracleWitness::Concrete { identity }) => {
            assert!(identity.is_array(), "{name}");
        }
        (
            NativeDataWitness::Symbolic(value),
            OracleWitness::Symbolic {
                domain_digest,
                family,
                ordinal,
            },
        ) => {
            assert_eq!(domain_digest.len(), 64, "{name}");
            assert_eq!(family_name(value.family), family, "{name}");
            assert_eq!(value.ordinal, *ordinal, "{name}");
        }
        _ => panic!("{name}: witness kind differs"),
    }
}

fn assert_certificate(
    result: &SemanticSolveResult,
    source: &SemanticDatatypeConstraintComponent,
    compiled: &CompiledSemanticDatatypeConstraintComponent,
    limits: SemanticSolverLimits,
    name: &str,
) {
    if !result.satisfiable {
        return;
    }
    let assignments = result
        .assignments
        .iter()
        .cloned()
        .collect::<BTreeMap<_, _>>();
    assert_eq!(assignments.len(), source.variables.len(), "{name}");
    for fixed in &source.fixed_values {
        assert_eq!(
            assignments[&fixed.variable],
            NativeDataWitness::Concrete(fixed.value.clone()),
            "{name}"
        );
    }
    for equality in &source.equalities {
        assert_eq!(
            assignments[&equality.left], assignments[&equality.right],
            "{name}"
        );
    }
    for inequality in &source.inequalities {
        assert_ne!(
            assignments[&inequality.left], assignments[&inequality.right],
            "{name}"
        );
    }
    for range in &source.ranges {
        let NativeDataWitness::Concrete(identity) = &assignments[&range.variable] else {
            continue;
        };
        let base = &compiled.compiled_ranges[&range.data_range_id];
        let contains = base
            .contains(identity, limits.range_wire, &NeverCancel)
            .unwrap();
        assert_eq!(contains, range.positive, "{name}");
    }
}

const fn family_name(value: NativeDataValueFamily) -> &'static str {
    match value {
        NativeDataValueFamily::Numeric => "numeric",
        NativeDataValueFamily::Boolean => "boolean",
        NativeDataValueFamily::Float => "float",
        NativeDataValueFamily::Double => "double",
        NativeDataValueFamily::String => "string",
        NativeDataValueFamily::HexBinary => "hex-binary",
        NativeDataValueFamily::Base64Binary => "base64-binary",
        NativeDataValueFamily::Uri => "uri",
        NativeDataValueFamily::Xml => "xml",
        NativeDataValueFamily::DateTime => "date-time",
    }
}

struct CancelAfter {
    fail_at: u32,
    polls: Cell<u32>,
}

impl CancelAfter {
    const fn new(fail_at: u32) -> Self {
        Self {
            fail_at,
            polls: Cell::new(0),
        }
    }
}

impl DatatypeControl for CancelAfter {
    fn poll(&self) -> Result<(), DatatypeError> {
        let polls = self.polls.get().saturating_add(1);
        self.polls.set(polls);
        if polls >= self.fail_at {
            Err(DatatypeError::cancelled(
                "semantic solver cancellation test",
            ))
        } else {
            Ok(())
        }
    }
}
