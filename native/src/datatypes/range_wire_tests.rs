// SPDX-License-Identifier: LGPL-3.0-or-later

#![allow(
    clippy::expect_used,
    clippy::field_reassign_with_default,
    clippy::panic,
    clippy::unwrap_used
)]

use std::cell::Cell;
use std::collections::BTreeSet;

use num_bigint::BigUint;
use serde::Deserialize;
use serde_json::{json, Value};

use super::*;
use crate::datatypes::{DatatypeErrorKind, NeverCancel};

const ORACLE: &str = include_str!("range_wire_oracle_v1.json");

#[derive(Deserialize)]
struct Oracle {
    literal_payloads: Vec<OracleLiteral>,
    model_json: String,
    ranges: Vec<OracleRange>,
    schema_version: u32,
}

#[derive(Deserialize)]
struct OracleLiteral {
    label: String,
    payload_json: String,
}

#[derive(Deserialize)]
struct OracleRange {
    cardinality: String,
    checks: Vec<bool>,
    empty: Value,
    label: String,
    range_id: u32,
}

#[test]
fn python_oracle_matches_every_wire_kind_facet_and_family() {
    let fixture: Oracle = serde_json::from_str(ORACLE).expect("oracle JSON");
    assert_eq!(fixture.schema_version, 1);
    let limits = RangeWireLimits::default();
    let model = decode_datatype_range_model(
        fixture.model_json.as_bytes(),
        limits,
        OpaqueRangePolicy::Preserve,
        &NeverCancel,
    )
    .expect("canonical model");
    assert_eq!(model.range_count(), fixture.ranges.len());
    assert_eq!(model.definition_count(), 2);
    assert_eq!(model.opaque_range_ids(), &[17]);

    let identities: Vec<_> = fixture
        .literal_payloads
        .iter()
        .enumerate()
        .map(|(index, literal)| {
            let source_id = u32::try_from(index).expect("small oracle");
            match decode_literal_semantic(
                source_id,
                literal.payload_json.as_bytes(),
                limits.values,
                &NeverCancel,
            )
            .unwrap_or_else(|error| panic!("literal {} failed: {error}", literal.label))
            {
                DecodedLiteral::Semantic(value) => value.data_identity,
                DecodedLiteral::Opaque(_) => panic!("oracle literal cannot be opaque"),
            }
        })
        .collect();

    for expected in &fixture.ranges {
        if expected.cardinality == "unsupported" {
            let error = model
                .compile_range(expected.range_id, &NeverCancel)
                .expect_err("opaque range must fail closed when evaluated");
            assert_eq!(error.kind, DatatypeErrorKind::Invalid);
            continue;
        }
        let range = model
            .compile_range(expected.range_id, &NeverCancel)
            .unwrap_or_else(|error| panic!("range {} failed: {error}", expected.label));
        assert_eq!(
            expected.checks.len(),
            identities.len(),
            "{}",
            expected.label
        );
        for ((identity, wanted), literal) in identities
            .iter()
            .zip(&expected.checks)
            .zip(&fixture.literal_payloads)
        {
            assert_eq!(
                range.contains(identity, limits, &NeverCancel).unwrap(),
                *wanted,
                "{} / {}",
                expected.label,
                literal.label
            );
        }
        let wanted_empty = expected.empty.as_bool().expect("supported emptiness bool");
        assert_eq!(
            range.is_empty_exact(limits, &NeverCancel).unwrap(),
            wanted_empty,
            "{}",
            expected.label
        );
        let wanted_cardinality = match expected.cardinality.as_str() {
            "infinite" => Cardinality::Infinite,
            value => Cardinality::Finite(
                value
                    .parse::<BigUint>()
                    .unwrap_or_else(|_| panic!("bad cardinality for {}", expected.label)),
            ),
        };
        assert_eq!(
            range.cardinality(limits, &NeverCancel).unwrap(),
            wanted_cardinality,
            "{}",
            expected.label
        );
    }
}

#[test]
fn opaque_policy_preserves_ids_but_rejects_evaluation() {
    let fixture: Oracle = serde_json::from_str(ORACLE).unwrap();
    let limits = RangeWireLimits::default();
    let rejected = decode_datatype_range_model(
        fixture.model_json.as_bytes(),
        limits,
        OpaqueRangePolicy::Reject,
        &NeverCancel,
    )
    .unwrap_err();
    assert_eq!(rejected.kind, DatatypeErrorKind::Invalid);

    let preserved = decode_datatype_range_model(
        fixture.model_json.as_bytes(),
        limits,
        OpaqueRangePolicy::Preserve,
        &NeverCancel,
    )
    .unwrap();
    assert_eq!(preserved.opaque_range_ids(), &[17]);
    assert!(preserved.compile_range(0, &NeverCancel).is_ok());
    assert!(preserved.compile_range(17, &NeverCancel).is_err());
}

#[test]
fn public_algebra_seam_keeps_solver_consumers_out_of_private_dnf() {
    let fixture: Oracle = serde_json::from_str(ORACLE).unwrap();
    let limits = RangeWireLimits::default();
    let model = decode_datatype_range_model(
        fixture.model_json.as_bytes(),
        limits,
        OpaqueRangePolicy::Preserve,
        &NeverCancel,
    )
    .unwrap();
    let boolean = model.compile_range(0, &NeverCancel).unwrap();
    let not_boolean = boolean.complement(limits, &NeverCancel).unwrap();
    assert!(boolean
        .intersection(&not_boolean, limits, &NeverCancel)
        .unwrap()
        .is_empty_exact(limits, &NeverCancel)
        .unwrap());
    assert_eq!(
        boolean
            .enumerate_identities(limits, &NeverCancel)
            .unwrap()
            .len(),
        2
    );
    assert!(boolean
        .cardinality_at_least(2, limits, &NeverCancel)
        .unwrap());
    assert!(!boolean
        .cardinality_at_least(3, limits, &NeverCancel)
        .unwrap());
    assert!(NativeDataRange::all()
        .cardinality_at_least(1_000_000, limits, &NeverCancel)
        .unwrap());
    assert!(NativeDataRange::empty()
        .is_empty_exact(limits, &NeverCancel)
        .unwrap());

    let first = boolean
        .witness(&BTreeSet::new(), limits, &NeverCancel)
        .unwrap();
    assert_eq!(
        first,
        NativeDataWitness::Concrete(DataIdentity::Boolean(false))
    );
    let second = boolean
        .witness(&std::iter::once(first).collect(), limits, &NeverCancel)
        .unwrap();
    assert_eq!(
        second,
        NativeDataWitness::Concrete(DataIdentity::Boolean(true))
    );

    let nonrational_real = canonical_intersection(vec![
        canonical_datatype_atom(OWL_REAL),
        canonical_complement(canonical_datatype_atom(OWL_RATIONAL)),
    ]);
    let nonrational_real = decode_data_range_semantic(
        &serde_json::to_vec(&nonrational_real).unwrap(),
        limits,
        OpaqueRangePolicy::Reject,
        &NeverCancel,
    )
    .unwrap();
    let symbolic = nonrational_real
        .witness(&BTreeSet::new(), limits, &NeverCancel)
        .unwrap();
    let NativeDataWitness::Symbolic(first_symbolic) = symbolic.clone() else {
        panic!("owl:real minus owl:rational requires a symbolic witness");
    };
    assert_eq!(first_symbolic.family, NativeDataValueFamily::Numeric);
    assert_eq!(first_symbolic.ordinal, 0);
    let next = nonrational_real
        .witness(&std::iter::once(symbolic).collect(), limits, &NeverCancel)
        .unwrap();
    let NativeDataWitness::Symbolic(next_symbolic) = next else {
        panic!("second nonrational witness must remain symbolic");
    };
    assert_eq!(next_symbolic.domain_digest, first_symbolic.domain_digest);
    assert_eq!(next_symbolic.ordinal, 1);
}

#[test]
fn decoder_rejects_noncanonical_unknown_unsorted_and_dangling_payloads() {
    let fixture: Oracle = serde_json::from_str(ORACLE).unwrap();
    let limits = RangeWireLimits::default();
    let prefixed = format!(" {}", fixture.model_json);
    assert!(decode_datatype_range_model(
        prefixed.as_bytes(),
        limits,
        OpaqueRangePolicy::Preserve,
        &NeverCancel,
    )
    .is_err());

    let mut unknown: Value = serde_json::from_str(&fixture.model_json).unwrap();
    unknown
        .as_object_mut()
        .unwrap()
        .insert("unknown".to_owned(), Value::Bool(true));
    let unknown = serde_json::to_vec(&unknown).unwrap();
    assert!(decode_datatype_range_model(
        &unknown,
        limits,
        OpaqueRangePolicy::Preserve,
        &NeverCancel,
    )
    .is_err());

    let mut unsorted: Value = serde_json::from_str(&fixture.model_json).unwrap();
    unsorted["data_ranges"][9]["operands"]
        .as_array_mut()
        .unwrap()
        .reverse();
    let unsorted = serde_json::to_vec(&unsorted).unwrap();
    assert!(decode_datatype_range_model(
        &unsorted,
        limits,
        OpaqueRangePolicy::Preserve,
        &NeverCancel,
    )
    .is_err());

    let dangling = canonical_datatype_atom("urn:pyhermit:test:dangling");
    let error = decode_data_range_semantic(
        &serde_json::to_vec(&dangling).unwrap(),
        limits,
        OpaqueRangePolicy::Reject,
        &NeverCancel,
    )
    .unwrap_err();
    assert_eq!(error.kind, DatatypeErrorKind::Invalid);
}

#[test]
fn decoder_enforces_payload_depth_size_nodes_and_cancellation() {
    let fixture: Oracle = serde_json::from_str(ORACLE).unwrap();
    let parsed_model: Value = serde_json::from_str(&fixture.model_json).unwrap();
    let shallow_restriction = serde_json::to_vec(&parsed_model["data_ranges"][1]).unwrap();
    let shallow_limits = RangeWireLimits {
        max_data_range_depth: 1,
        ..RangeWireLimits::default()
    };
    assert!(decode_data_range_semantic(
        &shallow_restriction,
        shallow_limits,
        OpaqueRangePolicy::Reject,
        &NeverCancel,
    )
    .is_ok());

    let mut expression = canonical_datatype_atom(XSD_BOOLEAN);
    for _ in 0..5 {
        expression = canonical_complement(expression);
    }
    let bytes = serde_json::to_vec(&expression).unwrap();
    let mut limits = RangeWireLimits::default();
    limits.max_data_range_depth = 3;
    let error = decode_data_range_semantic(&bytes, limits, OpaqueRangePolicy::Reject, &NeverCancel)
        .unwrap_err();
    assert_eq!(error.kind, DatatypeErrorKind::Resource);
    assert_eq!(error.limit, Some("max_data_range_depth"));

    let mut size_limits = RangeWireLimits::default();
    size_limits.max_payload_bytes =
        u64::try_from(fixture.model_json.len() - 1).expect("oracle length");
    let error = decode_datatype_range_model(
        fixture.model_json.as_bytes(),
        size_limits,
        OpaqueRangePolicy::Preserve,
        &NeverCancel,
    )
    .unwrap_err();
    assert_eq!(error.limit, Some("max_payload_bytes"));

    let mut node_limits = RangeWireLimits::default();
    node_limits.max_data_range_nodes = 1;
    let error = decode_datatype_range_model(
        fixture.model_json.as_bytes(),
        node_limits,
        OpaqueRangePolicy::Preserve,
        &NeverCancel,
    )
    .unwrap_err();
    assert_eq!(error.limit, Some("max_data_range_nodes"));

    let cancellation = CancelImmediately(Cell::new(0));
    let error = decode_datatype_range_model(
        fixture.model_json.as_bytes(),
        RangeWireLimits::default(),
        OpaqueRangePolicy::Preserve,
        &cancellation,
    )
    .unwrap_err();
    assert_eq!(error.kind, DatatypeErrorKind::Cancelled);
    assert!(cancellation.0.get() > 0);
}

#[test]
fn decoder_rejects_named_definition_cycles() {
    let fixture: Oracle = serde_json::from_str(ORACLE).unwrap();
    let mut model: Value = serde_json::from_str(&fixture.model_json).unwrap();
    model["definitions"][0]["data_range"] = canonical_datatype_atom("urn:pyhermit:oracle:selected");
    let bytes = serde_json::to_vec(&model).unwrap();
    let error = decode_datatype_range_model(
        &bytes,
        RangeWireLimits::default(),
        OpaqueRangePolicy::Preserve,
        &NeverCancel,
    )
    .unwrap_err();
    assert!(error.message.contains("acyclic"));
}

#[test]
fn language_tag_validation_is_structural_and_canonical() {
    assert!(is_valid_language_tag("en-gb"));
    assert!(is_valid_language_tag("x-private"));
    assert!(!is_valid_language_tag("EN-gb"));
    assert!(!is_valid_language_tag("en-a"));
    assert!(!is_valid_language_tag("en-variant-variant"));
}

fn canonical_datatype_atom(iri: &str) -> Value {
    json!({
        "datatype_iri": iri,
        "facets": [],
        "kind": "datatype",
        "operands": [],
        "record": "data_range_semantic",
        "schema_version": 1,
        "values": [],
    })
}

fn canonical_complement(operand: Value) -> Value {
    json!({
        "datatype_iri": null,
        "facets": [],
        "kind": "complement",
        "operands": [operand],
        "record": "data_range_semantic",
        "schema_version": 1,
        "values": [],
    })
}

fn canonical_intersection(mut operands: Vec<Value>) -> Value {
    operands.sort_by_key(|value| serde_json::to_vec(value).unwrap());
    json!({
        "datatype_iri": null,
        "facets": [],
        "kind": "intersection",
        "operands": operands,
        "record": "data_range_semantic",
        "schema_version": 1,
        "values": [],
    })
}

struct CancelImmediately(Cell<u64>);

impl DatatypeControl for CancelImmediately {
    fn poll(&self) -> Result<(), DatatypeError> {
        self.0.set(self.0.get() + 1);
        Err(DatatypeError::cancelled("oracle cancellation"))
    }
}
