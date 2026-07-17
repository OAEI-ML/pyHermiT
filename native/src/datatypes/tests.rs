use super::*;
use crate::datatypes::value::{tagged_comparison, tagged_identity};
use serde::Deserialize;
use serde_json::{json, Value};

fn payload(
    lexical_form: &str,
    datatype_iri: &str,
    language: Option<&str>,
    identity: Value,
    comparison: Value,
) -> Result<Vec<u8>, DatatypeError> {
    serde_json::to_vec(&json!({
        "comparison": comparison,
        "compatibility": "owl2",
        "data_identity": identity,
        "datatype_iri": datatype_iri,
        "language": language,
        "lexical_form": lexical_form,
        "record": "literal_semantic",
        "schema_version": 1,
    }))
    .map_err(DatatypeError::from)
}

fn semantic(value: &DecodedLiteral) -> Result<&NativeLiteral, DatatypeError> {
    match value {
        DecodedLiteral::Semantic(literal) => Ok(literal),
        DecodedLiteral::Opaque(_) => Err(DatatypeError::invalid(
            "test expected an executable semantic literal",
        )),
    }
}

#[test]
fn arbitrary_precision_rationals_preserve_source_and_compare_exactly(
) -> Result<(), Box<dyn std::error::Error>> {
    let huge = "+123456789abcdef0123456789abcdef0123456789abcdef";
    let encoded = payload(
        "+source-alias",
        "http://www.w3.org/2002/07/owl#rational",
        None,
        json!(["numeric-rational-hex-v1", huge, "+2"]),
        json!(["ordered-numeric-rational-hex-v1", huge, "+2"]),
    )?;
    let decoded = decode_literal_semantic(27, &encoded, DatatypeLimits::default(), &NeverCancel)?;
    let literal = semantic(&decoded)?;
    assert_eq!(literal.source_literal_id, 27);
    assert_eq!(literal.source.lexical_form, "+source-alias");
    assert_eq!(decoded.source_literal_id(), 27);
    assert_eq!(tagged_identity(&literal.data_identity)[1], json!(huge));
    assert_eq!(tagged_comparison(&literal.comparison)[2], json!("+2"));

    let larger = payload(
        "larger",
        "http://www.w3.org/2002/07/owl#rational",
        None,
        json!(["numeric-rational-hex-v1", "+7", "+1"]),
        json!(["ordered-numeric-rational-hex-v1", "+7", "+1"]),
    )?;
    let larger = decode_literal_semantic(28, &larger, DatatypeLimits::default(), &NeverCancel)?;
    assert_eq!(
        literal.comparison.compare(&semantic(&larger)?.comparison)?,
        ComparisonOrder::Greater
    );
    Ok(())
}

#[test]
fn ieee_signed_zero_nan_infinities_and_subnormal_values_are_bit_exact(
) -> Result<(), Box<dyn std::error::Error>> {
    let negative_zero = payload(
        "-0",
        "http://www.w3.org/2001/XMLSchema#float",
        None,
        json!(["ieee-identity-v1", "float32", "80000000"]),
        json!(["ieee-comparison-v1", "float32", "finite", "+0", "+1"]),
    )?;
    let positive_zero = payload(
        "+0",
        "http://www.w3.org/2001/XMLSchema#float",
        None,
        json!(["ieee-identity-v1", "float32", "00000000"]),
        json!(["ieee-comparison-v1", "float32", "finite", "+0", "+1"]),
    )?;
    let negative =
        decode_literal_semantic(0, &negative_zero, DatatypeLimits::default(), &NeverCancel)?;
    let positive =
        decode_literal_semantic(1, &positive_zero, DatatypeLimits::default(), &NeverCancel)?;
    assert_ne!(
        semantic(&negative)?.data_identity,
        semantic(&positive)?.data_identity
    );
    assert_eq!(
        semantic(&negative)?.comparison,
        semantic(&positive)?.comparison
    );

    let nan = payload(
        "NaN",
        "http://www.w3.org/2001/XMLSchema#float",
        None,
        json!(["ieee-identity-v1", "float32", "7fc00000"]),
        json!(["ieee-comparison-v1", "float32", "nan", "+0", "+1"]),
    )?;
    let nan = decode_literal_semantic(2, &nan, DatatypeLimits::default(), &NeverCancel)?;
    assert_eq!(
        semantic(&nan)?
            .comparison
            .compare(&semantic(&positive)?.comparison)?,
        ComparisonOrder::Unordered
    );

    let smallest = payload(
        "smallest-subnormal",
        "http://www.w3.org/2001/XMLSchema#float",
        None,
        json!(["ieee-identity-v1", "float32", "00000001"]),
        json!([
            "ieee-comparison-v1",
            "float32",
            "finite",
            "+1",
            "+20000000000000000000000000000000000000"
        ]),
    )?;
    decode_literal_semantic(3, &smallest, DatatypeLimits::default(), &NeverCancel)?;
    Ok(())
}

#[test]
fn nonnumeric_families_are_disjoint_and_source_spellings_remain_available(
) -> Result<(), Box<dyn std::error::Error>> {
    let cases = [
        (
            "true",
            "http://www.w3.org/2001/XMLSchema#boolean",
            None,
            json!(["boolean", true]),
            json!(["boolean-equality", true]),
        ),
        (
            "colour",
            "http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral",
            Some("en-GB"),
            json!(["plain-string-v1", "colour", "en-gb"]),
            json!(["plain-string-comparison-v1", "colour", "en-gb"]),
        ),
        (
            "0aFF",
            "http://www.w3.org/2001/XMLSchema#hexBinary",
            None,
            json!(["binary-identity-v1", "hexBinary", "0aff"]),
            json!(["binary-comparison-v1", "hexBinary", "0aff"]),
        ),
        (
            "urn:source:spelling",
            "http://www.w3.org/2001/XMLSchema#anyURI",
            None,
            json!(["any-uri-v1", "urn:source:spelling"]),
            json!(["any-uri-comparison-v1", "urn:source:spelling"]),
        ),
        (
            "<a></a>",
            "http://www.w3.org/1999/02/22-rdf-syntax-ns#XMLLiteral",
            None,
            json!(["xml-literal-c14n-v1", "<a></a>"]),
            json!(["xml-literal-comparison-v1", "<a></a>"]),
        ),
    ];
    let mut values = Vec::new();
    for (index, (lexical, datatype, language, identity, comparison)) in
        cases.into_iter().enumerate()
    {
        let source_id = u32::try_from(index)?;
        let encoded = payload(lexical, datatype, language, identity, comparison)?;
        values.push(decode_literal_semantic(
            source_id,
            &encoded,
            DatatypeLimits::default(),
            &NeverCancel,
        )?);
    }
    assert_eq!(
        semantic(&values[1])?.source.language.as_deref(),
        Some("en-GB")
    );
    assert!(values.windows(2).all(|pair| {
        semantic(&pair[0]).ok().map(|value| &value.data_identity)
            != semantic(&pair[1]).ok().map(|value| &value.data_identity)
    }));
    Ok(())
}

#[test]
fn date_time_partial_order_uses_possible_utc_intervals_not_local_timezone(
) -> Result<(), Box<dyn std::error::Error>> {
    let date_time = |source_id, local: &str, offset: Value| -> Result<_, DatatypeError> {
        let encoded = payload(
            "source-date-time",
            "http://www.w3.org/2001/XMLSchema#dateTime",
            None,
            json!(["date-time-identity-v1", local, "+1", offset, false]),
            json!(["date-time-comparison-v1", local, "+1", offset]),
        )?;
        decode_literal_semantic(source_id, &encoded, DatatypeLimits::default(), &NeverCancel)
    };
    let zoned = date_time(0, "+0", json!(0))?;
    let nearby_unzoned = date_time(1, "+0", Value::Null)?;
    let far_unzoned = date_time(2, "+20000", Value::Null)?;
    assert_eq!(
        semantic(&zoned)?
            .comparison
            .compare(&semantic(&nearby_unzoned)?.comparison)?,
        ComparisonOrder::Unordered
    );
    assert_eq!(
        semantic(&zoned)?
            .comparison
            .compare(&semantic(&far_unzoned)?.comparison)?,
        ComparisonOrder::Less
    );
    Ok(())
}

#[test]
fn opaque_payloads_preserve_source_without_inventing_data_identity(
) -> Result<(), Box<dyn std::error::Error>> {
    let encoded = serde_json::to_vec(&json!({
        "compatibility": "owl2",
        "datatype_iri": "urn:test:opaque",
        "language": null,
        "lexical_form": "unparsed source",
        "opaque_identity": ["opaque-source-literal-v1", "unparsed source", "urn:test:opaque", null],
        "record": "opaque_literal_semantic",
        "schema_version": 1,
    }))?;
    let decoded = decode_literal_semantic(91, &encoded, DatatypeLimits::default(), &NeverCancel)?;
    assert_eq!(decoded.source_literal_id(), 91);
    assert!(matches!(decoded, DecodedLiteral::Opaque(_)));
    Ok(())
}

#[derive(Debug)]
struct CancelImmediately;

impl DatatypeControl for CancelImmediately {
    fn poll(&self) -> Result<(), DatatypeError> {
        Err(DatatypeError::cancelled("test cancellation"))
    }
}

#[test]
fn hostile_noncanonical_mismatched_oversize_and_cancelled_inputs_fail_safely(
) -> Result<(), Box<dyn std::error::Error>> {
    let mismatched = payload(
        "1",
        "http://www.w3.org/2001/XMLSchema#integer",
        None,
        json!(["numeric-rational-hex-v1", "+1", "+1"]),
        json!(["ordered-numeric-rational-hex-v1", "+2", "+1"]),
    )?;
    assert_eq!(
        decode_literal_semantic(0, &mismatched, DatatypeLimits::default(), &NeverCancel)
            .err()
            .map(|error| error.kind),
        Some(DatatypeErrorKind::Invalid)
    );

    let noncanonical_number = payload(
        "1",
        "http://www.w3.org/2001/XMLSchema#integer",
        None,
        json!(["numeric-rational-hex-v1", "+01", "+1"]),
        json!(["ordered-numeric-rational-hex-v1", "+01", "+1"]),
    )?;
    assert_eq!(
        decode_literal_semantic(
            0,
            &noncanonical_number,
            DatatypeLimits::default(),
            &NeverCancel,
        )
        .err()
        .map(|error| error.kind),
        Some(DatatypeErrorKind::Invalid)
    );

    let limits = DatatypeLimits {
        max_payload_bytes: 2,
        ..DatatypeLimits::default()
    };
    assert_eq!(
        decode_literal_semantic(0, &mismatched, limits, &NeverCancel)
            .err()
            .map(|error| error.kind),
        Some(DatatypeErrorKind::Resource)
    );
    assert_eq!(
        decode_literal_semantic(
            0,
            &mismatched,
            DatatypeLimits::default(),
            &CancelImmediately,
        )
        .err()
        .map(|error| error.kind),
        Some(DatatypeErrorKind::Cancelled)
    );

    let mut spaced = mismatched;
    spaced.insert(0, b' ');
    assert_eq!(
        decode_literal_semantic(0, &spaced, DatatypeLimits::default(), &NeverCancel)
            .err()
            .map(|error| error.kind),
        Some(DatatypeErrorKind::Invalid)
    );
    Ok(())
}

#[derive(Debug, Deserialize)]
struct ValueFixture {
    schema_version: u32,
    literal_count: usize,
    pair_count: usize,
    literals: Vec<LiteralFixture>,
    pairs: Vec<PairFixture>,
}

#[derive(Debug, Deserialize)]
struct LiteralFixture {
    source_literal_id: u32,
    payload_json: String,
}

#[derive(Debug, Deserialize)]
struct PairFixture {
    left: usize,
    right: usize,
    identity_equal: bool,
    comparison: String,
}

#[test]
fn shared_python_value_identity_and_comparison_matrix_matches_exactly(
) -> Result<(), Box<dyn std::error::Error>> {
    let fixture: ValueFixture = serde_json::from_str(include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../tests/data/datatypes/wpr3-native-values-v1.json"
    )))?;
    assert_eq!(fixture.schema_version, 1);
    assert_eq!(fixture.literal_count, fixture.literals.len());
    assert_eq!(fixture.pair_count, fixture.pairs.len());
    assert_eq!(
        fixture.pair_count,
        fixture.literal_count * fixture.literal_count
    );
    let values = fixture
        .literals
        .iter()
        .map(|literal| {
            decode_literal_semantic(
                literal.source_literal_id,
                literal.payload_json.as_bytes(),
                DatatypeLimits::default(),
                &NeverCancel,
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    for pair in fixture.pairs {
        let left = semantic(
            values
                .get(pair.left)
                .ok_or_else(|| DatatypeError::invalid("fixture left literal is absent"))?,
        )?;
        let right = semantic(
            values
                .get(pair.right)
                .ok_or_else(|| DatatypeError::invalid("fixture right literal is absent"))?,
        )?;
        assert_eq!(
            left.data_identity == right.data_identity,
            pair.identity_equal,
            "identity pair ({}, {})",
            pair.left,
            pair.right,
        );
        let result = left.comparison.compare(&right.comparison);
        let observed = match result {
            Ok(ComparisonOrder::Less) => "less",
            Ok(ComparisonOrder::Equal) => "equal",
            Ok(ComparisonOrder::Greater) => "greater",
            Ok(ComparisonOrder::Unordered) => "unordered",
            Err(_) => "error",
        };
        assert_eq!(
            observed, pair.comparison,
            "comparison pair ({}, {})",
            pair.left, pair.right,
        );
    }
    Ok(())
}
