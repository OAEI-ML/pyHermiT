//! Canonical semantic-value wire decoder and exact comparison model.
// SPDX-License-Identifier: LGPL-3.0-or-later

use std::cmp::Ordering;
use std::error::Error;
use std::fmt;

use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Signed, Zero};
use serde::{Deserialize, Serialize};
use serde_json::Value;

const SCHEMA_VERSION: u32 = 1;
const POLL_STRIDE: usize = 1_024;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DatatypeErrorKind {
    Invalid,
    Resource,
    Cancelled,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DatatypeError {
    pub kind: DatatypeErrorKind,
    pub message: String,
    pub limit: Option<&'static str>,
    pub observed: Option<u64>,
    pub allowed: Option<u64>,
}

impl DatatypeError {
    #[must_use]
    pub fn invalid(message: impl Into<String>) -> Self {
        Self {
            kind: DatatypeErrorKind::Invalid,
            message: message.into(),
            limit: None,
            observed: None,
            allowed: None,
        }
    }

    #[must_use]
    pub fn resource(limit: &'static str, observed: u64, allowed: u64) -> Self {
        Self {
            kind: DatatypeErrorKind::Resource,
            message: format!("native datatype resource limit exceeded: {limit}"),
            limit: Some(limit),
            observed: Some(observed),
            allowed: Some(allowed),
        }
    }

    #[must_use]
    pub fn cancelled(message: impl Into<String>) -> Self {
        Self {
            kind: DatatypeErrorKind::Cancelled,
            message: message.into(),
            limit: None,
            observed: None,
            allowed: None,
        }
    }
}

impl fmt::Display for DatatypeError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.message)
    }
}

impl Error for DatatypeError {}

impl From<serde_json::Error> for DatatypeError {
    fn from(error: serde_json::Error) -> Self {
        Self::invalid(format!("invalid datatype semantic JSON: {error}"))
    }
}

pub trait DatatypeControl {
    fn poll(&self) -> Result<(), DatatypeError>;

    fn observe_memory(&self, _bytes: u64) -> Result<(), DatatypeError> {
        self.poll()
    }
}

#[derive(Clone, Copy, Debug, Default)]
pub struct NeverCancel;

impl DatatypeControl for NeverCancel {
    fn poll(&self) -> Result<(), DatatypeError> {
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct DatatypeLimits {
    pub max_payload_bytes: u64,
    pub max_numeric_hex_digits: u64,
    pub max_text_characters: u64,
    pub max_binary_bytes: u64,
}

impl Default for DatatypeLimits {
    fn default() -> Self {
        Self {
            max_payload_bytes: 16_000_000,
            // Four hexadecimal bits per digit; this is deliberately aligned with
            // Python's 100,000 decimal-digit hostile-input order of magnitude.
            max_numeric_hex_digits: 100_000,
            max_text_characters: 1_000_000,
            max_binary_bytes: 1_000_000,
        }
    }
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ExactRational {
    numerator: BigInt,
    denominator: BigInt,
}

impl ExactRational {
    pub fn new(numerator: BigInt, denominator: BigInt) -> Result<Self, DatatypeError> {
        if denominator.is_zero() {
            return Err(DatatypeError::invalid(
                "exact rational denominator must be nonzero",
            ));
        }
        let (mut numerator, mut denominator) = (numerator, denominator);
        if denominator.is_negative() {
            numerator = -numerator;
            denominator = -denominator;
        }
        let divisor = numerator.gcd(&denominator);
        Ok(Self {
            numerator: numerator / &divisor,
            denominator: denominator / divisor,
        })
    }

    pub fn from_tokens(
        numerator: &str,
        denominator: &str,
        limits: DatatypeLimits,
        control: &impl DatatypeControl,
    ) -> Result<Self, DatatypeError> {
        let numerator_value = parse_integer_token(numerator, limits, control)?;
        let denominator_value = parse_integer_token(denominator, limits, control)?;
        let result = Self::new(numerator_value, denominator_value)?;
        if result.numerator_token() != numerator || result.denominator_token() != denominator {
            return Err(DatatypeError::invalid(
                "exact rational tokens are not reduced canonical signed hexadecimal",
            ));
        }
        Ok(result)
    }

    #[must_use]
    pub fn numerator_token(&self) -> String {
        integer_token(&self.numerator)
    }

    #[must_use]
    pub fn denominator_token(&self) -> String {
        integer_token(&self.denominator)
    }

    #[must_use]
    pub fn compare(&self, other: &Self) -> Ordering {
        (&self.numerator * &other.denominator).cmp(&(&other.numerator * &self.denominator))
    }

    #[must_use]
    pub fn subtract_integer(&self, value: i64) -> Self {
        Self {
            numerator: &self.numerator - BigInt::from(value) * &self.denominator,
            denominator: self.denominator.clone(),
        }
    }

    #[must_use]
    fn plus_or_minus_integer(&self, value: i64) -> Self {
        Self {
            numerator: &self.numerator + BigInt::from(value) * &self.denominator,
            denominator: self.denominator.clone(),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum IEEEFormat {
    Float32,
    Float64,
}

impl IEEEFormat {
    #[must_use]
    const fn width(self) -> u32 {
        match self {
            Self::Float32 => 32,
            Self::Float64 => 64,
        }
    }

    #[must_use]
    const fn fraction_bits(self) -> u32 {
        match self {
            Self::Float32 => 23,
            Self::Float64 => 52,
        }
    }

    #[must_use]
    const fn exponent_bits(self) -> u32 {
        match self {
            Self::Float32 => 8,
            Self::Float64 => 11,
        }
    }

    #[must_use]
    const fn bias(self) -> i32 {
        match self {
            Self::Float32 => 127,
            Self::Float64 => 1_023,
        }
    }

    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Float32 => "float32",
            Self::Float64 => "float64",
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum IEEECategory {
    Finite,
    NegativeInfinity,
    PositiveInfinity,
    NaN,
}

impl IEEECategory {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Finite => "finite",
            Self::NegativeInfinity => "negative-infinity",
            Self::PositiveInfinity => "positive-infinity",
            Self::NaN => "nan",
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum BinaryKind {
    Hex,
    Base64,
}

impl BinaryKind {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Hex => "hexBinary",
            Self::Base64 => "base64Binary",
        }
    }
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum DataIdentity {
    Numeric(ExactRational),
    Boolean(bool),
    IEEE {
        format: IEEEFormat,
        bits: u64,
    },
    String {
        text: String,
        language: Option<String>,
    },
    Binary {
        kind: BinaryKind,
        octets: Vec<u8>,
    },
    Uri(String),
    Xml(String),
    DateTime {
        local: ExactRational,
        timezone_offset_minutes: Option<i16>,
        hermit_end_of_day: bool,
    },
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum ComparisonValue {
    Numeric(ExactRational),
    Boolean(bool),
    IEEE {
        format: IEEEFormat,
        category: IEEECategory,
        value: ExactRational,
    },
    String {
        text: String,
        language: Option<String>,
    },
    Binary {
        kind: BinaryKind,
        octets: Vec<u8>,
    },
    Uri(String),
    Xml(String),
    DateTime {
        local: ExactRational,
        timezone_offset_minutes: Option<i16>,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ComparisonOrder {
    Less,
    Equal,
    Greater,
    Unordered,
}

impl ComparisonValue {
    pub fn compare(&self, other: &Self) -> Result<ComparisonOrder, DatatypeError> {
        match (self, other) {
            (Self::Numeric(left), Self::Numeric(right)) => Ok(order(left.compare(right))),
            (Self::Boolean(left), Self::Boolean(right)) => Ok(equality_order(left == right)),
            (
                Self::IEEE {
                    format: left_format,
                    category: left_category,
                    value: left_value,
                },
                Self::IEEE {
                    format: right_format,
                    category: right_category,
                    value: right_value,
                },
            ) => compare_ieee(
                *left_format,
                *left_category,
                left_value,
                *right_format,
                *right_category,
                right_value,
            ),
            (
                Self::String {
                    text: left_text,
                    language: left_language,
                },
                Self::String {
                    text: right_text,
                    language: right_language,
                },
            ) => Ok(equality_order(
                left_text == right_text && left_language == right_language,
            )),
            (
                Self::Binary {
                    kind: left_kind,
                    octets: left_octets,
                },
                Self::Binary {
                    kind: right_kind,
                    octets: right_octets,
                },
            ) => Ok(equality_order(
                left_kind == right_kind && left_octets == right_octets,
            )),
            (Self::Uri(left), Self::Uri(right)) | (Self::Xml(left), Self::Xml(right)) => {
                Ok(equality_order(left == right))
            }
            (
                Self::DateTime {
                    local: left_local,
                    timezone_offset_minutes: left_offset,
                },
                Self::DateTime {
                    local: right_local,
                    timezone_offset_minutes: right_offset,
                },
            ) => Ok(compare_date_time(
                left_local,
                *left_offset,
                right_local,
                *right_offset,
            )),
            _ => Err(DatatypeError::invalid(
                "comparison values belong to different primitive families",
            )),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SourceLiteral {
    pub lexical_form: String,
    pub datatype_iri: String,
    pub language: Option<String>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NativeLiteral {
    pub source_literal_id: u32,
    pub source: SourceLiteral,
    pub data_identity: DataIdentity,
    pub comparison: ComparisonValue,
    pub compatibility: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct OpaqueLiteral {
    pub source_literal_id: u32,
    pub source: SourceLiteral,
    pub compatibility: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum DecodedLiteral {
    Semantic(NativeLiteral),
    Opaque(OpaqueLiteral),
}

impl DecodedLiteral {
    #[must_use]
    pub const fn source_literal_id(&self) -> u32 {
        match self {
            Self::Semantic(value) => value.source_literal_id,
            Self::Opaque(value) => value.source_literal_id,
        }
    }
}

#[derive(Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct LiteralWire {
    comparison: Vec<Value>,
    compatibility: String,
    data_identity: Vec<Value>,
    datatype_iri: String,
    language: Option<String>,
    lexical_form: String,
    record: String,
    schema_version: u32,
}

#[derive(Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct OpaqueLiteralWire {
    compatibility: String,
    datatype_iri: String,
    language: Option<String>,
    lexical_form: String,
    opaque_identity: Vec<Value>,
    record: String,
    schema_version: u32,
}

pub fn decode_literal_semantic(
    source_literal_id: u32,
    bytes: &[u8],
    limits: DatatypeLimits,
    control: &impl DatatypeControl,
) -> Result<DecodedLiteral, DatatypeError> {
    control.poll()?;
    let length = u64::try_from(bytes.len()).unwrap_or(u64::MAX);
    if length > limits.max_payload_bytes {
        return Err(DatatypeError::resource(
            "max_payload_bytes",
            length,
            limits.max_payload_bytes,
        ));
    }
    control.observe_memory(length)?;
    let value: Value = serde_json::from_slice(bytes)?;
    let record = value
        .get("record")
        .and_then(Value::as_str)
        .ok_or_else(|| DatatypeError::invalid("datatype payload has no string record tag"))?;
    let decoded = match record {
        "literal_semantic" => {
            let wire: LiteralWire = serde_json::from_value(value)?;
            require_canonical(bytes, &wire)?;
            decode_semantic_wire(source_literal_id, wire, limits, control)?
        }
        "opaque_literal_semantic" => {
            let wire: OpaqueLiteralWire = serde_json::from_value(value)?;
            require_canonical(bytes, &wire)?;
            decode_opaque_wire(source_literal_id, wire, limits, control)?
        }
        _ => {
            return Err(DatatypeError::invalid(
                "unknown datatype payload record tag",
            ))
        }
    };
    control.poll()?;
    Ok(decoded)
}

fn require_canonical<T: Serialize>(bytes: &[u8], wire: &T) -> Result<(), DatatypeError> {
    let canonical = serde_json::to_vec(wire)?;
    if canonical != bytes {
        return Err(DatatypeError::invalid(
            "datatype payload is not canonical JSON",
        ));
    }
    Ok(())
}

fn decode_semantic_wire(
    source_literal_id: u32,
    wire: LiteralWire,
    limits: DatatypeLimits,
    control: &impl DatatypeControl,
) -> Result<DecodedLiteral, DatatypeError> {
    if wire.record != "literal_semantic" || wire.schema_version != SCHEMA_VERSION {
        return Err(DatatypeError::invalid(
            "unsupported literal semantic record or schema version",
        ));
    }
    validate_source(
        &wire.lexical_form,
        &wire.datatype_iri,
        wire.language.as_deref(),
        limits,
    )?;
    validate_compatibility(&wire.compatibility)?;
    let identity = decode_identity(&wire.data_identity, limits, control)?;
    let comparison = decode_comparison(&wire.comparison, limits, control)?;
    require_matching_pair(&identity, &comparison)?;
    Ok(DecodedLiteral::Semantic(NativeLiteral {
        source_literal_id,
        source: SourceLiteral {
            lexical_form: wire.lexical_form,
            datatype_iri: wire.datatype_iri,
            language: wire.language,
        },
        data_identity: identity,
        comparison,
        compatibility: wire.compatibility,
    }))
}

fn decode_opaque_wire(
    source_literal_id: u32,
    wire: OpaqueLiteralWire,
    limits: DatatypeLimits,
    _control: &impl DatatypeControl,
) -> Result<DecodedLiteral, DatatypeError> {
    if wire.record != "opaque_literal_semantic" || wire.schema_version != SCHEMA_VERSION {
        return Err(DatatypeError::invalid(
            "unsupported opaque literal record or schema version",
        ));
    }
    validate_source(
        &wire.lexical_form,
        &wire.datatype_iri,
        wire.language.as_deref(),
        limits,
    )?;
    validate_compatibility(&wire.compatibility)?;
    let expected = vec![
        Value::String("opaque-source-literal-v1".to_owned()),
        Value::String(wire.lexical_form.clone()),
        Value::String(wire.datatype_iri.clone()),
        wire.language.clone().map_or(Value::Null, Value::String),
    ];
    if wire.opaque_identity != expected {
        return Err(DatatypeError::invalid(
            "opaque literal identity does not preserve its exact source",
        ));
    }
    Ok(DecodedLiteral::Opaque(OpaqueLiteral {
        source_literal_id,
        source: SourceLiteral {
            lexical_form: wire.lexical_form,
            datatype_iri: wire.datatype_iri,
            language: wire.language,
        },
        compatibility: wire.compatibility,
    }))
}

fn validate_source(
    lexical_form: &str,
    datatype_iri: &str,
    language: Option<&str>,
    limits: DatatypeLimits,
) -> Result<(), DatatypeError> {
    if datatype_iri.is_empty() {
        return Err(DatatypeError::invalid(
            "literal datatype IRI must be nonempty",
        ));
    }
    if language == Some("") {
        return Err(DatatypeError::invalid(
            "literal language must be nonempty when present",
        ));
    }
    let observed = u64::try_from(lexical_form.chars().count()).unwrap_or(u64::MAX);
    if observed > limits.max_text_characters {
        return Err(DatatypeError::resource(
            "max_text_characters",
            observed,
            limits.max_text_characters,
        ));
    }
    Ok(())
}

fn validate_compatibility(value: &str) -> Result<(), DatatypeError> {
    if matches!(value, "owl2" | "hermit-37ec30a") {
        Ok(())
    } else {
        Err(DatatypeError::invalid(
            "literal payload uses an unknown lexical compatibility policy",
        ))
    }
}

fn decode_identity(
    fields: &[Value],
    limits: DatatypeLimits,
    control: &impl DatatypeControl,
) -> Result<DataIdentity, DatatypeError> {
    let tag = tag(fields, "data identity")?;
    match tag {
        "numeric-rational-hex-v1" if fields.len() == 3 => Ok(DataIdentity::Numeric(
            rational_fields(fields, limits, control)?,
        )),
        "boolean" if fields.len() == 2 => Ok(DataIdentity::Boolean(boolean(&fields[1])?)),
        "ieee-identity-v1" if fields.len() == 3 => {
            let format = ieee_format(string(&fields[1], "IEEE format")?)?;
            let bits = decode_ieee_bits(string(&fields[2], "IEEE bits")?, format)?;
            Ok(DataIdentity::IEEE { format, bits })
        }
        "plain-string-v1" if fields.len() == 3 => Ok(DataIdentity::String {
            text: bounded_text(&fields[1], "string value", limits)?,
            language: optional_text(&fields[2], "string language", limits)?,
        }),
        "binary-identity-v1" if fields.len() == 3 => Ok(DataIdentity::Binary {
            kind: binary_kind(string(&fields[1], "binary kind")?)?,
            octets: decode_binary(string(&fields[2], "binary octets")?, limits, control)?,
        }),
        "any-uri-v1" if fields.len() == 2 => Ok(DataIdentity::Uri(bounded_text(
            &fields[1],
            "URI value",
            limits,
        )?)),
        "xml-literal-c14n-v1" if fields.len() == 2 => Ok(DataIdentity::Xml(bounded_text(
            &fields[1],
            "canonical XML",
            limits,
        )?)),
        "date-time-identity-v1" if fields.len() == 5 => Ok(DataIdentity::DateTime {
            local: rational_fields(fields, limits, control)?,
            timezone_offset_minutes: optional_offset(&fields[3])?,
            hermit_end_of_day: boolean(&fields[4])?,
        }),
        _ => Err(DatatypeError::invalid(
            "unknown or malformed data identity tag",
        )),
    }
}

fn decode_comparison(
    fields: &[Value],
    limits: DatatypeLimits,
    control: &impl DatatypeControl,
) -> Result<ComparisonValue, DatatypeError> {
    let tag = tag(fields, "comparison")?;
    match tag {
        "ordered-numeric-rational-hex-v1" if fields.len() == 3 => Ok(ComparisonValue::Numeric(
            rational_fields(fields, limits, control)?,
        )),
        "boolean-equality" if fields.len() == 2 => {
            Ok(ComparisonValue::Boolean(boolean(&fields[1])?))
        }
        "ieee-comparison-v1" if fields.len() == 5 => {
            let format = ieee_format(string(&fields[1], "IEEE comparison format")?)?;
            let category = ieee_category(string(&fields[2], "IEEE category")?)?;
            let value = ExactRational::from_tokens(
                string(&fields[3], "IEEE numerator")?,
                string(&fields[4], "IEEE denominator")?,
                limits,
                control,
            )?;
            if category != IEEECategory::Finite
                && value != ExactRational::new(BigInt::zero(), BigInt::one())?
            {
                return Err(DatatypeError::invalid(
                    "non-finite IEEE comparison carries a rational value",
                ));
            }
            Ok(ComparisonValue::IEEE {
                format,
                category,
                value,
            })
        }
        "plain-string-comparison-v1" if fields.len() == 3 => Ok(ComparisonValue::String {
            text: bounded_text(&fields[1], "string comparison", limits)?,
            language: optional_text(&fields[2], "string comparison language", limits)?,
        }),
        "binary-comparison-v1" if fields.len() == 3 => Ok(ComparisonValue::Binary {
            kind: binary_kind(string(&fields[1], "binary comparison kind")?)?,
            octets: decode_binary(
                string(&fields[2], "binary comparison octets")?,
                limits,
                control,
            )?,
        }),
        "any-uri-comparison-v1" if fields.len() == 2 => Ok(ComparisonValue::Uri(bounded_text(
            &fields[1],
            "URI comparison",
            limits,
        )?)),
        "xml-literal-comparison-v1" if fields.len() == 2 => Ok(ComparisonValue::Xml(bounded_text(
            &fields[1],
            "XML comparison",
            limits,
        )?)),
        "date-time-comparison-v1" if fields.len() == 4 => Ok(ComparisonValue::DateTime {
            local: ExactRational::from_tokens(
                string(&fields[1], "date/time comparison numerator")?,
                string(&fields[2], "date/time comparison denominator")?,
                limits,
                control,
            )?,
            timezone_offset_minutes: optional_offset(&fields[3])?,
        }),
        _ => Err(DatatypeError::invalid(
            "unknown or malformed comparison tag",
        )),
    }
}

fn require_matching_pair(
    identity: &DataIdentity,
    comparison: &ComparisonValue,
) -> Result<(), DatatypeError> {
    let matches = match (identity, comparison) {
        (DataIdentity::Numeric(left), ComparisonValue::Numeric(right)) => left == right,
        (DataIdentity::Boolean(left), ComparisonValue::Boolean(right)) => left == right,
        (
            DataIdentity::IEEE { format, bits },
            ComparisonValue::IEEE {
                format: comparison_format,
                category,
                value,
            },
        ) => {
            let (expected_category, expected_value) = ieee_comparison(*format, *bits)?;
            format == comparison_format
                && *category == expected_category
                && *value == expected_value
        }
        (
            DataIdentity::String { text, language },
            ComparisonValue::String {
                text: comparison_text,
                language: comparison_language,
            },
        ) => text == comparison_text && language == comparison_language,
        (
            DataIdentity::Binary { kind, octets },
            ComparisonValue::Binary {
                kind: comparison_kind,
                octets: comparison_octets,
            },
        ) => kind == comparison_kind && octets == comparison_octets,
        (DataIdentity::Uri(left), ComparisonValue::Uri(right))
        | (DataIdentity::Xml(left), ComparisonValue::Xml(right)) => left == right,
        (
            DataIdentity::DateTime {
                local,
                timezone_offset_minutes,
                ..
            },
            ComparisonValue::DateTime {
                local: comparison_local,
                timezone_offset_minutes: comparison_offset,
            },
        ) => local == comparison_local && timezone_offset_minutes == comparison_offset,
        _ => false,
    };
    if matches {
        Ok(())
    } else {
        Err(DatatypeError::invalid(
            "data identity and comparison do not describe one value",
        ))
    }
}

fn ieee_comparison(
    format: IEEEFormat,
    bits: u64,
) -> Result<(IEEECategory, ExactRational), DatatypeError> {
    let fraction_bits = format.fraction_bits();
    let exponent_bits = format.exponent_bits();
    let exponent_mask = (1_u64 << exponent_bits) - 1;
    let fraction_mask = (1_u64 << fraction_bits) - 1;
    let exponent = (bits >> fraction_bits) & exponent_mask;
    let fraction = bits & fraction_mask;
    let negative = bits >> (format.width() - 1) != 0;
    if exponent == exponent_mask {
        let category = if fraction != 0 {
            IEEECategory::NaN
        } else if negative {
            IEEECategory::NegativeInfinity
        } else {
            IEEECategory::PositiveInfinity
        };
        return Ok((category, ExactRational::new(BigInt::zero(), BigInt::one())?));
    }
    let (significand, binary_exponent) = if exponent == 0 {
        (
            fraction,
            1 - format.bias() - i32::try_from(fraction_bits).unwrap_or(i32::MAX),
        )
    } else {
        (
            (1_u64 << fraction_bits) | fraction,
            i32::try_from(exponent).unwrap_or(i32::MAX)
                - format.bias()
                - i32::try_from(fraction_bits).unwrap_or(i32::MAX),
        )
    };
    let mut numerator = BigInt::from(significand);
    let mut denominator = BigInt::one();
    if binary_exponent >= 0 {
        numerator <<= usize::try_from(binary_exponent).unwrap_or(usize::MAX);
    } else {
        denominator <<= usize::try_from(-binary_exponent).unwrap_or(usize::MAX);
    }
    if negative {
        numerator = -numerator;
    }
    Ok((
        IEEECategory::Finite,
        ExactRational::new(numerator, denominator)?,
    ))
}

fn compare_ieee(
    left_format: IEEEFormat,
    left_category: IEEECategory,
    left_value: &ExactRational,
    right_format: IEEEFormat,
    right_category: IEEECategory,
    right_value: &ExactRational,
) -> Result<ComparisonOrder, DatatypeError> {
    if left_format != right_format {
        return Err(DatatypeError::invalid(
            "IEEE comparisons require the same XML Schema datatype",
        ));
    }
    if left_category == IEEECategory::NaN || right_category == IEEECategory::NaN {
        return Ok(ComparisonOrder::Unordered);
    }
    let rank = |category| match category {
        IEEECategory::NegativeInfinity => 0,
        IEEECategory::Finite => 1,
        IEEECategory::PositiveInfinity => 2,
        IEEECategory::NaN => 3,
    };
    let left_rank = rank(left_category);
    let right_rank = rank(right_category);
    Ok(if left_rank != right_rank {
        order(left_rank.cmp(&right_rank))
    } else if left_category == IEEECategory::Finite {
        order(left_value.compare(right_value))
    } else {
        ComparisonOrder::Equal
    })
}

fn compare_date_time(
    left_local: &ExactRational,
    left_offset: Option<i16>,
    right_local: &ExactRational,
    right_offset: Option<i16>,
) -> ComparisonOrder {
    match (left_offset, right_offset) {
        (None, None) => order(left_local.compare(right_local)),
        (Some(left), Some(right)) => order(
            left_local
                .subtract_integer(i64::from(left) * 60)
                .compare(&right_local.subtract_integer(i64::from(right) * 60)),
        ),
        (Some(offset), None) => compare_zoned_to_unzoned(
            &left_local.subtract_integer(i64::from(offset) * 60),
            right_local,
        ),
        (None, Some(offset)) => reverse_order(compare_zoned_to_unzoned(
            &right_local.subtract_integer(i64::from(offset) * 60),
            left_local,
        )),
    }
}

fn compare_zoned_to_unzoned(
    zoned_utc: &ExactRational,
    unzoned_local: &ExactRational,
) -> ComparisonOrder {
    let low = unzoned_local.plus_or_minus_integer(-50_400);
    let high = unzoned_local.plus_or_minus_integer(50_400);
    if zoned_utc.compare(&low) == Ordering::Less {
        ComparisonOrder::Less
    } else if zoned_utc.compare(&high) == Ordering::Greater {
        ComparisonOrder::Greater
    } else {
        ComparisonOrder::Unordered
    }
}

const fn reverse_order(value: ComparisonOrder) -> ComparisonOrder {
    match value {
        ComparisonOrder::Less => ComparisonOrder::Greater,
        ComparisonOrder::Greater => ComparisonOrder::Less,
        ComparisonOrder::Equal => ComparisonOrder::Equal,
        ComparisonOrder::Unordered => ComparisonOrder::Unordered,
    }
}

const fn order(value: Ordering) -> ComparisonOrder {
    match value {
        Ordering::Less => ComparisonOrder::Less,
        Ordering::Equal => ComparisonOrder::Equal,
        Ordering::Greater => ComparisonOrder::Greater,
    }
}

const fn equality_order(equal: bool) -> ComparisonOrder {
    if equal {
        ComparisonOrder::Equal
    } else {
        ComparisonOrder::Unordered
    }
}

fn rational_fields(
    fields: &[Value],
    limits: DatatypeLimits,
    control: &impl DatatypeControl,
) -> Result<ExactRational, DatatypeError> {
    ExactRational::from_tokens(
        string(&fields[1], "rational numerator")?,
        string(&fields[2], "rational denominator")?,
        limits,
        control,
    )
}

fn parse_integer_token(
    value: &str,
    limits: DatatypeLimits,
    control: &impl DatatypeControl,
) -> Result<BigInt, DatatypeError> {
    let bytes = value.as_bytes();
    if bytes.len() < 2 || !matches!(bytes[0], b'+' | b'-') {
        return Err(DatatypeError::invalid(
            "integer token must be signed lowercase hexadecimal",
        ));
    }
    let digits = &bytes[1..];
    let observed = u64::try_from(digits.len()).unwrap_or(u64::MAX);
    if observed > limits.max_numeric_hex_digits {
        return Err(DatatypeError::resource(
            "max_numeric_hex_digits",
            observed,
            limits.max_numeric_hex_digits,
        ));
    }
    if digits.len() > 1 && digits[0] == b'0' {
        return Err(DatatypeError::invalid(
            "integer token has a noncanonical leading zero",
        ));
    }
    for (offset, digit) in digits.iter().enumerate() {
        if offset % POLL_STRIDE == 0 {
            control.poll()?;
        }
        if !digit.is_ascii_digit() && !(b'a'..=b'f').contains(digit) {
            return Err(DatatypeError::invalid(
                "integer token contains a non-lowercase-hexadecimal digit",
            ));
        }
    }
    let magnitude = BigInt::parse_bytes(digits, 16)
        .ok_or_else(|| DatatypeError::invalid("integer token has no hexadecimal magnitude"))?;
    let result = if bytes[0] == b'-' {
        -magnitude
    } else {
        magnitude
    };
    if integer_token(&result) != value {
        return Err(DatatypeError::invalid(
            "integer token is not canonical signed hexadecimal",
        ));
    }
    Ok(result)
}

fn integer_token(value: &BigInt) -> String {
    let sign = if value.is_negative() { '-' } else { '+' };
    format!("{sign}{}", value.abs().to_str_radix(16))
}

fn decode_ieee_bits(value: &str, format: IEEEFormat) -> Result<u64, DatatypeError> {
    let expected = usize::try_from(format.width() / 4).unwrap_or(usize::MAX);
    if value.len() != expected
        || !value
            .as_bytes()
            .iter()
            .all(|digit| digit.is_ascii_digit() || (b'a'..=b'f').contains(digit))
    {
        return Err(DatatypeError::invalid(
            "IEEE bits must be fixed-width lowercase hexadecimal",
        ));
    }
    let bits = u64::from_str_radix(value, 16)
        .map_err(|_| DatatypeError::invalid("IEEE bits cannot be decoded"))?;
    let fraction_bits = format.fraction_bits();
    let exponent_mask = (1_u64 << format.exponent_bits()) - 1;
    let exponent = (bits >> fraction_bits) & exponent_mask;
    let fraction = bits & ((1_u64 << fraction_bits) - 1);
    if exponent == exponent_mask && fraction != 0 {
        let canonical = (exponent_mask << fraction_bits) | (1_u64 << (fraction_bits - 1));
        if bits != canonical {
            return Err(DatatypeError::invalid(
                "IEEE NaN identity is not the canonical XML Schema NaN",
            ));
        }
    }
    Ok(bits)
}

fn decode_binary(
    value: &str,
    limits: DatatypeLimits,
    control: &impl DatatypeControl,
) -> Result<Vec<u8>, DatatypeError> {
    if value.len() % 2 != 0 {
        return Err(DatatypeError::invalid(
            "binary semantic octets require an even hexadecimal length",
        ));
    }
    let observed = u64::try_from(value.len() / 2).unwrap_or(u64::MAX);
    if observed > limits.max_binary_bytes {
        return Err(DatatypeError::resource(
            "max_binary_bytes",
            observed,
            limits.max_binary_bytes,
        ));
    }
    let mut result = Vec::with_capacity(value.len() / 2);
    for (offset, pair) in value.as_bytes().chunks_exact(2).enumerate() {
        if offset % POLL_STRIDE == 0 {
            control.poll()?;
        }
        let high = hex_nibble(pair[0])?;
        let low = hex_nibble(pair[1])?;
        result.push((high << 4) | low);
    }
    Ok(result)
}

fn hex_nibble(value: u8) -> Result<u8, DatatypeError> {
    match value {
        b'0'..=b'9' => Ok(value - b'0'),
        b'a'..=b'f' => Ok(value - b'a' + 10),
        _ => Err(DatatypeError::invalid(
            "binary semantic octets must be lowercase hexadecimal",
        )),
    }
}

fn tag<'a>(fields: &'a [Value], name: &str) -> Result<&'a str, DatatypeError> {
    fields
        .first()
        .and_then(Value::as_str)
        .ok_or_else(|| DatatypeError::invalid(format!("{name} has no string tag")))
}

fn string<'a>(value: &'a Value, name: &str) -> Result<&'a str, DatatypeError> {
    value
        .as_str()
        .ok_or_else(|| DatatypeError::invalid(format!("{name} must be a string")))
}

fn bounded_text(
    value: &Value,
    name: &str,
    limits: DatatypeLimits,
) -> Result<String, DatatypeError> {
    let text = string(value, name)?;
    let observed = u64::try_from(text.chars().count()).unwrap_or(u64::MAX);
    if observed > limits.max_text_characters {
        return Err(DatatypeError::resource(
            "max_text_characters",
            observed,
            limits.max_text_characters,
        ));
    }
    Ok(text.to_owned())
}

fn optional_text(
    value: &Value,
    name: &str,
    limits: DatatypeLimits,
) -> Result<Option<String>, DatatypeError> {
    if value.is_null() {
        Ok(None)
    } else {
        let text = bounded_text(value, name, limits)?;
        if text.is_empty() {
            return Err(DatatypeError::invalid(format!(
                "{name} must be nonempty when supplied"
            )));
        }
        Ok(Some(text))
    }
}

fn boolean(value: &Value) -> Result<bool, DatatypeError> {
    value
        .as_bool()
        .ok_or_else(|| DatatypeError::invalid("semantic Boolean field must be bool"))
}

fn optional_offset(value: &Value) -> Result<Option<i16>, DatatypeError> {
    if value.is_null() {
        return Ok(None);
    }
    let raw = value
        .as_i64()
        .ok_or_else(|| DatatypeError::invalid("date/time offset must be an integer or null"))?;
    if !(-840..=840).contains(&raw) {
        return Err(DatatypeError::invalid(
            "date/time offset must be from -840 through 840 minutes",
        ));
    }
    i16::try_from(raw)
        .map(Some)
        .map_err(|_| DatatypeError::invalid("date/time offset is not representable"))
}

fn ieee_format(value: &str) -> Result<IEEEFormat, DatatypeError> {
    match value {
        "float32" => Ok(IEEEFormat::Float32),
        "float64" => Ok(IEEEFormat::Float64),
        _ => Err(DatatypeError::invalid("unknown IEEE format")),
    }
}

fn ieee_category(value: &str) -> Result<IEEECategory, DatatypeError> {
    match value {
        "finite" => Ok(IEEECategory::Finite),
        "negative-infinity" => Ok(IEEECategory::NegativeInfinity),
        "positive-infinity" => Ok(IEEECategory::PositiveInfinity),
        "nan" => Ok(IEEECategory::NaN),
        _ => Err(DatatypeError::invalid("unknown IEEE comparison category")),
    }
}

fn binary_kind(value: &str) -> Result<BinaryKind, DatatypeError> {
    match value {
        "hexBinary" => Ok(BinaryKind::Hex),
        "base64Binary" => Ok(BinaryKind::Base64),
        _ => Err(DatatypeError::invalid("unknown binary primitive family")),
    }
}

#[cfg(test)]
pub(super) fn tagged_identity(value: &DataIdentity) -> Vec<Value> {
    match value {
        DataIdentity::Numeric(number) => vec![
            Value::String("numeric-rational-hex-v1".to_owned()),
            Value::String(number.numerator_token()),
            Value::String(number.denominator_token()),
        ],
        DataIdentity::Boolean(value) => {
            vec![Value::String("boolean".to_owned()), Value::Bool(*value)]
        }
        DataIdentity::IEEE { format, bits } => vec![
            Value::String("ieee-identity-v1".to_owned()),
            Value::String(format.as_str().to_owned()),
            Value::String(format!(
                "{bits:0width$x}",
                width = usize::try_from(format.width() / 4).unwrap_or(0)
            )),
        ],
        DataIdentity::String { text, language } => vec![
            Value::String("plain-string-v1".to_owned()),
            Value::String(text.clone()),
            language.clone().map_or(Value::Null, Value::String),
        ],
        DataIdentity::Binary { kind, octets } => vec![
            Value::String("binary-identity-v1".to_owned()),
            Value::String(kind.as_str().to_owned()),
            Value::String(crate::model::hex(octets)),
        ],
        DataIdentity::Uri(value) => vec![
            Value::String("any-uri-v1".to_owned()),
            Value::String(value.clone()),
        ],
        DataIdentity::Xml(value) => vec![
            Value::String("xml-literal-c14n-v1".to_owned()),
            Value::String(value.clone()),
        ],
        DataIdentity::DateTime {
            local,
            timezone_offset_minutes,
            hermit_end_of_day,
        } => vec![
            Value::String("date-time-identity-v1".to_owned()),
            Value::String(local.numerator_token()),
            Value::String(local.denominator_token()),
            timezone_offset_minutes.map_or(Value::Null, |value| Value::from(i64::from(value))),
            Value::Bool(*hermit_end_of_day),
        ],
    }
}

#[cfg(test)]
pub(super) fn tagged_comparison(value: &ComparisonValue) -> Vec<Value> {
    match value {
        ComparisonValue::Numeric(number) => vec![
            Value::String("ordered-numeric-rational-hex-v1".to_owned()),
            Value::String(number.numerator_token()),
            Value::String(number.denominator_token()),
        ],
        ComparisonValue::Boolean(value) => vec![
            Value::String("boolean-equality".to_owned()),
            Value::Bool(*value),
        ],
        ComparisonValue::IEEE {
            format,
            category,
            value,
        } => vec![
            Value::String("ieee-comparison-v1".to_owned()),
            Value::String(format.as_str().to_owned()),
            Value::String(category.as_str().to_owned()),
            Value::String(value.numerator_token()),
            Value::String(value.denominator_token()),
        ],
        ComparisonValue::String { text, language } => vec![
            Value::String("plain-string-comparison-v1".to_owned()),
            Value::String(text.clone()),
            language.clone().map_or(Value::Null, Value::String),
        ],
        ComparisonValue::Binary { kind, octets } => vec![
            Value::String("binary-comparison-v1".to_owned()),
            Value::String(kind.as_str().to_owned()),
            Value::String(crate::model::hex(octets)),
        ],
        ComparisonValue::Uri(value) => vec![
            Value::String("any-uri-comparison-v1".to_owned()),
            Value::String(value.clone()),
        ],
        ComparisonValue::Xml(value) => vec![
            Value::String("xml-literal-comparison-v1".to_owned()),
            Value::String(value.clone()),
        ],
        ComparisonValue::DateTime {
            local,
            timezone_offset_minutes,
        } => vec![
            Value::String("date-time-comparison-v1".to_owned()),
            Value::String(local.numerator_token()),
            Value::String(local.denominator_token()),
            timezone_offset_minutes.map_or(Value::Null, |value| Value::from(i64::from(value))),
        ],
    }
}
