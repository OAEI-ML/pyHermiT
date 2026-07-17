use std::cell::Cell;
use std::collections::HashSet;

use num_bigint::{BigInt, BigUint};
use serde_json::json;

use super::*;

fn rational(numerator: i64, denominator: i64) -> Result<ExactRational, DatatypeError> {
    ExactRational::new(BigInt::from(numerator), BigInt::from(denominator))
}

fn integer(value: i64) -> Result<ExactRational, DatatypeError> {
    rational(value, 1)
}

fn interval(
    lower: Option<(i64, bool)>,
    upper: Option<(i64, bool)>,
) -> Result<NumericInterval, DatatypeError> {
    NumericInterval::new(
        lower.map(|(value, _)| integer(value)).transpose()?,
        lower.is_some_and(|(_, inclusive)| inclusive),
        upper.map(|(value, _)| integer(value)).transpose()?,
        upper.is_some_and(|(_, inclusive)| inclusive),
    )
}

fn integer_ranges() -> Result<Vec<NumericRange>, DatatypeError> {
    let mut ranges = vec![
        NumericRange::empty(NumericDomain::Integer),
        NumericRange::all(NumericDomain::Integer),
        NumericRange::new(
            NumericDomain::Integer,
            [
                interval(Some((-4, true)), Some((-2, true)))?,
                interval(Some((1, true)), Some((3, true)))?,
            ],
        )?,
    ];
    let endpoints = [
        None,
        Some(-3),
        Some(-2),
        Some(-1),
        Some(0),
        Some(1),
        Some(2),
        Some(3),
    ];
    for lower in endpoints {
        for lower_inclusive in [false, true] {
            if lower.is_none() && lower_inclusive {
                continue;
            }
            for upper in endpoints {
                for upper_inclusive in [false, true] {
                    if upper.is_none() && upper_inclusive {
                        continue;
                    }
                    ranges.push(NumericRange::new(
                        NumericDomain::Integer,
                        [interval(
                            lower.map(|value| (value, lower_inclusive)),
                            upper.map(|value| (value, upper_inclusive)),
                        )?],
                    )?);
                }
            }
        }
    }
    Ok(ranges)
}

#[test]
fn numeric_domains_and_exact_emptiness_match_the_python_oracle(
) -> Result<(), Box<dyn std::error::Error>> {
    let half = rational(1, 2)?;
    let fifth = rational(1, 5)?;
    let third = rational(1, 3)?;
    assert!(!numeric_domain_contains(NumericDomain::Integer, &half)?);
    assert!(numeric_domain_contains(NumericDomain::Decimal, &half)?);
    assert!(numeric_domain_contains(NumericDomain::Decimal, &fifth)?);
    assert!(!numeric_domain_contains(NumericDomain::Decimal, &third)?);
    assert!(numeric_domain_contains(NumericDomain::Rational, &third)?);
    assert!(numeric_domain_contains(NumericDomain::Real, &third)?);

    let no_integer = NumericRange::between(
        NumericDomain::Integer,
        Some(integer(0)?),
        false,
        Some(integer(1)?),
        false,
    )?;
    assert!(no_integer.is_empty_exact());
    assert_eq!(no_integer.cardinality()?, Cardinality::Empty);

    let two_integers = NumericRange::between(
        NumericDomain::Integer,
        Some(integer(0)?),
        true,
        Some(integer(1)?),
        true,
    )?;
    assert_eq!(
        two_integers.cardinality()?,
        Cardinality::Finite(BigUint::from(2_u8))
    );

    let dense = NumericRange::between(
        NumericDomain::Rational,
        Some(integer(0)?),
        false,
        Some(integer(1)?),
        false,
    )?;
    assert_eq!(dense.cardinality()?, Cardinality::Infinite);

    let nondecimal_singleton = NumericRange::between(
        NumericDomain::Decimal,
        Some(third.clone()),
        true,
        Some(third),
        true,
    )?;
    assert!(nondecimal_singleton.is_empty_exact());
    Ok(())
}

#[test]
fn numeric_algebra_is_pointwise_exact_on_an_exhaustive_small_integer_oracle(
) -> Result<(), Box<dyn std::error::Error>> {
    let ranges = integer_ranges()?;
    for left in &ranges {
        let complement = left.complement()?;
        let round_trip = complement.complement()?;
        for probe in -8..=8 {
            let value = integer(probe)?;
            assert_eq!(complement.contains(&value)?, !left.contains(&value)?);
            assert_eq!(round_trip.contains(&value)?, left.contains(&value)?);
        }
        for right in &ranges {
            let intersection = left.intersection(right)?;
            let union = left.union(right)?;
            for probe in -8..=8 {
                let value = integer(probe)?;
                let left_contains = left.contains(&value)?;
                let right_contains = right.contains(&value)?;
                assert_eq!(
                    intersection.contains(&value)?,
                    left_contains && right_contains
                );
                assert_eq!(union.contains(&value)?, left_contains || right_contains);
            }
        }
    }
    Ok(())
}

#[test]
fn numeric_facets_cardinality_enumeration_and_witnesses_are_deterministic(
) -> Result<(), Box<dyn std::error::Error>> {
    let base = NumericRange::all(NumericDomain::Integer)
        .apply_facet(OrderedFacet::MinInclusive, integer(-1)?)?
        .apply_facet(OrderedFacet::MaxExclusive, integer(3)?)?;
    assert_eq!(
        base.enumerate_values(RangeLimits::default(), &super::super::NeverCancel)?,
        vec![integer(-1)?, integer(0)?, integer(1)?, integer(2)?]
    );
    assert_eq!(
        base.first_value(&[], RangeLimits::default(), &super::super::NeverCancel)?,
        Some(integer(0)?)
    );
    assert_eq!(
        base.first_value(
            &[integer(0)?, integer(1)?],
            RangeLimits::default(),
            &super::super::NeverCancel,
        )?,
        Some(integer(-1)?)
    );
    let opposite_facets = NumericRange::all(NumericDomain::Integer)
        .apply_facet(OrderedFacet::MinExclusive, integer(-2)?)?
        .apply_facet(OrderedFacet::MaxInclusive, integer(2)?)?;
    assert_eq!(
        opposite_facets.enumerate_values(RangeLimits::default(), &super::super::NeverCancel,)?,
        vec![integer(-1)?, integer(0)?, integer(1)?, integer(2)?]
    );

    let mixed = NumericRange::all(NumericDomain::Real)
        .intersection(&NumericRange::all(NumericDomain::Integer))?;
    assert_eq!(mixed.domain(), NumericDomain::Integer);
    assert!(NumericRange::all(NumericDomain::Real)
        .union(&NumericRange::all(NumericDomain::Integer))
        .is_err());
    Ok(())
}

#[test]
fn boolean_algebra_is_exhaustive() {
    let ranges = [
        BooleanRange::empty(),
        BooleanRange::from_values([false]),
        BooleanRange::from_values([true]),
        BooleanRange::all(),
    ];
    for left in ranges {
        assert_eq!(left.complement().complement(), left);
        for right in ranges {
            for probe in [false, true] {
                assert_eq!(
                    left.intersection(right).contains(probe),
                    left.contains(probe) && right.contains(probe)
                );
                assert_eq!(
                    left.union(right).contains(probe),
                    left.contains(probe) || right.contains(probe)
                );
            }
        }
    }
    assert_eq!(BooleanRange::all().enumerate_values(), vec![false, true]);
    assert_eq!(BooleanRange::all().first_value(&[false]), Some(true));
    assert_eq!(
        BooleanRange::all().cardinality(),
        Cardinality::Finite(BigUint::from(2_u8))
    );
}

#[test]
fn ieee_zero_nan_and_discrete_algebra_match_the_python_oracle(
) -> Result<(), Box<dyn std::error::Error>> {
    const POSITIVE_ZERO: u64 = 0x0000_0000;
    const NEGATIVE_ZERO: u64 = 0x8000_0000;
    const NEGATIVE_ONE: u64 = 0xbf80_0000;
    const POSITIVE_ONE: u64 = 0x3f80_0000;
    const NAN: u64 = 0x7fc0_0000;
    const POSITIVE_INFINITY: u64 = 0x7f80_0000;
    const NEGATIVE_INFINITY: u64 = 0xff80_0000;

    let all = IEEERange::all(IEEEFormat::Float32)?;
    for bits in [
        POSITIVE_ZERO,
        NEGATIVE_ZERO,
        NEGATIVE_ONE,
        POSITIVE_ONE,
        NAN,
        POSITIVE_INFINITY,
        NEGATIVE_INFINITY,
    ] {
        assert!(all.contains_bits(IEEEFormat::Float32, bits));
    }
    assert!(!all.contains_bits(IEEEFormat::Float64, POSITIVE_ZERO));

    let zero = IEEERange::bounded(
        IEEEFormat::Float32,
        Some(POSITIVE_ZERO),
        true,
        Some(NEGATIVE_ZERO),
        true,
    )?;
    assert!(zero.contains_bits(IEEEFormat::Float32, POSITIVE_ZERO));
    assert!(zero.contains_bits(IEEEFormat::Float32, NEGATIVE_ZERO));
    assert_eq!(zero.cardinality(), Cardinality::Finite(BigUint::from(2_u8)));

    let no_zero = IEEERange::bounded(
        IEEEFormat::Float32,
        Some(POSITIVE_ZERO),
        false,
        Some(NEGATIVE_ZERO),
        false,
    )?;
    assert!(no_zero.is_empty_exact());

    let finite_nonnegative = all
        .apply_facet(OrderedFacet::MinInclusive, POSITIVE_ZERO)?
        .apply_facet(OrderedFacet::MaxExclusive, POSITIVE_INFINITY)?;
    let complement = finite_nonnegative.complement()?;
    let probes = [
        POSITIVE_ZERO,
        NEGATIVE_ZERO,
        NEGATIVE_ONE,
        POSITIVE_ONE,
        NAN,
        POSITIVE_INFINITY,
        NEGATIVE_INFINITY,
    ];
    for bits in probes {
        assert_eq!(
            complement.contains_bits(IEEEFormat::Float32, bits),
            !finite_nonnegative.contains_bits(IEEEFormat::Float32, bits)
        );
    }
    let finite_unit = IEEERange::bounded(
        IEEEFormat::Float32,
        Some(NEGATIVE_ONE),
        true,
        Some(POSITIVE_ONE),
        true,
    )?;
    let ranges = [
        IEEERange::empty(IEEEFormat::Float32),
        all.clone(),
        zero,
        finite_nonnegative,
        finite_unit,
        IEEERange::new(IEEEFormat::Float32, [], true)?,
    ];
    for left in &ranges {
        let left_complement = left.complement()?;
        for bits in probes {
            assert_eq!(
                left_complement.contains_bits(IEEEFormat::Float32, bits),
                !left.contains_bits(IEEEFormat::Float32, bits)
            );
        }
        for right in &ranges {
            let intersection = left.intersection(right)?;
            let union = left.union(right)?;
            for bits in probes {
                let left_contains = left.contains_bits(IEEEFormat::Float32, bits);
                let right_contains = right.contains_bits(IEEEFormat::Float32, bits);
                assert_eq!(
                    intersection.contains_bits(IEEEFormat::Float32, bits),
                    left_contains && right_contains
                );
                assert_eq!(
                    union.contains_bits(IEEEFormat::Float32, bits),
                    left_contains || right_contains
                );
            }
        }
    }
    assert!(all
        .apply_facet(OrderedFacet::MinInclusive, NAN)?
        .is_empty_exact());
    assert!(all
        .intersection(&IEEERange::all(IEEEFormat::Float64)?)
        .is_err());
    Ok(())
}

#[test]
fn ieee_enumeration_and_witness_order_are_stable() -> Result<(), Box<dyn std::error::Error>> {
    const NEGATIVE_ZERO: u64 = 0x8000_0000;
    const POSITIVE_ZERO: u64 = 0x0000_0000;
    let zero = IEEERange::bounded(
        IEEEFormat::Float32,
        Some(POSITIVE_ZERO),
        true,
        Some(POSITIVE_ZERO),
        true,
    )?;
    let expected = vec![
        DataIdentity::IEEE {
            format: IEEEFormat::Float32,
            bits: NEGATIVE_ZERO,
        },
        DataIdentity::IEEE {
            format: IEEEFormat::Float32,
            bits: POSITIVE_ZERO,
        },
    ];
    assert_eq!(
        zero.enumerate_values(RangeLimits::default(), &super::super::NeverCancel)?,
        expected
    );
    assert_eq!(
        zero.first_identity(&[], RangeLimits::default(), &super::super::NeverCancel)?,
        Some(DataIdentity::IEEE {
            format: IEEEFormat::Float32,
            bits: NEGATIVE_ZERO,
        })
    );
    assert_eq!(
        zero.first_identity(
            &[DataIdentity::IEEE {
                format: IEEEFormat::Float32,
                bits: NEGATIVE_ZERO,
            }],
            RangeLimits::default(),
            &super::super::NeverCancel,
        )?,
        Some(DataIdentity::IEEE {
            format: IEEEFormat::Float32,
            bits: POSITIVE_ZERO,
        })
    );
    Ok(())
}

fn length_ranges() -> Result<Vec<LengthRange>, DatatypeError> {
    let mut ranges = vec![
        LengthRange::empty(),
        LengthRange::all(),
        LengthRange::new([
            LengthInterval::new(1, Some(2))?,
            LengthInterval::new(5, Some(7))?,
        ]),
    ];
    for lower in 0..=7 {
        for upper in lower..=7 {
            ranges.push(LengthRange::between(lower, Some(upper))?);
        }
        ranges.push(LengthRange::between(lower, None)?);
    }
    Ok(ranges)
}

#[test]
fn length_algebra_is_pointwise_exact_on_an_exhaustive_small_oracle(
) -> Result<(), Box<dyn std::error::Error>> {
    let ranges = length_ranges()?;
    for left in &ranges {
        let complement = left.complement();
        assert_eq!(complement.complement(), *left);
        for probe in 0..=12 {
            assert_eq!(complement.contains(probe), !left.contains(probe));
        }
        for right in &ranges {
            let intersection = left.intersection(right);
            let union = left.union(right);
            for probe in 0..=12 {
                assert_eq!(
                    intersection.contains(probe),
                    left.contains(probe) && right.contains(probe)
                );
                assert_eq!(
                    union.contains(probe),
                    left.contains(probe) || right.contains(probe)
                );
            }
        }
    }
    let faceted = LengthRange::all()
        .apply_facet(LengthFacet::MinLength, 2)
        .apply_facet(LengthFacet::MaxLength, 4);
    assert_eq!(
        faceted.cardinality(),
        Cardinality::Finite(BigUint::from(3_u8))
    );
    assert_eq!(
        faceted.first_length(
            &HashSet::from([2_u64, 3_u64]),
            RangeLimits::default(),
            &super::super::NeverCancel,
        )?,
        Some(4)
    );
    assert_eq!(
        LengthRange::between(0, Some(u64::MAX))?.cardinality(),
        Cardinality::Finite(BigUint::from(u64::MAX) + BigUint::from(1_u8))
    );
    Ok(())
}

#[test]
fn binary_cardinality_enumeration_and_witnesses_are_exact() -> Result<(), Box<dyn std::error::Error>>
{
    let lengths = LengthRange::between(0, Some(1))?;
    let range = BinaryRange::new(BinaryKind::Hex, lengths);
    assert_eq!(
        range.cardinality(RangeLimits::default(), &super::super::NeverCancel)?,
        Cardinality::Finite(BigUint::from(257_u16))
    );
    assert_eq!(
        range.cardinality_up_to(300, &super::super::NeverCancel)?,
        257
    );
    assert!(range.cardinality_at_least(257, &super::super::NeverCancel)?);
    assert!(!range.cardinality_at_least(258, &super::super::NeverCancel)?);

    let empty_identity = DataIdentity::Binary {
        kind: BinaryKind::Hex,
        octets: Vec::new(),
    };
    assert!(range.contains(&empty_identity));
    assert_eq!(
        range.first_identity(&[], RangeLimits::default(), &super::super::NeverCancel)?,
        Some(empty_identity.clone())
    );
    assert_eq!(
        range.first_identity(
            &[empty_identity],
            RangeLimits::default(),
            &super::super::NeverCancel,
        )?,
        Some(DataIdentity::Binary {
            kind: BinaryKind::Hex,
            octets: vec![0],
        })
    );

    let singleton = BinaryRange::new(BinaryKind::Hex, LengthRange::between(0, Some(0))?);
    assert_eq!(
        singleton.enumerate_values(RangeLimits::default(), &super::super::NeverCancel)?,
        vec![DataIdentity::Binary {
            kind: BinaryKind::Hex,
            octets: Vec::new(),
        }]
    );
    assert!(range
        .intersection(&BinaryRange::all(BinaryKind::Base64))
        .is_err());
    Ok(())
}

#[test]
fn binary_algebra_and_facets_are_family_relative() -> Result<(), Box<dyn std::error::Error>> {
    let all = BinaryRange::all(BinaryKind::Base64);
    let one = all.apply_facet(LengthFacet::Length, 1);
    let not_one = one.complement();
    for length in 0..=4 {
        let identity = DataIdentity::Binary {
            kind: BinaryKind::Base64,
            octets: vec![0; usize::try_from(length)?],
        };
        assert_eq!(not_one.contains(&identity), !one.contains(&identity));
    }
    assert_eq!(
        one.intersection(&not_one)?,
        BinaryRange::empty(BinaryKind::Base64)
    );
    assert_eq!(one.union(&not_one)?, all);
    Ok(())
}

#[derive(Debug)]
struct CancelImmediately {
    polls: Cell<u64>,
}

impl DatatypeControl for CancelImmediately {
    fn poll(&self) -> Result<(), DatatypeError> {
        self.polls.set(self.polls.get().saturating_add(1));
        Err(DatatypeError::cancelled("cancelled by range test"))
    }
}

#[test]
fn materialization_obeys_resource_and_cancellation_contracts(
) -> Result<(), Box<dyn std::error::Error>> {
    let booleans_as_integers = NumericRange::between(
        NumericDomain::Integer,
        Some(integer(0)?),
        true,
        Some(integer(1)?),
        true,
    )?;
    let limits = RangeLimits {
        max_enumeration_values: 1,
        ..RangeLimits::default()
    };
    let error = booleans_as_integers
        .enumerate_values(limits, &super::super::NeverCancel)
        .err()
        .ok_or_else(|| DatatypeError::invalid("expected enumeration resource error"))?;
    assert_eq!(error.limit, Some("max_enumeration_values"));

    let binary = BinaryRange::new(BinaryKind::Hex, LengthRange::between(2, Some(2))?);
    let limits = RangeLimits {
        max_binary_bytes: 1,
        ..RangeLimits::default()
    };
    let error = binary
        .first_identity(&[], limits, &super::super::NeverCancel)
        .err()
        .ok_or_else(|| DatatypeError::invalid("expected binary witness resource error"))?;
    assert_eq!(error.limit, Some("max_binary_bytes"));

    let cancellation = CancelImmediately {
        polls: Cell::new(0),
    };
    let error = booleans_as_integers
        .enumerate_values(RangeLimits::default(), &cancellation)
        .err()
        .ok_or_else(|| DatatypeError::invalid("expected cancellation"))?;
    assert_eq!(error.kind, super::super::DatatypeErrorKind::Cancelled);
    assert_eq!(cancellation.polls.get(), 1);
    Ok(())
}

#[test]
fn production_python_oracle_fixture_matches_byte_for_byte_semantics(
) -> Result<(), Box<dyn std::error::Error>> {
    let integer_probes = (-5..=5).map(integer).collect::<Result<Vec<_>, _>>()?;
    let left = NumericRange::between(
        NumericDomain::Integer,
        Some(integer(-2)?),
        true,
        Some(integer(2)?),
        true,
    )?;
    let right = NumericRange::new(
        NumericDomain::Integer,
        [
            interval(Some((-4, true)), Some((-1, false)))?,
            interval(Some((1, false)), Some((4, true)))?,
        ],
    )?;
    let intersection = left.intersection(&right)?;
    let union = left.union(&right)?;
    let complement = left.complement()?;
    let decimal_probes = [
        rational(1, 3)?,
        rational(1, 2)?,
        rational(1, 5)?,
        integer(1)?,
    ];
    let decimal = NumericRange::between(
        NumericDomain::Decimal,
        Some(integer(0)?),
        false,
        Some(integer(1)?),
        true,
    )?;
    let mut numeric_forbidden = Vec::new();
    let mut numeric_witnesses = Vec::new();
    for _ in 0..3 {
        let witness = left
            .first_value(
                &numeric_forbidden,
                RangeLimits::default(),
                &super::super::NeverCancel,
            )?
            .ok_or_else(|| DatatypeError::invalid("Python fixture numeric witness is absent"))?;
        numeric_witnesses.push(vec![witness.numerator_token(), witness.denominator_token()]);
        numeric_forbidden.push(witness);
    }

    let booleans = BooleanRange::from_values([false]);
    let bool_probes = [false, true];

    let ieee_probe_bits = [
        0xff80_0000,
        0xbf80_0000,
        0x8000_0000,
        0x0000_0000,
        0x3f80_0000,
        0x7f80_0000,
        0x7fc0_0000,
    ];
    let zero = IEEERange::bounded(IEEEFormat::Float32, Some(0), true, Some(0), true)?;
    let finite_unit = IEEERange::bounded(
        IEEEFormat::Float32,
        Some(0xbf80_0000),
        true,
        Some(0x3f80_0000),
        true,
    )?;
    let finite_unit_complement = finite_unit.complement()?;
    let zero_enumeration = zero
        .enumerate_values(RangeLimits::default(), &super::super::NeverCancel)?
        .into_iter()
        .map(|identity| match identity {
            DataIdentity::IEEE { bits, .. } => Ok(format!("{bits:08x}")),
            _ => Err(DatatypeError::invalid(
                "IEEE fixture enumeration returned a different primitive family",
            )),
        })
        .collect::<Result<Vec<_>, _>>()?;

    let lengths = LengthRange::between(2, Some(4))?;
    let length_probes = 0..8;
    let binary = BinaryRange::new(BinaryKind::Hex, LengthRange::between(0, Some(1))?);
    let binary_cardinality = match binary
        .cardinality(RangeLimits::default(), &super::super::NeverCancel)?
    {
        Cardinality::Finite(value) => value.to_string(),
        _ => {
            return Err(DatatypeError::invalid("Python fixture binary range is not finite").into())
        }
    };
    let mut binary_forbidden = Vec::new();
    let mut binary_witnesses = Vec::new();
    for _ in 0..3 {
        let witness = binary
            .first_identity(
                &binary_forbidden,
                RangeLimits::default(),
                &super::super::NeverCancel,
            )?
            .ok_or_else(|| DatatypeError::invalid("Python fixture binary witness is absent"))?;
        let DataIdentity::Binary { octets, .. } = &witness else {
            return Err(DatatypeError::invalid(
                "binary fixture witness returned a different primitive family",
            )
            .into());
        };
        binary_witnesses.push(crate::model::hex(octets));
        binary_forbidden.push(witness);
    }

    let actual = json!({
        "binary": {
            "cardinality": binary_cardinality,
            "witness_hex": binary_witnesses,
        },
        "boolean": {
            "complement": membership_mask(bool_probes.map(|value| booleans.complement().contains(value))),
            "range": membership_mask(bool_probes.map(|value| booleans.contains(value))),
        },
        "ieee": {
            "finite_unit_complement": membership_mask(
                ieee_probe_bits.map(|bits| finite_unit_complement.contains_bits(IEEEFormat::Float32, bits))
            ),
            "probe_bits": ieee_probe_bits.map(|bits| format!("{bits:08x}")),
            "zero_enumeration": zero_enumeration,
        },
        "length": {
            "complement": membership_mask(length_probes.clone().map(|value| lengths.complement().contains(value))),
            "range": membership_mask(length_probes.map(|value| lengths.contains(value))),
        },
        "numeric": {
            "complement": membership_mask_results(integer_probes.iter().map(|value| complement.contains(value)))?,
            "decimal": membership_mask_results(decimal_probes.iter().map(|value| decimal.contains(value)))?,
            "intersection": membership_mask_results(integer_probes.iter().map(|value| intersection.contains(value)))?,
            "left": membership_mask_results(integer_probes.iter().map(|value| left.contains(value)))?,
            "right": membership_mask_results(integer_probes.iter().map(|value| right.contains(value)))?,
            "union": membership_mask_results(integer_probes.iter().map(|value| union.contains(value)))?,
            "witness_tokens": numeric_witnesses,
        },
        "schema_version": 1,
    });
    let expected: serde_json::Value = serde_json::from_str(include_str!("range_oracle_v1.json"))?;
    assert_eq!(actual, expected);
    Ok(())
}

fn membership_mask(values: impl IntoIterator<Item = bool>) -> String {
    values
        .into_iter()
        .map(|value| if value { '1' } else { '0' })
        .collect()
}

fn membership_mask_results(
    values: impl IntoIterator<Item = Result<bool, DatatypeError>>,
) -> Result<String, DatatypeError> {
    values
        .into_iter()
        .map(|value| value.map(|selected| if selected { '1' } else { '0' }))
        .collect()
}
