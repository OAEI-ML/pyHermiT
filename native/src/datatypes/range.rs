//! Exact primitive-family datatype range algebra.
//!
//! This module mirrors the immutable Python numeric, Boolean, IEEE, length, and
//! binary ranges.  It deliberately stops below the mixed-family data-domain DNF
//! and the XML Schema regular-language layer: those are separate WPR3 concerns.
//! All witnesses are backend-private semantic identities.
// SPDX-License-Identifier: LGPL-3.0-or-later

use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};

use num_bigint::{BigInt, BigUint, Sign};
use num_integer::Integer;
use num_traits::{One, Zero};

use super::{BinaryKind, DataIdentity, DatatypeControl, DatatypeError, ExactRational, IEEEFormat};

const POLL_STRIDE: u64 = 64;

/// Resource ceilings for materializing primitive-range results.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RangeLimits {
    pub max_enumeration_values: u64,
    pub max_binary_bytes: u64,
    pub max_cardinality_bits: u64,
    pub max_witness_steps: u64,
}

impl Default for RangeLimits {
    fn default() -> Self {
        Self {
            max_enumeration_values: 100_000,
            max_binary_bytes: 1_000_000,
            max_cardinality_bits: 8_000_008,
            max_witness_steps: 1_000_000,
        }
    }
}

/// Exact cardinality classification.  `Infinite` includes countably and
/// uncountably infinite primitive spaces; the solver only needs the distinction
/// from finite spaces.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Cardinality {
    Empty,
    Finite(BigUint),
    Infinite,
}

/// Allocation-free finite/infinite classification.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CardinalityClass {
    Empty,
    Finite,
    Infinite,
}

impl Cardinality {
    fn finite(value: BigUint) -> Self {
        if value.is_zero() {
            Self::Empty
        } else {
            Self::Finite(value)
        }
    }

    #[must_use]
    pub const fn is_finite(&self) -> bool {
        !matches!(self, Self::Infinite)
    }

    #[must_use]
    pub fn at_least(&self, minimum: u64) -> bool {
        if minimum == 0 {
            return true;
        }
        match self {
            Self::Empty => false,
            Self::Finite(value) => value >= &BigUint::from(minimum),
            Self::Infinite => true,
        }
    }

    #[must_use]
    pub const fn class(&self) -> CardinalityClass {
        match self {
            Self::Empty => CardinalityClass::Empty,
            Self::Finite(_) => CardinalityClass::Finite,
            Self::Infinite => CardinalityClass::Infinite,
        }
    }
}

/// The four nested OWL exact-numeric domains.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum NumericDomain {
    Integer,
    Decimal,
    Rational,
    Real,
}

/// Ordered bound facets shared by numeric and IEEE primitive ranges.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum OrderedFacet {
    MinInclusive,
    MinExclusive,
    MaxInclusive,
    MaxExclusive,
}

/// Length facets shared by strings and the two binary primitive families.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LengthFacet {
    Length,
    MinLength,
    MaxLength,
}

/// Return exact membership in the nested numeric domains.
pub fn numeric_domain_contains(
    domain: NumericDomain,
    value: &ExactRational,
) -> Result<bool, DatatypeError> {
    if domain == NumericDomain::Integer {
        return Ok(rational_parts(value)?.1.is_one());
    }
    if domain == NumericDomain::Decimal {
        let (_, mut denominator) = rational_parts(value)?;
        let two = BigInt::from(2_u8);
        let five = BigInt::from(5_u8);
        while denominator.is_multiple_of(&two) {
            denominator /= &two;
        }
        while denominator.is_multiple_of(&five) {
            denominator /= &five;
        }
        return Ok(denominator.is_one());
    }
    Ok(true)
}

/// One open/closed exact rational interval.  `None` denotes infinity.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NumericInterval {
    lower: Option<ExactRational>,
    lower_inclusive: bool,
    upper: Option<ExactRational>,
    upper_inclusive: bool,
}

impl NumericInterval {
    pub fn new(
        lower: Option<ExactRational>,
        lower_inclusive: bool,
        upper: Option<ExactRational>,
        upper_inclusive: bool,
    ) -> Result<Self, DatatypeError> {
        if lower.is_none() && lower_inclusive {
            return Err(DatatypeError::invalid(
                "negative infinity cannot be inclusive",
            ));
        }
        if upper.is_none() && upper_inclusive {
            return Err(DatatypeError::invalid(
                "positive infinity cannot be inclusive",
            ));
        }
        Ok(Self {
            lower,
            lower_inclusive,
            upper,
            upper_inclusive,
        })
    }

    #[must_use]
    pub const fn unbounded() -> Self {
        Self {
            lower: None,
            lower_inclusive: false,
            upper: None,
            upper_inclusive: false,
        }
    }

    #[must_use]
    pub const fn lower(&self) -> Option<&ExactRational> {
        self.lower.as_ref()
    }

    #[must_use]
    pub const fn lower_inclusive(&self) -> bool {
        self.lower_inclusive
    }

    #[must_use]
    pub const fn upper(&self) -> Option<&ExactRational> {
        self.upper.as_ref()
    }

    #[must_use]
    pub const fn upper_inclusive(&self) -> bool {
        self.upper_inclusive
    }

    pub fn contains(
        &self,
        value: &ExactRational,
        domain: NumericDomain,
    ) -> Result<bool, DatatypeError> {
        if !numeric_domain_contains(domain, value)? {
            return Ok(false);
        }
        if let Some(lower) = &self.lower {
            let comparison = value.compare(lower);
            if comparison == Ordering::Less
                || (comparison == Ordering::Equal && !self.lower_inclusive)
            {
                return Ok(false);
            }
        }
        if let Some(upper) = &self.upper {
            let comparison = value.compare(upper);
            if comparison == Ordering::Greater
                || (comparison == Ordering::Equal && !self.upper_inclusive)
            {
                return Ok(false);
            }
        }
        Ok(true)
    }

    pub fn intersection(&self, other: &Self) -> Result<Self, DatatypeError> {
        let (lower, lower_inclusive) = stronger_lower(self, other);
        let (upper, upper_inclusive) = stronger_upper(self, other);
        Self::new(lower, lower_inclusive, upper, upper_inclusive)
    }

    pub fn is_empty_exact(&self, domain: NumericDomain) -> Result<bool, DatatypeError> {
        if domain == NumericDomain::Integer {
            return Ok(self
                .integer_bounds()?
                .is_some_and(|(lower, upper)| lower > upper));
        }
        let (Some(lower), Some(upper)) = (&self.lower, &self.upper) else {
            return Ok(false);
        };
        match lower.compare(upper) {
            Ordering::Greater => Ok(true),
            Ordering::Less => Ok(false),
            Ordering::Equal => Ok(!(self.lower_inclusive
                && self.upper_inclusive
                && numeric_domain_contains(domain, lower)?)),
        }
    }

    pub fn integer_bounds(&self) -> Result<Option<(BigInt, BigInt)>, DatatypeError> {
        let (Some(lower), Some(upper)) = (&self.lower, &self.upper) else {
            return Ok(None);
        };
        let (lower_numerator, lower_denominator) = rational_parts(lower)?;
        let (upper_numerator, upper_denominator) = rational_parts(upper)?;
        let lower = if self.lower_inclusive {
            lower_numerator.div_ceil(&lower_denominator)
        } else {
            lower_numerator.div_floor(&lower_denominator) + BigInt::one()
        };
        let upper = if self.upper_inclusive {
            upper_numerator.div_floor(&upper_denominator)
        } else {
            upper_numerator.div_ceil(&upper_denominator) - BigInt::one()
        };
        Ok(Some((lower, upper)))
    }

    fn cardinality(&self, domain: NumericDomain) -> Result<Cardinality, DatatypeError> {
        if self.is_empty_exact(domain)? {
            return Ok(Cardinality::Empty);
        }
        if domain == NumericDomain::Integer {
            let Some((lower, upper)) = self.integer_bounds()? else {
                return Ok(Cardinality::Infinite);
            };
            return Ok(Cardinality::finite(nonnegative_biguint(
                upper - lower + BigInt::one(),
            )?));
        }
        if let (Some(lower), Some(upper)) = (&self.lower, &self.upper) {
            if lower.compare(upper) == Ordering::Equal
                && self.lower_inclusive
                && self.upper_inclusive
                && numeric_domain_contains(domain, lower)?
            {
                return Ok(Cardinality::Finite(BigUint::one()));
            }
        }
        Ok(Cardinality::Infinite)
    }
}

/// Canonical union of intervals over one exact numeric domain.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NumericRange {
    domain: NumericDomain,
    intervals: Vec<NumericInterval>,
}

impl NumericRange {
    pub fn new(
        domain: NumericDomain,
        intervals: impl IntoIterator<Item = NumericInterval>,
    ) -> Result<Self, DatatypeError> {
        Ok(Self {
            domain,
            intervals: normalize_numeric(domain, intervals)?,
        })
    }

    #[must_use]
    pub const fn empty(domain: NumericDomain) -> Self {
        Self {
            domain,
            intervals: Vec::new(),
        }
    }

    #[must_use]
    pub fn all(domain: NumericDomain) -> Self {
        Self {
            domain,
            intervals: vec![NumericInterval::unbounded()],
        }
    }

    pub fn between(
        domain: NumericDomain,
        lower: Option<ExactRational>,
        lower_inclusive: bool,
        upper: Option<ExactRational>,
        upper_inclusive: bool,
    ) -> Result<Self, DatatypeError> {
        Self::new(
            domain,
            [NumericInterval::new(
                lower,
                lower_inclusive,
                upper,
                upper_inclusive,
            )?],
        )
    }

    #[must_use]
    pub const fn domain(&self) -> NumericDomain {
        self.domain
    }

    #[must_use]
    pub fn intervals(&self) -> &[NumericInterval] {
        &self.intervals
    }

    pub fn contains(&self, value: &ExactRational) -> Result<bool, DatatypeError> {
        for interval in &self.intervals {
            if interval.contains(value, self.domain)? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    #[must_use]
    pub fn is_empty_exact(&self) -> bool {
        self.intervals.is_empty()
    }

    pub fn intersection(&self, other: &Self) -> Result<Self, DatatypeError> {
        let domain = self.domain.min(other.domain);
        let mut output = Vec::new();
        let (mut left_index, mut right_index) = (0, 0);
        while left_index < self.intervals.len() && right_index < other.intervals.len() {
            let left = &self.intervals[left_index];
            let right = &other.intervals[right_index];
            output.push(left.intersection(right)?);
            match compare_numeric_upper(left, right) {
                Ordering::Less => left_index += 1,
                Ordering::Greater => right_index += 1,
                Ordering::Equal => {
                    left_index += 1;
                    right_index += 1;
                }
            }
        }
        Self::new(domain, output)
    }

    pub fn union(&self, other: &Self) -> Result<Self, DatatypeError> {
        if self.domain != other.domain {
            return Err(DatatypeError::invalid(
                "mixed-domain union requires the full data-domain algebra",
            ));
        }
        Self::new(
            self.domain,
            self.intervals.iter().chain(&other.intervals).cloned(),
        )
    }

    pub fn complement(&self) -> Result<Self, DatatypeError> {
        if self.intervals.is_empty() {
            return Ok(Self::all(self.domain));
        }
        let mut output = Vec::new();
        let mut lower = None;
        let mut lower_inclusive = false;
        for interval in &self.intervals {
            if let Some(interval_lower) = &interval.lower {
                output.push(NumericInterval::new(
                    lower,
                    lower_inclusive,
                    Some(interval_lower.clone()),
                    !interval.lower_inclusive,
                )?);
            }
            let Some(interval_upper) = &interval.upper else {
                return Self::new(self.domain, output);
            };
            lower = Some(interval_upper.clone());
            lower_inclusive = !interval.upper_inclusive;
        }
        output.push(NumericInterval::new(lower, lower_inclusive, None, false)?);
        Self::new(self.domain, output)
    }

    pub fn apply_facet(
        &self,
        facet: OrderedFacet,
        boundary: ExactRational,
    ) -> Result<Self, DatatypeError> {
        let restriction = match facet {
            OrderedFacet::MinInclusive => {
                Self::between(self.domain, Some(boundary), true, None, false)?
            }
            OrderedFacet::MinExclusive => {
                Self::between(self.domain, Some(boundary), false, None, false)?
            }
            OrderedFacet::MaxInclusive => {
                Self::between(self.domain, None, false, Some(boundary), true)?
            }
            OrderedFacet::MaxExclusive => {
                Self::between(self.domain, None, false, Some(boundary), false)?
            }
        };
        self.intersection(&restriction)
    }

    pub fn cardinality(&self) -> Result<Cardinality, DatatypeError> {
        let mut total = BigUint::zero();
        for interval in &self.intervals {
            match interval.cardinality(self.domain)? {
                Cardinality::Empty => {}
                Cardinality::Finite(value) => total += value,
                Cardinality::Infinite => return Ok(Cardinality::Infinite),
            }
        }
        Ok(Cardinality::finite(total))
    }

    pub fn enumerate_values(
        &self,
        limits: RangeLimits,
        control: &impl DatatypeControl,
    ) -> Result<Vec<ExactRational>, DatatypeError> {
        control.poll()?;
        let cardinality = self.cardinality()?;
        let count = materializable_count(&cardinality, limits.max_enumeration_values)?;
        control.observe_memory(count)?;
        let mut output = reserved_vector(count, limits.max_enumeration_values)?;
        let mut work = 0_u64;
        for interval in &self.intervals {
            if self.domain == NumericDomain::Integer {
                let Some((mut current, upper)) = interval.integer_bounds()? else {
                    return Err(DatatypeError::invalid(
                        "finite integer interval has an infinite endpoint",
                    ));
                };
                while current <= upper {
                    output.push(ExactRational::new(current.clone(), BigInt::one())?);
                    current += BigInt::one();
                    poll_work(control, &mut work)?;
                }
            } else if let Some(value) = &interval.lower {
                output.push(value.clone());
                poll_work(control, &mut work)?;
            } else {
                return Err(DatatypeError::invalid(
                    "finite dense interval has no singleton endpoint",
                ));
            }
        }
        control.poll()?;
        Ok(output)
    }

    /// Return the same deterministic rational witness sequence as the Python
    /// primitive-domain oracle, skipping already-used identities.
    pub fn first_value(
        &self,
        excluding: &[ExactRational],
        limits: RangeLimits,
        control: &impl DatatypeControl,
    ) -> Result<Option<ExactRational>, DatatypeError> {
        control.poll()?;
        if self.is_empty_exact() {
            return Ok(None);
        }
        let forbidden: HashSet<ExactRational> = excluding.iter().cloned().collect();
        let mut anchors = vec![rational_from_i64(0)?];
        for interval in &self.intervals {
            if let Some(lower) = &interval.lower {
                anchors.push(lower.clone());
            }
            if let Some(upper) = &interval.upper {
                anchors.push(upper.clone());
            }
            if let (Some(lower), Some(upper)) = (&interval.lower, &interval.upper) {
                anchors.push(midpoint(lower, upper)?);
            }
        }
        let deltas = [
            (0_i64, 1_i64),
            (1, 1),
            (-1, 1),
            (1, 2),
            (-1, 2),
            (1, 3),
            (-1, 3),
            (1, 10),
            (-1, 10),
        ]
        .into_iter()
        .map(|(numerator, denominator)| {
            ExactRational::new(BigInt::from(numerator), BigInt::from(denominator))
        })
        .collect::<Result<Vec<_>, _>>()?;
        let rounds = u64::try_from(forbidden.len())
            .unwrap_or(u64::MAX)
            .saturating_add(3);
        let mut steps = 0_u64;
        for round in 0..rounds {
            for anchor in &anchors {
                for delta in &deltas {
                    steps = steps.checked_add(1).ok_or_else(|| {
                        DatatypeError::resource(
                            "max_witness_steps",
                            u64::MAX,
                            limits.max_witness_steps,
                        )
                    })?;
                    if steps > limits.max_witness_steps {
                        return Err(DatatypeError::resource(
                            "max_witness_steps",
                            steps,
                            limits.max_witness_steps,
                        ));
                    }
                    if steps == 1 || steps % POLL_STRIDE == 0 {
                        control.poll()?;
                    }
                    let shifted = add_integer(delta, round)?;
                    let candidate = add_rational(anchor, &shifted)?;
                    if !forbidden.contains(&candidate) && self.contains(&candidate)? {
                        return Ok(Some(candidate));
                    }
                }
            }
        }
        Ok(None)
    }
}

/// Exact two-element Boolean value-space subset.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct BooleanRange {
    mask: u8,
}

impl BooleanRange {
    const FALSE: u8 = 1;
    const TRUE: u8 = 2;

    #[must_use]
    pub const fn all() -> Self {
        Self {
            mask: Self::FALSE | Self::TRUE,
        }
    }

    #[must_use]
    pub const fn empty() -> Self {
        Self { mask: 0 }
    }

    #[must_use]
    pub fn from_values(values: impl IntoIterator<Item = bool>) -> Self {
        let mut mask = 0;
        for value in values {
            mask |= if value { Self::TRUE } else { Self::FALSE };
        }
        Self { mask }
    }

    #[must_use]
    pub const fn contains(self, value: bool) -> bool {
        self.mask & if value { Self::TRUE } else { Self::FALSE } != 0
    }

    #[must_use]
    pub const fn is_empty_exact(self) -> bool {
        self.mask == 0
    }

    #[must_use]
    pub const fn intersection(self, other: Self) -> Self {
        Self {
            mask: self.mask & other.mask,
        }
    }

    #[must_use]
    pub const fn union(self, other: Self) -> Self {
        Self {
            mask: self.mask | other.mask,
        }
    }

    #[must_use]
    pub const fn complement(self) -> Self {
        Self {
            mask: Self::all().mask & !self.mask,
        }
    }

    #[must_use]
    pub fn cardinality(self) -> Cardinality {
        Cardinality::finite(BigUint::from(self.mask.count_ones()))
    }

    #[must_use]
    pub fn enumerate_values(self) -> Vec<bool> {
        [false, true]
            .into_iter()
            .filter(|value| self.contains(*value))
            .collect()
    }

    #[must_use]
    pub fn first_value(self, excluding: &[bool]) -> Option<bool> {
        [false, true]
            .into_iter()
            .find(|value| self.contains(*value) && !excluding.contains(value))
    }
}

/// Inclusive interval in the non-NaN discrete IEEE ordering.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct IEEEInterval {
    lower_rank: u64,
    upper_rank: u64,
}

impl IEEEInterval {
    #[must_use]
    pub const fn new(lower_rank: u64, upper_rank: u64) -> Self {
        Self {
            lower_rank,
            upper_rank,
        }
    }

    #[must_use]
    pub const fn lower_rank(self) -> u64 {
        self.lower_rank
    }

    #[must_use]
    pub const fn upper_rank(self) -> u64 {
        self.upper_rank
    }

    #[must_use]
    pub const fn is_empty_exact(self) -> bool {
        self.lower_rank > self.upper_rank
    }

    #[must_use]
    pub const fn intersection(self, other: Self) -> Self {
        Self {
            lower_rank: if self.lower_rank > other.lower_rank {
                self.lower_rank
            } else {
                other.lower_rank
            },
            upper_rank: if self.upper_rank < other.upper_rank {
                self.upper_rank
            } else {
                other.upper_rank
            },
        }
    }
}

/// Canonical IEEE rank union plus the singleton canonical NaN identity.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IEEERange {
    format: IEEEFormat,
    intervals: Vec<IEEEInterval>,
    include_nan: bool,
}

impl IEEERange {
    pub fn new(
        format: IEEEFormat,
        intervals: impl IntoIterator<Item = IEEEInterval>,
        include_nan: bool,
    ) -> Result<Self, DatatypeError> {
        let bounds = ieee_rank_bounds(format);
        let intervals = normalize_ieee(intervals);
        for interval in &intervals {
            if interval.lower_rank < bounds.0 || interval.upper_rank > bounds.1 {
                return Err(DatatypeError::invalid(
                    "IEEE interval endpoint is outside the selected format",
                ));
            }
        }
        let (negative_zero, positive_zero) = ieee_zero_ranks(format);
        let has_negative = intervals.iter().any(|interval| {
            interval.lower_rank <= negative_zero && negative_zero <= interval.upper_rank
        });
        let has_positive = intervals.iter().any(|interval| {
            interval.lower_rank <= positive_zero && positive_zero <= interval.upper_rank
        });
        if has_negative != has_positive {
            return Err(DatatypeError::invalid(
                "facet ranges must contain either both signed zeros or neither",
            ));
        }
        Ok(Self {
            format,
            intervals,
            include_nan,
        })
    }

    pub fn all(format: IEEEFormat) -> Result<Self, DatatypeError> {
        let (minimum, maximum) = ieee_rank_bounds(format);
        Self::new(format, [IEEEInterval::new(minimum, maximum)], true)
    }

    #[must_use]
    pub const fn empty(format: IEEEFormat) -> Self {
        Self {
            format,
            intervals: Vec::new(),
            include_nan: false,
        }
    }

    pub fn bounded(
        format: IEEEFormat,
        lower_bits: Option<u64>,
        lower_inclusive: bool,
        upper_bits: Option<u64>,
        upper_inclusive: bool,
    ) -> Result<Self, DatatypeError> {
        let (minimum, maximum) = ieee_rank_bounds(format);
        let mut lower_rank = minimum;
        let mut upper_rank = maximum;
        if let Some(bits) = lower_bits {
            validate_ieee_bits(format, bits)?;
            if ieee_is_nan(format, bits) {
                return Ok(Self::empty(format));
            }
            lower_rank = ieee_lower_rank(format, bits, lower_inclusive)?;
        }
        if let Some(bits) = upper_bits {
            validate_ieee_bits(format, bits)?;
            if ieee_is_nan(format, bits) {
                return Ok(Self::empty(format));
            }
            upper_rank = ieee_upper_rank(format, bits, upper_inclusive)?;
        }
        Self::new(format, [IEEEInterval::new(lower_rank, upper_rank)], false)
    }

    #[must_use]
    pub const fn format(&self) -> IEEEFormat {
        self.format
    }

    #[must_use]
    pub fn intervals(&self) -> &[IEEEInterval] {
        &self.intervals
    }

    #[must_use]
    pub const fn includes_nan(&self) -> bool {
        self.include_nan
    }

    #[must_use]
    pub fn contains_bits(&self, format: IEEEFormat, bits: u64) -> bool {
        if format != self.format || validate_ieee_bits(format, bits).is_err() {
            return false;
        }
        if ieee_is_nan(format, bits) {
            return self.include_nan;
        }
        let rank = ieee_ordered_rank(format, bits);
        self.intervals
            .iter()
            .any(|interval| interval.lower_rank <= rank && rank <= interval.upper_rank)
    }

    #[must_use]
    pub fn contains(&self, value: &DataIdentity) -> bool {
        matches!(
            value,
            DataIdentity::IEEE { format, bits } if self.contains_bits(*format, *bits)
        )
    }

    #[must_use]
    pub fn is_empty_exact(&self) -> bool {
        !self.include_nan && self.intervals.is_empty()
    }

    pub fn intersection(&self, other: &Self) -> Result<Self, DatatypeError> {
        self.require_same_format(other)?;
        let mut output = Vec::new();
        let (mut left_index, mut right_index) = (0, 0);
        while left_index < self.intervals.len() && right_index < other.intervals.len() {
            let left = self.intervals[left_index];
            let right = other.intervals[right_index];
            output.push(left.intersection(right));
            match left.upper_rank.cmp(&right.upper_rank) {
                Ordering::Less => left_index += 1,
                Ordering::Greater => right_index += 1,
                Ordering::Equal => {
                    left_index += 1;
                    right_index += 1;
                }
            }
        }
        Self::new(self.format, output, self.include_nan && other.include_nan)
    }

    pub fn union(&self, other: &Self) -> Result<Self, DatatypeError> {
        self.require_same_format(other)?;
        Self::new(
            self.format,
            self.intervals.iter().chain(&other.intervals).copied(),
            self.include_nan || other.include_nan,
        )
    }

    pub fn complement(&self) -> Result<Self, DatatypeError> {
        let (minimum, maximum) = ieee_rank_bounds(self.format);
        let mut output = Vec::new();
        let mut cursor = minimum;
        for interval in &self.intervals {
            if cursor < interval.lower_rank {
                output.push(IEEEInterval::new(cursor, interval.lower_rank - 1));
            }
            cursor = interval.upper_rank.saturating_add(1);
        }
        if cursor <= maximum {
            output.push(IEEEInterval::new(cursor, maximum));
        }
        Self::new(self.format, output, !self.include_nan)
    }

    pub fn apply_facet(
        &self,
        facet: OrderedFacet,
        boundary_bits: u64,
    ) -> Result<Self, DatatypeError> {
        let restriction = match facet {
            OrderedFacet::MinInclusive => {
                Self::bounded(self.format, Some(boundary_bits), true, None, false)?
            }
            OrderedFacet::MinExclusive => {
                Self::bounded(self.format, Some(boundary_bits), false, None, false)?
            }
            OrderedFacet::MaxInclusive => {
                Self::bounded(self.format, None, false, Some(boundary_bits), true)?
            }
            OrderedFacet::MaxExclusive => {
                Self::bounded(self.format, None, false, Some(boundary_bits), false)?
            }
        };
        self.intersection(&restriction)
    }

    #[must_use]
    pub fn cardinality(&self) -> Cardinality {
        let mut total = BigUint::from(u8::from(self.include_nan));
        for interval in &self.intervals {
            total += BigUint::from(interval.upper_rank - interval.lower_rank + 1);
        }
        Cardinality::finite(total)
    }

    pub fn enumerate_values(
        &self,
        limits: RangeLimits,
        control: &impl DatatypeControl,
    ) -> Result<Vec<DataIdentity>, DatatypeError> {
        control.poll()?;
        let count = materializable_count(&self.cardinality(), limits.max_enumeration_values)?;
        control.observe_memory(count.saturating_mul(16))?;
        let mut output = reserved_vector(count, limits.max_enumeration_values)?;
        let mut work = 0_u64;
        for interval in &self.intervals {
            let mut rank = interval.lower_rank;
            loop {
                output.push(DataIdentity::IEEE {
                    format: self.format,
                    bits: ieee_bits_from_rank(self.format, rank)?,
                });
                poll_work(control, &mut work)?;
                if rank == interval.upper_rank {
                    break;
                }
                rank += 1;
            }
        }
        if self.include_nan {
            output.push(DataIdentity::IEEE {
                format: self.format,
                bits: ieee_canonical_nan(self.format),
            });
        }
        control.poll()?;
        Ok(output)
    }

    pub fn first_identity(
        &self,
        excluding: &[DataIdentity],
        limits: RangeLimits,
        control: &impl DatatypeControl,
    ) -> Result<Option<DataIdentity>, DatatypeError> {
        control.poll()?;
        let mut blocked_ranks = HashSet::new();
        let mut blocked_nan = false;
        for identity in excluding {
            if let DataIdentity::IEEE { format, bits } = identity {
                if *format == self.format && validate_ieee_bits(*format, *bits).is_ok() {
                    if ieee_is_nan(*format, *bits) {
                        blocked_nan = true;
                    } else {
                        blocked_ranks.insert(ieee_ordered_rank(*format, *bits));
                    }
                }
            }
        }
        let mut steps = 0_u64;
        for interval in &self.intervals {
            let mut rank = interval.lower_rank;
            while blocked_ranks.contains(&rank) {
                add_witness_step(&mut steps, limits, control)?;
                if rank == interval.upper_rank {
                    break;
                }
                rank += 1;
            }
            if rank <= interval.upper_rank && !blocked_ranks.contains(&rank) {
                return Ok(Some(DataIdentity::IEEE {
                    format: self.format,
                    bits: ieee_bits_from_rank(self.format, rank)?,
                }));
            }
        }
        if self.include_nan && !blocked_nan {
            return Ok(Some(DataIdentity::IEEE {
                format: self.format,
                bits: ieee_canonical_nan(self.format),
            }));
        }
        Ok(None)
    }

    fn require_same_format(&self, other: &Self) -> Result<(), DatatypeError> {
        if self.format == other.format {
            Ok(())
        } else {
            Err(DatatypeError::invalid(
                "float and double value spaces are disjoint",
            ))
        }
    }
}

/// One inclusive interval over nonnegative lengths.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct LengthInterval {
    lower: u64,
    upper: Option<u64>,
}

impl LengthInterval {
    pub fn new(lower: u64, upper: Option<u64>) -> Result<Self, DatatypeError> {
        if upper.is_some_and(|value| value < lower) {
            return Err(DatatypeError::invalid(
                "length upper endpoint is smaller than its lower endpoint",
            ));
        }
        Ok(Self { lower, upper })
    }

    #[must_use]
    pub const fn lower(self) -> u64 {
        self.lower
    }

    #[must_use]
    pub const fn upper(self) -> Option<u64> {
        self.upper
    }

    #[must_use]
    pub const fn contains(self, length: u64) -> bool {
        self.lower <= length
            && match self.upper {
                Some(upper) => length <= upper,
                None => true,
            }
    }
}

/// Canonical finite union of nonnegative length intervals.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LengthRange {
    intervals: Vec<LengthInterval>,
}

impl LengthRange {
    #[must_use]
    pub fn new(intervals: impl IntoIterator<Item = LengthInterval>) -> Self {
        Self {
            intervals: normalize_lengths(intervals),
        }
    }

    #[must_use]
    pub fn all() -> Self {
        Self::new([LengthInterval {
            lower: 0,
            upper: None,
        }])
    }

    #[must_use]
    pub const fn empty() -> Self {
        Self {
            intervals: Vec::new(),
        }
    }

    pub fn between(minimum: u64, maximum: Option<u64>) -> Result<Self, DatatypeError> {
        Ok(Self::new([LengthInterval::new(minimum, maximum)?]))
    }

    #[must_use]
    pub fn intervals(&self) -> &[LengthInterval] {
        &self.intervals
    }

    #[must_use]
    pub fn contains(&self, length: u64) -> bool {
        self.intervals
            .iter()
            .any(|interval| interval.contains(length))
    }

    #[must_use]
    pub fn is_empty_exact(&self) -> bool {
        self.intervals.is_empty()
    }

    #[must_use]
    pub fn intersection(&self, other: &Self) -> Self {
        let mut output = Vec::new();
        let (mut left_index, mut right_index) = (0, 0);
        while left_index < self.intervals.len() && right_index < other.intervals.len() {
            let left = self.intervals[left_index];
            let right = other.intervals[right_index];
            let lower = left.lower.max(right.lower);
            let upper = min_optional(left.upper, right.upper);
            if upper.is_none_or(|value| lower <= value) {
                output.push(LengthInterval { lower, upper });
            }
            match compare_optional_upper(left.upper, right.upper) {
                Ordering::Less => left_index += 1,
                Ordering::Greater => right_index += 1,
                Ordering::Equal => {
                    left_index += 1;
                    right_index += 1;
                }
            }
        }
        Self::new(output)
    }

    #[must_use]
    pub fn union(&self, other: &Self) -> Self {
        Self::new(self.intervals.iter().chain(&other.intervals).copied())
    }

    #[must_use]
    pub fn complement(&self) -> Self {
        let mut cursor = 0_u64;
        let mut output = Vec::new();
        for interval in &self.intervals {
            if cursor < interval.lower {
                output.push(LengthInterval {
                    lower: cursor,
                    upper: Some(interval.lower - 1),
                });
            }
            let Some(upper) = interval.upper else {
                return Self::new(output);
            };
            let Some(next) = upper.checked_add(1) else {
                return Self::new(output);
            };
            cursor = next;
        }
        output.push(LengthInterval {
            lower: cursor,
            upper: None,
        });
        Self::new(output)
    }

    #[must_use]
    pub fn apply_facet(&self, facet: LengthFacet, boundary: u64) -> Self {
        let restriction = match facet {
            LengthFacet::Length => Self::new([LengthInterval {
                lower: boundary,
                upper: Some(boundary),
            }]),
            LengthFacet::MinLength => Self::new([LengthInterval {
                lower: boundary,
                upper: None,
            }]),
            LengthFacet::MaxLength => Self::new([LengthInterval {
                lower: 0,
                upper: Some(boundary),
            }]),
        };
        self.intersection(&restriction)
    }

    #[must_use]
    pub fn cardinality(&self) -> Cardinality {
        let mut total = BigUint::zero();
        for interval in &self.intervals {
            let Some(upper) = interval.upper else {
                return Cardinality::Infinite;
            };
            total += BigUint::from(upper) - BigUint::from(interval.lower) + BigUint::one();
        }
        Cardinality::finite(total)
    }

    pub fn first_length(
        &self,
        excluding: &HashSet<u64>,
        limits: RangeLimits,
        control: &impl DatatypeControl,
    ) -> Result<Option<u64>, DatatypeError> {
        let mut steps = 0_u64;
        for interval in &self.intervals {
            let mut candidate = interval.lower;
            while excluding.contains(&candidate) {
                add_witness_step(&mut steps, limits, control)?;
                if interval.upper == Some(candidate) || candidate == u64::MAX {
                    break;
                }
                candidate += 1;
            }
            if interval.contains(candidate) && !excluding.contains(&candidate) {
                return Ok(Some(candidate));
            }
        }
        Ok(None)
    }
}

/// A byte-length subset of one disjoint binary primitive value space.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BinaryRange {
    kind: BinaryKind,
    lengths: LengthRange,
}

impl BinaryRange {
    #[must_use]
    pub const fn new(kind: BinaryKind, lengths: LengthRange) -> Self {
        Self { kind, lengths }
    }

    #[must_use]
    pub fn all(kind: BinaryKind) -> Self {
        Self::new(kind, LengthRange::all())
    }

    #[must_use]
    pub const fn empty(kind: BinaryKind) -> Self {
        Self::new(kind, LengthRange::empty())
    }

    #[must_use]
    pub const fn kind(&self) -> BinaryKind {
        self.kind
    }

    #[must_use]
    pub const fn lengths(&self) -> &LengthRange {
        &self.lengths
    }

    #[must_use]
    pub fn contains(&self, value: &DataIdentity) -> bool {
        if let DataIdentity::Binary { kind, octets } = value {
            return *kind == self.kind
                && u64::try_from(octets.len()).is_ok_and(|length| self.lengths.contains(length));
        }
        false
    }

    #[must_use]
    pub fn is_empty_exact(&self) -> bool {
        self.lengths.is_empty_exact()
    }

    pub fn intersection(&self, other: &Self) -> Result<Self, DatatypeError> {
        self.require_same_kind(other)?;
        Ok(Self::new(
            self.kind,
            self.lengths.intersection(&other.lengths),
        ))
    }

    pub fn union(&self, other: &Self) -> Result<Self, DatatypeError> {
        self.require_same_kind(other)?;
        Ok(Self::new(self.kind, self.lengths.union(&other.lengths)))
    }

    #[must_use]
    pub fn complement(&self) -> Self {
        Self::new(self.kind, self.lengths.complement())
    }

    #[must_use]
    pub fn apply_facet(&self, facet: LengthFacet, boundary: u64) -> Self {
        Self::new(self.kind, self.lengths.apply_facet(facet, boundary))
    }

    #[must_use]
    pub fn cardinality_class(&self) -> CardinalityClass {
        match self.lengths.cardinality() {
            Cardinality::Empty => CardinalityClass::Empty,
            Cardinality::Finite(_) => CardinalityClass::Finite,
            Cardinality::Infinite => CardinalityClass::Infinite,
        }
    }

    pub fn cardinality(
        &self,
        limits: RangeLimits,
        control: &impl DatatypeControl,
    ) -> Result<Cardinality, DatatypeError> {
        match self.cardinality_class() {
            CardinalityClass::Empty => return Ok(Cardinality::Empty),
            CardinalityClass::Infinite => return Ok(Cardinality::Infinite),
            CardinalityClass::Finite => {}
        }
        let mut total = BigUint::zero();
        for interval in self.lengths.intervals() {
            let upper = interval.upper.ok_or_else(|| {
                DatatypeError::invalid("finite binary length range became unbounded")
            })?;
            let highest_exponent = upper
                .checked_add(1)
                .and_then(|value| value.checked_mul(8))
                .ok_or_else(|| {
                    DatatypeError::resource(
                        "max_cardinality_bits",
                        u64::MAX,
                        limits.max_cardinality_bits,
                    )
                })?;
            if highest_exponent > limits.max_cardinality_bits {
                return Err(DatatypeError::resource(
                    "max_cardinality_bits",
                    highest_exponent,
                    limits.max_cardinality_bits,
                ));
            }
            control.observe_memory(highest_exponent.saturating_add(7) / 8)?;
            let lower_exponent = interval.lower.checked_mul(8).ok_or_else(|| {
                DatatypeError::resource(
                    "max_cardinality_bits",
                    u64::MAX,
                    limits.max_cardinality_bits,
                )
            })?;
            let high_shift = usize::try_from(highest_exponent).map_err(|_| {
                DatatypeError::resource(
                    "max_cardinality_bits",
                    highest_exponent,
                    limits.max_cardinality_bits,
                )
            })?;
            let low_shift = usize::try_from(lower_exponent).map_err(|_| {
                DatatypeError::resource(
                    "max_cardinality_bits",
                    lower_exponent,
                    limits.max_cardinality_bits,
                )
            })?;
            let numerator = (BigUint::one() << high_shift) - (BigUint::one() << low_shift);
            total += numerator / BigUint::from(255_u16);
            control.poll()?;
        }
        Ok(Cardinality::finite(total))
    }

    /// Return `min(actual cardinality, maximum)` without constructing a giant
    /// integer.  This stays exact even for unbounded byte lengths.
    pub fn cardinality_up_to(
        &self,
        maximum: u64,
        control: &impl DatatypeControl,
    ) -> Result<u64, DatatypeError> {
        control.poll()?;
        if maximum == 0 {
            return Ok(0);
        }
        let mut total = 0_u64;
        for interval in self.lengths.intervals() {
            let mut length = interval.lower;
            loop {
                let remaining = maximum - total;
                if remaining == 0 {
                    return Ok(maximum);
                }
                let exponent = length.saturating_mul(8);
                if exponent >= 64 {
                    return Ok(maximum);
                }
                let term = 1_u64
                    << u32::try_from(exponent).map_err(|_| {
                        DatatypeError::invalid("binary cardinality exponent is not representable")
                    })?;
                if term >= remaining {
                    return Ok(maximum);
                }
                total += term;
                if interval.upper == Some(length) {
                    break;
                }
                if interval.upper.is_none() && length == u64::MAX {
                    return Ok(maximum);
                }
                length += 1;
                control.poll()?;
            }
        }
        Ok(total)
    }

    pub fn cardinality_at_least(
        &self,
        minimum: u64,
        control: &impl DatatypeControl,
    ) -> Result<bool, DatatypeError> {
        Ok(self.cardinality_up_to(minimum, control)? == minimum)
    }

    pub fn enumerate_values(
        &self,
        limits: RangeLimits,
        control: &impl DatatypeControl,
    ) -> Result<Vec<DataIdentity>, DatatypeError> {
        let cap = limits.max_enumeration_values.saturating_add(1);
        let count = self.cardinality_up_to(cap, control)?;
        if count > limits.max_enumeration_values
            || self.cardinality_class() == CardinalityClass::Infinite
        {
            return Err(DatatypeError::resource(
                "max_enumeration_values",
                count.max(cap),
                limits.max_enumeration_values,
            ));
        }
        control.observe_memory(count)?;
        let mut output = reserved_vector(count, limits.max_enumeration_values)?;
        let mut work = 0_u64;
        for interval in self.lengths.intervals() {
            let upper = interval.upper.ok_or_else(|| {
                DatatypeError::invalid("finite binary enumeration interval is unbounded")
            })?;
            let mut length = interval.lower;
            loop {
                if length > limits.max_binary_bytes {
                    return Err(DatatypeError::resource(
                        "max_binary_bytes",
                        length,
                        limits.max_binary_bytes,
                    ));
                }
                let native_length = usize::try_from(length).map_err(|_| {
                    DatatypeError::resource("max_binary_bytes", length, limits.max_binary_bytes)
                })?;
                let mut octets = vec![0_u8; native_length];
                loop {
                    output.push(DataIdentity::Binary {
                        kind: self.kind,
                        octets: octets.clone(),
                    });
                    poll_work(control, &mut work)?;
                    if !increment_octets(&mut octets) {
                        break;
                    }
                }
                if length == upper {
                    break;
                }
                length += 1;
            }
        }
        control.poll()?;
        Ok(output)
    }

    /// Deterministic least-length, then lexicographically least, available value.
    pub fn first_identity(
        &self,
        excluding: &[DataIdentity],
        limits: RangeLimits,
        control: &impl DatatypeControl,
    ) -> Result<Option<DataIdentity>, DatatypeError> {
        control.poll()?;
        let mut by_length: HashMap<u64, HashSet<Vec<u8>>> = HashMap::new();
        for identity in excluding {
            if let DataIdentity::Binary { kind, octets } = identity {
                if *kind == self.kind {
                    let length = u64::try_from(octets.len()).map_err(|_| {
                        DatatypeError::resource(
                            "max_binary_bytes",
                            u64::MAX,
                            limits.max_binary_bytes,
                        )
                    })?;
                    by_length.entry(length).or_default().insert(octets.clone());
                }
            }
        }
        let mut steps = 0_u64;
        for interval in self.lengths.intervals() {
            let mut length = interval.lower;
            loop {
                if length > limits.max_binary_bytes {
                    return Err(DatatypeError::resource(
                        "max_binary_bytes",
                        length,
                        limits.max_binary_bytes,
                    ));
                }
                let native_length = usize::try_from(length).map_err(|_| {
                    DatatypeError::resource("max_binary_bytes", length, limits.max_binary_bytes)
                })?;
                let mut candidate = vec![0_u8; native_length];
                let blocked = by_length.get(&length);
                loop {
                    if blocked.is_none_or(|values| !values.contains(&candidate)) {
                        return Ok(Some(DataIdentity::Binary {
                            kind: self.kind,
                            octets: candidate,
                        }));
                    }
                    add_witness_step(&mut steps, limits, control)?;
                    if !increment_octets(&mut candidate) {
                        break;
                    }
                }
                if interval.upper == Some(length) || length == u64::MAX {
                    break;
                }
                length += 1;
            }
        }
        Ok(None)
    }

    fn require_same_kind(&self, other: &Self) -> Result<(), DatatypeError> {
        if self.kind == other.kind {
            Ok(())
        } else {
            Err(DatatypeError::invalid(
                "hexBinary and base64Binary value spaces are disjoint",
            ))
        }
    }
}

fn normalize_numeric(
    domain: NumericDomain,
    intervals: impl IntoIterator<Item = NumericInterval>,
) -> Result<Vec<NumericInterval>, DatatypeError> {
    let mut retained = Vec::new();
    for interval in intervals {
        if !interval.is_empty_exact(domain)? {
            retained.push(interval);
        }
    }
    retained.sort_by(compare_numeric_lower);
    let mut output: Vec<NumericInterval> = Vec::new();
    for interval in retained {
        if output
            .last()
            .is_some_and(|previous| can_merge_numeric(previous, &interval))
        {
            let previous = output.pop().ok_or_else(|| {
                DatatypeError::invalid("numeric interval normalization lost its predecessor")
            })?;
            output.push(merge_numeric(previous, interval));
        } else {
            output.push(interval);
        }
    }
    Ok(output)
}

fn compare_numeric_lower(left: &NumericInterval, right: &NumericInterval) -> Ordering {
    match (&left.lower, &right.lower) {
        (None, None) => Ordering::Equal,
        (None, Some(_)) => Ordering::Less,
        (Some(_), None) => Ordering::Greater,
        (Some(left_value), Some(right_value)) => {
            let comparison = left_value.compare(right_value);
            if comparison == Ordering::Equal {
                right.lower_inclusive.cmp(&left.lower_inclusive)
            } else {
                comparison
            }
        }
    }
}

fn compare_numeric_upper(left: &NumericInterval, right: &NumericInterval) -> Ordering {
    match (&left.upper, &right.upper) {
        (None, None) => Ordering::Equal,
        (None, Some(_)) => Ordering::Greater,
        (Some(_), None) => Ordering::Less,
        (Some(left_value), Some(right_value)) => left_value.compare(right_value),
    }
}

fn can_merge_numeric(left: &NumericInterval, right: &NumericInterval) -> bool {
    match (&left.upper, &right.lower) {
        (None, _) | (_, None) => true,
        (Some(left_upper), Some(right_lower)) => match left_upper.compare(right_lower) {
            Ordering::Greater => true,
            Ordering::Equal => left.upper_inclusive || right.lower_inclusive,
            Ordering::Less => false,
        },
    }
}

fn merge_numeric(left: NumericInterval, right: NumericInterval) -> NumericInterval {
    let (upper, upper_inclusive) = match (&left.upper, &right.upper) {
        (None, _) | (_, None) => (None, false),
        (Some(left_upper), Some(right_upper)) => match left_upper.compare(right_upper) {
            Ordering::Greater => (Some(left_upper.clone()), left.upper_inclusive),
            Ordering::Less => (Some(right_upper.clone()), right.upper_inclusive),
            Ordering::Equal => (
                Some(left_upper.clone()),
                left.upper_inclusive || right.upper_inclusive,
            ),
        },
    };
    NumericInterval {
        lower: left.lower,
        lower_inclusive: left.lower_inclusive,
        upper,
        upper_inclusive,
    }
}

fn stronger_lower(
    left: &NumericInterval,
    right: &NumericInterval,
) -> (Option<ExactRational>, bool) {
    match (&left.lower, &right.lower) {
        (None, _) => (right.lower.clone(), right.lower_inclusive),
        (_, None) => (left.lower.clone(), left.lower_inclusive),
        (Some(left_value), Some(right_value)) => match left_value.compare(right_value) {
            Ordering::Greater => (Some(left_value.clone()), left.lower_inclusive),
            Ordering::Less => (Some(right_value.clone()), right.lower_inclusive),
            Ordering::Equal => (
                Some(left_value.clone()),
                left.lower_inclusive && right.lower_inclusive,
            ),
        },
    }
}

fn stronger_upper(
    left: &NumericInterval,
    right: &NumericInterval,
) -> (Option<ExactRational>, bool) {
    match (&left.upper, &right.upper) {
        (None, _) => (right.upper.clone(), right.upper_inclusive),
        (_, None) => (left.upper.clone(), left.upper_inclusive),
        (Some(left_value), Some(right_value)) => match left_value.compare(right_value) {
            Ordering::Less => (Some(left_value.clone()), left.upper_inclusive),
            Ordering::Greater => (Some(right_value.clone()), right.upper_inclusive),
            Ordering::Equal => (
                Some(left_value.clone()),
                left.upper_inclusive && right.upper_inclusive,
            ),
        },
    }
}

fn rational_parts(value: &ExactRational) -> Result<(BigInt, BigInt), DatatypeError> {
    Ok((
        parse_canonical_integer(&value.numerator_token())?,
        parse_canonical_integer(&value.denominator_token())?,
    ))
}

fn parse_canonical_integer(value: &str) -> Result<BigInt, DatatypeError> {
    let bytes = value.as_bytes();
    let Some((&sign, digits)) = bytes.split_first() else {
        return Err(DatatypeError::invalid("empty exact rational integer token"));
    };
    if !matches!(sign, b'+' | b'-') || digits.is_empty() {
        return Err(DatatypeError::invalid(
            "malformed exact rational integer token",
        ));
    }
    let magnitude = BigInt::parse_bytes(digits, 16)
        .ok_or_else(|| DatatypeError::invalid("malformed exact rational hexadecimal magnitude"))?;
    Ok(if sign == b'-' { -magnitude } else { magnitude })
}

fn nonnegative_biguint(value: BigInt) -> Result<BigUint, DatatypeError> {
    let (sign, bytes) = value.to_bytes_be();
    if sign == Sign::Minus {
        return Err(DatatypeError::invalid(
            "negative value cannot be used as a cardinality",
        ));
    }
    Ok(BigUint::from_bytes_be(&bytes))
}

fn rational_from_i64(value: i64) -> Result<ExactRational, DatatypeError> {
    ExactRational::new(BigInt::from(value), BigInt::one())
}

fn add_rational(
    left: &ExactRational,
    right: &ExactRational,
) -> Result<ExactRational, DatatypeError> {
    let (left_numerator, left_denominator) = rational_parts(left)?;
    let (right_numerator, right_denominator) = rational_parts(right)?;
    ExactRational::new(
        left_numerator * &right_denominator + right_numerator * &left_denominator,
        left_denominator * right_denominator,
    )
}

fn add_integer(value: &ExactRational, integer: u64) -> Result<ExactRational, DatatypeError> {
    let (numerator, denominator) = rational_parts(value)?;
    ExactRational::new(
        numerator + BigInt::from(integer) * &denominator,
        denominator,
    )
}

fn midpoint(left: &ExactRational, right: &ExactRational) -> Result<ExactRational, DatatypeError> {
    let (left_numerator, left_denominator) = rational_parts(left)?;
    let (right_numerator, right_denominator) = rational_parts(right)?;
    ExactRational::new(
        left_numerator * &right_denominator + right_numerator * &left_denominator,
        BigInt::from(2_u8) * left_denominator * right_denominator,
    )
}

fn normalize_ieee(intervals: impl IntoIterator<Item = IEEEInterval>) -> Vec<IEEEInterval> {
    let mut retained: Vec<_> = intervals
        .into_iter()
        .filter(|interval| !interval.is_empty_exact())
        .collect();
    retained.sort_by_key(|interval| interval.lower_rank);
    let mut output: Vec<IEEEInterval> = Vec::new();
    for interval in retained {
        if let Some(previous) = output.last_mut() {
            if interval.lower_rank <= previous.upper_rank.saturating_add(1) {
                previous.upper_rank = previous.upper_rank.max(interval.upper_rank);
                continue;
            }
        }
        output.push(interval);
    }
    output
}

const fn ieee_width(format: IEEEFormat) -> u32 {
    match format {
        IEEEFormat::Float32 => 32,
        IEEEFormat::Float64 => 64,
    }
}

const fn ieee_fraction_bits(format: IEEEFormat) -> u32 {
    match format {
        IEEEFormat::Float32 => 23,
        IEEEFormat::Float64 => 52,
    }
}

const fn ieee_exponent_bits(format: IEEEFormat) -> u32 {
    match format {
        IEEEFormat::Float32 => 8,
        IEEEFormat::Float64 => 11,
    }
}

const fn ieee_sign_bit(format: IEEEFormat) -> u64 {
    1_u64 << (ieee_width(format) - 1)
}

const fn ieee_width_mask(format: IEEEFormat) -> u64 {
    match format {
        IEEEFormat::Float32 => 0xffff_ffff,
        IEEEFormat::Float64 => u64::MAX,
    }
}

const fn ieee_exponent_mask(format: IEEEFormat) -> u64 {
    (1_u64 << ieee_exponent_bits(format)) - 1
}

const fn ieee_canonical_nan(format: IEEEFormat) -> u64 {
    (ieee_exponent_mask(format) << ieee_fraction_bits(format))
        | (1_u64 << (ieee_fraction_bits(format) - 1))
}

const fn ieee_is_nan(format: IEEEFormat, bits: u64) -> bool {
    let fraction_bits = ieee_fraction_bits(format);
    let exponent = (bits >> fraction_bits) & ieee_exponent_mask(format);
    let fraction = bits & ((1_u64 << fraction_bits) - 1);
    exponent == ieee_exponent_mask(format) && fraction != 0
}

fn validate_ieee_bits(format: IEEEFormat, bits: u64) -> Result<(), DatatypeError> {
    if format == IEEEFormat::Float32 && bits > u64::from(u32::MAX) {
        return Err(DatatypeError::invalid(
            "IEEE bits exceed the selected format width",
        ));
    }
    Ok(())
}

const fn ieee_ordered_rank(format: IEEEFormat, bits: u64) -> u64 {
    if bits & ieee_sign_bit(format) != 0 {
        (!bits) & ieee_width_mask(format)
    } else {
        bits | ieee_sign_bit(format)
    }
}

const fn ieee_rank_bounds(format: IEEEFormat) -> (u64, u64) {
    let positive_infinity = ieee_exponent_mask(format) << ieee_fraction_bits(format);
    let negative_infinity = ieee_sign_bit(format) | positive_infinity;
    (
        ieee_ordered_rank(format, negative_infinity),
        ieee_ordered_rank(format, positive_infinity),
    )
}

const fn ieee_zero_ranks(format: IEEEFormat) -> (u64, u64) {
    (
        ieee_ordered_rank(format, ieee_sign_bit(format)),
        ieee_ordered_rank(format, 0),
    )
}

fn ieee_bits_from_rank(format: IEEEFormat, rank: u64) -> Result<u64, DatatypeError> {
    let (minimum, maximum) = ieee_rank_bounds(format);
    if rank < minimum || rank > maximum {
        return Err(DatatypeError::invalid(
            "rank is outside the non-NaN IEEE value space",
        ));
    }
    let sign_bit = ieee_sign_bit(format);
    Ok(if rank < sign_bit {
        (!rank) & ieee_width_mask(format)
    } else {
        rank & (sign_bit - 1)
    })
}

fn ieee_lower_rank(format: IEEEFormat, bits: u64, inclusive: bool) -> Result<u64, DatatypeError> {
    if bits & (ieee_sign_bit(format) - 1) == 0 {
        let (negative_zero, positive_zero) = ieee_zero_ranks(format);
        return if inclusive {
            Ok(negative_zero)
        } else {
            positive_zero
                .checked_add(1)
                .ok_or_else(|| DatatypeError::invalid("IEEE lower rank overflow"))
        };
    }
    let rank = ieee_ordered_rank(format, bits);
    if inclusive {
        Ok(rank)
    } else {
        rank.checked_add(1)
            .ok_or_else(|| DatatypeError::invalid("IEEE lower rank overflow"))
    }
}

fn ieee_upper_rank(format: IEEEFormat, bits: u64, inclusive: bool) -> Result<u64, DatatypeError> {
    if bits & (ieee_sign_bit(format) - 1) == 0 {
        let (negative_zero, positive_zero) = ieee_zero_ranks(format);
        return if inclusive {
            Ok(positive_zero)
        } else {
            negative_zero
                .checked_sub(1)
                .ok_or_else(|| DatatypeError::invalid("IEEE upper rank underflow"))
        };
    }
    let rank = ieee_ordered_rank(format, bits);
    if inclusive {
        Ok(rank)
    } else {
        rank.checked_sub(1)
            .ok_or_else(|| DatatypeError::invalid("IEEE upper rank underflow"))
    }
}

fn normalize_lengths(intervals: impl IntoIterator<Item = LengthInterval>) -> Vec<LengthInterval> {
    let mut retained: Vec<_> = intervals.into_iter().collect();
    retained.sort_by_key(|interval| interval.lower);
    let mut output: Vec<LengthInterval> = Vec::new();
    for interval in retained {
        if let Some(previous) = output.last_mut() {
            let touches = previous
                .upper
                .is_none_or(|upper| interval.lower <= upper.saturating_add(1));
            if touches {
                previous.upper = max_optional(previous.upper, interval.upper);
                continue;
            }
        }
        output.push(interval);
    }
    output
}

const fn min_optional(left: Option<u64>, right: Option<u64>) -> Option<u64> {
    match (left, right) {
        (Some(left), Some(right)) => Some(if left < right { left } else { right }),
        (Some(value), None) | (None, Some(value)) => Some(value),
        (None, None) => None,
    }
}

const fn max_optional(left: Option<u64>, right: Option<u64>) -> Option<u64> {
    match (left, right) {
        (Some(left), Some(right)) => Some(if left > right { left } else { right }),
        (None, _) | (_, None) => None,
    }
}

const fn compare_optional_upper(left: Option<u64>, right: Option<u64>) -> Ordering {
    match (left, right) {
        (Some(left), Some(right)) => {
            if left < right {
                Ordering::Less
            } else if left > right {
                Ordering::Greater
            } else {
                Ordering::Equal
            }
        }
        (Some(_), None) => Ordering::Less,
        (None, Some(_)) => Ordering::Greater,
        (None, None) => Ordering::Equal,
    }
}

fn materializable_count(cardinality: &Cardinality, maximum: u64) -> Result<u64, DatatypeError> {
    match cardinality {
        Cardinality::Empty => Ok(0),
        Cardinality::Infinite => Err(DatatypeError::resource(
            "max_enumeration_values",
            maximum.saturating_add(1),
            maximum,
        )),
        Cardinality::Finite(value) => {
            let allowed = BigUint::from(maximum);
            if value > &allowed {
                return Err(DatatypeError::resource(
                    "max_enumeration_values",
                    maximum.saturating_add(1),
                    maximum,
                ));
            }
            let digits = value.to_u64_digits();
            match digits.as_slice() {
                [] => Ok(0),
                [count] => Ok(*count),
                _ => Err(DatatypeError::resource(
                    "max_enumeration_values",
                    maximum.saturating_add(1),
                    maximum,
                )),
            }
        }
    }
}

fn reserved_vector<T>(count: u64, maximum: u64) -> Result<Vec<T>, DatatypeError> {
    let capacity = usize::try_from(count)
        .map_err(|_| DatatypeError::resource("max_enumeration_values", count, maximum))?;
    let mut output = Vec::new();
    output
        .try_reserve_exact(capacity)
        .map_err(|_| DatatypeError::resource("max_enumeration_values", count, maximum))?;
    Ok(output)
}

fn poll_work(control: &impl DatatypeControl, work: &mut u64) -> Result<(), DatatypeError> {
    *work = work.saturating_add(1);
    if *work % POLL_STRIDE == 0 {
        control.poll()?;
    }
    Ok(())
}

fn add_witness_step(
    steps: &mut u64,
    limits: RangeLimits,
    control: &impl DatatypeControl,
) -> Result<(), DatatypeError> {
    *steps = steps.checked_add(1).ok_or_else(|| {
        DatatypeError::resource("max_witness_steps", u64::MAX, limits.max_witness_steps)
    })?;
    if *steps > limits.max_witness_steps {
        return Err(DatatypeError::resource(
            "max_witness_steps",
            *steps,
            limits.max_witness_steps,
        ));
    }
    if *steps == 1 || *steps % POLL_STRIDE == 0 {
        control.poll()?;
    }
    Ok(())
}

fn increment_octets(value: &mut [u8]) -> bool {
    for octet in value.iter_mut().rev() {
        if *octet != u8::MAX {
            *octet += 1;
            return true;
        }
        *octet = 0;
    }
    false
}

#[cfg(test)]
#[path = "range_tests.rs"]
mod range_tests;
