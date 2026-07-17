# Copyright 2008, 2009, 2010 by the Oxford University Computing Laboratory
# Modifications Copyright 2026 pyHermiT contributors
# SPDX-License-Identifier: LGPL-3.0-or-later

"""Bit-exact XML Schema float and double lexical mappings.

The range behavior is source-guided by HermiT's ``FloatDatatypeHandler``,
``DoubleDatatypeHandler``, and interval classes at commit ``37ec30a``.  Decimal
conversion is implemented from integer arithmetic and round-to-nearest-even; it
does not delegate semantic decisions to the host floating-point parser.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Final, NoReturn

from pyhermit.events import CancellationToken
from pyhermit.exceptions import InvalidLiteralError, ResourceLimitError

from .model import (
    DatatypeLimits,
    IEEECategory,
    IEEEComparison,
    IEEEFormat,
    IEEEIdentity,
    LexicalCompatibility,
)

_FLOAT_RE: Final = re.compile(
    r"(?:(?P<sign>[+-])?(?P<number>(?:[0-9]+(?:\.[0-9]*)?|\.[0-9]+)"
    r"(?:[eE][+-]?[0-9]+)?)|(?P<special>[+]?INF|-INF|NaN))"
)
_HERMIT_SPECIALS: Final = {
    "Infinity": "+INF",
    "+Infinity": "+INF",
    "-Infinity": "-INF",
}


@dataclass(frozen=True, slots=True)
class _Layout:
    width: int
    exponent_bits: int
    fraction_bits: int
    bias: int

    @property
    def precision(self) -> int:
        return self.fraction_bits + 1

    @property
    def minimum_normal_exponent(self) -> int:
        return 1 - self.bias

    @property
    def maximum_normal_exponent(self) -> int:
        return self.bias

    @property
    def minimum_subnormal_exponent(self) -> int:
        return self.minimum_normal_exponent - self.fraction_bits

    @property
    def exponent_mask(self) -> int:
        return (1 << self.exponent_bits) - 1

    @property
    def fraction_mask(self) -> int:
        return (1 << self.fraction_bits) - 1

    @property
    def sign_bit(self) -> int:
        return 1 << (self.width - 1)


_LAYOUTS: Final = {
    IEEEFormat.FLOAT32: _Layout(32, 8, 23, 127),
    IEEEFormat.FLOAT64: _Layout(64, 11, 52, 1023),
}


def parse_ieee(
    lexical: str,
    format_: IEEEFormat,
    *,
    compatibility: LexicalCompatibility,
    limits: DatatypeLimits,
    cancellation: CancellationToken | None,
) -> tuple[IEEEIdentity, IEEEComparison]:
    """Map one lexical form to exact IEEE identity and comparison records."""

    if not isinstance(lexical, str):
        raise TypeError("lexical must be str")
    if not isinstance(format_, IEEEFormat):
        raise TypeError("format_ must be IEEEFormat")
    if not isinstance(compatibility, LexicalCompatibility):
        raise TypeError("compatibility must be LexicalCompatibility")
    if not isinstance(limits, DatatypeLimits):
        raise TypeError("limits must be DatatypeLimits")
    selected = lexical
    if compatibility is LexicalCompatibility.HERMIT_1_4:
        selected = selected.strip()
        selected = _HERMIT_SPECIALS.get(selected, selected)
    match = _FLOAT_RE.fullmatch(selected)
    if match is None:
        _invalid(format_)
    special = match.group("special")
    layout = _LAYOUTS[format_]
    if special is not None:
        if special in {"INF", "+INF"}:
            bits = layout.exponent_mask << layout.fraction_bits
            category = IEEECategory.POSITIVE_INFINITY
        elif special == "-INF":
            bits = layout.sign_bit | (layout.exponent_mask << layout.fraction_bits)
            category = IEEECategory.NEGATIVE_INFINITY
        else:
            bits = (layout.exponent_mask << layout.fraction_bits) | (
                1 << (layout.fraction_bits - 1)
            )
            category = IEEECategory.NAN
        return IEEEIdentity(format_, bits), IEEEComparison(format_, category)

    number = match.group("number")
    if number is None:
        raise AssertionError("float regular expression produced no number or special value")
    sign = -1 if match.group("sign") == "-" else 1
    numerator, denominator = _decimal_ratio(
        number,
        limits=limits,
        cancellation=cancellation,
    )
    bits = _ratio_to_bits(numerator, denominator, sign=sign, layout=layout)
    identity = IEEEIdentity(format_, bits)
    return identity, comparison_from_identity(identity)


def comparison_from_identity(identity: IEEEIdentity) -> IEEEComparison:
    """Decode exact rational/category comparison semantics from identity bits."""

    if not isinstance(identity, IEEEIdentity):
        raise TypeError("identity must be IEEEIdentity")
    layout = _LAYOUTS[identity.format]
    bits = identity.bits
    exponent = (bits >> layout.fraction_bits) & layout.exponent_mask
    fraction = bits & layout.fraction_mask
    negative = bool(bits & layout.sign_bit)
    if exponent == layout.exponent_mask:
        if fraction:
            return IEEEComparison(identity.format, IEEECategory.NAN)
        return IEEEComparison(
            identity.format,
            IEEECategory.NEGATIVE_INFINITY if negative else IEEECategory.POSITIVE_INFINITY,
        )
    if exponent == 0:
        significand = fraction
        binary_exponent = layout.minimum_subnormal_exponent
    else:
        significand = (1 << layout.fraction_bits) | fraction
        binary_exponent = exponent - layout.bias - layout.fraction_bits
    if negative:
        significand = -significand
    if binary_exponent >= 0:
        return IEEEComparison(
            identity.format,
            IEEECategory.FINITE,
            significand << binary_exponent,
            1,
        )
    return IEEEComparison(
        identity.format,
        IEEECategory.FINITE,
        significand,
        1 << (-binary_exponent),
    )


def identity_from_comparison(comparison: IEEEComparison) -> IEEEIdentity:
    """Recover the unique nonzero IEEE identity (and positive identity for zero)."""

    if not isinstance(comparison, IEEEComparison):
        raise TypeError("comparison must be IEEEComparison")
    layout = _LAYOUTS[comparison.format]
    if comparison.category is IEEECategory.NAN:
        return IEEEIdentity(
            comparison.format,
            (layout.exponent_mask << layout.fraction_bits) | (1 << (layout.fraction_bits - 1)),
        )
    if comparison.category is IEEECategory.NEGATIVE_INFINITY:
        return IEEEIdentity(
            comparison.format,
            layout.sign_bit | (layout.exponent_mask << layout.fraction_bits),
        )
    if comparison.category is IEEECategory.POSITIVE_INFINITY:
        return IEEEIdentity(
            comparison.format,
            layout.exponent_mask << layout.fraction_bits,
        )
    sign = -1 if comparison.numerator < 0 else 1
    bits = _ratio_to_bits(
        abs(comparison.numerator),
        comparison.denominator,
        sign=sign,
        layout=layout,
    )
    identity = IEEEIdentity(comparison.format, bits)
    if comparison_from_identity(identity) != comparison:
        raise ValueError("comparison does not denote an exactly representable IEEE value")
    return identity


def ordered_rank(identity: IEEEIdentity) -> int:
    """Return the discrete non-NaN order rank, distinguishing both zeros."""

    comparison = comparison_from_identity(identity)
    if comparison.category is IEEECategory.NAN:
        raise ValueError("NaN has no ordered rank")
    width_mask = (1 << identity.format.width) - 1
    sign_bit = 1 << (identity.format.width - 1)
    if identity.bits & sign_bit:
        return (~identity.bits) & width_mask
    return identity.bits | sign_bit


def identity_from_ordered_rank(format_: IEEEFormat, rank: int) -> IEEEIdentity:
    """Invert :func:`ordered_rank` for a rank between -INF and +INF."""

    if not isinstance(format_, IEEEFormat):
        raise TypeError("format_ must be IEEEFormat")
    if isinstance(rank, bool) or not isinstance(rank, int):
        raise TypeError("rank must be int")
    minimum, maximum = rank_bounds(format_)
    if not minimum <= rank <= maximum:
        raise ValueError("rank is outside the non-NaN IEEE value space")
    width_mask = (1 << format_.width) - 1
    sign_bit = 1 << (format_.width - 1)
    bits = (~rank) & width_mask if rank < sign_bit else rank & (sign_bit - 1)
    return IEEEIdentity(format_, bits)


def rank_bounds(format_: IEEEFormat) -> tuple[int, int]:
    if not isinstance(format_, IEEEFormat):
        raise TypeError("format_ must be IEEEFormat")
    layout = _LAYOUTS[format_]
    negative_infinity = IEEEIdentity(
        format_, layout.sign_bit | (layout.exponent_mask << layout.fraction_bits)
    )
    positive_infinity = IEEEIdentity(format_, layout.exponent_mask << layout.fraction_bits)
    return ordered_rank(negative_infinity), ordered_rank(positive_infinity)


def zero_ranks(format_: IEEEFormat) -> tuple[int, int]:
    layout = _LAYOUTS[format_]
    return ordered_rank(IEEEIdentity(format_, layout.sign_bit)), ordered_rank(
        IEEEIdentity(format_, 0)
    )


def _decimal_ratio(
    value: str,
    *,
    limits: DatatypeLimits,
    cancellation: CancellationToken | None,
) -> tuple[int, int]:
    exponent = 0
    exponent_index = max(value.find("e"), value.find("E"))
    if exponent_index >= 0:
        mantissa = value[:exponent_index]
        exponent_text = value[exponent_index + 1 :]
        exponent_negative = exponent_text.startswith("-")
        if exponent_text[:1] in {"+", "-"}:
            exponent_text = exponent_text[1:]
        exponent_magnitude = _parse_digits(
            exponent_text,
            limits=limits,
            cancellation=cancellation,
        )
        if exponent_magnitude > limits.max_decimal_exponent:
            raise ResourceLimitError(
                "floating-point exponent exceeds the configured magnitude limit",
                limit="max_decimal_exponent",
                observed=limits.max_decimal_exponent + 1,
                allowed=limits.max_decimal_exponent,
            )
        exponent = -exponent_magnitude if exponent_negative else exponent_magnitude
    else:
        mantissa = value
    if "." in mantissa:
        whole, fraction = mantissa.split(".", 1)
    else:
        whole, fraction = mantissa, ""
    digits = (whole or "0") + fraction
    numerator = _parse_digits(digits, limits=limits, cancellation=cancellation)
    scale = len(fraction) - exponent
    if abs(scale) > limits.max_decimal_exponent:
        raise ResourceLimitError(
            "floating-point decimal scale exceeds the configured magnitude limit",
            limit="max_decimal_exponent",
            observed=abs(scale),
            allowed=limits.max_decimal_exponent,
        )
    _poll(cancellation)
    if scale > 0:
        return numerator, 10**scale
    if scale < 0:
        return numerator * 10 ** (-scale), 1
    return numerator, 1


def _ratio_to_bits(numerator: int, denominator: int, *, sign: int, layout: _Layout) -> int:
    if numerator == 0:
        return layout.sign_bit if sign < 0 else 0
    exponent = _floor_log2_ratio(numerator, denominator)
    if exponent < layout.minimum_normal_exponent:
        significand = _round_scaled_ratio(
            numerator,
            denominator,
            -layout.minimum_subnormal_exponent,
        )
        if significand == 0:
            return layout.sign_bit if sign < 0 else 0
        # Rounding can promote the largest subnormal to the minimum normal.
        bits = significand if significand < 1 << layout.fraction_bits else 1 << layout.fraction_bits
    else:
        significand = _round_scaled_ratio(
            numerator,
            denominator,
            layout.fraction_bits - exponent,
        )
        if significand == 1 << layout.precision:
            significand >>= 1
            exponent += 1
        if exponent > layout.maximum_normal_exponent:
            bits = layout.exponent_mask << layout.fraction_bits
        else:
            exponent_field = exponent + layout.bias
            bits = (exponent_field << layout.fraction_bits) | (
                significand - (1 << layout.fraction_bits)
            )
    return bits | (layout.sign_bit if sign < 0 else 0)


def _floor_log2_ratio(numerator: int, denominator: int) -> int:
    estimate = numerator.bit_length() - denominator.bit_length()
    if estimate >= 0:
        return estimate - 1 if numerator < denominator << estimate else estimate
    return estimate - 1 if numerator << (-estimate) < denominator else estimate


def _round_scaled_ratio(numerator: int, denominator: int, shift: int) -> int:
    if shift >= 0:
        numerator <<= shift
    else:
        denominator <<= -shift
    quotient, remainder = divmod(numerator, denominator)
    doubled = remainder << 1
    if doubled > denominator or (doubled == denominator and quotient & 1):
        quotient += 1
    return quotient


def _parse_digits(
    digits: str,
    *,
    limits: DatatypeLimits,
    cancellation: CancellationToken | None,
) -> int:
    count = len(digits)
    if count > limits.max_numeric_digits:
        raise ResourceLimitError(
            "floating-point lexical form exceeds the configured digit limit",
            limit="max_numeric_digits",
            observed=count,
            allowed=limits.max_numeric_digits,
        )
    if count <= 512:
        return int(digits)
    value = 0
    blocks_since_poll = 0
    for start in range(0, count, 9):
        block = digits[start : start + 9]
        value = value * 10 ** len(block) + int(block)
        blocks_since_poll += 1
        if blocks_since_poll == limits.cancellation_poll_stride:
            _poll(cancellation, blocks_since_poll)
            blocks_since_poll = 0
    _poll(cancellation, blocks_since_poll)
    return value


def _poll(cancellation: CancellationToken | None, work: int = 0) -> None:
    if cancellation is None:
        return
    if work:
        cancellation.add_work(work)
    cancellation.check()


def _invalid(format_: IEEEFormat) -> NoReturn:
    raise InvalidLiteralError(
        "literal lexical form is outside the datatype lexical space",
        context={
            "datatype_iri": "http://www.w3.org/2001/XMLSchema#"
            + ("float" if format_ is IEEEFormat.FLOAT32 else "double")
        },
    )


__all__ = [
    "comparison_from_identity",
    "identity_from_comparison",
    "identity_from_ordered_rank",
    "ordered_rank",
    "parse_ieee",
    "rank_bounds",
    "zero_ranks",
]
