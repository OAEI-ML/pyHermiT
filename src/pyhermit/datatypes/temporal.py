# Copyright 2008, 2009, 2010 by the Oxford University Computing Laboratory
# Modifications Copyright 2026 pyHermiT contributors
# SPDX-License-Identifier: LGPL-3.0-or-later

"""Arbitrary-year, exact-fraction XML Schema dateTime semantics."""

from __future__ import annotations

import re
from typing import Final, NoReturn

from pyhermit.events import CancellationToken
from pyhermit.exceptions import InvalidLiteralError, ResourceLimitError

from .model import (
    DatatypeLimits,
    DateTimeComparison,
    DateTimeIdentity,
    LexicalCompatibility,
)

XSD_NAMESPACE: Final = "http://www.w3.org/2001/XMLSchema#"
XSD_DATE_TIME: Final = XSD_NAMESPACE + "dateTime"
XSD_DATE_TIME_STAMP: Final = XSD_NAMESPACE + "dateTimeStamp"

_DATE_TIME = re.compile(
    r"(?P<year>-?(?:[1-9][0-9]{3,}|0[0-9]{3}))-"
    r"(?P<month>0[1-9]|1[0-2])-"
    r"(?P<day>0[1-9]|[12][0-9]|3[01])T"
    r"(?:(?P<hour>[01][0-9]|2[0-3]):(?P<minute>[0-5][0-9]):"
    r"(?P<second>[0-5][0-9])(?:\.(?P<fraction>[0-9]+))?"
    r"|(?P<end>24:00:00)(?:\.(?P<end_fraction>0+))?)"
    r"(?P<timezone>Z|[+-](?:(?:0[0-9]|1[0-3]):[0-5][0-9]|14:00))?"
)
_HERMIT_DATE_TIME = re.compile(
    r"(?P<year>-?[0-9]{4,})-(?P<month>[0-9]{2})-(?P<day>[0-9]{2})T"
    r"(?P<hour>[0-9]{2}):(?P<minute>[0-9]{2}):(?P<second>[0-9]{2})"
    r"(?:\.(?P<fraction>[0-9]{1,3}))?"
    r"(?P<timezone>Z|[+-][0-9]{2}:[0-9]{2})?"
)


def compile_date_time(
    lexical: str,
    *,
    require_timezone: bool,
    compatibility: LexicalCompatibility,
    limits: DatatypeLimits,
    cancellation: CancellationToken | None,
) -> tuple[DateTimeIdentity, DateTimeComparison]:
    """Compile dateTime/dateTimeStamp without ``datetime`` or host time zones."""

    if not isinstance(lexical, str):
        raise TypeError("lexical must be str")
    if not isinstance(require_timezone, bool):
        raise TypeError("require_timezone must be bool")
    selected = _collapse_xml_whitespace(lexical)
    pattern = _HERMIT_DATE_TIME if compatibility is LexicalCompatibility.HERMIT_1_4 else _DATE_TIME
    match = pattern.fullmatch(selected)
    datatype_iri = XSD_DATE_TIME_STAMP if require_timezone else XSD_DATE_TIME
    if match is None:
        _invalid(datatype_iri)
    year = _parse_signed_digits(match.group("year"), limits=limits, cancellation=cancellation)
    if (
        compatibility is LexicalCompatibility.OWL2
        and match.group("year").startswith("-")
        and year == 0
    ):
        _invalid(datatype_iri)
    month = int(match.group("month"))
    day = int(match.group("day"))
    if day > _days_in_month(year, month):
        _invalid(datatype_iri)

    hermit_end_of_day = False
    if compatibility is LexicalCompatibility.HERMIT_1_4:
        if not -9999 <= year <= 9999:
            _invalid(datatype_iri)
        hour = int(match.group("hour"))
        minute = int(match.group("minute"))
        second = int(match.group("second"))
        fraction_text = match.group("fraction") or ""
        if (
            hour > 24
            or minute > 59
            or second > 59
            or (hour == 24 and (minute or second or any(char != "0" for char in fraction_text)))
        ):
            _invalid(datatype_iri)
        hermit_end_of_day = hour == 24
    else:
        end_of_day = match.group("end") is not None
        hour = 24 if end_of_day else int(match.group("hour"))
        minute = 0 if end_of_day else int(match.group("minute"))
        second = 0 if end_of_day else int(match.group("second"))
        fraction_text = (
            match.group("end_fraction") if end_of_day else match.group("fraction")
        ) or ""

    fraction_numerator = 0
    fraction_denominator = 1
    if fraction_text:
        fraction_numerator = _parse_unsigned_digits(
            fraction_text,
            limits=limits,
            cancellation=cancellation,
        )
        fraction_denominator = 10 ** len(fraction_text)

    timezone = match.group("timezone")
    if require_timezone and timezone is None:
        _invalid(datatype_iri)
    offset = _timezone_offset(timezone, datatype_iri)
    days = _days_before_year(year) + _days_before_month(year, month) + day - 1
    whole_seconds = days * 86_400 + hour * 3_600 + minute * 60 + second
    local_numerator = whole_seconds * fraction_denominator + fraction_numerator
    identity = DateTimeIdentity(
        local_numerator,
        fraction_denominator,
        offset,
        hermit_end_of_day=hermit_end_of_day,
    )
    comparison = DateTimeComparison(local_numerator, fraction_denominator, offset)
    _poll(cancellation)
    return identity, comparison


def _timezone_offset(timezone: str | None, datatype_iri: str) -> int | None:
    if timezone is None:
        return None
    if timezone == "Z":
        return 0
    sign = -1 if timezone[0] == "-" else 1
    hour = int(timezone[1:3])
    minute = int(timezone[4:6])
    if hour > 14 or minute > 59 or (hour == 14 and minute != 0):
        _invalid(datatype_iri)
    return sign * (hour * 60 + minute)


def _days_before_year(year: int) -> int:
    prior = year - 1
    return 365 * prior + prior // 4 - prior // 100 + prior // 400


def _days_before_month(year: int, month: int) -> int:
    total = 0
    for selected in range(1, month):
        total += _days_in_month(year, selected)
    return total


def _days_in_month(year: int, month: int) -> int:
    if month == 2:
        return 29 if year % 4 == 0 and (year % 100 != 0 or year % 400 == 0) else 28
    return 30 if month in {4, 6, 9, 11} else 31


def _parse_signed_digits(
    value: str,
    *,
    limits: DatatypeLimits,
    cancellation: CancellationToken | None,
) -> int:
    negative = value.startswith("-")
    digits = value[1:] if negative else value
    result = _parse_unsigned_digits(digits, limits=limits, cancellation=cancellation)
    return -result if negative else result


def _parse_unsigned_digits(
    digits: str,
    *,
    limits: DatatypeLimits,
    cancellation: CancellationToken | None,
) -> int:
    if len(digits) > limits.max_numeric_digits:
        raise ResourceLimitError(
            "date/time lexical form exceeds the configured digit limit",
            limit="max_numeric_digits",
            observed=len(digits),
            allowed=limits.max_numeric_digits,
        )
    if len(digits) <= 512:
        return int(digits)
    value = 0
    since_poll = 0
    for start in range(0, len(digits), 9):
        block = digits[start : start + 9]
        value = value * 10 ** len(block) + int(block)
        since_poll += 1
        if since_poll == limits.cancellation_poll_stride:
            _poll(cancellation, since_poll)
            since_poll = 0
    _poll(cancellation, since_poll)
    return value


def _collapse_xml_whitespace(value: str) -> str:
    replaced = value.translate({0x9: 0x20, 0xA: 0x20, 0xD: 0x20})
    return " ".join(part for part in replaced.split(" ") if part)


def _poll(cancellation: CancellationToken | None, work: int = 0) -> None:
    if cancellation is None:
        return
    if work:
        cancellation.add_work(work)
    cancellation.check()


def _invalid(datatype_iri: str) -> NoReturn:
    raise InvalidLiteralError(
        "literal lexical form is outside the datatype lexical space",
        context={"datatype_iri": datatype_iri},
    )


__all__ = [
    "XSD_DATE_TIME",
    "XSD_DATE_TIME_STAMP",
    "compile_date_time",
]
