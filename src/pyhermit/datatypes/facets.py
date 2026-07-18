# Copyright 2008, 2009, 2010 by the Oxford University Computing Laboratory
# Modifications Copyright 2026 pyHermiT contributors
# SPDX-License-Identifier: LGPL-3.0-or-later
# Adapted from HermiT commit 37ec30aced32ac81ebecc5e33fad255ddefcb4c3;
# see reports/licensing/adapted-files.toml.

"""Validated OWL 2 facet compilation into exact immutable data ranges."""

from __future__ import annotations

from collections.abc import Iterable
from dataclasses import dataclass
from typing import Final, NoReturn, cast

from pyhermit.events import CancellationToken
from pyhermit.exceptions import OntologyProfileError

from .binary import XSD_BASE64_BINARY, XSD_HEX_BINARY
from .ieee_ranges import IEEERange
from .language_tags import LanguageTagRange
from .literals import (
    NUMERIC_DATATYPES,
    RDFS_LITERAL,
    XSD_BOOLEAN,
    XSD_DOUBLE,
    XSD_FLOAT,
    XSD_NAMESPACE,
)
from .model import (
    CompiledLiteral,
    DatatypeLimits,
    DateTimeComparison,
    IEEEComparison,
    IEEEFormat,
    NumericComparison,
    NumericIdentity,
    StringIdentity,
)
from .nonnumeric_ranges import (
    BinaryRange,
    LengthRange,
    StringRange,
    URIRange,
    length_regex,
)
from .ranges import DatatypeRange, NumericRange, range_for_datatype
from .temporal import XSD_DATE_TIME, XSD_DATE_TIME_STAMP
from .temporal_ranges import DateTimeRange
from .textual import RDF_NAMESPACE, RDF_PLAIN_LITERAL, STRING_DATATYPES, XSD_ANY_URI
from .xml_literal import RDF_XML_LITERAL
from .xsd_regex import XSDRegex

XSD_MIN_INCLUSIVE: Final = XSD_NAMESPACE + "minInclusive"
XSD_MIN_EXCLUSIVE: Final = XSD_NAMESPACE + "minExclusive"
XSD_MAX_INCLUSIVE: Final = XSD_NAMESPACE + "maxInclusive"
XSD_MAX_EXCLUSIVE: Final = XSD_NAMESPACE + "maxExclusive"
XSD_LENGTH: Final = XSD_NAMESPACE + "length"
XSD_MIN_LENGTH: Final = XSD_NAMESPACE + "minLength"
XSD_MAX_LENGTH: Final = XSD_NAMESPACE + "maxLength"
XSD_PATTERN: Final = XSD_NAMESPACE + "pattern"
RDF_LANG_RANGE: Final = RDF_NAMESPACE + "langRange"

_LOWER_FACETS: Final = frozenset((XSD_MIN_INCLUSIVE, XSD_MIN_EXCLUSIVE))
_UPPER_FACETS: Final = frozenset((XSD_MAX_INCLUSIVE, XSD_MAX_EXCLUSIVE))
_BOUND_FACETS: Final = _LOWER_FACETS | _UPPER_FACETS
_LENGTH_FACETS: Final = frozenset((XSD_LENGTH, XSD_MIN_LENGTH, XSD_MAX_LENGTH))


@dataclass(frozen=True, slots=True)
class FacetRestriction:
    """One facet IRI and its already compiled, source-preserving literal value."""

    facet_iri: str
    value: CompiledLiteral

    def __post_init__(self) -> None:
        if not isinstance(self.facet_iri, str) or not self.facet_iri:
            raise ValueError("facet_iri must be a nonempty string")
        if not isinstance(self.value, CompiledLiteral):
            raise TypeError("value must be CompiledLiteral")


def restrict_datatype(
    datatype_iri: str,
    facets: Iterable[FacetRestriction],
    *,
    limits: DatatypeLimits | None = None,
    cancellation: CancellationToken | None = None,
) -> DatatypeRange:
    """Validate and intersect all facets with one built-in datatype range."""

    if not isinstance(datatype_iri, str):
        raise TypeError("datatype_iri must be str")
    selected_limits = _controls(limits, cancellation)
    try:
        restrictions = tuple(facets)
    except TypeError as error:
        raise TypeError("facets must be an iterable of FacetRestriction values") from error
    if not all(isinstance(facet, FacetRestriction) for facet in restrictions):
        raise TypeError("facets must contain FacetRestriction values")
    result = range_for_datatype(datatype_iri)
    for restriction in restrictions:
        _poll(cancellation, 1)
        result = _apply_facet(
            datatype_iri,
            result,
            restriction,
            limits=selected_limits,
            cancellation=cancellation,
        )
    _poll(cancellation)
    return result


def _apply_facet(
    datatype_iri: str,
    range_: DatatypeRange,
    facet: FacetRestriction,
    *,
    limits: DatatypeLimits,
    cancellation: CancellationToken | None,
) -> DatatypeRange:
    facet_iri = facet.facet_iri
    if datatype_iri in NUMERIC_DATATYPES:
        _require_facet(datatype_iri, facet_iri, _BOUND_FACETS)
        comparison = facet.value.comparison
        if not isinstance(comparison, NumericComparison):
            _invalid_value(datatype_iri, facet_iri, "an exact owl:real-family number")
        numeric_range = cast(NumericRange, range_)
        numeric_bound = _numeric_bound(numeric_range, facet_iri, comparison)
        return numeric_range.intersection(numeric_bound)

    if datatype_iri in {XSD_FLOAT, XSD_DOUBLE}:
        _require_facet(datatype_iri, facet_iri, _BOUND_FACETS)
        comparison = facet.value.comparison
        expected = IEEEFormat.FLOAT32 if datatype_iri == XSD_FLOAT else IEEEFormat.FLOAT64
        if not isinstance(comparison, IEEEComparison) or comparison.format is not expected:
            _invalid_value(datatype_iri, facet_iri, datatype_iri)
        ieee_range = cast(IEEERange, range_)
        ieee_bound = _ieee_bound(expected, facet_iri, facet.value)
        return ieee_range.intersection(ieee_bound)

    if datatype_iri in {XSD_DATE_TIME, XSD_DATE_TIME_STAMP}:
        _require_facet(datatype_iri, facet_iri, _BOUND_FACETS)
        comparison = facet.value.comparison
        if not isinstance(comparison, DateTimeComparison):
            _invalid_value(datatype_iri, facet_iri, "xsd:dateTime or xsd:dateTimeStamp")
        date_time_range = cast(DateTimeRange, range_)
        date_time_bound = _date_time_bound(
            facet_iri,
            facet.value,
            require_timezone=datatype_iri == XSD_DATE_TIME_STAMP,
        )
        return date_time_range.intersection(date_time_bound)

    if datatype_iri in {XSD_HEX_BINARY, XSD_BASE64_BINARY}:
        _require_facet(datatype_iri, facet_iri, _LENGTH_FACETS)
        binary_range = cast(BinaryRange, range_)
        return BinaryRange(
            binary_range.kind,
            binary_range.lengths.intersection(_length_bound(datatype_iri, facet_iri, facet.value)),
        )

    if datatype_iri in STRING_DATATYPES:
        allowed = _LENGTH_FACETS | {XSD_PATTERN}
        if datatype_iri == RDF_PLAIN_LITERAL:
            allowed |= {RDF_LANG_RANGE}
        _require_facet(datatype_iri, facet_iri, allowed)
        string_range = cast(StringRange, range_)
        if facet_iri in _LENGTH_FACETS:
            return string_range.with_text_pattern(
                length_regex(
                    _length_bound(datatype_iri, facet_iri, facet.value),
                    limits=limits,
                    cancellation=cancellation,
                )
            )
        text = _string_facet_value(datatype_iri, facet_iri, facet.value)
        if facet_iri == XSD_PATTERN:
            return string_range.with_text_pattern(
                XSDRegex.compile(text, limits=limits, cancellation=cancellation)
            )
        return string_range.with_text_language(_language_tag_range(text))

    if datatype_iri == XSD_ANY_URI:
        _require_facet(datatype_iri, facet_iri, _LENGTH_FACETS | {XSD_PATTERN})
        uri_range = cast(URIRange, range_)
        if facet_iri in _LENGTH_FACETS:
            restriction = length_regex(
                _length_bound(datatype_iri, facet_iri, facet.value),
                limits=limits,
                cancellation=cancellation,
            )
        else:
            restriction = XSDRegex.compile(
                _string_facet_value(datatype_iri, facet_iri, facet.value),
                limits=limits,
                cancellation=cancellation,
            )
        return URIRange(
            uri_range.universe,
            uri_range.language.intersection(restriction),
        )

    if datatype_iri not in {XSD_BOOLEAN, RDF_XML_LITERAL, RDFS_LITERAL}:
        raise AssertionError("implemented datatype has no facet dispatch")
    _require_facet(datatype_iri, facet_iri, frozenset())
    raise AssertionError("unsupported facet validation unexpectedly returned")


def _numeric_bound(
    range_: NumericRange,
    facet_iri: str,
    comparison: NumericComparison,
) -> NumericRange:
    if facet_iri in _LOWER_FACETS:
        return NumericRange.between(
            range_.domain,
            lower=comparison,
            lower_inclusive=facet_iri == XSD_MIN_INCLUSIVE,
        )
    return NumericRange.between(
        range_.domain,
        upper=comparison,
        upper_inclusive=facet_iri == XSD_MAX_INCLUSIVE,
    )


def _ieee_bound(
    format_: IEEEFormat,
    facet_iri: str,
    value: CompiledLiteral,
) -> IEEERange:
    if facet_iri in _LOWER_FACETS:
        return IEEERange.bounded(
            format_,
            lower=value,
            lower_inclusive=facet_iri == XSD_MIN_INCLUSIVE,
        )
    return IEEERange.bounded(
        format_,
        upper=value,
        upper_inclusive=facet_iri == XSD_MAX_INCLUSIVE,
    )


def _date_time_bound(
    facet_iri: str,
    value: CompiledLiteral,
    *,
    require_timezone: bool,
) -> DateTimeRange:
    if facet_iri in _LOWER_FACETS:
        return DateTimeRange.bounded(
            require_timezone=require_timezone,
            lower=value,
            lower_inclusive=facet_iri == XSD_MIN_INCLUSIVE,
        )
    return DateTimeRange.bounded(
        require_timezone=require_timezone,
        upper=value,
        upper_inclusive=facet_iri == XSD_MAX_INCLUSIVE,
    )


def _length_bound(
    datatype_iri: str,
    facet_iri: str,
    value: CompiledLiteral,
) -> LengthRange:
    identity = value.data_identity
    if not isinstance(identity, NumericIdentity) or identity.denominator != 1:
        _invalid_value(datatype_iri, facet_iri, "a nonnegative integer")
    length = identity.numerator
    if length < 0:
        _invalid_value(datatype_iri, facet_iri, "a nonnegative integer")
    if facet_iri == XSD_LENGTH:
        return LengthRange.between(length, length)
    if facet_iri == XSD_MIN_LENGTH:
        return LengthRange.between(length)
    return LengthRange.between(0, length)


def _string_facet_value(
    datatype_iri: str,
    facet_iri: str,
    value: CompiledLiteral,
) -> str:
    identity = value.data_identity
    if not isinstance(identity, StringIdentity) or identity.language is not None:
        _invalid_value(datatype_iri, facet_iri, "an untagged string")
    return identity.text


def _language_tag_range(language_range: str) -> LanguageTagRange:
    try:
        return LanguageTagRange.basic(language_range)
    except ValueError:
        raise OntologyProfileError(
            "rdf:langRange requires an RFC 4647 basic language range",
            code="INVALID_FACET_VALUE",
            context={"facet_iri": RDF_LANG_RANGE},
        ) from None


def _require_facet(
    datatype_iri: str,
    facet_iri: str,
    allowed: frozenset[str] | set[str],
) -> None:
    if facet_iri not in allowed:
        raise OntologyProfileError(
            "facet is not legal for the restricted OWL 2 datatype",
            code="ILLEGAL_DATATYPE_FACET",
            context={"datatype_iri": datatype_iri, "facet_iri": facet_iri},
        )


def _invalid_value(datatype_iri: str, facet_iri: str, expected: str) -> NoReturn:
    raise OntologyProfileError(
        "facet literal has the wrong datatype or value domain",
        code="INVALID_FACET_VALUE",
        context={
            "datatype_iri": datatype_iri,
            "expected": expected,
            "facet_iri": facet_iri,
        },
    )


def _controls(
    limits: DatatypeLimits | None,
    cancellation: CancellationToken | None,
) -> DatatypeLimits:
    selected = limits or DatatypeLimits()
    if not isinstance(selected, DatatypeLimits):
        raise TypeError("limits must be DatatypeLimits or None")
    if cancellation is not None and not isinstance(cancellation, CancellationToken):
        raise TypeError("cancellation must be CancellationToken or None")
    _poll(cancellation)
    return selected


def _poll(cancellation: CancellationToken | None, work: int = 0) -> None:
    if cancellation is None:
        return
    if work:
        cancellation.add_work(work)
    cancellation.check()


__all__ = [
    "RDF_LANG_RANGE",
    "XSD_LENGTH",
    "XSD_MAX_EXCLUSIVE",
    "XSD_MAX_INCLUSIVE",
    "XSD_MAX_LENGTH",
    "XSD_MIN_EXCLUSIVE",
    "XSD_MIN_INCLUSIVE",
    "XSD_MIN_LENGTH",
    "XSD_PATTERN",
    "FacetRestriction",
    "restrict_datatype",
]
