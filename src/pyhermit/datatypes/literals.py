# Copyright 2008, 2009, 2010 by the Oxford University Computing Laboratory
# Modifications Copyright 2026 pyHermiT contributors
# SPDX-License-Identifier: LGPL-3.0-or-later

"""Exact OWL 2 built-in lexical/value compilation.

Source-guided compatibility references are the pinned HermiT datatype handlers at commit
``37ec30aced32ac81ebecc5e33fad255ddefcb4c3``.  OWL2 mode follows the W3C
datatype map; observed historical lexical quirks are isolated behind the explicit
``HERMIT_1_4`` compatibility key.
"""

from __future__ import annotations

import re
from collections.abc import Mapping
from dataclasses import dataclass
from types import MappingProxyType
from typing import Final, NoReturn

from pyowl_core.model import Literal

from pyhermit.events import CancellationToken
from pyhermit.exceptions import InvalidLiteralError, ResourceLimitError, UnsupportedDatatypeError

from .binary import XSD_BASE64_BINARY, XSD_HEX_BINARY, compile_binary
from .ieee754 import parse_ieee
from .model import (
    BinaryKind,
    BooleanComparison,
    BooleanIdentity,
    ComparisonValue,
    CompiledLiteral,
    DataIdentity,
    DatatypeLimits,
    IEEEFormat,
    LexicalCompatibility,
    NumericComparison,
    NumericDomain,
    NumericIdentity,
    SourceLiteralIdentity,
)
from .temporal import XSD_DATE_TIME, XSD_DATE_TIME_STAMP, compile_date_time
from .textual import (
    RDF_NAMESPACE,
    RDF_PLAIN_LITERAL,
    STRING_DATATYPES,
    XSD_ANY_URI,
    compile_string,
    compile_uri,
)
from .xml_literal import RDF_XML_LITERAL, compile_xml_literal

XSD_NAMESPACE: Final = "http://www.w3.org/2001/XMLSchema#"
OWL_NAMESPACE: Final = "http://www.w3.org/2002/07/owl#"
RDFS_NAMESPACE: Final = "http://www.w3.org/2000/01/rdf-schema#"

XSD_BOOLEAN: Final = XSD_NAMESPACE + "boolean"
XSD_DECIMAL: Final = XSD_NAMESPACE + "decimal"
XSD_INTEGER: Final = XSD_NAMESPACE + "integer"
XSD_FLOAT: Final = XSD_NAMESPACE + "float"
XSD_DOUBLE: Final = XSD_NAMESPACE + "double"
OWL_RATIONAL: Final = OWL_NAMESPACE + "rational"
OWL_REAL: Final = OWL_NAMESPACE + "real"
RDFS_LITERAL: Final = RDFS_NAMESPACE + "Literal"

_INTEGER = re.compile(r"[+-]?[0-9]+")
_DECIMAL = re.compile(r"[+-]?(?:[0-9]+(?:\.[0-9]*)?|\.[0-9]+)")
_HERMIT_DECIMAL = re.compile(r"[+-]?(?:[0-9]+(?:\.[0-9]*)?|\.[0-9]+)(?:[eE][+-]?[0-9]+)?")
_RATIONAL = re.compile(r"([+-]?)([0-9]+)/([0-9]+)")
_HERMIT_RATIONAL = re.compile(r"([+-]?)([0-9]+)/(?:\+?)([0-9]+)")


@dataclass(frozen=True, slots=True)
class NumericDatatypeSpec:
    iri: str
    domain: NumericDomain
    lower_inclusive: int | None = None
    upper_inclusive: int | None = None
    lexical_kind: str = "integer"

    def __post_init__(self) -> None:
        if not isinstance(self.iri, str) or not self.iri:
            raise ValueError("datatype IRI must be a nonempty string")
        if not isinstance(self.domain, NumericDomain):
            raise TypeError("domain must be NumericDomain")
        if self.lexical_kind not in {"integer", "decimal", "rational", "none"}:
            raise ValueError("unknown numeric lexical kind")
        for name in ("lower_inclusive", "upper_inclusive"):
            value = getattr(self, name)
            if value is not None and (isinstance(value, bool) or not isinstance(value, int)):
                raise TypeError(f"{name} must be int or None")
        if (
            self.lower_inclusive is not None
            and self.upper_inclusive is not None
            and self.lower_inclusive > self.upper_inclusive
        ):
            raise ValueError("numeric datatype lower bound exceeds upper bound")


def _numeric_specs() -> Mapping[str, NumericDatatypeSpec]:
    values = (
        NumericDatatypeSpec(OWL_REAL, NumericDomain.REAL, lexical_kind="none"),
        NumericDatatypeSpec(OWL_RATIONAL, NumericDomain.RATIONAL, lexical_kind="rational"),
        NumericDatatypeSpec(XSD_DECIMAL, NumericDomain.DECIMAL, lexical_kind="decimal"),
        NumericDatatypeSpec(XSD_INTEGER, NumericDomain.INTEGER),
        NumericDatatypeSpec(XSD_NAMESPACE + "nonNegativeInteger", NumericDomain.INTEGER, 0),
        NumericDatatypeSpec(XSD_NAMESPACE + "positiveInteger", NumericDomain.INTEGER, 1),
        NumericDatatypeSpec(XSD_NAMESPACE + "nonPositiveInteger", NumericDomain.INTEGER, None, 0),
        NumericDatatypeSpec(XSD_NAMESPACE + "negativeInteger", NumericDomain.INTEGER, None, -1),
        NumericDatatypeSpec(XSD_NAMESPACE + "long", NumericDomain.INTEGER, -(2**63), 2**63 - 1),
        NumericDatatypeSpec(XSD_NAMESPACE + "int", NumericDomain.INTEGER, -(2**31), 2**31 - 1),
        NumericDatatypeSpec(XSD_NAMESPACE + "short", NumericDomain.INTEGER, -(2**15), 2**15 - 1),
        NumericDatatypeSpec(XSD_NAMESPACE + "byte", NumericDomain.INTEGER, -(2**7), 2**7 - 1),
        NumericDatatypeSpec(XSD_NAMESPACE + "unsignedLong", NumericDomain.INTEGER, 0, 2**64 - 1),
        NumericDatatypeSpec(XSD_NAMESPACE + "unsignedInt", NumericDomain.INTEGER, 0, 2**32 - 1),
        NumericDatatypeSpec(XSD_NAMESPACE + "unsignedShort", NumericDomain.INTEGER, 0, 2**16 - 1),
        NumericDatatypeSpec(XSD_NAMESPACE + "unsignedByte", NumericDomain.INTEGER, 0, 2**8 - 1),
    )
    return MappingProxyType({value.iri: value for value in values})


NUMERIC_DATATYPES: Final[Mapping[str, NumericDatatypeSpec]] = _numeric_specs()
SUPPORTED_DATATYPES: Final[frozenset[str]] = frozenset(
    (
        *NUMERIC_DATATYPES,
        XSD_BOOLEAN,
        XSD_FLOAT,
        XSD_DOUBLE,
        *STRING_DATATYPES,
        XSD_HEX_BINARY,
        XSD_BASE64_BINARY,
        XSD_ANY_URI,
        XSD_DATE_TIME,
        XSD_DATE_TIME_STAMP,
        RDF_XML_LITERAL,
        RDFS_LITERAL,
    )
)


def numeric_datatype_spec(datatype_iri: str) -> NumericDatatypeSpec | None:
    if not isinstance(datatype_iri, str):
        raise TypeError("datatype_iri must be str")
    return NUMERIC_DATATYPES.get(datatype_iri)


def compile_literal(
    literal: Literal,
    *,
    compatibility: LexicalCompatibility = LexicalCompatibility.OWL2,
    limits: DatatypeLimits | None = None,
    cancellation: CancellationToken | None = None,
) -> CompiledLiteral:
    """Validate and compile one core literal without changing or rebuilding it."""

    if not isinstance(literal, Literal):
        raise TypeError("literal must be pyowl_core.model.Literal")
    if not isinstance(compatibility, LexicalCompatibility):
        raise TypeError("compatibility must be LexicalCompatibility")
    selected_limits = limits or DatatypeLimits()
    if not isinstance(selected_limits, DatatypeLimits):
        raise TypeError("limits must be DatatypeLimits or None")
    if cancellation is not None and not isinstance(cancellation, CancellationToken):
        raise TypeError("cancellation must be CancellationToken or None")
    _poll(cancellation)
    lexical = literal.lexical_form
    if len(lexical) > selected_limits.max_lexical_characters:
        raise ResourceLimitError(
            "datatype lexical form exceeds the configured character limit",
            limit="max_lexical_characters",
            observed=len(lexical),
            allowed=selected_limits.max_lexical_characters,
        )
    datatype_iri = literal.datatype.iri.value
    identity: DataIdentity
    comparison: ComparisonValue
    if datatype_iri == XSD_BOOLEAN:
        value = _parse_boolean(lexical, compatibility)
        identity = BooleanIdentity(value)
        comparison = BooleanComparison(value)
    elif datatype_iri in {XSD_FLOAT, XSD_DOUBLE}:
        identity, comparison = parse_ieee(
            lexical,
            IEEEFormat.FLOAT32 if datatype_iri == XSD_FLOAT else IEEEFormat.FLOAT64,
            compatibility=compatibility,
            limits=selected_limits,
            cancellation=cancellation,
        )
    elif datatype_iri in STRING_DATATYPES:
        identity, comparison = compile_string(
            literal,
            compatibility=compatibility,
            limits=selected_limits,
            cancellation=cancellation,
        )
    elif datatype_iri in {XSD_HEX_BINARY, XSD_BASE64_BINARY}:
        identity, comparison = compile_binary(
            lexical,
            BinaryKind.HEX if datatype_iri == XSD_HEX_BINARY else BinaryKind.BASE64,
            limits=selected_limits,
            cancellation=cancellation,
        )
    elif datatype_iri == XSD_ANY_URI:
        identity, comparison = compile_uri(
            lexical,
            limits=selected_limits,
            cancellation=cancellation,
        )
    elif datatype_iri in {XSD_DATE_TIME, XSD_DATE_TIME_STAMP}:
        identity, comparison = compile_date_time(
            lexical,
            require_timezone=datatype_iri == XSD_DATE_TIME_STAMP,
            compatibility=compatibility,
            limits=selected_limits,
            cancellation=cancellation,
        )
    elif datatype_iri == RDF_XML_LITERAL:
        identity, comparison = compile_xml_literal(
            lexical,
            limits=selected_limits,
            cancellation=cancellation,
        )
    elif datatype_iri == RDFS_LITERAL:
        # The universal data range has no direct lexical-to-value mapping.
        _invalid_lexical(RDFS_LITERAL)
    else:
        spec = NUMERIC_DATATYPES.get(datatype_iri)
        if spec is None:
            raise UnsupportedDatatypeError(
                "datatype is outside the implemented OWL 2 datatype map",
                context={"datatype_iri": datatype_iri},
            )
        numerator, denominator = _parse_numeric(
            lexical,
            spec,
            compatibility=compatibility,
            limits=selected_limits,
            cancellation=cancellation,
        )
        identity = NumericIdentity(numerator, denominator)
        comparison = NumericComparison(numerator, denominator)
    _poll(cancellation)
    return CompiledLiteral(
        source_literal=literal,
        source_identity=SourceLiteralIdentity.from_literal(literal),
        data_identity=identity,
        comparison=comparison,
        compatibility=compatibility,
    )


def _parse_boolean(lexical: str, compatibility: LexicalCompatibility) -> bool:
    selected = lexical
    if compatibility is LexicalCompatibility.HERMIT_1_4:
        # Pinned BooleanDatatypeHandler trims and uses equalsIgnoreCase.
        selected = selected.strip()
        if selected.lower() == "true" or selected == "1":
            return True
        if selected.lower() == "false" or selected == "0":
            return False
    else:
        if selected == "true" or selected == "1":
            return True
        if selected == "false" or selected == "0":
            return False
    _invalid_lexical(XSD_BOOLEAN)


def _parse_numeric(
    lexical: str,
    spec: NumericDatatypeSpec,
    *,
    compatibility: LexicalCompatibility,
    limits: DatatypeLimits,
    cancellation: CancellationToken | None,
) -> tuple[int, int]:
    if spec.lexical_kind == "none":
        _invalid_lexical(spec.iri)
    if spec.lexical_kind == "integer":
        if _INTEGER.fullmatch(lexical) is None:
            _invalid_lexical(spec.iri)
        sign, digits = _split_sign(lexical)
        value = sign * _parse_digits(digits, limits=limits, cancellation=cancellation)
        if spec.lower_inclusive is not None and value < spec.lower_inclusive:
            _invalid_lexical(spec.iri)
        if spec.upper_inclusive is not None and value > spec.upper_inclusive:
            _invalid_lexical(spec.iri)
        return value, 1
    if spec.lexical_kind == "decimal":
        pattern = _HERMIT_DECIMAL if compatibility is LexicalCompatibility.HERMIT_1_4 else _DECIMAL
        if pattern.fullmatch(lexical) is None:
            _invalid_lexical(spec.iri)
        return _parse_decimal(
            lexical,
            limits=limits,
            cancellation=cancellation,
        )
    pattern = _HERMIT_RATIONAL if compatibility is LexicalCompatibility.HERMIT_1_4 else _RATIONAL
    match = pattern.fullmatch(lexical)
    if match is None:
        _invalid_lexical(spec.iri)
    sign_text, numerator_digits, denominator_digits = match.groups()
    numerator = _parse_digits(numerator_digits, limits=limits, cancellation=cancellation)
    if sign_text == "-":
        numerator = -numerator
    denominator = _parse_digits(denominator_digits, limits=limits, cancellation=cancellation)
    if denominator == 0:
        _invalid_lexical(spec.iri)
    return numerator, denominator


def _parse_decimal(
    lexical: str,
    *,
    limits: DatatypeLimits,
    cancellation: CancellationToken | None,
) -> tuple[int, int]:
    sign, unsigned = _split_sign(lexical)
    exponent = 0
    exponent_index = max(unsigned.find("e"), unsigned.find("E"))
    if exponent_index >= 0:
        mantissa = unsigned[:exponent_index]
        exponent_text = unsigned[exponent_index + 1 :]
        exponent_sign, exponent_digits = _split_sign(exponent_text)
        exponent_magnitude = _parse_digits(
            exponent_digits,
            limits=limits,
            cancellation=cancellation,
        )
        if exponent_magnitude > limits.max_decimal_exponent:
            raise ResourceLimitError(
                "decimal exponent exceeds the configured magnitude limit",
                limit="max_decimal_exponent",
                observed=limits.max_decimal_exponent + 1,
                allowed=limits.max_decimal_exponent,
            )
        exponent = exponent_sign * exponent_magnitude
    else:
        mantissa = unsigned
    if "." in mantissa:
        whole, fraction = mantissa.split(".", 1)
    else:
        whole, fraction = mantissa, ""
    digits = (whole or "0") + fraction
    numerator = sign * _parse_digits(digits, limits=limits, cancellation=cancellation)
    scale = len(fraction) - exponent
    if abs(scale) > limits.max_decimal_exponent:
        raise ResourceLimitError(
            "decimal scale exceeds the configured magnitude limit",
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


def _split_sign(value: str) -> tuple[int, str]:
    if value.startswith("-"):
        return -1, value[1:]
    if value.startswith("+"):
        return 1, value[1:]
    return 1, value


def _parse_digits(
    digits: str,
    *,
    limits: DatatypeLimits,
    cancellation: CancellationToken | None,
) -> int:
    count = len(digits)
    if count > limits.max_numeric_digits:
        raise ResourceLimitError(
            "numeric lexical form exceeds the configured digit limit",
            limit="max_numeric_digits",
            observed=count,
            allowed=limits.max_numeric_digits,
        )
    # Small direct conversions avoid locks and Python's version-dependent large-int
    # string limit. Large values use fixed blocks and remain cooperatively cancellable.
    if count <= 512:
        return int(digits)
    value = 0
    stride = limits.cancellation_poll_stride
    blocks_since_poll = 0
    for start in range(0, count, 9):
        block = digits[start : start + 9]
        value = value * 10 ** len(block) + int(block)
        blocks_since_poll += 1
        if blocks_since_poll == stride:
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


def _invalid_lexical(datatype_iri: str) -> NoReturn:
    raise InvalidLiteralError(
        "literal lexical form is outside the datatype lexical space",
        context={"datatype_iri": datatype_iri},
    )


__all__ = [
    "NUMERIC_DATATYPES",
    "OWL_NAMESPACE",
    "OWL_RATIONAL",
    "OWL_REAL",
    "RDFS_LITERAL",
    "RDFS_NAMESPACE",
    "RDF_NAMESPACE",
    "RDF_PLAIN_LITERAL",
    "RDF_XML_LITERAL",
    "SUPPORTED_DATATYPES",
    "XSD_ANY_URI",
    "XSD_BASE64_BINARY",
    "XSD_BOOLEAN",
    "XSD_DATE_TIME",
    "XSD_DATE_TIME_STAMP",
    "XSD_DECIMAL",
    "XSD_DOUBLE",
    "XSD_FLOAT",
    "XSD_HEX_BINARY",
    "XSD_INTEGER",
    "XSD_NAMESPACE",
    "NumericDatatypeSpec",
    "compile_literal",
    "numeric_datatype_spec",
]
