# Copyright 2008, 2009, 2010 by the Oxford University Computing Laboratory
# Modifications Copyright 2026 pyHermiT contributors
# SPDX-License-Identifier: LGPL-3.0-or-later

"""Exact, bounded XML Schema hexBinary and base64Binary decoders."""

from __future__ import annotations

import base64
import binascii
from typing import Final, NoReturn

from pyhermit.events import CancellationToken
from pyhermit.exceptions import InvalidLiteralError, ResourceLimitError

from .model import BinaryComparison, BinaryIdentity, BinaryKind, DatatypeLimits

XSD_NAMESPACE: Final = "http://www.w3.org/2001/XMLSchema#"
XSD_HEX_BINARY: Final = XSD_NAMESPACE + "hexBinary"
XSD_BASE64_BINARY: Final = XSD_NAMESPACE + "base64Binary"


def compile_binary(
    lexical: str,
    kind: BinaryKind,
    *,
    limits: DatatypeLimits,
    cancellation: CancellationToken | None,
) -> tuple[BinaryIdentity, BinaryComparison]:
    """Decode one binary literal without conflating the two primitive spaces."""

    if not isinstance(lexical, str):
        raise TypeError("lexical must be str")
    if not isinstance(kind, BinaryKind):
        raise TypeError("kind must be BinaryKind")
    if not isinstance(limits, DatatypeLimits):
        raise TypeError("limits must be DatatypeLimits")
    _poll(cancellation)
    if kind is BinaryKind.HEX:
        octets = _decode_hex(lexical, limits=limits, cancellation=cancellation)
    else:
        octets = _decode_base64(lexical, limits=limits, cancellation=cancellation)
    _poll(cancellation)
    identity = BinaryIdentity(kind, octets)
    return identity, BinaryComparison(kind, octets)


def _decode_hex(
    lexical: str,
    *,
    limits: DatatypeLimits,
    cancellation: CancellationToken | None,
) -> bytes:
    # whiteSpace=collapse permits leading/trailing XML whitespace, but an
    # internal collapsed space is not part of the hexBinary grammar.
    normalized = _collapse_xml_whitespace(lexical)
    if " " in normalized or len(normalized) % 2:
        _invalid(XSD_HEX_BINARY)
    byte_count = len(normalized) // 2
    _check_size(byte_count, limits)
    output = bytearray(byte_count)
    stride = limits.cancellation_poll_stride
    since_poll = 0
    for index in range(byte_count):
        high = _hex_value(normalized[index * 2])
        low = _hex_value(normalized[index * 2 + 1])
        if high < 0 or low < 0:
            _invalid(XSD_HEX_BINARY)
        output[index] = (high << 4) | low
        since_poll += 1
        if since_poll == stride:
            _poll(cancellation, since_poll)
            since_poll = 0
    _poll(cancellation, since_poll)
    return bytes(output)


def _decode_base64(
    lexical: str,
    *,
    limits: DatatypeLimits,
    cancellation: CancellationToken | None,
) -> bytes:
    normalized = _collapse_xml_whitespace(lexical)
    if any(char != " " and not char.isascii() for char in normalized):
        _invalid(XSD_BASE64_BINARY)
    compact = normalized.replace(" ", "")
    if len(compact) % 4:
        _invalid(XSD_BASE64_BINARY)
    padding = len(compact) - len(compact.rstrip("="))
    if padding > 2 or "=" in compact[: -padding or None]:
        _invalid(XSD_BASE64_BINARY)
    byte_count = len(compact) // 4 * 3 - padding
    _check_size(byte_count, limits)
    _poll(cancellation, len(compact))
    try:
        decoded = base64.b64decode(compact, validate=True)
    except (binascii.Error, ValueError) as error:
        raise InvalidLiteralError(
            "literal lexical form is outside the datatype lexical space",
            context={"datatype_iri": XSD_BASE64_BINARY},
        ) from error
    # XSD's B16/B04 productions require unused pad bits to be zero.
    if base64.b64encode(decoded).decode("ascii") != compact:
        _invalid(XSD_BASE64_BINARY)
    return decoded


def _collapse_xml_whitespace(value: str) -> str:
    replaced = value.translate({0x9: 0x20, 0xA: 0x20, 0xD: 0x20})
    return " ".join(part for part in replaced.split(" ") if part)


def _hex_value(char: str) -> int:
    codepoint = ord(char)
    if 0x30 <= codepoint <= 0x39:
        return codepoint - 0x30
    if 0x41 <= codepoint <= 0x46:
        return codepoint - 0x41 + 10
    if 0x61 <= codepoint <= 0x66:
        return codepoint - 0x61 + 10
    return -1


def _check_size(observed: int, limits: DatatypeLimits) -> None:
    if observed > limits.max_binary_bytes:
        raise ResourceLimitError(
            "decoded binary value exceeds the configured byte limit",
            limit="max_binary_bytes",
            observed=observed,
            allowed=limits.max_binary_bytes,
        )


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
    "XSD_BASE64_BINARY",
    "XSD_HEX_BINARY",
    "compile_binary",
]
