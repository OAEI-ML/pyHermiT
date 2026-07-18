# Copyright 2008, 2009, 2010 by the Oxford University Computing Laboratory
# Modifications Copyright 2026 pyHermiT contributors
# SPDX-License-Identifier: LGPL-3.0-or-later
# Adapted from HermiT commit 37ec30aced32ac81ebecc5e33fad255ddefcb4c3;
# see reports/licensing/adapted-files.toml.

"""OWL 2 string, plain-literal, and anyURI lexical/value semantics."""

from __future__ import annotations

from collections.abc import Callable, Mapping
from dataclasses import dataclass
from types import MappingProxyType
from typing import Final, NoReturn

from pyowl_core.model import Literal

from pyhermit.events import CancellationToken
from pyhermit.exceptions import InvalidLiteralError

from .model import (
    DatatypeLimits,
    LexicalCompatibility,
    StringComparison,
    StringIdentity,
    URIComparison,
    URIIdentity,
)

XSD_NAMESPACE: Final = "http://www.w3.org/2001/XMLSchema#"
RDF_NAMESPACE: Final = "http://www.w3.org/1999/02/22-rdf-syntax-ns#"

RDF_PLAIN_LITERAL: Final = RDF_NAMESPACE + "PlainLiteral"
XSD_STRING: Final = XSD_NAMESPACE + "string"
XSD_NORMALIZED_STRING: Final = XSD_NAMESPACE + "normalizedString"
XSD_TOKEN: Final = XSD_NAMESPACE + "token"
XSD_LANGUAGE: Final = XSD_NAMESPACE + "language"
XSD_NAME: Final = XSD_NAMESPACE + "Name"
XSD_NCNAME: Final = XSD_NAMESPACE + "NCName"
XSD_NMTOKEN: Final = XSD_NAMESPACE + "NMTOKEN"
XSD_ANY_URI: Final = XSD_NAMESPACE + "anyURI"


@dataclass(frozen=True, slots=True)
class StringDatatypeSpec:
    iri: str
    whitespace: str
    validator: Callable[[str], bool]

    def __post_init__(self) -> None:
        if not isinstance(self.iri, str) or not self.iri:
            raise ValueError("iri must be a nonempty string")
        if self.whitespace not in {"preserve", "replace", "collapse"}:
            raise ValueError("unknown whitespace policy")
        if not callable(self.validator):
            raise TypeError("validator must be callable")


def _string_specs() -> Mapping[str, StringDatatypeSpec]:
    values = (
        StringDatatypeSpec(RDF_PLAIN_LITERAL, "preserve", _valid_xml_string),
        StringDatatypeSpec(XSD_STRING, "preserve", _valid_xml_string),
        StringDatatypeSpec(XSD_NORMALIZED_STRING, "replace", _valid_xml_string),
        StringDatatypeSpec(XSD_TOKEN, "collapse", _valid_xml_string),
        StringDatatypeSpec(XSD_LANGUAGE, "collapse", _valid_language),
        StringDatatypeSpec(XSD_NAME, "collapse", _valid_name),
        StringDatatypeSpec(XSD_NCNAME, "collapse", _valid_ncname),
        StringDatatypeSpec(XSD_NMTOKEN, "collapse", _valid_nmtoken),
    )
    return MappingProxyType({value.iri: value for value in values})


def compile_string(
    literal: Literal,
    *,
    compatibility: LexicalCompatibility,
    limits: DatatypeLimits,
    cancellation: CancellationToken | None,
) -> tuple[StringIdentity, StringComparison]:
    """Compile an overlapping rdf:PlainLiteral/XML Schema string value."""

    if not isinstance(literal, Literal):
        raise TypeError("literal must be pyowl_core.model.Literal")
    datatype_iri = literal.datatype.iri.value
    spec = STRING_DATATYPES.get(datatype_iri)
    if spec is None:
        raise ValueError("compile_string requires a string-family datatype")
    lexical = literal.lexical_form
    if compatibility is LexicalCompatibility.HERMIT_1_4 and datatype_iri not in {
        RDF_PLAIN_LITERAL,
        XSD_STRING,
    }:
        # Pinned HermiT tests raw lexical membership in the derived value-space
        # automaton rather than applying the XML Schema whitespace transform.
        transformed = lexical
        if spec.whitespace == "replace" and any(char in "\t\n\r" for char in lexical):
            _invalid(datatype_iri)
        if spec.whitespace == "collapse" and _collapse_whitespace(lexical) != lexical:
            _invalid(datatype_iri)
    else:
        transformed = _apply_whitespace(lexical, spec.whitespace)
    _scan_xml_characters(
        transformed,
        datatype_iri=datatype_iri,
        limits=limits,
        cancellation=cancellation,
    )
    if not spec.validator(transformed):
        _invalid(datatype_iri)
    language = literal.language if datatype_iri == RDF_PLAIN_LITERAL else None
    identity = StringIdentity(transformed, language)
    return identity, StringComparison(transformed, language)


def compile_uri(
    lexical: str,
    *,
    limits: DatatypeLimits,
    cancellation: CancellationToken | None,
) -> tuple[URIIdentity, URIComparison]:
    """Compile xsd:anyURI without resolution or network access.

    XSD 1.1 defines both lexical and value spaces as finite XML-character
    sequences.  Relative references and their exact spelling are retained.
    """

    if not isinstance(lexical, str):
        raise TypeError("lexical must be str")
    _scan_xml_characters(
        lexical,
        datatype_iri=XSD_ANY_URI,
        limits=limits,
        cancellation=cancellation,
    )
    identity = URIIdentity(lexical)
    return identity, URIComparison(lexical)


def string_datatype_spec(datatype_iri: str) -> StringDatatypeSpec | None:
    if not isinstance(datatype_iri, str):
        raise TypeError("datatype_iri must be str")
    return STRING_DATATYPES.get(datatype_iri)


def is_xml_character(char: str) -> bool:
    if not isinstance(char, str) or len(char) != 1:
        raise TypeError("char must be one Unicode character")
    codepoint = ord(char)
    return (
        codepoint in {0x9, 0xA, 0xD}
        or 0x20 <= codepoint <= 0xD7FF
        or 0xE000 <= codepoint <= 0xFFFD
        or 0x10000 <= codepoint <= 0x10FFFF
    )


def _scan_xml_characters(
    value: str,
    *,
    datatype_iri: str,
    limits: DatatypeLimits,
    cancellation: CancellationToken | None,
) -> None:
    stride = limits.cancellation_poll_stride
    since_poll = 0
    for char in value:
        if not is_xml_character(char):
            _invalid(datatype_iri)
        since_poll += 1
        if since_poll == stride:
            _poll(cancellation, since_poll)
            since_poll = 0
    _poll(cancellation, since_poll)


def _apply_whitespace(value: str, policy: str) -> str:
    if policy == "preserve":
        return value
    replaced = value.translate({0x9: 0x20, 0xA: 0x20, 0xD: 0x20})
    if policy == "replace":
        return replaced
    return " ".join(part for part in replaced.split(" ") if part)


def _collapse_whitespace(value: str) -> str:
    return _apply_whitespace(value, "collapse")


def _valid_xml_string(value: str) -> bool:
    return all(is_xml_character(char) for char in value)


def _valid_language(value: str) -> bool:
    if not value:
        return False
    parts = value.split("-")
    return (
        1 <= len(parts[0]) <= 8
        and parts[0].isascii()
        and parts[0].isalpha()
        and all(1 <= len(part) <= 8 and part.isascii() and part.isalnum() for part in parts[1:])
    )


def _valid_name(value: str) -> bool:
    return (
        bool(value)
        and _is_name_start(value[0], allow_colon=True)
        and all(_is_name_char(char, allow_colon=True) for char in value[1:])
    )


def _valid_ncname(value: str) -> bool:
    return (
        bool(value)
        and _is_name_start(value[0], allow_colon=False)
        and all(_is_name_char(char, allow_colon=False) for char in value[1:])
    )


def _valid_nmtoken(value: str) -> bool:
    return bool(value) and all(_is_name_char(char, allow_colon=True) for char in value)


def _is_name_start(char: str, *, allow_colon: bool) -> bool:
    codepoint = ord(char)
    return (
        (allow_colon and char == ":")
        or char == "_"
        or 0x41 <= codepoint <= 0x5A
        or 0x61 <= codepoint <= 0x7A
        or 0xC0 <= codepoint <= 0xD6
        or 0xD8 <= codepoint <= 0xF6
        or 0xF8 <= codepoint <= 0x2FF
        or 0x370 <= codepoint <= 0x37D
        or 0x37F <= codepoint <= 0x1FFF
        or 0x200C <= codepoint <= 0x200D
        or 0x2070 <= codepoint <= 0x218F
        or 0x2C00 <= codepoint <= 0x2FEF
        or 0x3001 <= codepoint <= 0xD7FF
        or 0xF900 <= codepoint <= 0xFDCF
        or 0xFDF0 <= codepoint <= 0xFFFD
        or 0x10000 <= codepoint <= 0xEFFFF
    )


def _is_name_char(char: str, *, allow_colon: bool) -> bool:
    codepoint = ord(char)
    return (
        _is_name_start(char, allow_colon=allow_colon)
        or char in {"-", "."}
        or 0x30 <= codepoint <= 0x39
        or codepoint == 0xB7
        or 0x300 <= codepoint <= 0x36F
        or 0x203F <= codepoint <= 0x2040
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


STRING_DATATYPES: Final[Mapping[str, StringDatatypeSpec]] = _string_specs()


__all__ = [
    "RDF_NAMESPACE",
    "RDF_PLAIN_LITERAL",
    "STRING_DATATYPES",
    "XSD_ANY_URI",
    "XSD_LANGUAGE",
    "XSD_NAME",
    "XSD_NCNAME",
    "XSD_NMTOKEN",
    "XSD_NORMALIZED_STRING",
    "XSD_STRING",
    "XSD_TOKEN",
    "StringDatatypeSpec",
    "compile_string",
    "compile_uri",
    "is_xml_character",
    "string_datatype_spec",
]
