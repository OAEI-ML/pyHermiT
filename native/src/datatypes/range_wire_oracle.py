"""Build the deterministic Python/Rust canonical data-range wire oracle.

SPDX-License-Identifier: LGPL-3.0-or-later
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import pyowl_core.model as owl

from pyhermit.datatypes import (
    RDF_LANG_RANGE,
    RDF_PLAIN_LITERAL,
    RDF_XML_LITERAL,
    XSD_ANY_URI,
    XSD_BASE64_BINARY,
    XSD_BOOLEAN,
    XSD_DATE_TIME,
    XSD_DATE_TIME_STAMP,
    XSD_DECIMAL,
    XSD_FLOAT,
    XSD_HEX_BINARY,
    XSD_INTEGER,
    XSD_LENGTH,
    XSD_MAX_EXCLUSIVE,
    XSD_MAX_INCLUSIVE,
    XSD_MAX_LENGTH,
    XSD_MIN_EXCLUSIVE,
    XSD_MIN_INCLUSIVE,
    XSD_MIN_LENGTH,
    XSD_PATTERN,
    XSD_STRING,
    DataDomainRange,
    LexicalCompatibility,
    LiteralSemanticPayload,
    compile_datatype_semantic_model,
    compile_literal,
    compile_literal_semantic_payload,
)

DEFAULT_OUTPUT = Path("native/src/datatypes/range_wire_oracle_v1.json")
XSD = "http://www.w3.org/2001/XMLSchema#"
OPAQUE = "urn:pyhermit:oracle:opaque"


@dataclass(frozen=True, slots=True)
class LiteralSource:
    label: str
    lexical: str
    datatype_iri: str
    language: str | None = None
    compatibility: LexicalCompatibility = LexicalCompatibility.OWL2


def datatype(iri: str) -> owl.Datatype:
    return owl.Datatype(owl.IRI(iri))


def literal(source: LiteralSource | tuple[str, str]) -> owl.Literal:
    if isinstance(source, tuple):
        lexical, datatype_iri = source
        return owl.Literal(lexical, datatype(datatype_iri))
    return owl.Literal(source.lexical, datatype(source.datatype_iri), source.language)


def facet(iri: str, lexical: str, datatype_iri: str) -> owl.FacetRestriction:
    return owl.FacetRestriction(owl.IRI(iri), literal((lexical, datatype_iri)))


def restriction(datatype_iri: str, *facets: owl.FacetRestriction) -> owl.DatatypeRestriction:
    return owl.DatatypeRestriction(datatype(datatype_iri), owl.CanonicalSet(facets))


def one_of(*values: tuple[str, str]) -> owl.DataOneOf:
    return owl.DataOneOf(owl.CanonicalSet(tuple(literal(value) for value in values)))


def semantic_fixture() -> tuple[
    tuple[str, ...], tuple[owl.DataRange, ...], tuple[owl.DatatypeDefinition, ...]
]:
    bounded_integer = restriction(
        XSD_INTEGER,
        facet(XSD_MIN_INCLUSIVE, "0", XSD_INTEGER),
        facet(XSD_MIN_EXCLUSIVE, "-1", XSD_INTEGER),
        facet(XSD_MAX_INCLUSIVE, "3", XSD_INTEGER),
        facet(XSD_MAX_EXCLUSIVE, "4", XSD_INTEGER),
    )
    two_letters = restriction(
        XSD_STRING,
        facet(XSD_LENGTH, "2", XSD_INTEGER),
        facet(XSD_MIN_LENGTH, "1", XSD_INTEGER),
        facet(XSD_MAX_LENGTH, "3", XSD_INTEGER),
        facet(XSD_PATTERN, "[ab]{2}", XSD_STRING),
    )
    english_ok = restriction(
        RDF_PLAIN_LITERAL,
        facet(RDF_LANG_RANGE, "en", XSD_STRING),
        facet(XSD_PATTERN, "ok", XSD_STRING),
    )
    one_byte = restriction(
        XSD_HEX_BINARY,
        facet(XSD_LENGTH, "1", XSD_INTEGER),
    )
    one_character_uri = restriction(
        XSD_ANY_URI,
        facet(XSD_MIN_LENGTH, "1", XSD_INTEGER),
        facet(XSD_MAX_LENGTH, "1", XSD_INTEGER),
        facet(XSD_PATTERN, "[ab]", XSD_STRING),
    )
    bounded_date = restriction(
        XSD_DATE_TIME,
        facet(XSD_MIN_INCLUSIVE, "2000-01-01T00:00:00Z", XSD_DATE_TIME),
        facet(XSD_MAX_EXCLUSIVE, "2000-01-02T00:00:00Z", XSD_DATE_TIME),
    )
    bounded_float = restriction(
        XSD_FLOAT,
        facet(XSD_MIN_EXCLUSIVE, "-1", XSD_FLOAT),
        facet(XSD_MAX_INCLUSIVE, "1", XSD_FLOAT),
    )
    empty_base64 = restriction(
        XSD_BASE64_BINARY,
        facet(XSD_MIN_LENGTH, "0", XSD_INTEGER),
        facet(XSD_MAX_LENGTH, "0", XSD_INTEGER),
    )
    selected_values = one_of(("01", XSD_INTEGER), ("1.0", XSD_DECIMAL), ("x", XSD_STRING))
    without_one = owl.DataIntersectionOf(
        owl.CanonicalSet((bounded_integer, owl.DataComplementOf(one_of(("1", XSD_INTEGER)))))
    )
    small = datatype("urn:pyhermit:oracle:small")
    selected = datatype("urn:pyhermit:oracle:selected")
    definitions = (
        owl.DatatypeDefinition(small, bounded_integer),
        owl.DatatypeDefinition(
            selected,
            owl.DataUnionOf(owl.CanonicalSet((small, selected_values))),
        ),
    )
    labels = (
        "boolean-datatype",
        "four-ordered-facets",
        "string-length-pattern-facets",
        "plain-literal-lang-range",
        "hex-binary-length",
        "uri-length-pattern",
        "date-time-bounds",
        "float-bounds",
        "enumeration",
        "union",
        "intersection-complement",
        "family-complement",
        "named-definition",
        "date-time-stamp",
        "base64-empty-value",
        "xml-literal",
        "date-time-stamp-complement",
        "opaque",
    )
    roots: tuple[owl.DataRange, ...] = (
        datatype(XSD_BOOLEAN),
        bounded_integer,
        two_letters,
        english_ok,
        one_byte,
        one_character_uri,
        bounded_date,
        bounded_float,
        selected_values,
        owl.DataUnionOf(owl.CanonicalSet((selected_values, datatype(XSD_BOOLEAN)))),
        without_one,
        owl.DataComplementOf(datatype(XSD_BOOLEAN)),
        selected,
        datatype(XSD_DATE_TIME_STAMP),
        empty_base64,
        datatype(RDF_XML_LITERAL),
        owl.DataComplementOf(datatype(XSD_DATE_TIME_STAMP)),
        datatype(OPAQUE),
    )
    return labels, roots, definitions


def literal_sources() -> tuple[LiteralSource, ...]:
    return (
        LiteralSource("false", "false", XSD_BOOLEAN),
        LiteralSource("true", "true", XSD_BOOLEAN),
        LiteralSource("integer--1", "-1", XSD_INTEGER),
        LiteralSource("integer-0", "0", XSD_INTEGER),
        LiteralSource("integer-1", "1", XSD_INTEGER),
        LiteralSource("integer-2", "2", XSD_INTEGER),
        LiteralSource("integer-3", "3", XSD_INTEGER),
        LiteralSource("integer-4", "4", XSD_INTEGER),
        LiteralSource("decimal-1-alias", "1.0", XSD_DECIMAL),
        LiteralSource("empty-string", "", XSD_STRING),
        LiteralSource("string-x", "x", XSD_STRING),
        LiteralSource("string-aa", "aa", XSD_STRING),
        LiteralSource("string-ab", "ab", XSD_STRING),
        LiteralSource("string-ac", "ac", XSD_STRING),
        LiteralSource("plain-ok-en", "ok", RDF_PLAIN_LITERAL, "en"),
        LiteralSource("plain-ok-en-gb", "ok", RDF_PLAIN_LITERAL, "en-GB"),
        LiteralSource("plain-ok-fr", "ok", RDF_PLAIN_LITERAL, "fr"),
        LiteralSource("hex-empty", "", XSD_HEX_BINARY),
        LiteralSource("hex-00", "00", XSD_HEX_BINARY),
        LiteralSource("hex-ff", "ff", XSD_HEX_BINARY),
        LiteralSource("base64-empty", "", XSD_BASE64_BINARY),
        LiteralSource("uri-empty", "", XSD_ANY_URI),
        LiteralSource("uri-a", "a", XSD_ANY_URI),
        LiteralSource("uri-b", "b", XSD_ANY_URI),
        LiteralSource("uri-c", "c", XSD_ANY_URI),
        LiteralSource("float--1", "-1", XSD_FLOAT),
        LiteralSource("float--0", "-0", XSD_FLOAT),
        LiteralSource("float-+0", "+0", XSD_FLOAT),
        LiteralSource("float-1", "1", XSD_FLOAT),
        LiteralSource("date-lower", "2000-01-01T00:00:00Z", XSD_DATE_TIME),
        LiteralSource("date-middle", "2000-01-01T12:00:00Z", XSD_DATE_TIME),
        LiteralSource("date-upper", "2000-01-02T00:00:00Z", XSD_DATE_TIME),
        LiteralSource("date-unzoned", "2000-01-01T12:00:00", XSD_DATE_TIME),
        LiteralSource("xml", "<a/>", RDF_XML_LITERAL),
        LiteralSource(
            "hermit-end-of-day",
            "2000-01-01T24:00:00",
            XSD_DATE_TIME,
            compatibility=LexicalCompatibility.HERMIT_1_4,
        ),
    )


def build_fixture() -> dict[str, Any]:
    labels, roots, definitions = semantic_fixture()
    model = compile_datatype_semantic_model(
        roots,
        definitions=definitions,
        opaque_datatype_iris=(OPAQUE,),
    )
    compiled = tuple(
        compile_literal(literal(source), compatibility=source.compatibility)
        for source in literal_sources()
    )
    literal_payloads = tuple(compile_literal_semantic_payload(value) for value in compiled)
    if not all(isinstance(value, LiteralSemanticPayload) for value in literal_payloads):
        raise AssertionError("oracle literals unexpectedly contain opaque semantics")
    ranges: list[dict[str, Any]] = []
    for index, label in enumerate(labels):
        if label == "opaque":
            ranges.append(
                {
                    "cardinality": "unsupported",
                    "checks": [],
                    "empty": "unsupported",
                    "label": label,
                    "range_id": index,
                }
            )
            continue
        domain = DataDomainRange.from_model(model, index)
        cardinality = domain.finite_cardinality()
        ranges.append(
            {
                "cardinality": "infinite" if cardinality is None else str(cardinality),
                "checks": [domain.contains(value) for value in compiled],
                "empty": domain.is_empty_exact(),
                "label": label,
                "range_id": index,
            }
        )
    return {
        "literal_payloads": [
            {
                "label": source.label,
                "payload_json": payload.canonical_bytes().decode(),
            }
            for source, payload in zip(literal_sources(), literal_payloads, strict=True)
        ],
        "model_json": model.canonical_bytes().decode(),
        "ranges": ranges,
        "schema_version": 1,
    }


def canonical_bytes() -> bytes:
    return (
        json.dumps(build_fixture(), ensure_ascii=False, separators=(",", ":"), sort_keys=True)
        + "\n"
    ).encode()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    arguments = parser.parse_args()
    generated = canonical_bytes()
    if arguments.check:
        return 0 if arguments.output.read_bytes() == generated else 1
    arguments.output.parent.mkdir(parents=True, exist_ok=True)
    arguments.output.write_bytes(generated)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
