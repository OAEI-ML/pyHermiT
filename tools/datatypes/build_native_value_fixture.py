"""Build WPR3's shared Python/Rust exact semantic-value fixture.

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
    OWL_RATIONAL,
    RDF_PLAIN_LITERAL,
    RDF_XML_LITERAL,
    XSD_ANY_URI,
    XSD_BASE64_BINARY,
    XSD_BOOLEAN,
    XSD_DATE_TIME,
    XSD_DECIMAL,
    XSD_DOUBLE,
    XSD_FLOAT,
    XSD_HEX_BINARY,
    XSD_INTEGER,
    XSD_STRING,
    XSD_TOKEN,
    BooleanComparison,
    ComparisonOrder,
    CompiledLiteral,
    LexicalCompatibility,
    LiteralSemanticPayload,
    compile_literal,
    compile_literal_semantic_payload,
)

DEFAULT_OUTPUT = Path("tests/data/datatypes/wpr3-native-values-v1.json")


@dataclass(frozen=True, slots=True)
class Source:
    lexical: str
    datatype_iri: str
    language: str | None = None
    compatibility: LexicalCompatibility = LexicalCompatibility.OWL2


def _literal(source: Source) -> owl.Literal:
    return owl.Literal(
        source.lexical,
        owl.Datatype(owl.IRI(source.datatype_iri)),
        source.language,
    )


def _sources() -> tuple[Source, ...]:
    return (
        Source("01", XSD_INTEGER),
        Source("+1", XSD_INTEGER),
        Source("1.0", XSD_DECIMAL),
        Source("1/2", OWL_RATIONAL),
        Source("-0", XSD_INTEGER),
        Source("12345678901234567890123456789012345678901234567890", XSD_INTEGER),
        Source("+0", XSD_FLOAT),
        Source("-0", XSD_FLOAT),
        Source("1.40129846E-45", XSD_FLOAT),
        Source("INF", XSD_FLOAT),
        Source("-INF", XSD_FLOAT),
        Source("NaN", XSD_FLOAT),
        Source("NaN", XSD_DOUBLE),
        Source("true", XSD_BOOLEAN),
        Source("1", XSD_BOOLEAN),
        Source("false", XSD_BOOLEAN),
        Source("same", XSD_STRING),
        Source("  same  ", XSD_TOKEN),
        Source("colour", RDF_PLAIN_LITERAL, "en-GB"),
        Source("colour", RDF_PLAIN_LITERAL, "fr"),
        Source("0aFF", XSD_HEX_BINARY),
        Source("Cv8=", XSD_BASE64_BINARY),
        Source("../relative?q=1#fragment", XSD_ANY_URI),
        Source('<a y="2" x="1"/>', RDF_XML_LITERAL),
        Source('<a x="1" y="2"></a>', RDF_XML_LITERAL),
        Source("2000-01-01T01:00:00+01:00", XSD_DATE_TIME),
        Source("2000-01-01T00:00:00Z", XSD_DATE_TIME),
        Source("2000-01-01T00:00:00", XSD_DATE_TIME),
        Source("1999-12-30T00:00:00Z", XSD_DATE_TIME),
        Source("2000-01-01T24:00:00", XSD_DATE_TIME, compatibility=LexicalCompatibility.HERMIT_1_4),
    )


def _comparison(left: CompiledLiteral, right: CompiledLiteral) -> str:
    first = left.comparison
    second = right.comparison
    if type(first) is not type(second):
        return "error"
    if isinstance(first, BooleanComparison):
        return "equal" if first == second else "unordered"
    compare = getattr(first, "compare", None)
    if compare is None:
        return "equal" if first == second else "unordered"
    try:
        result = int(compare(second))
    except TypeError:
        return "error"
    return {
        int(ComparisonOrder.LESS): "less",
        int(ComparisonOrder.EQUAL): "equal",
        int(ComparisonOrder.GREATER): "greater",
        int(ComparisonOrder.UNORDERED): "unordered",
    }[result]


def build_fixture() -> dict[str, Any]:
    compiled = tuple(
        compile_literal(_literal(source), compatibility=source.compatibility)
        for source in _sources()
    )
    payloads = tuple(compile_literal_semantic_payload(value) for value in compiled)
    if not all(isinstance(value, LiteralSemanticPayload) for value in payloads):
        raise AssertionError("known fixture datatype unexpectedly compiled as opaque")
    literals = [
        {
            "payload_json": value.canonical_bytes().decode(),
            "source_literal_id": index,
        }
        for index, value in enumerate(payloads)
    ]
    pairs = [
        {
            "comparison": _comparison(left, right),
            "identity_equal": left.data_identity == right.data_identity,
            "left": left_index,
            "right": right_index,
        }
        for left_index, left in enumerate(compiled)
        for right_index, right in enumerate(compiled)
    ]
    return {
        "literal_count": len(literals),
        "literals": literals,
        "pair_count": len(pairs),
        "pairs": pairs,
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
