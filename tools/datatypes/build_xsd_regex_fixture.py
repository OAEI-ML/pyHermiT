#!/usr/bin/env python3
"""Build bounded Python/Rust parity cases for the native XSD regex engine.

SPDX-License-Identifier: LGPL-3.0-or-later

The expected values come from pyHermiT's pure-Python derivative engine.  No
external or Java regular-expression runtime participates in fixture generation.
"""

from __future__ import annotations

import argparse
import json
from collections.abc import Iterable
from pathlib import Path

from pyhermit.datatypes.xsd_regex import PINNED_UNICODE_VERSION, XSDRegex
from pyhermit.exceptions import OntologyProfileError

ROOT = Path(__file__).resolve().parents[2]
DEFAULT_OUTPUT = ROOT / "tests" / "data" / "datatypes" / "xsd-regex-native-v1.json"
SCHEMA = "pyhermit.xsd-regex.native-parity.v1"


MEMBERSHIP_SOURCES: tuple[tuple[str, str, tuple[str, ...]], ...] = (
    ("empty-pattern", "", ("", "a", "\n")),
    ("implicitly-anchored-alternative", "ab|cd", ("ab", "cd", "", "a", "xab", "abcd")),
    ("bounded-quantifiers", "a{2,4}b?", ("aa", "aab", "aaaa", "aaaab", "a", "aaaaa")),
    (
        "xsd-character-class-subtraction",
        "[a-z-[aeiou]]+",
        ("b", "bcdf", "z", "a", "bed", "bé", ""),
    ),
    (
        "xml-name-without-colon",
        r"[\i-[:]][\c-[:]]*",
        ("Alpha", "_x", "\u00e9clair", "a-b", "a:b", "1a", ""),
    ),
    ("xsd-space", r"\s+", (" ", "\t\r\n", "\n", "\u00a0", "a", "")),
    (
        "unicode-decimal",
        r"\d+",
        ("0", "\u0665", "\u0967\u0968", "\u00b2", "A", ""),
    ),
    ("xsd-word", r"\w+", ("abc", "\u03b12", "$", "_", "a b", "")),
    (
        "unicode-categories",
        r"\p{Lu}\p{Ll}*",
        ("Abc", "\u0394elta", "A", "abc", "A2"),
    ),
    (
        "ucd-3-2-unassigned",
        r"\p{Cn}",
        ("\U0001f600", "\u20ba", "A", "\uffff", ""),
    ),
    (
        "ucd-3-2-symbol",
        r"\p{So}",
        ("\u00a9", "\u2122", "\U0001f600", "\u20ba", "A"),
    ),
    ("dot-is-an-xml-character", ".", ("A", "\n", "\t", "\x00", "", "AB")),
    ("negated-decimal-class", r"[^\d]+", ("abc", "_", "٣", "a٣", "", "\n")),
    ("finite-breadth-first-order", "[ab]{0,2}", ("", "a", "b", "aa", "ab", "ba", "bb", "aaa")),
)

ALGEBRA_SOURCES: tuple[tuple[str, str, str | None, str, tuple[str, ...]], ...] = (
    (
        "overlapping-intersection",
        "[a-z]+",
        "[a-f]+",
        "intersection",
        ("a", "fade", "face", "z", "ag", ""),
    ),
    ("disjoint-intersection", "a+", "b+", "intersection", ("a", "b", "ab", "")),
    ("finite-union", "[ab]", "[bc]", "union", ("a", "b", "c", "d", "")),
    ("language-complement", "[a-c]", None, "complement", ("", "a", "c", "z", "aa", "\n", "\x00")),
    (
        "finite-set-difference",
        "[a-z]",
        "[aeiou]",
        "difference",
        ("a", "b", "u", "z", "bb", ""),
    ),
)

INVALID_SOURCES: tuple[tuple[str, str], ...] = (
    ("unicode-block-awaits-pinned-inventory", r"\p{IsBasicLatin}"),
    ("reversed-character-range", "[z-a]"),
    ("decreasing-quantifier", "a{3,2}"),
    ("unknown-escape", r"\q"),
    ("unclosed-group", "(abc"),
    ("trailing-metacharacter", "abc]"),
)


def _language_record(name: str, pattern: str, values: Iterable[str]) -> dict[str, object]:
    language = XSDRegex.compile(pattern)
    cardinality = language.finite_cardinality()
    record: dict[str, object] = {
        "name": name,
        "pattern": pattern,
        "samples": [{"matches": language.fullmatch(value), "value": value} for value in values],
        "finite": cardinality is not None,
        "cardinality": None if cardinality is None else str(cardinality),
    }
    if cardinality is not None and cardinality <= 100:
        record["enumeration"] = list(language.enumerate_strings())
    return record


def _algebra_record(
    name: str,
    left_pattern: str,
    right_pattern: str | None,
    operation: str,
    values: Iterable[str],
) -> dict[str, object]:
    left = XSDRegex.compile(left_pattern)
    right = None if right_pattern is None else XSDRegex.compile(right_pattern)
    if operation == "intersection" and right is not None:
        language = left.intersection(right)
    elif operation == "union" and right is not None:
        language = left.union(right)
    elif operation == "complement" and right is None:
        language = left.complement()
    elif operation == "difference" and right is not None:
        language = left.intersection(right.complement())
    else:
        raise ValueError(f"unsupported fixture operation: {operation}")
    cardinality = language.finite_cardinality()
    record: dict[str, object] = {
        "name": name,
        "left": left_pattern,
        "right": right_pattern,
        "operation": operation,
        "empty": language.is_empty_exact(),
        "samples": [{"matches": language.fullmatch(value), "value": value} for value in values],
        "finite": cardinality is not None,
        "cardinality": None if cardinality is None else str(cardinality),
    }
    if cardinality is not None and cardinality <= 100:
        record["enumeration"] = list(language.enumerate_strings())
    return record


def _invalid_record(name: str, pattern: str) -> dict[str, str]:
    try:
        XSDRegex.compile(pattern)
    except (OntologyProfileError, TypeError, ValueError) as error:
        return {
            "exception": type(error).__name__,
            "message": str(error),
            "name": name,
            "pattern": pattern,
        }
    raise AssertionError(f"fixture pattern unexpectedly compiled: {pattern!r}")


def build_fixture() -> dict[str, object]:
    return {
        "schema": SCHEMA,
        "unicode_version": PINNED_UNICODE_VERSION,
        "membership": [_language_record(*source) for source in MEMBERSHIP_SOURCES],
        "algebra": [_algebra_record(*source) for source in ALGEBRA_SOURCES],
        "invalid": [_invalid_record(*source) for source in INVALID_SOURCES],
    }


def render() -> str:
    return json.dumps(build_fixture(), ensure_ascii=True, indent=2, sort_keys=True) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    rendered = render()
    if args.check:
        if not args.output.is_file() or args.output.read_text(encoding="utf-8") != rendered:
            raise SystemExit(f"stale generated XSD regex fixture: {args.output}")
        return
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(rendered, encoding="utf-8")


if __name__ == "__main__":
    main()
