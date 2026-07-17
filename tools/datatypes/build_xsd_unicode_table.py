#!/usr/bin/env python3
"""Generate the compact UCD 3.2 category table used by native XSD regexes.

SPDX-License-Identifier: LGPL-3.0-or-later
"""

from __future__ import annotations

import argparse
import unicodedata
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
DEFAULT_OUTPUT = ROOT / "native" / "src" / "datatypes" / "xsd_unicode_3_2.rs"

XML_INTERVALS = (
    (0x9, 0xA),
    (0xD, 0xD),
    (0x20, 0xD7FF),
    (0xE000, 0xFFFD),
    (0x10000, 0x10FFFF),
)
CATEGORIES = (
    "Lu",
    "Ll",
    "Lt",
    "Lm",
    "Lo",
    "Mn",
    "Mc",
    "Me",
    "Nd",
    "Nl",
    "No",
    "Pc",
    "Pd",
    "Ps",
    "Pe",
    "Pi",
    "Pf",
    "Po",
    "Zs",
    "Zl",
    "Zp",
    "Sm",
    "Sc",
    "Sk",
    "So",
    "Cc",
    "Cf",
    "Co",
    "Cn",
)


def _ranges() -> tuple[tuple[int, int, int], ...]:
    category_ids = {name: index for index, name in enumerate(CATEGORIES)}
    ranges: list[tuple[int, int, int]] = []
    start: int | None = None
    previous = -2
    previous_category: int | None = None
    for lower, upper in XML_INTERVALS:
        for codepoint in range(lower, upper + 1):
            category = category_ids[unicodedata.ucd_3_2_0.category(chr(codepoint))]
            if start is None or category != previous_category or codepoint != previous + 1:
                if start is not None and previous_category is not None:
                    ranges.append((start, previous, previous_category))
                start = codepoint
                previous_category = category
            previous = codepoint
    if start is not None and previous_category is not None:
        ranges.append((start, previous, previous_category))
    return tuple(ranges)


def render() -> str:
    if unicodedata.ucd_3_2_0.unidata_version != "3.2.0":
        raise RuntimeError("Python does not expose the required Unicode 3.2 database")
    names = (
        '    "Lu", "Ll", "Lt", "Lm", "Lo", "Mn", "Mc", "Me", "Nd", "Nl", "No", "Pc", '
        '"Pd", "Ps", "Pe", "Pi",\n'
        '    "Pf", "Po", "Zs", "Zl", "Zp", "Sm", "Sc", "Sk", "So", "Cc", "Cf", "Co", '
        '"Cn",'
    )
    packed = [(lower << 26) | (upper << 5) | category for lower, upper, category in _ranges()]
    rows = [f"    0x{value:x}," for value in packed]
    return (
        "//! Generated XML-character general-category runs from Python's UCD 3.2.\n"
        "//! Regenerate with `tools/datatypes/build_xsd_unicode_table.py`.\n"
        "// SPDX-License-Identifier: LGPL-3.0-or-later\n\n"
        "#![allow(clippy::unreadable_literal)]\n\n"
        'pub(super) const PINNED_UNICODE_VERSION: &str = "3.2.0";\n'
        f"pub(super) const CATEGORY_CODE_NAMES: [&str; {len(CATEGORIES)}] = [\n{names}\n];\n"
        "pub(super) const CATEGORY_RANGES_PACKED: &[u64] = &[\n" + "\n".join(rows) + "\n];\n"
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    rendered = render()
    if args.check:
        if not args.output.is_file() or args.output.read_text(encoding="utf-8") != rendered:
            raise SystemExit(f"stale generated Unicode table: {args.output}")
        return
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(rendered, encoding="utf-8")


if __name__ == "__main__":
    main()
