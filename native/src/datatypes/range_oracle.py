#!/usr/bin/env python3
"""Generate the small WPR3 primitive-range differential fixture.

Run from the repository root with both local source trees available::

    PYTHONPATH=src:../pyOWLCore/src python3 \
        native/src/datatypes/range_oracle.py

The output is canonical JSON so it can be compared byte-for-byte with
``range_oracle_v1.json``.  This generator imports the production Python range
implementations; it does not duplicate their interval algorithms.
"""

from __future__ import annotations

import json

from pyhermit.datatypes.domain import _numeric_first_identity
from pyhermit.datatypes.ieee_ranges import IEEERange
from pyhermit.datatypes.model import (
    BinaryKind,
    BooleanComparison,
    DatatypeLimits,
    IEEEFormat,
    IEEEIdentity,
    NumericComparison,
    NumericDomain,
)
from pyhermit.datatypes.nonnumeric_ranges import BinaryRange, LengthRange
from pyhermit.datatypes.ranges import BooleanRange, NumericInterval, NumericRange


def mask(values: list[bool]) -> str:
    return "".join("1" if value else "0" for value in values)


def main() -> None:
    integer_probes = list(range(-5, 6))
    left = NumericRange.between(
        NumericDomain.INTEGER,
        lower=NumericComparison(-2),
        lower_inclusive=True,
        upper=NumericComparison(2),
        upper_inclusive=True,
    )
    right = NumericRange(
        NumericDomain.INTEGER,
        (
            # Two separated components exercise canonical union and complement.
            NumericInterval(NumericComparison(-4), True, NumericComparison(-1), False),
            NumericInterval(NumericComparison(1), False, NumericComparison(4), True),
        ),
    )
    numeric_values = [NumericComparison(value) for value in integer_probes]
    decimal_probes = [
        NumericComparison(1, 3),
        NumericComparison(1, 2),
        NumericComparison(1, 5),
        NumericComparison(1),
    ]
    decimal = NumericRange.between(
        NumericDomain.DECIMAL,
        lower=NumericComparison(0),
        lower_inclusive=False,
        upper=NumericComparison(1),
        upper_inclusive=True,
    )
    forbidden = frozenset()
    witnesses = []
    for _ in range(3):
        witness = _numeric_first_identity(left, forbidden)
        witnesses.append(list(witness.as_tagged()[1:]))
        forbidden |= {witness}

    booleans = BooleanRange(frozenset((False,)))
    bool_probe = [BooleanComparison(False), BooleanComparison(True)]

    positive_zero = IEEEIdentity(IEEEFormat.FLOAT32, 0x00000000)
    zero = IEEERange.bounded(
        IEEEFormat.FLOAT32,
        lower=positive_zero,
        lower_inclusive=True,
        upper=positive_zero,
        upper_inclusive=True,
    )
    ieee_probe_bits = [
        0xFF800000,
        0xBF800000,
        0x80000000,
        0x00000000,
        0x3F800000,
        0x7F800000,
        0x7FC00000,
    ]
    finite_unit = IEEERange.bounded(
        IEEEFormat.FLOAT32,
        lower=IEEEIdentity(IEEEFormat.FLOAT32, 0xBF800000),
        lower_inclusive=True,
        upper=IEEEIdentity(IEEEFormat.FLOAT32, 0x3F800000),
        upper_inclusive=True,
    )

    lengths = LengthRange.between(2, 4)
    length_probes = list(range(8))
    binary = BinaryRange(BinaryKind.HEX, LengthRange.between(0, 1))
    binary_forbidden = []
    binary_witnesses = []
    for _ in range(3):
        witness = binary.first_identity(excluding=binary_forbidden)
        binary_witnesses.append(witness.octets.hex())
        binary_forbidden.append(witness)

    fixture = {
        "binary": {
            "cardinality": str(binary.finite_cardinality()),
            "witness_hex": binary_witnesses,
        },
        "boolean": {
            "complement": mask([booleans.complement().contains(value) for value in bool_probe]),
            "range": mask([booleans.contains(value) for value in bool_probe]),
        },
        "ieee": {
            "finite_unit_complement": mask(
                [
                    finite_unit.complement().contains(IEEEIdentity(IEEEFormat.FLOAT32, bits))
                    for bits in ieee_probe_bits
                ]
            ),
            "probe_bits": [f"{bits:08x}" for bits in ieee_probe_bits],
            "zero_enumeration": [
                f"{identity.bits:08x}"
                for identity in zero.enumerate_values(limits=DatatypeLimits())
            ],
        },
        "length": {
            "complement": mask([lengths.complement().contains(value) for value in length_probes]),
            "range": mask([lengths.contains(value) for value in length_probes]),
        },
        "numeric": {
            "complement": mask([left.complement().contains(value) for value in numeric_values]),
            "decimal": mask([decimal.contains(value) for value in decimal_probes]),
            "intersection": mask(
                [left.intersection(right).contains(value) for value in numeric_values]
            ),
            "left": mask([left.contains(value) for value in numeric_values]),
            "right": mask([right.contains(value) for value in numeric_values]),
            "union": mask([left.union(right).contains(value) for value in numeric_values]),
            "witness_tokens": witnesses,
        },
        "schema_version": 1,
    }
    print(json.dumps(fixture, sort_keys=True, separators=(",", ":")))


if __name__ == "__main__":
    main()
