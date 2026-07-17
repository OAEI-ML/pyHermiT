"""Pure-Python datatype semantics (WP07, numeric/Boolean foundation tranche).

SPDX-License-Identifier: LGPL-3.0-or-later

This package is independent of tableau state and imports no Java or native runtime.
It currently exposes the exact numeric and Boolean families only; the remaining WP07
families, full mixed-family algebra, facets, and component solver are deliberately not
claimed here.
"""

from __future__ import annotations

from .literals import (
    NUMERIC_DATATYPES,
    OWL_NAMESPACE,
    OWL_RATIONAL,
    OWL_REAL,
    SUPPORTED_DATATYPES,
    XSD_BOOLEAN,
    XSD_DECIMAL,
    XSD_INTEGER,
    XSD_NAMESPACE,
    NumericDatatypeSpec,
    compile_literal,
    numeric_datatype_spec,
)
from .model import (
    BooleanComparison,
    BooleanIdentity,
    ComparisonValue,
    CompiledLiteral,
    DataIdentity,
    DatatypeLimits,
    LexicalCompatibility,
    NumericComparison,
    NumericDomain,
    NumericIdentity,
    SourceLiteralIdentity,
)
from .ranges import (
    BooleanRange,
    DatatypeRange,
    NumericInterval,
    NumericRange,
    RangeValue,
    numeric_domain_contains,
    range_for_datatype,
)

__all__ = [
    "NUMERIC_DATATYPES",
    "OWL_NAMESPACE",
    "OWL_RATIONAL",
    "OWL_REAL",
    "SUPPORTED_DATATYPES",
    "XSD_BOOLEAN",
    "XSD_DECIMAL",
    "XSD_INTEGER",
    "XSD_NAMESPACE",
    "BooleanComparison",
    "BooleanIdentity",
    "BooleanRange",
    "ComparisonValue",
    "CompiledLiteral",
    "DataIdentity",
    "DatatypeLimits",
    "DatatypeRange",
    "LexicalCompatibility",
    "NumericComparison",
    "NumericDatatypeSpec",
    "NumericDomain",
    "NumericIdentity",
    "NumericInterval",
    "NumericRange",
    "RangeValue",
    "SourceLiteralIdentity",
    "compile_literal",
    "numeric_datatype_spec",
    "numeric_domain_contains",
    "range_for_datatype",
]
