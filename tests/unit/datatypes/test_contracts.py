from __future__ import annotations

import dataclasses

import pytest
from pyowl_core.model import IRI, Datatype, Literal

from pyhermit.datatypes import (
    XSD_INTEGER,
    CompiledLiteral,
    DatatypeLimits,
    LexicalCompatibility,
    NumericComparison,
    NumericDatatypeSpec,
    NumericDomain,
    NumericIdentity,
    SourceLiteralIdentity,
)


def test_rational_identity_normalizes_sign_and_gcd_once() -> None:
    assert NumericIdentity(6, -8) == NumericIdentity(-3, 4)
    assert NumericComparison(10, 20) == NumericComparison(1, 2)
    assert NumericComparison(-1, 3).compare(NumericComparison(-2, 5)) > 0
    with pytest.raises(ValueError, match="nonzero"):
        NumericIdentity(1, 0)
    with pytest.raises(TypeError, match="numerator"):
        NumericIdentity(True)  # type: ignore[arg-type]


@pytest.mark.parametrize(
    "changes",
    [
        {"max_lexical_characters": 0},
        {"max_numeric_digits": -1},
        {"max_decimal_exponent": True},
        {"max_enumeration_values": 0},
        {"max_binary_bytes": 0},
        {"max_pattern_states": 0},
        {"max_pattern_transitions": 0},
        {"max_xml_depth": 0},
        {"max_xml_nodes": 0},
        {"cancellation_poll_stride": 0},
    ],
)
def test_datatype_limits_validate_every_control(changes: dict[str, object]) -> None:
    with pytest.raises(ValueError, match="positive integer"):
        DatatypeLimits(**changes)  # type: ignore[arg-type]


def test_source_identity_validates_but_preserves_empty_lexical_form() -> None:
    identity = SourceLiteralIdentity("", XSD_INTEGER, None)
    assert identity.lexical_form == ""
    with pytest.raises(ValueError, match="datatype_iri"):
        SourceLiteralIdentity("1", "", None)
    with pytest.raises(ValueError, match="language"):
        SourceLiteralIdentity("text", XSD_INTEGER, "")


def test_compiled_literal_rejects_a_source_token_from_another_core_literal() -> None:
    source = Literal("1", Datatype(IRI(XSD_INTEGER)))
    wrong = SourceLiteralIdentity("01", XSD_INTEGER, None)
    with pytest.raises(ValueError, match="source_identity"):
        CompiledLiteral(
            source,
            wrong,
            NumericIdentity(1),
            NumericComparison(1),
            LexicalCompatibility.OWL2,
        )


def test_numeric_datatype_spec_and_compiled_values_are_immutable() -> None:
    spec = NumericDatatypeSpec("urn:test", NumericDomain.INTEGER, 0, 10)
    with pytest.raises(dataclasses.FrozenInstanceError):
        spec.upper_inclusive = 11  # type: ignore[misc]
    with pytest.raises(TypeError, match="lower_inclusive"):
        NumericDatatypeSpec("urn:test", NumericDomain.INTEGER, True, 10)  # type: ignore[arg-type]
    with pytest.raises(ValueError, match="lower bound"):
        NumericDatatypeSpec("urn:test", NumericDomain.INTEGER, 11, 10)
