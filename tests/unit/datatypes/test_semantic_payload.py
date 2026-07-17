from __future__ import annotations

import json

import pyowl_core.model as owl
import pytest

import pyhermit.datatypes.semantic as semantic_module
from pyhermit.datatypes import (
    RDF_PLAIN_LITERAL,
    RDF_XML_LITERAL,
    XSD_ANY_URI,
    XSD_BASE64_BINARY,
    XSD_BOOLEAN,
    XSD_DATE_TIME,
    XSD_DOUBLE,
    XSD_FLOAT,
    XSD_HEX_BINARY,
    XSD_INTEGER,
    XSD_MAX_INCLUSIVE,
    XSD_MIN_INCLUSIVE,
    XSD_STRING,
    DataRangePayloadKind,
    DatatypeLimits,
    DatatypeSemanticEvaluator,
    LexicalCompatibility,
    LiteralSemanticPayload,
    OpaqueLiteralSemanticPayload,
    compile_datatype_semantic_model,
    compile_literal,
    compile_literal_semantic_payload,
    decode_datatype_semantic_model,
    decode_literal_semantic_payload,
)
from pyhermit.exceptions import (
    OntologyProfileError,
    ResourceLimitError,
    UnsupportedDatatypeError,
)


def datatype(iri: str) -> owl.Datatype:
    return owl.Datatype(owl.IRI(iri))


def literal(lexical: str, datatype_iri: str, language: str | None = None) -> owl.Literal:
    return owl.Literal(lexical, datatype(datatype_iri), language)


@pytest.mark.parametrize(
    ("lexical", "datatype_iri", "language"),
    [
        ("+00042", XSD_INTEGER, None),
        ("true", XSD_BOOLEAN, None),
        ("-0", XSD_FLOAT, None),
        ("NaN", XSD_DOUBLE, None),
        ("hello", XSD_STRING, None),
        ("colour", RDF_PLAIN_LITERAL, "en-GB"),
        ("0aFF", XSD_HEX_BINARY, None),
        (" C v 8 = ", XSD_BASE64_BINARY, None),
        ("urn:payload:test", XSD_ANY_URI, None),
        ('<a y="2" x="1"/>', RDF_XML_LITERAL, None),
        ("2000-01-01T01:00:00+01:00", XSD_DATE_TIME, None),
    ],
)
def test_literal_payload_round_trip_preserves_all_three_relations(
    lexical: str,
    datatype_iri: str,
    language: str | None,
) -> None:
    source = literal(lexical, datatype_iri, language)
    compiled = compile_literal(source)
    payload = compile_literal_semantic_payload(compiled)
    decoded = decode_literal_semantic_payload(payload.canonical_bytes())
    restored = decoded.to_compiled()

    assert decoded == payload
    assert restored.source_literal == source
    assert restored.source_identity == compiled.source_identity
    assert restored.data_identity == compiled.data_identity
    assert restored.comparison == compiled.comparison
    assert restored.compatibility is LexicalCompatibility.OWL2
    assert decoded.canonical_digest() == payload.canonical_digest()


def test_literal_payload_keeps_identity_separate_from_comparison() -> None:
    negative = compile_literal_semantic_payload(literal("-0", XSD_FLOAT))
    positive = compile_literal_semantic_payload(literal("+0", XSD_FLOAT))
    assert negative.data_identity != positive.data_identity
    assert negative.comparison == positive.comparison
    assert negative.lexical_form != positive.lexical_form


def test_payload_rejects_mismatched_identity_and_comparison() -> None:
    one = compile_literal_semantic_payload(literal("1", XSD_INTEGER))
    two = compile_literal_semantic_payload(literal("2", XSD_INTEGER))
    with pytest.raises(ValueError, match="do not describe one value"):
        LiteralSemanticPayload(
            one.lexical_form,
            one.datatype_iri,
            one.language,
            one.data_identity,
            two.comparison,
            one.compatibility,
        )


def test_opaque_literal_payload_preserves_source_without_inventing_value_semantics() -> None:
    unknown_iri = "urn:test:datatype:opaque-literal"
    source = literal("unparsed source", unknown_iri)
    with pytest.raises(UnsupportedDatatypeError):
        compile_literal_semantic_payload(source)

    payload = compile_literal_semantic_payload(source, allow_opaque=True)
    assert isinstance(payload, OpaqueLiteralSemanticPayload)
    assert payload.opaque_identity == (
        "opaque-source-literal-v1",
        "unparsed source",
        unknown_iri,
        None,
    )
    decoded = decode_literal_semantic_payload(payload.canonical_bytes())
    assert decoded == payload
    assert isinstance(decoded, OpaqueLiteralSemanticPayload)
    assert decoded.source_literal() == source

    known_model = compile_datatype_semantic_model((datatype(XSD_STRING),))
    with pytest.raises(UnsupportedDatatypeError):
        DatatypeSemanticEvaluator(known_model).contains(0, decoded)


def _semantic_fixture() -> tuple[
    tuple[owl.DataRange, ...],
    tuple[owl.DatatypeDefinition, ...],
]:
    small = datatype("urn:test:datatype:small")
    selected = datatype("urn:test:datatype:selected")
    lower = owl.FacetRestriction(
        owl.IRI(XSD_MIN_INCLUSIVE),
        literal("0", XSD_INTEGER),
    )
    upper = owl.FacetRestriction(
        owl.IRI(XSD_MAX_INCLUSIVE),
        literal("10", XSD_INTEGER),
    )
    restricted = owl.DatatypeRestriction(
        datatype(XSD_INTEGER),
        owl.CanonicalSet((lower, upper)),
    )
    word = owl.DataOneOf(
        owl.CanonicalSet(
            (
                literal("ok", XSD_STRING),
                # This alias is one data value, not a second enumeration member.
                literal("01", XSD_INTEGER),
            )
        )
    )
    definitions = (
        owl.DatatypeDefinition(small, restricted),
        owl.DatatypeDefinition(
            selected,
            owl.DataUnionOf(owl.CanonicalSet((small, word))),
        ),
    )
    roots: tuple[owl.DataRange, ...] = (
        selected,
        owl.DataComplementOf(small),
        word,
        owl.DataIntersectionOf(owl.CanonicalSet((selected, owl.DataComplementOf(word)))),
    )
    return roots, definitions


def test_model_payload_executes_facets_enumerations_mixed_families_and_aliases(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    roots, definitions = _semantic_fixture()
    model = compile_datatype_semantic_model(roots, definitions=definitions)
    encoded = model.canonical_bytes()
    decoded = decode_datatype_semantic_model(encoded)
    assert decoded == model
    assert decoded.canonical_bytes() == encoded
    assert tuple(item.datatype_iri for item in model.definitions) == (
        "urn:test:datatype:selected",
        "urn:test:datatype:small",
    )
    assert model.data_ranges[2].kind is DataRangePayloadKind.ENUMERATION

    # Evaluation reconstructs tagged semantic records and family ranges.  It must not
    # invoke the lexical compiler after the model boundary has been frozen.
    monkeypatch.setattr(
        semantic_module,
        "compile_literal",
        lambda *args, **kwargs: (_ for _ in ()).throw(AssertionError("lexical reparse")),
    )
    evaluator = DatatypeSemanticEvaluator(decoded)
    integer_one = compile_literal(literal("1", XSD_INTEGER))
    decimal_alias = compile_literal(literal("1.0", "http://www.w3.org/2001/XMLSchema#decimal"))
    eleven = compile_literal(literal("11", XSD_INTEGER))
    word = compile_literal(literal("ok", XSD_STRING))
    other_word = compile_literal(literal("no", XSD_STRING))

    assert evaluator.contains(0, integer_one)
    assert evaluator.contains(0, word)
    assert not evaluator.contains(0, eleven)
    assert evaluator.contains(1, eleven)
    assert evaluator.contains(1, word)
    assert not evaluator.contains(1, integer_one)
    assert evaluator.contains(2, integer_one)
    assert evaluator.contains(2, decimal_alias)
    assert evaluator.contains(2, word)
    assert not evaluator.contains(2, other_word)
    assert evaluator.contains(3, compile_literal(literal("2", XSD_INTEGER)))
    assert not evaluator.contains(3, integer_one)
    assert not evaluator.contains(3, word)


def test_semantic_model_canonicalizes_commutative_input_order() -> None:
    one = owl.DataOneOf(owl.CanonicalSet((literal("1", XSD_INTEGER),)))
    text = owl.DataOneOf(owl.CanonicalSet((literal("x", XSD_STRING),)))
    first = owl.DataUnionOf(owl.CanonicalSet((one, text)))
    second = owl.DataUnionOf(owl.CanonicalSet((text, one)))
    assert compile_datatype_semantic_model((first,)).canonical_bytes() == (
        compile_datatype_semantic_model((second,)).canonical_bytes()
    )


def test_custom_definition_graph_rejects_cycles_duplicates_and_unknowns() -> None:
    first = datatype("urn:test:datatype:first")
    second = datatype("urn:test:datatype:second")
    cyclic = (
        owl.DatatypeDefinition(first, second),
        owl.DatatypeDefinition(second, first),
    )
    with pytest.raises(OntologyProfileError) as cycle:
        compile_datatype_semantic_model((first,), definitions=cyclic)
    assert cycle.value.code == "RECURSIVE_DATATYPE_DEFINITION"

    duplicate = (
        owl.DatatypeDefinition(first, datatype(XSD_INTEGER)),
        owl.DatatypeDefinition(first, datatype(XSD_STRING)),
    )
    with pytest.raises(OntologyProfileError) as repeated:
        compile_datatype_semantic_model((first,), definitions=duplicate)
    assert repeated.value.code == "DUPLICATE_DATATYPE_DEFINITION"

    with pytest.raises(UnsupportedDatatypeError) as unknown:
        compile_datatype_semantic_model((datatype("urn:test:datatype:unknown"),))
    assert unknown.value.context["datatype_iri"] == "urn:test:datatype:unknown"

    with pytest.raises(OntologyProfileError) as built_in:
        compile_datatype_semantic_model(
            (datatype(XSD_INTEGER),),
            definitions=(owl.DatatypeDefinition(datatype(XSD_INTEGER), datatype(XSD_STRING)),),
        )
    assert built_in.value.code == "BUILTIN_DATATYPE_REDEFINITION"


def test_declaration_only_opaque_datatype_keeps_dense_id_and_fails_on_evaluation() -> None:
    unknown_iri = "urn:test:datatype:declaration-only"
    model = compile_datatype_semantic_model(
        (datatype(XSD_STRING), datatype(unknown_iri), datatype(XSD_INTEGER)),
        opaque_datatype_iris=(unknown_iri,),
    )
    assert model.opaque_data_range_ids == (1,)
    assert model.data_ranges[1].kind is DataRangePayloadKind.OPAQUE
    decoded = decode_datatype_semantic_model(model.canonical_bytes())
    assert decoded.opaque_data_range_ids == (1,)

    evaluator = DatatypeSemanticEvaluator(decoded)
    assert evaluator.contains(0, compile_literal(literal("text", XSD_STRING)))
    assert evaluator.contains(2, compile_literal(literal("1", XSD_INTEGER)))
    with pytest.raises(UnsupportedDatatypeError) as unsupported:
        evaluator.contains(1, compile_literal(literal("1", XSD_INTEGER)))
    assert unsupported.value.context["datatype_iri"] == unknown_iri


def test_decoder_rejects_noncanonical_unknown_version_and_oversize_payloads() -> None:
    roots, definitions = _semantic_fixture()
    model = compile_datatype_semantic_model(roots, definitions=definitions)
    canonical = model.canonical_bytes()
    parsed = json.loads(canonical)

    assert isinstance(parsed, dict)
    parsed["unknown"] = True
    with pytest.raises(ValueError, match="unknown"):
        decode_datatype_semantic_model(
            json.dumps(parsed, sort_keys=True, separators=(",", ":")).encode()
        )

    parsed.pop("unknown")
    parsed["schema_version"] = 2
    with pytest.raises(ValueError, match="unsupported"):
        decode_datatype_semantic_model(
            json.dumps(parsed, sort_keys=True, separators=(",", ":")).encode()
        )

    with pytest.raises(ValueError, match="not canonical"):
        decode_datatype_semantic_model(b" " + canonical)

    with pytest.raises(ResourceLimitError) as oversized:
        decode_datatype_semantic_model(
            canonical,
            limits=DatatypeLimits(max_semantic_payload_bytes=len(canonical) - 1),
        )
    assert oversized.value.limit == "max_semantic_payload_bytes"


def test_compilation_and_evaluation_honor_depth_and_cancellation_controls() -> None:
    one = owl.DataOneOf(owl.CanonicalSet((literal("1", XSD_INTEGER),)))
    two = owl.DataOneOf(owl.CanonicalSet((literal("2", XSD_INTEGER),)))
    nested: owl.DataRange = owl.DataUnionOf(owl.CanonicalSet((one, two)))
    for _ in range(4):
        nested = owl.DataComplementOf(nested)
    with pytest.raises(ResourceLimitError) as depth:
        compile_datatype_semantic_model(
            (nested,),
            limits=DatatypeLimits(max_data_range_depth=3),
        )
    assert depth.value.limit == "max_data_range_depth"
