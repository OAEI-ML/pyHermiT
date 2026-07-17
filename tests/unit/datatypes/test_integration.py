from __future__ import annotations

import pyowl_core.model as owl
import pytest

import pyhermit.datatypes.integration as integration_module
from pyhermit.datatypes import (
    XSD_INTEGER,
    XSD_MAX_INCLUSIVE,
    XSD_MIN_INCLUSIVE,
    XSD_STRING,
    DatatypeConstraintSolver,
    DatatypeLimits,
    EqualityConstraint,
    LexicalCompatibility,
    OpaqueLiteralSemanticPayload,
    SemanticDatatypeConstraintComponent,
    SemanticFixedValueConstraint,
    SemanticRangeConstraint,
    compile_datatype_constraint_component,
    compile_datatype_semantic_model,
    compile_literal_semantic_payload,
)
from pyhermit.events import CancellationSource
from pyhermit.exceptions import ReasonerInterruptedError, UnsupportedDatatypeError


def datatype(iri: str) -> owl.Datatype:
    return owl.Datatype(owl.IRI(iri))


def literal(lexical: str, iri: str) -> owl.Literal:
    return owl.Literal(lexical, datatype(iri))


def test_adapter_resolves_each_dense_range_once_and_preserves_dependencies(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    model = compile_datatype_semantic_model((datatype(XSD_INTEGER), datatype(XSD_STRING)))
    one = compile_literal_semantic_payload(literal("01", XSD_INTEGER))
    component = SemanticDatatypeConstraintComponent(
        variables=(1, 0),
        ranges=(
            SemanticRangeConstraint(0, 0, dependencies=frozenset({10})),
            SemanticRangeConstraint(1, 0, dependencies=frozenset({11})),
        ),
        fixed_values=(SemanticFixedValueConstraint(0, one, frozenset({12})),),
        equalities=(EqualityConstraint(0, 1, frozenset({13})),),
    )
    calls: list[int] = []
    original = integration_module.DataDomainRange.from_model.__func__

    def counted(cls: type[object], *args: object, **kwargs: object) -> object:
        calls.append(args[1])
        return original(cls, *args, **kwargs)

    monkeypatch.setattr(
        integration_module.DataDomainRange,
        "from_model",
        classmethod(counted),
    )
    executable = compile_datatype_constraint_component(model, component)

    assert calls == [0]
    assert executable.variables == (0, 1)
    assert executable.ranges[0].dependencies == frozenset({10})
    assert executable.fixed_values[0].value.source_literal == literal("01", XSD_INTEGER)
    assert DatatypeConstraintSolver().solve(executable).satisfiable


def test_adapter_executes_custom_definitions_without_reparsing_literals() -> None:
    small = datatype("urn:test:datatype:small-integration")
    restriction = owl.DatatypeRestriction(
        datatype(XSD_INTEGER),
        owl.CanonicalSet(
            (
                owl.FacetRestriction(owl.IRI(XSD_MIN_INCLUSIVE), literal("0", XSD_INTEGER)),
                owl.FacetRestriction(owl.IRI(XSD_MAX_INCLUSIVE), literal("2", XSD_INTEGER)),
            )
        ),
    )
    model = compile_datatype_semantic_model(
        (small,),
        definitions=(owl.DatatypeDefinition(small, restriction),),
    )
    outside = compile_literal_semantic_payload(literal("3", XSD_INTEGER))
    executable = compile_datatype_constraint_component(
        model,
        SemanticDatatypeConstraintComponent(
            variables=(0,),
            ranges=(SemanticRangeConstraint(0, 0),),
            fixed_values=(SemanticFixedValueConstraint(0, outside),),
        ),
    )
    assert not DatatypeConstraintSolver().solve(executable).satisfiable


def test_adapter_fails_closed_for_dangling_and_opaque_semantics() -> None:
    model = compile_datatype_semantic_model((datatype(XSD_INTEGER),))
    with pytest.raises(ValueError, match="dangling"):
        compile_datatype_constraint_component(
            model,
            SemanticDatatypeConstraintComponent(
                variables=(0,),
                ranges=(SemanticRangeConstraint(0, 1),),
            ),
        )

    unknown = "urn:test:datatype:opaque-integration"
    opaque_model = compile_datatype_semantic_model(
        (datatype(unknown),),
        opaque_datatype_iris=(unknown,),
    )
    with pytest.raises(UnsupportedDatatypeError):
        compile_datatype_constraint_component(
            opaque_model,
            SemanticDatatypeConstraintComponent(
                variables=(0,),
                ranges=(SemanticRangeConstraint(0, 0),),
            ),
        )

    opaque_literal = OpaqueLiteralSemanticPayload(
        "source",
        unknown,
        None,
        LexicalCompatibility.OWL2,
    )
    with pytest.raises(UnsupportedDatatypeError, match="opaque literal"):
        compile_datatype_constraint_component(
            model,
            SemanticDatatypeConstraintComponent(
                variables=(0,),
                fixed_values=(SemanticFixedValueConstraint(0, opaque_literal),),
            ),
        )


def test_adapter_validates_boundaries_and_honours_cancellation() -> None:
    with pytest.raises(ValueError, match="outside"):
        SemanticDatatypeConstraintComponent(
            variables=(0,),
            ranges=(SemanticRangeConstraint(1, 0),),
        )
    with pytest.raises(TypeError, match="data_range_id"):
        SemanticRangeConstraint(0, True)

    model = compile_datatype_semantic_model((datatype(XSD_INTEGER),))
    component = SemanticDatatypeConstraintComponent(variables=(0,))
    cancellation = CancellationSource()
    cancellation.interrupt("integration adapter test")
    with pytest.raises(ReasonerInterruptedError, match="integration adapter test"):
        compile_datatype_constraint_component(
            model,
            component,
            limits=DatatypeLimits(),
            cancellation=cancellation.token,
        )
