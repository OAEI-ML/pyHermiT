"""Bounded assertion syntax for the native query compiler; no ontology traversal.

SPDX-License-Identifier: LGPL-3.0-or-later

Only requested symbols use the native metadata lookup. Unbound named classes and
individuals have query-local ordinals; scoped anonymous IDs use the full native
individual index before receiving an ordinal. Roles and literals must be retained.
"""

from __future__ import annotations

import json
from collections.abc import Iterable, Mapping
from typing import NoReturn

import pyowl_core.model as owl

from pyhermit.backends.native_context import NativeServiceContext, _NativeDomainMapping
from pyhermit.exceptions import FeatureNotImplementedError, ResourceLimitError

MAX_QUERY_BYTES = 1024 * 1024
MAX_QUERY_NODES = 16_384
MAX_QUERY_DEPTH = 64


def _ineligible(reason: str) -> NoReturn:
    raise FeatureNotImplementedError(reason, feature_id="native_query_delta_ineligible")


def _bound(name: str, observed: int, allowed: int) -> None:
    if observed > allowed:
        raise ResourceLimitError(
            "native query syntax exceeds its resource limit",
            limit=name,
            observed=observed,
            allowed=allowed,
        )


class _Syntax:
    def __init__(self, context: NativeServiceContext) -> None:
        self.context = context
        self.classes: dict[owl.StructuralNode, int] = {}
        self.individuals: dict[owl.StructuralNode, int] = {}
        self.nodes = 0

    def tick(self, depth: int = 0) -> None:
        self.nodes += 1
        _bound("native_query_nodes", self.nodes, MAX_QUERY_NODES)
        _bound("native_query_depth", depth, MAX_QUERY_DEPTH)

    def lookup(
        self, values: Mapping[int, owl.StructuralNode], value: owl.StructuralNode
    ) -> int | None:
        if not isinstance(values, _NativeDomainMapping):
            _ineligible("native query serialization requires retained native symbol domains")
        try:
            return values.native_id(value)
        except ValueError:
            return None

    def retained(self, values: Mapping[int, owl.StructuralNode], value: owl.StructuralNode) -> int:
        self.tick()
        identifier = self.lookup(values, value)
        if identifier is None:
            _ineligible("native query role or literal is absent from the permanent domain")
        return identifier

    def term(self, value: owl.StructuralNode, *, individual: bool) -> dict[str, int]:
        self.tick()
        values: Mapping[int, owl.StructuralNode]
        if individual:
            values = self.context.individual_ids
            local = self.individuals
            if isinstance(value, owl.AnonymousIndividual):
                if not isinstance(values, _NativeDomainMapping):
                    _ineligible("anonymous query identities require native permanent-scope lookup")
                identifier = values.native_query_individual_id(value)
                if identifier is not None:
                    return {"base": identifier}
                return {"local": local.setdefault(value, len(local))}
            if not isinstance(value, owl.NamedIndividual):
                _ineligible("native assertion queries require individual identities")
        else:
            if not isinstance(value, owl.Class):
                _ineligible("native class symbols must be named classes")
            values = self.context.class_ids
            local = self.classes
        identifier = self.lookup(values, value)
        if identifier is not None:
            return {"base": identifier}
        if not individual and value in (owl.OWL_THING, owl.OWL_NOTHING):
            _ineligible("native query builtin class is absent from the permanent domain")
        return {"local": local.setdefault(value, len(local))}

    def expression(self, value: owl.ClassExpression, depth: int = 0) -> dict[str, object]:
        self.tick(depth)
        if isinstance(value, owl.Class):
            return {"kind": "class", "symbol": self.term(value, individual=False)}
        if isinstance(value, owl.ObjectComplementOf):
            return {"kind": "not", "value": self.expression(value.operand, depth + 1)}
        if isinstance(value, (owl.ObjectIntersectionOf, owl.ObjectUnionOf)):
            return {
                "kind": "and" if isinstance(value, owl.ObjectIntersectionOf) else "or",
                "values": [self.expression(item, depth + 1) for item in value.operands],
            }
        if isinstance(value, owl.ObjectOneOf):
            return {
                "kind": "one_of",
                "individuals": [self.term(item, individual=True) for item in value.individuals],
            }
        if isinstance(value, (owl.ObjectSomeValuesFrom, owl.ObjectAllValuesFrom)):
            return {
                "kind": "some" if isinstance(value, owl.ObjectSomeValuesFrom) else "all",
                "role": self.retained(self.context.object_property_ids, value.property),
                "value": self.expression(value.filler, depth + 1),
            }
        if isinstance(value, owl.ObjectHasSelf):
            return {
                "kind": "self",
                "role": self.retained(self.context.object_property_ids, value.property),
            }
        if isinstance(value, owl.ObjectHasValue):
            return {
                "kind": "has_value",
                "role": self.retained(self.context.object_property_ids, value.property),
                "target": self.term(value.value, individual=True),
            }
        if isinstance(value, owl.DataHasValue):
            return {
                "kind": "data_value",
                "role": self.retained(self.context.data_property_ids, value.property),
                "literal": self.retained(self.context.source_literal_ids, value.value),
            }
        _ineligible(f"unsupported native query class constructor: {type(value).__name__}")

    def axiom(self, value: owl.AxiomNode) -> dict[str, object]:
        self.tick()
        if not isinstance(value, owl.AxiomNode):
            raise TypeError("query axioms must be core AxiomNode values")
        if getattr(value, "annotations", ()):
            _ineligible("annotated query assertions require the full provenance path")
        if isinstance(value, owl.ClassAssertion):
            return {
                "kind": "class",
                "expression": self.expression(value.class_expression),
                "individual": self.term(value.individual, individual=True),
            }
        if isinstance(value, (owl.ObjectPropertyAssertion, owl.NegativeObjectPropertyAssertion)):
            return {
                "kind": "object",
                "role": self.retained(self.context.object_property_ids, value.property),
                "source": self.term(value.source, individual=True),
                "target": self.term(value.target, individual=True),
                "negative": isinstance(value, owl.NegativeObjectPropertyAssertion),
            }
        if isinstance(value, (owl.DataPropertyAssertion, owl.NegativeDataPropertyAssertion)):
            return {
                "kind": "data",
                "role": self.retained(self.context.data_property_ids, value.property),
                "source": self.term(value.source, individual=True),
                "literal": self.retained(self.context.source_literal_ids, value.value),
                "negative": isinstance(value, owl.NegativeDataPropertyAssertion),
            }
        if isinstance(value, (owl.SameIndividual, owl.DifferentIndividuals)):
            return {
                "kind": "same" if isinstance(value, owl.SameIndividual) else "different",
                "individuals": [self.term(item, individual=True) for item in value.individuals],
            }
        _ineligible(f"unsupported native query axiom: {type(value).__name__}")


def serialize_query(axioms: Iterable[owl.AxiomNode], context: NativeServiceContext) -> bytes:
    """Serialize one request, bounded by bytes, syntax nodes, and nesting depth.

    Resource failures propagate rather than selecting a less bounded fallback.
    Batch admission additionally belongs to the native session dispatcher.
    """
    syntax = _Syntax(context)
    values = [syntax.axiom(value) for value in axioms]
    if not values:
        raise ValueError("a native query requires at least one axiom")
    payload = {
        "schema": 1,
        "permanent_program_sha256": context.permanent_program_sha256,
        "axioms": values,
        "individual_count": len(syntax.individuals),
        "class_count": len(syntax.classes),
    }
    output = bytearray()
    for chunk in json.JSONEncoder(separators=(",", ":"), ensure_ascii=True).iterencode(payload):
        encoded = chunk.encode("ascii")
        _bound("native_query_bytes", len(output) + len(encoded), MAX_QUERY_BYTES)
        output.extend(encoded)
    return bytes(output)
