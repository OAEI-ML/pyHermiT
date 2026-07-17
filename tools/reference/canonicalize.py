"""Language-neutral oracle value canonicalization.

The normalized JSON is intentionally independent of OWLAPI and pyowl-core objects.  It is a
comparison/wire format, not a public runtime model.
"""

from __future__ import annotations

import hashlib
import itertools
import math
from collections import defaultdict
from collections.abc import Iterable, Mapping, Sequence
from functools import partial
from typing import Any

from tools.reference._util import canonical_json


class CanonicalizationError(ValueError):
    """Raised when a value cannot be normalized without losing identity."""


def canonical_boolean(value: Any) -> bool:
    if type(value) is not bool:
        raise CanonicalizationError(f"logical boolean must be true/false, not {value!r}")
    return value


def typed_iri(value: str) -> dict[str, str]:
    if not isinstance(value, str) or ":" not in value or any(char.isspace() for char in value):
        raise CanonicalizationError(f"not an absolute IRI: {value!r}")
    return {"kind": "iri", "value": value}


def inverse_property(property_iri: str | Mapping[str, Any]) -> dict[str, Any]:
    direct = (
        typed_iri(property_iri) if isinstance(property_iri, str) else normalize_term(property_iri)
    )
    if direct.get("kind") != "iri":
        raise CanonicalizationError("an inverse property must wrap a named-property IRI")
    return {"kind": "inverse_object_property", "property": direct}


def literal(
    lexical: str,
    *,
    datatype: str | None = None,
    language: str | None = None,
    value_key: str | None = None,
    comparison_key: str | None = None,
) -> dict[str, Any]:
    if not isinstance(lexical, str):
        raise CanonicalizationError("literal lexical form must be a string")
    if datatype is not None and language is not None:
        raise CanonicalizationError("a literal cannot have both datatype and language")
    result: dict[str, Any] = {"kind": "literal", "lexical": lexical}
    if datatype is not None:
        result["datatype"] = typed_iri(datatype)
    elif language is not None:
        if not language or any(char.isspace() for char in language):
            raise CanonicalizationError(f"invalid language tag: {language!r}")
        result["language"] = language.lower()
    else:
        result["datatype"] = typed_iri("http://www.w3.org/2001/XMLSchema#string")
    # term_key preserves RDF-term identity; value_key is an optional reasoner-provided
    # value-space identity (e.g. integer 01 and 1).  They are never conflated.
    result["term_key"] = canonical_json(result)
    if value_key is not None:
        result["value_key"] = value_key
    if comparison_key is not None:
        result["comparison_key"] = comparison_key
    return result


def normalize_term(value: Mapping[str, Any] | str) -> dict[str, Any]:
    if isinstance(value, str):
        return typed_iri(value)
    kind = value.get("kind")
    if kind == "iri":
        return typed_iri(str(value.get("value", "")))
    if kind == "inverse_object_property":
        prop = value.get("property")
        if not isinstance(prop, Mapping):
            raise CanonicalizationError("inverse property is missing property")
        return inverse_property(prop)
    if kind == "literal":
        datatype = value.get("datatype")
        datatype_value = None
        if isinstance(datatype, Mapping):
            datatype_value = str(datatype.get("value", ""))
        language = value.get("language")
        value_key = value.get("value_key")
        comparison_key = value.get("comparison_key")
        return literal(
            str(value.get("lexical", "")),
            datatype=datatype_value,
            language=str(language) if language is not None else None,
            value_key=str(value_key) if value_key is not None else None,
            comparison_key=str(comparison_key) if comparison_key is not None else None,
        )
    if kind == "bnode":
        identifier = value.get("id")
        if not isinstance(identifier, str) or not identifier:
            raise CanonicalizationError("blank node requires a non-empty document-local id")
        return {"kind": "bnode", "id": identifier}
    raise CanonicalizationError(f"unknown term kind: {kind!r}")


def _term_sort_key(term: Mapping[str, Any]) -> str:
    return canonical_json(term)


def canonical_nodes(
    nodes: Iterable[Iterable[Mapping[str, Any] | str]], *, kind: str
) -> list[dict[str, Any]]:
    normalized: dict[str, list[dict[str, Any]]] = {}
    for node in nodes:
        members = sorted((normalize_term(member) for member in node), key=_term_sort_key)
        if not members:
            raise CanonicalizationError("equivalence/same-as nodes cannot be empty")
        key = canonical_json(members)
        normalized[key] = members
    output: list[dict[str, Any]] = []
    for key in sorted(normalized):
        node_id = hashlib.sha256(key.encode("utf-8")).hexdigest()[:24]
        output.append({"id": f"{kind}:{node_id}", "members": normalized[key]})
    return output


def canonical_hierarchy(
    nodes: Iterable[Iterable[Mapping[str, Any] | str]],
    edges: Iterable[Sequence[Iterable[Mapping[str, Any] | str]]],
) -> dict[str, Any]:
    canonical = canonical_nodes(nodes, kind="equivalence")
    id_by_members = {canonical_json(node["members"]): node["id"] for node in canonical}
    normalized_edges: set[tuple[str, str]] = set()
    for edge in edges:
        if len(edge) != 2:
            raise CanonicalizationError("hierarchy edge must be [parent_members, child_members]")
        parent = sorted((normalize_term(term) for term in edge[0]), key=_term_sort_key)
        child = sorted((normalize_term(term) for term in edge[1]), key=_term_sort_key)
        try:
            normalized_edges.add(
                (id_by_members[canonical_json(parent)], id_by_members[canonical_json(child)])
            )
        except KeyError as error:
            raise CanonicalizationError("hierarchy edge names a node not in nodes") from error
    return {
        "kind": "hierarchy",
        "nodes": canonical,
        "direct_edges": [
            {"parent": parent, "child": child} for parent, child in sorted(normalized_edges)
        ],
    }


def canonical_same_as(nodes: Iterable[Iterable[Mapping[str, Any] | str]]) -> dict[str, Any]:
    return {"kind": "same_as", "nodes": canonical_nodes(nodes, kind="same_as")}


def canonical_error(
    category: str, message: str, *, error_type: str | None = None
) -> dict[str, Any]:
    allowed = {"ERROR", "RESOURCE_LIMIT", "TIMEOUT"}
    if category not in allowed:
        raise CanonicalizationError(f"invalid error category: {category!r}")
    # Paths, addresses, and platform-specific stack traces belong in evidence hashes, not in
    # semantic error identity.  Whitespace normalization keeps parser diagnostics reviewable.
    result: dict[str, Any] = {
        "category": category,
        "message": " ".join(message.split()),
    }
    if error_type:
        result["type"] = error_type
    return result


Triple = tuple[Mapping[str, Any], Mapping[str, Any], Mapping[str, Any]]


def canonical_blank_node_triples(
    triples: Iterable[Triple], *, permutation_limit: int = 100_000
) -> list[list[dict[str, Any]]]:
    """Alpha-normalize document-scoped blank nodes in RDF-like triples.

    Refinement usually gives every node a unique structural signature.  Remaining symmetric
    partitions are exhaustively minimized.  The function fails explicitly rather than using
    source labels when a pathological symmetry exceeds ``permutation_limit``.
    """

    normalized = [tuple(normalize_term(term) for term in triple) for triple in triples]
    labels = sorted(
        {str(term["id"]) for triple in normalized for term in triple if term.get("kind") == "bnode"}
    )
    if not labels:
        return [list(triple) for triple in sorted(normalized, key=canonical_json)]

    def skeleton(term: Mapping[str, Any], colors: Mapping[str, str]) -> Any:
        if term.get("kind") != "bnode":
            return term
        return {"kind": "bnode", "color": colors.get(str(term["id"]), "_")}

    colors = {label: "_" for label in labels}
    for _ in range(len(labels) + 1):
        signatures: dict[str, str] = {}
        for label in labels:
            incidents: list[Any] = []
            for triple in normalized:
                for position, term in enumerate(triple):
                    if term.get("kind") == "bnode" and term.get("id") == label:
                        incidents.append(
                            [position, [skeleton(candidate, colors) for candidate in triple]]
                        )
            signatures[label] = hashlib.sha256(
                canonical_json(sorted(incidents, key=canonical_json)).encode("utf-8")
            ).hexdigest()
        palette = {
            value: str(index) for index, value in enumerate(sorted(set(signatures.values())))
        }
        updated = {label: palette[signatures[label]] for label in labels}
        if updated == colors:
            break
        colors = updated

    partitions: dict[str, list[str]] = defaultdict(list)
    for label, color in colors.items():
        partitions[color].append(label)
    groups = [partitions[color] for color in sorted(partitions)]
    combinations = math.prod(math.factorial(len(group)) for group in groups)
    if combinations > permutation_limit:
        raise CanonicalizationError(
            f"ambiguous blank-node graph needs {combinations} permutations; "
            f"limit is {permutation_limit}"
        )

    best: tuple[str, list[list[dict[str, Any]]]] | None = None
    permutations = [list(itertools.permutations(group)) for group in groups]
    for ordered_groups in itertools.product(*permutations):
        order = [label for group in ordered_groups for label in group]
        replacement = {label: f"b{index}" for index, label in enumerate(order)}
        candidate: list[list[dict[str, Any]]] = []
        for triple in normalized:
            rewritten: list[dict[str, Any]] = []
            for term in triple:
                if term.get("kind") == "bnode":
                    rewritten.append({"kind": "bnode", "id": replacement[str(term["id"])]})
                else:
                    rewritten.append(dict(term))
            candidate.append(rewritten)
        candidate.sort(key=canonical_json)
        encoded = canonical_json(candidate)
        if best is None or encoded < best[0]:
            best = (encoded, candidate)
    assert best is not None
    return best[1]


_NORMALIZATION_ENTITY_KINDS = {
    "class",
    "data_property",
    "datatype",
    "named_individual",
    "object_property",
}
_NORMALIZATION_CLASS_KINDS = {
    "class",
    "data_all",
    "data_exact",
    "data_has_value",
    "data_max",
    "data_min",
    "data_some",
    "object_all",
    "object_complement",
    "object_exact",
    "object_has_self",
    "object_has_value",
    "object_intersection",
    "object_max",
    "object_min",
    "object_one_of",
    "object_some",
    "object_union",
}
_NORMALIZATION_DATA_KINDS = {
    "data_complement",
    "data_intersection",
    "data_one_of",
    "data_union",
    "datatype",
    "datatype_restriction",
}
_NORMALIZATION_OBJECT_PROPERTY_KINDS = {
    "inverse_object_property",
    "object_property",
}
_NORMALIZATION_INDIVIDUAL_KINDS = {"anonymous_individual", "named_individual"}
_NORMALIZATION_FAMILY_KEYS = {
    "asymmetric_object_properties",
    "complex_object_property_inclusions",
    "concept_inclusions",
    "data_property_inclusions",
    "data_range_inclusions",
    "defined_datatypes",
    "disjoint_data_properties",
    "disjoint_object_properties",
    "facts",
    "has_keys",
    "irreflexive_object_properties",
    "reflexive_object_properties",
    "simple_object_property_inclusions",
}


def _normalization_mapping(value: Any, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise CanonicalizationError(f"{name} must be an object")
    if not all(isinstance(key, str) for key in value):
        raise CanonicalizationError(f"{name} keys must be strings")
    return value


def _normalization_exact_keys(value: Mapping[str, Any], expected: set[str], name: str) -> None:
    if set(value) != expected:
        raise CanonicalizationError(f"{name} keys must be exactly {sorted(expected)}")


def _normalization_string(value: Any, name: str, *, allow_empty: bool = False) -> str:
    if not isinstance(value, str) or (not allow_empty and not value):
        qualifier = "a string" if allow_empty else "a non-empty string"
        raise CanonicalizationError(f"{name} must be {qualifier}")
    return value


def _normalization_iri(value: Any, name: str) -> str:
    iri = _normalization_string(value, name)
    typed_iri(iri)
    return iri


def _normalization_sequence(value: Any, name: str) -> Sequence[Any]:
    if not isinstance(value, Sequence) or isinstance(value, (str, bytes, bytearray)):
        raise CanonicalizationError(f"{name} must be an array")
    return value


def _normalization_set(
    value: Any,
    normalizer: Any,
    name: str,
    *,
    minimum: int = 0,
) -> list[Any]:
    sequence = _normalization_sequence(value, name)
    normalized = [normalizer(item) for item in sequence]
    unique = {canonical_json(item): item for item in normalized}
    if len(unique) < minimum:
        raise CanonicalizationError(f"{name} must contain at least {minimum} distinct values")
    return [unique[key] for key in sorted(unique)]


def _normalization_literal(value: Mapping[str, Any]) -> dict[str, Any]:
    allowed = {
        frozenset(("kind", "lexical", "datatype", "language")),
        frozenset(("kind", "lexical", "datatype", "term_key")),
        frozenset(("kind", "lexical", "language", "term_key")),
    }
    if frozenset(value) not in allowed:
        raise CanonicalizationError("normalization literal has unexpected fields")
    lexical = _normalization_string(value.get("lexical"), "literal.lexical", allow_empty=True)
    language = value.get("language")
    if language is not None and language != "":
        return literal(lexical, language=_normalization_string(language, "literal.language"))
    datatype = value.get("datatype")
    if isinstance(datatype, Mapping):
        datatype_term = normalize_term(datatype)
        if datatype_term.get("kind") != "iri":
            raise CanonicalizationError("literal datatype must be an IRI")
        datatype_iri = str(datatype_term["value"])
    else:
        datatype_iri = _normalization_iri(datatype, "literal.datatype")
    return literal(lexical, datatype=datatype_iri)


def _normalization_node(value: Any) -> dict[str, Any]:
    node = _normalization_mapping(value, "normalization node")
    kind = _normalization_string(node.get("kind"), "normalization node kind")
    if kind in _NORMALIZATION_ENTITY_KINDS:
        if set(node) == {"kind", "iri"}:
            return {"kind": kind, "iri": _normalization_iri(node["iri"], f"{kind}.iri")}
        if set(node) == {"kind", "private"}:
            return {
                "kind": kind,
                "private": _normalization_string(node["private"], f"{kind}.private"),
            }
        raise CanonicalizationError(f"{kind} must contain exactly kind plus iri/private")
    if kind == "anonymous_individual":
        if set(node) == {"kind", "id"}:
            return {
                "kind": kind,
                "id": _normalization_string(node["id"], "anonymous_individual.id"),
            }
        if set(node) == {"kind", "private"}:
            return {
                "kind": kind,
                "private": _normalization_string(node["private"], "anonymous_individual.private"),
            }
        raise CanonicalizationError(
            "anonymous_individual must contain exactly kind plus id/private"
        )
    if kind == "literal":
        return _normalization_literal(node)
    if kind == "inverse_object_property":
        _normalization_exact_keys(node, {"kind", "property"}, kind)
        prop = _normalization_node(node["property"])
        if prop.get("kind") != "object_property":
            raise CanonicalizationError("inverse_object_property must wrap a named property")
        return {"kind": kind, "property": prop}
    if kind in {"object_complement", "data_complement"}:
        _normalization_exact_keys(node, {"kind", "operand"}, kind)
        operand = _normalization_node(node["operand"])
        expected = (
            _NORMALIZATION_CLASS_KINDS if kind == "object_complement" else _NORMALIZATION_DATA_KINDS
        )
        if operand.get("kind") not in expected:
            raise CanonicalizationError(f"invalid operand for {kind}")
        return {"kind": kind, "operand": operand}
    if kind in {"object_intersection", "object_union", "data_intersection", "data_union"}:
        _normalization_exact_keys(node, {"kind", "operands"}, kind)
        expected = (
            _NORMALIZATION_CLASS_KINDS if kind.startswith("object_") else _NORMALIZATION_DATA_KINDS
        )

        def normalize_operand(item: Any) -> dict[str, Any]:
            operand = _normalization_node(item)
            if operand.get("kind") not in expected:
                raise CanonicalizationError(f"invalid operand for {kind}")
            return operand

        return {
            "kind": kind,
            "operands": _normalization_set(
                node["operands"], normalize_operand, f"{kind}.operands", minimum=1
            ),
        }
    if kind == "object_one_of":
        _normalization_exact_keys(node, {"kind", "individuals"}, kind)
        return {
            "kind": kind,
            "individuals": _normalization_set(
                node["individuals"],
                _normalization_individual,
                "object_one_of.individuals",
                minimum=1,
            ),
        }
    if kind == "data_one_of":
        _normalization_exact_keys(node, {"kind", "values"}, kind)
        return {
            "kind": kind,
            "values": _normalization_set(
                node["values"], _normalization_literal_node, "data_one_of.values", minimum=1
            ),
        }
    if kind in {"object_some", "object_all"}:
        _normalization_exact_keys(node, {"kind", "property", "filler"}, kind)
        return {
            "kind": kind,
            "property": _normalization_object_property(node["property"]),
            "filler": _normalization_class_expression(node["filler"]),
        }
    if kind in {"data_some", "data_all"}:
        _normalization_exact_keys(node, {"kind", "property", "filler"}, kind)
        return {
            "kind": kind,
            "property": _normalization_data_property(node["property"]),
            "filler": _normalization_data_range(node["filler"]),
        }
    if kind in {"object_min", "object_max", "object_exact"}:
        _normalization_exact_keys(node, {"kind", "cardinality", "property", "filler"}, kind)
        cardinality = node["cardinality"]
        if isinstance(cardinality, bool) or not isinstance(cardinality, int) or cardinality < 0:
            raise CanonicalizationError(f"{kind}.cardinality must be a nonnegative integer")
        return {
            "kind": kind,
            "cardinality": cardinality,
            "property": _normalization_object_property(node["property"]),
            "filler": _normalization_class_expression(node["filler"]),
        }
    if kind in {"data_min", "data_max", "data_exact"}:
        _normalization_exact_keys(node, {"kind", "cardinality", "property", "filler"}, kind)
        cardinality = node["cardinality"]
        if isinstance(cardinality, bool) or not isinstance(cardinality, int) or cardinality < 0:
            raise CanonicalizationError(f"{kind}.cardinality must be a nonnegative integer")
        return {
            "kind": kind,
            "cardinality": cardinality,
            "property": _normalization_data_property(node["property"]),
            "filler": _normalization_data_range(node["filler"]),
        }
    if kind == "object_has_self":
        _normalization_exact_keys(node, {"kind", "property"}, kind)
        return {"kind": kind, "property": _normalization_object_property(node["property"])}
    if kind == "object_has_value":
        _normalization_exact_keys(node, {"kind", "property", "value"}, kind)
        return {
            "kind": kind,
            "property": _normalization_object_property(node["property"]),
            "value": _normalization_individual(node["value"]),
        }
    if kind == "data_has_value":
        _normalization_exact_keys(node, {"kind", "property", "value"}, kind)
        return {
            "kind": kind,
            "property": _normalization_data_property(node["property"]),
            "value": _normalization_literal_node(node["value"]),
        }
    if kind == "datatype_restriction":
        _normalization_exact_keys(node, {"kind", "datatype", "facets"}, kind)
        return {
            "kind": kind,
            "datatype": _normalization_datatype(node["datatype"]),
            "facets": _normalization_set(
                node["facets"],
                _normalization_facet,
                "datatype_restriction.facets",
                minimum=1,
            ),
        }
    raise CanonicalizationError(f"unknown normalization node kind: {kind!r}")


def _normalization_class_expression(value: Any) -> dict[str, Any]:
    node = _normalization_node(value)
    if node.get("kind") not in _NORMALIZATION_CLASS_KINDS:
        raise CanonicalizationError("expected a class expression")
    return node


def _normalization_data_range(value: Any) -> dict[str, Any]:
    node = _normalization_node(value)
    if node.get("kind") not in _NORMALIZATION_DATA_KINDS:
        raise CanonicalizationError("expected a data range")
    return node


def _normalization_object_property(value: Any) -> dict[str, Any]:
    node = _normalization_node(value)
    if node.get("kind") not in _NORMALIZATION_OBJECT_PROPERTY_KINDS:
        raise CanonicalizationError("expected an object property expression")
    return node


def _normalization_data_property(value: Any) -> dict[str, Any]:
    node = _normalization_node(value)
    if node.get("kind") != "data_property":
        raise CanonicalizationError("expected a data property")
    return node


def _normalization_datatype(value: Any) -> dict[str, Any]:
    node = _normalization_node(value)
    if node.get("kind") != "datatype":
        raise CanonicalizationError("expected a datatype")
    return node


def _normalization_individual(value: Any) -> dict[str, Any]:
    node = _normalization_node(value)
    if node.get("kind") not in _NORMALIZATION_INDIVIDUAL_KINDS:
        raise CanonicalizationError("expected an individual")
    return node


def _normalization_literal_node(value: Any) -> dict[str, Any]:
    node = _normalization_node(value)
    if node.get("kind") != "literal":
        raise CanonicalizationError("expected a literal")
    return node


def _normalization_facet(value: Any) -> dict[str, Any]:
    facet = _normalization_mapping(value, "facet restriction")
    _normalization_exact_keys(facet, {"facet", "value"}, "facet restriction")
    facet_value = facet["facet"]
    if isinstance(facet_value, Mapping):
        facet_term = normalize_term(facet_value)
        if facet_term.get("kind") != "iri":
            raise CanonicalizationError("facet must be an IRI")
    else:
        facet_term = typed_iri(_normalization_iri(facet_value, "facet IRI"))
    return {"facet": facet_term, "value": _normalization_literal_node(facet["value"])}


def _normalization_pair(value: Any, normalizer: Any, name: str) -> list[dict[str, Any]]:
    pair = _normalization_sequence(value, name)
    if len(pair) != 2:
        raise CanonicalizationError(f"{name} must contain exactly two values")
    return [normalizer(pair[0]), normalizer(pair[1])]


def _normalization_fact(value: Any) -> dict[str, Any]:
    fact = _normalization_mapping(value, "normalization fact")
    kind = _normalization_string(fact.get("kind"), "normalization fact kind")
    if kind == "class_assertion":
        _normalization_exact_keys(fact, {"kind", "class_expression", "individual"}, kind)
        return {
            "kind": kind,
            "class_expression": _normalization_class_expression(fact["class_expression"]),
            "individual": _normalization_individual(fact["individual"]),
        }
    if kind in {"object_property_assertion", "negative_object_property_assertion"}:
        _normalization_exact_keys(fact, {"kind", "property", "subject", "object"}, kind)
        return {
            "kind": kind,
            "property": _normalization_object_property(fact["property"]),
            "subject": _normalization_individual(fact["subject"]),
            "object": _normalization_individual(fact["object"]),
        }
    if kind in {"data_property_assertion", "negative_data_property_assertion"}:
        _normalization_exact_keys(fact, {"kind", "property", "subject", "value"}, kind)
        return {
            "kind": kind,
            "property": _normalization_data_property(fact["property"]),
            "subject": _normalization_individual(fact["subject"]),
            "value": _normalization_literal_node(fact["value"]),
        }
    if kind in {"same_individual", "different_individuals"}:
        _normalization_exact_keys(fact, {"kind", "individuals"}, kind)
        return {
            "kind": kind,
            "individuals": _normalization_set(
                fact["individuals"],
                _normalization_individual,
                f"{kind}.individuals",
                minimum=2,
            ),
        }
    raise CanonicalizationError(f"unknown normalization fact kind: {kind!r}")


def _normalization_key(value: Any) -> dict[str, Any]:
    key = _normalization_mapping(value, "has-key record")
    _normalization_exact_keys(
        key, {"class_expression", "object_properties", "data_properties"}, "has-key record"
    )
    return {
        "class_expression": _normalization_class_expression(key["class_expression"]),
        "object_properties": _normalization_set(
            key["object_properties"], _normalization_object_property, "key.object_properties"
        ),
        "data_properties": _normalization_set(
            key["data_properties"], _normalization_data_property, "key.data_properties"
        ),
    }


def _normalize_structural_normalization(value: Any) -> dict[str, Any]:
    root = _normalization_mapping(value, "normalization value")
    _normalization_exact_keys(root, {"kind", "families"}, "normalization value")
    if root["kind"] not in {"raw_structural_normalization", "structural_normalization"}:
        raise CanonicalizationError("normalization kind is not structural normalization")
    families = _normalization_mapping(root["families"], "normalization families")
    _normalization_exact_keys(families, _NORMALIZATION_FAMILY_KEYS, "normalization families")

    concept_inclusions = _normalization_set(
        families["concept_inclusions"],
        partial(
            _normalization_set,
            normalizer=_normalization_class_expression,
            name="concept inclusion",
            minimum=1,
        ),
        "concept inclusions",
    )
    data_range_inclusions = _normalization_set(
        families["data_range_inclusions"],
        partial(
            _normalization_set,
            normalizer=_normalization_data_range,
            name="data range inclusion",
            minimum=1,
        ),
        "data range inclusions",
    )

    def complex_inclusion(item: Any) -> dict[str, Any]:
        inclusion = _normalization_mapping(item, "complex object property inclusion")
        _normalization_exact_keys(
            inclusion, {"chain", "super_property"}, "complex object property inclusion"
        )
        chain = _normalization_sequence(inclusion["chain"], "complex property chain")
        if not chain:
            raise CanonicalizationError("complex property chain cannot be empty")
        return {
            "chain": [_normalization_object_property(prop) for prop in chain],
            "super_property": _normalization_object_property(inclusion["super_property"]),
        }

    normalized_families: dict[str, Any] = {
        "concept_inclusions": concept_inclusions,
        "data_range_inclusions": data_range_inclusions,
        "simple_object_property_inclusions": _normalization_set(
            families["simple_object_property_inclusions"],
            partial(
                _normalization_pair,
                normalizer=_normalization_object_property,
                name="simple object property inclusion",
            ),
            "simple object property inclusions",
        ),
        "complex_object_property_inclusions": _normalization_set(
            families["complex_object_property_inclusions"],
            complex_inclusion,
            "complex object property inclusions",
        ),
        "disjoint_object_properties": _normalization_set(
            families["disjoint_object_properties"],
            partial(
                _normalization_set,
                normalizer=_normalization_object_property,
                name="disjoint object properties",
                minimum=2,
            ),
            "disjoint object property groups",
        ),
        "reflexive_object_properties": _normalization_set(
            families["reflexive_object_properties"],
            _normalization_object_property,
            "reflexive object properties",
        ),
        "irreflexive_object_properties": _normalization_set(
            families["irreflexive_object_properties"],
            _normalization_object_property,
            "irreflexive object properties",
        ),
        "asymmetric_object_properties": _normalization_set(
            families["asymmetric_object_properties"],
            _normalization_object_property,
            "asymmetric object properties",
        ),
        "data_property_inclusions": _normalization_set(
            families["data_property_inclusions"],
            partial(
                _normalization_pair,
                normalizer=_normalization_data_property,
                name="data property inclusion",
            ),
            "data property inclusions",
        ),
        "disjoint_data_properties": _normalization_set(
            families["disjoint_data_properties"],
            partial(
                _normalization_set,
                normalizer=_normalization_data_property,
                name="disjoint data properties",
                minimum=2,
            ),
            "disjoint data property groups",
        ),
        "facts": _normalization_set(families["facts"], _normalization_fact, "facts"),
        "has_keys": _normalization_set(families["has_keys"], _normalization_key, "has keys"),
        "defined_datatypes": _normalization_set(
            families["defined_datatypes"], _normalization_datatype, "defined datatypes"
        ),
    }
    return {"kind": "structural_normalization", "families": normalized_families}


def _normalization_private_token(value: Mapping[str, Any]) -> tuple[str, str] | None:
    kind = value.get("kind")
    iri = value.get("iri")
    if kind in _NORMALIZATION_ENTITY_KINDS and isinstance(iri, str) and iri.startswith("internal:"):
        return str(kind), iri
    identifier = value.get("id")
    if kind == "anonymous_individual" and isinstance(identifier, str):
        return str(kind), identifier
    return None


def _normalization_private_tokens(value: Any) -> set[tuple[str, str]]:
    tokens: set[tuple[str, str]] = set()
    if isinstance(value, Mapping):
        token = _normalization_private_token(value)
        if token is not None:
            tokens.add(token)
        for item in value.values():
            tokens.update(_normalization_private_tokens(item))
    elif isinstance(value, Sequence) and not isinstance(value, (str, bytes, bytearray)):
        for item in value:
            tokens.update(_normalization_private_tokens(item))
    return tokens


def _rewrite_normalization_private(value: Any, replacements: Mapping[tuple[str, str], str]) -> Any:
    if isinstance(value, Mapping):
        token = _normalization_private_token(value)
        if token is not None and token in replacements:
            return {"kind": token[0], "private": replacements[token]}
        return {
            str(key): _rewrite_normalization_private(item, replacements)
            for key, item in value.items()
        }
    if isinstance(value, Sequence) and not isinstance(value, (str, bytes, bytearray)):
        return [_rewrite_normalization_private(item, replacements) for item in value]
    return value


def _alpha_normalize_structural_normalization(
    value: dict[str, Any], *, permutation_limit: int
) -> dict[str, Any]:
    tokens = _normalization_private_tokens(value)
    if not tokens:
        return value
    colors = {token: f"{token[0]}:0" for token in tokens}
    for _ in range(len(tokens) + 1):
        signatures: dict[tuple[str, str], str] = {}
        for target in tokens:
            replacements = {
                token: (
                    f"{token[0]}:@self" if token == target else f"{token[0]}:@color:{colors[token]}"
                )
                for token in tokens
            }
            rooted = _normalize_structural_normalization(
                _rewrite_normalization_private(value, replacements)
            )
            signatures[target] = hashlib.sha256(canonical_json(rooted).encode("utf-8")).hexdigest()
        palette = {
            signature: str(index)
            for index, signature in enumerate(sorted(set(signatures.values())))
        }
        updated = {token: f"{token[0]}:{palette[signatures[token]]}" for token in tokens}
        if updated == colors:
            break
        colors = updated

    partitions: dict[tuple[str, str], list[tuple[str, str]]] = defaultdict(list)
    for token, color in colors.items():
        partitions[(token[0], color)].append(token)
    groups = [sorted(partitions[key]) for key in sorted(partitions)]
    combinations = math.prod(math.factorial(len(group)) for group in groups)
    if combinations > permutation_limit:
        raise CanonicalizationError(
            f"ambiguous normalization graph needs {combinations} permutations; "
            f"limit is {permutation_limit}"
        )

    permutations = [list(itertools.permutations(group)) for group in groups]
    best: tuple[str, dict[str, Any]] | None = None
    for ordered_groups in itertools.product(*permutations):
        counters: dict[str, int] = defaultdict(int)
        canonical_replacements: dict[tuple[str, str], str] = {}
        for group in ordered_groups:
            for token in group:
                index = counters[token[0]]
                counters[token[0]] += 1
                canonical_replacements[token] = f"{token[0]}:{index}"
        candidate = _normalize_structural_normalization(
            _rewrite_normalization_private(value, canonical_replacements)
        )
        encoded = canonical_json(candidate)
        if best is None or encoded < best[0]:
            best = encoded, candidate
    assert best is not None
    return best[1]


def canonical_normalization(
    value: Mapping[str, Any], *, permutation_limit: int = 100_000
) -> dict[str, Any]:
    """Validate and alpha-canonicalize a raw HermiT ``OWLAxioms`` snapshot.

    Collection order and duplicates have no comparison meaning. HermiT-reserved
    ``internal:`` entity IRIs and anonymous-individual IDs are treated as graph-local
    private symbols, refined structurally, and renamed by a bounded canonical search.
    """

    if (
        isinstance(permutation_limit, bool)
        or not isinstance(permutation_limit, int)
        or permutation_limit < 1
    ):
        raise CanonicalizationError("permutation_limit must be a positive integer")
    normalized = _normalize_structural_normalization(value)
    return _alpha_normalize_structural_normalization(
        normalized, permutation_limit=permutation_limit
    )


def semantic_projection(record: Mapping[str, Any]) -> dict[str, Any]:
    """Return the deterministic portion used by committed golden comparisons."""

    keys = ("schema_version", "request_id", "status", "outcome", "value")
    result = {key: record[key] for key in keys if key in record}
    error = record.get("error")
    if isinstance(error, Mapping):
        # Exception text and stack traces are diagnostics.  Stable public category/type is the
        # comparison identity.
        result["error"] = {key: error[key] for key in ("category", "type") if key in error}
    return result
