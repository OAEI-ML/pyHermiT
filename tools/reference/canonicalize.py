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
