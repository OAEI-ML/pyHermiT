"""Complete-closure OWL 2 DL global-restriction validation.

SPDX-License-Identifier: LGPL-3.0-or-later
"""

from __future__ import annotations

import hashlib
from collections.abc import Callable, Iterable, Iterator
from typing import cast

import pyowl_core.model as owl
from pyowl_core import OntologyView
from pyowl_core.index import OntologyIdentityIndex

from pyhermit.config import UnsupportedDatatypePolicy
from pyhermit.datatypes import (
    SUPPORTED_DATATYPES,
    compile_datatype_semantic_model,
    compile_literal_semantic_payload,
)
from pyhermit.exceptions import (
    IncompleteImportClosureError,
    InvalidLiteralError,
    OntologyProfileError,
    ReasonerInterruptedError,
    UnsupportedDatatypeError,
)
from pyhermit.roles import build_role_axiom_graph

from .model import OWL2DLReport, ProfileIssue, ProfileSeverity

_RDF = "http://www.w3.org/1999/02/22-rdf-syntax-ns#"
_RDFS = "http://www.w3.org/2000/01/rdf-schema#"
_XSD = "http://www.w3.org/2001/XMLSchema#"
_OWL = "http://www.w3.org/2002/07/owl#"
_RESERVED_PREFIXES = (_RDF, _RDFS, _XSD, _OWL)

_BUILTIN_KINDS: dict[str, frozenset[owl.EntityKind]] = {
    owl.OWL_THING.iri.value: frozenset((owl.EntityKind.CLASS,)),
    owl.OWL_NOTHING.iri.value: frozenset((owl.EntityKind.CLASS,)),
    owl.OWL_TOP_OBJECT_PROPERTY.iri.value: frozenset((owl.EntityKind.OBJECT_PROPERTY,)),
    owl.OWL_BOTTOM_OBJECT_PROPERTY.iri.value: frozenset((owl.EntityKind.OBJECT_PROPERTY,)),
    owl.OWL_TOP_DATA_PROPERTY.iri.value: frozenset((owl.EntityKind.DATA_PROPERTY,)),
    owl.OWL_BOTTOM_DATA_PROPERTY.iri.value: frozenset((owl.EntityKind.DATA_PROPERTY,)),
    **{iri: frozenset((owl.EntityKind.DATATYPE,)) for iri in SUPPORTED_DATATYPES},
    **{
        iri: frozenset((owl.EntityKind.ANNOTATION_PROPERTY,))
        for iri in (
            _RDFS + "label",
            _RDFS + "comment",
            _RDFS + "seeAlso",
            _RDFS + "isDefinedBy",
            _OWL + "deprecated",
            _OWL + "versionInfo",
            _OWL + "priorVersion",
            _OWL + "backwardCompatibleWith",
            _OWL + "incompatibleWith",
        )
    },
}

_SIMPLE_CHARACTERISTICS = (
    owl.FunctionalObjectProperty,
    owl.InverseFunctionalObjectProperty,
    owl.IrreflexiveObjectProperty,
    owl.AsymmetricObjectProperty,
)
_SIMPLE_EXPRESSIONS = (
    owl.ObjectHasSelf,
    owl.ObjectMinCardinality,
    owl.ObjectMaxCardinality,
    owl.ObjectExactCardinality,
)
_ANONYMOUS_FORBIDDEN_AXIOMS = (
    owl.SameIndividual,
    owl.DifferentIndividuals,
    owl.NegativeObjectPropertyAssertion,
    owl.NegativeDataPropertyAssertion,
)
_ANONYMOUS_FORBIDDEN_EXPRESSIONS = (owl.ObjectOneOf, owl.ObjectHasValue)
_DATATYPE_ERRORS = (InvalidLiteralError, OntologyProfileError, UnsupportedDatatypeError)


def validate_owl2_dl_view(
    view: OntologyView,
    *,
    unsupported_datatypes: UnsupportedDatatypePolicy = UnsupportedDatatypePolicy.ERROR,
    cancelled: Callable[[], bool] | None = None,
) -> OWL2DLReport:
    """Validate one already-captured, proven-complete ontology view."""

    if not isinstance(view, OntologyView):
        raise TypeError("view must satisfy pyowl_core.OntologyView")
    if not isinstance(unsupported_datatypes, UnsupportedDatatypePolicy):
        raise TypeError("unsupported_datatypes must be UnsupportedDatatypePolicy")
    if cancelled is not None and not callable(cancelled):
        raise TypeError("cancelled must be callable or None")
    identity = view.view(OntologyIdentityIndex)
    if not view.is_complete or not identity.is_complete:
        raise IncompleteImportClosureError(
            "OWL 2 DL reasoning requires a complete resolved import closure",
            context={
                "core_backend": view.report.backend,
                "import_manifest_sha256": identity.import_manifest_digest.hex(),
                "loader_diagnostics_sha256": identity.loader_diagnostics_digest.hex(),
            },
        )

    def checkpoint() -> None:
        if cancelled is not None and cancelled():
            raise ReasonerInterruptedError("OWL 2 DL profile validation was interrupted")

    checkpoint()
    role_graph = build_role_axiom_graph(
        view.iter_axioms(),
        require_regular=False,
        cancelled=cancelled,
    )
    issues: list[ProfileIssue] = _ontology_identifier_issues(identity)
    issues.extend(
        ProfileIssue(
            violation.code,
            ProfileSeverity.ERROR,
            violation.message,
            "SubObjectPropertyOf",
            provenance_sha256=violation.provenance_sha256,
        )
        for violation in role_graph.regularity_violations
    )
    declarations: dict[str, set[owl.EntityKind]] = {}
    uses: dict[str, set[owl.EntityKind]] = {}
    datatype_definitions: list[owl.DatatypeDefinition] = []
    data_ranges: dict[bytes, owl.DataRange] = {}
    literals: dict[bytes, owl.Literal] = {}
    anonymous: set[owl.AnonymousIndividual] = set()
    anonymous_edges: list[
        tuple[owl.AnonymousIndividual, owl.AnonymousIndividual, owl.AxiomNode]
    ] = []
    named_links: dict[owl.AnonymousIndividual, tuple[int, owl.AxiomNode]] = {}
    axiom_count = 0

    for axiom_count, axiom in enumerate(view.iter_axioms(), 1):
        if axiom_count & 0x3F == 0:
            checkpoint()
        if isinstance(axiom, owl.Declaration):
            declarations.setdefault(axiom.entity.iri.value, set()).add(axiom.entity.kind)
        if isinstance(axiom, owl.DatatypeDefinition):
            datatype_definitions.append(axiom)
        _validate_top_data_property(view, axiom, issues)
        _collect_anonymous_constraints(
            view,
            axiom,
            issues,
            anonymous,
            anonymous_edges,
            named_links,
        )
        for node in owl.walk(axiom):
            if isinstance(node, owl.Entity):
                uses.setdefault(node.iri.value, set()).add(node.kind)
            if isinstance(node, owl.DATA_RANGE_TYPES):
                data_ranges[node.canonical_bytes()] = cast(owl.DataRange, node)
            if isinstance(node, owl.Literal):
                literals[node.canonical_bytes()] = node
            if (
                isinstance(node, (owl.DataSomeValuesFrom, owl.DataAllValuesFrom))
                and len(node.properties) != 1
            ):
                issues.append(
                    _issue_for_axiom(
                        view,
                        axiom,
                        "OWL2_DATA_RANGE_ARITY",
                        "OWL 2 defines only unary data ranges, so the restriction must use "
                        "exactly one data property",
                        constructor=type(node).__name__,
                    )
                )
        for property_ in _simple_required_properties(axiom):
            if not role_graph.is_simple(property_):
                issues.append(
                    _issue_for_axiom(
                        view,
                        axiom,
                        "OWL2DL_NON_SIMPLE_PROPERTY",
                        "axiom position requires a simple object property expression",
                    )
                )

    for annotation in view.ontology_annotations():
        checkpoint()
        for node in owl.walk(annotation):
            if isinstance(node, owl.Entity):
                uses.setdefault(node.iri.value, set()).add(node.kind)
            if isinstance(node, owl.DATA_RANGE_TYPES):
                data_ranges[node.canonical_bytes()] = cast(owl.DataRange, node)
            if isinstance(node, owl.Literal):
                literals[node.canonical_bytes()] = node

    _validate_entity_kinds(declarations, uses, issues)
    _validate_reserved_vocabulary(uses, issues)
    _validate_declarations(declarations, uses, issues)
    _validate_anonymous_graph(view, anonymous, anonymous_edges, named_links, issues)
    unknown = _unknown_datatypes(data_ranges.values(), datatype_definitions)
    opaque: Iterable[str] = ()
    if unknown and unsupported_datatypes is UnsupportedDatatypePolicy.IGNORE_WITH_WARNING:
        opaque = unknown
        issues.extend(
            ProfileIssue(
                "UNSUPPORTED_DATATYPE_OPAQUE",
                ProfileSeverity.WARNING,
                f"unsupported datatype is treated as opaque: {iri}",
                "Datatype",
            )
            for iri in sorted(unknown)
        )
    try:
        compile_datatype_semantic_model(
            tuple(data_ranges[key] for key in sorted(data_ranges)),
            definitions=tuple(datatype_definitions),
            opaque_datatype_iris=opaque,
        )
    except _DATATYPE_ERRORS as error:
        issues.append(_datatype_issue(error))
    defined_datatypes = frozenset(item.datatype.iri.value for item in datatype_definitions)
    for key in sorted(literals):
        checkpoint()
        literal = literals[key]
        datatype_iri = literal.datatype.iri.value
        if datatype_iri in defined_datatypes:
            issues.append(
                ProfileIssue(
                    "CUSTOM_DATATYPE_LITERAL",
                    ProfileSeverity.ERROR,
                    "a datatype defined in the ontology has no lexical space and cannot be "
                    f"used on a literal: {datatype_iri}",
                    "Literal",
                )
            )
            continue
        try:
            compile_literal_semantic_payload(
                literal,
                allow_opaque=(
                    unsupported_datatypes is UnsupportedDatatypePolicy.IGNORE_WITH_WARNING
                ),
            )
        except _DATATYPE_ERRORS as error:
            issues.append(_datatype_issue(error, constructor="Literal"))

    extension_count = 0
    for extension in view.iter_extensions():
        extension_count += 1
        checkpoint()
        issues.append(
            ProfileIssue(
                "OWL2DL_EXTENSION_COMPONENT",
                ProfileSeverity.ERROR,
                "extension components such as SWRL are outside the OWL 2 DL reasoner scope",
                type(extension).__name__,
                tuple(
                    sorted(
                        {origin.document_key for origin in view.origin_index.origins_for(extension)}
                    )
                ),
                hashlib.sha256(extension.canonical_bytes()).hexdigest(),
            )
        )
    checkpoint()
    return OWL2DLReport(
        tuple(issues),
        role_graph,
        axiom_count,
        extension_count,
        complete=True,
    )


def _ontology_identifier_issues(
    identity: OntologyIdentityIndex,
) -> list[ProfileIssue]:
    issues: list[ProfileIssue] = []
    for document in identity.documents:
        ontology_id = document.ontology_id
        for field, iri in (
            ("ONTOLOGY", ontology_id.ontology_iri),
            ("VERSION", ontology_id.version_iri),
        ):
            if iri is None or not iri.value.startswith(_RESERVED_PREFIXES):
                continue
            issues.append(
                ProfileIssue(
                    f"OWL2DL_RESERVED_{field}_IRI",
                    ProfileSeverity.ERROR,
                    f"{field.lower()} IRI must not use reserved OWL/RDF vocabulary: {iri.value}",
                    "OntologyID",
                    (document.document_key,),
                )
            )
    return issues


def _simple_required_properties(
    axiom: owl.AxiomNode,
) -> Iterator[owl.ObjectPropertyExpression]:
    if isinstance(axiom, _SIMPLE_CHARACTERISTICS):
        yield axiom.property
    if isinstance(axiom, owl.DisjointObjectProperties):
        yield from axiom.properties
    for node in owl.walk(axiom):
        if isinstance(node, _SIMPLE_EXPRESSIONS):
            yield node.property


def _issue_for_axiom(
    view: OntologyView,
    axiom: owl.AxiomNode,
    rule_id: str,
    message: str,
    *,
    constructor: str | None = None,
) -> ProfileIssue:
    return ProfileIssue(
        rule_id,
        ProfileSeverity.ERROR,
        message,
        type(axiom).__name__ if constructor is None else constructor,
        tuple(sorted({origin.document_key for origin in view.origin_index.origins_for(axiom)})),
        hashlib.sha256(axiom.canonical_bytes()).hexdigest(),
    )


def _datatype_issue(
    error: InvalidLiteralError | OntologyProfileError | UnsupportedDatatypeError,
    *,
    constructor: str = "DataRange",
) -> ProfileIssue:
    return ProfileIssue(
        error.code,
        ProfileSeverity.ERROR,
        str(error),
        constructor,
    )


def _validate_top_data_property(
    view: OntologyView,
    axiom: owl.AxiomNode,
    issues: list[ProfileIssue],
) -> None:
    top_iri = owl.OWL_TOP_DATA_PROPERTY.iri.value
    occurs = any(
        isinstance(node, owl.DataProperty) and node.iri.value == top_iri for node in owl.walk(axiom)
    )
    if not occurs:
        return
    allowed = (
        isinstance(axiom, owl.SubDataPropertyOf)
        and axiom.super_property.iri.value == top_iri
        and axiom.sub_property.iri.value != top_iri
    )
    if not allowed:
        issues.append(
            _issue_for_axiom(
                view,
                axiom,
                "OWL2DL_TOP_DATA_PROPERTY_POSITION",
                "owl:topDataProperty may occur only as the super-property of a data "
                "subproperty axiom",
            )
        )


def _collect_anonymous_constraints(
    view: OntologyView,
    axiom: owl.AxiomNode,
    issues: list[ProfileIssue],
    anonymous: set[owl.AnonymousIndividual],
    edges: list[tuple[owl.AnonymousIndividual, owl.AnonymousIndividual, owl.AxiomNode]],
    named_links: dict[owl.AnonymousIndividual, tuple[int, owl.AxiomNode]],
) -> None:
    nodes = tuple(owl.walk(axiom))
    values = tuple(node for node in nodes if isinstance(node, owl.AnonymousIndividual))
    anonymous.update(values)
    if values and isinstance(axiom, _ANONYMOUS_FORBIDDEN_AXIOMS):
        issues.append(
            _issue_for_axiom(
                view,
                axiom,
                "OWL2DL_ANONYMOUS_AXIOM_POSITION",
                "anonymous individuals are forbidden in this axiom type",
            )
        )
    for node in nodes:
        if isinstance(node, _ANONYMOUS_FORBIDDEN_EXPRESSIONS) and any(
            isinstance(value, owl.AnonymousIndividual) for value in owl.walk(node)
        ):
            issues.append(
                _issue_for_axiom(
                    view,
                    axiom,
                    "OWL2DL_ANONYMOUS_CLASS_EXPRESSION",
                    "anonymous individuals are forbidden in ObjectOneOf and "
                    "ObjectHasValue expressions",
                    constructor=type(node).__name__,
                )
            )
    if not isinstance(axiom, owl.ObjectPropertyAssertion):
        return
    source = axiom.source
    target = axiom.target
    if isinstance(source, owl.AnonymousIndividual) and isinstance(target, owl.AnonymousIndividual):
        edges.append((source, target, axiom))
    elif isinstance(source, owl.AnonymousIndividual) and isinstance(target, owl.NamedIndividual):
        count, retained = named_links.get(source, (0, axiom))
        named_links[source] = (count + 1, retained)
    elif isinstance(source, owl.NamedIndividual) and isinstance(target, owl.AnonymousIndividual):
        count, retained = named_links.get(target, (0, axiom))
        named_links[target] = (count + 1, retained)


def _validate_anonymous_graph(
    view: OntologyView,
    anonymous: set[owl.AnonymousIndividual],
    edges: list[tuple[owl.AnonymousIndividual, owl.AnonymousIndividual, owl.AxiomNode]],
    named_links: dict[owl.AnonymousIndividual, tuple[int, owl.AxiomNode]],
    issues: list[ProfileIssue],
) -> None:
    parent = {value: value for value in anonymous}

    def root(value: owl.AnonymousIndividual) -> owl.AnonymousIndividual:
        trail: list[owl.AnonymousIndividual] = []
        while parent[value] != value:
            trail.append(value)
            value = parent[value]
        for item in trail:
            parent[item] = value
        return value

    edge_counts: dict[frozenset[owl.AnonymousIndividual], int] = {}
    for source, target, axiom in edges:
        pair = frozenset((source, target))
        edge_counts[pair] = edge_counts.get(pair, 0) + 1
        source_root = root(source)
        target_root = root(target)
        if source == target or source_root == target_root:
            issues.append(
                _issue_for_axiom(
                    view,
                    axiom,
                    "OWL2DL_ANONYMOUS_GRAPH_CYCLE",
                    "the anonymous-individual object-assertion graph must be a forest",
                )
            )
        else:
            parent[target_root] = source_root
    for pair, count in edge_counts.items():
        if count <= 1:
            continue
        representative = next(
            axiom for source, target, axiom in edges if frozenset((source, target)) == pair
        )
        issues.append(
            _issue_for_axiom(
                view,
                representative,
                "OWL2DL_ANONYMOUS_PARALLEL_EDGE",
                "at most one object-property assertion may connect an anonymous pair",
            )
        )
    components: dict[owl.AnonymousIndividual, list[owl.AnonymousIndividual]] = {}
    for value in anonymous:
        components.setdefault(root(value), []).append(value)
    for values in components.values():
        if all(value in named_links and named_links[value][0] > 1 for value in values):
            representative = min(
                (named_links[value][1] for value in values),
                key=lambda axiom: axiom.canonical_bytes(),
            )
            issues.append(
                _issue_for_axiom(
                    view,
                    representative,
                    "OWL2DL_ANONYMOUS_TREE_ROOT",
                    "each anonymous-individual tree must contain a vertex connected by at "
                    "most one assertion to named individuals",
                )
            )


def _validate_entity_kinds(
    declarations: dict[str, set[owl.EntityKind]],
    uses: dict[str, set[owl.EntityKind]],
    issues: list[ProfileIssue],
) -> None:
    property_kinds = {
        owl.EntityKind.OBJECT_PROPERTY,
        owl.EntityKind.DATA_PROPERTY,
        owl.EntityKind.ANNOTATION_PROPERTY,
    }
    for iri in sorted(set(declarations) | set(uses)):
        kinds = declarations.get(iri, set()) | uses.get(iri, set())
        if len(kinds & property_kinds) > 1:
            issues.append(
                ProfileIssue(
                    "OWL2DL_PROPERTY_PUNNING",
                    ProfileSeverity.ERROR,
                    f"IRI is used for more than one property kind: {iri}",
                )
            )
        if owl.EntityKind.CLASS in kinds and owl.EntityKind.DATATYPE in kinds:
            issues.append(
                ProfileIssue(
                    "OWL2DL_CLASS_DATATYPE_PUNNING",
                    ProfileSeverity.ERROR,
                    f"IRI is used as both class and datatype: {iri}",
                )
            )


def _validate_reserved_vocabulary(
    uses: dict[str, set[owl.EntityKind]],
    issues: list[ProfileIssue],
) -> None:
    for iri, kinds in sorted(uses.items()):
        if not iri.startswith(_RESERVED_PREFIXES):
            continue
        allowed = _BUILTIN_KINDS.get(iri)
        if allowed is None:
            issues.append(
                ProfileIssue(
                    "OWL2DL_RESERVED_VOCABULARY",
                    ProfileSeverity.ERROR,
                    f"reserved vocabulary IRI is not an OWL 2 built-in entity: {iri}",
                )
            )
        elif not kinds.issubset(allowed):
            issues.append(
                ProfileIssue(
                    "OWL2DL_BUILTIN_ENTITY_KIND",
                    ProfileSeverity.ERROR,
                    f"built-in IRI is used with an illegal entity kind: {iri}",
                )
            )


def _validate_declarations(
    declarations: dict[str, set[owl.EntityKind]],
    uses: dict[str, set[owl.EntityKind]],
    issues: list[ProfileIssue],
) -> None:
    for iri, kinds in sorted(uses.items()):
        if iri in _BUILTIN_KINDS:
            continue
        declared = declarations.get(iri, set())
        for kind in sorted(kinds, key=lambda value: value.value):
            if kind is owl.EntityKind.NAMED_INDIVIDUAL or kind in declared:
                continue
            issues.append(
                ProfileIssue(
                    "OWL2DL_MISSING_DECLARATION",
                    ProfileSeverity.ERROR,
                    f"used {kind.value} is not declared: {iri}",
                )
            )


def _unknown_datatypes(
    data_ranges: Iterable[owl.DataRange],
    definitions: Iterable[owl.DatatypeDefinition],
) -> frozenset[str]:
    defined = frozenset(value.datatype.iri.value for value in definitions)
    return frozenset(
        node.iri.value
        for data_range in data_ranges
        for node in owl.walk(data_range)
        if isinstance(node, owl.Datatype)
        and node.iri.value not in SUPPORTED_DATATYPES
        and node.iri.value not in defined
    )


__all__ = ["validate_owl2_dl_view"]
