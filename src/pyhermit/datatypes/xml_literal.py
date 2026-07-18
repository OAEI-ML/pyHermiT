# Copyright 2008, 2009, 2010 by the Oxford University Computing Laboratory
# Modifications Copyright 2026 pyHermiT contributors
# SPDX-License-Identifier: LGPL-3.0-or-later
# Adapted from HermiT commit 37ec30aced32ac81ebecc5e33fad255ddefcb4c3;
# see reports/licensing/adapted-files.toml.

"""Entity-safe deterministic canonicalization for rdf:XMLLiteral fragments."""

from __future__ import annotations

import re
import xml.etree.ElementTree as ET
from collections.abc import Iterable
from typing import Final, NoReturn, cast

from pyhermit.events import CancellationToken
from pyhermit.exceptions import InvalidLiteralError, ResourceLimitError

from .model import DatatypeLimits, XMLComparison, XMLIdentity

RDF_NAMESPACE: Final = "http://www.w3.org/1999/02/22-rdf-syntax-ns#"
RDF_XML_LITERAL: Final = RDF_NAMESPACE + "XMLLiteral"

_FORBIDDEN_DECLARATION = re.compile(r"<!\s*(?:DOCTYPE|ENTITY)\b", re.IGNORECASE)
_WRAPPER: Final = "pyhermit-xml-literal-wrapper"


def compile_xml_literal(
    lexical: str,
    *,
    limits: DatatypeLimits,
    cancellation: CancellationToken | None,
) -> tuple[XMLIdentity, XMLComparison]:
    """Validate and canonicalize a fragment without DTD/entity/network access."""

    if not isinstance(lexical, str):
        raise TypeError("lexical must be str")
    if not isinstance(limits, DatatypeLimits):
        raise TypeError("limits must be DatatypeLimits")
    if _FORBIDDEN_DECLARATION.search(lexical) is not None:
        _invalid()
    enclosed = f"<{_WRAPPER}>{lexical}</{_WRAPPER}>"
    _bounded_parse(enclosed, limits=limits, cancellation=cancellation)
    _poll(cancellation)
    try:
        canonical = ET.canonicalize(
            xml_data=enclosed,
            with_comments=True,
            strip_text=False,
            rewrite_prefixes=False,
        )
    except (ET.ParseError, ValueError) as error:
        raise InvalidLiteralError(
            "rdf:XMLLiteral is not a well-formed XML fragment",
            context={"datatype_iri": RDF_XML_LITERAL},
        ) from error
    prefix = f"<{_WRAPPER}>"
    suffix = f"</{_WRAPPER}>"
    if not canonical.startswith(prefix) or not canonical.endswith(suffix):
        raise AssertionError("XML canonicalizer changed the private wrapper")
    fragment = canonical[len(prefix) : -len(suffix)]
    _poll(cancellation)
    identity = XMLIdentity(fragment)
    return identity, XMLComparison(fragment)


def _bounded_parse(
    enclosed: str,
    *,
    limits: DatatypeLimits,
    cancellation: CancellationToken | None,
) -> None:
    parser: ET.XMLPullParser[ET.Element[str]] = ET.XMLPullParser(
        events=("start", "end", "comment", "pi")
    )
    depth = 0
    nodes = 0
    chunk_size = max(256, limits.cancellation_poll_stride * 16)
    try:
        for start in range(0, len(enclosed), chunk_size):
            chunk = enclosed[start : start + chunk_size]
            parser.feed(chunk)
            events = cast(
                "Iterable[tuple[str, ET.Element[str]]]",
                parser.read_events(),
            )
            for event, _element in events:
                if event == "start":
                    depth += 1
                    nodes += 1
                    if depth - 1 > limits.max_xml_depth:
                        raise ResourceLimitError(
                            "XML literal exceeds the configured nesting-depth limit",
                            limit="max_xml_depth",
                            observed=depth - 1,
                            allowed=limits.max_xml_depth,
                        )
                    if nodes - 1 > limits.max_xml_nodes:
                        raise ResourceLimitError(
                            "XML literal exceeds the configured node limit",
                            limit="max_xml_nodes",
                            observed=nodes - 1,
                            allowed=limits.max_xml_nodes,
                        )
                elif event == "end":
                    depth -= 1
                else:
                    nodes += 1
                    if nodes - 1 > limits.max_xml_nodes:
                        raise ResourceLimitError(
                            "XML literal exceeds the configured node limit",
                            limit="max_xml_nodes",
                            observed=nodes - 1,
                            allowed=limits.max_xml_nodes,
                        )
            _poll(cancellation, len(chunk))
        parser.close()
    except ET.ParseError as error:
        raise InvalidLiteralError(
            "rdf:XMLLiteral is not a well-formed XML fragment",
            context={"datatype_iri": RDF_XML_LITERAL},
        ) from error


def _poll(cancellation: CancellationToken | None, work: int = 0) -> None:
    if cancellation is None:
        return
    if work:
        cancellation.add_work(work)
    cancellation.check()


def _invalid() -> NoReturn:
    raise InvalidLiteralError(
        "rdf:XMLLiteral forbids DTD and entity declarations",
        context={"datatype_iri": RDF_XML_LITERAL},
    )


__all__ = ["RDF_XML_LITERAL", "compile_xml_literal"]
