"""Re-export-only shared input surface; pyHermiT defines no parser."""

from __future__ import annotations

from pyowl_core import coerce_snapshot, load_snapshot, parse_document

from pyhermit.inputs import ValidatedOntology, capture_ontology

__all__ = [
    "ValidatedOntology",
    "capture_ontology",
    "coerce_snapshot",
    "load_snapshot",
    "parse_document",
]
