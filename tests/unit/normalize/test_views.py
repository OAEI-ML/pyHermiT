from __future__ import annotations

from pyowl_core import (
    BackendPreference,
    ImportPolicy,
    LoadOptions,
    OntologyDelta,
    apply_delta,
    compose_views,
    load_snapshot,
)
from pyowl_core.model import IRI, Class, SubClassOf

from pyhermit.normalize import normalize_view


def _snapshot(name: str, first: str, second: str):  # type: ignore[no-untyped-def]
    source = f"""
Prefix(:=<urn:test:>)
Ontology(<urn:test:{name}>
  Declaration(Class(:{first}))
  Declaration(Class(:{second}))
  SubClassOf(:{first} :{second})
)
""".encode()
    return load_snapshot(
        source,
        options=LoadOptions(
            imports=ImportPolicy.IGNORE,
            backend=BackendPreference.PYTHON,
        ),
    )


def test_snapshot_overlay_composite_and_materialized_views_normalize_identically() -> None:
    source = _snapshot("source", "A", "B")
    target = _snapshot("target", "C", "D")
    bridge = SubClassOf(Class(IRI("urn:test:B")), Class(IRI("urn:test:C")))
    overlay = apply_delta(source, OntologyDelta(add_axioms={bridge}))
    composite = compose_views(overlay, target, roles=("source", "target"))
    normalized = normalize_view(composite)
    materialized = normalize_view(composite.materialize())
    assert normalized.canonical_snapshot() == materialized.canonical_snapshot()
    assert normalized.logical_fingerprint == composite.logical_fingerprint.hex
    assert normalized.source_axiom_count == sum(1 for _ in composite.iter_axioms())


def test_composite_member_order_does_not_change_normalized_output() -> None:
    source = _snapshot("source-order", "A", "B")
    target = _snapshot("target-order", "C", "D")
    forward = normalize_view(compose_views(source, target, roles=("source", "target")))
    reverse = normalize_view(compose_views(target, source, roles=("target", "source")))
    assert forward.canonical_snapshot() == reverse.canonical_snapshot()
