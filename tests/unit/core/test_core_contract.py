from __future__ import annotations

import dataclasses
import os
import subprocess
import sys
from pathlib import Path

import pyowl_core
import pytest

import pyhermit.model as hermit_model
from pyhermit.config import ReasonerConfig
from pyhermit.core import (
    AdapterCompatibilityError,
    CapturedOntology,
    CoreVersionInfo,
    OptionConflictError,
    assign_dense_ids,
    capture_compatible_view,
    compiler_cache_key,
    generated_symbol_iri,
    load_snapshot,
    require_core_compatibility,
    validate_dense_id_capacity,
)
from pyhermit.exceptions import ResourceLimitError


class _View:
    def __init__(self, *, features: frozenset[str] | None = None) -> None:
        self.capabilities = pyowl_core.CoreCapabilities(
            adapter_protocol=1,
            model_schema=2,
            wire_format=(1, 2),
            features=features
            or frozenset(
                {
                    "document-boundaries",
                    "document-scoped-anonymous",
                    "import-manifest",
                    "ontology-identity-index",
                    "owl2-structural",
                }
            ),
        )
        self.structural_fingerprint = pyowl_core.Fingerprint("sha256", 2, b"s" * 32)
        self.logical_fingerprint = pyowl_core.Fingerprint("sha256", 2, b"l" * 32)
        self.signature_fingerprint = pyowl_core.Fingerprint("sha256", 2, b"g" * 32)
        self.report = object()
        self.origin_index = pyowl_core.OriginIndex()
        self.is_complete = True

    def iter_axioms(
        self,
        axiom_type=None,
        *,
        scope=pyowl_core.AxiomScope.CLOSURE,
        document_key=None,
    ):
        return iter(())

    def iter_extensions(
        self,
        namespace=None,
        *,
        scope=pyowl_core.AxiomScope.CLOSURE,
        document_key=None,
    ):
        return iter(())

    def contains(self, axiom, *, scope=pyowl_core.AxiomScope.CLOSURE, document_key=None):
        return False

    def ontology_annotations(
        self,
        *,
        scope=pyowl_core.AxiomScope.CLOSURE,
        document_key=None,
    ):
        return pyowl_core.CanonicalSet()

    def signature(
        self,
        kind=None,
        *,
        scope=pyowl_core.AxiomScope.CLOSURE,
        document_key=None,
        include_builtins=True,
    ):
        return ()

    def view(self, view_type, /, **options):
        return self


def test_all_structural_model_exports_are_exact_core_objects() -> None:
    assert hermit_model.__all__ == pyowl_core.model.__all__
    for name in hermit_model.__all__:
        assert getattr(hermit_model, name) is getattr(pyowl_core.model, name), name
    assert load_snapshot is pyowl_core.load_snapshot
    assert AdapterCompatibilityError is pyowl_core.AdapterCompatibilityError
    assert OptionConflictError is pyowl_core.OptionConflictError


def test_all_shared_view_and_delta_exports_are_exact_core_objects() -> None:
    import pyhermit.core as hermit_core

    for name in (
        "OntologyComposite",
        "OntologyDelta",
        "OntologyOverlay",
        "apply_delta",
        "compose_views",
    ):
        assert getattr(hermit_core, name) is getattr(pyowl_core, name)
        assert name in hermit_core.__all__


def test_capture_retains_exact_view_identity_and_fingerprints() -> None:
    view = _View()
    captured = capture_compatible_view(view)  # type: ignore[arg-type]
    assert captured.view is view
    assert captured.logical_fingerprint is view.logical_fingerprint
    assert captured.structural_fingerprint is view.structural_fingerprint
    assert captured.signature_fingerprint is view.signature_fingerprint
    with pytest.raises(dataclasses.FrozenInstanceError):
        captured.view = _View()  # type: ignore[misc]


@pytest.mark.parametrize(
    ("field", "value"),
    [
        ("package_version", "0.1.1"),
        ("api_version", (0, 1)),
        ("model_schema_version", 1),
        ("wire_format_version", (2, 0)),
        ("adapter_protocol_version", 2),
    ],
)
def test_version_mismatch_fails_with_exact_core_error(field: str, value: object) -> None:
    baseline = CoreVersionInfo("0.2.0", (0, 2), 2, (1, 2), 1)
    incompatible = dataclasses.replace(baseline, **{field: value})
    with pytest.raises(pyowl_core.AdapterCompatibilityError) as caught:
        require_core_compatibility(incompatible)
    assert caught.value.diagnostic is not None
    assert caught.value.diagnostic.details["field"]


def test_missing_view_capability_fails_before_private_compilation() -> None:
    view = _View(features=frozenset({"owl2-structural"}))
    with pytest.raises(pyowl_core.AdapterCompatibilityError, match="features"):
        capture_compatible_view(view)  # type: ignore[arg-type]


def test_compiler_key_uses_logical_signature_not_structural_fingerprint() -> None:
    captured = capture_compatible_view(_View())  # type: ignore[arg-type]
    first = compiler_cache_key(captured, ReasonerConfig())
    changed_structural = CapturedOntology(
        view=captured.view,
        structural_fingerprint=pyowl_core.Fingerprint("sha256", 2, b"z" * 32),
        logical_fingerprint=captured.logical_fingerprint,
        signature_fingerprint=captured.signature_fingerprint,
        core_package_version=captured.core_package_version,
        core_api_version=captured.core_api_version,
        core_model_schema_version=captured.core_model_schema_version,
        core_wire_format_version=captured.core_wire_format_version,
        core_adapter_protocol_version=captured.core_adapter_protocol_version,
    )
    assert compiler_cache_key(changed_structural, ReasonerConfig()) == first
    assert compiler_cache_key(captured, ReasonerConfig(blocking="ancestor")) != first  # type: ignore[arg-type]


def test_dense_ids_are_key_sorted_and_permutation_independent() -> None:
    forward = assign_dense_ids(((b"z", "last"), (b"a", "first")))
    reverse = assign_dense_ids(((b"a", "first"), (b"z", "last")))
    assert forward == reverse
    assert [(item.identifier, item.value) for item in forward] == [(0, "first"), (1, "last")]
    with pytest.raises(ValueError, match="unique"):
        assign_dense_ids(((b"same", 1), (b"same", 2)))


def test_dense_id_capacity_checks_boundary_without_allocating() -> None:
    validate_dense_id_capacity(1 << 32)
    with pytest.raises(ResourceLimitError):
        validate_dense_id_capacity((1 << 32) + 1)


def test_generated_names_bind_polarity_and_query_scope() -> None:
    fingerprint = pyowl_core.Fingerprint("sha256", 2, b"l" * 32)
    positive = generated_symbol_iri(fingerprint, b"expression", "positive")
    assert positive == generated_symbol_iri(fingerprint, b"expression", "positive")
    assert positive != generated_symbol_iri(fingerprint, b"expression", "negative")
    assert positive != generated_symbol_iri(
        fingerprint, b"expression", "positive", query_hash=b"q" * 32
    )
    assert "expression" not in positive


def test_import_has_no_native_java_network_or_rdflib_side_effects() -> None:
    script = """
import sys
import pyhermit.core
for name in ('rdflib', 'jpype', 'requests', 'pyhermit._native', 'pyhermit.backends.native'):
    assert name not in sys.modules, name
"""
    environment = dict(os.environ)
    roots = [str(pyowl_core.__path__[0] + "/.."), str(Path(__file__).parents[3] / "src")]
    environment["PYTHONPATH"] = os.pathsep.join(roots)
    subprocess.run([sys.executable, "-c", script], check=True, env=environment)
