"""Opt-in strict native construction and taxonomy have no Python fallback."""

# SPDX-License-Identifier: LGPL-3.0-or-later
from __future__ import annotations

import pyowl_core as core
import pyowl_core.model as owl
import pytest
from tests.differential.encoded_compiler.test_native_receipt_input import snapshot

from pyhermit import Reasoner, ReasonerConfig, require_native_pipeline_support
from pyhermit.backends import dispatch, native_context
from pyhermit.config import BackendName
from pyhermit.exceptions import FeatureNotImplementedError, NativeBackendUnavailableError


def test_strict_public_native_taxonomy_uses_receipts_without_python_scans(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    view = snapshot()
    require_native_pipeline_support()

    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("strict native pipeline performed Python ontology traversal")

    import pyhermit.services.checks as checks

    monkeypatch.setattr(checks, "enumerate", forbidden, raising=False)
    monkeypatch.setattr(native_context._NativeSignature, "__iter__", forbidden)
    monkeypatch.setattr(type(view), "origin_index", property(forbidden))
    a, b = owl.Class(owl.IRI("urn:A")), owl.Class(owl.IRI("urn:B"))
    with Reasoner(view, config=ReasonerConfig(require_native_pipeline=True)) as reasoner:
        assert reasoner.is_consistent()
        before = reasoner.diagnostics()
        assert before["native_pipeline_required"] is True
        assert before["native_core_receipt_validated"] is True
        assert before["native_metadata_validation"] is True
        assert before["native_metadata_domain_copies"] == 0
        assert before["native_result_validation"] is False
        assert before["native_result_publications"] == 0
        assert reasoner.is_subclass(a, b)
        assert a in set().union(*reasoner.subclasses(b))
        assert reasoner.class_hierarchy().nodes
        assert reasoner.object_property_hierarchy().nodes
        assert reasoner.data_property_hierarchy().nodes
        assert reasoner.diagnostics()["native_result_validation"] is True
        publications = reasoner.diagnostics()["native_result_publications"]
        assert isinstance(publications, int) and publications >= 3
        assert reasoner.diagnostics()["encoded_compiler_gil_released"] is True
        assert reasoner.diagnostics()["python_symbol_validation_rows"] == 0


def test_strict_native_preflight_rejects_missing_receipts_before_input_capture(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import pyhermit.facade as facade

    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("input captured before unavailable native preflight")

    monkeypatch.setattr(core, "native_validation_available", lambda: False)
    monkeypatch.setattr(facade, "_capture_ontology_input", forbidden)
    with pytest.raises(NativeBackendUnavailableError, match="validation receipts"):
        Reasoner(b"not parsed", config=ReasonerConfig(require_native_pipeline=True))
    with pytest.raises(NativeBackendUnavailableError, match="validation receipts"):
        require_native_pipeline_support()


@pytest.mark.parametrize("backend", [BackendName.PYTHON, BackendName.VERIFY])
def test_strict_native_rejects_incompatible_backend(backend: BackendName) -> None:
    with pytest.raises(NativeBackendUnavailableError, match="incompatible"):
        dispatch.select_backend_factory(
            ReasonerConfig(backend=backend, require_native_pipeline=True)
        )


def test_strict_native_rejects_unproven_owner_and_optional_operations_before_work(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from pyowl_core.exceptions import AdapterCompatibilityError, BackendProtocolError

    config = ReasonerConfig(require_native_pipeline=True)
    with pytest.raises((AdapterCompatibilityError, BackendProtocolError)):
        Reasoner(snapshot(core.BackendPreference.PYTHON), config=config)
    with Reasoner(snapshot(), config=config) as reasoner:

        def forbidden(*args: object, **kwargs: object) -> None:
            raise AssertionError("strict unsupported operation reached an overlay")

        monkeypatch.setattr(core, "apply_delta", forbidden)
        with pytest.raises(FeatureNotImplementedError, match="query-delta"):
            reasoner._temporary_encoded_check(
                (owl.ClassAssertion(owl.OWL_THING, owl.NamedIndividual(owl.IRI("urn:fresh"))),)
            )
        with pytest.raises(FeatureNotImplementedError, match="realization"):
            reasoner._runtime.realization._ensure_coarse()
        assert reasoner.is_consistent()


def test_strict_flag_is_boolean_and_default_cache_identity_stays_compatible() -> None:
    assert "require_native_pipeline" not in ReasonerConfig().as_dict()
    assert ReasonerConfig(require_native_pipeline=True).as_dict()["require_native_pipeline"] is True
    with pytest.raises(TypeError, match="bool"):
        ReasonerConfig(require_native_pipeline=1)  # type: ignore[arg-type]


def test_strict_native_constructor_rejects_python_indexed_buffers() -> None:
    from typing import Any

    from tests.differential.encoded_compiler.test_permanent_program_assembly import _slice_record

    from pyhermit import _native
    from pyhermit.backends.native_input import encode_config, encode_encoded_session_metadata
    from pyhermit.inputs import capture_ontology

    view = snapshot()
    config = ReasonerConfig()
    captured = capture_ontology(view, config=config).captured

    def backed_by_bytearray(value: Any) -> Any:
        if isinstance(value, memoryview):
            return memoryview(bytearray(value)).toreadonly()
        if isinstance(value, tuple):
            return tuple(map(backed_by_bytearray, value))
        return value

    with pytest.raises(FeatureNotImplementedError, match="Python byte indexing"):
        _native._create_encoded_session_v1(
            slices=(backed_by_bytearray(_slice_record(view)),),
            metadata=encode_encoded_session_metadata(captured, config),
            config=encode_config(config),
            cancellation=_native.CancellationHandle(),
            require_native_pipeline=True,
        )


def test_strict_composite_and_overlay_owners_fail_with_core_compatibility_error(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from pyowl_core.exceptions import AdapterCompatibilityError

    left, right = snapshot(), snapshot()
    composite = core.compose_views(left, right, roles=("left", "right"))
    overlay = core.apply_delta(
        left,
        core.OntologyDelta(
            add_axioms=owl.CanonicalSet((owl.Declaration(owl.Class(owl.IRI("urn:C"))),))
        ),
    )
    import pyhermit.facade as facade

    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("unsupported owner reached capture/fingerprint work")

    monkeypatch.setattr(facade, "_capture_ontology_input", forbidden)
    for view in (composite, overlay):
        with pytest.raises(AdapterCompatibilityError, match="native"):
            Reasoner(view, config=ReasonerConfig(require_native_pipeline=True))
