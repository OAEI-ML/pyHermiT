"""One-call pyowl-core input capture with strict closure/profile validation.

SPDX-License-Identifier: LGPL-3.0-or-later
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass

import pyowl_core
from pyowl_core import (
    IRI,
    CancellationToken,
    ImportResolver,
    LoadOptions,
    OntologyInput,
    OntologyView,
)
from pyowl_core.index import OntologyIdentityIndex

from .config import ReasonerConfig, UnsupportedDatatypePolicy
from .core import (
    CapturedOntology,
    DeferredCapturedOntology,
    _deferred_capture_eligible,
    capture_compatible_view,
    capture_compatible_view_deferred,
    materialize_deferred_capture,
)
from .exceptions import IncompleteImportClosureError
from .profile import OWL2DLReport, validate_owl2_dl_view

_ProfileValidator = Callable[
    [OntologyView, OWL2DLReport, UnsupportedDatatypePolicy],
    None,
]


@dataclass(frozen=True, slots=True)
class _CapturedOntologyInput:
    """Complete retained input before the backend-specific profile gate."""

    captured: CapturedOntology | DeferredCapturedOntology
    identity: OntologyIdentityIndex

    def __post_init__(self) -> None:
        if not isinstance(
            self.captured,
            (CapturedOntology, DeferredCapturedOntology),
        ):
            raise TypeError(
                "captured must be CapturedOntology or DeferredCapturedOntology"
            )
        if not isinstance(self.identity, OntologyIdentityIndex):
            raise TypeError("identity must be OntologyIdentityIndex")

    @property
    def view(self) -> OntologyView:
        return self.captured.view


@dataclass(frozen=True, slots=True)
class ValidatedOntology:
    captured: CapturedOntology
    profile: OWL2DLReport
    identity: OntologyIdentityIndex

    def __post_init__(self) -> None:
        if not isinstance(self.captured, CapturedOntology):
            raise TypeError("captured must be CapturedOntology")
        if not isinstance(self.profile, OWL2DLReport):
            raise TypeError("profile must be OWL2DLReport")
        if not isinstance(self.identity, OntologyIdentityIndex):
            raise TypeError("identity must be OntologyIdentityIndex")
        if not self.profile.conforms:
            raise ValueError("profile must be a complete conforming OWL2DLReport")

    @property
    def view(self) -> OntologyView:
        return self.captured.view


def capture_ontology(
    source: OntologyInput,
    *,
    config: ReasonerConfig | None = None,
    document_iri: IRI | str | None = None,
    load_options: LoadOptions | None = None,
    resolver: ImportResolver | None = None,
    cancellation_token: CancellationToken | None = None,
    cancelled: Callable[[], bool] | None = None,
    _profile_validator: _ProfileValidator | None = None,
) -> ValidatedOntology:
    """Cross the shared-core boundary exactly once and validate the retained view."""

    selected_config = ReasonerConfig() if config is None else config
    if not isinstance(selected_config, ReasonerConfig):
        raise TypeError("config must be ReasonerConfig or None")
    if load_options is not None and not isinstance(load_options, LoadOptions):
        raise TypeError("load_options must be LoadOptions or None")
    if document_iri is not None and not isinstance(document_iri, (IRI, str)):
        raise TypeError("document_iri must be IRI, str, or None")
    if resolver is not None and not isinstance(resolver, ImportResolver):
        raise TypeError("resolver must satisfy ImportResolver or be None")
    if cancellation_token is not None and not isinstance(cancellation_token, CancellationToken):
        raise TypeError("cancellation_token must be pyowl_core.CancellationToken or None")
    if cancelled is not None and not callable(cancelled):
        raise TypeError("cancelled must be callable or None")
    if _profile_validator is not None and not callable(_profile_validator):
        raise TypeError("_profile_validator must be callable or None")
    captured_input = _capture_ontology_input(
        source,
        document_iri=document_iri,
        load_options=load_options,
        resolver=resolver,
        cancellation_token=cancellation_token,
    )
    return _validate_captured_ontology(
        captured_input,
        config=selected_config,
        cancellation_token=cancellation_token,
        cancelled=cancelled,
        profile_validator=_profile_validator,
    )


def _capture_ontology_input(
    source: OntologyInput,
    *,
    document_iri: IRI | str | None = None,
    load_options: LoadOptions | None = None,
    resolver: ImportResolver | None = None,
    cancellation_token: CancellationToken | None = None,
    defer_fingerprints: bool = False,
) -> _CapturedOntologyInput:
    """Capture and prove closure completeness without traversing scalar axioms."""

    if load_options is not None and not isinstance(load_options, LoadOptions):
        raise TypeError("load_options must be LoadOptions or None")
    if document_iri is not None and not isinstance(document_iri, (IRI, str)):
        raise TypeError("document_iri must be IRI, str, or None")
    if resolver is not None and not isinstance(resolver, ImportResolver):
        raise TypeError("resolver must satisfy ImportResolver or be None")
    if cancellation_token is not None and not isinstance(cancellation_token, CancellationToken):
        raise TypeError("cancellation_token must be pyowl_core.CancellationToken or None")
    if type(defer_fingerprints) is not bool:
        raise TypeError("defer_fingerprints must be bool")
    view = pyowl_core.coerce_snapshot(
        source,
        document_iri=document_iri,
        options=load_options,
        resolver=resolver,
        cancellation_token=cancellation_token,
    )
    captured: CapturedOntology | DeferredCapturedOntology
    if defer_fingerprints and isinstance(
        view,
        (pyowl_core.OntologyOverlay, pyowl_core.OntologyComposite),
    ) and _deferred_capture_eligible(view):
        captured = capture_compatible_view_deferred(view)
    else:
        captured = capture_compatible_view(view)
    identity = view.view(OntologyIdentityIndex)
    if not view.is_complete or not identity.is_complete:
        diagnostic_codes = ",".join(
            sorted({diagnostic.code for diagnostic in view.report.diagnostics})
        )
        raise IncompleteImportClosureError(
            "reasoning requires a complete resolved import closure",
            context={
                "core_backend": view.report.backend,
                "core_diagnostic_codes": diagnostic_codes or None,
                "document_count": view.report.document_count,
                "import_manifest_sha256": identity.import_manifest_digest.hex(),
                "loader_diagnostics_sha256": identity.loader_diagnostics_digest.hex(),
                "structural_fingerprint": view.structural_fingerprint.hex,
            },
        )
    return _CapturedOntologyInput(captured, identity)


def _validate_captured_ontology(
    captured_input: _CapturedOntologyInput,
    *,
    config: ReasonerConfig,
    cancellation_token: CancellationToken | None = None,
    cancelled: Callable[[], bool] | None = None,
    profile_validator: _ProfileValidator | None = None,
) -> ValidatedOntology:
    """Run the scalar compatibility profile gate over an existing capture."""

    if not isinstance(captured_input, _CapturedOntologyInput):
        raise TypeError("captured_input must be _CapturedOntologyInput")
    if not isinstance(config, ReasonerConfig):
        raise TypeError("config must be ReasonerConfig")
    if cancellation_token is not None and not isinstance(cancellation_token, CancellationToken):
        raise TypeError("cancellation_token must be pyowl_core.CancellationToken or None")
    if cancelled is not None and not callable(cancelled):
        raise TypeError("cancelled must be callable or None")
    if profile_validator is not None and not callable(profile_validator):
        raise TypeError("profile_validator must be callable or None")

    captured = captured_input.captured
    if isinstance(captured, DeferredCapturedOntology):
        captured = materialize_deferred_capture(captured)

    def is_cancelled() -> bool:
        return bool(
            (cancellation_token is not None and cancellation_token.cancelled)
            or (cancelled is not None and cancelled())
        )

    report = validate_owl2_dl_view(
        captured_input.view,
        unsupported_datatypes=config.unsupported_datatypes,
        cancelled=is_cancelled if cancelled is not None or cancellation_token is not None else None,
    )
    if profile_validator is not None:
        profile_validator(
            captured_input.view,
            report,
            config.unsupported_datatypes,
        )
    report.raise_for_errors()
    return ValidatedOntology(
        captured,
        report,
        captured_input.identity,
    )


__all__ = ["ValidatedOntology", "capture_ontology"]
