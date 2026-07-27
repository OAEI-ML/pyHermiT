"""Native lifecycle dispatch before scalar ontology traversal."""

# SPDX-License-Identifier: LGPL-3.0-or-later

from __future__ import annotations

from types import SimpleNamespace
from typing import NoReturn

import pyowl_core
import pyowl_core.model as owl
import pytest

import pyhermit.facade as facade_module
from pyhermit import Reasoner, ReasonerConfig
from pyhermit.exceptions import OntologyProfileError

OPTIONS = pyowl_core.LoadOptions(
    imports=pyowl_core.ImportPolicy.IGNORE,
    backend=pyowl_core.BackendPreference.PYTHON,
)


def functional(*body: str) -> bytes:
    return (
        "Prefix(:=<urn:test:native-first#>) "
        "Ontology(<urn:test:native-first> " + " ".join(body) + ")"
    ).encode()


class _Session:
    def __init__(self) -> None:
        self.closed = False

    def close(self) -> None:
        self.closed = True


class _Factory:
    def __init__(self, failure: BaseException | None = None) -> None:
        self.failure = failure
        self.calls: list[tuple[object, ReasonerConfig, object, bool]] = []
        self.sessions: list[_Session] = []

    def _create_encoded_lifecycle_handoff(
        self,
        captured: object,
        config: ReasonerConfig,
        cancellation: object,
        *,
        validate_profile: bool,
    ) -> _Session:
        self.calls.append((captured, config, cancellation, validate_profile))
        if self.failure is not None:
            raise self.failure
        session = _Session()
        self.sessions.append(session)
        return session

    @staticmethod
    def _validate_encoded_handoff(_view: object) -> NoReturn:
        raise AssertionError("encoded preflight replayed before native construction")

    @staticmethod
    def _validate_encoded_profile_handoff(*_args: object, **_kwargs: object) -> NoReturn:
        raise AssertionError("scalar/native profile comparison ran on production native path")


def _forbidden_scalar(*_args: object, **_kwargs: object) -> NoReturn:
    raise AssertionError("scalar ontology traversal ran before native construction")


def _runtime(
    _reasoner: Reasoner,
    _captured: object,
    session: _Session,
    *,
    compile_started: float,
) -> SimpleNamespace:
    assert compile_started >= 0.0
    return SimpleNamespace(program=None, session=session)


def test_native_initialization_and_flush_never_enter_scalar_profile_or_compiler(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "SubClassOf(:A :B)",
        ),
        options=OPTIONS,
    )
    factory = _Factory()
    monkeypatch.setattr(facade_module, "select_backend_factory", lambda _config: factory)
    monkeypatch.setattr(facade_module, "_validate_captured_ontology", _forbidden_scalar)
    monkeypatch.setattr(facade_module, "capture_ontology", _forbidden_scalar)
    monkeypatch.setattr(facade_module, "compile_captured_bundle", _forbidden_scalar)
    monkeypatch.setattr(Reasoner, "_encoded_services", _runtime)

    reasoner = Reasoner(snapshot)
    addition = owl.SubClassOf(
        owl.Class(owl.IRI("urn:test:native-first#B")),
        owl.Class(owl.IRI("urn:test:native-first#C")),
    )
    reasoner._pending_additions.add(addition)
    reasoner._flush_locked()

    assert len(factory.calls) == 2
    assert all(call[3] is True for call in factory.calls)
    assert factory.sessions[0].closed
    assert not factory.sessions[1].closed
    assert reasoner.ontology is not snapshot
    reasoner.dispose()
    assert factory.sessions[1].closed


def test_native_profile_failure_is_not_replayed_through_scalar_validation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    snapshot = pyowl_core.load_snapshot(
        functional("Declaration(Class(:A))"),
        options=OPTIONS,
    )
    failure = OntologyProfileError(
        "native profile rejected the ontology",
        code="OWL2DL_PROFILE_VIOLATION",
        context={"issue_count": 1},
    )
    factory = _Factory(failure)
    monkeypatch.setattr(facade_module, "select_backend_factory", lambda _config: factory)
    monkeypatch.setattr(facade_module, "_validate_captured_ontology", _forbidden_scalar)
    monkeypatch.setattr(facade_module, "capture_ontology", _forbidden_scalar)
    monkeypatch.setattr(facade_module, "compile_captured_bundle", _forbidden_scalar)

    with pytest.raises(OntologyProfileError) as caught:
        Reasoner(snapshot)

    assert caught.value is failure
    assert len(factory.calls) == 1
