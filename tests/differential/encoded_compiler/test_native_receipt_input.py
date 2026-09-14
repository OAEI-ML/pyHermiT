"""Core-issued native receipts replace duplicate Python bulk validation."""

# SPDX-License-Identifier: LGPL-3.0-or-later
from __future__ import annotations

from dataclasses import replace

import pyowl_core
import pyowl_core as owl
import pytest
from pyowl_core.exceptions import AdapterCompatibilityError, BackendProtocolError

from pyhermit import encoded_input


def snapshot(
    backend: pyowl_core.BackendPreference = pyowl_core.BackendPreference.NATIVE,
) -> owl.OntologyView:
    return pyowl_core.load_snapshot(
        b"Ontology(<urn:receipt:test> Declaration(Class(<urn:A>)) "
        b"Declaration(Class(<urn:B>)) SubClassOf(<urn:A> <urn:B>))",
        options=pyowl_core.LoadOptions(backend=backend, imports=pyowl_core.ImportPolicy.IGNORE),
    )


def test_strict_native_receipt_skips_duplicate_python_fingerprint_scan(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    view = snapshot()

    def forbidden(*args: object, **kwargs: object) -> object:
        raise AssertionError("Python repeated a native column fingerprint scan")

    monkeypatch.setattr(encoded_input, "_encoded_fingerprint", forbidden)
    result = encoded_input.negotiate_encoded_input(
        view, {encoded_input.ENCODED_SCHEMA_NAME: 2}, require_native_validation=True
    )
    assert result.lease is not None
    assert result.lease.native_validated
    assert len(result.lease.root_slices()) == 1
    assert result.lease.owner is view


def test_strict_receipt_rejects_unproven_python_owners_and_missing_capability() -> None:
    view = snapshot(pyowl_core.BackendPreference.PYTHON)
    with pytest.raises((AdapterCompatibilityError, BackendProtocolError)):
        encoded_input.negotiate_encoded_input(
            view, {encoded_input.ENCODED_SCHEMA_NAME: 2}, require_native_validation=True
        )
    with pytest.raises((AdapterCompatibilityError, BackendProtocolError)):
        encoded_input.negotiate_encoded_input(snapshot(), {}, require_native_validation=True)


def test_native_receipt_binds_exact_owner_and_fingerprint() -> None:
    view = snapshot()
    lease = encoded_input.negotiate_encoded_input(
        view, {encoded_input.ENCODED_SCHEMA_NAME: 2}, require_native_validation=True
    ).lease
    assert lease is not None
    other = snapshot()
    with pytest.raises(BackendProtocolError):
        encoded_input._validate_encoded_view(
            other,
            lease.encoded_view,
            owl.AxiomScope.CLOSURE,
            document_key=None,
            active=frozenset(),
            validated={},
            require_native_validation=True,
        )
    forged = replace(
        lease.encoded_view, structural_fingerprint=owl.Fingerprint("sha256", 2, bytes(32))
    )
    with pytest.raises(BackendProtocolError):
        encoded_input._validate_encoded_view(
            view,
            forged,
            owl.AxiomScope.CLOSURE,
            document_key=None,
            active=frozenset(),
            validated={},
            require_native_validation=True,
        )
