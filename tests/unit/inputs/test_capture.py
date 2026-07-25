from __future__ import annotations

import io

import pyowl_core
import pytest
from pyowl_core import (
    AdapterCompatibilityError,
    BackendPreference,
    ImportPolicy,
    LoadOptions,
    MappingResolver,
    OptionConflictError,
)

from pyhermit.config import UnsupportedDatatypePolicy
from pyhermit.exceptions import (
    IncompleteImportClosureError,
    OntologyProfileError,
    ReasonerInterruptedError,
)
from pyhermit.inputs import capture_ontology
from pyhermit.io import (
    coerce_snapshot as reexported_coerce_snapshot,
)
from pyhermit.io import (
    load_snapshot as reexported_load_snapshot,
)
from pyhermit.io import (
    parse_document as reexported_parse_document,
)

OPTIONS = LoadOptions(imports=ImportPolicy.IGNORE, backend=BackendPreference.PYTHON)


def functional(*body: str, imports: tuple[str, ...] = ()) -> bytes:
    import_values = " ".join(f"Import(<{value}>)" for value in imports)
    return (
        "Prefix(:=<urn:test#>) Ontology(<urn:test:input> "
        + import_values
        + " "
        + " ".join(body)
        + ")"
    ).encode()


class Provider:
    def __init__(self, value: object) -> None:
        self.value = value
        self.calls = 0

    def owl_snapshot(self) -> object:
        self.calls += 1
        return self.value


def test_io_surface_is_an_exact_core_reexport() -> None:
    assert reexported_parse_document is pyowl_core.parse_document
    assert reexported_load_snapshot is pyowl_core.load_snapshot
    assert reexported_coerce_snapshot is pyowl_core.coerce_snapshot


def test_capture_retains_existing_view_and_calls_provider_once() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional("Declaration(Class(:A))"),
        options=OPTIONS,
    )
    provider = Provider(snapshot)

    direct = capture_ontology(snapshot)
    supplied = capture_ontology(provider)  # type: ignore[arg-type]

    assert direct.view is snapshot
    assert supplied.view is snapshot
    assert supplied.captured.logical_fingerprint is snapshot.logical_fingerprint
    assert provider.calls == 1


def test_bytes_and_caller_owned_stream_have_equal_validated_semantics() -> None:
    source = functional(
        "Declaration(Class(:A))",
        "Declaration(Class(:B))",
        "SubClassOf(:A :B)",
    )
    stream = io.BytesIO(source)

    from_bytes = capture_ontology(source, load_options=OPTIONS)
    from_stream = capture_ontology(
        stream,
        document_iri="urn:test:stream-input",
        load_options=OPTIONS,
    )

    assert not stream.closed
    assert from_bytes.captured.logical_fingerprint == from_stream.captured.logical_fingerprint
    assert from_bytes.profile == from_stream.profile


def test_incomplete_import_closure_fails_before_profile_validation() -> None:
    source = functional("Declaration(Class(:A))", imports=("urn:test:missing",))

    with pytest.raises(IncompleteImportClosureError) as caught:
        capture_ontology(source, load_options=OPTIONS)
    assert caught.value.context["document_count"] == 1
    assert len(str(caught.value.context["import_manifest_sha256"])) == 64
    assert len(str(caught.value.context["loader_diagnostics_sha256"])) == 64
    assert len(str(caught.value.context["structural_fingerprint"])) == 64


def test_existing_view_option_and_resolver_conflicts_propagate_without_rebuild() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional("Declaration(Class(:A))"),
        options=OPTIONS,
    )
    with pytest.raises(OptionConflictError):
        capture_ontology(snapshot, load_options=LoadOptions())
    with pytest.raises(OptionConflictError):
        capture_ontology(snapshot, resolver=MappingResolver({}))


def test_malformed_provider_and_profile_cancellation_are_not_retried() -> None:
    invalid = Provider(object())
    with pytest.raises(AdapterCompatibilityError):
        capture_ontology(invalid)  # type: ignore[arg-type]
    assert invalid.calls == 1

    snapshot = pyowl_core.load_snapshot(
        functional("Declaration(Class(:A))"),
        options=OPTIONS,
    )
    with pytest.raises(ReasonerInterruptedError):
        capture_ontology(snapshot, cancelled=lambda: True)


def test_profile_validator_observes_the_complete_report_before_public_rejection() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(DataProperty(:p))",
            "Declaration(DataProperty(:q))",
            "SubClassOf(:A DataSomeValuesFrom(:p :q <http://www.w3.org/2001/XMLSchema#string>))",
        ),
        options=OPTIONS,
    )
    observed: list[tuple[object, object, object]] = []

    def validate(view: object, report: object, policy: object) -> None:
        observed.append((view, report, policy))

    with pytest.raises(OntologyProfileError) as caught:
        capture_ontology(snapshot, _profile_validator=validate)

    assert len(observed) == 1
    assert observed[0][0] is snapshot
    report = observed[0][1]
    assert report.conforms is False  # type: ignore[attr-defined]
    assert observed[0][2] is UnsupportedDatatypePolicy.ERROR
    assert caught.value.context["rule_ids"] == "OWL2_DATA_RANGE_ARITY"
