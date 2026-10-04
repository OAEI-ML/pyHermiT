"""Actual native profile manifests enforce the existing handle memory allowance."""

# SPDX-License-Identifier: LGPL-3.0-or-later

from __future__ import annotations

from typing import Any

import pyowl_core
import pytest
from pyowl_core.backends.native_views import produce_encoded_structural_view_v2

import pyhermit._native as native
from pyhermit.backends.native import NativeBackendFactory
from pyhermit.config import UnsupportedDatatypePolicy
from pyhermit.exceptions import ReasonerInterruptedError, ResourceLimitError
from pyhermit.profile import validate_owl2_dl_view


def _snapshot() -> pyowl_core.OntologyView:
    return pyowl_core.load_snapshot(
        b"Prefix(:=<urn:test:profile-memory#>) "
        b"Ontology(<urn:test:profile-memory> "
        b"Declaration(Class(:A)) Declaration(Class(:B)) SubClassOf(:A :B))",
        options=pyowl_core.LoadOptions(
            imports=pyowl_core.ImportPolicy.IGNORE,
            backend=pyowl_core.BackendPreference.NATIVE,
        ),
    )


@pytest.mark.parametrize("sliced", (False, True), ids=("columns", "slices"))
def test_profile_manifest_handle_budget_failure_reset_and_cancellation(sliced: bool) -> None:
    buffers = dict(produce_encoded_structural_view_v2(_snapshot()).buffers)
    arguments: dict[str, Any]
    if sliced:
        record = (
            0,
            memoryview(b""),
            (),
            (),
            buffers["root_kinds"],
            buffers["root_ids"],
            buffers["node_tags"],
            buffers["node_field_offsets"],
            buffers["field_kinds"],
            buffers["field_values"],
            buffers["field_lengths"],
            buffers["item_kinds"],
            buffers["item_values"],
            buffers["item_lengths"],
            buffers["scalar_bytes"],
        )
        arguments = {"slices": (record,)}
        compiler = native._encoded_profile_slices_manifest_v1
    else:
        arguments = dict(buffers)
        compiler = native._encoded_profile_manifest_v1

    baseline = compiler(**arguments)
    handle = native.CancellationHandle(max_memory_bytes=1)
    with pytest.raises(ResourceLimitError) as caught:
        compiler(**arguments, cancellation=handle)
    assert caught.value.context["limit"] == "profile-owned-bytes"
    assert int(caught.value.context["max_owned_bytes"]) == 1
    assert (
        int(caught.value.context["current_bytes"]) + int(caught.value.context["requested_bytes"])
        > 1
    )

    handle.reset(max_memory_bytes=1024 * 1024)
    assert compiler(**arguments, cancellation=handle) == baseline
    assert handle.interrupt("profile memory test")
    with pytest.raises(ReasonerInterruptedError, match="profile memory test"):
        compiler(**arguments, cancellation=handle)

    handle.reset()
    assert compiler(**arguments, cancellation=handle) == baseline


def test_profile_handoff_enforces_memory_without_python_cancellation_token() -> None:
    snapshot = _snapshot()
    profile = validate_owl2_dl_view(snapshot)
    factory = NativeBackendFactory(native)

    with pytest.raises(ResourceLimitError, match=r"profile.*byte limit"):
        factory._validate_encoded_profile_handoff(
            snapshot,
            profile,
            UnsupportedDatatypePolicy.ERROR,
            max_memory_bytes=1,
        )

    for maximum in (1024 * 1024, None):
        factory._validate_encoded_profile_handoff(
            snapshot,
            profile,
            UnsupportedDatatypePolicy.ERROR,
            max_memory_bytes=maximum,
        )
