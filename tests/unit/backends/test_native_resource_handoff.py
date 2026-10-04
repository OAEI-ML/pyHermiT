"""Native profile limits remain effective without an operation token."""

# SPDX-License-Identifier: LGPL-3.0-or-later

from __future__ import annotations

from types import SimpleNamespace

import pytest
from tests.unit.backends.test_native_adapter import (
    _extension,
    _Handle,
    _profile_fixture,
    _profile_lease,
    _profile_result,
)

from pyhermit.backends.native import NativeBackendFactory
from pyhermit.config import UnsupportedDatatypePolicy


@pytest.mark.parametrize("max_memory_bytes", (None, 4_096))
@pytest.mark.parametrize("compiler_fails", (False, True), ids=("success", "failure"))
def test_profile_handoff_honors_memory_limit_without_cancellation(
    monkeypatch: pytest.MonkeyPatch,
    max_memory_bytes: int | None,
    compiler_fails: bool,
) -> None:
    extension, _handles, _sessions = _extension()
    snapshot, report = _profile_fixture()
    handles: list[_Handle] = []
    received: dict[str, object] = {}
    failure = RuntimeError("profile compiler failed")

    class TrackingHandle(_Handle):
        def __init__(
            self,
            timeout: float | None = None,
            max_memory_bytes: int | None = None,
        ) -> None:
            super().__init__(timeout, max_memory_bytes)
            handles.append(self)

    def compile_profile(**values: object) -> bytes:
        received.update(values)
        if compiler_fails:
            raise failure
        return _profile_result(report)

    extension.CancellationHandle = TrackingHandle
    extension._encoded_profile_slices_manifest_v1 = compile_profile
    monkeypatch.setattr(
        "pyhermit.backends.native.negotiate_encoded_input",
        lambda _view, _schemas: SimpleNamespace(lease=_profile_lease(snapshot)),
    )
    factory = NativeBackendFactory(extension)
    if compiler_fails:
        with pytest.raises(RuntimeError) as caught:
            factory._validate_encoded_profile_handoff(
                snapshot,
                report,
                UnsupportedDatatypePolicy.ERROR,
                max_memory_bytes=max_memory_bytes,
            )
        assert caught.value is failure
    else:
        factory._validate_encoded_profile_handoff(
            snapshot,
            report,
            UnsupportedDatatypePolicy.ERROR,
            max_memory_bytes=max_memory_bytes,
        )

    if max_memory_bytes is None:
        assert handles == []
        assert received["cancellation"] is None
    else:
        assert len(handles) == 1
        assert received["cancellation"] is handles[0]
        assert handles[0].resets == [(None, max_memory_bytes)]
        assert handles[0].interruptions == []
