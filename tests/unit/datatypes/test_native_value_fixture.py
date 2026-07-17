from __future__ import annotations

from pathlib import Path

from tools.datatypes.build_native_value_fixture import canonical_bytes

FIXTURE = Path("tests/data/datatypes/wpr3-native-values-v1.json")


def test_wpr3_native_value_fixture_is_reproducible_from_python_semantics() -> None:
    assert FIXTURE.read_bytes() == canonical_bytes()
