from __future__ import annotations

from pathlib import Path

from tools.roles.build_native_fixture import canonical_bytes

FIXTURE = Path("tests/data/roles/wpr3-role-automata-v1.json")


def test_wpr3_native_role_fixture_is_reproducible_from_python_oracle() -> None:
    assert FIXTURE.read_bytes() == canonical_bytes()
