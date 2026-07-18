from pathlib import Path

from tools.datatypes.build_native_semantic_solver_fixture import canonical_bytes

FIXTURE = Path("tests/data/datatypes/wpr3-native-semantic-solver-v1.json")


def test_native_semantic_solver_fixture_is_canonical_and_reproducible() -> None:
    assert FIXTURE.read_bytes() == canonical_bytes()
