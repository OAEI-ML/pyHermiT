from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass

import pytest

from pyhermit.backends.protocol import (
    U32_MAX,
    BackendAvailability,
    BackendInfo,
    BackendStatus,
    CheckResult,
    CompiledOntology,
    EntityRef,
    Hierarchy,
    HierarchyIds,
    RealizationIds,
    ReasoningStatistics,
    canonical_backend_json,
)
from pyhermit.exceptions import ResourceLimitError


@dataclass(frozen=True)
class _Fingerprint:
    digest: bytes
    algorithm: str = "sha256"
    schema: int = 1

    @property
    def hex(self) -> str:
        return self.digest.hex()


@dataclass(frozen=True)
class _IR:
    payload: bytes
    schema_version: int = 1

    def canonical_bytes(self) -> bytes:
        return self.payload


def _compiled() -> CompiledOntology:
    fingerprint = _Fingerprint(b"x" * 32)
    a, b = _IR(b"a"), _IR(b"b")
    clauses = tuple(sorted((a, b), key=lambda value: hashlib.sha256(value.payload).digest()))
    return CompiledOntology(
        schema_version=1,
        ontology_fingerprint="0" * 64,
        source_structural_fingerprint=fingerprint,
        source_logical_fingerprint=fingerprint,
        source_signature_fingerprint=fingerprint,
        core_package_version="0.1.0",
        core_api_version=(0, 1),
        core_model_schema_version=1,
        core_wire_format_version=(1, 0),
        core_adapter_protocol_version=1,
        symbols=a,
        clauses=clauses,
        positive_facts=(),
        negative_facts=(),
        ground_disjunctions=(),
        role_model=a,
        datatype_model=a,
        expressivity=a,
        declared_entities=(EntityRef("class", "https://example.org/A", 0),),
        named_individuals=(0,),
        provenance=a,
    )


def test_compiled_manifest_is_canonical_and_contains_no_source_path_or_owl_text() -> None:
    compiled = _compiled()
    first = compiled.canonical_json()
    second = _compiled().canonical_json()
    assert first == second
    assert "https://example.org/A" in first
    assert "source_path" not in first
    assert "Ontology(" not in first


def test_compiled_collections_preserve_native_order_and_require_uniqueness() -> None:
    compiled = _compiled()
    values = {field: getattr(compiled, field) for field in compiled.__dataclass_fields__}
    values["clauses"] = tuple(reversed(compiled.clauses))
    reordered = CompiledOntology(**values)
    assert reordered.clauses == tuple(reversed(compiled.clauses))
    values["clauses"] = (compiled.clauses[0], compiled.clauses[0])
    with pytest.raises(ValueError, match="unique canonical"):
        CompiledOntology(**values)


def test_entity_ref_rejects_u32_overflow() -> None:
    with pytest.raises(ResourceLimitError) as caught:
        EntityRef("class", "https://example.org/A", U32_MAX + 1)
    assert caught.value.context["limit"] == "u32"


def test_check_result_equality_ignores_statistics() -> None:
    assert CheckResult(True, ReasoningStatistics(nodes=1)) == CheckResult(
        True, ReasoningStatistics(nodes=100)
    )


def test_hierarchy_ids_validate_partition_dag_and_reduction() -> None:
    hierarchy = HierarchyIds(
        nodes=((0,), (1, 2), (3,)),
        edges=((0, 1), (1, 2)),
        top_node=2,
        bottom_node=0,
    )
    assert hierarchy.nodes[1] == (1, 2)
    with pytest.raises(ValueError, match="transitive reduction"):
        HierarchyIds(
            nodes=((0,), (1,), (2,)),
            edges=((0, 1), (0, 2), (1, 2)),
            top_node=2,
            bottom_node=0,
        )
    with pytest.raises(ValueError, match="acyclic"):
        HierarchyIds(
            nodes=((0,), (1,)),
            edges=((0, 1), (1, 0)),
            top_node=1,
            bottom_node=0,
        )


def test_public_hierarchy_derives_ancestors_and_descendants() -> None:
    hierarchy = Hierarchy(
        nodes=(frozenset({"bottom"}), frozenset({"middle"}), frozenset({"top"})),
        edges=frozenset({(0, 1), (1, 2)}),
        top_node=2,
        bottom_node=0,
    )
    assert hierarchy.ancestors(0) == frozenset({1, 2})
    assert hierarchy.descendants(2) == frozenset({0, 1})


def test_realization_ids_partition_and_reference_validation() -> None:
    result = RealizationIds(
        same_as=((0, 1), (2,)),
        direct_types=((0, (3,)),),
        object_targets=((0, 4, (1,)),),
        data_targets=((1, 5, (6, 7)),),
        different_from=((0, 1),),
    )
    assert result.same_as == ((0, 1), (2,))
    with pytest.raises(ValueError, match="partition"):
        RealizationIds(same_as=((0, 1), (1, 2)))


def test_realization_ids_require_canonical_rows_and_group_object_targets() -> None:
    with pytest.raises(ValueError, match="object target"):
        RealizationIds(
            same_as=((0,), (1,)),
            object_targets=((0, 4, (2,)),),
        )
    with pytest.raises(ValueError, match="direct-type rows"):
        RealizationIds(
            same_as=((0,), (1,)),
            direct_types=((1, (3,)), (0, (2,))),
        )
    with pytest.raises(ValueError, match="unique by subject and property"):
        RealizationIds(
            same_as=((0,), (1,)),
            data_targets=((0, 4, (1,)), (0, 4, (2,))),
        )
    with pytest.raises(ValueError, match="different-from pairs"):
        RealizationIds(
            same_as=((0,), (1,), (2,)),
            different_from=((1, 2), (0, 1)),
        )


def test_backend_diagnostic_json_is_exact_and_sorted() -> None:
    python = BackendAvailability("python", True, "1", 1, None)
    native = BackendAvailability("native", False, None, None, "not_installed")
    status = BackendStatus(None, "python", python, native, "0.1.0", (0, 1))
    assert canonical_backend_json(status) == (
        '{"core_api_version":[0,1],"core_package_version":"0.1.0",'
        '"default_selection":"python","environment_request":null,'
        '"native":{"available":false,"implementation_version":null,'
        '"ir_schema_version":null,"name":"native","reason":"not_installed"},'
        '"python":{"available":true,"implementation_version":"1",'
        '"ir_schema_version":1,"name":"python","reason":null}}'
    )
    info = BackendInfo(
        "python",
        "0.1.0",
        1,
        "python-1",
        "0.1.0",
        (0, 1),
        1,
        (1, 0),
        1,
        frozenset({"owl2-dl"}),
        False,
    )
    assert '"complete_features":["owl2-dl"]' in canonical_backend_json(info)


def test_backend_info_recursively_freezes_compiler_handoff_and_serializes_it() -> None:
    widths = {"root_ids": 4, "scalar_bytes": 1}
    handoff: dict[str, object] = {
        "buffer_widths": widths,
        "descriptor_sha256": "ab" * 32,
        "model_schema": 1,
        "schema_name": "pyowl-core/structural-columns",
        "schema_version": 1,
    }
    info = BackendInfo(
        "native",
        "0.1.0",
        1,
        "native-1",
        "0.1.0",
        (0, 1),
        1,
        (1, 0),
        1,
        frozenset({"encoded-structural-compiler-v1"}),
        True,
        handoff,
    )
    handoff["schema_name"] = "mutated"
    widths["root_ids"] = 8

    assert info.compiler_handoff is not None
    assert info.compiler_handoff["schema_name"] == "pyowl-core/structural-columns"
    assert info.compiler_handoff["buffer_widths"] == {
        "root_ids": 4,
        "scalar_bytes": 1,
    }
    with pytest.raises(TypeError):
        info.compiler_handoff["schema_name"] = "mutated"  # type: ignore[index]
    with pytest.raises(TypeError):
        info.compiler_handoff["buffer_widths"]["root_ids"] = 8  # type: ignore[index]
    assert json.loads(canonical_backend_json(info))["compiler_handoff"] == {
        "buffer_widths": {"root_ids": 4, "scalar_bytes": 1},
        "descriptor_sha256": "ab" * 32,
        "model_schema": 1,
        "schema_name": "pyowl-core/structural-columns",
        "schema_version": 1,
    }
