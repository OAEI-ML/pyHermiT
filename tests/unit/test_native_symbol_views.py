"""Native metadata views do bounded lookup and construct only requested objects."""

# SPDX-License-Identifier: LGPL-3.0-or-later
from __future__ import annotations

import pyowl_core.model as owl
import pytest

from pyhermit.backends.native_context import (
    _NativeDomainMapping,
    _NativeSignature,
    _NativeSignatureBytes,
)
from pyhermit.backends.native_mapping import CompiledResultMapper


class Symbols:
    def __init__(self) -> None:
        self.entity = owl.Class(owl.IRI("urn:class:A"))
        self.lookups: list[tuple[str, int]] = []
        self.iterations = 0

    def metadata(self) -> tuple[str, str, bool, bool, int]:
        return "1" * 64, "2" * 64, True, False, 100

    def count(self, domain: str) -> int:
        return 1 if domain in {"class", "entity"} else 0

    def ids(self, domain: str) -> list[int]:
        self.iterations += 1
        return [3] if self.count(domain) else []

    def id_at(self, domain: str, offset: int) -> int | None:
        return 3 if self.count(domain) and offset == 0 else None

    def find(self, domain: str, key: bytes) -> int | None:
        return 3 if self.count(domain) and key == self.entity.canonical_bytes() else None

    def key(self, domain: str, identifier: int) -> bytes | None:
        self.lookups.append((domain, identifier))
        return self.entity.canonical_bytes() if self.count(domain) and identifier == 3 else None


def test_mapping_creation_and_reverse_lookup_do_not_enumerate_domains() -> None:
    owner = Symbols()
    classes = _NativeDomainMapping[owl.Class](owner, "class")
    assert owner.iterations == 0
    assert classes.native_id(owner.entity) == 3
    assert owner.lookups == []
    assert classes[3] == owner.entity
    assert owner.lookups == [("class", 3)]
    assert owner.iterations == 0
    with pytest.raises(KeyError):
        classes[2]
    with pytest.raises(ValueError):
        classes.native_id(owl.Class(owl.IRI("urn:unknown")))


def test_signature_membership_and_witness_collision_lookup_are_native() -> None:
    owner = Symbols()
    signature = _NativeSignature(owner)
    reserved = _NativeSignatureBytes(owner)
    assert owner.entity in signature
    assert owl.OWL_THING in signature
    assert owner.entity.canonical_bytes() in reserved
    assert owl.OWL_THING.canonical_bytes() in reserved
    assert b"unknown" not in reserved
    assert owner.iterations == 0
    assert owner.lookups == []
    assert set(signature) >= {owner.entity, owl.OWL_THING, owl.OWL_NOTHING}
    assert owner.iterations == 1


def test_mapper_retains_native_views_without_copying_or_scanning() -> None:
    owner = Symbols()
    classes = _NativeDomainMapping[owl.Class](owner, "class")
    mapper = CompiledResultMapper._from_native_domain_mappings(
        classes=classes,
        object_properties=_NativeDomainMapping(owner, "object_property"),
        data_properties=_NativeDomainMapping(owner, "data_property"),
        individuals=_NativeDomainMapping(owner, "individual"),
        source_literals=_NativeDomainMapping(owner, "source_literal"),
    )
    assert mapper.class_ids is classes
    assert mapper.class_id(owner.entity) == 3
    assert owner.iterations == 0
    assert owner.lookups == []
