"""Validate the compact source-visible context exported by an encoded native session.

SPDX-License-Identifier: LGPL-3.0-or-later

The context contains only public symbol ID/key pairs and control flags.  It deliberately
cannot represent clauses, normalized axioms, predicates, provenance, or another complete
ontology IR.
"""

from __future__ import annotations

import json
import re
from collections.abc import Container, Iterable, Iterator, Mapping, Sequence, Set
from dataclasses import dataclass
from types import MappingProxyType
from typing import Generic, NoReturn, Protocol, TypeVar, cast, overload

import pyowl_core.model as owl

from pyhermit.backends.native_mapping import CompiledResultMapper
from pyhermit.exceptions import BackendMismatchError

_HEX_256 = re.compile(r"^[0-9a-f]{64}$")
_DOMAIN_KINDS = frozenset(
    {
        "class",
        "data_property",
        "entity",
        "individual",
        "object_property",
        "source_literal",
    }
)
_BUILTIN_ENTITIES = frozenset(
    {
        owl.OWL_THING,
        owl.OWL_NOTHING,
        owl.OWL_TOP_OBJECT_PROPERTY,
        owl.OWL_BOTTOM_OBJECT_PROPERTY,
        owl.OWL_TOP_DATA_PROPERTY,
        owl.OWL_BOTTOM_DATA_PROPERTY,
        owl.RDFS_LITERAL,
        owl.XSD_STRING,
        owl.RDF_PLAIN_LITERAL,
    }
)
_T = TypeVar("_T", bound=owl.StructuralNode)


@dataclass(frozen=True, slots=True)
class NativeServiceContext:
    """Immutable source domains needed by facade services and result mapping."""

    query_scope_digest: str
    compiler_digest: str
    permanent_program_sha256: str
    source_signature: Set[owl.Entity]
    source_literals: Sequence[owl.Literal]
    deterministic_program: bool
    semantic_equality_possible: bool
    class_ids: Mapping[int, owl.Class]
    object_property_ids: Mapping[int, owl.ObjectPropertyExpression]
    data_property_ids: Mapping[int, owl.DataProperty]
    individual_ids: Mapping[int, owl.NamedIndividual]
    source_literal_ids: Mapping[int, owl.Literal]
    native_signature_bytes: Container[bytes] | None = None
    native_index_bytes: int = 0
    python_symbol_validation_rows: int = 0

    def result_mapper(self) -> CompiledResultMapper:
        factory = (
            CompiledResultMapper._from_native_domain_mappings
            if self.native_signature_bytes is not None
            else CompiledResultMapper.from_domain_mappings
        )
        return factory(
            classes=self.class_ids,
            object_properties=self.object_property_ids,
            data_properties=self.data_property_ids,
            individuals=self.individual_ids,
            source_literals=self.source_literal_ids,
        )


def decode_service_context(
    encoded: bytes,
    *,
    query_scope_digest: str,
) -> NativeServiceContext:
    """Decode one exact native context and bind every ID to a public core value."""

    if type(encoded) is not bytes:
        raise TypeError("encoded service context must be exact bytes")
    _digest(query_scope_digest, "query_scope_digest")
    try:
        root = json.loads(
            encoded.decode("utf-8", errors="strict"),
            object_pairs_hook=_reject_duplicate_keys,
        )
    except (UnicodeDecodeError, ValueError, RecursionError) as error:
        raise _mismatch(
            "native encoded service context is malformed",
            "encoded_service_context_invalid",
        ) from error
    payload = _mapping(root, "service context")
    if set(payload) != {
        "compiler_digest",
        "deterministic_program",
        "domains",
        "permanent_program_sha256",
        "schema_version",
        "semantic_equality_possible",
    }:
        _fail(
            "native encoded service context has an incompatible shape",
            "encoded_service_context_invalid",
        )
    if _integer(payload["schema_version"], "service context schema") != 3:
        _fail(
            "native encoded service context schema is unsupported",
            "encoded_service_context_schema",
        )
    compiler_digest = _text(payload["compiler_digest"], "compiler digest")
    _digest(compiler_digest, "compiler_digest")
    program_digest = _text(payload["permanent_program_sha256"], "program digest")
    _digest(program_digest, "permanent_program_sha256")
    deterministic = _boolean(payload["deterministic_program"], "deterministic_program")
    equality = _boolean(
        payload["semantic_equality_possible"],
        "semantic_equality_possible",
    )
    domains: dict[str, Mapping[int, bytes]] = {}
    for raw_domain in _list(payload["domains"], "service domains"):
        domain = _mapping(raw_domain, "service domain")
        if set(domain) != {"kind", "values"}:
            _fail(
                "native encoded service domain has an incompatible shape",
                "encoded_service_context_invalid",
            )
        kind = _text(domain["kind"], "service domain kind")
        if kind not in _DOMAIN_KINDS or kind in domains:
            _fail(
                "native encoded service domains are missing, duplicate, or unknown",
                "encoded_service_context_invalid",
            )
        rows: dict[int, bytes] = {}
        previous = -1
        observed_keys: set[bytes] = set()
        for raw_value in _list(domain["values"], f"{kind} values"):
            value = _mapping(raw_value, f"{kind} value")
            if set(value) != {"identifier", "key_hex"}:
                _fail(
                    "native encoded service symbol has an incompatible shape",
                    "encoded_service_context_invalid",
                )
            identifier = _integer(value["identifier"], f"{kind} identifier")
            if not 0 <= identifier <= (1 << 32) - 1 or identifier <= previous:
                _fail(
                    "native encoded service symbol IDs are not canonical",
                    "encoded_service_context_invalid",
                )
            key = _hex_bytes(_text(value["key_hex"], f"{kind} key"), f"{kind} key")
            if key in observed_keys:
                _fail(
                    "native encoded service symbol keys are not unique",
                    "encoded_service_context_invalid",
                )
            rows[identifier] = key
            observed_keys.add(key)
            previous = identifier
        domains[kind] = MappingProxyType(rows)
    if frozenset(domains) != _DOMAIN_KINDS:
        _fail(
            "native encoded service domains are incomplete",
            "encoded_service_context_invalid",
        )

    source_signature = frozenset(
        (*_decode_entities(domains["entity"]).values(), *_BUILTIN_ENTITIES)
    )
    classes = _bind_domain(
        domains["class"],
        (value for value in source_signature if isinstance(value, owl.Class)),
        "class",
    )
    named_object_properties = frozenset(
        value
        for value in source_signature
        if isinstance(value, owl.ObjectProperty)
        and value not in (owl.OWL_TOP_OBJECT_PROPERTY, owl.OWL_BOTTOM_OBJECT_PROPERTY)
    )
    object_properties = _bind_domain(
        domains["object_property"],
        (
            owl.OWL_TOP_OBJECT_PROPERTY,
            owl.OWL_BOTTOM_OBJECT_PROPERTY,
            *named_object_properties,
            *(owl.inverse_property(value) for value in named_object_properties),
        ),
        "object property",
    )
    data_properties = _bind_domain(
        domains["data_property"],
        (value for value in source_signature if isinstance(value, owl.DataProperty)),
        "data property",
    )
    individuals = _bind_domain(
        domains["individual"],
        (value for value in source_signature if isinstance(value, owl.NamedIndividual)),
        "named individual",
    )
    source_literals = _decode_literals(domains["source_literal"])
    return NativeServiceContext(
        query_scope_digest,
        compiler_digest,
        program_digest,
        source_signature,
        tuple(source_literals.values()),
        deterministic,
        equality,
        classes,
        object_properties,
        data_properties,
        individuals,
        source_literals,
        python_symbol_validation_rows=sum(len(rows) for rows in domains.values()),
    )


def _bind_domain(
    rows: Mapping[int, bytes],
    values: Iterable[_T],
    label: str,
) -> Mapping[int, _T]:
    by_key = {value.canonical_bytes(): value for value in values}
    result: dict[int, _T] = {}
    for identifier, key in rows.items():
        value = by_key.get(key)
        if value is None:
            _fail(
                f"native encoded {label} key is absent from the retained core signature",
                "encoded_service_symbol_missing",
            )
        result[identifier] = value
    if frozenset(rows.values()) != frozenset(by_key):
        _fail(
            f"native encoded {label} domain differs from the retained core signature",
            "encoded_service_domain_mismatch",
        )
    return MappingProxyType(result)


def _decode_entities(rows: Mapping[int, bytes]) -> Mapping[int, owl.Entity]:
    values: dict[int, owl.Entity] = {}
    for identifier, encoded in rows.items():
        try:
            decoded = owl.decode_canonical(encoded)
        except (TypeError, ValueError) as error:
            raise _mismatch(
                "native encoded source-entity key is malformed",
                "encoded_service_symbol_invalid",
            ) from error
        if not isinstance(decoded, owl.Entity) or decoded.canonical_bytes() != encoded:
            _fail(
                "native encoded source-entity key is not a canonical entity",
                "encoded_service_symbol_invalid",
            )
        values[identifier] = decoded
    return MappingProxyType(values)


def _decode_literals(rows: Mapping[int, bytes]) -> Mapping[int, owl.Literal]:
    values: dict[int, owl.Literal] = {}
    for identifier, encoded in rows.items():
        try:
            decoded = owl.decode_canonical(encoded)
        except (TypeError, ValueError) as error:
            raise _mismatch(
                "native encoded source-literal key is malformed",
                "encoded_service_symbol_invalid",
            ) from error
        if not isinstance(decoded, owl.Literal) or decoded.canonical_bytes() != encoded:
            _fail(
                "native encoded source-literal key is not a canonical literal",
                "encoded_service_symbol_invalid",
            )
        values[identifier] = decoded
    return MappingProxyType(values)


def _reject_duplicate_keys(pairs: list[tuple[str, object]]) -> dict[str, object]:
    values: dict[str, object] = {}
    for key, value in pairs:
        if key in values:
            raise ValueError(f"duplicate JSON object key: {key}")
        values[key] = value
    return values


def _mapping(value: object, label: str) -> dict[str, object]:
    if type(value) is not dict:
        _fail(f"native encoded {label} must be an object", "encoded_service_context_invalid")
    return cast(dict[str, object], value)


def _list(value: object, label: str) -> list[object]:
    if type(value) is not list:
        _fail(f"native encoded {label} must be a list", "encoded_service_context_invalid")
    return cast(list[object], value)


def _text(value: object, label: str) -> str:
    if type(value) is not str or not value:
        _fail(
            f"native encoded {label} must be a nonempty string",
            "encoded_service_context_invalid",
        )
    return value


def _integer(value: object, label: str) -> int:
    if type(value) is not int:
        _fail(f"native encoded {label} must be an integer", "encoded_service_context_invalid")
    return value


def _boolean(value: object, label: str) -> bool:
    if type(value) is not bool:
        _fail(f"native encoded {label} must be a boolean", "encoded_service_context_invalid")
    return value


def _hex_bytes(value: str, label: str) -> bytes:
    if len(value) % 2:
        _fail(f"native encoded {label} is not hexadecimal", "encoded_service_context_invalid")
    try:
        decoded = bytes.fromhex(value)
    except ValueError as error:
        raise _mismatch(
            f"native encoded {label} is not hexadecimal",
            "encoded_service_context_invalid",
        ) from error
    if decoded.hex() != value:
        _fail(
            f"native encoded {label} is not canonical hexadecimal",
            "encoded_service_context_invalid",
        )
    return decoded


def _digest(value: str, label: str) -> None:
    if _HEX_256.fullmatch(value) is None:
        raise ValueError(f"{label} must be a lowercase SHA-256 digest")


def _mismatch(message: str, reason: str) -> BackendMismatchError:
    return BackendMismatchError(message, context={"reason": reason})


def _fail(message: str, reason: str) -> NoReturn:
    raise _mismatch(message, reason)


__all__ = ["NativeServiceContext", "decode_service_context"]


class _NativeSymbols(Protocol):
    def metadata(self) -> tuple[str, str, bool, bool, int]: ...
    def count(self, domain: str) -> int: ...
    def ids(self, domain: str) -> list[int]: ...
    def id_at(self, domain: str, offset: int) -> int | None: ...
    def find(self, domain: str, key: bytes) -> int | None: ...
    def key(self, domain: str, identifier: int) -> bytes | None: ...


class _NativeDomainMapping(Mapping[int, _T], Generic[_T]):
    """Read-only domain backed by an opaque native owner, without a Python mirror."""

    __slots__ = ("_domain", "_owner")

    def __init__(self, owner: _NativeSymbols, domain: str) -> None:
        self._owner = owner
        self._domain = domain

    def __len__(self) -> int:
        return self._owner.count(self._domain)

    def __iter__(self) -> Iterator[int]:
        return iter(self._owner.ids(self._domain))

    def __getitem__(self, identifier: int) -> _T:
        if (
            isinstance(identifier, bool)
            or not isinstance(identifier, int)
            or not 0 <= identifier <= 0xFFFFFFFF
        ):
            raise KeyError(identifier)
        key = self._owner.key(self._domain, identifier)
        if key is None:
            raise KeyError(identifier)
        # The native constructor validates identities. This creates the requested
        # public result object and does not scan or revalidate the source domain.
        return cast(_T, owl.decode_canonical(key))

    def native_id(self, value: owl.StructuralNode) -> int:
        identifier = self._owner.find(self._domain, value.canonical_bytes())
        if identifier is None:
            raise ValueError(f"{self._domain} is not retained by this compiled runtime")
        return identifier


class _NativeSignature(Set[owl.Entity]):
    __slots__ = ("_entities", "_owner")

    def __init__(self, owner: _NativeSymbols) -> None:
        self._owner = owner
        self._entities = _NativeDomainMapping[owl.Entity](owner, "entity")

    def __contains__(self, value: object) -> bool:
        return isinstance(value, owl.Entity) and (
            value in _BUILTIN_ENTITIES
            or self._owner.find("entity", value.canonical_bytes()) is not None
        )

    def __iter__(self) -> Iterator[owl.Entity]:
        yield from self._entities.values()
        for value in _BUILTIN_ENTITIES:
            if self._owner.find("entity", value.canonical_bytes()) is None:
                yield value

    def __len__(self) -> int:
        return len(self._entities) + sum(
            self._owner.find("entity", value.canonical_bytes()) is None
            for value in _BUILTIN_ENTITIES
        )


class _NativeSignatureBytes(Container[bytes]):
    def __init__(self, owner: _NativeSymbols) -> None:
        self._owner = owner
        self._builtins = frozenset(value.canonical_bytes() for value in _BUILTIN_ENTITIES)

    def __contains__(self, value: object) -> bool:
        return isinstance(value, bytes) and (
            value in self._builtins or self._owner.find("entity", value) is not None
        )


class _NativeLiterals(Sequence[owl.Literal]):
    def __init__(self, values: _NativeDomainMapping[owl.Literal]) -> None:
        self._values = values

    def __len__(self) -> int:
        return len(self._values)

    @overload
    def __getitem__(self, index: int) -> owl.Literal: ...
    @overload
    def __getitem__(self, index: slice) -> Sequence[owl.Literal]: ...
    def __getitem__(self, index: int | slice) -> owl.Literal | Sequence[owl.Literal]:
        if isinstance(index, slice):
            return tuple(self[offset] for offset in range(*index.indices(len(self))))
        if index < 0:
            index += len(self)
        if index < 0:
            raise IndexError(index)
        identifier = self._values._owner.id_at("source_literal", index)
        if identifier is None:
            raise IndexError(index)
        return self._values[identifier]

    def __iter__(self) -> Iterator[owl.Literal]:
        return iter(self._values.values())


def native_service_context(owner: object, *, query_scope_digest: str) -> NativeServiceContext:
    """Accept only an unforgeable extension object that owns validated symbol indexes."""
    from pyhermit import _native

    if type(owner) is not getattr(_native, "_NativeServiceSymbols", None):
        raise _mismatch("native symbol owner has the wrong type", "encoded_service_context_invalid")
    symbols = cast(_NativeSymbols, owner)
    compiler, program, deterministic, equality, _bytes = symbols.metadata()
    literals = _NativeDomainMapping[owl.Literal](symbols, "source_literal")
    return NativeServiceContext(
        query_scope_digest,
        compiler,
        program,
        _NativeSignature(symbols),
        _NativeLiterals(literals),
        deterministic,
        equality,
        _NativeDomainMapping[owl.Class](symbols, "class"),
        _NativeDomainMapping[owl.ObjectPropertyExpression](symbols, "object_property"),
        _NativeDomainMapping[owl.DataProperty](symbols, "data_property"),
        _NativeDomainMapping[owl.NamedIndividual](symbols, "individual"),
        literals,
        _NativeSignatureBytes(symbols),
        _bytes,
    )
