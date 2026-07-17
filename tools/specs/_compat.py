"""Small compatibility helpers shared by WP00 validation tools."""

from __future__ import annotations

import sys
from importlib import import_module
from pathlib import Path
from typing import Any, BinaryIO, Protocol, cast


class _TomlModule(Protocol):
    def load(self, stream: BinaryIO, /) -> dict[str, Any]: ...


_toml = cast(
    _TomlModule,
    import_module("tomllib" if sys.version_info >= (3, 11) else "tomli"),
)


def repository_root() -> Path:
    """Return the checkout root independently of the current working directory."""

    return Path(__file__).resolve().parents[2]


def load_toml(path: Path) -> dict[str, Any]:
    """Load one UTF-8 TOML document with the Python 3.10 compatibility dependency."""

    with path.open("rb") as stream:
        return _toml.load(stream)


def require_mapping(value: object, context: str) -> dict[str, Any]:
    if not isinstance(value, dict) or any(not isinstance(key, str) for key in value):
        raise ValueError(f"{context} must be a TOML table")
    return cast(dict[str, Any], value)


def require_list(value: object, context: str) -> list[Any]:
    if not isinstance(value, list):
        raise ValueError(f"{context} must be a TOML array")
    return value


def require_str(value: object, context: str) -> str:
    if not isinstance(value, str) or not value:
        raise ValueError(f"{context} must be a nonempty string")
    return value


def require_int(value: object, context: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise ValueError(f"{context} must be an integer")
    return value


def require_bool(value: object, context: str) -> bool:
    if not isinstance(value, bool):
        raise ValueError(f"{context} must be a boolean")
    return value
