"""Backend-neutral contracts and lazy backend dispatch."""

from __future__ import annotations

from .dispatch import backend_info, select_backend_factory
from .protocol import *  # noqa: F403
from .protocol import __all__ as _protocol_exports

__all__ = [*_protocol_exports, "backend_info", "select_backend_factory"]
