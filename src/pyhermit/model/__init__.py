"""Exact re-exports of pyowl-core's immutable OWL structural model.

SPDX-License-Identifier: LGPL-3.0-or-later

This module intentionally defines no classes.  Dynamic population keeps the identity
surface exhaustive as compatible pyowl-core 0.2 patch releases add constructors.
"""

from __future__ import annotations

from pyowl_core import model as _model

globals().update({name: getattr(_model, name) for name in _model.__all__})
__all__ = list(_model.__all__)
