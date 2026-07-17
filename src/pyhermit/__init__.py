"""Foundation marker for the future pyHermiT public API.

WP00 intentionally exports no reasoner, ontology model, parser, or backend. Public OWL
values and reasoning services are introduced only by their dependency-ordered work
packages.
"""

from __future__ import annotations

__version__ = "0.1.0.dev0"

__all__ = ["__version__"]
