from __future__ import annotations

import os
import subprocess
import sys

import pytest
from pyowl_core import IRI, Declaration, ObjectProperty

from pyhermit.exceptions import ReasonerInterruptedError
from pyhermit.roles import RoleBuildLimits, build_role_axiom_graph


def test_role_and_nfa_limits_fail_before_unbounded_growth() -> None:
    first = ObjectProperty(IRI("urn:test:first"))
    second = ObjectProperty(IRI("urn:test:second"))
    with pytest.raises(ValueError, match="object role limit"):
        build_role_axiom_graph(
            (Declaration(first), Declaration(second)),
            limits=RoleBuildLimits(max_object_roles=5),
        )
    with pytest.raises(ValueError, match="NFA state limit"):
        build_role_axiom_graph(
            (Declaration(first),),
            limits=RoleBuildLimits(max_nfa_states=1),
        )


def test_role_preprocessing_polls_cooperative_cancellation_between_phases() -> None:
    calls = 0

    def cancelled() -> bool:
        nonlocal calls
        calls += 1
        return calls >= 3

    axioms = tuple(
        Declaration(ObjectProperty(IRI(f"urn:test:cancel-role:{index}"))) for index in range(256)
    )
    with pytest.raises(ReasonerInterruptedError, match="role preprocessing cancelled"):
        build_role_axiom_graph(axioms, cancelled=cancelled)
    assert calls == 3


def test_roles_import_has_no_tableau_java_or_native_side_effects() -> None:
    script = """
import sys
import pyhermit.roles
for name in ('jpype', 'pyhermit._native', 'pyhermit.backends.python.state'):
    assert name not in sys.modules, name
"""
    environment = dict(os.environ)
    subprocess.run([sys.executable, "-c", script], check=True, env=environment)
