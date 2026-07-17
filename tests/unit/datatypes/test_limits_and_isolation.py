from __future__ import annotations

import ast
import json
import os
import subprocess
import sys
from pathlib import Path

import pytest
from pyowl_core.model import IRI, Datatype, Literal

from pyhermit.datatypes import (
    XSD_DECIMAL,
    XSD_INTEGER,
    DatatypeLimits,
    LexicalCompatibility,
    NumericIdentity,
    compile_literal,
)
from pyhermit.events import CancellationSource
from pyhermit.exceptions import ReasonerInterruptedError, ResourceLimitError

_ROOT = Path(__file__).parents[3]
_SOURCE = _ROOT / "src" / "pyhermit" / "datatypes"


def literal(lexical: str, datatype_iri: str) -> Literal:
    return Literal(lexical, Datatype(IRI(datatype_iri)))


def test_large_arbitrary_precision_integer_ignores_python_decimal_digit_cap() -> None:
    digits = "9" * 10_000
    cancellation = CancellationSource()
    compiled = compile_literal(
        literal(digits, XSD_INTEGER),
        limits=DatatypeLimits(max_numeric_digits=10_000, cancellation_poll_stride=1),
        cancellation=cancellation.token,
    )
    assert isinstance(compiled.data_identity, NumericIdentity)
    assert compiled.data_identity.denominator == 1
    assert compiled.data_identity.numerator.bit_length() > 33_000
    assert cancellation.token.work > 1_000
    # Language-neutral serialization uses an exact hexadecimal token and therefore
    # also remains independent of Python 3.11+'s int-to-decimal safety limit.
    encoded = json.dumps(compiled.as_tagged(), sort_keys=True)
    assert "numeric-rational-hex-v1" in encoded


def test_lexical_digit_scale_and_exponent_limits_fail_before_unbounded_work() -> None:
    with pytest.raises(ResourceLimitError) as characters:
        compile_literal(
            literal("1" * 11, XSD_INTEGER),
            limits=DatatypeLimits(max_lexical_characters=10),
        )
    assert characters.value.limit == "max_lexical_characters"

    with pytest.raises(ResourceLimitError) as digits:
        compile_literal(
            literal("1" * 11, XSD_INTEGER),
            limits=DatatypeLimits(max_lexical_characters=20, max_numeric_digits=10),
        )
    assert digits.value.limit == "max_numeric_digits"

    with pytest.raises(ResourceLimitError) as exponent:
        compile_literal(
            literal("1E101", XSD_DECIMAL),
            compatibility=LexicalCompatibility.HERMIT_1_4,
            limits=DatatypeLimits(max_decimal_exponent=100),
        )
    assert exponent.value.limit == "max_decimal_exponent"

    with pytest.raises(ResourceLimitError) as scale:
        compile_literal(
            literal("0." + "1" * 101, XSD_DECIMAL),
            limits=DatatypeLimits(max_decimal_exponent=100),
        )
    assert scale.value.limit == "max_decimal_exponent"


def test_compile_observes_shared_cancellation_token_at_operation_boundary() -> None:
    source = CancellationSource()
    source.interrupt("datatype test cancellation")
    with pytest.raises(ReasonerInterruptedError, match="datatype test cancellation"):
        compile_literal(literal("123", XSD_INTEGER), cancellation=source.token)


def test_datatype_import_loads_no_java_native_tableau_or_parser_runtime() -> None:
    script = """
import sys
import pyhermit.datatypes
for name in (
    'jpype', 'java', 'rdflib', 'pyhermit._native',
    'pyhermit.backends.python.state', 'pyhermit.backends.python.tableau'
):
    assert name not in sys.modules, name
"""
    environment = dict(os.environ)
    roots = [str(_ROOT / "src"), str(_ROOT.parent / "pyOWLCore" / "src")]
    environment["PYTHONPATH"] = os.pathsep.join(roots)
    subprocess.run([sys.executable, "-c", script], check=True, env=environment)


def test_datatype_sources_have_no_forbidden_runtime_import_edges() -> None:
    forbidden = {"java", "jpype", "rdflib", "pyhermit._native"}
    for path in sorted(_SOURCE.glob("*.py")):
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        imported: set[str] = set()
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                imported.update(alias.name for alias in node.names)
            elif isinstance(node, ast.ImportFrom) and node.module is not None:
                imported.add(node.module)
        assert not any(
            name in forbidden
            or name.startswith("pyhermit.backends")
            or name.startswith("pyhermit.clauses")
            or name.startswith("pyhermit.normalize")
            for name in imported
        ), path


def test_numeric_results_are_hash_seed_locale_and_timezone_independent() -> None:
    script = """
import json
from pyowl_core.model import Datatype, IRI, Literal
from pyhermit.datatypes import OWL_RATIONAL, XSD_DECIMAL, compile_literal
def lit(text, iri):
    return Literal(text, Datatype(IRI(iri)))
values = [
    compile_literal(lit('-001.2500', XSD_DECIMAL)).as_tagged(),
    compile_literal(lit('-5/4', OWL_RATIONAL)).as_tagged(),
]
print(json.dumps(values, sort_keys=True, separators=(',', ':')))
"""
    roots = [str(_ROOT / "src"), str(_ROOT.parent / "pyOWLCore" / "src")]
    outputs = []
    for seed, timezone in (("1", "UTC"), ("987654", "Pacific/Honolulu")):
        environment = dict(os.environ)
        environment.update(
            {
                "LC_ALL": "C",
                "PYTHONHASHSEED": seed,
                "PYTHONPATH": os.pathsep.join(roots),
                "TZ": timezone,
            }
        )
        outputs.append(
            subprocess.run(
                [sys.executable, "-c", script],
                check=True,
                capture_output=True,
                env=environment,
                text=True,
            ).stdout
        )
    assert outputs[0] == outputs[1]
