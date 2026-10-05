#!/usr/bin/env python3
"""Run the configured semantic suite against the installed package, not ``src/``."""

from __future__ import annotations

import argparse
import os
import subprocess
import sys
from pathlib import Path


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--backend", choices=("python", "native"), required=True)
    parser.add_argument(
        "--resource-limits-only",
        action="store_true",
        help="Run the mandatory native resource cases after installing native pyowl-core",
    )
    args = parser.parse_args()
    if args.resource_limits_only and args.backend != "native":
        parser.error("--resource-limits-only requires --backend native")
    root = Path(__file__).resolve().parents[2]
    env = os.environ.copy()
    env.pop("PYTHONPATH", None)
    env["PYTHONSAFEPATH"] = "1"
    env["PYHERMIT_BACKEND"] = args.backend
    code = (
        "from pathlib import Path; import pyhermit; "
        f"assert Path({str(root)!r}) not in Path(pyhermit.__file__).resolve().parents"
    )
    subprocess.run([sys.executable, "-c", code], check=True, cwd=root, env=env)
    targets = [
        str(root / f"tests/{suite}") for suite in ("unit", "conformance", "parity", "integration")
    ]
    if args.resource_limits_only:
        # Run separately from the original semantic matrix: these fixtures require
        # native pyowl-core, while the baseline also covers its universal fallback.
        targets = [
            str(root / target)
            for target in (
                "tests/differential/encoded_compiler/test_permanent_program_assembly.py"
                "::test_public_memory_allowance_controls_profile_compilation_without_changing_results",
                "tests/differential/encoded_compiler/test_permanent_program_assembly.py"
                "::test_public_compile_work_limit_and_deferred_identity",
                "tests/native/encoded_input/test_profile_manifest_memory.py",
                "tests/native/encoded_input/test_deferred_fingerprints.py"
                "::test_deferred_identity_retains_combined_native_resource_options",
                "tests/differential/encoded_compiler/test_native_symbol_limits.py",
            )
        ]
    pytest_code = f"""
import sys
import pyhermit

# Load pyHermiT from the installed wheel before exposing repository-only test
# support modules such as ``tools.reference`` to collection.
sys.path.insert(0, {str(root)!r})

def deny_network(event, _arguments):
    if event in {{"socket.connect", "socket.getaddrinfo", "socket.gethostbyname"}}:
        raise RuntimeError(f"installed suite attempted forbidden network access: {{event}}")

sys.addaudithook(deny_network)
import pytest
raise SystemExit(pytest.main(sys.argv[1:]))
"""
    subprocess.run(
        [
            sys.executable,
            "-c",
            pytest_code,
            "-q",
            "-p",
            "no:cacheprovider",
            *targets,
        ],
        check=True,
        cwd=root,
        env=env,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
