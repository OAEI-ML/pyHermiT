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
    args = parser.parse_args()
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
            str(root / "tests/unit"),
            str(root / "tests/conformance"),
            str(root / "tests/parity"),
            str(root / "tests/integration"),
        ],
        check=True,
        cwd=root,
        env=env,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
