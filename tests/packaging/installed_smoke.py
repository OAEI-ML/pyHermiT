#!/usr/bin/env python3
"""Exercise standalone, shared-view, and provider inputs from an installed artifact."""

from __future__ import annotations

import argparse
import os
import shutil
import sys
from pathlib import Path


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--expected-backend", choices=("python", "native"), required=True)
    parser.add_argument(
        "--expected-core-backend",
        choices=("python", "native", "either"),
        default="either",
    )
    args = parser.parse_args()

    os.environ["PATH"] = str(Path(sys.executable).resolve().parent)
    assert all(
        shutil.which(command) is None
        for command in ("java", "javac", "cargo", "rustc", "cc", "gcc", "clang")
    )
    os.environ["PYHERMIT_BACKEND"] = args.expected_backend

    def deny_network(event: str, _arguments: tuple[object, ...]) -> None:
        if event in {"socket.connect", "socket.getaddrinfo", "socket.gethostbyname"}:
            raise RuntimeError(f"installed smoke attempted forbidden network access: {event}")

    sys.addaudithook(deny_network)

    before = set(sys.modules)
    import pyowl_core as owl

    import pyhermit

    assert owl.__version__ == "0.1.1", owl.__version__
    added = set(sys.modules) - before
    assert not added.intersection({"jpype", "jnius", "javabridge", "owlready2"})
    source_root = Path(__file__).resolve().parents[2]
    installed_root = Path(pyhermit.__file__).resolve()
    assert source_root not in installed_root.parents, (
        f"imported source checkout instead of installed artifact: {installed_root}"
    )

    status = pyhermit.backend_info()
    if args.expected_backend == "native":
        assert status.native.available is True, status
        assert status.native.implementation_version == pyhermit.__version__, status
    config = pyhermit.ReasonerConfig(backend=pyhermit.BackendName(args.expected_backend))
    payload = (
        b"Prefix(:=<urn:installed#>) Ontology(<urn:installed> "
        b"Declaration(Class(:A)) Declaration(Class(:B)) SubClassOf(:A :B))"
    )
    core_preference = {
        "either": owl.BackendPreference.AUTO,
        "native": owl.BackendPreference.NATIVE,
        "python": owl.BackendPreference.PYTHON,
    }[args.expected_core_backend]
    options = owl.LoadOptions(
        format=owl.DocumentFormat.FUNCTIONAL,
        imports=owl.ImportPolicy.IGNORE,
        backend=core_preference,
    )
    snapshot = owl.load_snapshot(payload, options=options)
    if args.expected_core_backend != "either":
        assert snapshot.capabilities.backend == args.expected_core_backend

    class Provider:
        def __init__(self) -> None:
            self.calls = 0

        def owl_snapshot(self) -> owl.OntologyView:
            self.calls += 1
            return snapshot

    provider = Provider()
    outcomes = []
    for source, load_options in ((payload, options), (snapshot, None), (provider, None)):
        with pyhermit.Reasoner(source, config=config, load_options=load_options) as reasoner:
            assert reasoner.backend.name == args.expected_backend
            outcomes.append((reasoner.is_consistent(), reasoner.class_hierarchy()))
    assert provider.calls == 1
    assert outcomes[0] == outcomes[1] == outcomes[2]
    print(
        f"installed smoke passed: backend={args.expected_backend} "
        f"core={owl.__version__} python={sys.version_info.major}.{sys.version_info.minor}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
