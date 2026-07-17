"""Opt-in, process-isolated JSONL driver for the quarantined Java HermiT oracle."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import time
from collections.abc import Iterator
from pathlib import Path
from typing import Any, TextIO

from tools.reference._util import canonical_json, confined_path, sha256_bytes, sha256_file
from tools.reference.canonicalize import (
    canonical_boolean,
    canonical_error,
    canonical_hierarchy,
    canonical_normalization,
)

SCHEMA_VERSION = "1.0"
REFERENCE = {
    "repository": "https://github.com/phillord/hermit-reasoner.git",
    "commit": "37ec30aced32ac81ebecc5e33fad255ddefcb4c3",
    "tree": "576db18fd8152be24d577b24c99e2af0d31ceef8",
    "archive_sha256": "41e389ddaf63dcff32bd3b5e360d000c15fccb328ddc749fd8464894f9c29dd7",
    "hermit_version": "1.4.0.0-SNAPSHOT",
}
OWLAPI = {
    "version": "4.2.8",
    "distribution_sha256": "ae5eb861d74fd5d10706477d23547f4c4a5c30d8c851acdbfadf9a31d0f26d23",
}
BUILD = {
    "maven_version": "3.9.16",
    "maven_revision": "2bdd9fddda4b155ebf8000e807eb73fd829a51d5",
    "build_patch_sha256": "576fb81fec05b6adc0b22e4b5e8446e17e838624514bcf307536f7ef7651a377",
}


def _validate_request(value: Any) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise ValueError("request must be a JSON object")
    required = {"schema_version", "request_id", "operation", "input", "config", "limits"}
    if set(value) != required:
        raise ValueError(f"request keys must be exactly {sorted(required)}")
    if value["schema_version"] != SCHEMA_VERSION:
        raise ValueError("unsupported schema_version")
    if not isinstance(value["request_id"], str) or not value["request_id"]:
        raise ValueError("request_id must be a non-empty string")
    if value["operation"] not in {
        "identity",
        "consistency",
        "class_hierarchy",
        "normalization",
    }:
        raise ValueError("unsupported operation")
    input_value = value["input"]
    if not isinstance(input_value, dict) or set(input_value) != {"document", "sha256", "imports"}:
        raise ValueError("input must contain exactly document, sha256, imports")
    if not isinstance(input_value["imports"], list):
        raise ValueError("input.imports must be an array")
    for imported in input_value["imports"]:
        if not isinstance(imported, dict) or set(imported) != {
            "logical_iri",
            "document",
            "sha256",
        }:
            raise ValueError("each import must contain logical_iri, document, sha256")
    config = value["config"]
    if not isinstance(config, dict) or set(config) != {"ignore_unsupported_datatypes"}:
        raise ValueError("config must contain exactly ignore_unsupported_datatypes")
    if not isinstance(config["ignore_unsupported_datatypes"], bool):
        raise ValueError("ignore_unsupported_datatypes must be boolean")
    limits = value["limits"]
    if not isinstance(limits, dict) or set(limits) != {"timeout_seconds", "memory_mb"}:
        raise ValueError("limits must contain exactly timeout_seconds and memory_mb")
    timeout = limits["timeout_seconds"]
    memory = limits["memory_mb"]
    if not isinstance(timeout, int) or isinstance(timeout, bool) or not 1 <= timeout <= 3600:
        raise ValueError("timeout_seconds must be an integer in [1, 3600]")
    if not isinstance(memory, int) or isinstance(memory, bool) or not 128 <= memory <= 32768:
        raise ValueError("memory_mb must be an integer in [128, 32768]")
    return value


def _generator_identity(tool_root: Path) -> dict[str, Any]:
    paths = [
        tool_root / "oracle.py",
        tool_root / "canonicalize.py",
        tool_root / "java/org/oaeiml/pyhermit/reference/OracleMain.java",
        tool_root / "java/org/oaeiml/pyhermit/reference/NormalizationSerializer.java",
        tool_root / "schema/request-v1.schema.json",
        tool_root / "schema/result-v1.schema.json",
    ]
    files = {str(path.relative_to(tool_root)): sha256_file(path) for path in paths}
    aggregate = hashlib.sha256(canonical_json(files).encode("utf-8")).hexdigest()
    return {"schema_version": SCHEMA_VERSION, "sha256": aggregate, "files": files}


def _sample_rss_kb(pid: int) -> int | None:
    try:
        output = subprocess.run(
            ["ps", "-o", "rss=", "-p", str(pid)],
            check=False,
            capture_output=True,
            text=True,
            timeout=1,
        ).stdout.strip()
        return int(output) if output else None
    except (OSError, ValueError, subprocess.SubprocessError):
        return None


def _cpu_limit(timeout_seconds: int) -> Any:
    if os.name != "posix":
        return None

    def apply_limit() -> None:
        import resource

        resource.setrlimit(resource.RLIMIT_CPU, (timeout_seconds, timeout_seconds + 1))

    return apply_limit


def _resolve_inputs(request: dict[str, Any], input_root: Path) -> tuple[Path, list[dict[str, str]]]:
    input_value = request["input"]
    document = confined_path(input_root, input_value["document"])
    if not document.is_file():
        raise ValueError(f"input document is not a file: {input_value['document']}")
    actual = sha256_file(document)
    if actual != input_value["sha256"]:
        raise ValueError(f"input SHA-256 mismatch: expected {input_value['sha256']}, got {actual}")
    imports: list[dict[str, str]] = []
    for imported in input_value["imports"]:
        path = confined_path(input_root, imported["document"])
        if not path.is_file():
            raise ValueError(f"import document is not a file: {imported['document']}")
        imported_actual = sha256_file(path)
        if imported_actual != imported["sha256"]:
            raise ValueError(f"import SHA-256 mismatch for {imported['document']}")
        imports.append({"logical_iri": imported["logical_iri"], "path": str(path)})
    return document, imports


def _verify_dependency_lock(args: argparse.Namespace) -> str:
    lock = json.loads(args.classpath_lock_file.read_text())
    dependencies = args.classpath_file.read_text().strip().split(os.pathsep)
    expected = lock.get("dependencies")
    if not isinstance(expected, list) or len(expected) != len(dependencies):
        raise ValueError("dependency lock/classpath count mismatch")
    unmatched = set(dependencies)
    for entry in expected:
        relative = str(entry["path"])
        suffix = relative.removeprefix("reference-worktree/")
        candidates = [path for path in unmatched if Path(path).as_posix().endswith(suffix)]
        if len(candidates) != 1:
            raise ValueError(f"dependency lock path mismatch: {relative}")
        candidate = candidates[0]
        if sha256_file(Path(candidate)) != entry["sha256"]:
            raise ValueError(f"dependency SHA-256 mismatch: {relative}")
        unmatched.remove(candidate)
    if unmatched:
        raise ValueError(f"unlocked classpath entries: {sorted(unmatched)}")
    if lock.get("java", {}).get("sha256") != sha256_file(args.java):
        raise ValueError("Java executable does not match dependency lock")
    return sha256_file(args.classpath_lock_file)


def run_one(request: dict[str, Any], args: argparse.Namespace) -> dict[str, Any]:
    started = time.monotonic()
    input_root = args.input_root.resolve()
    document, imports = _resolve_inputs(request, input_root)
    dependency_lock_sha256 = _verify_dependency_lock(args)
    dependency_classpath = args.classpath_file.read_text().strip()
    classpath = os.pathsep.join(
        [
            str(args.oracle_classes.resolve()),
            str(args.hermit_classes.resolve()),
            dependency_classpath,
        ]
    )
    java_request = dict(request)
    java_request["_resolved_document"] = str(document)
    java_request["_resolved_imports"] = imports
    payload = (canonical_json(java_request) + "\n").encode("utf-8")
    command = [
        str(args.java.resolve()),
        f"-Xmx{request['limits']['memory_mb']}m",
        "-Dfile.encoding=UTF-8",
        "-cp",
        classpath,
        "org.oaeiml.pyhermit.reference.OracleMain",
    ]
    process = subprocess.Popen(
        command,
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        preexec_fn=_cpu_limit(request["limits"]["timeout_seconds"]),
        start_new_session=True,
    )
    assert process.stdin is not None
    process.stdin.write(payload)
    process.stdin.close()
    process.stdin = None
    deadline = started + request["limits"]["timeout_seconds"]
    peak_rss = 0
    timed_out = False
    while process.poll() is None:
        sample = _sample_rss_kb(process.pid)
        if sample is not None:
            peak_rss = max(peak_rss, sample)
        if time.monotonic() >= deadline:
            timed_out = True
            if os.name == "posix":
                os.killpg(process.pid, 9)
            else:
                process.kill()
            break
        time.sleep(0.01)
    stdout, stderr = process.communicate()
    if not peak_rss:
        try:
            import resource

            child_high_water = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
            # macOS reports bytes while Linux and the BSDs report KiB.
            peak_rss = (
                int(child_high_water / 1024) if sys.platform == "darwin" else int(child_high_water)
            )
        except (ImportError, OSError, ValueError):
            peak_rss = 0
    duration_ms = round((time.monotonic() - started) * 1000, 3)
    response: dict[str, Any] = {}
    for line in stdout.decode("utf-8", errors="replace").splitlines():
        try:
            candidate = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(candidate, dict) and candidate.get("request_id") == request["request_id"]:
            response = candidate
    stderr_text = stderr.decode("utf-8", errors="replace")
    if timed_out:
        status = "TIMEOUT"
        response = {"error_type": "OracleTimeout", "message": "oracle deadline exceeded"}
    elif "OutOfMemoryError" in stderr_text or response.get("status") == "RESOURCE_LIMIT":
        status = "RESOURCE_LIMIT"
    elif process.returncode != 0 or not response:
        status = "RESOURCE_LIMIT" if process.returncode in {-24, -9, 137, 152} else "ERROR"
        if not response:
            response = {
                "error_type": "OracleProcessError",
                "message": f"oracle exited with return code {process.returncode}",
            }
    else:
        status = str(response.get("status", "ERROR"))

    jvm = dict(response.get("jvm", {}))
    jvm["java_executable_sha256"] = sha256_file(args.java)
    build_identity = dict(BUILD)
    build_identity["classpath_sha256"] = sha256_file(args.classpath_file)
    build_identity["dependency_lock_sha256"] = dependency_lock_sha256
    result: dict[str, Any] = {
        "schema_version": SCHEMA_VERSION,
        "request_id": request["request_id"],
        "status": status,
        "identity": {
            "reference": REFERENCE,
            "jvm": jvm,
            "owlapi": OWLAPI,
            "build": build_identity,
            "config": request["config"],
            "input": {
                "document": request["input"]["document"],
                "sha256": request["input"]["sha256"],
                "imports": request["input"]["imports"],
            },
            "generator": _generator_identity(Path(__file__).resolve().parent),
        },
        "evidence": {
            "duration_ms": duration_ms,
            "peak_rss_kb": peak_rss or None,
            "stdout_sha256": sha256_bytes(stdout),
            "stderr_sha256": sha256_bytes(stderr),
            "returncode": process.returncode,
        },
    }
    if status == "LOGICAL":
        result["raw"] = {
            key: response[key] for key in ("status", "outcome", "value") if key in response
        }
        if "outcome" in response:
            result["outcome"] = response["outcome"]
        raw_value = response.get("value")
        if isinstance(raw_value, dict) and raw_value.get("kind") == "raw_hierarchy":
            raw = raw_value
            result["value"] = canonical_hierarchy(raw["nodes"], raw["edges"])
        elif (
            isinstance(raw_value, dict) and raw_value.get("kind") == "raw_structural_normalization"
        ):
            result["value"] = canonical_normalization(raw_value)
        elif "value" in response:
            result["value"] = (
                canonical_boolean(raw_value) if isinstance(raw_value, bool) else raw_value
            )
    else:
        error_type = str(response.get("error_type", "OracleError"))
        if error_type.endswith("UnparsableOntologyException"):
            message = "ontology document could not be parsed"
        else:
            message = str(response.get("message", "oracle failure")).replace(
                str(input_root), "<INPUT_ROOT>"
            )
            message = re.sub(r"@[0-9a-fA-F]+", "@<instance>", message)
            message = message.splitlines()[0]
        result["error"] = canonical_error(
            status,
            message,
            error_type=error_type,
        )
        result["raw"] = {"status": response.get("status", status), "error_type": error_type}
    return result


def _requests(stream: TextIO) -> Iterator[dict[str, Any]]:
    for line_number, line in enumerate(stream, 1):
        if not line.strip():
            continue
        try:
            yield _validate_request(json.loads(line))
        except (json.JSONDecodeError, ValueError) as error:
            raise ValueError(f"invalid request on JSONL line {line_number}: {error}") from error


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--requests", type=Path, help="default: stdin")
    parser.add_argument("--input-root", type=Path, required=True)
    parser.add_argument("--java", type=Path, required=True)
    parser.add_argument("--oracle-classes", type=Path, required=True)
    parser.add_argument("--hermit-classes", type=Path, required=True)
    parser.add_argument("--classpath-file", type=Path, required=True)
    parser.add_argument("--classpath-lock-file", type=Path, required=True)
    args = parser.parse_args()
    stream = args.requests.open() if args.requests else sys.stdin
    try:
        for request in _requests(stream):
            print(canonical_json(run_one(request, args)), flush=True)
    finally:
        if args.requests:
            stream.close()


if __name__ == "__main__":
    main()
