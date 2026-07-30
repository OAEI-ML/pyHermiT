# LIC-001 local artifact audit

Audit date: 2026-07-18

Status: **local repository-owned artifact audit complete; owner/legal and hosted release gates
pending**.

## Audited artifact set

The artifacts were built from the current tree on macOS 14 x86-64 with CPython 3.12,
`SOURCE_DATE_EPOCH=946684800`, and the repository's locked Rust dependencies. This is a local
engineering audit, not legal advice or permission to publish.

| Artifact | Shape | Bytes | Archive SHA-256 |
| --- | --- | ---: | --- |
| `pyhermit-0.1.0.dev0-py3-none-any.whl` | pure Python, 99 members | 378,157 | `74d814d3eef1347aa1d856d437ff8b6f78963fea405a6c303f7fa726d12ad783` |
| `pyhermit-0.1.0.dev0-cp310-abi3-macosx_14_0_x86_64.whl` | native, 100 members | 2,100,169 | `11968747fcb4c4868906641f6482d41e595fbc70f80a4188b70d78563b69dfd0` |
| `pyhermit-0.1.0.dev0.tar.gz` | source, 342 members | recorded externally | recorded externally |

## Checks

The existing fail-closed inspector in `tools/packaging_probe/check_artifact.py` was applied to
the universal wheel, forced-native `cp310-abi3` wheel, and sdist. It verifies safe bounded
archive paths, project/version/Python metadata, exact runtime dependency boundaries, license
metadata and payloads, truthful wheel tags, complete `RECORD` hashes, pure/native payload
identity, one allowlisted native extension, the complete source/evidence sdist layout, absence
of absolute build paths, and absence of Java/JVM/reference/probe material.

All local inspector invocations exited successfully. The sdist was reported as Java-free,
probe-excluded, and complete for the required Python, Rust, licensing, specification, and
LIC-001 evidence sources. Wheel comparison found identical project metadata, 92 Python payload
hashes, and license payload hashes, with only `pyhermit/_native.abi3.so` added by the native
wheel. The common metadata SHA-256 was
`a047aa332688a1342b8468ad24b7b67ee094f250459ef739414b28c829c7e7ba`.

| License payload | SHA-256 in both wheels and the sdist |
| --- | --- |
| `LICENSE` | `e3a994d82e644b03a792a930f574002658412f62407f5fee083f2555c5f23118` |
| `COPYING` | `3972dc9744f6499f0f9b2dbf76696f2ae7ad8af9b23dde66d6af86c9dfb36986` |
| `NOTICE.md` | `cc870e2162df6a26938fbed059df2f53274d4e5f2fcf5af85fbd9ed0ff0c1da0` |

The source-archive digest is not embedded inside its own archive. A final immutable release
must publish that digest through the external provenance attestation described in
`reports/README.md`.

## Exclusions and release status

This local audit does not claim results for the eight hosted platform/architecture targets,
sanitizers, registry trusted publishing, signatures, external attestation, or legal review.
No upload action or package-index permission is enabled while LIC-001 is open. The only LIC-001
requirement remaining after these repository-owned audits is
`owner-legal-review-signoff`; consequently `gate_status` remains `open` and
`publish_allowed` remains `false`.

## Reproduction

```text
PYHERMIT_BUILD_NATIVE=0 SOURCE_DATE_EPOCH=946684800 python -m build \
  --no-isolation --wheel --sdist --outdir DIST
PYHERMIT_BUILD_NATIVE=1 SOURCE_DATE_EPOCH=946684800 python -m build \
  --no-isolation --wheel --outdir DIST
PYTHONPATH=. python -m tools.packaging_probe.check_artifact DIST/*.tar.gz
PYTHONPATH=. python -m tools.packaging_probe.check_artifact --compare \
  DIST/*-py3-none-any.whl DIST/*-cp310-abi3-*.whl
PYTHONPATH=. python -m tools.specs.check_release_gate --assert-blocked
```
