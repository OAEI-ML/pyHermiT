# Release benchmark harness

`run_release.py` is the WP17 phase probe for the project-generated taxonomy family. It
forces one backend, retains the exact core snapshot by identity, records raw phase
samples, Python allocation peak and process peak RSS where available, and refuses to
combine samples whose canonical result digest differs.

```shell
PYTHONPATH=src:../pyOWLCore/src python benchmarks/run_release.py \
  --backend python --size small --samples 3 --output /tmp/python-small.json
PYTHONPATH=src:../pyOWLCore/src python benchmarks/run_release.py \
  --backend native --size small --samples 3 --output /tmp/native-small.json
```

The output conforms to `schema/release-result-v1.schema.json`. A local result is always
`informational-local`; this schema deliberately has no accepted-release status. Timeout,
resource-limit, interruption, and other failures are emitted as structured outcomes with
partial phase samples and a null result hash rather than omitted. A dedicated runner must
use a separately reviewed acceptance schema, record its machine image, invoke cold processes as required by
`../specs/performance.md`, validate identical result hashes, and commit an approved
baseline before `targets.toml` can change from
`provisional-awaiting-dedicated-calibration` to `frozen`.

The medium and large points are scale probes, not timeout-skipped tests. Resource and
timeout failures must be retained as results by the dedicated orchestration lane.
