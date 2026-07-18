# Accepted baselines

This directory intentionally contains no accepted performance baseline yet. A baseline
is valid only when produced on the recorded dedicated machine/VM, with all raw process
samples, result hashes, peak RSS, exact artifacts/configuration, and the Java comparison
manifest required by `../../specs/performance.md`.

Local smoke JSON belongs under `../evidence/` and must retain
`"status": "informational-local"`. The empty calibration identity in
`../targets.toml` keeps the performance release gate blocked.
