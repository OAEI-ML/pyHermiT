# HermiT reference oracle (development only)

This directory defines the exact, quarantined Java oracle used to establish behavioral
evidence for the Java-free pyHermiT implementation. It is not imported by `pyhermit`, is not
included in wheels or sdists, performs no work at import time, and is never part of the
ordinary test run. The installed product remains Java-free.

`manifest.toml` is authoritative for the source, tree, archive, toolchain, OWLAPI, corpus, and
historical-report identities. External source and ontology bodies are fetch-only under
`.reference/`; only derived metadata and results over small project-authored inputs are
committed.

## Explicit workflow

All commands are opt-in. Acquisition is the only stage that can clone source, and Maven is
offline unless `--allow-network` is supplied deliberately.

```console
python -m tools.reference.acquire \
  --destination .reference/hermit-37ec30a \
  --archive .reference/hermit-37ec30a.tar \
  --allow-network

python -m tools.reference.build_oracle \
  --source .reference/hermit-37ec30a \
  --worktree .reference/hermit-build-37ec30a \
  --maven-repo .reference/m2 \
  --classpath-file .reference/oracle-classpath.txt \
  --lock-file .reference/oracle-classpath.lock.candidate.json \
  --oracle-classes .reference/oracle/classes \
  --patch tools/reference/patches/skip-buildnumber.patch \
  --java-source tools/reference/java/org/oaeiml/pyhermit/reference/OracleMain.java \
  --java-home /path/to/pinned-jdk-11 \
  --maven /path/to/pinned-maven/bin/mvn \
  --allow-network
```

The build patch removes only an obsolete SVN build-number plugin whose HTTP-era dependency
resolution fails today. `build_oracle.py` verifies the exact reference commit, applies the
hash-pinned patch to a detached worktree, captures a content-hashed dependency lock, compiles
outside distributable paths, and requires an explicit JDK/Maven location.

Run the four reviewed requests (one Java subprocess per request, with timeout and heap cap):

```console
python -m tools.reference.oracle \
  --requests tests/data/reference/requests-v1.jsonl \
  --input-root tests/data/reference/inputs \
  --java /path/to/pinned-jdk-11/bin/java \
  --oracle-classes .reference/oracle/classes \
  --hermit-classes .reference/hermit-build-37ec30a/target/classes \
  --classpath-file .reference/oracle-classpath.txt \
  --classpath-lock-file tools/reference/dependencies.lock.json \
  > .reference/candidate-results.jsonl

python -m tools.reference.goldens \
  tests/data/reference/goldens-v1.jsonl \
  .reference/candidate-results.jsonl
```

The final command compares only the deterministic semantic projection and never overwrites a
committed golden. Full live records still carry reference, JVM, OWLAPI, configuration, input,
generator, duration, sampled peak RSS, exit status, and stdout/stderr identities.

## W3C executor and inventories

`w3c_manifest.py` independently reads the public RDF vocabulary in the pinned export. It
selects Approved + DIRECT + DL cases, verifies the source hash and 266/350 counts, and can
materialize a requested check in memory for a temporary run. Its `execute_checks` entry point
runs all or selected checks through a backend-neutral callback and records PASS/FAIL/ERROR per
check. It does not use or copy the upstream Java harness. Positive/negative entailment checks
are inventoried now and can use the same executor when the corresponding pyHermiT service work
package lands.

Regenerate inventories into a temporary file and review/diff them; do not overwrite committed
files blindly:

```console
python -m tools.reference.inventory \
  --reference-root .reference/hermit-37ec30a \
  --output .reference/upstream-test-inventory.candidate.json
python -m tools.reference.w3c_manifest \
  .reference/hermit-37ec30a/src/test/resources/org/semanticweb/HermiT/owl_wg_tests/ontologies/all.rdf \
  --output .reference/w3c-inventory.candidate.json
```
