# Deviations, provenance, and licensing

This project is a source-guided behavioral reimplementation, not a clean-room project:
implementers may study pinned HermiT source and tests. That choice must be reflected
honestly in notices, provenance, and licensing.

This document is an engineering policy, not legal advice. Release owners must obtain
appropriate legal review for distribution and branding claims.

## 1. Correctness decision rule

When pyHermiT, pinned HermiT, and a W3C expectation disagree:

1. minimize the case while preserving valid OWL 2 DL structure;
2. reproduce it in both pyHermiT backends and the pinned Java oracle;
3. identify the exact Structural Specification/Direct Semantics/erratum/conformance
   text and applicable datatype rules;
4. determine whether the difference is semantic, API-shape, parser, timeout/resource,
   or nondeterministic presentation;
5. propose a deviation record if pyHermiT should intentionally differ from HermiT;
6. obtain review before changing a golden; and
7. commit permanent W3C, Java observation, Python, and native regression fixtures.

A timeout/OOM does not establish a logical reference answer. A newer reasoner agreeing
with pyHermiT is useful evidence but does not outrank normative semantics.

## 2. Deviation record schema

Accepted records are added below and mirrored in
`tests/data/deviations/manifest.toml` when implementation begins.

```markdown
### DEV-NNN — Short title

- Status: proposed | accepted | withdrawn
- Applies since: pyHermiT version/commit
- Input fixture and SHA-256:
- Operation/configuration:
- Pinned HermiT observation:
- pyHermiT required result:
- Difference class: semantic bug | parser/profile bug | API bug | safety/resource fix
- Normative evidence: stable W3C section/erratum/test links
- Upstream issue/history, if any:
- Python regression:
- Native regression:
- Oracle generator version:
- Approved by/date:
```

Rules:

- One independently reversible behavior per record.
- “More correct,” “Pythonic,” or performance is not sufficient evidence.
- An accepted deviation changes only the enumerated case class; generalization needs
  explicit tests.
- Withdrawals retain history and migrate goldens in a dedicated change.
- The public changelog calls out deviations affecting prior user-visible answers.

## 3. Accepted deviations

None at specification time. Historical HermiT bugs and known test failures are
regression candidates, not preapproved deviations.

## 4. Source/reference provenance

`tools/reference/manifest.toml` records:

- upstream repository and immutable commit;
- source archive/tree hash and retrieval date;
- Maven HermiT/OWLAPI/JVM versions used by the oracle;
- license identifiers and notice paths;
- files/classes consulted by each work package; and
- hashes/schema versions of generated oracle fixtures.

Production code comments cite a pinned path/class/method when behavior is materially
source-guided. Do not cite mutable `master` or bare line numbers as the only reference.
Method/class plus commit is stable; line ranges are supplementary.

Do not vendor or modify the HermiT tree in this repository. A hash-verifying fetch or
container step populates an ignored development cache. No reference source or binary is
included in wheels.

## 5. Project and upstream licensing

### LIC-001 — release-blocking project/derivative license decision

Status: **decision recorded (owner, 2026-07-17); repository-owned implementation and
artifact audits completed 2026-07-18; the owner explicitly waived the remaining
owner/legal-review signoff as-is for `0.1.0`, the documentation-only `0.1.1`
patch, and the complete-artifact `0.1.2` release on 2026-07-30. This is a release override,
not legal advice and not a representation that legal review occurred.**

Recorded decision (owner, 2026-07-17):

- **Implementation mode: 1 — source-guided/ported.** This project is not clean-room and
  must never be relabeled as such (see §1 above and `verification.md` §11 precedent in
  pyELK).
- **Project license: `LGPL-3.0-or-later`, matching the pinned upstream HermiT
  declaration.** Apache-2.0 was considered for consistency with the rest of the
  workspace and rejected: translated/adapted HermiT material is treated as derivative of
  LGPL source, and only a documented clean-room implementation (mode 2) could support an
  Apache-2.0 core. Individual original pyHermiT files that adapt no HermiT material MAY
  additionally be offered under Apache-2.0 only if the file-level provenance inventory
  supports it and legal review approves the resulting notice layout; the combined
  artifact remains `LGPL-3.0-or-later`.
- Executed on 2026-07-17: `LICENSE` now contains the LGPL-3.0 text, `COPYING` retains
  the GPL-3.0 text it incorporates, and `NOTICE.md` credits HermiT and records this
  decision. The earlier bare GPL-3 `LICENSE` was never an approved relicensing and is
  superseded.
- Executed on 2026-07-18: the file-level adapted-source inventory, aggregate upstream
  and modification headers, wheel/sdist license and corresponding-source policy, and
  local artifact audit are recorded under `reports/licensing/` and
  `reports/release/artifact-audit.md`. Their executable checks leave the machine gate
  open and publication disabled.
- Still recommended as post-release follow-up: owner/legal review of the inventory
  boundary, aggregate notice layout (the pinned source contains more than one
  copyright-header variant), source-distribution strategy, and artifact policy. The
  `0.1.0` release proceeded under
  `reports/release/0.1.0-owner-release-override.md`; `0.1.1` proceeded under
  `reports/release/0.1.1-owner-release-override.md`; and `0.1.2` proceeds under
  `reports/release/0.1.2-owner-release-override.md`. None of these records substitutes for
  that review.

Historical context: the repository previously contained the GNU GPL version 3 text as
`LICENSE`, while pinned HermiT declares `LGPL-3.0-or-later`. Merely placing a license
text in the repository does not document who selected an SPDX expression for new
pyHermiT work, does not determine whether particular translated/adapted files are
derivative, and does not discharge HermiT's LGPL notices/source obligations — which is
why the decision above had to be recorded explicitly.

Before any wheel, sdist, crate, container, or public release is published, the recorded
strategy must be completed with exact SPDX expressions, copyright holders,
source/offer/linkage obligations, notices, and artifact policy, all under appropriate
legal review. These are the implementation modes that were evaluated (mode 1 was
selected above):

1. **Source-guided/ported implementation.** Implementers may inspect or adapt pinned HermiT.
   Every copied, translated, or adapted file/test is inventoried, retains applicable Oxford/
   authors' copyright and `LGPL-3.0-or-later` notice, states modifications, and follows the
   reviewed LGPL-compatible distribution/source strategy. Mechanical translation is not
   made original by changing language or identifiers.
2. **Documented clean-room implementation.** Only a genuinely separated requirements/oracle
   team and implementation team with auditable information flow may use this label. Existing
   source-guided specifications/code cannot become clean-room retroactively; affected work
   must be independently replaced and provenance reviewed. Public standards and black-box
   oracle outputs may be used only under the reviewed protocol.
3. **Mixed implementation.** File-level provenance and licensing distinguish original,
   source-guided, copied-test, generated-fixture, and third-party components; the combined
   artifact policy must be reviewed as a whole.

LIC-001 remains fail-closed unless every repository requirement is completed or explicitly
waived with repository evidence. For `0.1.2`, the owner waiver closes the machine gate
without marking the legal-review requirement complete. The decision, license texts,
metadata, adapted-file/header inventory, package-source policy, local artifact audit, and
release override are all part of the release record.

Release requirements:

- `pyproject.toml` has an SPDX license expression matching the repository decision;
- `NOTICE.md` credits HermiT and lists source/revision and adapted components;
- source files with adapted material carry both provenance and required notices;
- wheel/sdist license files satisfy Python metadata and upstream obligations;
- the Rust crate uses the same project license expression; and
- README/API docs do not imply endorsement by the original HermiT authors.
- a machine-readable `LIC-001` gate proves the reviewed decision is closed before publish.

Do not copy OWLAPI, dk.brics automaton, JAutomata, Apache Axiom, GNU getopt, Protege, or
other HermiT dependencies. Replace their behavior with Python/Rust/W3C-based components
and track any new dependency separately.

## 6. Dependency policy

Every Python/Rust runtime, build, or development dependency has a machine-readable
record with version range, source, license, purpose, shipped/linkage status, and audit
owner. Runtime/native dependencies must be compatible with the project license and
wheel targets. General ontology parsing is supplied only by the pinned pyowl-core contract;
prefer small, maintained libraries for other low-level primitives. Reasoner semantics remain
owned and tested by pyHermiT.

`Cargo.lock` and Python build constraints are committed for release builds. Automated
advisory and license scans are release gates, but scanner approval does not replace
manual review of unusual/custom licenses or bundled data.

## 7. Test and ontology licensing

For every external test/ontology, `tests/data/PROVENANCE.toml` records:

```toml
[[artifact]]
id = "..."
origin = "https://..."
revision = "..."
sha256 = "..."
license = "SPDX-or-exact-custom-id"
notice = "..."
redistribution = "vendored | fetch-only | generated-output-only"
modifications = "none"
```

Specific cautions:

- do not copy the AGPL-licensed `owlwg-test` Java harness; implement the public W3C
  manifest semantics independently;
- do not assume HermiT's LGPL declaration relicenses every bundled W3C or third-party
  ontology;
- W3C's current test-suite dual-license policy must be tied to the exact acquired
  artifacts/notices before redistribution; and
- Pizza, Wine, GALEN, DOLCE, ORE, and similar benchmark ontologies remain fetch-only or
  absent until their individual licenses permit the intended use.

An unmodified official suite under its prescribed license may support a W3C conformance
claim. A modified/subset corpus is labeled an internal compatibility suite.

## 8. Security and input provenance

External ontologies are untrusted data. pyowl-core owns XML/RDF/syntax parser hardening,
explicit bounded import resolution, compressed/cache input limits, and core-wire validation;
pyHermiT pins a compatible core line and consumes its security/conformance report rather than
forking those readers. pyHermiT owns strict-closure acceptance, profile validation,
regex/datatype cancellation/resource bounds, and private Rust-wire length/reference checks.

Security fixes may intentionally reject a hostile input that an old Java dependency
accepted. Record a deviation only if this changes behavior for a structurally valid OWL
2 DL ontology; malformed-input hardening ordinarily needs a security regression and
changelog entry, not semantic compatibility.

## 9. Reference updates

Updating the HermiT pin requires one dedicated work package/PR that:

1. records old/new commits, versions, licenses, and complete source/test diffs;
2. rebuilds both oracle versions in controlled environments;
3. regenerates the full golden set without overwriting old results first;
4. reports every normalized semantic/API/performance change;
5. resolves changes through the correctness decision rule;
6. updates `reference-scope.md`, work-package references, hashes, notices, and
   benchmarks; and
7. passes the complete conformance/backend/release matrix.

The reference never floats automatically with an upstream branch.
