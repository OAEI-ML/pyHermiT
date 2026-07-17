# pyHermiT

pyHermiT is specified as a Java-free Python and Rust reimplementation of the core
HermiT OWL 2 DL reasoner, with a complete pure-Python fallback. It targets Python 3.10+
and uses the Java-free `pyowl-core` package for shared ontology parsing, immutable views,
overlays, composites, and zero-reparse communication with Exact-OM and other consumers.

Implementation has not started. The normative architecture, compatibility rules, and
parallel agent work packages begin at [`specs/README.md`](specs/README.md).

The owner has selected the source-guided implementation mode and
`LGPL-3.0-or-later`, matching the pinned upstream declaration. `LICENSE` contains the
LGPL text, `COPYING` the GPL text it incorporates, and `NOTICE.md` the initial upstream
attribution. No release may be published while the remaining `LIC-001` provenance,
file-header, package-metadata, source-obligation, artifact-audit, and legal-review
checklist in [`specs/deviations.md`](specs/deviations.md) is open.
