# Notices

## Project license

pyHermiT is licensed under **LGPL-3.0-or-later**. `LICENSE` contains the GNU
Lesser General Public License version 3; `COPYING` contains the GNU General
Public License version 3, which the LGPL incorporates and supplements.

This choice follows the pinned upstream reference and was recorded as the
LIC-001 decision in [`specs/deviations.md`](specs/deviations.md) (owner,
2026-07-17). pyHermiT is a **source-guided** reimplementation — implementers
may study and adapt the pinned HermiT source — so the project matches the
upstream license rather than claiming a clean-room Apache-compatible core.

## Upstream attribution

pyHermiT reimplements the core reasoning behavior of **HermiT**:

- Repository: <https://github.com/phillord/hermit-reasoner>
- Pinned commit: `37ec30aced32ac81ebecc5e33fad255ddefcb4c3`
  (upstream Maven version `1.4.0.0-SNAPSHOT`)
- Upstream license: `LGPL-3.0-or-later`
- Copyright: the HermiT authors, University of Oxford, and contributors

No HermiT source or binary is vendored in this repository. Files that
translate or adapt pinned HermiT material carry upstream copyright and
license notices plus a modification statement. The repository-owned inventory
is `reports/licensing/adapted-files.toml`. For `0.1.2`, the owner waived the pending
legal-review signoff as-is without representing that legal review occurred; see
`reports/release/0.1.2-owner-release-override.md`.

pyHermiT does not claim endorsement by the original HermiT authors.
