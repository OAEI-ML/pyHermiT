from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

from tools.specs._compat import repository_root
from tools.specs.check_release_gate import ReleaseGateError, main, release_status


class ReleaseGateTests(unittest.TestCase):
    def test_actual_gate_is_valid_and_permits_owner_authorized_publication(self) -> None:
        path = repository_root() / "tools/specs/licensing.toml"

        allowed, pending = release_status(path)

        self.assertTrue(allowed)
        self.assertEqual(pending, ())
        self.assertEqual(main(["--manifest", str(path), "--assert-blocked"]), 1)
        self.assertEqual(main(["--manifest", str(path), "--require-publishable"]), 0)

    def test_malformed_gate_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "licensing.toml"
            path.write_text(
                """
schema = 1
gate_id = "LIC-001"
decision_status = "recorded"
gate_status = "open"
publish_allowed = true
[[requirement]]
id = "legal-review"
status = "pending"
""",
                encoding="utf-8",
            )

            with self.assertRaises(ReleaseGateError):
                release_status(path, evidence_root=Path(temporary))
            self.assertEqual(main(["--manifest", str(path), "--require-publishable"]), 1)

    def test_completed_requirement_with_missing_evidence_fails_closed(self) -> None:
        source = repository_root() / "tools/specs/licensing.toml"
        content = source.read_text(encoding="utf-8").replace(
            'evidence = "specs/deviations.md"',
            'evidence = "missing-owner-decision.md"',
            1,
        )
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "licensing.toml"
            path.write_text(content, encoding="utf-8")

            with self.assertRaisesRegex(ReleaseGateError, "does not exist"):
                release_status(path, evidence_root=repository_root())

    def test_expected_evidence_identity_drift_fails_closed(self) -> None:
        source = repository_root() / "tools/specs/licensing.toml"
        content = source.read_text(encoding="utf-8").replace(
            'expected_evidence = ["specs/deviations.md"]',
            'expected_evidence = ["README.md"]',
            1,
        )
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "licensing.toml"
            path.write_text(content, encoding="utf-8")

            with self.assertRaisesRegex(ReleaseGateError, "identity drift"):
                release_status(path, evidence_root=repository_root())

    def test_owner_waiver_must_match_the_runtime_release_version(self) -> None:
        source = repository_root() / "tools/specs/licensing.toml"
        content = source.read_text(encoding="utf-8").replace(
            "reports/release/0.2.0-owner-release-override.md",
            "reports/release/0.1.1-owner-release-override.md",
        )
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "licensing.toml"
            path.write_text(content, encoding="utf-8")

            with self.assertRaisesRegex(ReleaseGateError, "identity drift"):
                release_status(path, evidence_root=repository_root())


if __name__ == "__main__":
    unittest.main()
