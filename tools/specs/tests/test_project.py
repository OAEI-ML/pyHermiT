from __future__ import annotations

import unittest

from tools.specs._compat import repository_root
from tools.specs.check_links import _documentation, check_links
from tools.specs.check_project import validate_project


class ProjectMetadataTests(unittest.TestCase):
    def test_current_project_metadata_is_valid(self) -> None:
        summary = validate_project(repository_root())

        self.assertEqual(summary["dependencies"], 25)
        self.assertEqual(summary["reference_areas"], 12)
        self.assertEqual(summary["licensing_pending"], 1)
        self.assertEqual(summary["planned_native_targets"], 8)

    def test_all_local_documentation_links_resolve(self) -> None:
        paths = _documentation(repository_root())

        self.assertEqual(check_links(paths), [])
        self.assertGreaterEqual(len(paths), 42)


if __name__ == "__main__":
    unittest.main()
