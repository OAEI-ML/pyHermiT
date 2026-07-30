from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def test_readme_quick_start_executes_public_reasoner_api() -> None:
    readme = (ROOT / "README.md").read_text(encoding="utf-8")
    quick_start = readme.split("## Quick start", 1)[1].split("## ", 1)[0]
    match = re.search(r"```python\n(?P<source>.*?)```", quick_start, flags=re.DOTALL)
    assert match is not None
    source = match.group("source")
    assert "reasoner.classify_classes()" not in source
    assert "taxonomy = reasoner.class_hierarchy()" in source

    namespace: dict[str, object] = {}
    exec(compile(source, "README.md#quick-start", "exec"), namespace)
    taxonomy = namespace["taxonomy"]
    assert taxonomy.nodes  # type: ignore[attr-defined]
