"""Check local Markdown links and heading fragments in project documentation."""

from __future__ import annotations

import argparse
import re
import urllib.parse
from collections import Counter
from collections.abc import Iterable, Sequence
from pathlib import Path

from tools.specs._compat import repository_root

_LINK = re.compile(r"(?<!!)\[[^\]]*\]\(([^)]+)\)")
_HEADING = re.compile(r"^#{1,6}\s+(.+?)\s*#*\s*$")


def _slug_base(value: str) -> str:
    value = re.sub(r"<[^>]+>", "", value).strip().lower()
    value = re.sub(r"[^\w\- ]", "", value, flags=re.UNICODE)
    return re.sub(r"[ ]+", "-", value)


def _heading_slugs(path: Path) -> set[str]:
    counts: Counter[str] = Counter()
    slugs: set[str] = set()
    for line in path.read_text(encoding="utf-8").splitlines():
        match = _HEADING.match(line)
        if match is None:
            continue
        base = _slug_base(match.group(1))
        count = counts[base]
        counts[base] += 1
        slugs.add(base if count == 0 else f"{base}-{count}")
    return slugs


def _documentation(root: Path) -> tuple[Path, ...]:
    paths = [root / "README.md", root / "NOTICE.md"]
    paths.extend(sorted((root / "specs").rglob("*.md")))
    paths.extend(sorted((root / "tools/specs").glob("*.md")))
    return tuple(path for path in paths if path.is_file())


def check_links(paths: Iterable[Path]) -> list[str]:
    errors: list[str] = []
    slug_cache: dict[Path, set[str]] = {}
    for source in paths:
        for raw_target in _LINK.findall(source.read_text(encoding="utf-8")):
            target = raw_target.strip()
            if target.startswith("<") and target.endswith(">"):
                target = target[1:-1]
            if target.startswith(("http://", "https://", "mailto:")):
                continue
            path_text, separator, fragment = target.partition("#")
            decoded_path = urllib.parse.unquote(path_text)
            destination = source if not decoded_path else (source.parent / decoded_path).resolve()
            if not destination.exists():
                errors.append(f"{source}: missing link target {raw_target!r}")
                continue
            if separator and fragment and destination.is_file() and destination.suffix == ".md":
                expected = urllib.parse.unquote(fragment).lower()
                slugs = slug_cache.setdefault(destination, _heading_slugs(destination))
                if expected not in slugs:
                    errors.append(f"{source}: missing heading #{fragment} in {destination}")
    return errors


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paths", nargs="*", type=Path)
    args = parser.parse_args(argv)
    paths = tuple(args.paths) if args.paths else _documentation(repository_root())
    errors = check_links(paths)
    if errors:
        print("\n".join(errors))
        return 1
    print(f"Markdown links valid: {len(paths)} files")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
