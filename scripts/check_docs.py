#!/usr/bin/env python3
"""Check local Markdown targets and coverage of the Lean root imports."""

from pathlib import Path
import re
import sys
from urllib.parse import unquote, urlsplit


ROOT = Path(__file__).resolve().parents[1]


def main() -> int:
    errors = []
    links = 0
    docs = [*ROOT.glob("*.md"), *ROOT.joinpath("docs").rglob("*.md")]
    docs += list(ROOT.joinpath("lean").glob("*.md"))
    for path in sorted(docs):
        text = path.read_text(encoding="utf-8")
        # Inline links, including image links; skip external URLs and anchors.
        for target in re.findall(r"\[[^\]]*\]\(([^)]+)\)", text):
            target = target.strip().split(' "', 1)[0].strip("<>")
            url = urlsplit(target)
            if url.scheme or url.netloc or not url.path:
                continue
            links += 1
            if not (path.parent / unquote(url.path)).exists():
                errors.append(f"{path.relative_to(ROOT)}: missing target {target}")

    lean = ROOT / "lean"
    sources = {"Qleisli": lean / "Qleisli.lean"}
    for path in (lean / "Qleisli").rglob("*.lean"):
        sources[".".join(path.relative_to(lean).with_suffix("").parts)] = path
    visited = set()

    def visit(module: str) -> None:
        if module in visited:
            return
        visited.add(module)
        if module not in sources:
            errors.append(f"missing Lean module: {module}")
            return
        for dependency in re.findall(
            r"^import (Qleisli(?:\.\w+)*)\s*$", sources[module].read_text(), re.MULTILINE
        ):
            visit(dependency)

    visit("Qleisli")
    for module in sorted(sources.keys() - visited):
        errors.append(f"Lean module absent from root import/audit: {module}")
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    print(f"Checked {links} local link targets and {len(sources)} Lean root modules.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
