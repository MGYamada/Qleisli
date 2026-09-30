#!/usr/bin/env python3
"""Lint contract-writing pilots, not equations, executable code or proof claims.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""

from pathlib import Path
import re
import sys
from urllib.parse import unquote, urlsplit

sys.dont_write_bytecode = True
from check_docs import LINK, check_links, markdown_prose


ROOT = Path(__file__).resolve().parents[1]
SECTIONS = (
    "Meaning", "Interface and encoding", "Premises and capabilities",
    "Ancillas and effects", "Approximation", "Resources",
    "Validation and proof status", "Adoption and teaching",
)
ASPECT_STATUSES = {
    "Source checking": {"checked", "pending"},
    "Semantic tests": {"tested", "pending"},
    "Actual IR conformance": {"proved", "pending", "not-applicable"},
    "Source preservation": {"proved", "pending", "not-applicable"},
    "Specification review": {"reviewed", "pending"},
}
REQUIRED_PILOTS = {"qft2.md", "add2.md", "and-phase.md"}
PLACEHOLDER = re.compile(r"\b(?:TODO|TBD)\b|^\s*\[[^\n]+\]\s*$", re.MULTILINE)


def sections(text: str) -> dict[str, list[str]]:
    """Preserve duplicate sections; examples in fences/comments cannot satisfy them."""
    prose = markdown_prose(text)
    headings = list(re.finditer(r"^## ([^\n]+)\s*$", prose, re.MULTILINE))
    result: dict[str, list[str]] = {}
    for index, heading in enumerate(headings):
        end = headings[index + 1].start() if index + 1 < len(headings) else len(prose)
        result.setdefault(heading[1].strip(), []).append(prose[heading.end():end].strip())
    return result


def check_document(root: Path, path: Path, template: bool = False) -> list[str]:
    label = path.relative_to(root).as_posix()
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as error:
        return [f"{label}: cannot read contract: {error}"]
    fields = sections(text)
    errors = []
    for name in SECTIONS:
        bodies = fields.get(name, [])
        if len(bodies) != 1:
            errors.append(f"{label}: expected one '{name}' section, found {len(bodies)}")
        elif not bodies[0]:
            errors.append(f"{label}: empty '{name}' section")
        elif not template and PLACEHOLDER.search(bodies[0]):
            errors.append(f"{label}: unfilled prompt in '{name}' section")

    status_sections = fields.get("Validation and proof status", [])
    if len(status_sections) == 1:
        seen = set()
        headers = 0
        separators = 0
        for line in status_sections[0].splitlines():
            if not line.startswith("|"):
                continue
            cells = [cell.strip() for cell in line.strip().strip("|").split("|")]
            if cells[0] == "Aspect":
                headers += 1
                if cells != ["Aspect", "Status", "Scope and evidence"]:
                    errors.append(f"{label}: malformed status table header")
                continue
            if all(re.fullmatch(r":?-+:?", cell) for cell in cells):
                separators += 1
                if len(cells) != 3:
                    errors.append(f"{label}: status separator must have three columns")
                continue
            if len(cells) != 3:
                errors.append(f"{label}: status row must have three columns")
                continue
            aspect, status, grounds = cells
            if aspect not in ASPECT_STATUSES:
                errors.append(f"{label}: unknown status aspect '{aspect}'")
            elif aspect in seen:
                errors.append(f"{label}: duplicate status aspect '{aspect}'")
            elif status not in ASPECT_STATUSES[aspect]:
                errors.append(f"{label}: unsupported status '{status}' for '{aspect}'")
            seen.add(aspect)
            if not grounds:
                errors.append(f"{label}: missing scope/evidence for '{aspect}'")
            elif not template and status in {"checked", "tested", "proved", "reviewed"}:
                if not LINK.search(grounds):
                    errors.append(f"{label}: completed '{aspect}' needs an evidence link")
        for aspect in ASPECT_STATUSES.keys() - seen:
            errors.append(f"{label}: missing status aspect '{aspect}'")
        if headers != 1 or separators != 1:
            errors.append(f"{label}: status table needs one header and one separator")

    if not template:
        interfaces = fields.get("Interface and encoding", [])
        source_found = False
        if len(interfaces) == 1:
            for match in LINK.finditer(interfaces[0]):
                target = urlsplit(unquote(match[2]))
                if target.scheme or target.netloc or not target.path.endswith(".qli"):
                    continue
                source = (path.parent / target.path).resolve()
                if source.is_relative_to(root.resolve()) and source.is_file():
                    source_found = True
        if not source_found:
            errors.append(f"{label}: interface needs an existing local .qli source link")
    return errors


def check_contract_docs(root: Path) -> tuple[list[str], int]:
    template = root / "docs/stdlib-contract-template.md"
    examples = sorted((root / "docs/stdlib-contract-examples").glob("*.md"))
    errors = check_document(root, template, template=True)
    missing = REQUIRED_PILOTS - {path.name for path in examples}
    errors.extend(f"contract pilots: missing {name}" for name in sorted(missing))
    for path in examples:
        errors.extend(check_document(root, path))
    paths = [root / "STDLIB.md", template, *examples]
    for path in paths:
        if not path.is_file() and path != template:
            errors.append(f"contract conventions: missing {path.relative_to(root)}")
    # Reuse normal anchor/declaration checking. This does not replay linked results.
    link_errors, _ = check_links(root, [path for path in paths if path.is_file()])
    errors.extend(link_errors)
    return errors, len(examples)


def main() -> int:
    if sys.argv[1:]:
        print("usage: check_stdlib_contract_docs.py", file=sys.stderr)
        return 2
    errors, count = check_contract_docs(ROOT)
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    print(f"Checked contract template and {count} pilots; documentation structure/links only.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
