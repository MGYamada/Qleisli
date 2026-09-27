#!/usr/bin/env python3
"""Check Markdown references, Lean imports, and the generated current-state view.

A link labelled with one backticked identifier and targeting a .rs file opts
into declaration checking. Under tests/, it must name a #[test] function.
This is a source-reference check, not a Rust parser or a coverage proof.
"""

from pathlib import Path
import json
import re
import sys
from urllib.parse import unquote, urlsplit


ROOT = Path(__file__).resolve().parents[1]
LINK = re.compile(r"\[([^\]]*)\]\(([^)]+)\)")
IDENTIFIER = re.compile(r"`([A-Za-z_][A-Za-z_0-9]*)`")


def markdown_prose(text: str) -> str:
    """Ignore fenced examples and HTML comments, retaining diagnostic lines."""
    lines = []
    fence = None
    for line in text.splitlines(keepends=True):
        marker = re.match(r"^ {0,3}(`{3,}|~{3,})(.*)$", line)
        if fence is None and marker:
            fence = marker[1]
        elif fence and marker and marker[1][0] == fence[0]:
            if len(marker[1]) >= len(fence) and not marker[2].strip():
                fence = None
        elif fence is None:
            lines.append(line)
            continue
        lines.append("\n" if line.endswith("\n") else "")
    return re.sub(
        r"<!--.*?(?:-->|$)",
        lambda match: re.sub(r"[^\n]", " ", match[0]),
        "".join(lines),
        flags=re.DOTALL,
    )


def markdown_anchors(text: str) -> set[str]:
    """Support explicit HTML ids and the repository's ATX heading convention."""
    prose = markdown_prose(text)
    anchors = set(re.findall(r'<a\s+id=[\'"]([^\'"]+)[\'"]', prose))
    used = set()
    for heading in re.findall(r"^ {0,3}#{1,6}\s+(.+?)\s*$", prose, re.MULTILINE):
        heading = re.sub(r"\s+#+$", "", heading)
        heading = LINK.sub(lambda match: match[1], heading)
        heading = re.sub(r"<[^>]*>", "", heading)
        slug = re.sub(r"[^\w\- ]", "", heading.lower()).replace(" ", "-")
        anchor = slug
        suffix = 0
        while anchor in used:
            suffix += 1
            anchor = f"{slug}-{suffix}"
        used.add(anchor)
        anchors.add(anchor)
    return anchors


RUST_LITERAL = re.compile(
    r'//[^\n]*|/\*|\b(?:br|cr|r)(#*)"|(?:b|c)?"(?:\\.|[^"\\])*"'
    r"|b?'(?:\\.|[^'\\])'",
    re.DOTALL,
)


def rust_code(text: str) -> str:
    """Mask comments and literals so embedded source examples cannot satisfy links."""
    chunks = []
    start = 0
    while match := RUST_LITERAL.search(text, start):
        chunks.append(text[start:match.start()])
        end = match.end()
        if match[0] == "/*":
            depth = 1
            while depth and (comment := re.search(r"/\*|\*/", text[end:])):
                depth += 1 if comment[0] == "/*" else -1
                end += comment.end()
            if depth:
                end = len(text)
        elif match[1] is not None:
            terminator = '"' + match[1]
            closing = text.find(terminator, end)
            end = len(text) if closing == -1 else closing + len(terminator)
        chunks.append(re.sub(r"[^\n]", " ", text[match.start():end]))
        start = end
    chunks.append(text[start:])
    return "".join(chunks)


def rust_references(text: str) -> tuple[set[str], set[str]]:
    code = rust_code(text)
    visibility = r"(?:pub(?:\([^)]*\))?\s+)?"
    names = set(re.findall(
        r"^\s*" + visibility + r"(?:(?:async|unsafe|const)\s+)*"
        r"(?:fn|struct|enum|type|trait|const|static|mod)\s+([A-Za-z_]\w*)\b",
        code, re.MULTILINE,
    ))
    tests = set(re.findall(
        r"#\[\s*test\s*\]\s*(?:#\[[^]\n]*\]\s*)*" + visibility
        + r"(?:async\s+)?fn\s+([A-Za-z_]\w*)\s*\(", code,
    ))
    return names, tests


def check_links(root: Path, docs: list[Path]) -> tuple[list[str], dict[str, int]]:
    errors = []
    counts = dict(links=0, anchors=0, symbols=0, tests=0)
    source_cache = {}
    for path in sorted(docs):
        prose = markdown_prose(path.read_text(encoding="utf-8"))
        for match in LINK.finditer(prose):
            label, target = match.groups()
            target = target.strip().split(' "', 1)[0].strip("<>")
            url = urlsplit(target)
            if url.scheme or url.netloc:
                continue
            counts["links"] += 1
            location = f"{path.relative_to(root)}:{prose.count(chr(10), 0, match.start()) + 1}"
            destination = (path.parent / unquote(url.path)).resolve() if url.path else path
            if not destination.exists():
                errors.append(f"{location}: missing target {target}")
                continue
            if destination.suffix == ".md" and url.fragment:
                counts["anchors"] += 1
                if unquote(url.fragment) not in markdown_anchors(destination.read_text(encoding="utf-8")):
                    errors.append(f"{location}: missing Markdown anchor {target}")
            identifier = IDENTIFIER.fullmatch(label)
            if destination.suffix != ".rs" or identifier is None:
                continue
            name = identifier[1]
            if destination not in source_cache:
                source_cache[destination] = rust_references(destination.read_text(encoding="utf-8"))
            symbols, tests = source_cache[destination]
            is_test = (root / "tests") in destination.parents
            counts["tests" if is_test else "symbols"] += 1
            if name not in (tests if is_test else symbols):
                kind = "#[test] function" if is_test else "Rust declaration"
                errors.append(f"{location}: missing {kind} {name} in {target}")
    return errors, counts


LEAN_MODULE_NAME = re.compile(r"[^\W\d][\w']*(?:\.[^\W\d][\w']*)*")


def lean_imports(text: str) -> list[str]:
    """Read the initial import header without requiring Lean in the docs job.

    Support the repository's unquoted module names and Lean 4's optional
    module/prelude and public/meta/all modifiers. Ordinary comments are header
    whitespace; nested block comments are counted, not parsed as code. A doc
    comment or any other command ends the header, as in Lean's parser. In
    particular, declarations and their strings/quotations are never scanned.
    Unsupported header syntax is left for the Lean build to diagnose and
    cannot supply a project dependency here.
    """
    position = 0

    def token() -> str | None:
        nonlocal position
        while position < len(text):
            if text[position].isspace():
                position += 1
            elif text.startswith("--", position):
                end = text.find("\n", position)
                position = len(text) if end == -1 else end + 1
            elif text.startswith(("/--", "/-!"), position):
                return None  # Documentation comments are commands, not whitespace.
            elif text.startswith("/-", position):
                depth = 1
                position += 2
                while position < len(text) and depth:
                    if text.startswith("/-", position):
                        depth += 1
                        position += 2
                    elif text.startswith("-/", position):
                        depth -= 1
                        position += 2
                    else:
                        position += 1
            else:
                match = LEAN_MODULE_NAME.match(text, position)
                if match is None:
                    return None
                end = match.end()
                if end < len(text) and not (
                    text[end].isspace() or text.startswith(("--", "/-"), end)
                ):
                    return None  # Never count a prefix of an unsupported name.
                position = end
                return match[0]
        return None

    current = token()
    if current == "module":
        current = token()
    if current == "prelude":
        current = token()
    imports = []
    while current is not None:
        if current == "public":
            current = token()
        if current == "meta":
            current = token()
        if current != "import":
            break
        dependency = token()
        if dependency == "all":
            dependency = token()
        if dependency is None:
            break
        imports.append(dependency)
        current = token()
    return imports


def check_lean(root: Path) -> tuple[list[str], int]:
    errors = []
    lean = root / "lean"
    sources = {"Qleisli": lean / "Qleisli.lean"}
    for path in (lean / "Qleisli").rglob("*.lean"):
        sources[".".join(path.relative_to(lean).with_suffix("").parts)] = path
    visited = set()

    def visit(module: str) -> None:
        if module in visited:
            return
        visited.add(module)
        if module not in sources or not sources[module].is_file():
            errors.append(f"missing Lean module: {module}")
            return
        for dependency in lean_imports(sources[module].read_text(encoding="utf-8")):
            if dependency == "Qleisli" or dependency.startswith("Qleisli."):
                visit(dependency)

    visit("Qleisli")
    for module in sorted(sources.keys() - visited):
        errors.append(f"Lean module absent from root import/audit: {module}")
    return errors, len(sources)


def render_status(root: Path) -> str:
    """Render current planning states and a scoped inventory, not proof claims."""
    data = json.loads((root / "docs/project-status.json").read_text(encoding="utf-8"))
    if set(data) != {"format", "release_state", "milestones", "inventory"} or data["format"] != 1:
        raise ValueError("unsupported project-status format or fields")
    versions = []
    for manifest in ["Cargo.toml", "lean/lakefile.toml"]:
        match = re.search(r'^version = "([^"]+)"$', (root / manifest).read_text(), re.MULTILINE)
        if not match:
            raise ValueError(f"missing project version in {manifest}")
        versions.append(match[1])
    if versions[0] != versions[1]:
        raise ValueError("Rust and Lean project versions differ")

    def cell(value):
        if not isinstance(value, str) or not value.strip() or "\n" in value or "\r" in value:
            raise ValueError("status cells must be nonempty single-line strings")
        return value.replace("|", "\\|")

    def rows(items, fields):
        if not isinstance(items, list) or not items:
            raise ValueError("status tables must be nonempty lists")
        result = []
        for item in items:
            if not isinstance(item, dict) or set(item) != set(fields):
                raise ValueError("status row has missing or unknown fields")
            result.append("| " + " | ".join(cell(item[key]) for key in fields) + " |")
        return result

    milestone_rows = rows(data["milestones"], ["id", "state", "evidence", "open"])
    if [item["id"] for item in data["milestones"]] != [f"M{i}" for i in range(6)]:
        raise ValueError("milestones must contain M0 through M5 once, in order")
    inventory_rows = rows(data["inventory"], ["rule", "implementation", "tests", "proof"])
    return "\n".join([
        "# Current project status and finite-rule inventory", "",
        "<!-- Generated by scripts/check_docs.py --write-status; edit docs/project-status.json. -->", "",
        f"Selected product version: **{versions[0]}**. Release state: {cell(data['release_state'])}.",
        f"See the [validation/publication record](releases/v{versions[0]}.md).", "",
        "This view is generated from [project-status.json](project-status.json) and the project manifests.",
        "It centralizes current scheduling states and an initial rule/implementation/test/proof inventory.",
        "The inventory names inspected boundaries and existing regressions; it is not a complete",
        "conformance audit, a test execution report or a proof of Rust acceptance soundness.",
        "Dated execution evidence remains in the [conformance history](specification-status.md).", "",
        "## Active milestone states", "",
        "| Milestone | State | Evidence / direction | Remaining work |",
        "| --- | --- | --- | --- |", *milestone_rows, "",
        "## Finite rule inventory", "",
        "| Rule | Implementation boundary | Existing regression evidence | Proof status and gap |",
        "| --- | --- | --- | --- |", *inventory_rows, "",
        "[M0–M5 and legacy IDs](v0x-roadmap.md#legacy-id-mapping) separate active scheduling",
        "from requirements, theorem names, acceptance criteria and historical release steps.",
        "Regenerate with `python3 scripts/check_docs.py --write-status`; ordinary checks reject drift.", "",
    ])


def check_status(root: Path, write: bool = False) -> list[str]:
    try:
        expected = render_status(root)
        path = root / "docs/current-status.md"
        if write:
            path.write_text(expected, encoding="utf-8")
        elif not path.exists() or path.read_text(encoding="utf-8") != expected:
            return ["docs/current-status.md is stale; run python3 scripts/check_docs.py --write-status"]
    except (OSError, ValueError, TypeError, KeyError) as failure:
        return [f"project status: {failure}"]
    return []


def main() -> int:
    if sys.argv[1:] not in ([], ["--write-status"]):
        print("usage: check_docs.py [--write-status]", file=sys.stderr)
        return 2
    status_errors = check_status(ROOT, write=sys.argv[1:] == ["--write-status"])
    docs = [*ROOT.glob("*.md"), *ROOT.joinpath("docs").rglob("*.md")]
    docs += list(ROOT.joinpath("lean").glob("*.md"))
    docs += list(ROOT.joinpath("research").glob("*/README.md"))
    errors, counts = check_links(ROOT, docs)
    errors.extend(status_errors)
    lean_errors, modules = check_lean(ROOT)
    errors.extend(lean_errors)
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    print(
        f"Checked {counts['links']} local links, {counts['anchors']} Markdown anchors, "
        f"{counts['symbols']} Rust declarations, {counts['tests']} Rust tests, "
        f"and {modules} Lean root modules."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
