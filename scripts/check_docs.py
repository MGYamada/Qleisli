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
import tomllib
from urllib.parse import unquote, urlsplit


ROOT = Path(__file__).resolve().parents[1]
LINK = re.compile(r"\[([^\]]*)\]\(([^)]+)\)")
IDENTIFIER = re.compile(r"`([A-Za-z_][A-Za-z_0-9]*)`")
AGENTS_MAX_LINES = 100
AGENTS_MAX_BYTES = 6000


def check_agents_budget(root: Path) -> list[str]:
    """Keep working instructions compact, including comments and examples."""
    try:
        content = (root / "AGENTS.md").read_bytes()
        lines = len(content.decode("utf-8").splitlines())
    except (OSError, UnicodeError) as failure:
        return [f"AGENTS.md: {failure}"]
    errors = []
    if lines > AGENTS_MAX_LINES:
        errors.append(f"AGENTS.md: {lines} lines exceeds {AGENTS_MAX_LINES}; replace or shorten existing rules")
    if len(content) > AGENTS_MAX_BYTES:
        errors.append(f"AGENTS.md: {len(content)} UTF-8 bytes exceeds {AGENTS_MAX_BYTES}; replace or shorten existing rules")
    return errors


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


def check_links(root: Path, docs: list[Path], *, text_overrides: dict[Path, str] | None = None) -> tuple[list[str], dict[str, int]]:
    errors = []
    counts = dict(links=0, anchors=0, symbols=0, tests=0)
    source_cache = {}
    for path in sorted(docs):
        source = text_overrides[path] if text_overrides and path in text_overrides else path.read_text(encoding="utf-8")
        prose = markdown_prose(source)
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


def render_status(root: Path, *, inventory_only: bool = False) -> str:
    """Render current planning states and a scoped inventory, not proof claims."""
    data = json.loads((root / "docs/project-status.json").read_text(encoding="utf-8"))
    if set(data) != {"format", "release_state", "current", "milestones", "inventory"} or data["format"] != 3:
        raise ValueError("unsupported project-status format or fields")
    versions = []
    for manifest in ["Cargo.toml", "lean/lakefile.toml", "lean-kernel/lakefile.toml", "python/pyproject.toml"]:
        match = re.search(r'^version = "([^"]+)"$', (root / manifest).read_text(), re.MULTILINE)
        if not match:
            raise ValueError(f"missing project version in {manifest}")
        versions.append(match[1])
    if len(set(versions)) != 1:
        raise ValueError("Rust, Lean and Python project versions differ")
    python_version = re.search(r'^__version__ = "([^"]+)"$', (root / "python/qleisli/__init__.py").read_text(), re.MULTILINE)
    if python_version is None or python_version[1] != versions[0]:
        raise ValueError("Python runtime version differs from project manifests")
    for notice in ["LICENSE", "NOTICE"]:
        if (root / "python" / notice).read_bytes() != (root / notice).read_bytes():
            raise ValueError(f"Python package {notice} differs from repository {notice}")

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
    current_rows = rows(data["current"], ["topic", "state", "detail"])
    if inventory_only:
        # Keep every rule visible, with one primary reference per evidence
        # column. The source ledger retains the complete reference lists and
        # scoped component statements rather than duplicating them in prose.
        def primary(value, label):
            links = LINK.findall(value)
            if links:
                original_label, target = links[0]
                if IDENTIFIER.fullmatch(original_label):
                    label = original_label
                return f"[{label}]({target})"
            return value if len(value) <= 80 else "[ledger](project-status.json)"

        compact_inventory = [
            {**item,
             "implementation": primary(item["implementation"], "code"),
             "tests": primary(item["tests"], "tests"),
             "proof": primary(item["proof"], "scope")}
            for item in data["inventory"]
        ]
        inventory_rows = rows(compact_inventory, ["rule", "implementation", "tests", "proof"])
        return "\n".join([
            "# Finite rule and implementation inventory", "",
            "<!-- Generated by scripts/check_docs.py --write-status; edit docs/project-status.json. -->", "",
            "For the current overview, read [current status](current-status.md).", "",
            "This scoped inventory identifies implementation boundaries, existing regressions",
            "and proved/open obligations. It is not a fresh execution report or complete soundness audit.", "",
            "Each row names a bounded component; linked packets/modules retain its exact premises",
            "and capacities. General source/Rust/native/execution correspondence, complete production",
            "soundness and R14/H1–H5 remain open. Rust acceptance stays authoritative; external",
            "schemas remain disabled. Historical probe counts belong to their frozen reports.", "",
            "The [source ledger](project-status.json) retains complete reference lists and",
            "component statements; this table gives one primary reference per column.", "",
            "| Rule | Implementation boundary | Existing regression evidence | Proof status and gap |",
            "| --- | --- | --- | --- |", *inventory_rows, "",
        ])
    return "\n".join([
        "# Current project status and finite-rule inventory", "",
        "<!-- Generated by scripts/check_docs.py --write-status; edit docs/project-status.json. -->", "",
        f"Selected product version: **{versions[0]}**. {cell(data['release_state'])}",
        f"See the [validation/publication record](releases/v{versions[0]}.md).", "",
        "## Where we are now", "",
        "| Area | Current state | Details |",
        "| --- | --- | --- |", *current_rows, "",
        "Historical narrative pages are retired; lookup uses Git history and published tags.", "",
        "This view is generated from [project-status.json](project-status.json) and the project manifests.",
        "It centralizes current scheduling states and an initial rule/implementation/test/proof inventory.",
        "The inventory names inspected boundaries and existing regressions; it is not a complete",
        "conformance audit, a test execution report or a proof of Rust acceptance soundness.",
        "Execution evidence remains beside the source and [validation fixtures](../tests/fixtures/authoring_sessions/README.md).", "",
        "## Active milestone states", "",
        "| Milestone | State | Evidence / direction | Remaining work |",
        "| --- | --- | --- | --- |", *milestone_rows, "",
        "## Finite rule inventory", "",
        "Read the [separate implementation/test/proof inventory](rule-inventory.md).", "",
        "[M0–M5 and legacy IDs](v0x-roadmap.md#legacy-id-mapping) separate active scheduling",
        "from requirements, theorem names, acceptance criteria and historical release steps.",
        "Regenerate with `python3 scripts/check_docs.py --write-status`; ordinary checks reject drift.", "",
    ])


def check_status(root: Path, write: bool = False) -> list[str]:
    try:
        views = {"docs/current-status.md": render_status(root),
                 "docs/rule-inventory.md": render_status(root, inventory_only=True)}
        for name, expected in views.items():
            path = root / name
            if write:
                path.write_text(expected, encoding="utf-8")
            elif not path.exists() or path.read_text(encoding="utf-8") != expected:
                return [f"{name} is stale; run python3 scripts/check_docs.py --write-status"]
    except (OSError, ValueError, TypeError, KeyError) as failure:
        return [f"project status: {failure}"]
    # The compact view displays primary references; validate every reference
    # retained in the source ledger, including secondary declaration links.
    ledger = root / "docs/project-status.json"
    data = json.loads(ledger.read_text(encoding="utf-8"))
    references = "\n".join(
        value for group in ["current", "milestones", "inventory"]
        for item in data[group] for value in item.values()
    )
    return check_links(root, [ledger], text_overrides={ledger: references})[0]


def markdown_paths(root: Path) -> list[Path]:
    docs = [*root.glob("*.md"), *root.joinpath("docs").rglob("*.md")]
    docs += list(root.joinpath("lean").glob("*.md"))
    docs += list(root.joinpath("lean-kernel").glob("*.md"))
    docs += list(root.joinpath("research").glob("*/README.md"))
    for directory in ["examples", "corpus", "stdlib", "tests/fixtures"]:
        docs += list(root.joinpath(directory).rglob("*.md"))
    return docs


def check_release_doc_links(root: Path) -> list[str]:
    """Package-facing documentation must follow the package's selected version."""
    version = tomllib.loads((root / "Cargo.toml").read_text())["package"]["version"]
    pattern = re.compile(r"https://github\.com/MGYamada/Qleisli/blob/v([^/\s)]+)/")
    errors = []
    for name in ["src/lib.rs", "README.crates.md"]:
        text = (root / name).read_text()
        for match in pattern.finditer(text):
            if match[1] != version:
                line = text.count("\n", 0, match.start()) + 1
                errors.append(f"{name}:{line}: documentation tag v{match[1]} differs from package v{version}")
    return errors


def check_corpus_overview(root: Path, write: bool = False) -> list[str]:
    """Current inventory counts come from manifests, never historical log totals."""
    try:
        manifest = json.loads((root / "corpus/manifest.json").read_text())
        faults = json.loads((root / "corpus/semantic_faults/manifest.json").read_text())
        cases = manifest["cases"]
        unitary = sum(case["kind"] == "unitary" for case in cases)
        begin, end = "<!-- corpus-inventory:start -->", "<!-- corpus-inventory:end -->"
        expected = (f"{begin}\n"
                    "<!-- Generated by scripts/check_docs.py --write-status from corpus manifests. -->\n\n"
                    "| Finite examples | Unitary examples | Observing examples | Semantic faults |\n"
                    "| --- | --- | --- | --- |\n"
                    f"| {len(cases)} | {unitary} | {len(cases) - unitary} | {len(faults['cases'])} |\n\n"
                    f"{end}")
        path = root / "corpus/README.md"
        text = path.read_text()
        if text.count(begin) != 1 or text.count(end) != 1:
            return ["corpus/README.md: missing or duplicate generated inventory markers"]
        if text.index(end) < text.index(begin):
            return ["corpus/README.md: generated inventory markers out of order"]
        start, stop = text.index(begin), text.index(end) + len(end)
        if write:
            path.write_text(text[:start] + expected + text[stop:])
        elif text[start:stop] != expected:
            return ["corpus/README.md inventory is stale; run python3 scripts/check_docs.py --write-status"]
    except (OSError, ValueError, TypeError, KeyError) as failure:
        return [f"corpus overview: {failure}"]
    return []


def main() -> int:
    if sys.argv[1:] not in ([], ["--write-status"]):
        print("usage: check_docs.py [--write-status]", file=sys.stderr)
        return 2
    status_errors = check_status(ROOT, write=sys.argv[1:] == ["--write-status"])
    errors, counts = check_links(ROOT, markdown_paths(ROOT))
    errors.extend(check_agents_budget(ROOT))
    errors.extend(status_errors)
    errors.extend(check_release_doc_links(ROOT))
    errors.extend(check_corpus_overview(ROOT, write=sys.argv[1:] == ["--write-status"]))
    lean_errors, modules = check_lean(ROOT)
    errors.extend(lean_errors)
    # Loaded here so the standalone checker can reuse lean_imports above.
    from check_lean_kernel import check_kernel
    kernel_errors, kernel_modules = check_kernel(ROOT)
    errors.extend(kernel_errors)
    modules += kernel_modules
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
