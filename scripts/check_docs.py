#!/usr/bin/env python3
"""Check Markdown references, Lean imports, and the active documentation layout.

A link labelled with one backticked identifier and targeting a .rs file opts
into declaration checking. Under tests/, it must name a #[test] function.
This is a source-reference check, not a Rust parser or a coverage proof.
"""

from pathlib import Path
import json
import os
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
    """Require identical, compact instructions, including comments and examples."""
    errors = []
    contents = {}
    for name in ("AGENTS.md", "CLAUDE.md"):
        try:
            content = (root / name).read_bytes()
            lines = len(content.decode("utf-8").splitlines())
        except (OSError, UnicodeError) as failure:
            errors.append(f"{name}: {failure}")
            continue
        contents[name] = content
        if lines > AGENTS_MAX_LINES:
            errors.append(f"{name}: {lines} lines exceeds {AGENTS_MAX_LINES}; replace or shorten existing rules")
        if len(content) > AGENTS_MAX_BYTES:
            errors.append(f"{name}: {len(content)} UTF-8 bytes exceeds {AGENTS_MAX_BYTES}; replace or shorten existing rules")
    if len(contents) == 2 and contents["AGENTS.md"] != contents["CLAUDE.md"]:
        errors.append("AGENTS.md and CLAUDE.md must be byte-for-byte identical; update both together")
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


def check_project_metadata(root: Path) -> list[str]:
    """Keep release metadata and notices synchronized without retired status pages."""
    try:
        versions = []
        for manifest in ["Cargo.toml", "lean/lakefile.toml", "lean-kernel/lakefile.toml", "python/pyproject.toml"]:
            match = re.search(r'^version = "([^"]+)"$', (root / manifest).read_text(), re.MULTILINE)
            if not match:
                raise ValueError(f"missing project version in {manifest}")
            versions.append(match[1])
        if len(set(versions)) != 1:
            raise ValueError("Rust, Lean and Python project versions differ")
        native_product = root / "lean-kernel/Protocol/Product.lean"
        if native_product.is_file():
            native_version = re.search(r'^def productVersion : String := "([^"]+)"$', native_product.read_text(), re.MULTILINE)
            if native_version is None or native_version[1] != versions[0]:
                raise ValueError("native runtime product version differs from project manifests")
        python_version = re.search(r'^__version__ = "([^"]+)"$', (root / "python/qleisli/__init__.py").read_text(), re.MULTILINE)
        if python_version is None or python_version[1] != versions[0]:
            raise ValueError("Python runtime version differs from project manifests")
        for notice in ["LICENSE", "NOTICE"]:
            if (root / "python" / notice).read_bytes() != (root / notice).read_bytes():
                raise ValueError(f"Python package {notice} differs from repository {notice}")
    except (OSError, ValueError, TypeError, KeyError) as failure:
        return [f"project metadata: {failure}"]
    return []


def retained_doc(relative: str) -> bool:
    """The only two exceptions surviving the v0.3.0 docs cleanup boundary."""
    return relative == "lean-backend-plan-v0.3.md" or relative.startswith("imaginary-v1/")


def check_docs_layout(root: Path) -> list[str]:
    """Require both cleanup survivors and exclude every other legacy docs path."""
    errors = []
    for name in ("docs/imaginary-v1/README.md", "docs/lean-backend-plan-v0.3.md"):
        if not (root / name).is_file():
            errors.append(f"missing retained document: {name}")
    for path in sorted((root / "docs").rglob("*")):
        if path.is_file() and path.name != ".DS_Store" and not retained_doc(path.relative_to(root / "docs").as_posix()):
            errors.append(f"{path.relative_to(root)}: move retired documentation to docs-old until v0.3.0")
    return errors


def check_retired_doc_links(root: Path, paths: list[Path]) -> list[str]:
    """Retiring documents must not remain dependencies, including pinned web links."""
    errors = []
    for path in paths:
        prose = markdown_prose(path.read_text(encoding="utf-8"))
        targets = [match[2] for match in LINK.finditer(prose)]
        targets += re.findall(r'^ {0,3}\[[^\]]+\]:\s*(<[^>]+>|\S+)', prose, re.MULTILINE)
        targets += re.findall(r'(?:href|src)\s*=\s*[\'"]([^\'"]+)[\'"]', prose)
        targets += re.findall(r'https?://[^\s<>"\)]+', prose)
        for raw in dict.fromkeys(targets):
            target = raw.strip().split(' "', 1)[0].strip("<>")
            url = urlsplit(target)
            retired = False
            if url.scheme or url.netloc:
                remote = re.fullmatch(r"/MGYamada/Qleisli/(?:blob|tree)/[^/]+/(docs(?:-old)?)(?:/(.*))?", unquote(url.path))
                if url.netloc == "github.com" and remote:
                    retired = remote[1] == "docs-old" or not retained_doc(remote[2] or "")
            elif url.path:
                destination = (path.parent / unquote(url.path)).resolve()
                if destination.is_relative_to((root / "docs-old").resolve()):
                    retired = True
                elif destination.is_relative_to((root / "docs").resolve()):
                    retired = not retained_doc(destination.relative_to((root / "docs").resolve()).as_posix())
            if retired:
                errors.append(f"{path.relative_to(root)}: remove retired document link {target}")
    return errors


def markdown_paths(root: Path) -> list[Path]:
    """Discover maintained Markdown, pruning archives, builds and frozen upstream."""
    excluded = {".git", ".lake", "target", "__pycache__", ".venv", "node_modules", ".codex", ".agents"}
    docs = []
    for directory, children, files in os.walk(root, followlinks=False):
        base = Path(directory)
        children[:] = sorted(name for name in children if name not in excluded
                             and not (base / name).is_symlink()
                             and (base / name).relative_to(root).as_posix() not in {"docs-old", "corpus/upstream"})
        docs.extend(base / name for name in files if name.endswith(".md") and not (base / name).is_symlink())
    return sorted(docs)


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


def check_source_doc_references(root: Path) -> list[str]:
    """Check repository document paths in QLI comments, excluding remote URLs."""
    errors = []
    pattern = re.compile(r"(?<![\w/])docs/[A-Za-z0-9_./-]+\.md(?:#[A-Za-z0-9_-]+)?")
    # Source trees only; generated build outputs and historical records are not
    # current documentation. Strings cannot contain // in the QLI grammar.
    for directory in ("stdlib", "examples", "corpus", "tests", "research"):
        for path in sorted((root / directory).rglob("*.qli")):
            if any(part in {"target", ".lake", ".git"} for part in path.parts):
                continue
            for number, line in enumerate(path.read_text().splitlines(), 1):
                if "//" not in line:
                    continue
                comment = re.sub(r"https?://[^\s)>]+", "", line.split("//", 1)[1])
                for match in pattern.finditer(comment):
                    document = match[0].split("#", 1)[0]
                    if not (root / document).is_file():
                        errors.append(f"{path.relative_to(root)}:{number}: missing document {document}")
    return errors


def check_python_readme_version(root: Path) -> list[str]:
    version = tomllib.loads((root / "Cargo.toml").read_text())["package"]["version"]
    text = (root / "python/README.md").read_text()
    mentions = re.findall(r"Qleisli\s+([0-9]+\.[0-9]+\.[0-9]+)\s+Rust", text)
    if not mentions or any(value != version for value in mentions) or "latest published rust release" in text.lower():
        return ["python/README.md: name the selected Rust version; leave publication status to release records"]
    return []


def check_corpus_overview(root: Path, write: bool = False) -> list[str]:
    """Current inventory counts come from manifests, never historical log totals."""
    try:
        manifest = json.loads((root / "corpus/manifest.json").read_text())
        faults = json.loads((root / "corpus/semantic_faults/manifest.json").read_text())
        cases = manifest["cases"]
        unitary = sum(case["kind"] == "unitary" for case in cases)
        begin, end = "<!-- corpus-inventory:start -->", "<!-- corpus-inventory:end -->"
        expected = (f"{begin}\n"
                    "<!-- Generated by scripts/check_docs.py --write-corpus from corpus manifests. -->\n\n"
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
            return ["corpus/README.md inventory is stale; run python3 scripts/check_docs.py --write-corpus"]
    except (OSError, ValueError, TypeError, KeyError) as failure:
        return [f"corpus overview: {failure}"]
    return []


def main() -> int:
    if sys.argv[1:] not in ([], ["--write-corpus"]):
        print("usage: check_docs.py [--write-corpus]", file=sys.stderr)
        return 2
    errors, counts = check_links(ROOT, markdown_paths(ROOT))
    errors.extend(check_agents_budget(ROOT))
    errors.extend(check_project_metadata(ROOT))
    errors.extend(check_docs_layout(ROOT))
    errors.extend(check_retired_doc_links(ROOT, markdown_paths(ROOT) + list((ROOT / "src").rglob("*.rs"))))
    errors.extend(check_release_doc_links(ROOT))
    errors.extend(check_source_doc_references(ROOT))
    errors.extend(check_python_readme_version(ROOT))
    errors.extend(check_corpus_overview(ROOT, write=sys.argv[1:] == ["--write-corpus"]))
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
