#!/usr/bin/env python3
"""Validate a rendered mdBook's local links and the style of its sources.

The rendered check covers local href/src targets, without network access. It
checks HTML files and assets, not CSS imports, JavaScript-generated links,
or the contents of external URLs. The first <base href> controls relative URLs,
including fragment-only references. Scheme URLs (including data/javascript)
and network-path URLs are outside this local-link check and are never executed.

The source check applies the mechanical rules of the style guide in
docs/src/building.md to the chapters that SUMMARY.md lists. It reads prose
only: it does not judge meaning, and passing it is not a review.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
"""

import argparse
from dataclasses import dataclass, field
from html.parser import HTMLParser
from pathlib import Path
import re
import sys
from urllib.parse import unquote, urlsplit


DEFAULT_ROOT = Path(__file__).resolve().parents[1] / "target" / "mdbook"
DEFAULT_SOURCE = Path(__file__).resolve().parents[1] / "docs" / "src"
HTML_SUFFIXES = {".html", ".htm"}

# Chapters that keep the wording their adopted records or retained drafts bind.
EXEMPT = frozenset({
    "design/initial-guarantees.md",
    "design/initial-interpretations.md",
    "design/ratification.md",
    "imaginary-v1/index.md",
    "imaginary-v1/requirements.md",
    "reference/authority.md",
})
# Chapters that predate the style guide. Remove a chapter from this list in
# the change that rewrites it; a listed chapter that passes is an error.
PENDING = frozenset()

STATUS_WORD = re.compile(
    r"\b(now|new|newly|currently|still|remain|remains|remained|remaining)\b", re.IGNORECASE)
TRACKER_REFERENCE = re.compile(r"(?<![\w&/])#\d+\b|/(?:issues|pull)/\d+")
RAW_TAG = re.compile(r"</?([A-Za-z][A-Za-z0-9]*)>")
HTML_TAGS = frozenset({"a", "br", "details", "kbd", "sub", "summary", "sup"})
FENCE_LABELS = frozenset({"json", "qli", "sh", "text", "toml"})
MAX_PARAGRAPH_WORDS = 120


@dataclass(frozen=True)
class Reference:
    attribute: str
    target: str
    line: int
    is_base: bool = False


@dataclass
class Page:
    anchors: set[str] = field(default_factory=set)
    references: list[Reference] = field(default_factory=list)
    base: Reference | None = None


class BookHTMLParser(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.page = Page()

    def handle_starttag(self, tag, attrs):
        for attribute, value in attrs:
            if value is None:
                continue
            if attribute == "id" or (tag == "a" and attribute == "name"):
                self.page.anchors.add(value)
            if attribute in {"href", "src"}:
                reference = Reference(attribute, value, self.getpos()[0],
                                      tag == "base" and attribute == "href")
                self.page.references.append(reference)
                if reference.is_base and self.page.base is None:
                    self.page.base = reference

    def handle_startendtag(self, tag, attrs):
        self.handle_starttag(tag, attrs)


@dataclass(frozen=True)
class URLBase:
    path: Path
    directory: bool = False
    external: bool = False
    fragment: str = ""


def resolve_local(root: Path, base: URLBase, target: str):
    """Return (URL base, fragment), or None for a nonlocal URL.

    Keep a base URL's trailing slash independently of whether its path exists:
    <base> selects URL resolution and need not itself be a loadable resource.
    Resolve decoded paths before checking containment, including symlinks.
    """
    target = target.strip().replace("\\", "/")
    parts = urlsplit(target)
    if parts.scheme or parts.netloc or base.external:
        return None
    path = unquote(parts.path, errors="strict").replace("\\", "/")
    fragment = (base.fragment if not target
                else unquote(parts.fragment, errors="strict"))
    if not path:
        destination = base.path
        directory = base.directory
    elif path.startswith("/"):
        destination = root / path.lstrip("/")
        directory = path.endswith("/")
    else:
        destination = (base.path if base.directory else base.path.parent) / path
        directory = path.endswith("/")
    destination = destination.resolve()
    if not destination.is_relative_to(root):
        raise ValueError("target escapes the rendered book")
    return URLBase(destination, directory, fragment=fragment), fragment


def check_book(root: Path) -> tuple[list[str], dict[str, int]]:
    root = root.resolve()
    errors = []
    counts = {"html_files": 0, "local_links": 0, "anchors": 0}
    if not root.is_dir():
        return [f"rendered book directory is missing: {root}"], counts

    for name in ("index.html", "print.html"):
        required = root / name
        if not required.is_file():
            errors.append(f"missing required rendered page: {name}")
        elif not required.resolve().is_relative_to(root):
            errors.append(f"required rendered page escapes the book: {name}")

    pages = {}
    try:
        candidates = sorted(p for p in root.rglob("*")
                            if p.suffix.lower() in HTML_SUFFIXES and p.is_file())
    except OSError as failure:
        return errors + [f"cannot enumerate rendered HTML: {failure}"], counts
    for path in candidates:
        try:
            resolved = path.resolve()
            if not resolved.is_relative_to(root):
                raise ValueError("HTML file escapes the rendered book")
            parser = BookHTMLParser()
            parser.feed(path.read_text(encoding="utf-8"))
            parser.close()
            pages[resolved] = parser.page
            counts["html_files"] += 1
        except (OSError, ValueError, RuntimeError) as failure:
            errors.append(f"{path.relative_to(root)}: cannot read HTML: {failure}")

    for source, page in sorted(pages.items()):
        document_base = URLBase(source)
        effective_base = document_base
        if page.base is not None:
            try:
                resolved = resolve_local(root, document_base, page.base.target)
                effective_base = (resolved[0] if resolved is not None
                                  else URLBase(source, external=True))
            except (OSError, ValueError, RuntimeError) as failure:
                errors.append(f"{source.relative_to(root)}:{page.base.line}: "
                              f"invalid base href {page.base.target!r}: {failure}")
                continue

        for reference in page.references:
            # A base href is a resolution context, not a fetched asset. The
            # first one has already been checked; HTML ignores later bases.
            if reference.is_base:
                continue
            location = f"{source.relative_to(root)}:{reference.line}"
            try:
                resolved = resolve_local(root, effective_base, reference.target)
                if resolved is None:
                    continue
                counts["local_links"] += 1
                target, fragment = resolved
                destination = target.path
                if target.directory or destination.is_dir():
                    destination = (destination / "index.html").resolve()
                if not destination.is_relative_to(root):
                    raise ValueError("target escapes the rendered book")
                if not destination.is_file():
                    errors.append(f"{location}: missing {reference.attribute} target "
                                  f"{reference.target!r} ({destination.relative_to(root)})")
                    continue
                if fragment and destination.suffix.lower() in HTML_SUFFIXES:
                    counts["anchors"] += 1
                    target_page = pages.get(destination)
                    if target_page is None:
                        errors.append(f"{location}: cannot check HTML anchor in "
                                      f"{reference.target!r}")
                    elif fragment not in target_page.anchors:
                        errors.append(f"{location}: missing anchor {fragment!r} in "
                                      f"{destination.relative_to(root)} "
                                      f"({reference.attribute} {reference.target!r})")
            except (OSError, ValueError, RuntimeError) as failure:
                errors.append(f"{location}: invalid {reference.attribute} "
                              f"{reference.target!r}: {failure}")
    return errors, counts


def summary_chapters(source: Path) -> list[str]:
    """Return the chapter paths that SUMMARY.md links, in order, once each."""
    summary = (source / "SUMMARY.md").read_text(encoding="utf-8")
    return list(dict.fromkeys(re.findall(r"\]\(([^)#\s:]+\.md)(?:#[^)\s]*)?\)", summary)))


def _blank(match: re.Match) -> str:
    """Erase a match but keep its length and line breaks, so offsets stay valid."""
    return re.sub(r"[^\n]", " ", match.group(0))


def chapter_blocks(text: str):
    """Yield (kind, line, text, section) for the prose blocks of one chapter.

    Kinds are "paragraph", "table", "fence" (text is the label) and
    "unclosed". A list item or a quoted block is its own paragraph. Fenced
    code is not prose. `section` is the title of the enclosing level-two
    heading, or "" before the first one.
    """
    section, fence, start, lines = "", None, 0, []

    def flush():
        nonlocal lines
        if lines:
            yield "paragraph", start, "\n".join(lines), section
        lines = []

    for number, raw in enumerate(text.split("\n"), 1):
        line = re.sub(r"^\s*(>\s?)+", "", raw)
        marker = re.match(r"\s*(`{3,}|~{3,})(.*)$", line)
        if fence is not None:
            if marker and marker[1][0] == fence[0] and len(marker[1]) >= len(fence) \
                    and not marker[2].strip():
                fence = None
            continue
        if marker:
            yield from flush()
            fence = marker[1]
            yield "fence", number, marker[2].strip(), section
            continue
        heading = re.match(r"(#{1,6})\s+(.*)$", line)
        if heading or not line.strip():
            yield from flush()
            if heading and len(heading[1]) == 2:
                section = heading[2].strip()
            continue
        if line.lstrip().startswith("|"):
            yield from flush()
            yield "table", number, line, section
            continue
        if re.match(r"\s*(?:[-*+]|\d+\.)\s", line) or (raw.lstrip().startswith(">") and not lines):
            yield from flush()
        if not lines:
            start = number
        lines.append(line)
    yield from flush()
    if fence is not None:
        yield "unclosed", len(text.split("\n")), "", section


def check_chapter(text: str) -> tuple[list[tuple[int, str]], list[tuple[int, str]]]:
    """Return (rendering errors, style errors) as (line, message) pairs."""
    rendering, style = [], []
    for kind, line, block, section in chapter_blocks(text):
        if kind == "unclosed":
            rendering.append((line, "code fence is not closed"))
            continue
        if kind == "fence":
            if block not in FENCE_LABELS:
                style.append((line, f"code fence label {block!r} is not one of "
                                    f"{', '.join(sorted(FENCE_LABELS))}"))
            continue
        if kind == "table":
            for span in re.findall(r"`[^`]*`", block):
                if re.search(r"(?<!\\)\|", span):
                    rendering.append((line, f"{span} holds an unescaped | and ends its "
                                            "table cell; write \\| inside the code span"))
        # Code spans and comments are not prose. Words in double quotation
        # marks mention a word rather than use it, and a link target is a URL.
        visible = re.sub(r"<!--.*?-->", _blank, block, flags=re.DOTALL)
        visible = re.sub(r"`[^`]*`", _blank, visible)

        def at(offset: int) -> int:
            return line + visible.count("\n", 0, offset)

        for match in RAW_TAG.finditer(visible):
            # A type parameter such as <A> is an anchor tag to a browser. Only
            # a lower-case tag is markup here, and <a> needs its attributes.
            markup = match[1] in HTML_TAGS and (match[0].startswith("</") or match[1] != "a")
            if not markup:
                rendering.append((at(match.start()),
                                  f"{match[0]} outside a code span renders as an HTML tag"))
        if section != "History":
            reported = set()  # A link shows a number and names it again in its target.
            for match in TRACKER_REFERENCE.finditer(visible):
                if at(match.start()) not in reported:
                    reported.add(at(match.start()))
                    style.append((at(match.start()), f"Issue or pull request reference "
                                  f"{match[0]!r} outside a History section"))
        prose = re.sub(r"\]\([^)]*\)", _blank, visible)
        prose = re.sub(r"\"[^\"\n]*\"|“[^”\n]*”", _blank, prose)
        for match in STATUS_WORD.finditer(prose):
            style.append((at(match.start()), f"status word {match[0]!r}; state what "
                          "the language does, and keep history in a History section"))
        words = len(prose.split()) + block.count("`") // 2
        if kind == "paragraph" and words > MAX_PARAGRAPH_WORDS:
            style.append((line, f"paragraph has {words} words; "
                                f"the limit is {MAX_PARAGRAPH_WORDS}"))
    return rendering, style


def check_sources(source: Path, exempt=EXEMPT, pending=PENDING) -> tuple[list[str], dict[str, int]]:
    """Apply the style guide's mechanical rules to the chapters of SUMMARY.md.

    Every chapter is checked for text that renders wrongly. A chapter in
    neither list must also keep the style rules. A pending chapter may break
    them, and must leave the list once it keeps them.
    """
    counts = {"checked": 0, "pending": 0, "exempt": 0}
    try:
        chapters = summary_chapters(source)
    except OSError as failure:
        return [f"cannot read the book summary: {failure}"], counts
    errors = [f"{name}: listed as exempt or pending, but SUMMARY.md has no such chapter"
              for name in sorted((exempt | pending) - set(chapters))]
    errors += [f"{name}: listed as both exempt and pending" for name in sorted(exempt & pending)]
    for name in chapters:
        try:
            text = (source / name).read_text(encoding="utf-8")
        except (OSError, UnicodeError) as failure:
            errors.append(f"{name}: cannot read the chapter: {failure}")
            continue
        rendering, style = check_chapter(text)
        errors += [f"{name}:{line}: {message}" for line, message in rendering]
        if name in exempt:
            counts["exempt"] += 1
        elif name in pending:
            counts["pending"] += 1
            if not style:
                errors.append(f"{name}: keeps the style rules; remove it from PENDING "
                              "in scripts/check_book.py")
        else:
            counts["checked"] += 1
            errors += [f"{name}:{line}: {message}" for line, message in style]
    return errors, counts


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=DEFAULT_ROOT,
                        help="rendered book directory (default: repository target/mdbook)")
    parser.add_argument("--source", type=Path, default=DEFAULT_SOURCE,
                        help="book source directory (default: repository docs/src)")
    args = parser.parse_args(argv)
    errors, counts = check_book(args.root)
    # The two lists name chapters of this repository's book. Another book has none.
    own = args.source.resolve() == DEFAULT_SOURCE.resolve()
    source_errors, chapters = check_sources(
        args.source, EXEMPT if own else frozenset(), PENDING if own else frozenset())
    errors += source_errors
    if errors:
        for error in errors:
            print(error, file=sys.stderr)
        return 1
    print(f"rendered book: {counts['html_files']} HTML files, "
          f"{counts['local_links']} local links, {counts['anchors']} anchors checked")
    print(f"book sources: {chapters['checked']} chapters keep the style rules, "
          f"{chapters['pending']} pending, {chapters['exempt']} exempt")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
