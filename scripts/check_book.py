#!/usr/bin/env python3
"""Validate local href/src targets in a rendered mdBook, without network access.

This checks HTML files and assets, not CSS imports, JavaScript-generated links,
or the contents of external URLs. The first <base href> controls relative URLs,
including fragment-only references. Scheme URLs (including data/javascript)
and network-path URLs are outside this local-link check and are never executed.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""

import argparse
from dataclasses import dataclass, field
from html.parser import HTMLParser
from pathlib import Path
import sys
from urllib.parse import unquote, urlsplit


DEFAULT_ROOT = Path(__file__).resolve().parents[1] / "target" / "mdbook"
HTML_SUFFIXES = {".html", ".htm"}


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


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=DEFAULT_ROOT,
                        help="rendered book directory (default: repository target/mdbook)")
    args = parser.parse_args(argv)
    errors, counts = check_book(args.root)
    if errors:
        for error in errors:
            print(error, file=sys.stderr)
        return 1
    print(f"rendered book: {counts['html_files']} HTML files, "
          f"{counts['local_links']} local links, {counts['anchors']} anchors checked")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
