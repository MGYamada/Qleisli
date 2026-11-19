"""Regressions for rendered-book links and source style, independent of mdBook installation.

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
"""

from contextlib import redirect_stderr, redirect_stdout
from io import StringIO
from pathlib import Path
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
from check_book import (DEFAULT_SOURCE, EXEMPT, MAX_PARAGRAPH_WORDS, PENDING, check_book,
                        check_chapter, check_sources, main, summary_chapters)


class RenderedBookLinks(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name).resolve() / "book"
        self.write("index.html", '<h1 id="home">Home</h1>')
        self.write("print.html", '<h1 id="print-home">Print</h1>')

    def write(self, name, content):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding="utf-8")
        return path

    def test_missing_build_and_required_pages_fail(self):
        self.assertIn("directory is missing", check_book(self.root / "absent")[0][0])
        (self.root / "index.html").unlink()
        (self.root / "print.html").unlink()
        errors, _ = check_book(self.root)
        self.assertEqual(errors, ["missing required rendered page: index.html",
                                  "missing required rendered page: print.html"])

    def test_local_ids_legacy_names_assets_queries_and_entities(self):
        self.write("chapters/one.html", '<a href="../index.html?theme=x&amp;y=z#home">Home</a>'
                   '<a name="legacy"></a><a href="#legacy">Legacy</a>'
                   '<h2 id="a&amp;b">Heading</h2><a href="#a%26b">Heading</a>'
                   '<link href="../style.css?v=1#ignored">'
                   '<script src="../app.js?v=1"></script><img src="../image.svg#icon"/>')
        for name in ("style.css", "app.js", "image.svg"):
            self.write(name, "Asset; non-HTML fragments are not parsed.")
        errors, counts = check_book(self.root)
        self.assertEqual(errors, [])
        self.assertEqual(counts, {"html_files": 3, "local_links": 6, "anchors": 3})

    def test_missing_anchors_in_chapters_and_print_are_detected(self):
        self.write("chapter.html", '<a href="index.html#gone">Broken</a>')
        self.write("print.html", '<a href="#not-in-print">Broken print</a>')
        errors, _ = check_book(self.root)
        self.assertEqual(len(errors), 2)
        self.assertTrue(any("chapter.html:1: missing anchor 'gone'" in e for e in errors))
        self.assertTrue(any("print.html:1: missing anchor 'not-in-print'" in e for e in errors))

    def test_missing_document_and_asset_are_detected(self):
        self.write("chapter.html", '<a href="missing.html">Missing</a>\n'
                   '<script src="missing.js"></script>')
        errors, _ = check_book(self.root)
        self.assertEqual(len(errors), 2)
        self.assertIn("chapter.html:1: missing href target 'missing.html'", errors[0])
        self.assertIn("chapter.html:2: missing src target 'missing.js'", errors[1])

    def test_literal_and_encoded_escape_reject_even_when_file_exists(self):
        self.write("../outside.html", '<h1 id="exists">Outside</h1>')
        self.write("chapter.html", '<a href="../outside.html">Escape</a>'
                   '<a href="%2e%2e/outside.html">Encoded escape</a>'
                   '<a href="/../outside.html">Root escape</a>'
                   '<a href="..\\outside.html">Backslash escape</a>')
        errors, _ = check_book(self.root)
        self.assertEqual(len(errors), 4)
        self.assertTrue(all("escapes the rendered book" in e for e in errors))

    def test_symlink_asset_cannot_escape_book(self):
        outside = self.write("../outside.svg", "Outside")
        (self.root / "inside.svg").symlink_to(outside)
        self.write("chapter.html", '<img src="inside.svg">')
        errors, _ = check_book(self.root)
        self.assertEqual(len(errors), 1)
        self.assertIn("escapes the rendered book", errors[0])

    def test_percent_encoded_unicode_space_and_fragment(self):
        self.write("章 one.html", '<h1 id="見出し one">Heading</h1>')
        self.write("chapter.html", '<a href="%E7%AB%A0%20one.html#%E8%A6%8B%E5%87%BA%E3%81%97%20one">Link</a>')
        self.assertEqual(check_book(self.root)[0], [])

    def test_root_relative_404_base_and_fragment_use_index(self):
        self.write("style.css", "Style")
        self.write("nested/404.html", '<base href="/">'
                   '<link href="style.css"><a href="/">Home</a>'
                   '<a href="#home">Home heading</a><p>Not found.</p>')
        self.assertEqual(check_book(self.root)[0], [])
        self.write("nested/404.html", '<base href="/">'
                   '<h1 id="not-found">Not found</h1><a href="#not-found">Heading</a>')
        errors, _ = check_book(self.root)
        self.assertEqual(len(errors), 1)
        self.assertIn("missing anchor 'not-found' in index.html", errors[0])

    def test_first_relative_base_controls_paths_and_fragments(self):
        self.write("assets/index.html", '<h1 id="assets">Assets</h1>')
        self.write("assets/image.svg", "Image")
        self.write("nested/page.html", '<base href="../assets/">'
                   '<base href="https://ignored.example/">'
                   '<img src="image.svg"><a href="#assets">Assets</a>')
        self.assertEqual(check_book(self.root)[0], [])
        # A base need not itself exist; only actual href/src resources do.
        self.write("nested/page.html", '<base href="../assets/nonexistent.html">'
                   '<img src="image.svg"><a href="index.html#assets">Assets</a>')
        self.assertEqual(check_book(self.root)[0], [])
        self.write("nested/page.html", '<base href="../../outside/">')
        self.assertIn("invalid base href", check_book(self.root)[0][0])

    def test_external_and_scheme_urls_are_not_fetched_or_executed(self):
        self.write("chapter.html", '<a href="https://example.invalid/gone#missing">External</a>'
                   '<script src="//example.invalid/script.js"></script>'
                   '<a href="mailto:reader@example.invalid">Mail</a>'
                   '<img src="data:image/svg+xml,unparsed">'
                   '<a href="javascript:void(0)">Script</a>')
        self.write("remote.html", '<base href="https://example.invalid/">'
                   '<img src="missing.png"><a href="/missing.html#missing">Remote root</a>')
        errors, counts = check_book(self.root)
        self.assertEqual(errors, [])
        self.assertEqual(counts["local_links"], 0)

    def test_empty_reference_inherits_base_fragment_but_query_replaces_it(self):
        self.write("chapter.html", '<base href="index.html#missing">'
                   '<a href="">Base</a><a href="?theme=light">Document</a>'
                   '<a href="#">Document top</a>')
        errors, counts = check_book(self.root)
        self.assertEqual(len(errors), 1)
        self.assertIn("missing anchor 'missing' in index.html", errors[0])
        self.assertEqual(counts["anchors"], 1)

    def test_cli_root_and_failure_exit_status(self):
        source = self.root.parent / "src"
        source.mkdir()
        (source / "SUMMARY.md").write_text("[Intro](intro.md)\n", encoding="utf-8")
        (source / "intro.md").write_text("# Intro\n\nOne chapter.\n", encoding="utf-8")
        arguments = ["--root", str(self.root), "--source", str(source)]
        with redirect_stdout(StringIO()) as output, redirect_stderr(StringIO()) as errors:
            self.assertEqual(main(arguments), 0)
        self.assertIn("2 HTML files", output.getvalue())
        self.assertIn("1 chapters keep the style rules, 0 pending, 0 exempt", output.getvalue())
        self.assertEqual(errors.getvalue(), "")
        (source / "intro.md").write_text("# Intro\n\nIt now works.\n", encoding="utf-8")
        with redirect_stdout(StringIO()), redirect_stderr(StringIO()) as errors:
            self.assertEqual(main(arguments), 1)
        self.assertIn("intro.md:3: status word 'now'", errors.getvalue())
        (source / "intro.md").write_text("# Intro\n\nOne chapter.\n", encoding="utf-8")
        (self.root / "print.html").unlink()
        with redirect_stdout(StringIO()), redirect_stderr(StringIO()) as errors:
            self.assertEqual(main(arguments), 1)
        self.assertIn("missing required rendered page: print.html", errors.getvalue())


class BookSourceStyle(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.source = Path(self.directory.name).resolve()

    def book(self, **chapters):
        summary = "".join(f"- [{name}]({name}.md)\n" for name in chapters)
        (self.source / "SUMMARY.md").write_text("# Summary\n\n" + summary, encoding="utf-8")
        for name, text in chapters.items():
            (self.source / f"{name}.md").write_text(text, encoding="utf-8")

    def style(self, text):
        return [message for _, message in check_chapter(text)[1]]

    def test_summary_lists_each_linked_chapter_once_without_fragments(self):
        (self.source / "SUMMARY.md").write_text(
            "[A](a.md)\n- [B](part/b.md)\n  - [A again](a.md)\n- [Web](https://example.invalid/x.md)\n"
            "- [Anchor](a.md#part)\n", encoding="utf-8")
        self.assertEqual(summary_chapters(self.source), ["a.md", "part/b.md"])

    def test_status_words_are_reported_in_prose_with_their_line(self):
        _, style = check_chapter("# Title\n\nThe checker\nnow rejects it.\n\n| a | still b |\n")
        self.assertEqual([(line, message.split(";")[0]) for line, message in style],
                         [(4, "status word 'now'"), (6, "status word 'still'")])
        for word in ("New", "newly", "currently", "remain", "remains", "remained", "remaining"):
            self.assertEqual(len(self.style(f"The {word} rule.\n")), 1, word)
        for clean in ("renewal", "known", "nowhere", "remainder", "distill"):
            self.assertEqual(self.style(f"A {clean} word.\n"), [], clean)

    def test_status_words_in_code_quotes_links_and_comments_are_not_prose(self):
        text = ("Use `now` and\n`new\nvalue` here. Do not write \"now\" or “still”.\n"
                "See [the page](https://example.invalid/new/now.html). <!-- still new -->\n\n"
                "```text\nnow new still remains\n```\n\n> ```qli\n> let now = new;\n> ```\n")
        self.assertEqual(check_chapter(text), ([], []))

    def test_tracker_references_belong_in_a_history_section(self):
        body = "See [Issue #12](https://github.com/o/r/issues/12) and #34.\n"
        self.assertEqual(self.style("# T\n\n" + body),
                         ["Issue or pull request reference '#12' outside a History section"])
        self.assertEqual(len(self.style("# T\n\n## Rules\n\nSee o/r/pull/7.\n\nAnd #8.\n")), 2)
        self.assertEqual(self.style("# T\n\n## History\n\n- " + body + "\n### Earlier\n\n#56\n"), [])
        self.assertEqual(len(self.style("# T\n\n## History\n\n#1\n\n## Rules\n\n#2\n")), 1)
        for clean in ("`#12`", "color &#35; or &#123;", "[top](#rules)", "item#12", "a/#12"):
            self.assertEqual(self.style(f"# T\n\n{clean}\n"), [], clean)

    def test_paragraph_limit_counts_list_items_and_quotes_separately(self):
        words = " ".join(["word"] * MAX_PARAGRAPH_WORDS)
        self.assertEqual(self.style(words + "\n"), [])
        self.assertEqual(self.style(words + " more\n"),
                         [f"paragraph has {MAX_PARAGRAPH_WORDS + 1} words; "
                          f"the limit is {MAX_PARAGRAPH_WORDS}"])
        half = " ".join(["word"] * (MAX_PARAGRAPH_WORDS // 2 + 5))
        self.assertEqual(self.style(f"- {half}\n- {half}\n1. {half}\n\n> {half}\n\n{half}\n"), [])
        self.assertEqual(len(self.style(f"- {half}\n  {half}\n")), 1)
        self.assertEqual(self.style(f"| {words} more words | cell |\n"), [])
        self.assertEqual(len(self.style(" ".join(["`code span`"] * (MAX_PARAGRAPH_WORDS + 1)))), 1)

    def test_fences_need_a_known_label_and_must_close(self):
        self.assertEqual(check_chapter("```qli\nfn f() {}\n```\n\n~~~text\n```\n~~~\n"), ([], []))
        self.assertEqual(self.style("```\ncode\n```\n")[0][:26], "code fence label '' is not")
        self.assertEqual(self.style("```rust\ncode\n```\n")[0][:30], "code fence label 'rust' is not")
        rendering, _ = check_chapter("Text.\n\n```qli\nfn f() {}\n")
        self.assertEqual(rendering, [(5, "code fence is not closed")])

    def test_raw_generic_brackets_are_rendering_errors(self):
        rendering, style = check_chapter("General const<T> and\nQ<Bit> here; `Q<Bit>` is fine.\n")
        self.assertEqual(style, [])
        self.assertEqual([(line, message.split(" ")[0]) for line, message in rendering],
                         [(1, "<T>"), (2, "<Bit>")])
        clean = 'Bits<0>, a < b > c, <a id="x"></a>, H<sub>2</sub><br>, <!-- <T> -->\n'
        self.assertEqual(check_chapter(clean), ([], []))

    def test_unescaped_pipe_in_a_table_code_span_is_a_rendering_error(self):
        rendering, style = check_chapter("| Form | Action |\n| --- | --- |\n| `h` | `H|b>` |\n")
        self.assertEqual(style, [])
        self.assertEqual([(line, message.split(" holds")[0]) for line, message in rendering],
                         [(3, "`H|b>`")])
        clean = "| `a \\| b` | plain a or b |\n\nOutside a table, `x|y` and |z| are fine.\n"
        self.assertEqual(check_chapter(clean), ([], []))

    def test_pending_exempt_and_checked_chapters(self):
        self.book(good="# G\n\nFine.\n", old="# O\n\nIt now works.\n", record="# R\n\nStill bound.\n")
        pending, exempt = frozenset({"old.md"}), frozenset({"record.md"})
        errors, counts = check_sources(self.source, exempt, pending)
        self.assertEqual(errors, [])
        self.assertEqual(counts, {"checked": 1, "pending": 1, "exempt": 1})
        errors, _ = check_sources(self.source, frozenset(), frozenset())
        self.assertEqual(len(errors), 2)
        self.assertTrue(errors[0].startswith("old.md:3: status word 'now'"))
        # A pending chapter must leave the list once it keeps the rules.
        (self.source / "old.md").write_text("# O\n\nIt works.\n", encoding="utf-8")
        errors, _ = check_sources(self.source, exempt, pending)
        self.assertEqual(errors, ["old.md: keeps the style rules; remove it from PENDING "
                                  "in scripts/check_book.py"])

    def test_rendering_errors_apply_to_every_chapter_and_lists_must_be_current(self):
        self.book(old="# O\n\nIt now uses Op<A>.\n", record="# R\n\nA const<T> form.\n")
        errors, _ = check_sources(self.source, frozenset({"record.md"}), frozenset({"old.md"}))
        self.assertEqual([error.split(" outside")[0] for error in errors],
                         ["old.md:3: <A>", "record.md:3: <T>"])
        errors, _ = check_sources(self.source, frozenset({"gone.md", "old.md"}),
                                  frozenset({"old.md", "record.md"}))
        self.assertIn("gone.md: listed as exempt or pending, but SUMMARY.md has no such chapter",
                      errors)
        self.assertIn("old.md: listed as both exempt and pending", errors)
        (self.source / "old.md").unlink()
        errors, _ = check_sources(self.source, frozenset(), frozenset())
        self.assertTrue(any(error.startswith("old.md: cannot read the chapter") for error in errors))
        self.assertIn("cannot read the book summary",
                      check_sources(self.source / "absent", frozenset(), frozenset())[0][0])

    def test_repository_lists_name_chapters_of_the_book(self):
        chapters = set(summary_chapters(DEFAULT_SOURCE))
        self.assertEqual(sorted((EXEMPT | PENDING) - chapters), [])
        self.assertEqual(sorted(EXEMPT & PENDING), [])


if __name__ == "__main__":
    unittest.main()
