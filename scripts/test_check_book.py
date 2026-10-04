"""Regressions for rendered-book links, independent of mdBook installation.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""

from contextlib import redirect_stderr, redirect_stdout
from io import StringIO
from pathlib import Path
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
from check_book import check_book, main


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
        with redirect_stdout(StringIO()) as output, redirect_stderr(StringIO()) as errors:
            self.assertEqual(main(["--root", str(self.root)]), 0)
        self.assertIn("2 HTML files", output.getvalue())
        self.assertEqual(errors.getvalue(), "")
        (self.root / "print.html").unlink()
        with redirect_stdout(StringIO()), redirect_stderr(StringIO()) as errors:
            self.assertEqual(main(["--root", str(self.root)]), 1)
        self.assertIn("missing required rendered page: print.html", errors.getvalue())


if __name__ == "__main__":
    unittest.main()
