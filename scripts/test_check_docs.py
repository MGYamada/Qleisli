"""Regression checks for stale-reference diagnostics, without Rust dependencies."""

from pathlib import Path
import json
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
from check_docs import check_source_doc_references, check_python_readme_version, check_agents_budget, check_corpus_overview, check_lean, check_links, check_release_doc_links, check_project_metadata, check_docs_layout, check_retired_doc_links, markdown_anchors, markdown_paths


class DocumentationReferences(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name).resolve()

    def write(self, name, content):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding="utf-8")
        return path

    def book_sources(self):
        for name in ("building.md", "lean-backend-plan-v0.3.md",
                     "imaginary-v1/index.md", "imaginary-v1/requirements.md"):
            self.write("docs/src/" + name, "Current chapter source.")

    def check(self, markdown):
        return check_links(self.root, [self.write("docs/rules.md", markdown)])

    def test_qli_comment_paths_require_existing_documents(self):
        self.write("docs/active.md", "# Active")
        self.write("stdlib/src/test.qli", "//! docs/active.md#active docs/gone.md\n// https://github.com/example/blob/v1/docs/old.md\n")
        self.assertEqual(check_source_doc_references(self.root),
                         ["stdlib/src/test.qli:1: missing document docs/gone.md"])

    def test_python_readme_tracks_selected_not_published_version(self):
        self.write("Cargo.toml", '[package]\nversion = "0.2.8"\n')
        for text in ("Qleisli 0.2.7 Rust", "Qleisli 0.2.8 Rust; latest published Rust release is 0.2.8"):
            self.write("python/README.md", text)
            self.assertTrue(check_python_readme_version(self.root))
        self.write("python/README.md", "Qleisli 0.2.8 Rust executable from the same checkout.")
        self.assertEqual(check_python_readme_version(self.root), [])

    def test_python_readme_tracks_exact_prerelease_version(self):
        self.write("Cargo.toml", '[package]\nversion = "0.3.0-alpha"\n')
        self.write("python/README.md", "Qleisli 0.3.0-alpha Rust executable from the same checkout.")
        self.assertEqual(check_python_readme_version(self.root), [])
        for version in ("0.3.0", "0.3.0a0", "0.3.0-alpha.1", "0.3.0-beta", "0.2.9"):
            self.write("python/README.md", f"Qleisli {version} Rust executable from the same checkout.")
            self.assertTrue(check_python_readme_version(self.root))

    def test_agents_budget_accepts_exact_limits_and_rejects_hidden_extra_lines(self):
        for name in ("AGENTS.md", "CLAUDE.md"):
            self.write(name, "x" * 5900 + "\n" * 100)
        self.assertEqual(check_agents_budget(self.root), [])
        for name in ("AGENTS.md", "CLAUDE.md"):
            self.write(name, "<!--\n" + "\n" * 99 + "-->\n")
        errors = check_agents_budget(self.root)
        self.assertEqual(len(errors), 2)
        for name, error in zip(("AGENTS.md", "CLAUDE.md"), errors):
            self.assertIn(f"{name}: 101 lines exceeds 100", error)

    def test_agents_budget_counts_utf8_bytes_and_requires_both_files(self):
        errors = check_agents_budget(self.root)
        self.assertEqual(len(errors), 2)
        for name, error in zip(("AGENTS.md", "CLAUDE.md"), errors):
            self.assertIn(f"{name}:", error)
            self.write(name, "あ" * 2001 + "\n")
        errors = check_agents_budget(self.root)
        self.assertEqual(len(errors), 2)
        for name, error in zip(("AGENTS.md", "CLAUDE.md"), errors):
            self.assertIn(f"{name}: 6004 UTF-8 bytes exceeds 6000", error)

    def test_agent_instructions_reject_drift_and_a_missing_or_invalid_mirror(self):
        for name in ("AGENTS.md", "CLAUDE.md"):
            with self.subTest(name=name):
                for peer in ("AGENTS.md", "CLAUDE.md"):
                    self.write(peer, "Same working rules.\n")
                path = self.write(name, "Different working rules.\n")
                self.assertIn("must be byte-for-byte identical", check_agents_budget(self.root)[0])
                path.unlink()
                self.assertEqual(len(check_agents_budget(self.root)), 1)
                self.assertIn(f"{name}:", check_agents_budget(self.root)[0])
                path.write_bytes(b"\xff")
                self.assertEqual(len(check_agents_budget(self.root)), 1)
                self.assertIn(f"{name}:", check_agents_budget(self.root)[0])

    def test_corpus_links_are_part_of_normal_document_discovery(self):
        self.write("corpus/source/case/README.md", "[missing](deleted.qli)\n")
        errors, counts = check_links(self.root, markdown_paths(self.root))
        self.assertEqual(counts["links"], 1)
        self.assertEqual(len(errors), 1)
        self.assertIn("corpus/source/case/README.md:1: missing target deleted.qli", errors[0])

    def test_corpus_inventory_is_derived_and_stale_views_reject(self):
        self.write("corpus/manifest.json", json.dumps({"cases": [{"kind": "unitary"}, {"kind": "observe"}]}))
        self.write("corpus/semantic_faults/manifest.json", json.dumps({"cases": [{}]}))
        path = self.write("corpus/README.md", "intro\n<!-- corpus-inventory:start -->\nold total\n<!-- corpus-inventory:end -->\nend\n")
        self.assertIn("stale", check_corpus_overview(self.root)[0])
        self.assertEqual(check_corpus_overview(self.root, write=True), [])
        self.assertIn("| 2 | 1 | 1 | 1 |", path.read_text())
        self.assertEqual(check_corpus_overview(self.root), [])
        self.write("corpus/manifest.json", json.dumps({"cases": [{"kind": "unitary"}]}))
        self.assertTrue(check_corpus_overview(self.root))

    def test_missing_corpus_markers_do_not_allow_a_silent_rewrite(self):
        self.write("corpus/manifest.json", '{"cases": []}')
        self.write("corpus/semantic_faults/manifest.json", '{"cases": []}')
        path = self.write("corpus/README.md", "historical prose\n")
        self.assertIn("markers", check_corpus_overview(self.root, write=True)[0])
        self.assertEqual(path.read_text(), "historical prose\n")

    def test_swapped_corpus_markers_reject_without_rewriting_in_both_modes(self):
        self.write("corpus/manifest.json", '{"cases": []}')
        self.write("corpus/semantic_faults/manifest.json", '{"cases": []}')
        original = "intro\n<!-- corpus-inventory:end -->\nprose between\n<!-- corpus-inventory:start -->\nend\n"
        path = self.write("corpus/README.md", original)
        for write in (False, True):
            self.assertIn("markers out of order", check_corpus_overview(self.root, write=write)[0])
            self.assertEqual(path.read_text(), original)

    def test_package_doc_links_reject_previous_and_future_tags(self):
        self.write("Cargo.toml", '[package]\nversion = "0.2.5"\n')
        self.write("src/lib.rs", "//! [trust](https://github.com/MGYamada/Qleisli/blob/v0.2.4/TRUST_BOUNDARY.md)\n")
        self.write("README.crates.md", "[quick reference](https://github.com/MGYamada/Qleisli/blob/v0.3.0/docs/qli-quick-reference.md)\n")
        errors = check_release_doc_links(self.root)
        self.assertEqual(len(errors), 2)
        self.assertIn("src/lib.rs:1: documentation tag v0.2.4", errors[0])
        self.assertIn("README.crates.md:1: documentation tag v0.3.0", errors[1])

    def test_package_doc_links_accept_matching_and_independent_targets(self):
        self.write("Cargo.toml", '[package]\nversion = "0.2.5"\n')
        self.write("src/lib.rs", "//! [trust](https://github.com/MGYamada/Qleisli/blob/v0.2.5/TRUST_BOUNDARY.md)\n")
        self.write("README.crates.md", "[current](https://github.com/MGYamada/Qleisli/blob/main/README.md)\n[release history](https://github.com/MGYamada/Qleisli/releases/tag/v0.2.4)\n")
        self.assertEqual(check_release_doc_links(self.root), [])

    def metadata_fixture(self):
        self.write("Cargo.toml", '[package]\nversion = "0.2.9"\n')
        self.write("lean/lakefile.toml", 'version = "0.2.9"\n')
        self.write("lean-kernel/lakefile.toml", 'version = "0.2.9"\n')
        self.write("python/pyproject.toml", 'version = "0.2.9"\n')
        self.write("python/qleisli/__init__.py", '__version__ = "0.2.9"\n')
        for name in ("LICENSE", "NOTICE"):
            self.write(name, "attribution\n")
            self.write("python/" + name, "attribution\n")

    def test_metadata_does_not_require_or_recreate_retired_docs(self):
        self.metadata_fixture()
        self.assertEqual(check_project_metadata(self.root), [])
        self.assertFalse((self.root / "docs").exists())
        self.assertFalse((self.root / "docs-old").exists())

    def test_metadata_still_checks_versions_runtime_and_notices(self):
        for name, text, diagnostic in [
            ("lean/lakefile.toml", 'version = "0.2.8"', "versions differ"),
            ("lean-kernel/lakefile.toml", 'version = "0.2.8"', "versions differ"),
            ("python/pyproject.toml", 'version = "0.2.8"', "versions differ"),
            ("python/qleisli/__init__.py", '__version__ = "0.2.8"', "runtime version differs"),
            ("python/LICENSE", "wrong", "LICENSE differs"),
            ("python/NOTICE", "wrong", "NOTICE differs"),
        ]:
            with self.subTest(name=name):
                self.metadata_fixture()
                self.write(name, text)
                self.assertIn(diagnostic, check_project_metadata(self.root)[0])

    def test_docs_layout_retains_drafts_and_requested_backend_plan(self):
        self.assertTrue(check_docs_layout(self.root))
        self.book_sources()
        self.write("docs/src/imaginary-v1/nested/draft.md", "draft")
        self.assertEqual(check_docs_layout(self.root), [])
        self.write("docs/current-guide.md", "New documentation derived from current source and proofs.")
        self.assertEqual(check_docs_layout(self.root), [])

    def test_docs_layout_rejects_resurrected_retired_tree(self):
        self.book_sources()
        retired = self.root / "docs-old"
        retired.mkdir()
        self.assertIn("must remain deleted", check_docs_layout(self.root)[0])
        retired.rmdir()
        retired.symlink_to(self.root / "absent-history", target_is_directory=True)
        self.assertIn("must remain deleted", check_docs_layout(self.root)[0])

    def test_docs_layout_rejects_second_sources_and_redirects_at_old_locations(self):
        self.book_sources()
        for name in ("docs/README.md", "docs/lean-backend-plan-v0.3.md",
                     "docs/imaginary-v1/README.md", "docs/imaginary-v1/requirements.md"):
            with self.subTest(name=name):
                old = self.write(name, "Use the relocated chapter instead.")
                self.assertTrue(any("relocated originals must remain deleted" in error
                                    for error in check_docs_layout(self.root)))
                old.unlink()
        old = self.root / "docs/README.md"
        old.symlink_to(self.root / "docs/src/building.md")
        self.assertTrue(any("relocated originals must remain deleted" in error
                            for error in check_docs_layout(self.root)))

    def test_retired_doc_links_reject_local_and_pinned_references(self):
        for target in ["docs-old/design.md", "docs/type-system.md", "docs/verification-migration-v0.2.md",
                       "docs/lean-backend-plan-v0.3-copy.md",
                       "docs/README.md", "docs/lean-backend-plan-v0.3.md",
                       "docs/imaginary-v1/README.md", "docs/imaginary-v1/requirements.md",
                       "https://github.com/MGYamada/Qleisli/blob/main/docs/README.md",
                       "https://github.com/MGYamada/Qleisli/blob/main/docs/imaginary-v1/README.md",
                       "docs/%2e%2e/docs-old/design.md",
                       "https://github.com/MGYamada/Qleisli/blob/v0.2.8/docs/type-system.md",
                       "https://github.com/MGYamada/Qleisli/blob/main/docs-old/design.md"]:
            path = self.write("README.md", f"[old]({target})")
            self.assertIn("remove retired document link", check_retired_doc_links(self.root, [path])[0])
        self.book_sources()
        path = self.write("README.md", "[decision](https://github.com/MGYamada/Qleisli/issues/276) "
                          "[draft](docs/src/imaginary-v1/index.md) "
                          "[plan](docs/src/lean-backend-plan-v0.3.md) "
                          "[build](docs/src/building.md) "
                          "[plan online](https://github.com/MGYamada/Qleisli/blob/main/docs/src/lean-backend-plan-v0.3.md) "
                          "[upstream](https://github.com/example/repo/blob/main/docs/types.md)")
        self.assertEqual(check_retired_doc_links(self.root, [path]), [])

    def test_only_existing_immutable_draft_references_survive_the_move(self):
        base = "https://github.com/MGYamada/Qleisli/blob/"
        for name, revision in [(name, "b316a5065527c84f3dbcb059750637e2b14b0965")
                               for name in ("qpe", "grover", "amplitude-estimation", "shor", "quantum-walk", "qsvt")] + [
                                   ("review", "7bfcd36916199b05d5ab11851d38d53375ccf71e")]:
            suffix = f"/docs/imaginary-v1/{name}.md"
            with self.subTest(name=name):
                path = self.write("README.md", f"[historical draft]({base}{revision}{suffix})")
                self.assertEqual(check_retired_doc_links(self.root, [path]), [])
                for other in ("main", "v0.3.0-alpha", "0" * 40):
                    path.write_text(f"[unbound draft]({base}{other}{suffix})")
                    self.assertTrue(check_retired_doc_links(self.root, [path]))
        path.write_text(f"[removed original]({base}{revision}/docs/imaginary-v1/README.md)")
        self.assertTrue(check_retired_doc_links(self.root, [path]))

    def test_new_docs_support_local_and_remote_links(self):
        self.write("docs/guide/README.md", "# New guide derived from code and proofs")
        path = self.write("README.md", "[guide](docs/guide/README.md) "
                          "[online](https://github.com/MGYamada/Qleisli/blob/v0.3.0-alpha/docs/guide/README.md) "
                          "[directory](docs/guide/) "
                          "[online directory](https://github.com/MGYamada/Qleisli/tree/main/docs)")
        self.assertEqual(check_retired_doc_links(self.root, [path]), [])

    def test_all_maintained_markdown_is_discovered_including_new_directories(self):
        names = ["python/README.md", ".github/ci/README.md", "new-area/nested/guide.md"]
        expected = [self.write(name, "[old](../../docs-old/old.md)") for name in names]
        for name in ["docs-old/old.md", "corpus/upstream/source/README.md", "target/build.md",
                     "lean/.lake/package/README.md", ".git/README.md"]:
            self.write(name, "archived or external")
        self.assertEqual(set(markdown_paths(self.root)), set(expected))
        self.assertEqual(len(check_retired_doc_links(self.root, expected[1:2])), 1)

    def test_retired_reference_definitions_html_and_bare_urls_reject(self):
        for markdown in ['[old]: docs-old/old.md', '<a href="docs-old/old.md">old</a>',
                         '<https://github.com/MGYamada/Qleisli/blob/main/docs-old/old.md>']:
            path = self.write("README.md", markdown)
            self.assertTrue(check_retired_doc_links(self.root, [path]))

    def test_direct_declarations_methods_and_attributed_tests(self):
        self.write("src/lower.rs", """
pub(super) enum Value { Unit }
impl Value {
    pub(crate) fn owns_quantum(&self) -> bool { false }
}
""")
        self.write("tests/rules.rs", """
#[test]
// Extra attributes and comments may separate the attribute and function.
#[should_panic(expected = "error")]
fn rejects_duplicate() { panic!("error"); }
""")
        errors, counts = self.check("""
[`Value`](../src/lower.rs) [`owns_quantum`](../src/lower.rs)
[`rejects_duplicate`](../tests/rules.rs)
""")
        self.assertEqual(errors, [])
        self.assertEqual((counts["symbols"], counts["tests"]), (2, 1))

    def test_deleted_or_moved_declaration_is_rejected(self):
        self.write("src/lower.rs", "fn moved_away() {}")
        self.write("src/branch.rs", "fn branch() {}")
        errors, _ = self.check("[`branch`](../src/lower.rs)")
        self.assertEqual(len(errors), 1)
        self.assertIn("docs/rules.md:1: missing Rust declaration branch", errors[0])

    def test_test_reference_requires_the_exact_test_attribute(self):
        self.write("tests/rules.rs", """
#[test]
fn actual_test() {}
fn helper() {}
#[cfg(test)]
fn helper_in_test_build() {}
""")
        errors, _ = self.check("""
[`helper`](../tests/rules.rs)
[`helper_in_test_build`](../tests/rules.rs)
[`removed_test`](../tests/rules.rs)
""")
        self.assertEqual(len(errors), 3)
        self.assertTrue(all("missing #[test] function" in error for error in errors))

    def test_comments_and_source_in_literals_cannot_supply_declarations(self):
        self.write("src/lower.rs", '''
// fn in_line_comment() {}
/* outer /* nested */
fn in_block_comment() {}
*/
const EXAMPLE: &str = r###"
fn in_raw_string() {}
"###;
const QUOTED: &str = "
fn in_string() {}
";
''')
        names = ["in_line_comment", "in_block_comment", "in_raw_string", "in_string"]
        errors, _ = self.check("\n".join(f"[`{name}`](../src/lower.rs)" for name in names))
        self.assertEqual(len(errors), len(names))

    def test_real_anchors_repeated_headings_and_escaped_unicode(self):
        self.write("docs/other.md", '<a id="legacy-rule"></a>\n## Other rule\n')
        errors, counts = self.check("""
## Rule `Q`
## Rule `Q`
## 資源
[local](#rule-q) [second](#rule-q-1) [unicode](#%E8%B3%87%E6%BA%90)
[explicit](other.md#legacy-rule) [heading](other.md#other-rule)
""")
        self.assertEqual(errors, [])
        self.assertEqual(counts["anchors"], 5)
        self.assertEqual(markdown_anchors("## Same\n## Same\n## Same-1\n"),
                         {"same", "same-1", "same-1-1"})

    def test_missing_anchor_and_target_are_rejected(self):
        errors, _ = self.check("## Rule\n[stale](#renamed-rule) [missing](other.md)\n")
        self.assertEqual(len(errors), 2)
        self.assertIn("missing Markdown anchor #renamed-rule", errors[0])
        self.assertIn("missing target other.md", errors[1])

    def test_commented_out_rules_are_not_link_targets(self):
        errors, _ = self.check('''<!--
## Deleted rule
<a id="old-rule"></a>
[removed link](missing.md)
-->
# Current
[stale heading](#deleted-rule)
[stale id](#old-rule)
[current](#current)
''')
        self.assertEqual(len(errors), 2)
        self.assertIn("docs/rules.md:7: missing Markdown anchor #deleted-rule", errors[0])
        self.assertIn("docs/rules.md:8: missing Markdown anchor #old-rule", errors[1])

    def test_fenced_examples_external_links_and_plain_file_labels(self):
        self.write("src/lower.rs", "fn exists() {}")
        errors, counts = self.check("""
```markdown
[example](missing.md)
## Fake rule
```
~~~
[example](another-missing.md)
~~~
[external](https://example.invalid/not-fetched)
[lower.rs](../src/lower.rs)
[`not_a_symbol`](https://example.invalid/example.rs)
""")
        self.assertEqual(errors, [])
        self.assertEqual(counts, dict(links=1, anchors=0, symbols=0, tests=0))
        self.assertEqual(markdown_anchors("```\n## Fake rule\n```\n"), set())

    def test_lean_root_must_reach_every_module_and_resolve_imports(self):
        self.write("lean/Qleisli.lean", "import Qleisli.Missing\n")
        self.write("lean/Qleisli/Unreachable.lean", "")
        errors, count = check_lean(self.root)
        self.assertEqual(count, 2)
        self.assertEqual(errors, ["missing Lean module: Qleisli.Missing",
                                 "Lean module absent from root import/audit: Qleisli.Unreachable"])

    def test_lean_comments_cannot_supply_a_root_import(self):
        self.write("lean/Qleisli/Safe.lean", "")
        self.write("lean/Qleisli/Hidden.lean", "axiom unchecked_claim : False\n")
        comments = [
            "-- import Qleisli.Hidden\n",
            "/-\nimport Qleisli.Hidden\n-/\n",
            "/- outer /- nested -/\nimport Qleisli.Hidden\n-/\n",
            "/- outer\n/-\nimport Qleisli.Hidden\n-/\n-/\n",
            "/- unterminated\nimport Qleisli.Hidden\n",
        ]
        for comment in comments:
            with self.subTest(comment=comment):
                self.write("lean/Qleisli.lean", "import Qleisli.Safe\n" + comment)
                errors, count = check_lean(self.root)
                self.assertEqual(count, 3)
                self.assertEqual(errors, [
                    "Lean module absent from root import/audit: Qleisli.Hidden"
                ])

    def test_lean_real_header_imports_accept_comments_modifiers_and_transitive_edges(self):
        self.write("lean/Qleisli.lean", """
/- License /- nested comment -/ ends here. -/
module
prelude
import Mathlib.Data.List.Basic
public import Qleisli.First -- a trailing comment
meta import /- between tokens -/ Qleisli.Second
import all Qleisli.Third
public meta import Qleisli.Fourth
""")
        self.write("lean/Qleisli/First.lean", "import\n  Qleisli.Leaf/- adjacent -/\n")
        for name in ["Second", "Third", "Fourth", "Leaf"]:
            self.write(f"lean/Qleisli/{name}.lean", "")
        errors, count = check_lean(self.root)
        self.assertEqual((errors, count), ([], 6))

    def test_lean_body_strings_and_quotations_cannot_supply_imports(self):
        self.write("lean/Qleisli/Safe.lean", "")
        self.write("lean/Qleisli/Hidden.lean", "axiom unchecked_claim : False\n")
        bodies = [
            'def example := "\nimport Qleisli.Hidden\n"\n',
            'def example := r##" /- not a comment -/ "\nimport Qleisli.Hidden\n"##\n',
            'def example := s!"\nimport Qleisli.Hidden\n"\n',
            'def example := `(Module.header|\nimport Qleisli.Hidden\n)\n',
            'def example := 0\nimport Qleisli.Hidden\n',
        ]
        for body in bodies:
            with self.subTest(body=body):
                self.write("lean/Qleisli.lean", "import Qleisli.Safe\n" + body)
                errors, _ = check_lean(self.root)
                self.assertEqual(errors, [
                    "Lean module absent from root import/audit: Qleisli.Hidden"
                ])

    def test_lean_documentation_comments_end_the_import_header(self):
        self.write("lean/Qleisli/Hidden.lean", "")
        for opening in ["/--", "/-!"]:
            with self.subTest(opening=opening):
                self.write("lean/Qleisli.lean", f"{opening} Documentation -/\nimport Qleisli.Hidden\n")
                errors, _ = check_lean(self.root)
                self.assertEqual(errors, [
                    "Lean module absent from root import/audit: Qleisli.Hidden"
                ])

    def test_lean_unsupported_quoted_names_cannot_supply_a_module_prefix(self):
        self.write("lean/Qleisli/Prefix.lean", "")
        for name in ["Qleisli.Prefix.«Quoted»", "«Qleisli.Prefix»"]:
            with self.subTest(name=name):
                self.write("lean/Qleisli.lean", f"import {name}\n")
                errors, _ = check_lean(self.root)
                self.assertEqual(errors, [
                    "Lean module absent from root import/audit: Qleisli.Prefix"
                ])


if __name__ == "__main__":
    unittest.main()
