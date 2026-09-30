"""Regression checks for stale-reference diagnostics, without Rust dependencies."""

from pathlib import Path
import json
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
from check_docs import check_lean, check_links, check_status, markdown_anchors, markdown_paths, render_status


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

    def check(self, markdown):
        return check_links(self.root, [self.write("docs/rules.md", markdown)])

    def test_corpus_links_are_part_of_normal_document_discovery(self):
        self.write("corpus/source/case/README.md", "[missing](deleted.qli)\n")
        errors, counts = check_links(self.root, markdown_paths(self.root))
        self.assertEqual(counts["links"], 1)
        self.assertEqual(len(errors), 1)
        self.assertIn("corpus/source/case/README.md:1: missing target deleted.qli", errors[0])

    def status_fixture(self):
        self.write("Cargo.toml", '[package]\nversion = "0.1.5"\n')
        self.write("lean/lakefile.toml", 'version = "0.1.5"\n')
        self.write("lean-kernel/lakefile.toml", 'version = "0.1.5"\n')
        self.write("python/pyproject.toml", 'version = "0.1.5"\n')
        self.write("python/qleisli/__init__.py", '__version__ = "0.1.5"\n')
        for notice in ["LICENSE", "NOTICE"]:
            self.write(notice, "fixture attribution\n")
            self.write("python/" + notice, "fixture attribution\n")
        data = {
            "format": 3,
            "release_state": "selected",
            "current": [dict(topic="Use", state="finite", detail="current")],
            "milestones": [dict(id=f"M{i}", state="planned", evidence="direction", open="work") for i in range(6)],
            "inventory": [dict(rule="rule", implementation="code", tests="tests", proof="open")],
        }
        self.write("docs/project-status.json", json.dumps(data))
        return data

    def test_status_drift_is_rejected_without_rewriting_the_view(self):
        self.status_fixture()
        self.assertTrue(check_status(self.root))
        self.assertEqual(check_status(self.root, write=True), [])
        self.assertEqual(check_status(self.root), [])
        path = self.write("docs/current-status.md", "incorrect completion claim\n")
        self.assertIn("stale", check_status(self.root)[0])
        self.assertEqual(path.read_text(), "incorrect completion claim\n")

    def test_status_requires_synchronized_versions(self):
        self.status_fixture()
        self.write("lean/lakefile.toml", 'version = "0.1.4"\n')
        self.assertIn("versions differ", check_status(self.root, write=True)[0])
        self.assertFalse((self.root / "docs/current-status.md").exists())

    def test_current_summary_and_inventory_are_separate_without_history(self):
        self.status_fixture()
        self.assertEqual(check_status(self.root, write=True), [])
        current = (self.root / "docs/current-status.md").read_text()
        self.assertIn("Where we are now", current)
        self.assertFalse((self.root / "docs/status-history.md").exists())
        inventory = (self.root / "docs/rule-inventory.md").read_text()
        self.assertIn("| rule | code | tests | open |", inventory)
        self.assertNotIn("| rule | code | tests | open |", current)
        self.write("docs/rule-inventory.md", "invented proof")
        self.assertIn("rule-inventory.md is stale", check_status(self.root)[0])

    def test_retired_history_schema_is_rejected_without_recreating_it(self):
        data = self.status_fixture()
        data["format"] = 2
        data["history"] = [dict(title="Old report", paragraphs=["superseded"])]
        self.write("docs/project-status.json", json.dumps(data))
        self.assertIn("unsupported", check_status(self.root, write=True)[0])
        self.assertFalse((self.root / "docs/status-history.md").exists())

    def test_status_requires_synchronized_executable_kernel_version(self):
        self.status_fixture()
        self.write("lean-kernel/lakefile.toml", 'version = "0.1.4"\n')
        self.assertIn("versions differ", check_status(self.root, write=True)[0])
        self.assertFalse((self.root / "docs/current-status.md").exists())

    def test_status_requires_synchronized_python_version_and_notices(self):
        for name, content, message in [
            ("python/pyproject.toml", 'version = "0.1.4"\n', "versions differ"),
            ("python/qleisli/__init__.py", '__version__ = "0.1.4"\n', "runtime version differs"),
            ("python/LICENSE", "wrong license\n", "LICENSE differs"),
            ("python/NOTICE", "missing attribution\n", "NOTICE differs"),
        ]:
            with self.subTest(name=name):
                self.status_fixture()
                self.write(name, content)
                self.assertIn(message, check_status(self.root, write=True)[0])
                self.assertFalse((self.root / "docs/current-status.md").exists())

    def test_status_rejects_missing_proof_fields_and_duplicate_milestones(self):
        data = self.status_fixture()
        del data["inventory"][0]["proof"]
        self.write("docs/project-status.json", json.dumps(data))
        self.assertIn("missing or unknown", check_status(self.root)[0])
        data = self.status_fixture()
        data["milestones"][1]["id"] = "M0"
        self.write("docs/project-status.json", json.dumps(data))
        self.assertIn("once, in order", check_status(self.root)[0])

    def test_status_invalid_format_and_cells_are_diagnosed(self):
        for bad in ['{"format":', '{"format": 3}', 'null', '[]']:
            self.status_fixture()
            self.write("docs/project-status.json", bad)
            self.assertTrue(check_status(self.root))
        data = self.status_fixture()
        data["inventory"][0]["proof"] = "open\n| invented row |"
        self.write("docs/project-status.json", json.dumps(data))
        self.assertIn("single-line", check_status(self.root)[0])

    def test_generated_status_references_are_checked_by_normal_link_validation(self):
        data = self.status_fixture()
        data["inventory"][0]["tests"] = "[`deleted_test`](../tests/rules.rs)"
        self.write("docs/project-status.json", json.dumps(data))
        self.write("tests/rules.rs", "#[test]\nfn present_test() {}")
        self.write("docs/rule-inventory.md", render_status(self.root, inventory_only=True))
        errors, _ = check_links(self.root, [self.root / "docs/rule-inventory.md"])
        self.assertTrue(any("missing #[test] function deleted_test" in error for error in errors))

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
