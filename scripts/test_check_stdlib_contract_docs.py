"""Mutation regressions for contract linting, without quantum/proof dependencies.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""

from pathlib import Path
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
from check_stdlib_contract_docs import ASPECT_STATUSES, SECTIONS, check_contract_docs, check_document


class ContractDocumentation(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name).resolve()
        self.write("stdlib/src/pilot.qli", "pub unitary fn pilot(q: Q<Bit>) -> Q<Bit> { q }\n")
        self.write("docs/result.json", "{}\n")
        self.write("STDLIB.md", "# Conventions\n")
        self.text = "# Pilot\n\n"
        for name in SECTIONS:
            body = "Explicit scope and pending obligation."
            if name == "Interface and encoding":
                body = "[Source](../../stdlib/src/pilot.qli); consume/return Q<Bit>."
            if name == "Validation and proof status":
                body = "| Aspect | Status | Scope and evidence |\n| --- | --- | --- |\n"
                body += "\n".join(f"| {aspect} | pending | Scope and missing obligation. |"
                                  for aspect in ASPECT_STATUSES)
            self.text += f"## {name}\n\n{body}\n\n"
        self.path = self.write("docs/stdlib-contract-examples/qft2.md", self.text)

    def write(self, name, text):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")
        return path

    def lint(self, text):
        self.path.write_text(text, encoding="utf-8")
        return check_document(self.root, self.path)

    def test_explicit_open_proofs_are_valid(self):
        self.assertEqual(self.lint(self.text), [])

    def test_missing_and_duplicate_fields_reject(self):
        for text in [self.text.replace("## Approximation", "## Removed"),
                     self.text + "## Meaning\n\nSecond contract.\n"]:
            self.assertTrue(self.lint(text))

    def test_comments_and_fenced_prompts_cannot_supply_missing_fields(self):
        for wrapper in ["<!--\n## Approximation\nNone.\n-->",
                        "```md\n## Approximation\nNone.\n```"]:
            text = self.text.replace("## Approximation", "## Removed") + wrapper
            self.assertTrue(any("Approximation" in error for error in self.lint(text)))

    def test_empty_fields_and_unfilled_prompts_reject(self):
        for body in ["", "TODO", "[Write the meaning here]"]:
            text = self.text.replace("## Meaning\n\nExplicit scope and pending obligation.",
                                     "## Meaning\n\n" + body)
            self.assertTrue(self.lint(text))

    def test_missing_duplicate_or_undifferentiated_status_rejects(self):
        row = "| Actual IR conformance | pending | Scope and missing obligation. |"
        for text in [self.text.replace(row, ""), self.text.replace(row, row + "\n" + row),
                     self.text.replace(row, row.replace("pending", "verified")),
                     self.text.replace(row, "| Actual IR conformance | pending | |")]:
            self.assertTrue(self.lint(text))

    def test_status_dimensions_do_not_substitute_for_each_other(self):
        text = self.text.replace("| Actual IR conformance | pending |",
                                 "| Actual IR conformance | tested |")
        self.assertTrue(any("unsupported status" in error for error in self.lint(text)))

    def test_malformed_table_cannot_look_like_scoped_status(self):
        for text in [self.text.replace("| Aspect | Status | Scope and evidence |", ""),
                     self.text.replace("| --- | --- | --- |", ""),
                     self.text.replace("| Aspect | Status | Scope and evidence |",
                                       "| Aspect | verified |"),
                     self.text.replace("| Actual IR conformance | pending |",
                                       "| Actual IR conformance | pending | extra |")]:
            self.assertTrue(self.lint(text))

    def test_completed_status_requires_link_but_not_proof_replay(self):
        text = self.text.replace("| Semantic tests | pending | Scope and missing obligation. |",
                                 "| Semantic tests | tested | Small inputs, not a proof. |")
        self.assertTrue(any("evidence link" in error for error in self.lint(text)))
        text = text.replace("Small inputs, not a proof.", "Small inputs; [record](../result.json).")
        self.assertEqual(self.lint(text), [])

    def test_source_link_must_be_local_existing_and_inside_repository(self):
        for target in ["../../stdlib/src/missing.qli", "https://example.org/pilot.qli",
                       "../../../outside.qli"]:
            self.assertTrue(any(".qli source link" in error for error in
                                self.lint(self.text.replace("../../stdlib/src/pilot.qli", target))))

    def test_all_pilots_template_and_links_are_checked(self):
        template = self.text.replace("../../stdlib/src/pilot.qli", "../stdlib/src/pilot.qli")
        self.write("docs/stdlib-contract-template.md", template)
        self.write("docs/stdlib-contract-examples/add2.md", self.text)
        self.write("docs/stdlib-contract-examples/and-phase.md", self.text)
        self.assertEqual(check_contract_docs(self.root), ([], 3))
        self.write("docs/stdlib-contract-examples/add2.md", self.text + "[stale](deleted.md)\n")
        self.assertTrue(any("deleted.md" in error for error in check_contract_docs(self.root)[0]))

    def test_deleting_pilot_cannot_silently_reduce_coverage(self):
        errors, count = check_contract_docs(self.root)
        self.assertEqual(count, 1)
        self.assertTrue(any("missing add2.md" in error for error in errors))
        self.assertTrue(any("cannot read contract" in error for error in errors))


if __name__ == "__main__":
    unittest.main()
