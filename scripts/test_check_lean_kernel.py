"""Runtime policy regressions; --compiled also mutates real Lean modules.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from check_lean_kernel import ROOT, TOOLCHAIN, check_kernel, lean_code, source_errors


COMPILED = "--compiled" in sys.argv
if COMPILED:
    sys.argv.remove("--compiled")


class RuntimeSourcePolicy(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.write("QleisliKernel.lean", "import QleisliKernel.Check\n")
        self.write("QleisliKernel/Check.lean", "import Std\ndef check := true\n")
        self.write("Main.lean", "import QleisliKernel\nimport Protocol\n")
        self.write("Protocol.lean", "import Lean.Data.Json\n")
        self.write("Audit.lean", "import QleisliKernel\nimport Main\n")
        self.write("lakefile.toml", 'name = "qleisli_kernel"\nversion = "0.2.0"\n')
        self.write("lake-manifest.json", json.dumps({"packages": []}))
        self.write("lean-toolchain", TOOLCHAIN + "\n")

    def write(self, name, content):
        path = self.root / "lean-kernel" / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding="utf-8")

    def errors(self):
        return check_kernel(self.root)[0]

    def test_separate_transport_imports_are_allowed(self):
        self.assertEqual(check_kernel(self.root), ([], 4))

    def test_reference_semantics_cannot_depend_on_checkers(self):
        self.write("QleisliKernel/Check.lean", "import QleisliKernel.Semantics.Word\ndef check := true\n")
        self.write("QleisliKernel/Semantics/Word.lean", "import Std\ndef meaning := true\n")
        self.assertEqual(self.errors(), [])
        self.write("QleisliKernel/Semantics/Word.lean", "import QleisliKernel.Other\ndef meaning := true\n")
        self.write("QleisliKernel/Other.lean", "import Std\ndef other := true\n")
        self.assertTrue(any("reference semantics imports checker" in e for e in self.errors()))

    def test_comments_and_plain_raw_literals_do_not_trigger_tokens(self):
        source = '''/- extern /- unsafe -/ partial -/
-- native_decide
def explanation := "axiom sorry \\" extern"
def rawText := r##"unsafe /- string -/ \" partial"##
def quote := '\"'
def escape := '\\n'
def apostrophe' := true
'''
        self.assertEqual(source_errors(source), [])
        self.assertEqual(lean_code(source).count("\n"), source.count("\n"))

    def test_complex_reference_models_have_one_way_dependencies(self):
        directory = self.root / "lean/Qleisli/Semantics"
        directory.mkdir(parents=True)
        path = directory / "Instrument.lean"
        path.write_text("import Mathlib.Data.Complex.Basic\nimport QleisliKernel.Semantics.Readout\n")
        self.assertEqual(self.errors(), [])
        for module in ["Qleisli.HierarchicalRoot", "QleisliKernel.Hierarchical.Readout", "Protocol", "Main"]:
            with self.subTest(module=module):
                path.write_text(f"import {module}\n")
                self.assertTrue(any("complex reference semantics imports checker" in e for e in self.errors()))
        # A reference helper cannot hide the forbidden edge from the scan.
        path.write_text("import Qleisli.Semantics.Helper\n")
        (directory / "Helper.lean").write_text("import Qleisli.HierarchicalRoot\n")
        self.assertTrue(any("Helper.lean" in e for e in self.errors()))

    def test_tokens_cannot_hide_behind_comments_or_quoted_names(self):
        for source in ["partial /- note -/ def loop := loop", "@[ /- note -/ extern \"f\"] def f := 0",
                       "attribute [implemented_by /- note -/ replacement] f",
                       "def «unsafe» := 0", "theorem p := by decide + /- note -/ native"]:
            with self.subTest(source=source):
                self.assertTrue(source_errors(source))

    def test_four_escape_hatches_are_rejected_in_backend_modules(self):
        self.write("QleisliKernel.lean", "import QleisliKernel.Check\nimport QleisliKernel.Backend.LeafRealizer\n")
        for token, source in [
                ("unsafe", "private unsafe def implementation : Nat := 1\n"),
                ("partial", "private partial def loop (n : Nat) : Nat := loop (n + 1)\n"),
                ("extern", '@[extern "untrusted_backend"] private def implementation : Nat := 1\n'),
                ("implemented_by", "private def replacement : Nat := 2\n"
                 "@[implemented_by replacement] private def implementation : Nat := 1\n")]:
            with self.subTest(token=token):
                self.write("QleisliKernel/Backend/LeafRealizer.lean", "import Init\n" + source)
                self.assertTrue(any("Backend/LeafRealizer.lean" in error and token in error
                                    for error in self.errors()))

    def test_backend_modules_cannot_be_omitted_from_the_compiled_audit(self):
        self.write("QleisliKernel/Backend/Emit.lean", "import Init\ndef emit : Nat := 1\n")
        self.assertTrue(any("absent from root import/audit: QleisliKernel.Backend.Emit" in error
                            for error in self.errors()))
        self.write("QleisliKernel.lean", "import QleisliKernel.Check\nimport QleisliKernel.Backend.Emit\n")
        self.assertEqual(self.errors(), [])

    def test_build_time_harnesses_cannot_be_runtime_imports(self):
        self.write("Tests.lean", "import QleisliKernel\nexample : true = true := by decide\n")
        for module in ["Audit", "Tests"]:
            with self.subTest(module=module):
                self.write("Main.lean", f"import QleisliKernel\nimport Protocol\nimport {module}\n")
                self.assertTrue(any(f"missing or forbidden kernel import: {module}" in error
                                    for error in self.errors()))

    def test_interpolation_does_not_hide_executable_tokens(self):
        self.assertTrue(source_errors('def text := s!"{by sorry}"'))
        self.assertEqual(source_errors('def text := s!"result {1 + 2}"'), [])

    def test_eval_commands_cannot_execute_during_elaboration(self):
        for command in ['#eval', '#eval!', '# /- note -/ eval', '#eval /- note -/ !']:
            with self.subTest(command=command):
                source = '\n' + command + ' (IO.FS.writeFile "unused" "unused")\n'
                self.assertTrue(any('line 2:' in e for e in source_errors(source)))
                self.write('QleisliKernel/Check.lean', 'import Std\n' + source)
                self.assertTrue(any('forbidden' in e for e in self.errors()))
        self.assertEqual(source_errors('''-- #eval! ignored
/- #eval ignored -/
def explanation := "#eval IO.println"
def rawText := r#"#eval!"#
def eval := 1
#check eval
'''), [])

    def test_unterminated_comments_and_strings_fail_closed(self):
        for source in ["/-", 'def s := "', 'def s := r##"', 'def s := s!"']:
            with self.subTest(source=source):
                self.assertTrue(source_errors(source))

    def test_mathlib_and_unowned_helpers_are_not_runtime_dependencies(self):
        for module in ["Mathlib", "Batteries", "External.Helper"]:
            with self.subTest(module=module):
                self.write("QleisliKernel/Check.lean", f"import {module}\n")
                self.assertTrue(any("forbidden" in error for error in self.errors()))

    def test_pure_code_cannot_import_transport_or_lean_metaprogramming(self):
        for module in ["Protocol", "Main", "Lean", "Lean.Data.Json"]:
            with self.subTest(module=module):
                self.write("QleisliKernel/Check.lean", f"import {module}\n")
                self.assertTrue(self.errors())

    def test_hidden_generated_build_files_do_not_count_as_source(self):
        self.write(".lake/Bad.lean", "axiom bad : False")
        self.assertEqual(self.errors(), [])
        self.write("QleisliKernel/Hidden.lean", "def hidden := true\n")
        self.assertTrue(any("absent from root" in error for error in self.errors()))

    def test_comments_cannot_supply_required_imports(self):
        self.write("QleisliKernel.lean", "-- import QleisliKernel.Check\n")
        self.assertTrue(any("absent from root" in error for error in self.errors()))
        self.write("Audit.lean", "import QleisliKernel\n-- import Main\n")
        self.assertTrue(any("must import both" in error for error in self.errors()))

    def test_import_cycles_and_unknown_owned_module_names_fail(self):
        self.write("QleisliKernel/Check.lean", "import QleisliKernel\n")
        self.assertTrue(any("cyclic" in error for error in self.errors()))
        self.write("Other.lean", "def f := 0\n")
        self.assertTrue(any("unaudited" in error for error in self.errors()))

    def test_reduction_tests_are_checked_but_not_executable_roots(self):
        self.write("Tests.lean", "import QleisliKernel\nexample : true = true := by decide\n")
        self.assertEqual(check_kernel(self.root), ([], 4))
        self.write("Tests.lean", "example : False := by sorry\n")
        self.assertTrue(any("sorry" in error for error in self.errors()))

    def test_dependencies_and_toolchain_are_pinned(self):
        self.write("lakefile.toml", '[[require]]\nname = "mathlib"\n')
        self.write("lake-manifest.json", json.dumps({"packages": [{"name": "mathlib"}]}))
        self.write("lean-toolchain", "leanprover/lean4:v4.31.0\n")
        self.assertEqual(len(self.errors()), 3)


@unittest.skipUnless(COMPILED, "pass --compiled to test actual Lean declaration metadata")
class CompiledAudit(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        result = subprocess.run(["lake", "env", "lean", "--print-prefix"],
                                cwd=ROOT / "lean-kernel", text=True, capture_output=True, check=True)
        cls.lean = Path(result.stdout.strip()) / "bin" / "lean"
        cls.audit_source = (ROOT / "lean-kernel/Audit.lean").read_text(encoding="utf-8")

    def audit(self, body, main="import QleisliKernel\ndef main : IO Unit := pure ()\n",
              *, module="QleisliKernel"):
        """Compile mutations without the source scanner to test metadata independently."""
        with tempfile.TemporaryDirectory(prefix="qleisli-kernel-audit-") as directory:
            root = Path(directory)
            env = dict(os.environ, LEAN_PATH=str(root))
            source = root / (module.replace(".", "/") + ".lean")
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_text("import Init\n" + body, encoding="utf-8")
            modules = [module]
            if module != "QleisliKernel":
                (root / "QleisliKernel.lean").write_text(f"import {module}\n", encoding="utf-8")
                modules.append("QleisliKernel")
            (root / "Main.lean").write_text(main, encoding="utf-8")
            (root / "Audit.lean").write_text(self.audit_source, encoding="utf-8")
            for name in [*modules, "Main"]:
                relative = name.replace(".", "/")
                compiled = subprocess.run([self.lean, "-o", relative + ".olean", relative + ".lean"],
                                          cwd=root, env=env, text=True, capture_output=True)
                self.assertEqual(compiled.returncode, 0, compiled.stdout + compiled.stderr)
            result = subprocess.run([self.lean, "Audit.lean"], cwd=root, env=env,
                                    text=True, capture_output=True)
            return result.returncode, result.stdout + result.stderr

    def test_safe_runtime_declarations_pass(self):
        code, output = self.audit("def value : Nat := 1\n")
        self.assertEqual(code, 0, output)
        self.assertIn("Audited", output)

    def test_compiled_escape_hatches_fail_including_private_helpers(self):
        cases = [
            ("private partial def loop (n : Nat) : Nat := loop (n + 1)\n", "partial project"),
            ("unsafe def value : Nat := 1\n", "unsafe project"),
            ('@[extern "untrusted_audit_test"] def value : Nat := 1\n', "extern implementation"),
            ("def replacement : Nat := 2\n@[implemented_by replacement] def value : Nat := 1\n",
             "implemented_by replacement"),
            ("namespace Other\naxiom forged : False\nend Other\n", "project axiom"),
            ("private theorem unfinished : False := by sorry\n", "forbidden axiom"),
            ("noncomputable def value : Nat := Classical.choice (inferInstance : Nonempty Nat)\n",
             "noncomputable project"),
        ]
        for body, expected in cases:
            with self.subTest(expected=expected):
                code, output = self.audit(body)
                self.assertNotEqual(code, 0, output)
                self.assertIn(expected, output)

    def test_backend_private_declarations_are_audited_by_origin_module(self):
        cases = [
            ("private unsafe def value : Nat := 1\n", "unsafe project"),
            ("private partial def loop (n : Nat) : Nat := loop (n + 1)\n", "partial project"),
            ('@[extern "untrusted_backend"] private def value : Nat := 1\n', "extern implementation"),
            ("private def replacement : Nat := 2\n"
             "@[implemented_by replacement] private def value : Nat := 1\n", "implemented_by replacement"),
        ]
        for body, expected in cases:
            with self.subTest(expected=expected):
                # The declaration namespace deliberately differs from its audited module.
                code, output = self.audit("namespace Outside\n" + body + "end Outside\n",
                                          module="QleisliKernel.Backend.LeafRealizer")
                self.assertNotEqual(code, 0, output)
                self.assertIn(expected, output)
                self.assertIn("Outside", output)

    def test_axiom_free_theorems_do_not_authorize_runtime_replacements(self):
        for prefix, expected in [
                ("def replacement : Nat := 2\n@[implemented_by replacement]", "implemented_by replacement"),
                ('@[extern "untrusted_backend"]', "extern implementation")]:
            with self.subTest(expected=expected):
                body = prefix + " def value : Nat := 1\n" + """
theorem kernelDefinition : value = 1 := rfl
/-- info: 'kernelDefinition' does not depend on any axioms -/
#guard_msgs in
#print axioms kernelDefinition
"""
                code, output = self.audit(body, module="QleisliKernel.Backend.Emit")
                self.assertNotEqual(code, 0, output)
                self.assertIn(expected, output)

    def test_plain_backend_definition_generated_helpers_are_audited(self):
        # Pinned Lean generates a partial _unsafe_rec helper for this total
        # equation-compiler definition. A source keyword check cannot see it.
        body = """
inductive Atom where
  | unit | bit | bits (n : Nat) | tuple (n : Nat)
def width : List Atom → Nat
  | [] => 0
  | .unit :: rest | .tuple _ :: rest => width rest
  | .bit :: rest => 1 + width rest
  | .bits n :: rest => n + width rest
"""
        self.assertEqual(source_errors(body), [])
        code, output = self.audit(body, module="QleisliKernel.Backend.Generated")
        self.assertNotEqual(code, 0, output)
        self.assertIn("width._unsafe_rec", output)
        self.assertIn("partial project", output)

    def test_native_proof_in_transport_is_still_rejected(self):
        main = ("import QleisliKernel\nimport Lean\n"
                "theorem nativeProof : 1 + 1 = 2 := by native_decide\n"
                "def main : IO Unit := pure ()\n")
        code, output = self.audit("def value : Nat := 1\n", main)
        self.assertNotEqual(code, 0, output)
        self.assertTrue("forbidden axiom" in output or "project axiom" in output, output)

    def test_compiled_pure_import_closure_cannot_add_lean_metaprogramming(self):
        code, output = self.audit("import Lean\ndef value : Nat := 1\n")
        self.assertNotEqual(code, 0, output)
        self.assertIn("forbidden runtime import Lean", output)


if __name__ == "__main__":
    unittest.main()
