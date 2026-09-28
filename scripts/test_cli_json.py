#!/usr/bin/env python3
"""Independent JSON decoding and X1 CLI conformance; pass a built binary path."""

import json
import math
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

BINARY = str(Path(sys.argv.pop(1)).resolve()) if len(sys.argv) > 1 else "target/debug/qleisli"


class JsonCliTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix="qleisli-json-日本語-")
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)

    def source(self, source):
        (self.root / "main.qli").write_bytes(source.encode("utf-8"))

    def invoke(self, *args, status=0):
        output = subprocess.run([BINARY, *args], capture_output=True, check=False)
        self.assertEqual(output.returncode, status, output)
        self.assertEqual(output.stderr, b"", output)
        self.assertTrue(output.stdout.endswith(b"\n"), output)
        self.assertEqual(output.stdout.count(b"\n"), 1, output)

        def reject_constant(value):
            self.fail(f"Non-JSON number: {value}")

        def unique_object(pairs):
            self.assertEqual(len(pairs), len(dict(pairs)), pairs)
            return dict(pairs)

        result = json.loads(output.stdout, parse_constant=reject_constant, object_pairs_hook=unique_object)
        self.assertEqual(set(result), {"format", "version", "command", "outcome", "diagnostics", "result"})
        self.assertEqual(result["format"], "qleisli.result")
        self.assertEqual(result["version"], 1)
        self.assertEqual(result["outcome"], "error" if status else "ok")
        if status:
            self.assertIsNone(result["result"])
            self.assertTrue(result["diagnostics"])
        else:
            self.assertEqual(result["diagnostics"], [])
        for diagnostic in result["diagnostics"]:
            self.assertEqual(set(diagnostic), {"code", "severity", "message", "primary", "related"})
            self.assertEqual(diagnostic["severity"], "error")
            self.assertEqual(diagnostic["related"], [])
            if diagnostic["primary"] is not None:
                self.assertEqual(set(diagnostic["primary"]), {"path", "start", "end", "line", "column"})
        return result

    def test_check_run_and_distribution_order(self):
        self.source("use std::quantum::init0; use std::quantum::h; use std::observe::measure_z;\n"
                    "observe fn main() -> (CBit,CBit) { let a = measure_z(h(init0())); (a,not a) }")
        self.assertEqual(self.invoke("check", self.root, "--format=json")["result"], {"verified": True})
        rows = self.invoke("run", "--format=json", self.root)["result"]["distribution"]
        self.assertEqual([row["bits"] for row in rows], [[False, True], [True, False]])
        for row in rows:
            self.assertEqual(set(row), {"bits", "probability"})
            self.assertTrue(math.isfinite(row["probability"]))
            self.assertAlmostEqual(row["probability"], 0.5)
        self.source("observe fn main() -> Unit { () }")
        self.assertEqual(self.invoke("--format=json", "run", self.root)["result"],
                         {"distribution": [{"bits": [], "probability": 1}]})

    def test_original_byte_spans_and_unicode_scalar_columns(self):
        for source in ["/* 🦀日本語 */ @", "// 日本語\r\nobserve fn main() -> Unit {", "@"]:
            with self.subTest(source=source):
                self.source(source)
                diagnostic = self.invoke("check", self.root, "--format=json", status=1)["diagnostics"][0]
                self.assertEqual(diagnostic["code"], "parse")
                start = source.index("@") if "@" in source else len(source)
                end = start + 1 if "@" in source else start
                self.assertEqual(diagnostic["primary"], {
                    "path": "main.qli", "start": len(source[:start].encode()), "end": len(source[:end].encode()),
                    "line": source[:start].count("\n") + 1, "column": len(source[:start].split("\n")[-1]) + 1,
                })

    def test_truncated_static_arguments_are_located_parse_failures(self):
        for source in ["unitary fn f(q: Q<Bit>) -> Q<Bit> { g[",
                       "unitary fn f(q: Q<Bit>) -> Q<Bit> { g[repeat_op(0,"]:
            self.source(source)
            for command in ["check", "run"]:
                with self.subTest(source=source, command=command):
                    result = self.invoke(command, self.root, "--format=json", status=1)
                    self.assertEqual(len(result["diagnostics"]), 1)
                    diagnostic = result["diagnostics"][0]
                    self.assertEqual(diagnostic["code"], "parse")
                    self.assertEqual(diagnostic["primary"], {
                        "path": "main.qli", "start": len(source), "end": len(source),
                        "line": 1, "column": len(source) + 1,
                    })

    def test_error_categories_and_nested_project_relative_paths(self):
        sources = {
            "type_mismatch": "observe fn main() -> CBit { () }",
            "unknown_name": "observe fn main() -> Unit { missing() }",
            "recursive_call": "unitary fn f() -> Unit { f() }",
            "ownership": "unitary fn f(q:Q<Bit>) -> (Q<Bit>,Q<Bit>) { (q,q) }",
            "effect": "use std::quantum::init0; unitary fn f() -> Q<Bit> { init0() }",
            "arity": "unitary fn f() -> Unit { () } observe fn main() -> Unit { f(true) }",
            "project": "use absent::name;",
        }
        for code, source in sources.items():
            with self.subTest(code=code):
                self.source(source)
                diagnostic = self.invoke("check", self.root, "--format=json", status=1)["diagnostics"][0]
                self.assertEqual(diagnostic["code"], code)
                self.assertEqual(diagnostic["primary"]["path"], "main.qli")
        self.source("")
        (self.root / "nested").mkdir()
        (self.root / "nested" / "module.qli").write_text("unitary fn f() -> Unit { missing() }")
        diagnostic = self.invoke("check", self.root, "--format=json", status=1)["diagnostics"][0]
        self.assertEqual(diagnostic["primary"]["path"], "nested/module.qli")

    def test_project_and_entry_errors_have_no_invented_source_span(self):
        self.source("")
        for command, root, code in [("run", self.root, "invalid_entry"),
                                    ("check", self.root / "missing", "project")]:
            diagnostic = self.invoke(command, root, "--format=json", status=1)["diagnostics"][0]
            self.assertEqual(diagnostic["code"], code)
            self.assertIsNone(diagnostic["primary"])
        (self.root / "main.qli").write_bytes(b"\xff")
        diagnostic = self.invoke("check", self.root, "--format=json", status=1)["diagnostics"][0]
        self.assertEqual(diagnostic["code"], "project")
        self.assertIsNone(diagnostic["primary"])

    def test_usage_and_escaped_command_names(self):
        for command in ["doc", "sample", "emit-ir", "verify-ir", 'unknown"\\\n\t日本語']:
            result = self.invoke(command, self.root, "--format=json", status=2)
            self.assertEqual(result["command"], command)
            self.assertEqual(result["diagnostics"][0]["code"], "usage")
        result = self.invoke("--format=json", status=2)
        self.assertEqual(result["command"], "")

    @unittest.skipUnless(os.name == "posix", "raw POSIX argument bytes")
    def test_non_utf8_paths_and_commands(self):
        root = os.fsencode(self.root) + b"/invalid-\xff"
        diagnostic = self.invoke("check", root, "--format=json", status=1)["diagnostics"][0]
        self.assertEqual(diagnostic["code"], "project")
        self.assertIsNone(diagnostic["primary"])
        result = self.invoke(b"check\xff", self.root, "--format=json", status=2)
        self.assertEqual(result["command"], "")

    @unittest.skipUnless(sys.platform.startswith("linux"), "non-UTF-8 filesystem names")
    def test_existing_non_utf8_path_and_stdout_write_failure(self):
        root = os.fsencode(self.root) + b"/invalid-\xff"
        os.mkdir(root)
        with open(root + b"/main.qli", "wb") as source:
            source.write(b"observe fn main() -> Unit { () }")
        self.assertEqual(self.invoke("check", root, "--format=json", status=1)["diagnostics"][0]["code"], "project")
        self.source("observe fn main() -> Unit { () }")
        with open("/dev/full", "wb") as output:
            result = subprocess.run([BINARY, "check", str(self.root), "--format=json"], stdout=output, stderr=subprocess.PIPE)
        self.assertEqual(result.returncode, 1)
        self.assertIn(b"could not write JSON result", result.stderr)


if __name__ == "__main__":
    unittest.main()
