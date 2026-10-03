#!/usr/bin/env python3
"""Independent JSON decoding and machine CLI conformance; pass a built binary path."""

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
        (self.root / "Qargo.toml").write_text('schema-version = 2\n[qrate]\nedition = "2026"\n')

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
            for related in diagnostic["related"]:
                self.assertEqual(set(related), {"message", "location"})
                self.assertTrue(related["message"].startswith("json_pointer:"))
                self.assertIsNone(related["location"])
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
        for command, root, code, path in [("run", self.root, "invalid_entry", None),
                                          ("check", self.root / "missing", "project", ".")]:
            diagnostic = self.invoke(command, root, "--format=json", status=1)["diagnostics"][0]
            self.assertEqual(diagnostic["code"], code)
            if path is None:
                self.assertIsNone(diagnostic["primary"])
            else:
                self.assertEqual(diagnostic["primary"], {
                    "path": path, "start": 0, "end": 0, "line": 1, "column": 1})
        (self.root / "main.qli").write_bytes(b"\xff")
        diagnostic = self.invoke("check", self.root, "--format=json", status=1)["diagnostics"][0]
        self.assertEqual(diagnostic["code"], "project")
        self.assertEqual(diagnostic["primary"], {
            "path": "main.qli", "start": 0, "end": 0, "line": 1, "column": 1})

    def test_usage_and_escaped_command_names(self):
        for command in ["doc", "sample", "emit-ir", 'unknown"\\\n\t日本語']:
            result = self.invoke(command, self.root, "--format=json", status=2)
            self.assertEqual(result["command"], command)
            self.assertEqual(result["diagnostics"][0]["code"], "usage")
        result = self.invoke("--format=json", status=2)
        self.assertEqual(result["command"], "")

    def test_seeded_samples_use_fresh_preparation_and_preserve_correlation(self):
        self.source("use std::quantum::init0; use std::quantum::h; use std::observe::measure_z;\n"
                    "observe fn main() -> (CBit,CBit) { let a = measure_z(h(init0())); (a,not a) }")
        args = ("sample", self.root, "--shots=64", "--seed=18446744073709551615", "--format=json")
        result = self.invoke(*args)["result"]
        self.assertEqual(result, self.invoke(*args)["result"])
        self.assertEqual(set(result), {"rng", "seed", "shots", "execution_steps"})
        self.assertEqual(result["rng"], "splitmix64-v1")
        self.assertEqual(result["seed"], "18446744073709551615")
        self.assertEqual(len(result["shots"]), 64)
        self.assertEqual(result["execution_steps"], sum(s["execution_steps"] for s in result["shots"]))
        for shot in result["shots"]:
            self.assertEqual(set(shot), {"bits", "execution_steps"})
            self.assertNotEqual(*shot["bits"])

    def test_text_json_and_interop_samples_keep_the_same_seeded_results(self):
        for source in [
            "observe fn main() -> Unit { () }",
            "use std::quantum::{init0,h,cnot}; use std::observe::measure_z; "
            "observe fn main() -> (CBit,CBit) { "
            "let (a,b) = cnot(h(init0()),init0()); (measure_z(a),measure_z(b)) }",
        ]:
            with self.subTest(source=source):
                self.source(source)
                flags = ("--shots=32", "--seed=18446744073709551615")
                direct = self.invoke("sample", self.root, *flags, "--format=json")["result"]
                imported = self.invoke("interop", "sample", self.root, "--input=qli", *flags)["result"]
                self.assertEqual(direct, imported)
                text = subprocess.run([BINARY, "sample", self.root, *flags], capture_output=True)
                self.assertEqual(text.returncode, 0, text)
                self.assertEqual(text.stderr, b"")
                expected = "".join(
                    ("".join("1" if bit else "0" for bit in shot["bits"]) or "()") + "\n"
                    for shot in direct["shots"]
                )
                self.assertEqual(text.stdout.decode(), expected)
                for shot in direct["shots"]:
                    self.assertIn(shot["bits"], [[], [False, False], [True, True]])

    def test_numeric_spelling_is_consistent_across_cli_adapters(self):
        self.source("observe fn main() -> CBit { true }")
        for seed in ["", "01", "+1", "-1", "１", "18446744073709551616"]:
            with self.subTest(seed=seed):
                for args in [
                    ("sample", self.root, "--shots=1", f"--seed={seed}", "--format=json"),
                    ("interop", "sample", self.root, "--input=qli", "--shots=1", f"--seed={seed}"),
                ]:
                    result = self.invoke(*args, status=2)
                    self.assertEqual(result["diagnostics"][0]["code"], "usage")
                sized = subprocess.run(
                    [BINARY, "sized", "sample", "--entry=main::f", "--module=main=missing.qli",
                     "--kernel=missing", "--shots=1", f"--seed={seed}"], capture_output=True,
                )
                self.assertEqual(sized.returncode, 2, sized)
                self.assertEqual(sized.stdout, b"")
        # Sized naturals keep their u32 bound even though seeds use u64.
        sized = subprocess.run(
            [BINARY, "sized", "check", "--entry=main::f", "--module=main=missing.qli",
             "--kernel=missing", "--nat=n=4294967296"], capture_output=True,
        )
        self.assertEqual(sized.returncode, 2, sized)
        self.assertEqual(sized.stdout, b"")

    def test_portable_ir_is_independently_decoded_and_reverified(self):
        self.source("observe fn main() -> CBit { true }")
        artifact = self.root / "artifact.json"
        self.assertEqual(self.invoke("emit-ir", self.root, f"--output={artifact}", "--format=json")["result"], {"path": str(artifact)})
        data = json.loads(artifact.read_bytes())
        self.assertEqual(set(data), {"format", "version", "profile", "sources", "programs", "evidence", "root", "root_interface"})
        self.assertEqual(data["format"], "qleisli.finite-ir")
        self.assertEqual(data["version"], 2)
        (self.root / "main.qli").unlink()
        self.assertEqual(self.invoke("verify-ir", artifact, "--format=json")["result"], {"verified": True, "request_checked": False})
        data["programs"][data["root"]]["classical_outputs"] = [4294967295]
        artifact.write_text(json.dumps(data), encoding="utf-8")
        error = self.invoke("verify-ir", artifact, "--format=json", status=1)["diagnostics"][0]
        self.assertEqual(error["code"], "invalid_ir")
        self.assertTrue(error["related"])

    @unittest.skipUnless(os.name == "posix", "raw POSIX argument bytes")
    def test_non_utf8_paths_and_commands(self):
        root = os.fsencode(self.root) + b"/invalid-\xff"
        diagnostic = self.invoke("check", root, "--format=json", status=1)["diagnostics"][0]
        self.assertEqual(diagnostic["code"], "project")
        self.assertIsNone(diagnostic["primary"])
        result = self.invoke(b"check\xff", self.root, "--format=json", status=2)
        self.assertEqual(result["command"], "")

    def test_qrate_selection_locations_are_independent_of_root_spelling(self):
        self.source("observe fn main()->Unit{()}")
        alias = self.root / "alias"
        alias.symlink_to(self.root, target_is_directory=True)
        diagnostics = []
        for path in [self.root.resolve(), self.root.relative_to(self.root.parent), alias]:
            output = subprocess.run([BINARY, "check", str(path), "--qrate", "--format=json"], cwd=self.root.parent, capture_output=True)
            self.assertEqual(output.returncode, 1)
            diagnostic = json.loads(output.stdout)["diagnostics"][0]
            self.assertEqual(diagnostic["code"], "project")
            self.assertIsNotNone(diagnostic["primary"])
            self.assertEqual(diagnostic["primary"]["path"], "Qargo.toml")
            diagnostics.append(diagnostic["primary"])
        self.assertEqual(diagnostics, [diagnostics[0]] * 3)

    @unittest.skipUnless(sys.platform.startswith("linux"), "non-UTF-8 filesystem names")
    def test_canonical_non_utf8_source_roots_are_rejected_in_json(self):
        root = os.fsencode(self.root) + b"/invalid-\xff"
        os.mkdir(root)
        for name, data in [(b"main.qli", b"observe fn main()->Unit{()}"), (b"Qargo.toml", b"schema-version=2\n[qrate]\nedition='2026'\n[source]\nroot='src'\n")]:
            with open(root + b"/" + name, "wb") as file:
                file.write(data)
        os.mkdir(root + b"/src")
        with open(root + b"/src/main.qli", "wb") as file:
            file.write(b"observe fn main()->Unit{()}")
        alias = self.root / "alias"
        os.symlink(root, alias)
        for path, cwd, options in [(alias, self.root, []), (".", root, []), (alias, self.root, ["--qrate"])]:
            for command, extra in [("check", []), ("run", []), ("sample", ["--shots=1", "--seed=0"])]:
                output = subprocess.run([BINARY, command, str(path), "--format=json", *options, *extra], cwd=cwd, capture_output=True)
                self.assertEqual(output.returncode, 1, output)
                diagnostic = json.loads(output.stdout)["diagnostics"][0]
                self.assertEqual(diagnostic["code"], "project")
                self.assertEqual(diagnostic["message"], "source root is not valid UTF-8")
                self.assertIsNone(diagnostic["primary"])

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
