#!/usr/bin/env python3
"""Fail-closed lane selection for fresh native bundles (Issue #223).
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import contextlib
import io
from pathlib import Path
import subprocess
import sys
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
from package_lean_kernel import ROOT, parse_args, validate


class NativeBundleLanes(unittest.TestCase):
    def run_validation(self, lane, results=None):
        with patch("package_lean_kernel.subprocess.run", side_effect=results,
                   return_value=subprocess.CompletedProcess([], 0, "checked", "")) as run:
            with contextlib.redirect_stdout(io.StringIO()):
                logs = validate(Path("fresh-package"), lane)
        return logs, run.call_args_list

    def test_routine_and_model_keep_native_build_and_compiled_audit(self):
        for lane in ("tests", "model"):
            with self.subTest(lane=lane):
                logs, calls = self.run_validation(lane)
                self.assertEqual([row["command"] for row in logs], [
                    ["lake", "build"],
                    ["lake", "env", "lean", "-DwarningAsError=true", "Audit.lean"],
                ])
                for call in calls:
                    self.assertEqual(call.kwargs["cwd"], Path("fresh-package"))
                    self.assertEqual(call.kwargs["timeout"], 600)
                self.assertTrue(all(row["exit_code"] == 0 and row["seconds"] >= 0 for row in logs))

    def test_full_keeps_independent_replay_of_both_roots(self):
        logs, _ = self.run_validation("full")
        self.assertEqual([row["command"] for row in logs], [
            ["lake", "build"],
            ["lake", "env", "lean", "-DwarningAsError=true", "Audit.lean"],
            ["lake", "env", "leanchecker", "--fresh", "QleisliKernel"],
            ["lake", "env", "leanchecker", "--fresh", "Main"],
        ])

    def test_unspecified_lane_is_full_and_unknown_lane_never_falls_back(self):
        self.assertEqual(parse_args(["--output", "new-bundle"]).validation, "full")
        for lane in ("tests", "model", "full"):
            self.assertEqual(parse_args(["--output", "new-bundle", "--validation", lane]).validation, lane)
        for lane in ("", "unknown", "FULL"):
            with self.subTest(lane=lane), contextlib.redirect_stderr(io.StringIO()):
                with self.assertRaises(SystemExit):
                    parse_args(["--output", "new-bundle", "--validation", lane])
                with patch("package_lean_kernel.subprocess.run") as run:
                    with self.assertRaisesRegex(ValueError, "unknown validation lane"):
                        validate(Path("unused"), lane)
                    run.assert_not_called()

    def test_failed_build_audit_or_replay_never_produces_success(self):
        passed = subprocess.CompletedProcess([], 0, "checked", "")
        failed = subprocess.CompletedProcess([], 1, "", "deliberate rejection")
        for lane, count in (("tests", 2), ("model", 2), ("full", 4)):
            for stage in range(count):
                with self.subTest(lane=lane, stage=stage):
                    with patch("package_lean_kernel.subprocess.run", side_effect=[passed] * stage + [failed]) as run:
                        with contextlib.redirect_stdout(io.StringIO()), self.assertRaisesRegex(RuntimeError, "deliberate rejection"):
                            validate(Path("unused"), lane)
                        self.assertEqual(run.call_count, stage + 1)
        for error in (FileNotFoundError("lake"), subprocess.TimeoutExpired("lake", 600)):
            with patch("package_lean_kernel.subprocess.run", side_effect=error):
                with self.assertRaises(type(error)):
                    validate(Path("unused"), "tests")

    def test_both_platforms_forward_the_selected_lane_and_keep_relocation_tests(self):
        workflow = (ROOT / ".github/workflows/ci.yml").read_text()
        self.assertIn("python3 scripts/test_package_lean_kernel.py", workflow)
        package_lines = [line for line in workflow.splitlines() if "scripts/package_lean_kernel.py " in line]
        self.assertEqual(len(package_lines), 2)
        for line in package_lines:
            self.assertIn('--validation "${{ needs.changes.outputs.proof_lane }}"', line)
        for name, following in (("check-macos-source", "check-interop"), ("check-lean-kernel", "check-distribution")):
            job = workflow.split(f"  {name}:\n")[1].split(f"  {following}:\n")[0]
            self.assertIn('test_native_verification.py --kernel "$RUNNER_TEMP/qleisli-native-bundle/bin/qleisli-kernel"', job)


if __name__ == "__main__":
    unittest.main()
