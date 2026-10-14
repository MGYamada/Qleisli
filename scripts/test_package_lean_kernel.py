#!/usr/bin/env python3
"""Fail-closed lane selection for fresh native bundles (Issue #223).
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
"""
import contextlib
import io
from pathlib import Path
import re
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
        from ci_source_checks import plan
        self.assertIn('--checks ci-preflight --output', workflow)
        self.assertIn(['python3', 'scripts/test_package_lean_kernel.py'], plan('ci-preflight'))
        package_lines = [line for line in workflow.splitlines() if "scripts/package_lean_kernel.py " in line]
        self.assertEqual(len(package_lines), 2)
        for line in package_lines:
            self.assertIn('--validation "${{ needs.changes.outputs.proof_lane }}"', line)
        self.assertEqual(workflow.count('uses: ./.github/actions/native-bundle-smoke'), 2)
        for name, following, record in (
            ('check-macos-source', 'check-interop', '${{ runner.temp }}/native-macos'),
            ('check-lean-kernel', 'check-distribution', '${{ runner.temp }}/native-comparisons/native-bundle'),
        ):
            with self.subTest(job=name):
                job = workflow.split(f"  {name}:\n")[1].split(f"  {following}:\n")[0]
                steps = re.split(r'(?m)^      - ', job)
                smoke = [step for step in steps if 'uses: ./.github/actions/native-bundle-smoke\n' in step]
                self.assertEqual(len(smoke), 1)
                self.assertIn(f'          record: {record}\n', smoke[0])
                self.assertNotIn('        if:', smoke[0])
                package = job.index('scripts/package_lean_kernel.py ')
                check = job.index('uses: ./.github/actions/native-bundle-smoke')
                self.assertLess(package, check)
                if name == 'check-macos-source':
                    compiler = job.index('cargo +1.85.0 build --locked --bin qleisli')
                    self.assertLess(package, compiler)
                    self.assertLess(compiler, check)
                    self.assertLess(check, job.index('scripts/test_interop_native.py'))
                    self.assertIn('--record "$RUNNER_TEMP/native-macos/interop-native.json"', job)
                else:
                    self.assertLess(check, job.index('python3 -m venv "$RUNNER_TEMP/native-qir"'))
                    self.assertIn('"$RUNNER_TEMP/native-qir/bin/pip" install -r scripts/qir-reader-requirements.txt', job)
                    self.assertIn('"$RUNNER_TEMP/native-qir/bin/python" scripts/test_interop_native.py', job)
                    self.assertIn('--record "$RUNNER_TEMP/native-comparisons/native-bundle/interop-native.json"', job)
                archive = [step for step in steps if 'scripts/archive_lean_kernel.py ' in step]
                self.assertEqual(len(archive), 1)
                self.assertIn("if: needs.changes.outputs.proof_lane == 'full'", archive[0])
                self.assertLess(check, job.index('scripts/archive_lean_kernel.py '))
        shared = (ROOT / '.github/actions/native-bundle-smoke/action.yml').read_text()
        self.assertIn('BUNDLE_KERNEL: ${{ runner.temp }}/qleisli-native-bundle/bin/qleisli-kernel', shared)
        self.assertIn('RECORD_PATH: ${{ inputs.record }}', shared)
        self.assertIn('python3 scripts/test_native_verification.py --kernel "$BUNDLE_KERNEL" --record "$RECORD_PATH"', shared)
        self.assertIn('QLEISLI_KERNEL="$BUNDLE_KERNEL" python3 scripts/test_source_kernel.py', shared)


if __name__ == "__main__":
    unittest.main()
