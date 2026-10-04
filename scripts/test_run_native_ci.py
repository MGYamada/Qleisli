"""Scheduling must retain the pre-#206 commands and fail closed."""

import copy
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
from run_native_ci import MANIFEST, ROOT, execute, execution_environment, launch_command, load_tasks, source_binding, verify_coverage


class NativeCI(unittest.TestCase):
    def test_native_cargo_uses_only_the_already_checked_toolchain_pin(self):
        self.assertEqual(launch_command(["cargo", "+1.98.1", "test"]), ["cargo", "test"])
        for version in ["+1.85.0", "+stable", "+nightly"]:
            with self.assertRaises(ValueError):
                launch_command(["cargo", version, "test"])
        self.assertEqual(launch_command(["echo", "+1.98.1"]), ["echo", "+1.98.1"])

    def test_retains_every_pre_206_command_and_environment(self):
        tasks = load_tasks(MANIFEST)
        self.assertEqual(len(tasks), 67)
        self.assertEqual(sum(len(task["commands"]) for task in tasks), 81)
        inventory = [{key: value for key, value in task.items() if key in ("commands", "env")} for task in tasks if task["id"] not in {"native-paths", "native-acceptance"}]
        inventory = copy.deepcopy(inventory)
        for task in inventory:
            task["commands"] = [command for command in task["commands"]
                                if command not in (["python3", "scripts/test_hierarchical_finite_binding.py"],
                                    ["python3", "scripts/test_verification_decoders.py", "--record", "{record}"],
                                    ["python3", "scripts/test_qpe_instrument_host.py", "--record", "{record}"],
                                    ["python3", "scripts/test_instrument_transport.py", "--record", "{record}"])]
        digest = hashlib.sha256(json.dumps(inventory, sort_keys=True).encode()).hexdigest()
        # v0.2.6 workflow commands, replacing only isolated --record paths.
        self.assertEqual(digest, "33f46d04c2071b73d673c1c509866d57b547b63fbf468a894e0b809a213f424e")
        for task in tasks:
            for command in task["commands"]:
                if command[0] == "python3":
                    self.assertTrue((ROOT / command[1]).is_file())

    def test_invalid_manifest_coverage_is_rejected(self):
        original = json.loads(MANIFEST.read_text())
        mutations = [dict(format=2, tasks=original["tasks"]), dict(format=1, tasks=[])]
        for mutate in (lambda m: m["tasks"].append(m["tasks"][0]),
                       lambda m: m["tasks"][0].update(id="../escape"),
                       lambda m: m["tasks"][0].update(commands=[]),
                       lambda m: m["tasks"][0].update(commands=["shell command"]),
                       lambda m: m["tasks"][0].update(env={"BAD KEY": "value"}),
                       lambda m: m["tasks"][0].update(env={"RUSTUP_TOOLCHAIN": "1.85.0"}),
                       lambda m: m["tasks"][0].update(commands=[["cargo", "+1.85.0", "test"]])):
            mutated = copy.deepcopy(original)
            mutate(mutated)
            mutations.append(mutated)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "manifest.json"
            for manifest in mutations:
                path.write_text(json.dumps(manifest))
                with self.assertRaises(ValueError):
                    load_tasks(path)

    def test_named_qpe_host_faults_have_a_required_ci_command(self):
        task = next(t for t in load_tasks(MANIFEST) if t['id'] == 'hierarchical-qpe-instrument')
        self.assertIn(['python3', 'scripts/test_qpe_instrument_host.py', '--record', '{record}'], task['commands'])

    def test_dynamic_component_version_checks_are_required(self):
        task = next(t for t in load_tasks(MANIFEST) if t['id'] == 'hierarchical-preparation')
        self.assertIn(['python3', 'scripts/test_instrument_transport.py', '--record', '{record}'], task['commands'])

    def test_native_handles_and_original_input_replay_are_required(self):
        task = next(t for t in load_tasks(MANIFEST) if t['id'] == 'native-acceptance')
        self.assertEqual(task['commands'], [
            ['cargo', '+1.98.1', 'test', '--test', 'native_acceptance', '--', '--include-ignored'],
            ['cargo', '+1.98.1', 'test', '--test', 'native_roundtrip', '--', '--nocapture'],
            ['cargo', '+1.98.1', 'test', '--test', 'predicate_domain'],
            ['cargo', '+1.98.1', 'test', '--test', 'ordinary_types'],
            ['cargo', '+1.98.1', 'build', '--locked', '--offline', '--example', 'native_acceptance'],
            ['python3', 'scripts/test_native_acceptance_replay.py', '--record', '{record}'],
        ])
        self.assertEqual(task['env']['QLEISLI_KERNEL'], 'lean-kernel/.lake/build/bin/qleisli-kernel')

    def test_workflow_separates_full_proofs_from_native_tests(self):
        workflow = (ROOT / ".github/workflows/ci.yml").read_text()
        kernel = workflow.split("  check-lean-kernel:\n")[1].split("  check-distribution:\n")[0]
        for command in ("check_lean_kernel.py", "Audit.lean", "Tests.lean", "kernel-refactoring-equivalence.lean",
                        "leanchecker --fresh QleisliKernel", "leanchecker --fresh Main", "test_check_lean_kernel.py --compiled"):
            self.assertLess(kernel.index(command), kernel.index("run_native_ci.py"))
        model = workflow.split("  check-lean:\n")[1].split("  check-lean-kernel:\n")[0]
        self.assertIn("python3 scripts/check_schema_registry.py", model)
        self.assertIn("use-github-cache: 'false'", model)
        self.assertIn("options: ['4', '2', '1']", workflow)
        self.assertIn("python3 scripts/test_run_native_ci.py", workflow)
        self.assertIn("options: [full, tests]", workflow)
        for name in ["Replay retained proof reductions", "Replay the compiled project definitions"]:
            step = kernel.split(f"- name: {name}")[1].split("      - ")[0]
            self.assertIn("if: needs.changes.outputs.proof_lane == 'full'", step)
        audit = kernel.split("- name: Audit axioms")[1].split("      - ")[0]
        native = kernel.split("- name: Run all retained native comparisons")[1].split("      - ")[0]
        self.assertNotIn("if:", audit)
        self.assertNotIn("if:", native)
        self.assertIn("check_schema_registry.py --source-only", model)
        self.assertIn("proof_lane == 'model'", model)
        self.assertIn("proof_lane == 'full'", model)

    def test_workers_really_overlap(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            script = ("import pathlib,sys,time; p=pathlib.Path(sys.argv[1]); p.touch(); "
                      "other=pathlib.Path(sys.argv[2]); deadline=time.monotonic()+3\n"
                      "while not other.exists() and time.monotonic()<deadline: time.sleep(0.01)\n"
                      "assert other.exists(), 'workers did not overlap'\n")
            tasks = [dict(id=f"task-{i}", name="overlap", commands=[[sys.executable, "-c", script,
                     str(root / f"started-{i}"), str(root / f"started-{1-i}")]]) for i in range(2)]
            results = execute(tasks, root, root, 2, 5)
            self.assertTrue(all(row["status"] == "passed" for row in results))

    def run_tasks(self, commands, workers=2, timeout=5):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)
            tasks = [dict(id=f"task-{i}", name=f"task {i}", commands=group) for i, group in enumerate(commands)]
            results = execute(tasks, path, path, workers, timeout)
            report = dict(binding={"head": "a"}, manifest_sha256="hash", tasks=results)
            return tasks, report

    def test_parallel_tasks_have_isolated_records_and_complete_coverage(self):
        command = [sys.executable, "-c", "import pathlib,sys; pathlib.Path(sys.argv[1]).write_text('independent')", "{record}"]
        tasks, report = self.run_tasks([[command], [command, command]])
        verify_coverage(report, tasks, {"head": "a"}, "hash")
        self.assertNotEqual(report["tasks"][0]["commands"][0]["command"][-1], report["tasks"][1]["commands"][0]["command"][-1])

        mutations = []
        for mutate in (lambda r: r["tasks"].pop(),
                       lambda r: r["tasks"].append(r["tasks"][0]),
                       lambda r: r["tasks"][1].update(id=r["tasks"][0]["id"]),
                       lambda r: r["tasks"][0].update(status="failed"),
                       lambda r: r["tasks"][0].update(commands=[]),
                       lambda r: r["tasks"][0]["commands"][0].update(exit_code=1),
                       lambda r: r["tasks"][0]["commands"][0].update(command=["different"]),
                       lambda r: r["tasks"][0]["commands"][0].update(executed_command=["different"]),
                       lambda r: r.update(binding={"head": "stale"}),
                       lambda r: r.update(manifest_sha256="corrupt")):
            mutated = copy.deepcopy(report)
            mutate(mutated)
            mutations.append(mutated)
        for mutated in mutations:
            with self.assertRaises(ValueError):
                verify_coverage(mutated, tasks, {"head": "a"}, "hash")

    def test_nested_record_paths_stay_inside_each_task_output(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            output = root / "outputs"
            output.mkdir()
            script = ("import pathlib,sys; p=pathlib.Path(sys.argv[1]); "
                      "p.parent.mkdir(parents=True); p.write_text('nested')")
            tasks = [dict(id="nested", name="nested record", commands=[
                [sys.executable, "-c", script, "{record}/interop-native.json"]])]
            results = execute(tasks, root, output, 1, 5)
            self.assertEqual(results[0]["status"], "passed")
            self.assertEqual((output / "nested/record.json/interop-native.json").read_text(), "nested")
            self.assertFalse((root / "{record}").exists())
            report = dict(binding={"head": "a"}, manifest_sha256="hash", tasks=results)
            verify_coverage(report, tasks, {"head": "a"}, "hash")
            results[0]["commands"][0]["command"][-1] = "{record}/interop-native.json"
            with self.assertRaises(ValueError):
                verify_coverage(report, tasks, {"head": "a"}, "hash")

    def test_failure_and_timeout_do_not_skip_other_groups_or_pass(self):
        fail = [sys.executable, "-c", "raise SystemExit(2)"]
        timeout = [sys.executable, "-c", "import time; time.sleep(10)"]
        passed = [sys.executable, "-c", "print('still checked')"]
        tasks, report = self.run_tasks([[fail, passed], [timeout], [passed]], timeout=0.2)
        self.assertEqual([row["status"] for row in report["tasks"]], ["failed", "failed", "passed"])
        self.assertEqual(len(report["tasks"][0]["commands"]), 1)
        with self.assertRaises(ValueError):
            verify_coverage(report, tasks, {"head": "a"}, "hash")

    def test_invalid_worker_count_and_existing_task_directory_fail(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)
            task = dict(id="task", name="task", commands=[[sys.executable, "-c", "pass"]])
            with self.assertRaises(ValueError):
                execute([task], path, path, 0, 1)
            (path / "task").mkdir()
            with self.assertRaises(FileExistsError):
                execute([task], path, path, 1, 1)

    def test_source_and_actual_toolchain_binding(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "lean-kernel").mkdir()
            (root / "lean-kernel/lean-toolchain").write_text("leanprover/lean4:v4.30.0\n")
            good = ["a" * 40, "", "Lean (version 4.30.0, test)", "rustc 1.98.1 (test)", "cargo 1.98.1 (test)"]
            with patch("run_native_ci.subprocess.check_output", side_effect=good):
                binding = source_binding(root, "a" * 40)
                self.assertEqual(binding["head"], "a" * 40)
                self.assertEqual(binding["environment"]["RUSTUP_TOOLCHAIN"], "1.98.1")
            for outputs in (["b" * 40], [good[0], "?? lean-kernel/extra.lean"],
                            good[:2] + ["Lean (version 4.29.0, test)"] + good[3:],
                            good[:3] + ["rustc 1.85.0 (test)", good[4]],
                            good[:4] + ["cargo 1.85.0 (test)"]):
                with patch("run_native_ci.subprocess.check_output", side_effect=outputs):
                    with self.assertRaises(ValueError):
                        source_binding(root, "a" * 40)

    def test_untracked_input_is_rejected_in_a_real_checkout(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for command in (["git", "init", "-q"], ["git", "-c", "user.name=test", "-c", "user.email=test@example.invalid",
                            "commit", "-q", "--allow-empty", "-m", "fixture"]):
                subprocess.run(command, cwd=root, check=True, capture_output=True)
            (root / "untracked.py").write_text("raise RuntimeError('unbound input')")
            with self.assertRaisesRegex(ValueError, "untracked changes"):
                source_binding(root, None)

    def test_nested_processes_receive_only_bound_environment(self):
        poison = {name: "injected" for name in ("PYTHONPATH", "PYTHONHOME", "RUSTFLAGS", "RUSTC_WRAPPER",
                  "CARGO_ENCODED_RUSTFLAGS", "LEAN_PATH", "QLEISLI_BIN")}
        poison["RUSTUP_TOOLCHAIN"] = "1.85.0"
        with patch.dict(os.environ, poison):
            env = execution_environment()
            self.assertEqual(env["RUSTUP_TOOLCHAIN"], "1.98.1")
            for name in poison.keys() - {"RUSTUP_TOOLCHAIN"}:
                self.assertNotIn(name, env)
            code = ("import os,subprocess,sys; "
                    "assert os.environ['RUSTUP_TOOLCHAIN']=='1.98.1'; "
                    "assert 'RUSTFLAGS' not in os.environ and 'PYTHONPATH' not in os.environ; "
                    "subprocess.run([sys.executable,'-c',\"import os; assert os.environ['RUSTUP_TOOLCHAIN']=='1.98.1'\"],check=True)")
            tasks, report = self.run_tasks([[[sys.executable, "-c", code]]])
            verify_coverage(report, tasks, {"head": "a"}, "hash")


if __name__ == "__main__":
    unittest.main()
