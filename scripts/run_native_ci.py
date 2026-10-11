#!/usr/bin/env python3
"""Run every retained native comparison on one freshly audited CI checkout.

This schedules checks, not evidence reuse: no cached project outputs or reports
can authorize a task skip. Each task keeps its own log and record directory.
"""

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time
import native_harness
from ci_runtime import (LEAN_TOOLCHAIN, RUST_TOOLCHAIN, execution_environment,
                        launch_command, record_command, run_task)

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / ".github/ci/native-comparisons.json"
TASK_ENVIRONMENT = {"QLEISLI_HIERARCHY_KERNEL", "QLEISLI_KERNEL"}


def load_tasks(path: Path) -> list[dict]:
    manifest = json.loads(path.read_text())
    if set(manifest) != {"format", "tasks"} or manifest["format"] != 1:
        raise ValueError("unknown comparison manifest format")
    tasks = manifest["tasks"]
    if not isinstance(tasks, list) or not tasks:
        raise ValueError("empty comparison coverage")
    ids = set()
    for task in tasks:
        if not isinstance(task, dict) or not {"id", "name", "commands"} <= task.keys() or task.keys() - {"id", "name", "commands", "env"}:
            raise ValueError("invalid comparison task")
        identifier = task["id"]
        if not isinstance(identifier, str) or not re.fullmatch(r"[a-z0-9-]+", identifier) or identifier in ids:
            raise ValueError("invalid or duplicate comparison id")
        ids.add(identifier)
        if not isinstance(task["name"], str) or not task["name"] or not isinstance(task["commands"], list) or not task["commands"]:
            raise ValueError("missing comparison commands")
        for command in task["commands"]:
            if not isinstance(command, list) or not command or any(not isinstance(arg, str) or not arg or "\x00" in arg for arg in command):
                raise ValueError("invalid comparison command")
            if Path(command[0]).name in {"cargo", "rustc", "rustdoc"} and any(
                    arg.startswith("+") and arg != "+" + RUST_TOOLCHAIN for arg in command[1:]):
                raise ValueError("comparison command overrides the pinned Rust toolchain")
        env = task.get("env", {})
        if not isinstance(env, dict) or any(not isinstance(key, str) or not re.fullmatch(r"[A-Z_][A-Z_0-9]*", key) or not isinstance(value, str) or "\x00" in value for key, value in env.items()):
            raise ValueError("invalid comparison environment")
        if env.keys() - TASK_ENVIRONMENT:
            raise ValueError("comparison environment is not in the reviewed allowlist")
    return tasks


def select_tasks(tasks: list[dict], requested: list[str], hosted: bool = False) -> list[dict]:
    """Named local reproduction never changes the hosted coverage requirement."""
    if not requested:
        return tasks
    if hosted:
        raise ValueError("hosted native comparisons require every group")
    known = {task["id"] for task in tasks}
    if len(set(requested)) != len(requested) or not set(requested) <= known:
        raise ValueError("unknown or duplicate comparison selection")
    return [task for task in tasks if task["id"] in requested]


def source_binding(root: Path, expected_head: str | None, environment: dict | None = None) -> dict:
    environment = execution_environment() if environment is None else environment
    def output(command, directory=root):
        return subprocess.check_output(command, cwd=directory, env=environment, text=True).strip()

    head = output(["git", "rev-parse", "HEAD"])
    if expected_head and head != expected_head:
        raise ValueError("comparison checkout differs from GITHUB_SHA")
    changed = output(["git", "status", "--porcelain=v1", "--untracked-files=all"])
    if changed:
        raise ValueError("comparison checkout has tracked or untracked changes:\n" + changed)
    pin = (root / "lean-kernel/lean-toolchain").read_text().strip()
    if pin != LEAN_TOOLCHAIN:
        raise ValueError("unexpected Lean toolchain pin")
    lean = output(["lake", "env", "lean", "--version"], root / "lean-kernel")
    rust = output(["rustc", "--version"])
    cargo = output(["cargo", "--version"])
    if not lean.startswith("Lean (version 4.30.0,") or not rust.startswith("rustc 1.98.1 ") or not cargo.startswith("cargo 1.98.1 "):
        raise ValueError("native comparison toolchain mismatch")
    return dict(head=head, lean_pin=pin, lean_version=lean, rust_version=rust,
                cargo_version=cargo, environment=environment)


def verify_coverage(report: dict, tasks: list[dict], binding: dict, manifest_hash: str) -> None:
    if report.get("binding") != binding or report.get("manifest_sha256") != manifest_hash:
        raise ValueError("comparison report source/toolchain/manifest mismatch")
    results = report.get("tasks", [])
    expected = {task["id"] for task in tasks}
    if not isinstance(results, list) or len(results) != len(expected) or {row["id"] for row in results} != expected:
        raise ValueError("missing, extra or duplicate comparison results")
    by_id = {row["id"]: row for row in results}
    for task in tasks:
        result = by_id[task["id"]]
        if result.get("status") != "passed" or len(result.get("commands", [])) != len(task["commands"]):
            raise ValueError(f"failed or incomplete comparison: {task['id']}")
        for observed, template in zip(result["commands"], task["commands"]):
            command = record_command(template, Path(result["log"]).parent)
            if observed.get("command") != command or observed.get("executed_command") != launch_command(command) or observed.get("exit_code") != 0:
                raise ValueError(f"wrong or failed comparison command: {task['id']}")


def execute(tasks: list[dict], root: Path, directory: Path, workers: int, timeout: float,
            environment: dict | None = None) -> list[dict]:
    if workers not in (1, 2, 4):
        raise ValueError("workers must be 1, 2 or 4")
    results = []
    environment = execution_environment() if environment is None else environment
    if any(task.get("env", {}).keys() - TASK_ENVIRONMENT for task in tasks):
        raise ValueError("comparison environment is not in the reviewed allowlist")
    with ThreadPoolExecutor(max_workers=workers) as pool:
        futures = {pool.submit(run_task, task, root, directory / task["id"], timeout, environment): task for task in tasks}
        for future in as_completed(futures):
            result = future.result()
            results.append(result)
            print(f"{result['status']}: {result['id']} ({result['seconds']:.1f}s)", flush=True)
            if result["status"] != "passed":
                print(Path(result["log"]).read_text(), flush=True)
    return sorted(results, key=lambda row: row["id"])


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workers", type=int, choices=(1, 2, 4), default=4)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--plan", action="store_true", help="print exact commands without building or running them")
    parser.add_argument("--task", action="append", default=[], help="local reproduction of a named manifest group")
    args = parser.parse_args()
    if not args.plan and args.output is None:
        parser.error("--output is required when executing comparisons")
    report = dict(format=1, status="failed", workers=args.workers,
                  run_id=os.environ.get("GITHUB_RUN_ID"), attempt=os.environ.get("GITHUB_RUN_ATTEMPT"))
    started = time.monotonic()
    created_output = False
    try:
        if not args.plan:
            args.output = args.output.resolve()
            args.output.mkdir(parents=True, exist_ok=False)
            created_output = True
        all_tasks = load_tasks(MANIFEST)
        tasks = select_tasks(all_tasks, args.task, os.environ.get("GITHUB_ACTIONS") == "true")
        report.update(coverage="selected-local-groups" if args.task else "complete-native-manifest",
                      expected_ids=[task["id"] for task in tasks],
                      omitted_ids=[task["id"] for task in all_tasks if task not in tasks])
        if args.plan:
            print(json.dumps(dict(report, status="not-run", tasks=tasks,
                                  prerequisites=["clean source and pinned tools", "native library", "Rust all-target build"]), indent=2))
            return 0
        # Refuse stale output directories; every invocation must actually execute.
        report["tasks"] = [dict(id=task["id"], status="not-run", reason="preparation did not complete",
                                commands=task["commands"]) for task in tasks]
        manifest_hash = hashlib.sha256(MANIFEST.read_bytes()).hexdigest()
        environment = execution_environment()
        binding = source_binding(ROOT, os.environ.get("GITHUB_SHA"), environment)
        report.update(binding=binding, manifest_sha256=manifest_hash, expected_ids=[task["id"] for task in tasks])
        build_path = args.output / "native-build.json"
        report["native_build_commands"] = []
        native_harness.prepare(build_path, report["native_build_commands"])
        # Every source driver sees the same compiler before workers start. This
        # removes an implicit dependency on whichever comparison first happens
        # to run `cargo build`, while retaining fresh decisions in every test.
        host_build = dict(id="host-build", commands=[["cargo", "build", "--locked", "--all-targets"]])
        report["host_build"] = run_task(host_build, ROOT, args.output / "host-build", 900, environment)
        if report["host_build"]["status"] != "passed":
            raise ValueError("native comparison host build failed: " + report["host_build"]["log"])
        report["tasks"] = execute(tasks, ROOT, args.output, args.workers, 900,
                                  environment | {native_harness.BUILD_ENV: str(build_path),
                                  "QLEISLI_KERNEL": str(ROOT / "lean-kernel/.lake/build/bin/qleisli-kernel")})
        native_harness.validate(build_path)
        if source_binding(ROOT, os.environ.get("GITHUB_SHA"), environment) != binding or hashlib.sha256(MANIFEST.read_bytes()).hexdigest() != manifest_hash:
            raise ValueError("source or toolchain changed during comparisons")
        verify_coverage(report, tasks, binding, manifest_hash)
        report["status"] = "passed"
    except (OSError, ValueError, KeyError, TypeError, RuntimeError, subprocess.SubprocessError) as failure:
        report["error"] = str(failure)
        print(f"Native CI: {failure}", file=sys.stderr)
    report["elapsed_seconds"] = time.monotonic() - started
    # Never overwrite a prior run when the fresh-directory check failed.
    if created_output:
        (args.output / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    sys.exit(main())
