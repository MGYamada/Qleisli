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
import signal
import subprocess
import sys
import time
import native_harness

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / ".github/ci/native-comparisons.json"
RUST_TOOLCHAIN = "1.98.1"
LEAN_TOOLCHAIN = "leanprover/lean4:v4.30.0"
TASK_ENVIRONMENT = {"QLEISLI_HIERARCHY_KERNEL", "QLEISLI_KERNEL"}


def execution_environment() -> dict[str, str]:
    """Retain tool discovery/home/temp locations, never ambient compiler flags."""
    names = {"PATH", "HOME", "TMPDIR", "TMP", "TEMP", "SYSTEMROOT", "WINDIR",
             "PATHEXT", "CARGO_HOME", "RUSTUP_HOME", "ELAN_HOME"}
    return {key: value for key, value in os.environ.items() if key in names} | {
        "RUSTUP_TOOLCHAIN": RUST_TOOLCHAIN, "ELAN_TOOLCHAIN": LEAN_TOOLCHAIN,
        "PYTHONNOUSERSITE": "1", "PYTHONDONTWRITEBYTECODE": "1",
        "LC_ALL": "C", "LANG": "C",
    }


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


def launch_command(command: list[str]) -> list[str]:
    """Use the already version-checked tools with either Rustup or native Cargo.

    +toolchain is Rustup proxy syntax, not a Cargo argument. The runner binds
    actual rustc/cargo versions and RUSTUP_TOOLCHAIN before and after every run.
    Only the identical pin can be removed; an override remains an error.
    """
    if Path(command[0]).name in {"cargo", "rustc", "rustdoc"} and len(command) > 1 and command[1].startswith("+"):
        if command[1] != "+" + RUST_TOOLCHAIN:
            raise ValueError("comparison command overrides the pinned Rust toolchain")
        return command[:1] + command[2:]
    return command


def run_task(task: dict, root: Path, directory: Path, timeout: float, environment: dict) -> dict:
    directory.mkdir()
    started = time.monotonic()
    results = []
    log_path = directory / "command.log"
    try:
        with log_path.open("w") as log:
            for template in task["commands"]:
                command = [arg.replace("{record}", str(directory / "record.json")) for arg in template]
                executed = launch_command(command)
                log.write(json.dumps(dict(command=command, executed_command=executed)) + "\n")
                log.flush()
                before = time.monotonic()
                with subprocess.Popen(executed, cwd=root, env=environment | task.get("env", {}),
                                      stdout=log, stderr=subprocess.STDOUT, start_new_session=True) as process:
                    try:
                        code = process.wait(timeout=timeout)
                    except subprocess.TimeoutExpired:
                        # Kill the whole native compiler/test tree, not just Python.
                        os.killpg(process.pid, signal.SIGKILL)
                        process.wait()
                        raise TimeoutError(f"command exceeded {timeout} seconds")
                results.append(dict(command=command, executed_command=executed, exit_code=code, seconds=time.monotonic() - before))
                if code != 0:
                    raise ValueError(f"command exited {code}")
        return dict(id=task["id"], status="passed", commands=results,
                    seconds=time.monotonic() - started, log=str(log_path))
    except (OSError, ValueError, TimeoutError) as failure:
        return dict(id=task["id"], status="failed", error=str(failure), commands=results,
                    seconds=time.monotonic() - started, log=str(log_path))


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
            command = [str(Path(result["log"]).parent / "record.json") if arg == "{record}" else arg for arg in template]
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
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    report = dict(format=1, status="failed", workers=args.workers,
                  run_id=os.environ.get("GITHUB_RUN_ID"), attempt=os.environ.get("GITHUB_RUN_ATTEMPT"))
    started = time.monotonic()
    try:
        # Refuse stale output directories; every invocation must actually execute.
        args.output = args.output.resolve()
        args.output.mkdir(parents=True, exist_ok=False)
        tasks = load_tasks(MANIFEST)
        manifest_hash = hashlib.sha256(MANIFEST.read_bytes()).hexdigest()
        environment = execution_environment()
        binding = source_binding(ROOT, os.environ.get("GITHUB_SHA"), environment)
        report.update(binding=binding, manifest_sha256=manifest_hash, expected_ids=[task["id"] for task in tasks])
        build_path = args.output / "native-build.json"
        report["native_build_commands"] = []
        native_harness.prepare(build_path, report["native_build_commands"])
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
    if args.output.is_dir() and "binding" in report:
        (args.output / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    sys.exit(main())
