"""Shared command execution for local source checks and hosted native comparisons.

This owns process groups, bounded scratch directories and command records;
selection, acceptance, source identity and coverage remain with the callers.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import json
import os
from pathlib import Path
import signal
import subprocess
import tempfile
import time

RUST_TOOLCHAIN = "1.98.1"
LEAN_TOOLCHAIN = "leanprover/lean4:v4.30.0"


def execution_environment() -> dict[str, str]:
    """Retain tool discovery/home/temp locations, never ambient compiler flags."""
    names = {"PATH", "HOME", "TMPDIR", "TMP", "TEMP", "SYSTEMROOT", "WINDIR",
             "PATHEXT", "CARGO_HOME", "RUSTUP_HOME", "ELAN_HOME"}
    return {key: value for key, value in os.environ.items() if key in names} | {
        "RUSTUP_TOOLCHAIN": RUST_TOOLCHAIN, "ELAN_TOOLCHAIN": LEAN_TOOLCHAIN,
        "PYTHONNOUSERSITE": "1", "PYTHONDONTWRITEBYTECODE": "1",
        # CI executes the same assertions without retaining debug/incremental
        # products in every temporary comparison crate. These fixed settings
        # are included in the source/toolchain binding, never taken from callers.
        "CARGO_PROFILE_DEV_DEBUG": "0", "CARGO_PROFILE_TEST_DEBUG": "0",
        "CARGO_INCREMENTAL": "0",
        "LC_ALL": "C", "LANG": "C",
    }


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


def record_command(template: list[str], directory: Path) -> list[str]:
    return [arg.replace("{record}", str(directory / "record.json")) for arg in template]


def run_task(task: dict, root: Path, directory: Path, timeout: float, environment: dict) -> dict:
    directory.mkdir()
    started = time.monotonic()
    results = [dict(command=record_command(template, directory), status="not-run",
                    reason="earlier command did not complete") for template in task["commands"]]
    log_path = directory / "command.log"
    try:
        # Children may be killed before their own TemporaryDirectory cleanup.
        # Own their default scratch area here; retain logs/records separately.
        with tempfile.TemporaryDirectory(prefix=".work-", dir=directory) as work, log_path.open("w") as log:
            task_environment = environment | task.get("env", {}) | {
                "TMPDIR": work, "TMP": work, "TEMP": work,
            }
            for number, template in enumerate(task["commands"]):
                command = record_command(template, directory)
                executed = launch_command(command)
                log.write(json.dumps(dict(command=command, executed_command=executed)) + "\n")
                log.flush()
                before = time.monotonic()
                result = results[number] = dict(command=command, executed_command=executed, status="failed")
                with subprocess.Popen(executed, cwd=root, env=task_environment,
                                      stdout=log, stderr=subprocess.STDOUT, start_new_session=True) as process:
                    try:
                        code = process.wait(timeout=timeout)
                    except subprocess.TimeoutExpired:
                        # Kill the whole native compiler/test tree, not just Python.
                        os.killpg(process.pid, signal.SIGKILL)
                        process.wait()
                        result.update(status="timed-out", exit_code=process.returncode,
                                      seconds=time.monotonic() - before)
                        raise TimeoutError(f"command exceeded {timeout} seconds")
                    finally:
                        # Also close descendants left behind by a successful
                        # command before reclaiming their scratch directory.
                        try:
                            os.killpg(process.pid, signal.SIGKILL)
                        except ProcessLookupError:
                            pass
                        process.wait()
                result.update(exit_code=code, seconds=time.monotonic() - before,
                              status="passed" if code == 0 else "failed")
                if code != 0:
                    raise ValueError(f"command exited {code}")
        return dict(id=task["id"], status="passed", commands=results,
                    seconds=time.monotonic() - started, log=str(log_path))
    except (OSError, ValueError, TimeoutError) as failure:
        return dict(id=task["id"], status="failed", error=str(failure), commands=results,
                    seconds=time.monotonic() - started, log=str(log_path))
