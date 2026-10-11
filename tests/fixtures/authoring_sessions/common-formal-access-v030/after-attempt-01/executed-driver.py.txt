#!/usr/bin/env python3
"""Compare forty literal checks against immutable FIRST bytes, without normalization.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import resource
import sys

sys.dont_write_bytecode = True
DESIGN = Path(__file__).resolve().parent
ROOT = DESIGN.parent
OUT = ROOT / "after-attempt-01"
LIMIT = 1 << 20
DRIVER_SHA = "320b75c15abb1479859823ea03feb4034344edb41cdc57f8798c2e9c14893cf6"
FIRST_SHA = "140bc0e555d23460d6f8c523627c8cba643ca3ddc2aaa3d95533e06234a2e454"
CLI_SHA = "2209c0528e4f25dc46498bbbe8cc3ca3df31201e0fa7bed41130bff593e233c9"
NATIVE_SHA = "39effde0f152a2c926fcea3a7f99fc2f25f9de65906be2b8c527508353c90c85"
CASES = ("valid-operation", "valid-dependent-basis", "forward-natural", "forward-basis",
         "duplicate-access", "wrong-kind-access", "static-runtime-collision",
         "unused-missing-access", "natural-priority", "basis-scan-priority")
FORMS = (("finite", "text"), ("finite", "json"),
         ("selected-auto", "text"), ("selected-auto", "json"))
EQUAL_KEYS = ("command_equal", "exit_equal", "stdout_raw_equal", "stderr_raw_equal",
              "native_argv_raw_equal", "native_count_equal")


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise ValueError("cannot load guarded authored helper")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--inputs-sha256", required=True)
    args = parser.parse_args()
    if sys.version_info < (3, 11):
        raise ValueError("development Python 3.11+ required")
    if len(args.inputs_sha256) != 64 or any(c not in "0123456789abcdef" for c in args.inputs_sha256):
        parser.error("inputs SHA must be 64 lowercase hexadecimal digits")
    import hashlib
    if hashlib.sha256((ROOT / "driver.py").read_bytes()).hexdigest() != DRIVER_SHA:
        raise ValueError("original fixed driver changed")
    before = load(ROOT / "driver.py", "formal_first_fixed_functions")
    # Reuse only guarded authored functions. Never call original main or its
    # old identity guard; its 235-file baseline is historical after this unit.
    input_path = DESIGN / "inputs.json"
    if before.sha(input_path) != args.inputs_sha256:
        raise ValueError("explicit reviewed after input map changed")
    inputs = json.loads(before.read_bounded(input_path))
    first_path = ROOT / "first-files.json"
    if before.sha(first_path) != FIRST_SHA:
        raise ValueError("immutable FIRST map changed")
    first = json.loads(before.read_bounded(first_path))["files"]
    expected_order = [(case, profile, presentation) for case in CASES for profile, presentation in FORMS]

    def unchanged():
        if before.sha(input_path) != args.inputs_sha256 or before.sha(first_path) != FIRST_SHA:
            raise ValueError("reviewed maps changed")
        for row in first + inputs["frozen_files"]:
            path = (before.REPO / row["path"]).resolve()
            path.relative_to(before.REPO)
            if (path.stat().st_size != row["bytes"] or before.sha(path) != row["sha256"]
                    or path.stat().st_mode & 0o777 != row["mode"]):
                raise ValueError("immutable source/record/driver changed: " + row["path"])
        if sorted(p.name for p in (ROOT / "before").iterdir()) != inputs["before_inventory"]:
            raise ValueError("complete before raw inventory changed")
        if {p.name for p in (ROOT / "attempt-01").iterdir()} != set(CASES):
            raise ValueError("complete FIRST case inventory changed")
        for case in CASES:
            if {p.name for p in (ROOT / "attempt-01" / case).iterdir()} != {"main.qli", "Qargo.toml"}:
                raise ValueError("complete FIRST project inventory changed")
        if before.identity() != inputs["current_identity"]:
            raise ValueError("current source/CLI/native/contracts changed after freeze")

    unchanged()
    current = inputs["current_identity"]
    if current["cli_sha256"] != CLI_SHA or current["native_sha256"] != NATIVE_SHA:
        raise ValueError("fixed rebuilt CLI/native identity differs")
    baseline = json.loads(before.read_bounded(ROOT / "identity-prepared.json"))["identity"]
    if baseline != json.loads(before.read_bounded(ROOT / "before/identity.final.json"))["identity"]:
        raise ValueError("FIRST capture input identity was not unchanged")
    old_summary = json.loads(before.read_bounded(ROOT / "before/summary.json"))
    if (old_summary["actual_observation_count"] != 40 or old_summary["native_forwarded_attempts"] != 46
            or [(r["case"], r["profile"], r["presentation"]) for r in old_summary["rows"]] != expected_order):
        raise ValueError("immutable complete FIRST observations differ")
    if tuple(before.CASES) != CASES or tuple(before.FORMS) != FORMS:
        raise ValueError("guarded command function case/forms differ")
    commands = [before.command(*item) for item in expected_order]
    if commands != inputs["commands"]:
        raise ValueError("literal authored command mapping changed")
    if not os.access(before.CLI, os.X_OK) or not os.access(before.WRAPPER, os.X_OK):
        raise ValueError("fixed CLI/forwarder not executable")
    helper = load(before.HELPER, "formal_reviewed_bounded_capture")
    soft, hard = resource.getrlimit(resource.RLIMIT_FSIZE)
    ceiling = min([LIMIT] + [n for n in (soft, hard) if n != resource.RLIM_INFINITY])
    resource.setrlimit(resource.RLIMIT_FSIZE, (ceiling, ceiling))
    OUT.mkdir()  # One shot; originals and partial after records are never overwritten.
    (OUT / "executed-driver.py.txt").open("xb").write(Path(__file__).read_bytes())
    before.save(OUT / "started.json", dict(recorded_utc=before.timestamp(), inputs_sha256=args.inputs_sha256,
        status="after-capture-started", regular_file_byte_ceiling=ceiling, outer_seconds=55,
        python=sys.executable, python_version=sys.version))
    before.save(OUT / "identity.before.json", dict(identity=current, first_files_sha256=FIRST_SHA,
        inputs_sha256=args.inputs_sha256, frozen_before_file_count=len(inputs["before_inventory"])))
    rows = []
    try:
        for case, profile, presentation in expected_order:
            unchanged()
            label = case + "-" + profile + "-check-" + presentation
            argv = before.command(case, profile, presentation)  # Authored code, never metadata argv.
            journal = OUT / (label + ".native.jsonl")
            journal.touch(exist_ok=False)
            env = dict(os.environ, QLEISLI_PARAMETER_NATIVE_LOG=str(journal), PYTHONDONTWRITEBYTECODE="1")
            env.pop("QLEISLI_KERNEL", None)
            env.pop("QLEISLI_HIERARCHY_KERNEL", None)
            before.save(OUT / (label + ".command-before.json"), dict(recorded_utc=before.timestamp(), argv=argv, cwd=str(before.REPO)))
            result = helper.capture(argv, before.REPO, env, b"", seconds=55, output_limit=LIMIT)
            stdout, stderr = result.pop("stdout"), result.pop("stderr")
            stdout_path, stderr_path = OUT / (label + ".stdout.bin"), OUT / (label + ".stderr.bin")
            for path, data in ((stdout_path, stdout), (stderr_path, stderr)):
                with path.open("xb") as stream:
                    stream.write(data)
            native_raw = before.read_bounded(journal)
            attempts = [json.loads(line) for line in native_raw.splitlines()]
            event = dict(command=argv, exit_code=result["returncode"], recorded_utc=before.timestamp(),
                client_capture=result, native_forwarded_attempts=len(attempts), native_argv_log=journal.name,
                native_count_scope="Forwarder JSONL rows immediately before execv; no independently observed native starts/exits.",
                stdout_raw=stdout_path.name, stderr_raw=stderr_path.name, stdout_sha256=before.sha(stdout_path),
                stderr_sha256=before.sha(stderr_path), native_journal_sha256=before.sha(journal))
            before.save(OUT / (label + ".json"), event)
            old = json.loads(before.read_bounded(ROOT / "before" / (label + ".json")))
            row = dict(case=case, profile=profile, presentation=presentation,
                command_equal=argv == old["command"], exit_equal=event["exit_code"] == old["exit_code"],
                stdout_raw_equal=stdout == before.read_bounded(ROOT / "before" / (label + ".stdout.bin")),
                stderr_raw_equal=stderr == before.read_bounded(ROOT / "before" / (label + ".stderr.bin")),
                native_argv_raw_equal=native_raw == before.read_bounded(ROOT / "before" / (label + ".native.jsonl")),
                native_count_equal=len(attempts) == old["native_forwarded_attempts"],
                actual_exit_code=event["exit_code"], native_forwarded_attempts=len(attempts),
                observation="after-attempt-01/" + label + ".json")
            rows.append(row)
            unchanged()
            print(label, event["exit_code"], len(attempts), all(row[k] for k in EQUAL_KEYS), flush=True)
            if not result["spawned"] or result["reason"] is not None:
                before.save(OUT / "incomplete.json", dict(rows=rows,
                    reason="Actual operational failure retained; no retry or invented exit.",
                    process_scope="Outer group cleanup does not attest all separate descendant groups."))
                return 1
        equal = len(rows) == 40 and all(row[k] for row in rows for k in EQUAL_KEYS)
        before.save(OUT / "summary.json", dict(status="all_equal" if equal else "differences-observed",
            comparisons=rows, actual_observation_count=len(rows),
            native_forwarded_attempts=sum(row["native_forwarded_attempts"] for row in rows),
            output_normalizations=0, source_repairs=0, recorded_commands_executed=False,
            source_meaning_verified=False, original_before_packet_unchanged=True,
            scope="Exact bounded check-observation comparison; no source-preservation proof, guarantee or Issue completion."))
        unchanged()
        before.save(OUT / "identity.final.json", dict(identity=before.identity(),
            selected_inputs_unchanged=True, original_before_packet_unchanged=True))
        before.save(OUT / "files.json", dict(files={p.name: dict(bytes=p.stat().st_size, sha256=before.sha(p))
            for p in sorted(OUT.iterdir()) if p.is_file()}, self_excluded="files.json"))
        return 0 if equal else 1
    except BaseException as error:
        before.save(OUT / "aborted.json", dict(recorded_utc=before.timestamp(), completed_observations=len(rows),
            error_type=type(error).__name__, message=str(error), note="Partial output retained; no repair/retry."))
        raise


if __name__ == "__main__":
    sys.exit(main())
