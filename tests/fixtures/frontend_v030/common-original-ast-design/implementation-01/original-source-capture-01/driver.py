#!/usr/bin/env python3
"""Additive 72-original-source capture; no recorded argv is executable input.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import re
import resource
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[5]
ORIGINAL = REPO / "tests/fixtures/authoring_sessions/common-original-ast-v030"
PARENT = ORIGINAL / "capture-design-01/driver.py"
PARENT_SHA = "fd071d35bd2d9113296ef6f410485c93cf659be046eedf945e4aecdc1087844a"
LIMIT = 1 << 20
STAGES = ("cargo-version", "rustc-version", "format", "check-all-targets",
          "shared-type-tests", "focused-integration-tests", "native-small-arithmetic-tests",
          "clippy-all-targets", "rebuilt-cli")


def load(path, expected, name):
    import hashlib
    if hashlib.sha256(path.read_bytes()).hexdigest() != expected:
        raise ValueError("reviewed authored module changed: " + str(path))
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise ValueError("cannot load reviewed authored module")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)  # Guarded authored functions only; never main/metadata code.
    return module


base = load(PARENT, PARENT_SHA, "reviewed_original_source_capture_functions")


def snapshot(paths):
    return {str(p.relative_to(REPO)): base.record(p) for p in sorted(set(paths))}


def identity(attempt, results_sha):
    if base.sha(ORIGINAL / "first-files.json") != base.FIRST_SHA:
        raise ValueError("immutable original FIRST41 map changed")
    first = json.loads(base.read_bounded(ORIGINAL / "first-files.json"))["files"]
    if len(first) != 41 or any(base.record(base.repository_path(r["path"])) != {
            k: r[k] for k in ("bytes", "sha256", "mode")} for r in first):
        raise ValueError("complete original FIRST41 bytes or modes changed")
    projects = ORIGINAL / "attempt-01"
    if {p.name for p in projects.iterdir()} != set(base.CASES):
        raise ValueError("exact original eighteen-project inventory changed")
    for case in base.CASES:
        if {p.name for p in (projects / case).iterdir()} != {"main.qli", "Qargo.toml"}:
            raise ValueError("exact original two-file project inventory changed")
    folder = HERE.parent / "validation" / ("msrv-" + attempt)
    results = folder / "results.json"
    if base.sha(results) != results_sha:
        raise ValueError("explicit actual MSRV result hash differs")
    terminal = json.loads(base.read_bounded(results))
    before = json.loads(base.read_bounded(folder / "inputs-before.json"))
    after = json.loads(base.read_bounded(folder / "inputs-after.json"))
    digest = __import__("hashlib").sha256(json.dumps(before["files"], sort_keys=True,
        separators=(",", ":")).encode()).hexdigest()
    if (before != after or before["sha256"] != digest or terminal["mode"] != "msrv"
            or terminal["attempt"] != attempt or terminal["status"] != "passed"
            or terminal["remaining_stages_not_run"] != 0 or not terminal["source_inputs_unchanged"]
            or terminal["source_files_before"] != len(before["files"])
            or not terminal["cli_rebuild_completed"] or terminal["cli_path"] != str(base.CLI)
            or terminal["cli_sha256_after"] != base.sha(base.CLI)
            or terminal["native_sha256_before"] != base.NATIVE_SHA
            or terminal["native_sha256_after"] != base.NATIVE_SHA
            or [row["label"] for row in terminal["records"]] != list(STAGES)):
        raise ValueError("actual terminal MSRV/CLI/input association differs")
    for row in terminal["records"]:
        if (row["exit_code"] != 0 or row["launch_error"] is not None or row["timed_out"]
                or row["postcondition_error"] is not None or not row["identities_unchanged"]
                or row["source_input_digest_after"] != digest
                or row["native_sha256_after"] != base.NATIVE_SHA):
            raise ValueError("actual MSRV stage did not complete successfully")
        for kind in ("stdout", "stderr"):
            raw = row[kind]
            if Path(raw["path"]).name != raw["path"]:
                raise ValueError("stage raw log must be local to fixed MSRV attempt")
            observed = base.record(folder / raw["path"])
            if observed["bytes"] != raw["bytes"] or observed["sha256"] != raw["sha256"]:
                raise ValueError("actual MSRV raw log changed")
        if row["label"].endswith("tests") and (not row["actual_test_results"] or any(
                r["status"] != "ok" or r["failed"] != 0 for r in row["actual_test_results"])
                or sum(r["passed"] for r in row["actual_test_results"]) == 0):
            raise ValueError("actual MSRV test stage has no genuine passing results")
    for label, tool in (("cargo-version", "cargo"), ("rustc-version", "rustc")):
        row = next(r for r in terminal["records"] if r["label"] == label)
        if not re.match(tool + r" 1\.85\.0(?:\s|$)", base.read_bounded(folder / row["stdout"]["path"]).decode()):
            raise ValueError("actual MSRV version differs")
    current = snapshot(base.repository_path(name) for name in before["files"])
    if any(row["sha256"] != before["files"][name] for name, row in current.items()):
        raise ValueError("current declared source bytes differ from actual MSRV inputs")
    paths = list((REPO / "src").rglob("*.rs")) + [REPO / n for n in base.EMBEDDED + ("Cargo.toml", "Cargo.lock")]
    paths += [REPO / n for n in ("build.rs", "rust-toolchain", "rust-toolchain.toml") if (REPO / n).is_file()]
    paths += [p for p in (REPO / ".cargo").rglob("*") if p.is_file()]
    build = snapshot(paths)
    if any(name.startswith("src/") and name not in before["files"] for name in build):
        raise ValueError("current production source is absent from declared MSRV map")
    if base.sha(base.NATIVE) != base.NATIVE_SHA or base.sha(base.WRAPPER) != base.WRAPPER_SHA or base.sha(base.HELPER) != base.HELPER_SHA:
        raise ValueError("fixed checker/forwarder/helper changed")
    return dict(checkout_head=base.checkout_head(), cli_path=str(base.CLI), cli_sha256=base.sha(base.CLI),
        native_sha256=base.sha(base.NATIVE), binaries={str(base.CLI): base.record(base.CLI), str(base.NATIVE): base.record(base.NATIVE)},
        msrv_attempt=attempt, msrv_results_sha256=results_sha,
        msrv_declared_current_inputs=current, msrv_records=snapshot(p for p in folder.iterdir() if p.is_file()),
        production_and_context=build, extra_context_not_in_msrv_map=[n for n in build if n not in before["files"]],
        original_tree=snapshot(p for p in ORIGINAL.rglob("*") if p.is_file()),
        capture_design=snapshot((HERE / "driver.py", HERE / "README.md", PARENT, base.WRAPPER, base.HELPER)))


def prospective_freeze(attempt, results_sha):
    if base.sha(ORIGINAL / "first-files.json") != base.FIRST_SHA:
        raise ValueError("original FIRST41 changed")
    first = json.loads(base.read_bounded(ORIGINAL / "first-files.json"))["files"]
    if len(first) != 41 or any(base.record(base.repository_path(r["path"])) != {
            k: r[k] for k in ("bytes", "sha256", "mode")} for r in first):
        raise ValueError("actual complete FIRST sources changed")
    value = identity(attempt, results_sha)
    base.save(HERE / "prospective-inputs.json", dict(status="prospective-frozen-not-captured",
        identity=value, commands=[base.command(c, p, f) for c in base.CASES for p, f in base.FORMS],
        first_files_sha256=base.FIRST_SHA, scope="Declared incomplete closure; HEAD is not compiled-source attestation."))


def capture(inputs_sha):
    inputs = HERE / "prospective-inputs.json"
    if base.sha(inputs) != inputs_sha:
        raise ValueError("reviewed prospective input map changed")
    frozen = json.loads(base.read_bounded(inputs))
    order = [(c, p, f) for c in base.CASES for p, f in base.FORMS]
    if len(order) != 72 or [base.command(*item) for item in order] != frozen["commands"]:
        raise ValueError("literal 18 by 4 commands differ")
    def unchanged():
        if base.sha(inputs) != inputs_sha or identity(frozen["identity"]["msrv_attempt"],
                frozen["identity"]["msrv_results_sha256"]) != frozen["identity"]:
            raise ValueError("capture inputs or identities changed")
    unchanged()
    if not os.access(base.CLI, os.X_OK) or not os.access(base.WRAPPER, os.X_OK):
        raise ValueError("fixed CLI/forwarder not executable")
    helper = load(base.HELPER, base.HELPER_SHA, "reviewed_bounded_original_source_capture")
    soft, hard = resource.getrlimit(resource.RLIMIT_FSIZE)
    ceiling = min([LIMIT] + [n for n in (soft, hard) if n != resource.RLIM_INFINITY])
    resource.setrlimit(resource.RLIMIT_FSIZE, (ceiling, ceiling))
    out = HERE / "observations"
    out.mkdir(exist_ok=False)
    (out / "executed-driver.py.txt").open("xb").write(Path(__file__).read_bytes())
    base.save(out / "identity.before.json", frozen)
    rows = []
    try:
        for case, profile, presentation in order:
            unchanged()
            label = case + "-" + profile + "-check-" + presentation
            argv, journal = base.command(case, profile, presentation), out / (label + ".native.jsonl")
            journal.touch(exist_ok=False)
            env = dict(os.environ, QLEISLI_PARAMETER_NATIVE_LOG=str(journal), PYTHONDONTWRITEBYTECODE="1")
            for key in ("QLEISLI_KERNEL", "QLEISLI_HIERARCHY_KERNEL"):
                env.pop(key, None)
            base.save(out / (label + ".command-before.json"), dict(argv=argv, cwd=str(REPO), recorded_utc=base.timestamp()))
            result = helper.capture(argv, REPO, env, b"", seconds=55, output_limit=LIMIT)
            raw = {kind: result.pop(kind) for kind in ("stdout", "stderr")}
            for kind, data in raw.items():
                (out / (label + "." + kind + ".bin")).open("xb").write(data)
            journal_error, count = None, None
            try:
                count = len([json.loads(line) for line in base.read_bounded(journal).splitlines()])
            except (ValueError, UnicodeError) as error:
                journal_error = str(error)
            event = dict(argv=argv, cwd=str(REPO), recorded_utc=base.timestamp(), client_capture=result,
                exit_code=result["returncode"], raw={k: dict(path=label+"."+k+".bin", **base.record(out / (label+"."+k+".bin"))) for k in raw},
                native_journal=dict(path=journal.name, **base.record(journal)), native_forwarded_attempts=count,
                native_journal_parse_error=journal_error,
                native_count_scope="Forwarder rows immediately before execv; not independent native-start/exit attestations.")
            base.save(out / (label + ".json"), event)
            rows.append(dict(case=case, profile=profile, presentation=presentation,
                observation="observations/"+label+".json", exit_code=result["returncode"], native_forwarded_attempts=count))
            unchanged()
            print(label, result["returncode"], count, flush=True)
            if not result["spawned"] or result["reason"] is not None or journal_error is not None:
                base.save(out / "incomplete.json", dict(rows=rows, status="actual-operational-failure-no-retry",
                    client_capture=result, native_journal_parse_error=journal_error))
                return 1
        base.save(out / "summary.json", dict(rows=rows, actual_observation_count=len(rows),
            actual_successes=sum(r["exit_code"] == 0 for r in rows), actual_nonzero_exits=sum(r["exit_code"] != 0 for r in rows),
            native_forwarded_attempts=sum(r["native_forwarded_attempts"] for r in rows),
            scope="72 additive check observations only; no forced byte parity, source preservation, guarantee or issue completion."))
        unchanged()
        base.save(out / "identity.final.json", dict(identity=frozen["identity"], all_declared_inputs_unchanged=True))
        base.save(out / "files.json", dict(files={p.name: base.record(p) for p in sorted(out.iterdir()) if p.is_file()}, self_excluded="files.json"))
        return 0
    except BaseException as error:
        base.save(out / "incomplete.json", dict(status="capture-aborted-no-retry", completed_observations=len(rows),
            error_type=type(error).__name__, message=str(error)))
        raise


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_subparsers(dest="mode", required=True)
    freeze = modes.add_parser("freeze")
    freeze.add_argument("--msrv-attempt", required=True)
    freeze.add_argument("--msrv-results-sha256", required=True)
    modes.add_parser("capture").add_argument("--inputs-sha256", required=True)
    args = parser.parse_args()
    if sys.version_info < (3, 11):
        parser.error("Python 3.11+ required")
    digest = args.msrv_results_sha256 if args.mode == "freeze" else args.inputs_sha256
    if not re.fullmatch(r"[0-9a-f]{64}", digest):
        parser.error("explicit SHA must be 64 lowercase hexadecimal digits")
    if args.mode == "freeze":
        if not re.fullmatch(r"attempt-[0-9]{2}", args.msrv_attempt):
            parser.error("fixed local MSRV attempt must be attempt-NN")
        prospective_freeze(args.msrv_attempt, digest)
        return 0
    return capture(digest)


if __name__ == "__main__":
    raise SystemExit(main())
