#!/usr/bin/env python3
"""Fresh fixed proof maintenance; produce a reviewable patch, never acceptance.

Run only in a clean disposable exact-commit checkout. No imported success
receipts, replacement commands, profiles, output references or proof limits.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
"""
import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import time

import check_schema_registry as registry
import check_initial_guarantees as guarantees
import check_guarantee_continuity as continuity
import check_pr_size as size_policy
import check_fixture_budget as fixture_policy
import check_fixture_references as reference_policy

ROOT = Path(__file__).resolve().parents[1]
SCHEMA = "lean/schema-registry.json"
AUDIT = guarantees.CURRENT_AUDIT_PATH
CURRENT = guarantees.CURRENT_PATH
LEDGER = "governance/guarantees.json"
ALLOWED = frozenset((SCHEMA, AUDIT, CURRENT, LEDGER))
TRUSTED = "28c6e75ac7341e53f8a06c22bd6634b8cbbc38cb"
BASE = "0bd108183649e0462cb5c5b1c8bae29d07e1c9fc"
KERNEL = "lean-kernel/.lake/build/bin/qleisli-kernel"
FIXED = (
    ("review", "lean", guarantees.REVIEW_ARGV, guarantees.REVIEW_STDOUT),
    ("binding", "lean", guarantees.BINDING_ARGV, guarantees.BINDING_STDOUT),
    ("basis", "lean", continuity.TRANSPORT_ARGV, continuity.TRANSPORT_STDOUT),
    ("raw", "lean", continuity.RAW_REVIEW_ARGV, continuity.RAW_STDOUT),
    ("extract", "lean", continuity.RAW_ARGV, continuity.CURRENT_PATH),
    ("main", "lean-kernel", guarantees.REPLAY_ARGV, guarantees.REPLAY_STDOUT),
)
TIMEOUTS = dict(size=180, fixtures=180, references=180, registry=900, review=180,
    binding=180, basis=180, raw=180, extract=300, main=900,
    **{"lean-version": 60, "full-tests": 900, "hierarchical-current": 900,
       "schema-source": 180, "initial": 180, "constitution": 180})


def require(value, message):
    if not value:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def encoded(value):
    return (json.dumps(value, indent=2, ensure_ascii=False) + "\n").encode()


def git(*args):
    return subprocess.check_output(["git", "--no-replace-objects", *args], cwd=ROOT)


def inventory():
    names = set(git("ls-files", "--cached", "--others", "--exclude-standard", "-z").split(b"\0")) - {b""}
    result = {}
    for raw in sorted(names):
        name = os.fsdecode(raw)
        path = ROOT / name
        require(path.is_file() and not path.is_symlink(), "missing/linked source: " + name)
        with path.open("rb") as stream:
            result[name] = {"sha256": hashlib.file_digest(stream, "sha256").hexdigest(), "mode": path.stat().st_mode & 0o777}
    return result


def unchanged(before, after, allowed):
    changed = {name for name in set(before) | set(after) if before.get(name) != after.get(name)}
    require(changed <= set(allowed), "source drift outside fixed record allowlist: " + repr(sorted(changed)))
    return changed


def exact_head(expected, actual):
    require(re.fullmatch(r"[0-9a-f]{40}", expected) is not None and expected == actual, "source commit changed or is not exact")


def hosted_context(commit, environment):
    expected = {"GITHUB_REPOSITORY": "MGYamada/Qleisli", "GITHUB_REF": "refs/heads/codex/beta-finite-adts", "GITHUB_SHA": commit, "GITHUB_JOB": "produce-review-artifact"}
    require(all(environment.get(key) == value for key, value in expected.items()), "wrong hosted repository/ref/head/job")
    require(environment.get("GITHUB_EVENT_NAME") in {"push", "workflow_dispatch"}, "wrong hosted event")
    for key in ("GITHUB_RUN_ID", "GITHUB_RUN_ATTEMPT"):
        require(re.fullmatch(r"[1-9][0-9]*", environment.get(key, "")) is not None, "invalid hosted run identity")
    workflow = "MGYamada/Qleisli/.github/workflows/current-proof-records.yml@refs/heads/codex/beta-finite-adts"
    require(environment.get("GITHUB_WORKFLOW_REF") == workflow and environment.get("GITHUB_WORKFLOW_SHA") == commit, "workflow source differs from selected head")
    return {key: environment[key] for key in (*expected, "GITHUB_EVENT_NAME", "GITHUB_RUN_ID", "GITHUB_RUN_ATTEMPT", "GITHUB_WORKFLOW_REF", "GITHUB_WORKFLOW_SHA")}


def actual_result(code, stdout, stderr, expected=None):
    require(type(code) is int and code == 0, "fixed command failed")
    if expected is not None:
        require(stderr == b"" and stdout == expected, "fixed proof output differs; references are immutable")


def exact_records(planned, actual):
    require(set(planned) == ALLOWED and actual == planned, "planned four-record bytes changed after validation")


def complete_fixed_results(results):
    require(set(results) == {row[0] for row in FIXED}, "missing or unexpected fixed proof stage")
    require(all(type(row.get("exit_code")) is int and row["exit_code"] == 0 for row in results.values()), "failed or skipped fixed proof stage")


def lean_version(output):
    require(re.fullmatch(rb"Lean \(version 4\.30\.0, [^\r\n]+\)\r?\n", output) is not None, "actual Lean toolchain differs from pinned version")


def cumulative(head):
    exact_head(head, git("rev-parse", "HEAD").decode().strip())
    diff = size_policy.count_diff(ROOT, BASE, head)
    whole = size_policy.policy_result(diff)  # Additional fixed-base check; no PR exception.
    policy, digest = fixture_policy.load_policy(ROOT, head)
    fixtures = fixture_policy.enforce(policy, fixture_policy.committed_totals(ROOT, head), fixture_policy.fixture_growth(ROOT, diff["base"], diff["head"], diff["merge_base"]))
    references = reference_policy.inspect(ROOT, BASE, head)
    require(all(row["status"] == "allowed" for row in (whole, fixtures, references)), "cumulative size/fixture/reference policy refused")
    return dict(format="qleisli.cumulative-proof-preflight", base=BASE, head=head, policy_sha256=digest, whole=whole, fixtures=fixtures, references=references)


def execute(argv, cwd, stdout, stderr, limit):
    process = subprocess.Popen(argv, cwd=cwd, stdout=stdout, stderr=stderr, start_new_session=True)
    try:
        return process.wait(timeout=limit), None
    except subprocess.TimeoutExpired:
        # This group belongs only to this invocation. Always kill lingering
        # descendants too, even if Lake exits promptly after SIGTERM.
        for signum in (signal.SIGTERM, signal.SIGKILL):
            try:
                os.killpg(process.pid, signum)
            except ProcessLookupError:
                pass
            if signum == signal.SIGTERM:
                try:
                    process.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    pass
        process.wait()
        return process.returncode, "timeout"


def proposed(current, ledger, revision, audit_bytes, schema_bytes, results):
    require(current["continuity"]["format"] == continuity.RAW_FORMAT, "unsupported current proof profile")
    fresh = copy.deepcopy(current)
    validation = fresh["validation"]
    alpha = copy.deepcopy(validation["observed_native_build"])
    validation["source_revision"] = revision
    validation["files"][SCHEMA] = sha(schema_bytes)
    validation["files"][AUDIT] = sha(audit_bytes)
    validation["commands"][0]["seconds"] = results["review"]["seconds"]
    validation["commands"][1]["seconds"] = results["main"]["seconds"]
    fresh["binding_review"]["command"]["seconds"] = results["binding"]["seconds"]
    fresh["continuity"]["source_revision_sha256"] = revision["sha256"]
    validation["native_binary_note"] = "observed_native_build remains immutable historical alpha data; the outside fresh proof artifact records the current checker only as a build identity, with no binary-source/runtime attestation."
    old = "Ordinary source ADT execution, host-selected roots, constructors/match/qmatch and source-function preservation remain pending."
    new = "Common static plans and classical constructors are implemented, and the explicit check-only source carrier adapter replays retained source steps against a fresh typed native body equation. Ordinary nominal runtime, match/qmatch and the original AST/source-function preservation theorem remain pending."
    validation["scope"] = validation["scope"].replace(old, new).replace("Evidence argv spells lake canonically; the retained fresh report records the actual /opt/homebrew/bin/lake executable and observed command outputs.", "Fresh canonical argv and complete observed streams are retained in the separate proof-maintenance artifact; this does not grant normal CI, release readiness or Issue completion.")
    require(validation["observed_native_build"] == alpha, "historical alpha identity changed")
    payload = encoded(fresh)
    updated = copy.deepcopy(ledger)
    bindings = [row for row in updated["current_bindings"] if row["evidence"]["path"] == CURRENT]
    require(len(bindings) == 1, "ambiguous ledger current binding")
    bindings[0]["evidence"]["sha256"] = sha(payload)
    return {AUDIT: audit_bytes, CURRENT: payload, LEDGER: encoded(updated)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-commit", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    exact_head(args.source_commit, git("rev-parse", "HEAD").decode().strip())
    hosted = hosted_context(args.source_commit, os.environ)
    require(git("status", "--porcelain=v1", "-z") == b"", "proof producer requires clean disposable checkout")
    output = registry.command_output_directory(ROOT, args.output)
    before = inventory()
    originals = {name: (ROOT / name).read_bytes() for name in ALLOWED}
    current, ledger = (json.loads(originals[name]) for name in (CURRENT, LEDGER))
    report = dict(format="qleisli.current-proof-maintenance", version=1, source_commit=args.source_commit, tree=git("rev-parse", "HEAD^{tree}").decode().strip(), hosted=hosted, status="failed", commands=[], before=before, scope="Reviewable derived metadata only; no new guarantee, AST proof, normal CI green credit, release readiness, commit, merge or publication.")

    def window(allowed):
        exact_head(args.source_commit, git("rev-parse", "HEAD").decode().strip())
        unchanged(before, inventory(), allowed)

    def run(label, cwd, argv, expected=None, kernel=None, allowed=frozenset({SCHEMA})):
        window(allowed)
        directory = output / label
        directory.mkdir()
        started = time.monotonic()
        with (directory / "stdout").open("wb") as stdout, (directory / "stderr").open("wb") as stderr:
            code, reason = execute(argv, ROOT / cwd, stdout, stderr, TIMEOUTS[label])
        row = dict(argv=argv, cwd=cwd, exit_code=code, stop_reason=reason, timeout_seconds=TIMEOUTS[label], seconds=time.monotonic() - started, stdout_sha256=sha((directory / "stdout").read_bytes()), stderr_sha256=sha((directory / "stderr").read_bytes()))
        report["commands"].append(row)
        (directory / "command.json").write_bytes(encoded(row))
        require(reason is None, "fixed command timed out")
        actual_result(code, (directory / "stdout").read_bytes(), (directory / "stderr").read_bytes(), expected)
        window(allowed)
        if kernel is not None:
            require(sha((ROOT / KERNEL).read_bytes()) == kernel, "checker changed across proof window")
        return row

    try:
        for label, argv in (("size", ["scripts/check_pr_size.py"]), ("fixtures", ["scripts/check_fixture_budget.py", "--hosted"]), ("references", ["scripts/check_fixture_references.py", "--hosted"])):
            run(label, ".", [sys.executable, *argv])
        (output / "cumulative-preflight.json").write_bytes(encoded(cumulative(args.source_commit)))
        run("lean-version", "lean-kernel", ["lake", "env", "lean", "--version"])
        lean_version((output / "lean-version/stdout").read_bytes())
        run("registry", ".", [sys.executable, "scripts/check_schema_registry.py", "--write", "--report", str(output / "registry-report.json"), "--command-output-dir", str(output / "registry-commands")])
        audit_bytes = (output / "registry-report.json").read_bytes()
        audit = json.loads(audit_bytes)
        revision = registry.source_revision(ROOT)
        guarantees.validate_audit_record(audit_bytes, revision, sha((ROOT / SCHEMA).read_bytes()))
        window({SCHEMA})
        kernel = sha((ROOT / KERNEL).read_bytes())
        report["kernel_sha256"] = kernel
        report["source_revision"] = revision
        run("full-tests", "lean-kernel", ["lake", "env", "lean", "-DwarningAsError=true", "Tests.lean"], kernel=kernel)
        run("hierarchical-current", "lean-kernel", ["lake", "env", "lean", "-DwarningAsError=true", "../tests/fixtures/hierarchical_prepared_v030/Current.lean"], kernel=kernel)
        results = {}
        for label, cwd, argv, reference in FIXED:
            expected = (ROOT / reference).read_bytes()
            if label == "extract":
                expected = continuity.decompressed(expected)
            results[label] = run(label, cwd, argv, expected, kernel)
        complete_fixed_results(results)
        for index, command in enumerate(audit["commands"]):
            for stream in ("stdout", "stderr"):
                require(sha((output / "registry-commands" / f"{index:02d}" / stream).read_bytes()) == command[stream + "_sha256"], "retained canonical command stream changed")
        require(registry.source_revision(ROOT) == revision, "Lean source closure changed")
        schema_bytes = (ROOT / SCHEMA).read_bytes()
        updates = proposed(current, ledger, revision, audit_bytes, schema_bytes, results)
        planned = {SCHEMA: schema_bytes, **updates}
        for name, data in updates.items():
            (ROOT / name).write_bytes(data)
        window(ALLOWED)
        for label, argv in (("schema-source", ["scripts/check_schema_registry.py", "--source-only"]), ("initial", ["scripts/check_initial_guarantees.py"]), ("constitution", ["scripts/check_constitution.py", "--base-ref", TRUSTED])):
            run(label, ".", [sys.executable, *argv], allowed=ALLOWED)
        window(ALLOWED)
        require(registry.source_revision(ROOT) == revision and sha((ROOT / KERNEL).read_bytes()) == kernel, "final source/checker drift")
        exact_records(planned, {name: (ROOT / name).read_bytes() for name in ALLOWED})
        patch = git("diff", "--binary", "--no-ext-diff", "--", *sorted(ALLOWED))
        report["after"] = inventory()
        report["changed_paths"] = sorted(unchanged(before, report["after"], ALLOWED))
        report["patch_sha256"] = sha(patch)
        report["status"] = "validated-pending-source-restoration"
    except BaseException as error:
        report["error"] = f"{type(error).__name__}: {error}"
        raise
    finally:
        for name, data in originals.items():
            (ROOT / name).write_bytes(data)
        try:
            report["restored"] = inventory()
            unchanged(before, report["restored"], set())
            exact_head(args.source_commit, git("rev-parse", "HEAD").decode().strip())
        except BaseException as error:
            report.update(status="failed", error=f"source restoration failed: {error}")
            raise
        finally:
            (output / "report.json").write_bytes(encoded(report))
    require(report["status"] == "validated-pending-source-restoration", "fresh validation incomplete")
    for name, data in planned.items():
        path = output / "proposed" / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
    (output / "current-records.patch").write_bytes(patch)
    report["status"] = "passed"
    (output / "report.json").write_bytes(encoded(report))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
