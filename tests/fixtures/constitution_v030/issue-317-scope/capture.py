#!/usr/bin/env python3
"""Capture fixed local scope-accounting checks; never execute record commands."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent
BASE = "faa5cfb5e7ea1cf3b39a43b80f7f2345e89197c2"
CHANGED = [
    "scripts/check_release_ready.py", "scripts/test_check_release_ready.py",
    ".github/ci/README.md", "docs/src/design/ratification.md",
]
INPUTS = CHANGED + [
    "scripts/ci_profiles.py", "scripts/test_ci_profiles.py",
    ".github/ci/profiles.json", "CONSTITUTION.md", "GOVERNANCE.md",
    "governance/ratification-2026.json", "governance/guarantees.json",
    "governance/interpretations/initial-2026-reviewed.txt",
    "governance/interpretations/initial-2026-adoption.json",
    "governance/proposals/exactness-2026.md",
    "governance/interpretations/exactness-2026-adoption.json",
    "governance/proposals/initial-guarantees.json",
    "governance/guarantees/initial-2026-admission.json",
    "governance/guarantees/current-evidence.json",
    "tests/fixtures/constitution_v030/issue-317-scope/issue-317.md",
    "tests/fixtures/constitution_v030/issue-317-scope/request.json",
]


def encoded(value):
    return (json.dumps(value, sort_keys=True, indent=2) + "\n").encode()


def write(path, data):
    with path.open("xb") as output:
        output.write(data)


def source_map():
    files = {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
             for name in sorted(INPUTS)}
    return dict(files=files, sha256=hashlib.sha256(encoded(files)).hexdigest(),
                algorithm="sha256-json-sort_keys-indent2-newline-path-content-map-v1")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("phase", choices=["before", "after"])
    args = parser.parse_args()
    directory = HERE / args.phase
    directory.mkdir(exist_ok=False)
    starting = source_map()
    write(directory / "source-before.json", encoded(starting))
    commands = [
        [sys.executable, "scripts/check_constitution.py", "--base-ref", BASE],
        [sys.executable, "scripts/test_check_release_ready.py"],
        [sys.executable, "scripts/test_ci_profiles.py"],
    ]
    if args.phase == "after":
        commands.extend([
            [sys.executable, "scripts/check_docs.py"],
            ["git", "diff", "--check", "--", *CHANGED],
        ])
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")
    records = []
    for index, argv in enumerate(commands, 1):
        started = time.monotonic()
        observed = datetime.now(timezone.utc).isoformat()
        result = subprocess.run(argv, cwd=ROOT, env=env, capture_output=True,
                                timeout=180)
        stdout = f"{index:02d}.stdout.txt"
        stderr = f"{index:02d}.stderr.txt"
        write(directory / stdout, result.stdout)
        write(directory / stderr, result.stderr)
        records.append(dict(argv=argv, cwd=str(ROOT), observed_utc=observed,
                            timeout_seconds=180, seconds=time.monotonic() - started,
                            exit_code=result.returncode, stdout=stdout, stderr=stderr))
        print(f"{args.phase}: {argv[1]} exit {result.returncode}", flush=True)
    final = source_map()
    write(directory / "source-after.json", encoded(final))
    write(directory / "commands.json", encoded(records))
    sys.path.insert(0, str(ROOT / "scripts"))
    sys.dont_write_bytecode = True
    import check_release_ready as checker
    import ci_profiles
    policy = ci_profiles.load_policy(ROOT)
    scope = dict(issue_count=len(checker.ISSUES), groups=checker.GROUPS,
                 assigned_paths=CHANGED,
                 ci_suite_profile=ci_profiles.classify(CHANGED, policy)[0],
                 proof_lane=ci_profiles.proof_lane(CHANGED, policy),
                 hosted_ci="not-run", release_approval="not-granted")
    write(directory / "scope.json", encoded(scope))
    if final != starting:
        raise SystemExit("captured inputs changed during checks")
    if args.phase == "after":
        previous = json.loads((HERE / "before/source-after.json").read_bytes())
        changed = [name for name in INPUTS
                   if previous["files"][name] != final["files"][name]]
        write(directory / "metadata-audit.json", encoded(dict(
            changed_paths=changed, expected_changed_paths=CHANGED,
            other_captured_inputs_unchanged=sorted(changed) == sorted(CHANGED),
            issue_317_original_criteria_implemented=0,
            no_guardian_or_proof_status_change=True)))
        if sorted(changed) != sorted(CHANGED):
            raise SystemExit("unexpected captured input changes")
    if any(record["exit_code"] for record in records):
        raise SystemExit("a captured check failed; keep the actual records")


if __name__ == "__main__":
    main()
