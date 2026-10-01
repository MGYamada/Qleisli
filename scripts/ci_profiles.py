#!/usr/bin/env python3
"""Fail-closed CI selection and required-check aggregation (Issue #145).

This selects validation work, not acceptance authority or constitutional policy.
Only explicit descriptive documents/result records may skip compiler/proof work.
Every other path, missing diff and release/manual run uses the complete profile.
"""

import argparse
from fnmatch import fnmatchcase
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
SUITES = (
    "check-rust", "check-rust-msrv", "check-macos-source", "check-interop",
    "check-lean", "check-lean-kernel", "check-distribution", "check-docs",
)
SHA = re.compile(r"[0-9a-f]{40}\Z")


def valid_path(path: str) -> bool:
    return bool(path) and "\\" not in path and not any(ord(c) < 32 for c in path) and (
        not PurePosixPath(path).is_absolute() and ".." not in path.split("/")
        and path == str(PurePosixPath(path))
    )


def load_policy(root: Path) -> dict:
    policy = json.loads((root / ".github/ci/profiles.json").read_text(encoding="utf-8"))
    if set(policy) != {"format", "documentation_only", "result_records"} or policy["format"] != 1:
        raise ValueError("unknown CI profile policy")
    for field in ("documentation_only", "result_records"):
        if not isinstance(policy[field], list) or not all(isinstance(p, str) and valid_path(p) for p in policy[field]):
            raise ValueError(f"invalid {field}")
    return policy


def classify(paths: list[str], policy: dict) -> tuple[str, str]:
    if not paths:
        return "full", "empty diff; full validation required"
    for path in paths:
        if not valid_path(path):
            return "full", "unrecognized path; full validation required"
        if path.startswith((".github/", "scripts/", "src/", "lean/", "lean-kernel/", "corpus/", "stdlib/", "python/", "research/", "examples/")):
            return "full", f"protected executable/policy input: {path}"
        if path in policy["documentation_only"]:
            continue
        if any(len(path.split("/")) == len(pattern.split("/")) and all(
            fnmatchcase(part, glob) for part, glob in zip(path.split("/"), pattern.split("/"))
        ) for pattern in policy["result_records"]):
            continue
        return "full", f"protected or unclassified input: {path}"
    return "docs", "only explicitly listed descriptive documents/result records"


def git(root: Path, *args: str) -> str:
    return subprocess.run(["git", *args], cwd=root, check=True, capture_output=True).stdout.decode("utf-8")


def plan(root: Path, event_name: str, event: dict, expected_sha: str, ref: str) -> dict:
    policy = load_policy(root)
    head = git(root, "rev-parse", "HEAD").strip()
    if not SHA.fullmatch(expected_sha) or head != expected_sha:
        raise ValueError("checkout differs from the exact event commit")
    result = dict(format=1, head=head, event=event_name, ref=ref, base=None,
                  profile="full", reason="release, manual or unrecognized event", paths=[],
                  dependency_cache=event.get("inputs", {}).get("cache", "enabled"),
                  project_build_cache="disabled")
    if event_name not in {"pull_request", "push"} or ref.startswith("refs/tags/"):
        return result
    if event_name == "pull_request":
        base = event.get("pull_request", {}).get("base", {}).get("sha")
    else:
        if event.get("forced"):
            result["reason"] = "forced push; full validation required"
            return result
        base = event.get("before")
    if not isinstance(base, str) or not SHA.fullmatch(base) or base == "0" * 40:
        result["reason"] = "missing comparison base; full validation required"
        return result
    result["base"] = base
    try:
        git(root, "cat-file", "-e", f"{base}^{{commit}}")
        paths = git(root, "diff", "--no-renames", "--name-only", "-z", base, head, "--").split("\0")
        raw = git(root, "diff", "--raw", "--no-renames", "-z", base, head, "--").split("\0")
    except (subprocess.CalledProcessError, UnicodeError):
        result["reason"] = "unavailable diff; full validation required"
        return result
    result["paths"] = sorted(set(p for p in paths if p))
    for header in raw[:-1:2]:
        old_mode, new_mode = header.lstrip(":").split()[:2]
        if old_mode not in {"000000", "100644"} or new_mode not in {"000000", "100644"}:
            result["reason"] = "nonregular/executable artifact or mode change; full validation required"
            return result
    result["profile"], result["reason"] = classify(result["paths"], policy)
    result["policy_sha256"] = hashlib.sha256((root / ".github/ci/profiles.json").read_bytes()).hexdigest()
    return result


def check_needs(needs: dict, expected_sha: str) -> str:
    """Every legacy required context rejects any missing/failed selected suite."""
    if set(needs) != {"changes", *SUITES}:
        raise ValueError("missing or unexpected validation dependency")
    selection = needs["changes"]
    outputs = selection.get("outputs", {})
    profile = outputs.get("profile")
    if selection.get("result") != "success" or profile not in {"docs", "full"}:
        raise ValueError("validation selection failed or has an unknown profile")
    if not SHA.fullmatch(expected_sha) or outputs.get("head") != expected_sha:
        raise ValueError("validation selection is not bound to this commit")
    for name in SUITES:
        expected = "success" if profile == "full" or name == "check-docs" else "skipped"
        if needs[name].get("result") != expected:
            raise ValueError(f"{name}: expected {expected}, got {needs[name].get('result')}")
    return profile


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--gate", action="store_true")
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    try:
        if args.gate:
            needs = json.loads(os.environ["NEEDS_JSON"])
            if args.report:
                args.report.write_text(json.dumps(dict(format=1, head=os.environ["GITHUB_SHA"], needs=needs), indent=2) + "\n", encoding="utf-8")
            profile = check_needs(needs, os.environ["GITHUB_SHA"])
            print(f"Required checks passed for exact commit {os.environ['GITHUB_SHA']} ({profile} profile).")
            return 0
        event = json.loads(Path(os.environ["GITHUB_EVENT_PATH"]).read_text(encoding="utf-8"))
        result = plan(ROOT, os.environ["GITHUB_EVENT_NAME"], event, os.environ["GITHUB_SHA"], os.environ["GITHUB_REF"])
        encoded = json.dumps(result, indent=2) + "\n"
        if args.report:
            args.report.write_text(encoded, encoding="utf-8")
        with Path(os.environ["GITHUB_OUTPUT"]).open("a", encoding="utf-8") as output:
            output.write(f"profile={result['profile']}\nhead={result['head']}\n")
        if summary := os.environ.get("GITHUB_STEP_SUMMARY"):
            with Path(summary).open("a", encoding="utf-8") as output:
                output.write(f"CI profile: **{result['profile']}**. Commit `{result['head']}`.\n\n")
                output.write("```json\n" + encoded + "```\n")
        print(encoded, end="")
        return 0
    except (OSError, ValueError, KeyError, TypeError, subprocess.CalledProcessError) as failure:
        print(f"CI validation: {failure}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
