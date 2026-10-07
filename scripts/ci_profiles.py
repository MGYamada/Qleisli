#!/usr/bin/env python3
"""Fail-closed CI selection and required-check aggregation (Issue #145).

This selects validation work, not acceptance authority or constitutional policy.
Only explicit descriptive documents/result records may skip executable tests.
Routine validation is test-oriented; proof maintenance and fresh full replay
are separately selected. Missing/unknown inputs still select full proof replay.
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
PROTECTED_ROOTS = {
    "Cargo.toml", "Cargo.lock", "LICENSE", "NOTICE", "TRUSTBOUNDARY.md",
    "CONSTITUTION.md", "GOVERNANCE.md", "STDLIB.md", "README.crates.md",
}
NORMATIVE_DOCS = {"TRUSTBOUNDARY.md"}


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
        if path in PROTECTED_ROOTS | NORMATIVE_DOCS or PurePosixPath(path).suffix in {".rs", ".lean", ".qli", ".qlt", ".toml", ".lock"} or path.startswith((".github/", "scripts/", "src/", "lean/", "lean-kernel/", "corpus/", "stdlib/", "python/", "research/", "examples/", "docs/", "docs-old/", "governance/", "tests/fixtures/constitution_v030/")):
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


def proof_lane(paths: list[str], policy: dict | None = None,
               registry_source_only: bool = False) -> str:
    """Kernel proofs compile with the executable; Mathlib proofs need their own build."""
    if not paths:
        return "full"
    policy = policy or load_policy(ROOT)
    model = False
    for path in paths:
        if path == "lean/schema-registry.json" and registry_source_only:
            continue
        if not valid_path(path) or path.startswith((".github/", "governance/", "tests/fixtures/constitution_v030/")) or path in {
            "TRUSTBOUNDARY.md", "CONSTITUTION.md", "GOVERNANCE.md",
            "scripts/ci_profiles.py", "scripts/run_native_ci.py",
            "scripts/package_lean_kernel.py",
            "scripts/check_lean_kernel.py", "scripts/check_schema_registry.py",
            "lean/Audit.lean", "lean-kernel/Audit.lean",
            "lean/schema-registry.json",
        } or path.endswith(("lean-toolchain", "lakefile.toml", "lake-manifest.json")):
            return "full"
        if classify([path], policy)[0] == "docs":
            continue
        if path.startswith("lean/") or path in NORMATIVE_DOCS:
            model = True
        elif not (path.startswith(("src/", "tests/", "lean-kernel/", "corpus/",
                                   "stdlib/", "python/", "research/", "examples/",
                                   "scripts/test_", "scripts/check_input_corpus"))
                  or path in {"Cargo.toml", "Cargo.lock", "CHANGELOG.md", "README.md",
                              "README.crates.md", "LICENSE", "NOTICE", "ROADMAP.md"}):
            return "full"
    return "model" if model else "tests"


def registry_binding_only(root: Path, base: str, head: str) -> bool:
    """Only source identity may change without rebuilding exported theorem types."""
    from check_schema_registry import RegistryError, read_json
    try:
        versions = [read_json(git(root, "show", f"{revision}:lean/schema-registry.json").encode())
                    for revision in (base, head)]
        for manifest in versions:
            if not isinstance(manifest, dict) or set(manifest) != {
                "format", "version", "profile", "lean_toolchain", "source_revision", "checker", "entries"
            } or type(manifest["version"]) is not int or manifest["version"] != 1 or (
                manifest["format"] != "qleisli.schema-registry"
                or manifest["profile"] != "qpe-dyadic8-v1"
                or manifest["lean_toolchain"] != "leanprover/lean4:v4.30.0"
            ):
                return False
        return ({key: value for key, value in versions[0].items() if key != "source_revision"}
                == {key: value for key, value in versions[1].items() if key != "source_revision"})
    except (RegistryError, OSError, ValueError, subprocess.CalledProcessError, UnicodeError):
        return False


def plan(root: Path, event_name: str, event: dict, expected_sha: str, ref: str) -> dict:
    policy = load_policy(root)
    head = git(root, "rev-parse", "HEAD").strip()
    if not SHA.fullmatch(expected_sha) or head != expected_sha:
        raise ValueError("checkout differs from the exact event commit")
    result = dict(format=1, head=head, event=event_name, ref=ref, base=None,
                  profile="full", proof_lane="full", reason="release, manual or unrecognized event", paths=[],
                  dependency_cache=event.get("inputs", {}).get("cache", "enabled"),
                  project_build_cache="disabled")
    if ref.startswith(("refs/tags/", "refs/heads/codex/release-", "refs/heads/release/")):
        result["reason"] = "release ref; fresh full validation"
        return result
    if event_name == "workflow_dispatch":
        requested = event.get("inputs", {}).get("validation", "full")
        if requested not in {"tests", "full"}:
            raise ValueError("unknown manual validation lane")
        result["proof_lane"] = requested
        return result
    if event_name not in {"pull_request", "push"}:
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
    source_only = "lean/schema-registry.json" in result["paths"] and registry_binding_only(root, base, head)
    result["registry_source_only_change"] = source_only
    result["proof_lane"] = "tests" if result["profile"] == "docs" else proof_lane(result["paths"], policy, source_only)
    if event_name == "pull_request" and event.get("pull_request", {}).get("head", {}).get("ref", "").startswith(("codex/release-", "release/")):
        result.update(profile="full", proof_lane="full", reason="release branch; fresh full validation")
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
    if outputs.get("proof_lane") not in {"tests", "model", "full"}:
        raise ValueError("missing or unknown proof-maintenance lane")
    if profile == "docs" and outputs["proof_lane"] != "tests":
        raise ValueError("inconsistent documentation lane")
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
    parser.add_argument("--checks", help="execute a group from the shared check manifest")
    parser.add_argument("--plan", action="store_true")
    parser.add_argument("--compiler", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    try:
        if args.checks:
            import ci_source_checks
            if args.gate:
                raise ValueError("--checks and --gate are separate operations")
            if args.plan:
                print(json.dumps(dict(status="not-run", group=args.checks,
                                      commands=ci_source_checks.plan(args.checks, args.compiler)), indent=2))
                return 0
            if args.output is None:
                raise ValueError("executing --checks requires --output")
            return ci_source_checks.execute(args.checks, args.compiler, args.output)
        if args.plan or args.compiler is not None or args.output is not None:
            raise ValueError("source-check options require --checks")
        if args.gate:
            needs = json.loads(os.environ["NEEDS_JSON"])
            if args.report:
                args.report.write_text(json.dumps(dict(format=1, head=os.environ["GITHUB_SHA"], needs=needs), indent=2) + "\n", encoding="utf-8")
            if summary := os.environ.get("GITHUB_STEP_SUMMARY"):
                with Path(summary).open("a", encoding="utf-8") as output:
                    output.write("Producer results for commit `" + os.environ["GITHUB_SHA"] + "`.\n\n")
                    output.write("| Producer | Result |\n| --- | --- |\n")
                    for name in ("changes", *SUITES):
                        result = needs.get(name, {}).get("result", "missing")
                        output.write(f"| {name} | {result} |\n")
                    output.write("\nEach required context reports this complete gate; a failed context is not an additional producer failure.\n")
            profile = check_needs(needs, os.environ["GITHUB_SHA"])
            lane = needs["changes"]["outputs"]["proof_lane"]
            print(f"Required checks passed for exact commit {os.environ['GITHUB_SHA']} (suites: {profile}; proof lane: {lane}).")
            return 0
        event = json.loads(Path(os.environ["GITHUB_EVENT_PATH"]).read_text(encoding="utf-8"))
        result = plan(ROOT, os.environ["GITHUB_EVENT_NAME"], event, os.environ["GITHUB_SHA"], os.environ["GITHUB_REF"])
        encoded = json.dumps(result, indent=2) + "\n"
        if args.report:
            args.report.write_text(encoded, encoding="utf-8")
        with Path(os.environ["GITHUB_OUTPUT"]).open("a", encoding="utf-8") as output:
            output.write(f"profile={result['profile']}\nproof_lane={result['proof_lane']}\nhead={result['head']}\n")
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
