#!/usr/bin/env python3
"""Reject PRs with at least 1,000,000 added plus deleted Git text lines.

Only MGYamada/Qleisli PR #307 has the human-authorized existing-PR exception.
Hosted mode binds it to the PR event/merge parents or API-bound manual PR head.
Local --base/--head preflight has no exception. Moves count as delete plus add;
binary records are reported separately, not interpreted as zero-byte changes.
This gate counts immutable commits, never the working tree or API diff summaries.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from urllib.request import Request, urlopen


ROOT = Path(__file__).resolve().parents[1]
LIMIT = 1_000_000
EXCEPTION = ("MGYamada/Qleisli", 307)
SHA = re.compile(r"[0-9a-f]{40}\Z")
NUMBER = re.compile(rb"(?:0|[1-9][0-9]*)\Z")
REPOSITORY = re.compile(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+\Z")


def completion_pr(repository: str, number: int) -> dict:
    """Fetch read-only GitHub metadata; counts still come only from exact Git objects."""
    token = os.environ.get("GH_TOKEN")
    if not token:
        raise ValueError("manual PR validation requires its read-only workflow token")
    request = Request(f"https://api.github.com/repos/{repository}/pulls/{number}", headers={
        "Authorization": "Bearer " + token, "Accept": "application/vnd.github+json",
        "X-GitHub-Api-Version": "2022-11-28",
    })
    with urlopen(request, timeout=30) as response:
        raw = response.read((1 << 20) + 1)
    if len(raw) > 1 << 20:
        raise ValueError("PR metadata exceeds its bounded response size")
    return json.loads(raw, object_pairs_hook=unique_object)


def git(root: Path, *args: str) -> bytes:
    # Replacement objects and external/textconv diff commands cannot supply counts.
    return subprocess.run(
        ["git", "--no-replace-objects", *args], cwd=root, check=True,
        capture_output=True,
    ).stdout


def exact_commit(root: Path, value: str) -> str:
    if not isinstance(value, str) or not SHA.fullmatch(value):
        raise ValueError("an exact 40-character commit SHA is required")
    if git(root, "cat-file", "-t", value).strip() != b"commit" or (
        git(root, "rev-parse", "--verify", f"{value}^{{commit}}").strip().decode("ascii") != value
    ):
        raise ValueError("the supplied object is not that exact commit")
    return value


def parse_numstat(data: bytes) -> dict:
    """Parse --numstat -z --no-renames without interpreting path characters."""
    if not isinstance(data, bytes) or (data and not data.endswith(b"\0")):
        raise ValueError("missing or malformed NUL-terminated numstat data")
    result = dict(additions=0, deletions=0, text_files=0, binary_files=0)
    seen = set()
    for record in data.split(b"\0")[:-1]:
        fields = record.split(b"\t", 2)
        if len(fields) != 3 or not fields[2] or fields[2] in seen:
            raise ValueError("malformed or duplicate numstat path record")
        added, deleted, path = fields
        seen.add(path)
        if added == deleted == b"-":
            result["binary_files"] += 1
        elif NUMBER.fullmatch(added) and NUMBER.fullmatch(deleted):
            result["additions"] += int(added)
            result["deletions"] += int(deleted)
            result["text_files"] += 1
        else:
            raise ValueError("malformed numstat line counts")
    result["changed_files"] = len(seen)
    result["changed_lines"] = result["additions"] + result["deletions"]
    return result


def count_diff(root: Path, base: str, head: str) -> dict:
    if git(root, "rev-parse", "--is-shallow-repository").strip() != b"false":
        raise ValueError("complete Git history is required; shallow counts are refused")
    graft_path = Path(os.fsdecode(git(root, "rev-parse", "--git-path", "info/grafts").strip()))
    if not graft_path.is_absolute():
        graft_path = root / graft_path
    if graft_path.exists() and graft_path.read_bytes().strip():
        raise ValueError("local grafts cannot supply PR comparison history")
    exact_commit(root, base)
    exact_commit(root, head)
    bases = git(root, "merge-base", "--all", base, head).decode("ascii").splitlines()
    if len(bases) != 1:
        raise ValueError("a unique available merge base is required")
    merge_base = exact_commit(root, bases[0])
    data = git(root, "diff", "--numstat", "-z", "--no-renames", "--no-ext-diff",
               "--no-textconv", "--diff-algorithm=myers", "--ignore-submodules=none",
               merge_base, head, "--")
    return dict(base=base, head=head, merge_base=merge_base,
                numstat_sha256=hashlib.sha256(data).hexdigest(), **parse_numstat(data))


def policy_result(counts: dict, repository: str | None = None,
                  number: int | None = None) -> dict:
    # Only hosted_context supplies this pair. No CLI/env exemption switch exists.
    exception = (repository, number) == EXCEPTION and type(number) is int
    allowed = counts["changed_lines"] < LIMIT or exception
    return dict(format=1, status="allowed" if allowed else "forbidden",
                limit=LIMIT, repository=repository, pull_request=number,
                exception="MGYamada/Qleisli#307" if exception else None,
                count_policy="merge-base to head; no-renames; added plus deleted Git text lines",
                binary_policy="separate records; no byte-size limit or text-line assertion",
                **counts)


def hosted_context(root: Path, event_name: str, event: dict, expected_sha: str,
                   ref: str, repository: str) -> dict:
    """GitHub-provided context is trusted by the workflow, not authenticated here."""
    if not isinstance(event, dict) or not isinstance(repository, str) or not REPOSITORY.fullmatch(repository):
        raise ValueError("missing or malformed GitHub repository/event context")
    if event.get("repository", {}).get("full_name") != repository:
        raise ValueError("event repository differs from the workflow repository")
    exact_commit(root, expected_sha)
    if git(root, "rev-parse", "HEAD").strip().decode("ascii") != expected_sha:
        raise ValueError("checkout differs from the exact workflow commit")
    if event_name in {"push", "workflow_dispatch"}:
        if not isinstance(ref, str) or not ref.startswith(("refs/heads/", "refs/tags/")) or (
            "pull_request" in event
        ):
            raise ValueError("malformed non-PR workflow context")
        selected = event.get("inputs", {}).get("completion_pr", "") if event_name == "workflow_dispatch" else ""
        if selected:
            if not isinstance(selected, str) or not re.fullmatch(r"[1-9][0-9]{0,9}", selected) or int(selected) > 2**31 - 1:
                raise ValueError("invalid completion PR number")
            number = int(selected)
            pr = completion_pr(repository, number)
            if not isinstance(pr, dict) or type(pr.get("number")) is not int or pr["number"] != number:
                raise ValueError("completion PR metadata differs from the requested repository/number")
            base_info, head_info = pr.get("base"), pr.get("head")
            if not isinstance(base_info, dict) or not isinstance(head_info, dict) or not isinstance(
                    base_info.get("repo"), dict) or base_info["repo"].get("full_name") != repository:
                raise ValueError("completion PR metadata has no matching base/head repository")
            base = exact_commit(root, base_info.get("sha"))
            head = exact_commit(root, head_info.get("sha"))
            if head != expected_sha:
                raise ValueError("completion PR head differs from the exact workflow commit")
            result = policy_result(count_diff(root, base, head), repository, number)
            result.update(event=event_name, checkout_sha=expected_sha, merge_ref=None)
            return result
        return dict(format=1, status="not-applicable", event=event_name,
                    checkout_sha=expected_sha, repository=repository, limit=LIMIT,
                    reason="PR-size requirement does not apply to push or manual validation")
    if event_name != "pull_request":
        raise ValueError("unsupported or missing workflow event; PR-size gate cannot be skipped")
    pr = event.get("pull_request")
    if not isinstance(pr, dict):
        raise ValueError("missing pull-request context")
    number = event.get("number")
    if type(number) is not int or number <= 0 or pr.get("number") != number or (
        type(pr.get("number")) is not int or ref != f"refs/pull/{number}/merge"
    ):
        raise ValueError("pull-request number is not bound to the event and merge ref")
    base_info, head_info = pr.get("base"), pr.get("head")
    if not isinstance(base_info, dict) or not isinstance(head_info, dict) or (
        base_info.get("repo", {}).get("full_name") != repository
    ):
        raise ValueError("missing or inconsistent pull-request repository/commit context")
    head_repository = head_info.get("repo", {}).get("full_name")
    if not isinstance(head_repository, str) or not REPOSITORY.fullmatch(head_repository):
        raise ValueError("missing or malformed pull-request head repository")
    base, head = exact_commit(root, base_info.get("sha")), exact_commit(root, head_info.get("sha"))
    parents = git(root, "show", "-s", "--format=%P", expected_sha).decode("ascii").strip().split()
    if parents != [base, head]:
        raise ValueError("checkout merge parents do not match the exact event base and head")
    result = policy_result(count_diff(root, base, head), repository, number)
    result.update(event=event_name, checkout_sha=expected_sha, merge_ref=ref)
    return result


def unique_object(pairs: list) -> dict:
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate event field: {key}")
        result[key] = value
    return result


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base", help="exact base commit for local preflight (with --head)")
    parser.add_argument("--head", help="exact head commit for local preflight (with --base)")
    parser.add_argument("--report", type=Path)
    args = parser.parse_args(argv)
    try:
        if args.base is not None or args.head is not None:
            if args.base is None or args.head is None:
                raise ValueError("local preflight requires both --base and --head")
            if os.environ.get("GITHUB_ACTIONS") == "true":
                raise ValueError("local preflight cannot replace the hosted event-bound gate")
            result = policy_result(count_diff(ROOT, args.base, args.head))
            result["event"] = "local-preflight"
        else:
            event = json.loads(Path(os.environ["GITHUB_EVENT_PATH"]).read_text(encoding="utf-8"),
                               object_pairs_hook=unique_object)
            result = hosted_context(ROOT, os.environ["GITHUB_EVENT_NAME"], event,
                                    os.environ["GITHUB_SHA"], os.environ["GITHUB_REF"],
                                    os.environ["GITHUB_REPOSITORY"])
        success = result["status"] != "forbidden"
    except (OSError, ValueError, KeyError, TypeError, AttributeError, UnicodeError,
            subprocess.CalledProcessError) as failure:
        result = dict(format=1, status="error", limit=LIMIT, reason=str(failure))
        success = False
    encoded = json.dumps(result, indent=2) + "\n"
    try:
        if args.report:
            args.report.write_text(encoded, encoding="utf-8")
        print(encoded, end="", file=sys.stdout if success else sys.stderr)
    except OSError as failure:
        print(f"PR-size report failed: {failure}", file=sys.stderr)
        return 1
    return 0 if success else 1


if __name__ == "__main__":
    sys.exit(main())

# Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
