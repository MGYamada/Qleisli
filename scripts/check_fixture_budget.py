#!/usr/bin/env python3
"""Bound fixture growth before CI scheduling and before local commits.

Hosted checks count the exact committed checkout tree. Local default checks
every fixture-tree file, including ignored/untracked files, without following
symlinks. Explicit local --base/--head checks committed head and PR additions;
it has no PR exception. Configuration cannot raise the operational ceilings.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import stat
import subprocess
import sys

from check_pr_size import (
    EXCEPTION, NUMBER, ROOT, SHA, exact_commit, git, hosted_context, unique_object,
)


POLICY_PATH = ".github/ci/size-budgets.json"
FIXTURE_ROOT = "tests/fixtures"
CEILINGS = dict(max_bytes=150 * 1024 * 1024, max_files=18_000, max_added_lines=100_000)
LFS_PREFIX = b"version https://git-lfs.github.com/spec/v1"


def validate_policy(policy: dict) -> dict:
    if not isinstance(policy, dict) or set(policy) != {
        "format", "version", "fixture_root", "totals", "pull_request"
    } or policy["format"] != "qleisli.fixture-size-budgets" or (
        type(policy["version"]) is not int or policy["version"] != 1
        or policy["fixture_root"] != FIXTURE_ROOT
    ):
        raise ValueError("unknown fixture-budget policy")
    totals, pr = policy["totals"], policy["pull_request"]
    if not isinstance(totals, dict) or set(totals) != {"max_bytes", "max_files"} or (
        not isinstance(pr, dict) or set(pr) != {"max_added_lines", "exception"}
    ):
        raise ValueError("missing or unexpected fixture-budget fields")
    for key, value in {**totals, "max_added_lines": pr["max_added_lines"]}.items():
        if type(value) is not int or not 0 < value <= CEILINGS[key]:
            raise ValueError("fixture budgets must be positive and cannot raise configured ceilings")
    exception = pr["exception"]
    if not isinstance(exception, dict) or set(exception) != {"repository", "number"} or (
        type(exception["number"]) is not int
        or (exception["repository"], exception["number"]) != EXCEPTION
    ):
        raise ValueError("only the existing canonical PR #307 growth exception is configured")
    return policy


def load_policy(root: Path, commit: str | None = None) -> tuple[dict, str]:
    data = (root / POLICY_PATH).read_bytes()
    if commit is not None and git(root, "show", f"{exact_commit(root, commit)}:{POLICY_PATH}") != data:
        raise ValueError("working policy differs from the exact counted commit")
    policy = validate_policy(json.loads(data, object_pairs_hook=unique_object))
    return policy, hashlib.sha256(data).hexdigest()


def records(data: bytes) -> list[bytes]:
    if not isinstance(data, bytes) or (data and not data.endswith(b"\0")):
        raise ValueError("missing or malformed NUL-terminated Git data")
    result = data.split(b"\0")[:-1]
    if any(not record for record in result):
        raise ValueError("empty Git record")
    return result


def fixture_path(path: bytes) -> bool:
    return path.startswith(FIXTURE_ROOT.encode() + b"/") and all(
        component not in {b"", b".", b".."} for component in path.split(b"/")
    )


def assert_tree_ancestry(root: Path, commit: str) -> None:
    components = FIXTURE_ROOT.split("/")
    for end in range(1, len(components) + 1):
        path = "/".join(components[:end])
        entries = records(git(root, "ls-tree", "-z", commit, "--", path))
        if len(entries) != 1:
            raise ValueError("fixture root and its ancestors must exist as Git directories")
        header, separator, found = entries[0].partition(b"\t")
        fields = header.split()
        if not separator or found != path.encode() or len(fields) != 3 or (
            fields[:2] != [b"040000", b"tree"]
            or not SHA.fullmatch(fields[2].decode("ascii"))
        ):
            raise ValueError("fixture-root ancestry contains a symlink or non-directory Git entry")


def parse_tree_sizes(data: bytes) -> tuple[dict, set[str]]:
    seen = set()
    total = 0
    pointer_candidates = set()
    for record in records(data):
        header, separator, path = record.partition(b"\t")
        fields = header.split()
        if not separator or len(fields) != 4 or fields[0] not in {b"100644", b"100755"} or (
            fields[1] != b"blob" or not SHA.fullmatch(fields[2].decode("ascii"))
            or not NUMBER.fullmatch(fields[3]) or not fixture_path(path) or path in seen
        ):
            raise ValueError("malformed fixture tree, symlink, submodule or duplicate path")
        size = int(fields[3])
        seen.add(path)
        total += size  # Same blob/hardlinked content counts once for EACH path.
        if len(LFS_PREFIX) <= size <= 1024:
            pointer_candidates.add(fields[2].decode("ascii"))
    return dict(files=len(seen), bytes=total), pointer_candidates


def reject_lfs_blobs(root: Path, candidates: set[str]) -> None:
    # Only small canonical-pointer candidates are read, never expanded archives
    # or external objects. Prefix recognition does not measure an LFS payload.
    if not candidates:
        return
    data = subprocess.run(
        ["git", "--no-replace-objects", "cat-file", "--batch"], cwd=root,
        input="".join(f"{oid}\n" for oid in sorted(candidates)).encode("ascii"),
        check=True, capture_output=True,
    ).stdout
    offset = 0
    for oid in sorted(candidates):
        end = data.find(b"\n", offset)
        if end == -1:
            raise ValueError("missing LFS candidate blob header")
        fields = data[offset:end].split()
        if len(fields) != 3 or fields[:2] != [oid.encode(), b"blob"] or not NUMBER.fullmatch(fields[2]):
            raise ValueError("malformed LFS candidate blob header")
        size = int(fields[2])
        if not len(LFS_PREFIX) <= size <= 1024:
            raise ValueError("LFS candidate size differs from Git tree metadata")
        start = end + 1
        body = data[start:start + size]
        if len(body) != size or data[start + size:start + size + 1] != b"\n":
            raise ValueError("truncated LFS candidate blob")
        if body.startswith(LFS_PREFIX):
            raise ValueError("LFS fixture pointers are unsupported; external payload bytes are not measured")
        offset = start + size + 1
    if offset != len(data):
        raise ValueError("unexpected trailing LFS candidate data")


def committed_totals(root: Path, commit: str) -> dict:
    if git(root, "rev-parse", "--is-shallow-repository").strip() != b"false":
        raise ValueError("complete history is required for committed fixture validation")
    commit = exact_commit(root, commit)
    assert_tree_ancestry(root, commit)
    data = git(root, "ls-tree", "-r", "-l", "-z", "--full-tree", commit, "--", FIXTURE_ROOT)
    totals, candidates = parse_tree_sizes(data)
    reject_lfs_blobs(root, candidates)
    return dict(scope="committed-git-tree", commit=commit,
                tree_records_sha256=hashlib.sha256(data).hexdigest(), **totals)


def working_totals(root: Path) -> dict:
    """Anchor each directory/file open to its parent fd; never follow symlinks."""
    if not hasattr(os, "O_NOFOLLOW") or not hasattr(os, "O_DIRECTORY") or os.open not in os.supports_dir_fd:
        raise ValueError("local fixture traversal requires nofollow directory-fd support")
    directory_flags = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW
    fd = os.open(root, directory_flags)
    seen = set()
    totals = dict(files=0, bytes=0)

    def walk(directory: int, prefix: bytes) -> None:
        with os.scandir(directory) as entries:
            for entry in entries:
                name = os.fsencode(entry.name)
                path = prefix + b"/" + name
                before = entry.stat(follow_symlinks=False)
                if stat.S_ISDIR(before.st_mode):
                    child = os.open(entry.name, directory_flags, dir_fd=directory)
                    try:
                        opened = os.fstat(child)
                        if (opened.st_dev, opened.st_ino) != (before.st_dev, before.st_ino):
                            raise ValueError("fixture directory changed during traversal")
                        walk(child, path)
                    finally:
                        os.close(child)
                elif stat.S_ISREG(before.st_mode):
                    child = os.open(entry.name, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK,
                                    dir_fd=directory)
                    try:
                        opened = os.fstat(child)
                        if not stat.S_ISREG(opened.st_mode) or (
                            (opened.st_dev, opened.st_ino, opened.st_size)
                            != (before.st_dev, before.st_ino, before.st_size)
                        ):
                            raise ValueError("fixture file changed during traversal")
                        if os.read(child, min(1024, opened.st_size)).startswith(LFS_PREFIX):
                            raise ValueError("LFS fixture pointers are unsupported; external payload bytes are not measured")
                        after = os.fstat(child)
                        if (after.st_size, after.st_mtime_ns) != (opened.st_size, opened.st_mtime_ns):
                            raise ValueError("fixture file changed during inspection")
                        seen.add(path)
                        totals["files"] += 1
                        totals["bytes"] += opened.st_size
                    finally:
                        os.close(child)
                else:
                    raise ValueError("fixture symlinks and special files are forbidden")

    try:
        for component in FIXTURE_ROOT.split("/"):
            child = os.open(component, directory_flags, dir_fd=fd)
            os.close(fd)
            fd = child
        walk(fd, FIXTURE_ROOT.encode())
    finally:
        os.close(fd)
    cached = records(git(root, "ls-files", "--cached", "-z", "--", FIXTURE_ROOT))
    head = exact_commit(root, git(root, "rev-parse", "HEAD").strip().decode("ascii"))
    assert_tree_ancestry(root, head)
    committed = records(git(root, "ls-tree", "-r", "--name-only", "-z", head, "--", FIXTURE_ROOT))
    if any(not fixture_path(path) or path not in seen for path in [*cached, *committed]) or (
        len(set(cached)) != len(cached) or len(set(committed)) != len(committed)
    ):
        raise ValueError("tracked fixture missing, malformed or conflicted; commit reviewed deletion before preflight")
    return dict(scope="all-working-fixture-files-including-ignored", **totals)


def fixture_growth(root: Path, base: str, head: str, merge_base: str) -> dict:
    # All three hashes were verified by count_diff or hosted_context beforehand.
    data = git(root, "diff", "--numstat", "-z", "--no-renames", "--no-ext-diff",
               "--no-textconv", "--diff-algorithm=myers", "--ignore-submodules=none",
               merge_base, head, "--", FIXTURE_ROOT)
    from check_pr_size import parse_numstat
    paths = [record.split(b"\t", 2)[2] for record in records(data) if len(record.split(b"\t", 2)) == 3]
    counts = parse_numstat(data)
    if any(not fixture_path(path) for path in paths):
        raise ValueError("fixture diff contains an unexpected path")
    return dict(base=base, head=head, merge_base=merge_base,
                numstat_sha256=hashlib.sha256(data).hexdigest(), **counts)


def enforce(policy: dict, totals: dict, growth: dict | None = None,
            repository: str | None = None, number: int | None = None) -> dict:
    failures = []
    for field, limit_field in [("bytes", "max_bytes"), ("files", "max_files")]:
        value = totals.get(field)
        if type(value) is not int or value < 0:
            raise ValueError("invalid fixture total")
        if value > policy["totals"][limit_field]:
            failures.append(f"fixture {field} exceed configured total cap")
    exception = (repository, number) == EXCEPTION and type(number) is int
    if growth is not None:
        value = growth.get("additions")
        if type(value) is not int or value < 0:
            raise ValueError("invalid fixture added-line count")
        if value > policy["pull_request"]["max_added_lines"] and not exception:
            failures.append("fixture PR added text lines exceed configured growth cap")
    return dict(format=1, status="forbidden" if failures else "allowed", policy=policy,
                totals=totals, growth=growth, failures=failures,
                growth_exception="MGYamada/Qleisli#307" if growth is not None and exception else None)


def write_report_exclusively(path: Path, encoded: str) -> None:
    # The caller resolved and checked this external path before counting. Pin
    # each directory without following a later symlink swap; never truncate an
    # existing destination, which could be hardlinked to a counted fixture.
    if not path.is_absolute() or not hasattr(os, "O_NOFOLLOW") or not hasattr(os, "O_DIRECTORY") or (
        os.open not in os.supports_dir_fd
    ):
        raise OSError("exclusive nofollow report creation is unavailable")
    flags = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW
    parent = os.open(path.anchor, flags)
    try:
        for component in path.parts[1:-1]:
            child = os.open(component, flags, dir_fd=parent)
            os.close(parent)
            parent = child
        descriptor = os.open(path.name, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW,
                             0o600, dir_fd=parent)
        with os.fdopen(descriptor, "w", encoding="utf-8") as report:
            report.write(encoded)
    finally:
        os.close(parent)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--hosted", action="store_true", help="require exact GitHub workflow context")
    parser.add_argument("--base", help="exact base commit for committed local preflight")
    parser.add_argument("--head", help="exact head commit for committed local preflight")
    parser.add_argument("--report", type=Path)
    args = parser.parse_args(argv)
    report_allowed = True
    report_path = None
    try:
        if args.report is not None:
            report_path = args.report.resolve()
            if report_path.is_relative_to((ROOT / FIXTURE_ROOT).resolve()):
                report_allowed = False
                raise ValueError("fixture-budget reports must stay outside the counted fixture tree")
        hosted = args.hosted or os.environ.get("GITHUB_ACTIONS") == "true"
        if args.base is not None or args.head is not None:
            if hosted or args.base is None or args.head is None:
                raise ValueError("committed local preflight requires both hashes and cannot replace hosted checking")
            from check_pr_size import count_diff
            diff = count_diff(ROOT, args.base, args.head)
            policy, digest = load_policy(ROOT, diff["head"])
            result = enforce(policy, committed_totals(ROOT, diff["head"]),
                             fixture_growth(ROOT, diff["base"], diff["head"], diff["merge_base"]))
            result["event"] = "local-committed-preflight"
        elif hosted:
            event = json.loads(Path(os.environ["GITHUB_EVENT_PATH"]).read_bytes(), object_pairs_hook=unique_object)
            context = hosted_context(ROOT, os.environ["GITHUB_EVENT_NAME"], event,
                                     os.environ["GITHUB_SHA"], os.environ["GITHUB_REF"],
                                     os.environ["GITHUB_REPOSITORY"])
            policy, digest = load_policy(ROOT, context["checkout_sha"])
            growth = None if context["status"] == "not-applicable" else fixture_growth(
                ROOT, context["base"], context["head"], context["merge_base"])
            result = enforce(policy, committed_totals(ROOT, context["checkout_sha"]), growth,
                             context["repository"], context.get("pull_request"))
            if context["status"] == "forbidden":
                result["status"] = "forbidden"
                result["failures"].append("whole-PR size gate refused this exact PR")
            result.update(event=context["event"], checkout_sha=context["checkout_sha"],
                          repository=context["repository"], pull_request=context.get("pull_request"))
        else:
            policy, digest = load_policy(ROOT)
            result = enforce(policy, working_totals(ROOT))
            result["event"] = "local-working-preflight"
        result["policy_sha256"] = digest
        success = result["status"] == "allowed"
    except (OSError, ValueError, KeyError, TypeError, AttributeError, UnicodeError,
            subprocess.CalledProcessError) as failure:
        result = dict(format=1, status="error", reason=str(failure))
        success = False
    encoded = json.dumps(result, indent=2) + "\n"
    try:
        if report_path is not None and report_allowed:
            write_report_exclusively(report_path, encoded)
        print(encoded, end="", file=sys.stdout if success else sys.stderr)
    except OSError as failure:
        print(f"Fixture-budget report failed: {failure}", file=sys.stderr)
        return 1
    return 0 if success else 1


if __name__ == "__main__":
    sys.exit(main())

# Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
