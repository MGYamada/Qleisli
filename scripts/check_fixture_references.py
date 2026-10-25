"""Reject new fixtures without a rooted static consumer reference.

References establish retention reachability, not execution or semantic coverage.
Never execute a manifest, historical command or fixture while inspecting it.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
"""
import argparse
from collections import deque
import fnmatch
from functools import lru_cache
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys

from check_pr_size import ROOT, event_inputs, exact_commit, git, hosted_context, unique_object
from check_authoring_sessions import retained_source_record_index
import current_metadata

# Reviewed pre-retention tree. Existing records are not retroactively deleted
# or declared consumed. New paths remain checked on pushes as well as PRs.
BASELINE = "22dccc5bdbf62f802f12fe7ce457132ae51e036d"
PREFIX = "tests/fixtures/"
TEXT_LIMIT = 16 * 1024 * 1024
LITERALS = re.compile(r'''["']([^"'\n\r\x00]+)["']''')
RETAINED_INDEX = "tests/fixtures/authoring_sessions/retained-source-records-v1.json"
RETAINED_PREFIX = "tests/fixtures/authoring_sessions/retained-source-records-v1/"
AUTHORING_PREFIX = "tests/fixtures/authoring_sessions/"


def rooted_source(name):
    path = PurePosixPath(name)
    # This inspector and its graph tests describe synthetic fixture paths;
    # neither consumes those paths. They cannot grant their own exceptions.
    synthetic = {"scripts/check_fixture_references.py",
                 "scripts/test_check_fixture_references.py"}
    return name not in synthetic and not name.startswith(PREFIX) and (
        (path.parts[0] in {"scripts", "tests", "src", "lean", "lean-kernel"}
         and path.suffix in {".py", ".rs", ".sh", ".lean"})
        or name.startswith(".github/") and path.suffix in {".json", ".yml", ".yaml"}
        or name in {"Cargo.toml", "python/pyproject.toml"})


def strings(name, text):
    if name.endswith(".json") or name in current_metadata.CURRENT_PATHS:
        try:
            value = json.loads(text, object_pairs_hook=unique_object)
        except (ValueError, RecursionError):
            return []
        result, pending = [], [value]
        while pending:
            item = pending.pop()
            if isinstance(item, dict):
                result.extend(item)
                pending.extend(item.values())
            elif isinstance(item, list):
                pending.extend(item)
            elif isinstance(item, str):
                result.append(item)
        return result
    return LITERALS.findall(text)


def path_index(paths):
    directories = {}
    for path in paths:
        parent = PurePosixPath(path).parent
        while str(parent) != ".":
            directories.setdefault(str(parent), set()).add(path)
            parent = parent.parent
    return directories


@lru_cache(maxsize=32768)
def _cached_parts(name):
    return PurePosixPath(name).parts


def path_parts(name):
    """Reuse bounded immutable text only, never a reference or gate decision."""
    if type(name) is str and len(name) <= 4096:
        return _cached_parts(name)
    # Subclasses, long strings and other existing PathLike inputs still receive
    # the full ordinary parse. Cache bounds never become acceptance limits.
    return PurePosixPath(name).parts


def glob_match(path, pattern):
    """Match path components; only an explicit ** crosses directories."""
    parts = path_parts(pattern)
    positions = {0}
    for component in (*path_parts(path), None):
        # ** also matches zero components. Iterate in order to close adjacent
        # recursive wildcards without recursive calls on candidate input.
        for position in range(len(parts)):
            if position in positions and parts[position] == "**":
                positions.add(position + 1)
        if component is None:
            return len(parts) in positions
        positions = {position if parts[position] == "**" else position + 1
                     for position in positions if position < len(parts)
                     and (parts[position] == "**"
                          or fnmatch.fnmatchcase(component, parts[position]))}
    return False


def glob_candidates(pattern, paths, index):
    fixed = []
    for part in PurePosixPath(pattern).parts:
        if any(character in part for character in "*?["):
            break
        fixed.append(part)
    return index.get("/".join(fixed), paths)


def references(name, text, paths, index=None):
    """Resolve literals and manifest-relative paths against known files only."""
    index = path_index(paths) if index is None else index
    values = strings(name, text)
    parent = PurePosixPath(name).parent
    candidates = set()
    for value in values:
        if "\\" in value or "://" in value or value.startswith("/"):
            continue
        # A brace in a source string represents a bounded file-name pattern;
        # an arbitrary recursive fixture-root scan is not a consumer claim.
        value = re.sub(r"\{[^{}]*\}", "*", value)
        for base in (PurePosixPath("."), parent):
            relative = base / value
            if ".." not in relative.parts:
                candidates.add(str(relative))
    directories = {c for c in candidates if c.startswith(PREFIX)
                   and len(PurePosixPath(c).parts) >= 4 and c in index}
    # Source projects are consumed by their directory, including their explicit
    # manifest. This does not admit unrelated logs beneath the same directory.
    for directory in directories:
        if rooted_source(name):
            candidates.update(p for p in index[directory]
                              if p.endswith(".qli") or p.endswith("/Qargo.toml"))
        for value in values:
            if "/" not in value and "\\" not in value:
                candidates.add(directory + "/" + re.sub(r"\{[^{}]*\}", "*", value))
    found = set()
    for candidate in candidates:
        if candidate in paths:
            found.add(candidate)
        elif any(c in candidate for c in "*?[") and candidate.startswith(PREFIX):
            found.update(p for p in glob_candidates(candidate, paths, index)
                         if glob_match(p, candidate))
    return found


def retained_record_references(contents, paths):
    """Only the exact validated inert-copy set is a consumed archive.

    Directory links and invalid candidate index fields grant no reachability.
    Read immutable snapshot bytes; never run a recorded command or Git lookup.
    """
    def read_bytes(name):
        return contents[AUTHORING_PREFIX + name].encode("utf-8")

    stored = {path[len(AUTHORING_PREFIX):] for path in paths if path.startswith(RETAINED_PREFIX)}
    records = retained_source_record_index(contents[RETAINED_INDEX].encode("utf-8"), read_bytes, stored)
    return {AUTHORING_PREFIX + path for path in records.values()}


def reachability(contents, paths):
    index = path_index(paths)
    roots = {name for name in contents if rooted_source(name)}
    reached = set(roots)
    pending = deque(sorted(roots))
    # These two enumerated manifest families have actual fixed integrity
    # readers. Their members are not roots; they must be reached from a manifest.
    enumerated = {
        "scripts/check_fixture_archives.py": ("tests/fixtures/**/*.archive.json",),
        "scripts/check_authoring_sessions.py": ("tests/fixtures/authoring_sessions/*/session.json",
                                                RETAINED_INDEX),
    }
    for reader, patterns in enumerated.items():
        if reader in roots:
            for pattern in patterns:
                for path in glob_candidates(pattern, paths, index):
                    if glob_match(path, pattern) and path not in reached:
                        reached.add(path)
                        pending.append(path)
    while pending:
        name = pending.popleft()
        if name not in contents:
            continue
        if name.startswith(RETAINED_PREFIX):
            links = set()  # Inert source bytes are hashed, never transitive consumers.
        elif name == RETAINED_INDEX:
            try:
                links = retained_record_references(contents, paths)
            except (ValueError, KeyError, TypeError, AttributeError, RecursionError):
                links = set()  # The strict integrity reader reports malformed copies/index.
        else:
            links = references(name, contents[name], paths, index)
        # Authoring manifests store source names relative to attempt IDs.
        if name.endswith("/session.json"):
            try:
                data = json.loads(contents[name], object_pairs_hook=unique_object)
                for attempt in data.get("attempts", []):
                    for source in attempt.get("sha256", {}):
                        target = str(PurePosixPath(name).parent / attempt["id"] / source)
                        if target in paths:
                            links.add(target)
                    project_manifest = str(PurePosixPath(name).parent / attempt["id"] / "Qargo.toml")
                    if project_manifest in paths:
                        links.add(project_manifest)
            except (ValueError, KeyError, TypeError, AttributeError, RecursionError):
                pass  # The separate authoring integrity check rejects malformed records.
        for link in links - reached:
            reached.add(link)
            pending.append(link)
    return reached


def snapshot(root, commit):
    """Read exact immutable Git blobs; never follow checkout symlinks."""
    rows = {}
    for row in git(root, "ls-tree", "-rlz", commit).split(b"\0"):
        if not row:
            continue
        meta, name = row.split(b"\t", 1)
        mode, kind, oid, size = meta.decode().split()
        path = name.decode("utf-8")
        if kind != "blob" or mode not in {"100644", "100755"}:
            if path.startswith(PREFIX):
                raise ValueError("fixture reference inspection forbids nonregular entries")
            continue
        rows[path] = (oid, int(size))
    paths = set(rows)
    # Never silently lose the decoded fixture edges of a former current gzip
    # HEAD. Its matching historical checker remains in Git; no codec fallback.
    if paths & current_metadata.OBSOLETE_GZIP_PATHS:
        raise ValueError("obsolete gzip current metadata Git snapshot; use its historical checker")
    for path in paths & current_metadata.CURRENT_PATHS:
        if paths.intersection(current_metadata.obsolete_paths(path)):
            raise ValueError("obsolete plain/gzip duplicate in current metadata Git snapshot")
        if rows[path][1] > current_metadata.MAX_BYTES:
            raise ValueError("current metadata stored size exceeds capacity")
    selected = [(p, oid, size) for p, (oid, size) in rows.items()
                if size <= TEXT_LIMIT and (rooted_source(p) or p.startswith(PREFIX)
                                          and (p in current_metadata.CURRENT_PATHS or PurePosixPath(p).suffix in {".json", ".toml"}
                                               or p.startswith(RETAINED_PREFIX) and p.endswith(".qli.txt")))]
    reply = subprocess.run(["git", "--no-replace-objects", "cat-file", "--batch"], cwd=root,
                           input="".join(oid + "\n" for _, oid, _ in selected).encode(),
                           capture_output=True, check=True).stdout
    contents, offset = {}, 0
    for path, oid, size in selected:
        end = reply.index(b"\n", offset)
        if reply[offset:end] != f"{oid} blob {size}".encode():
            raise ValueError("fixture consumer blob identity differs")
        start = end + 1
        body = reply[start:start + size]
        if len(body) != size or reply[start + size:start + size + 1] != b"\n":
            raise ValueError("truncated fixture consumer blob")
        offset = start + size + 1
        if path in current_metadata.CURRENT_PATHS:
            body = current_metadata.decode_bytes(path, body)
            current_metadata.json_object(body)  # malformed current views fail closed
        try:
            if b"\0" not in body:
                contents[path] = body.decode("utf-8")
        except UnicodeError:
            pass
    if offset != len(reply):
        raise ValueError("unexpected fixture consumer blob data")
    return contents, paths


def inspect(root, base, head, changed_since=None):
    base, head = exact_commit(root, base), exact_commit(root, head)
    if git(root, "merge-base", "--is-ancestor", base, head):
        raise ValueError("unexpected ancestry reply")
    contents, paths = snapshot(root, head)
    old_paths = set(git(root, "ls-tree", "-rz", "--name-only", base).decode().split("\0"))
    added = {p for p in paths - old_paths if p.startswith(PREFIX)}
    # A new branch/tag has no previous ref commit. Inspect every addition in
    # the bound head's history after the reviewed ancestor as well as endpoint
    # differences. This also catches delete/re-add pairs within one push and
    # reintroductions before the new head's immediate parent.
    history = [row.split() for row in git(root, "rev-list", "--ancestry-path", "--parents",
                                         f"{base}..{head}").decode("ascii").splitlines()]
    descendants = {base, *(row[0] for row in history)}
    for commit, *parents in history:
        additions = None
        # Only edges descending from the reviewed ancestor are relevant. A
        # merge may inherit an unchanged old file from either eligible parent;
        # absence on an older side branch does not make that file new.
        for parent in (p for p in parents if p in descendants):
            delta = set(git(root, "diff", "--name-only", "-z", "--diff-filter=A",
                            "--no-renames", parent, commit, "--", PREFIX).decode("utf-8").split("\0"))
            additions = delta if additions is None else additions & delta
        added.update(p for p in additions or () if p in paths and p.startswith(PREFIX))
    if changed_since is not None:
        changed_since = exact_commit(root, changed_since)
        previous = set(git(root, "ls-tree", "-rz", "--name-only", changed_since).decode().split("\0"))
        # Reintroducing a removed historical path is a new file in this event,
        # even if its name was present at the grandfathered historical base.
        added.update(p for p in paths - previous if p.startswith(PREFIX))
    reached = reachability(contents, paths)
    missing = sorted(added - reached)
    return dict(format=1, status="forbidden" if missing else "allowed", base=base, head=head,
                change_base=changed_since,
                new_fixtures=len(added), referenced_new_fixtures=len(added & reached),
                unreferenced=missing,
                scope="Static rooted retention references; no execution or semantic coverage claim.")


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--hosted", action="store_true")
    parser.add_argument("--base", default=BASELINE)
    parser.add_argument("--head")
    parser.add_argument("--changed-since", help="also check additions/reintroductions since this exact commit")
    args = parser.parse_args(argv)
    try:
        hosted = args.hosted or os.environ.get("GITHUB_ACTIONS") == "true"
        if hosted:
            if args.head or args.changed_since or args.base != BASELINE:
                raise ValueError("local arguments cannot replace hosted fixture reference inspection")
            event = json.loads(Path(os.environ["GITHUB_EVENT_PATH"]).read_bytes(), object_pairs_hook=unique_object)
            context = hosted_context(ROOT, os.environ["GITHUB_EVENT_NAME"], event,
                                     os.environ["GITHUB_SHA"], os.environ["GITHUB_REF"],
                                     os.environ["GITHUB_REPOSITORY"])
            head = context["checkout_sha"]
            changed_since = context.get("merge_base")
            if changed_since is None and os.environ["GITHUB_EVENT_NAME"] == "push":
                previous = event.get("before")
                if not isinstance(previous, str) or not re.fullmatch(r"[0-9a-f]{40}", previous):
                    raise ValueError("push reference inspection requires the exact previous commit")
                changed_since = None if previous == "0" * 40 else previous
            elif changed_since is None and os.environ["GITHUB_EVENT_NAME"] == "workflow_dispatch":
                changed_since = event_inputs(event).get("release_base") or None
        else:
            head = args.head or git(ROOT, "rev-parse", "HEAD").decode().strip()
            changed_since = args.changed_since
        result = inspect(ROOT, args.base, head, changed_since)
    except (OSError, ValueError, KeyError, TypeError, AttributeError, UnicodeError,
            subprocess.CalledProcessError) as error:
        result = dict(format=1, status="error", reason=str(error))
    print(json.dumps(result, indent=2))
    return 0 if result["status"] == "allowed" else 1


if __name__ == "__main__":
    sys.exit(main())
