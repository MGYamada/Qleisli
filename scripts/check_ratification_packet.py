#!/usr/bin/env python3
"""Check the archived pre-ratification packet, never current human authority.

This is not constitutional CI, a ratification mechanism, or verification of any
guarantee. The frozen candidate's pending status describes its historical state;
the later human event is checked separately by check_constitution.py.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""

import argparse
from datetime import datetime
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import sys


ROOT = Path(__file__).resolve().parents[1]
PACKET_PATH = "tests/fixtures/constitution_v030/packet.json"
ISSUE_URL = "https://github.com/MGYamada/Qleisli/issues/129"
ARTIFACTS = {"CONSTITUTION.md", "GOVERNANCE.md"}
GOVERNANCE_SNAPSHOT = "tests/fixtures/constitution_v030/governance-candidate.txt"
# The packet stays byte-for-byte frozen. Only the original governance candidate
# moved after adoption; the active governance status is not the approved bytes.
ARTIFACT_SNAPSHOTS = {"CONSTITUTION.md": "CONSTITUTION.md",
                      "GOVERNANCE.md": GOVERNANCE_SNAPSHOT}
SHA256 = re.compile(r"[0-9a-f]{64}\Z")
TIMESTAMP = re.compile(r"\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}(?:\.\d+)?(?:Z|[+-]\d{2}:\d{2})\Z")


class PacketError(ValueError):
    """The candidate packet is malformed or no longer matches its local files."""


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise PacketError(f"duplicate JSON field: {key}")
        result[key] = value
    return result


def json_object(data, label):
    def invalid_constant(value):
        raise PacketError(f"{label}: non-JSON numeric constant {value}")

    try:
        value = json.loads(data.decode("utf-8"), object_pairs_hook=unique_object,
                           parse_constant=invalid_constant)
    except (UnicodeError, json.JSONDecodeError) as error:
        raise PacketError(f"{label}: invalid UTF-8 JSON: {error}") from error
    if type(value) is not dict:
        raise PacketError(f"{label}: expected a JSON object")
    return value


def exact_keys(value, expected, label):
    if type(value) is not dict or set(value) != set(expected):
        raise PacketError(f"{label}: expected exactly these fields: {', '.join(sorted(expected))}")


def read_file(root, name):
    """Read a regular file beneath a held root, without following symlinks.

    Descriptor-relative opens prevent a replaced intermediate directory from
    redirecting the read outside the selected repository. They do not promise a
    snapshot of files being concurrently edited; the recorded hashes bind bytes.
    """
    if (type(name) is not str or not name or "\\" in name
            or any(ord(char) < 32 or ord(char) == 127 for char in name)):
        raise PacketError("file path must be a normalized repository-relative path")
    relative = PurePosixPath(name)
    if (relative.is_absolute() or relative.as_posix() != name
            or any(part in {".", ".."} or ":" in part for part in relative.parts)):
        raise PacketError(f"{name}: file path must stay within the repository")
    if not relative.parts:
        raise PacketError("empty file path")
    if (os.open not in os.supports_dir_fd or not hasattr(os, "O_NOFOLLOW")
            or not hasattr(os, "O_DIRECTORY")):
        raise PacketError("safe packet reads require descriptor-relative no-follow file support")

    directory_flags = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW
    directory = None
    file_descriptor = None
    try:
        directory = os.open(root, directory_flags)
        for part in relative.parts[:-1]:
            child = os.open(part, directory_flags, dir_fd=directory)
            os.close(directory)
            directory = child
        # Nonblocking also avoids hanging on a malformed FIFO artifact.
        file_descriptor = os.open(relative.name, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK,
                                  dir_fd=directory)
        if not stat.S_ISREG(os.fstat(file_descriptor).st_mode):
            raise PacketError(f"{name}: expected a regular file, not a symlink or special file")
        with os.fdopen(file_descriptor, "rb") as stream:
            file_descriptor = None
            return stream.read()
    except OSError as error:
        # Do not expose the repository's absolute host path in diagnostics.
        raise PacketError(f"{name}: cannot read confined regular file (missing, symlink, or inaccessible)") from error
    finally:
        if file_descriptor is not None:
            os.close(file_descriptor)
        if directory is not None:
            os.close(directory)


def checked_file(root, name, digest):
    if type(digest) is not str or SHA256.fullmatch(digest) is None:
        raise PacketError(f"{name}: expected a lowercase SHA-256 digest")
    data = read_file(root, name)
    if hashlib.sha256(data).hexdigest() != digest:
        raise PacketError(f"{name}: SHA-256 mismatch")
    return data


def check_constitution(data):
    try:
        text = data.decode("utf-8")
    except UnicodeError as error:
        raise PacketError("CONSTITUTION.md: expected UTF-8 text") from error
    headings = []
    fence = None
    for line in text.splitlines():
        opening = re.match(r"^ {0,3}(`{3,}|~{3,})", line)
        if fence is not None:
            if re.fullmatch(r" {0,3}" + re.escape(fence[0]) + "{" + str(len(fence)) + r",}\s*", line):
                fence = None
            continue
        if opening:
            fence = opening[1]
            continue
        heading = re.match(r"^ {0,3}(#{1,6})\s+(.+?)\s*#*\s*$", line)
        if heading:
            title = heading[2]
            if "explanatory notes" in title.lower():
                raise PacketError("CONSTITUTION.md: Draft 5 explanatory notes are not constitutional text")
            if len(heading[1]) == 2:
                if title == "Preamble":
                    headings.append("Preamble")
                elif match := re.match(r"Article ([IVX]+)(?:\b|$)", title):
                    headings.append(match[1])
    expected = ["Preamble", "I", "II", "III", "IV", "V", "VI", "VII", "VIII", "IX"]
    if headings != expected:
        raise PacketError("CONSTITUTION.md: require Preamble and Articles I–IX exactly once, in order")


def check_packet(root=ROOT, *, require_ratified=False):
    root = Path(root)
    packet = json_object(read_file(root, PACKET_PATH), PACKET_PATH)
    exact_keys(packet, {"format", "version", "edition", "status", "proposed_guardian",
                        "source_issue", "artifacts", "baseline", "human_ratification",
                        "binding_interpretations", "discharged_guarantees"}, "packet")
    if packet["format"] != "qleisli.ratification-candidate":
        raise PacketError("packet: unsupported format")
    if type(packet["version"]) is not int or packet["version"] != 1:
        raise PacketError("packet: version must be integer 1")
    if packet["edition"] != "2026":
        raise PacketError("packet: constitutional edition must be explicit string '2026'")
    if packet["status"] != "awaiting-human-ratification":
        raise PacketError("packet: candidate status must be awaiting-human-ratification; a status string cannot confer authority")
    if packet["proposed_guardian"] != "Masahiko G. Yamada":
        raise PacketError("packet: unexpected proposed guardian; a proposal does not appoint a guardian")
    if packet["human_ratification"] is not None:
        raise PacketError("packet: candidate human_ratification must be null; this checker cannot authenticate a human event")
    for field in ("binding_interpretations", "discharged_guarantees"):
        if type(packet[field]) is not list or packet[field]:
            raise PacketError(f"packet: candidate {field} must be an empty array")

    issue = packet["source_issue"]
    exact_keys(issue, {"number", "url", "updated_at", "body_path", "body_sha256"}, "source_issue")
    if type(issue["number"]) is not int or issue["number"] != 129 or issue["url"] != ISSUE_URL:
        raise PacketError("source_issue: expected Issue #129 and its exact GitHub URL")
    timestamp = issue["updated_at"]
    if type(timestamp) is not str or TIMESTAMP.fullmatch(timestamp) is None:
        raise PacketError("source_issue: updated_at must be an ISO timestamp with timezone")
    try:
        datetime.fromisoformat(timestamp.replace("Z", "+00:00"))
    except ValueError as error:
        raise PacketError("source_issue: invalid updated_at timestamp") from error
    source = json_object(checked_file(root, issue["body_path"], issue["body_sha256"]), "source issue")
    if (type(source.get("number")) is not int or source["number"] != issue["number"]
            or source.get("url") != issue["url"] or source.get("updatedAt") != timestamp
            or type(source.get("body")) is not str or not source["body"].strip()):
        raise PacketError("source issue: saved number, URL, updatedAt and nonempty body must match the packet")

    artifacts = packet["artifacts"]
    if type(artifacts) is not list or len(artifacts) != len(ARTIFACTS):
        raise PacketError("artifacts: require CONSTITUTION.md and GOVERNANCE.md")
    seen = set()
    for artifact in artifacts:
        exact_keys(artifact, {"path", "sha256"}, "artifact")
        name = artifact["path"]
        if type(name) is not str or name not in ARTIFACTS or name in seen:
            raise PacketError("artifacts: require each of CONSTITUTION.md and GOVERNANCE.md exactly once")
        seen.add(name)
        content = checked_file(root, ARTIFACT_SNAPSHOTS[name], artifact["sha256"])
        if name == "CONSTITUTION.md":
            check_constitution(content)

    baseline = packet["baseline"]
    exact_keys(baseline, {"manifest_path", "manifest_sha256"}, "baseline")
    json_object(checked_file(root, baseline["manifest_path"], baseline["manifest_sha256"]), "baseline manifest")
    if require_ratified:
        raise PacketError("human ratification event required: the historical candidate packet cannot establish current ratification; use check_constitution.py for recorded-event identity")


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--require-ratified", action="store_true",
                        help="fail: this candidate format cannot establish a human ratification event")
    args = parser.parse_args(argv)
    try:
        check_packet(args.root, require_ratified=args.require_ratified)
    except (PacketError, OSError) as error:
        print(f"ratification candidate integrity: {error}", file=sys.stderr)
        return 1
    print("Historical ratification candidate integrity verified; its pending status is archived. "
          "This does not verify human approval, constitutional authority, or discharged guarantees.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
