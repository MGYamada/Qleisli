"""Check lossless historical fixture archives; never execute archived records.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""
import gzip
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import tarfile

ROOT = Path(__file__).resolve().parents[1]
MAX_BYTES = 150 * 1024 * 1024
MAX_MEMBERS = 18_000


def require(value, message):
    if not value:
        raise ValueError(message)


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "duplicate JSON key")
        result[key] = value
    return result


def local_name(name):
    require(type(name) is str and name and "\\" not in name,
            "invalid archive path")
    path = PurePosixPath(name)
    require(not path.is_absolute() and ".." not in path.parts
            and str(path) == name and name.startswith("tests/fixtures/"),
            "nonlocal archive path")
    return name


def sha(data):
    return hashlib.sha256(data).hexdigest()


def verify(root, manifest, *, git_baseline=False):
    require(manifest.stat().st_size <= 16 * 1024 * 1024, "manifest exceeds capacity")
    data = json.loads(manifest.read_bytes(), object_pairs_hook=unique_object)
    require(set(data) == {"format", "version", "source_commit", "prefix", "archive",
                          "archive_sha256", "entries"}, "unknown archive manifest fields")
    require(data["format"] == "qleisli.historical-fixture-archive"
            and type(data["version"]) is int and data["version"] == 1,
            "unknown archive format")
    require(type(data["source_commit"]) is str
            and re.fullmatch(r"[0-9a-f]{40}", data["source_commit"]), "invalid source commit")
    prefix = local_name(data["prefix"])
    archive = root / local_name(data["archive"])
    require(not archive.is_symlink() and archive.is_file()
            and archive.resolve().is_relative_to(root.resolve()), "nonlocal archive file")
    require(archive.stat().st_size <= MAX_BYTES, "archive exceeds stored capacity")
    require(sha(archive.read_bytes()) == data["archive_sha256"], "archive digest mismatch")
    entries = data["entries"]
    require(type(entries) is dict and 0 < len(entries) <= MAX_MEMBERS,
            "archive inventory exceeds capacity")
    total = 0
    for name, row in entries.items():
        local_name(name)
        require(name.startswith(prefix + "/"), "member outside historical prefix")
        require(type(row) is dict and set(row) == {"bytes", "sha256", "mode"},
                "invalid member metadata")
        require(type(row["bytes"]) is int and row["bytes"] >= 0
                and row["mode"] in {"100644", "100755"}
                and type(row["sha256"]) is str
                and re.fullmatch(r"[0-9a-f]{64}", row["sha256"]), "invalid member identity")
        total += row["bytes"]
        require(total <= MAX_BYTES, "archive expanded contents exceed capacity")
    seen = set()
    # Bound decompression before tarfile processes extended headers. Inventory
    # limits alone cannot constrain a malicious gzip/PAX header expansion.
    container_limit = MAX_BYTES + MAX_MEMBERS * 2048 + 10240
    with gzip.open(archive, "rb") as compressed:
        unpacked = compressed.read(container_limit + 1)
    require(len(unpacked) <= container_limit, "archive container exceeds capacity")
    with tarfile.open(fileobj=io.BytesIO(unpacked), mode="r:") as tar:
        for member in tar:
            name = local_name(member.name)
            require(member.isfile() and name in entries and name not in seen,
                    "unlisted, duplicate or nonregular archive member")
            row = entries[name]
            require(member.size == row["bytes"]
                    and member.mode == (int(row["mode"], 8) & 0o777),
                    "member size or mode differs")
            stream = tar.extractfile(member)
            require(stream is not None, "missing member data")
            content = stream.read(member.size + 1)
            require(len(content) == member.size and sha(content) == row["sha256"],
                    "member content differs")
            seen.add(name)
    require(seen == set(entries), "missing archived member")
    if git_baseline:
        listing = subprocess.check_output(
            ["git", "ls-tree", "-rl", "-z", data["source_commit"], "--", prefix], cwd=root)
        rows = {}
        for item in listing.split(b"\0"):
            if not item:
                continue
            meta, name = item.split(b"\t", 1)
            mode, kind, oid, size_text = meta.decode().split()
            require(kind == "blob" and mode in {"100644", "100755"}, "nonregular Git source")
            require(size_text.isdigit(), "invalid Git source size")
            require(int(size_text) == entries.get(name.decode(), {}).get("bytes"),
                    "Git source size differs from bounded inventory")
            rows[name.decode()] = (mode, oid)
        require(set(rows) == set(entries), "archive differs from complete Git source inventory")
        command = subprocess.run(["git", "cat-file", "--batch"], cwd=root,
                                 input="".join(oid + "\n" for _, oid in rows.values()).encode(),
                                 capture_output=True, check=True)
        offset = 0
        for name, (mode, oid) in rows.items():
            end = command.stdout.index(b"\n", offset)
            header = command.stdout[offset:end].decode().split()
            require(len(header) == 3 and header[:2] == [oid, "blob"], "invalid Git blob reply")
            size = int(header[2]); offset = end + 1
            content = command.stdout[offset:offset + size]; offset += size + 1
            require(entries[name] == {"bytes": size, "sha256": sha(content), "mode": mode},
                    "archived bytes differ from original Git source")
        require(offset == len(command.stdout), "extra Git blob data")
    return len(entries), total


def main():
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--git-baseline", action="store_true")
    args = parser.parse_args()
    manifests = sorted((ROOT / "tests/fixtures").rglob("*.archive.json"))
    require(bool(manifests), "missing historical archive manifest")
    members = size = 0
    for manifest in manifests:
        count, amount = verify(ROOT, manifest, git_baseline=args.git_baseline)
        members += count; size += amount
    print(f"Checked {len(manifests)} historical archives: {members} original files, {size} expanded bytes; no command executed.")


if __name__ == "__main__":
    main()
