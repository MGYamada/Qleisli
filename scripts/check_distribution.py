#!/usr/bin/env python3
"""Validate the production package and complete source archive of a clean HEAD.

Artifacts, logs and the JSON report are retained outside the checkout. Uses
installed Git, Cargo/Rust and Python only; Cargo runs offline. This is the
distribution gate, not a replacement for MSRV, Lean or exact-commit CI checks.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import argparse
from dataclasses import dataclass
import datetime
import hashlib
import io
import json
from pathlib import Path, PurePosixPath, PureWindowsPath
import subprocess
import sys
import tarfile
import tempfile
import time


class DistributionError(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise DistributionError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


@dataclass(frozen=True)
class File:
    data: bytes
    mode: int = 0o644


def git(root, *args, input=None):
    result = subprocess.run(["git", "-C", str(root), *args], input=input,
                            capture_output=True, check=False)
    require(result.returncode == 0, result.stderr.decode(errors="replace"))
    return result.stdout


def clean_candidate(root):
    top = Path(git(root, "rev-parse", "--show-toplevel").decode().strip()).resolve()
    require(top == root.resolve(), "--root must be the Git checkout root")
    status = git(root, "status", "--porcelain=v1", "--untracked-files=all")
    require(not status, "candidate is dirty (tracked changes or untracked files)")
    return {
        "commit": git(root, "rev-parse", "HEAD").decode().strip(),
        "tree": git(root, "rev-parse", "HEAD^{tree}").decode().strip(),
        "clean": True,
    }


def tracked_files(root, commit):
    entries = []
    for entry in git(root, "ls-tree", "-rz", "--full-tree", commit).split(b"\0"):
        if not entry:
            continue
        header, name = entry.split(b"\t", 1)
        mode, kind, oid = header.decode().split()
        require(kind == "blob" and mode in {"100644", "100755"},
                "source archive does not support tracked symlinks/submodules")
        entries.append((name.decode("utf-8"), int(mode[-3:], 8), oid))
    raw = git(root, "cat-file", "--batch",
              input="".join(oid + "\n" for _, _, oid in entries).encode())
    stream = io.BytesIO(raw)
    result = {}
    for name, mode, oid in entries:
        actual_oid, kind, size = stream.readline().decode().split()
        require(actual_oid == oid and kind == "blob", "unexpected Git blob")
        data = stream.read(int(size))
        require(len(data) == int(size) and stream.read(1) == b"\n", "truncated Git blob")
        require(name not in result, "duplicate tracked path")
        result[name] = File(data, mode)
    require(not stream.read(), "trailing Git blob data")
    return result


def read_archive(path, prefix="", expected=None):
    """Read regular files only, rejecting aliases, duplicate entries and links."""
    files, seen = {}, set()
    with tarfile.open(path, "r:*") as archive:
        for member in archive:
            raw = member.name.rstrip("/") if member.isdir() else member.name
            parts = raw.split("/")
            require(raw and not raw.startswith("/") and not PureWindowsPath(raw).drive and "\\" not in raw
                    and all(part not in {"", ".", ".."} for part in parts),
                    f"unsafe archive path: {member.name}")
            require(raw not in seen, f"duplicate archive path: {raw}")
            seen.add(raw)
            require(member.isdir() or member.isfile(), f"link/special archive entry: {raw}")
            require(not member.mode & 0o7000, f"special mode: {raw}")
            if prefix:
                require(parts[0] == prefix, f"wrong archive root: {raw}")
                parts = parts[1:]
                if not parts:
                    require(member.isdir(), "archive root must be a directory")
                    continue
            name = "/".join(parts)
            require(not PureWindowsPath(name).drive, f"drive-qualified archive path: {name}")
            if member.isdir():
                continue
            if expected is not None:
                require(name in expected, f"unexpected archive file: {name}")
                require(member.size == len(expected[name].data), f"wrong byte length: {name}")
            data = archive.extractfile(member).read()
            require(len(data) == member.size, f"truncated archive file: {name}")
            files[name] = File(data, member.mode & 0o777)
    # A regular file must not also be a parent directory of another file.
    for name in files:
        require(not any(str(parent) in files for parent in PurePosixPath(name).parents),
                f"file/directory collision: {name}")
    if expected is not None:
        compare_files(files, expected)
    return files


def compare_files(actual, expected):
    require(actual.keys() == expected.keys(),
            "archive inventory mismatch: missing=" + repr(sorted(expected.keys() - actual.keys()))
            + " extra=" + repr(sorted(actual.keys() - expected.keys())))
    for name, wanted in expected.items():
        require(actual[name].data == wanted.data, f"tracked bytes changed: {name}")
        require(actual[name].mode == wanted.mode, f"tracked mode changed: {name}")


def extract_checked(files, destination):
    require(not destination.exists(), "extraction destination already exists")
    destination.mkdir(parents=True)
    for name, content in files.items():
        path = destination / name
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open("xb") as handle:
            handle.write(content.data)
        path.chmod(content.mode)


def license_inventory(files):
    """Derive required corpus files from the pinned manifest, not case counts."""
    required = {"LICENSE", "NOTICE", "CONTRIBUTING.md", "corpus/NOTICE",
                "corpus/POLICY.md", "corpus/manifest.json"}
    require("corpus/manifest.json" in files, "missing corpus manifest")
    manifest = json.loads(files["corpus/manifest.json"].data)
    originals, translations = set(), set()
    for source in manifest["sources"]:
        for original in source["files"]:
            name = "corpus/" + original["local"]
            require(name in files, f"missing upstream file: {name}")
            require(digest(files[name].data) == original["sha256"],
                    f"upstream hash changed: {name}")
            originals.add(name)
    for case in manifest["cases"]:
        base = "corpus/" + case["project"] + "/"
        translations.update(base + name for name in ("main.qli", "kernel.qli"))
        required.add(base + "README.md")
    required.update(originals | translations)
    for name in required:
        require(name in files and files[name].data, f"missing/empty attribution file: {name}")
    return {"required_files": sorted(required), "upstream_files": len(originals),
            "translation_files": len(translations), "cases": len(manifest["cases"])}


def check_package(files, tracked, listed, candidate):
    require(set(files) == set(listed), "Cargo list/package inventory mismatch")
    generated = {"Cargo.toml", "Cargo.lock", ".cargo_vcs_info.json"}
    require(generated | {"Cargo.toml.orig"} <= files.keys(), "missing Cargo metadata")
    require(all(files[name].mode == 0o644 for name in generated), "wrong generated metadata mode")
    original = files["Cargo.toml.orig"]
    require(original.data == tracked["Cargo.toml"].data, "Cargo.toml.orig changed")
    require(original.mode == tracked["Cargo.toml"].mode, "Cargo.toml.orig mode changed")
    vcs = json.loads(files[".cargo_vcs_info.json"].data)
    require(vcs.get("git", {}).get("sha1") == candidate["commit"], "wrong package Git commit")
    require(not vcs.get("git", {}).get("dirty", False), "Cargo reports a dirty package")
    require(vcs.get("path_in_vcs") == "", "package is not bound to the checkout root")
    for name, file in files.items():
        if name in generated | {"Cargo.toml.orig"}:
            continue
        require(name in tracked, f"untracked package content: {name}")
        compare_files({name: file}, {name: tracked[name]})
    require(not any(name.startswith("research/semantic-kernel/") for name in files),
            "unexpected nested research package inclusion; review distribution policy")
    inventory = license_inventory(files)
    inventory["generated_files"] = sorted(generated | {"Cargo.toml.orig"})
    inventory["excluded_tracked_files"] = sorted(tracked.keys() - files.keys())
    inventory["nested_research"] = "excluded by Cargo; retained and tested in complete source archive"
    return inventory


def compare_package_metadata(original, packaged):
    for key in ["name", "version", "license", "license_file", "edition", "rust_version",
                "dependencies", "links", "features"]:
        require(original.get(key) == packaged.get(key), f"packaged metadata changed: {key}")
    def targets(package):
        values = []
        for target in package.get("targets", []):
            value = {key: target.get(key) for key in
                     ["kind", "name", "crate_types", "edition", "doc", "doctest", "test",
                      "required-features"]}
            value["src_path"] = str(Path(target["src_path"]).resolve().relative_to(
                Path(package["manifest_path"]).resolve().parent))
            values.append(json.dumps(value, sort_keys=True))
        return sorted(values)
    require(targets(original) == targets(packaged), "packaged build targets changed")


class Commands:
    def __init__(self, artifacts, report):
        self.artifacts, self.report = artifacts, report
        (artifacts / "logs").mkdir()

    def run(self, argv, cwd, stdout_path=None):
        number = len(self.report["commands"])
        output = stdout_path or self.artifacts / "logs" / f"{number:02d}.stdout"
        error = self.artifacts / "logs" / f"{number:02d}.stderr"
        entry = {"argv": [str(a) for a in argv], "cwd": str(cwd),
                 "stdout": str(output), "stderr": str(error)}
        self.report["commands"].append(entry)
        start = time.monotonic()
        with output.open("wb") as out, error.open("wb") as err:
            process = subprocess.run(entry["argv"], cwd=cwd, stdout=out, stderr=err,
                                     check=False)
        entry.update(exit_code=process.returncode,
                     elapsed_seconds=round(time.monotonic() - start, 3))
        require(process.returncode == 0, f"command failed ({process.returncode}): {argv}; see {error}")
        return output.read_bytes()


def validate(root, report_path, target_dir=None):
    require(not report_path.is_relative_to(root), "report must be outside the source tree")
    require(not report_path.exists(), "report already exists; choose a new report path")
    report_path.parent.mkdir(parents=True, exist_ok=True)
    artifacts = Path(tempfile.mkdtemp(prefix=report_path.stem + "-artifacts-",
                                      dir=report_path.parent))
    report = {"format": "qleisli.distribution-validation", "version": 1,
              "started_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
              "status": "failed", "source_root": str(root), "artifacts": str(artifacts),
              "commands": [], "candidate": {"clean": False},
              "scope": "clean HEAD production package and complete repository source archive",
              "not_run": ["MSRV matrix", "Lean build/axiom audit", "hosted CI",
                          "tagging", "push", "publication"]}
    try:
        candidate = clean_candidate(root)
        report["candidate"] = candidate
        tracked = tracked_files(root, candidate["commit"])
        report["tracked_files"] = {name: {"sha256": digest(file.data), "mode": oct(file.mode)}
                                   for name, file in tracked.items()}
        report["source_attribution"] = license_inventory(tracked)
        target = (target_dir or artifacts / "target").resolve()
        require(not target.is_relative_to(root), "target directory must be outside source tree")
        commands = Commands(artifacts, report)
        report["rustc"] = commands.run(["rustc", "--version"], root).decode().strip()
        report["cargo"] = commands.run(["cargo", "--version"], root).decode().strip()
        report["python"] = sys.version
        metadata = json.loads(commands.run(
            ["cargo", "metadata", "--offline", "--no-deps", "--format-version=1"], root))
        package = next(p for p in metadata["packages"]
                       if Path(p["manifest_path"]).resolve() == root / "Cargo.toml")
        require(package["license"] == "Apache-2.0", "wrong production package license")
        prefix = package["name"] + "-" + package["version"]
        report["package"] = {"name": package["name"], "version": package["version"],
                             "license": package["license"]}
        archive_path = artifacts / (prefix + "-source.tar")
        commands.run(["git", "-c", "tar.umask=0022", "archive", "--format=tar",
                      candidate["commit"]], root, archive_path)
        archived = read_archive(archive_path, expected=tracked)
        report["source_archive"] = {"path": str(archive_path),
                                    "sha256": digest(archive_path.read_bytes()),
                                    "file_count": len(archived), "excluded_tracked_files": []}
        source = artifacts / "source"
        extract_checked(archived, source)
        required_roots = ["research/semantic-kernel/Cargo.toml", "lean/Audit.lean",
                          "lean/lakefile.toml", "lean/lean-toolchain"]
        require(all(name in archived for name in required_roots), "missing research/proof root")
        commands.run([sys.executable, "scripts/check_input_corpus.py"], source)
        listed = commands.run(["cargo", "package", "--offline", "--list"], root).decode().splitlines()
        commands.run(["cargo", "package", "--offline", "--target-dir", target / "package"], root)
        crate_path = target / "package" / "package" / (prefix + ".crate")
        crate_copy = artifacts / crate_path.name
        with crate_copy.open("xb") as handle:
            handle.write(crate_path.read_bytes())
        contents = read_archive(crate_copy, prefix=prefix)
        report["package_attribution"] = check_package(contents, tracked, listed, candidate)
        packaged_source = artifacts / "packaged-source"
        extract_checked(contents, packaged_source)
        # Without --no-deps Cargo also parses/checks the generated lockfile.
        packaged_metadata = json.loads(commands.run(
            ["cargo", "metadata", "--offline", "--locked", "--format-version=1"], packaged_source))
        packaged = next(p for p in packaged_metadata["packages"]
                        if Path(p["manifest_path"]).resolve() == packaged_source / "Cargo.toml")
        compare_package_metadata(package, packaged)
        require(all((packaged_source / name).is_file()
                    and not (packaged_source / name).is_symlink()
                    and (packaged_source / name).read_bytes() == file.data
                    and (packaged_source / name).stat().st_mode & 0o777 == file.mode
                    for name, file in contents.items()), "packaged files changed during validation")
        report["crate"] = {"path": str(crate_copy), "sha256": digest(crate_copy.read_bytes()),
                           "file_count": len(contents), "cargo_verification": "passed",
                           "extracted_metadata_and_lock": "validated offline with --locked"}
        commands.run(["cargo", "test", "--offline", "--all-targets", "--target-dir",
                      target / "source-production"], source)
        commands.run(["cargo", "test", "--offline", "--all-targets", "--manifest-path",
                      "research/semantic-kernel/Cargo.toml", "--target-dir",
                      target / "source-research"], source)
        research_metadata = json.loads(commands.run(
            ["cargo", "metadata", "--offline", "--no-deps", "--format-version=1",
             "--manifest-path", "research/semantic-kernel/Cargo.toml"], source))
        research_manifest = source / "research/semantic-kernel/Cargo.toml"
        research_package = next(p for p in research_metadata["packages"]
                                if Path(p["manifest_path"]).resolve() == research_manifest)
        require(research_package["license"] == "Apache-2.0", "wrong research package license")
        require(research_package["publish"] == [], "research package must remain unpublished")
        report["research_package"] = {"name": research_package["name"],
                                      "version": research_package["version"],
                                      "license": research_package["license"], "publish": False}
        require(clean_candidate(root) == candidate, "candidate changed during validation")
        # Build tools may create ignored lock/target files; tracked payload stays exact.
        for name, file in archived.items():
            path = source / name
            require(path.is_file() and not path.is_symlink(), f"extracted file lost: {name}")
            require(path.read_bytes() == file.data and path.stat().st_mode & 0o777 == file.mode,
                    f"extracted tracked file changed while building: {name}")
        report["status"] = "passed"
    except (DistributionError, OSError, ValueError, tarfile.TarError, StopIteration) as error:
        report["error"] = str(error)
    finally:
        report["finished_utc"] = datetime.datetime.now(datetime.timezone.utc).isoformat()
        with report_path.open("x") as handle:
            json.dump(report, handle, indent=2, sort_keys=True)
            handle.write("\n")
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--report", required=True, type=Path)
    parser.add_argument("--target-dir", type=Path)
    args = parser.parse_args()
    try:
        report = validate(args.root.resolve(), args.report.resolve(), args.target_dir)
    except (DistributionError, OSError) as error:
        print(error, file=sys.stderr)
        return 1
    print(f"Distribution validation {report['status']}; report: {args.report.resolve()}")
    if report["status"] != "passed":
        print(report["error"], file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
