#!/usr/bin/env python3
"""Validate the production package and complete source archive of a clean HEAD.

Archives, logs and the JSON report are retained outside the checkout. Owned
build work is removed unless --keep-work is requested; an explicit --target-dir
remains caller-owned. Uses installed Git, Cargo/Rust and Python only; Cargo runs
offline. This gate does not replace MSRV, Lean or exact-commit CI checks.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import argparse
from dataclasses import dataclass
import datetime
import hashlib
import io
import json
import os
from pathlib import Path, PurePosixPath, PureWindowsPath
import shutil
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


SOURCE_ROOTS = (
    "research/semantic-kernel/Cargo.toml", "lean/Audit.lean", "lean/lakefile.toml",
    "lean/lean-toolchain", "lean-kernel/QleisliKernel.lean", "lean-kernel/Audit.lean",
    "lean-kernel/Main.lean", "lean-kernel/Protocol.lean", "lean-kernel/Tests.lean",
    "lean-kernel/lakefile.toml", "lean-kernel/lean-toolchain", "lean-kernel/lake-manifest.json",
    "scripts/check_lean_kernel.py", "scripts/test_check_lean_kernel.py", "scripts/test_lean_hierarchy.py",
    "scripts/test_lean_layout.py",
    "scripts/test_lean_layout_dag.py",
    "scripts/test_lean_phase_layout.py",
    "scripts/test_lean_interference.py",
    "scripts/test_lean_qft.py",
    "scripts/test_lean_qft_graph.py",
    "scripts/test_lean_qpe.py",
    "scripts/test_lean_controlled_power.py",
    "lean/SchemaExport.lean", "lean/schema-registry.json",
    "scripts/check_schema_registry.py", "scripts/test_check_schema_registry.py",
    "scripts/test_hierarchical_graph.py",
    "scripts/test_hierarchical_artifact.py",
    "scripts/test_hierarchical_typing.py",
    "scripts/test_hierarchical_contract_typing.py",
    "scripts/test_hierarchical_structural.py",
    "scripts/test_hierarchical_power.py",
    "scripts/test_hierarchical_derivation.py",
    "examples/lean_kernel.rs",
)


def check_source_roots(files):
    missing = [name for name in SOURCE_ROOTS if name not in files]
    require(not missing, "missing research/proof/kernel root: " + repr(missing))


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
                "dependencies", "links", "features", "readme", "documentation",
                "description", "repository", "keywords", "categories"]:
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


def retain_crate(source, destination):
    """Publish complete bytes only; a failed copy remains explicitly partial."""
    partial = destination.with_suffix(destination.suffix + ".partial")
    data = source.read_bytes()
    with partial.open("xb") as handle:
        handle.write(data)
    partial.rename(destination)
    return {"path": str(destination), "sha256": digest(data)}


def validate(root, report_path, target_dir=None, *, keep_work=False):
    require(not report_path.is_relative_to(root), "report must be outside the source tree")
    require(not report_path.exists(), "report already exists; choose a new report path")
    report_path.parent.mkdir(parents=True, exist_ok=True)
    artifacts = Path(tempfile.mkdtemp(prefix=report_path.stem + "-artifacts-",
                                      dir=report_path.parent))
    report = {"format": "qleisli.distribution-validation", "version": 1,
              "started_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
              "status": "failed", "source_root": str(root), "artifacts": str(artifacts),
              "work": {"path": None, "status": "not-created", "keep_requested": keep_work},
              "commands": [], "candidate": {"clean": False},
              "scope": "clean HEAD production package and complete repository source archive",
              "not_run": ["MSRV matrix", "Lean build/axiom audit", "hosted CI",
                          "tagging", "push", "publication"]}
    work = None
    try:
        candidate = clean_candidate(root)
        report["candidate"] = candidate
        tracked = tracked_files(root, candidate["commit"])
        report["tracked_files"] = {name: {"sha256": digest(file.data), "mode": oct(file.mode)}
                                   for name, file in tracked.items()}
        report["source_attribution"] = license_inventory(tracked)
        if target_dir is not None:
            require(not target_dir.resolve().is_relative_to(root),
                    "target directory must be outside source tree")
        work = Path(tempfile.mkdtemp(prefix=report_path.stem + "-work-",
                                     dir=report_path.parent))
        report["work"].update(path=str(work), status="active")
        target = (target_dir if target_dir is not None else work / "target").resolve()
        report["cargo_target"] = {"path": str(target),
                                  "ownership": "caller" if target_dir is not None else "validator"}
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
        source = work / "source"
        extract_checked(archived, source)
        check_source_roots(archived)
        commands.run([sys.executable, "scripts/check_input_corpus.py"], source)
        commands.run([sys.executable, "scripts/check_lean_kernel.py"], source)
        commands.run([sys.executable, "scripts/check_schema_registry.py", "--source-only"], source)
        listed = commands.run(["cargo", "package", "--offline", "--list"], root).decode().splitlines()
        crate_path = target / "package" / "package" / (prefix + ".crate")
        crate_copy = artifacts / crate_path.name

        def record_preservation_failure(error):
            report["artifact_preservation_error"] = f"crate preservation failed: {error}"
            report["unretained_crate_path"] = str(crate_path)
            if target_dir is None:
                # Do not delete the only candidate bytes when durable storage
                # failed (for example, because the destination is full).
                report["work"]["retention_reason"] = "artifact-preservation-failed"

        try:
            commands.run(["cargo", "package", "--offline", "--target-dir", target / "package"], root)
        except (DistributionError, OSError):
            try:
                if crate_path.exists():
                    report["unverified_crate"] = {
                        **retain_crate(crate_path, crate_copy), "cargo_verification": "failed",
                        # A caller-owned target can contain an older archive.
                        # Capturing these bytes does not bind them to this run.
                        "candidate_binding": "not-verified", "source_path": str(crate_path)}
            except OSError as error:
                record_preservation_failure(error)
            raise
        try:
            crate_record = retain_crate(crate_path, crate_copy)
        except OSError as error:
            record_preservation_failure(error)
            raise
        contents = read_archive(crate_copy, prefix=prefix)
        report["package_attribution"] = check_package(contents, tracked, listed, candidate)
        packaged_source = work / "packaged-source"
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
        report["crate"] = {**crate_record,
                           "file_count": len(contents), "cargo_verification": "passed",
                           "extracted_metadata_and_lock": "validated offline with --locked"}
        # Exercise the distribution's documentation and actual installed binary,
        # not the checkout's target/debug executable or external library files.
        commands.run(["cargo", "rustdoc", "--offline", "--locked", "--lib",
                      "--target-dir", target / "package-docs", "--", "-D", "warnings"],
                     packaged_source)
        commands.run(["cargo", "test", "--offline", "--locked", "--doc",
                      "--target-dir", target / "package-docs"], packaged_source)
        install_root = work / "installed"
        commands.run(["cargo", "install", "--path", packaged_source, "--offline", "--locked",
                      "--bin", "qleisli", "--root", install_root,
                      "--target-dir", target / "install"], work)
        executable = install_root / "bin" / ("qleisli.exe" if os.name == "nt" else "qleisli")
        report["installed_quickstart"] = json.loads(commands.run(
            [sys.executable, packaged_source / "scripts/check_installation.py", executable],
            work))
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
        if work is not None:
            if keep_work or report["work"].get("retention_reason"):
                report["work"]["status"] = "retained"
            else:
                try:
                    # Only this invocation's private directory is owned here.
                    # Explicit Cargo target directories are never removed.
                    shutil.rmtree(work)
                    report["work"]["status"] = "removed"
                except OSError as error:
                    report["work"]["status"] = "cleanup-failed"
                    report["cleanup_error"] = f"work directory cleanup failed: {error}"
                    report["status"] = "failed"
                    report.setdefault("error", report["cleanup_error"])
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
    parser.add_argument("--keep-work", action="store_true",
                        help="retain extracted sources, installation and owned Cargo build work")
    args = parser.parse_args()
    try:
        report = validate(args.root.resolve(), args.report.resolve(), args.target_dir,
                          keep_work=args.keep_work)
    except (DistributionError, OSError) as error:
        print(error, file=sys.stderr)
        return 1
    print(f"Distribution validation {report['status']}; report: {args.report.resolve()}")
    if report["status"] != "passed":
        print(report["error"], file=sys.stderr)
        if report.get("cleanup_error") not in {None, report["error"]}:
            print(report["cleanup_error"], file=sys.stderr)
        if report.get("artifact_preservation_error") not in {None, report["error"]}:
            print(report["artifact_preservation_error"], file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
