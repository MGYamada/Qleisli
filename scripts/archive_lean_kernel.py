#!/usr/bin/env python3
"""Archive a freshly audited native bundle for explicit release distribution.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import argparse
import gzip
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import tarfile

from maintain_release import PRODUCT_VERSION

ROOT = Path(__file__).resolve().parents[1]


def sha(data):
    return hashlib.sha256(data).hexdigest()


def archive_bundle(bundle, output, revision, source_root):
    if not re.fullmatch(r"[0-9a-f]{40}", revision):
        raise ValueError("distribution requires an exact source commit")
    manifest_bytes = (bundle / "manifest.json").read_bytes()
    manifest = json.loads(manifest_bytes)
    if manifest.get("format") != "qleisli.native-bundle" or manifest.get("version") != 1:
        raise ValueError("unknown bundle manifest")
    if manifest.get("validation", {}).get("lane") != "full" or manifest["validation"].get("fresh_replay") is not True:
        raise ValueError("distribution requires full fresh proof replay")
    version = manifest["package_version"]
    if not isinstance(version, str) or not re.fullmatch(PRODUCT_VERSION, version):
        raise ValueError("invalid product version")
    targets = {("Darwin", "arm64"): "aarch64-apple-darwin",
               ("Darwin", "x86_64"): "x86_64-apple-darwin",
               ("Linux", "x86_64"): "x86_64-unknown-linux-gnu",
               ("Linux", "aarch64"): "aarch64-unknown-linux-gnu"}
    target = targets.get((manifest["platform"], manifest["machine"]))
    if target is None:
        raise ValueError("unsupported distribution platform")
    for name, expected in manifest["sources"].items():
        path = PurePosixPath(name)
        if path.is_absolute() or ".." in path.parts or "\\" in name or sha((source_root / name).read_bytes()) != expected:
            raise ValueError("bundle source identity differs: " + name)
    payload = {}
    for path in bundle.rglob("*"):
        if path.is_symlink() or not (path.is_file() or path.is_dir()):
            raise ValueError("bundle contains a link/special entry")
        if path.is_file():
            payload[path.relative_to(bundle).as_posix()] = path.read_bytes()
    files = {name: sha(data) for name, data in payload.items() if name != "manifest.json"}
    if files != manifest["files"]:
        raise ValueError("bundle file inventory or hashes differ")
    if not {"bin/qleisli-kernel", "LICENSE", "NOTICE", "lean-runtime-licenses/LICENSE"} <= files.keys():
        raise ValueError("bundle lacks executable or required licenses")
    name = f"qleisli-kernel-{version}-{target}"
    payload["INSTALL.txt"] = (
        f"Qleisli native checker {version} ({target})\n\n"
        "Extract this entire archive, preserving its license files.\n"
        "No Lean, Lake, Mathlib, Python or runtime download is required.\n"
        f"Use only the matching Qleisli {version} Rust CLI/library.\n"
        "Select this executable with --lean-kernel=/absolute/path/bin/qleisli-kernel\n"
        "or export QLEISLI_KERNEL=/absolute/path/bin/qleisli-kernel.\n"
        "For the experimental sized API also set QLEISLI_HIERARCHY_KERNEL to that path.\n"
        "Platform/library validation is recorded in manifest.json; older OS compatibility\n"
        "is not established by the architecture name. Preserve all bundled notices.\n"
    ).encode()
    payload["distribution.json"] = (json.dumps(dict(
        format="qleisli.kernel-distribution", version=1, source_commit=revision,
        package_version=version, target=target, bundle_manifest_sha256=sha(manifest_bytes),
        archive_script_sha256=sha(Path(__file__).read_bytes()),
    ), indent=2) + "\n").encode()
    output.mkdir(parents=True, exist_ok=True)
    archive = output / (name + ".tar.gz")
    checksum = output / (archive.name + ".sha256")
    if archive.exists() or checksum.exists():
        raise ValueError("distribution destination already exists")
    with archive.open("xb") as handle, gzip.GzipFile(filename="", mode="wb", fileobj=handle, mtime=0) as compressed:
        with tarfile.open(fileobj=compressed, mode="w") as tar:
            for relative, data in sorted(payload.items()):
                entry = tarfile.TarInfo(name + "/" + relative)
                entry.size = len(data)
                entry.mode = 0o755 if relative == "bin/qleisli-kernel" else 0o644
                tar.addfile(entry, io.BytesIO(data))
    checksum.write_text(f"{sha(archive.read_bytes())}  {archive.name}\n")
    return archive


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bundle", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    status = subprocess.check_output(["git", "status", "--porcelain=v1", "--untracked-files=all"], cwd=ROOT)
    if status:
        raise ValueError("distribution requires a clean committed source tree")
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    print(archive_bundle(args.bundle.resolve(), args.output.resolve(), revision, ROOT))


if __name__ == "__main__":
    main()
