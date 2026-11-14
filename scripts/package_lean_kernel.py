#!/usr/bin/env python3
"""Build an audited native kernel bundle from a fresh source copy.
No project build outputs, result caches, Mathlib or compiled result caches.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
"""
import argparse
from graphlib import TopologicalSorter
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import tempfile
import time
import tomllib
from native_packet import envelope, parse_reply

from check_lean_kernel import check_kernel, lean_imports

ROOT = Path(__file__).resolve().parents[1]
PRODUCT_VERSION = tomllib.loads((ROOT / "Cargo.toml").read_text())["package"]["version"]
NATIVE_BUILD_SUPPORT = {
    "scripts/check_lean_kernel.py",
    "scripts/native_packet.py",
    "scripts/package_lean_kernel.py",
    "tests/fixtures/interop/clean-reuse.qasm",
}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def library_builds(package):
    """Bound each cold build command without omitting library modules.

    Imported project modules precede importers, so the first batch cannot
    accidentally request the whole closure. Lake remains the actual builder;
    the final complete library target checks coverage against its own globs.
    """
    sources = {}
    for path in sorted(package.rglob("*.lean")):
        relative = path.relative_to(package)
        name = ".".join(relative.with_suffix("").parts)
        if ".lake" not in relative.parts and (
                name in {"QleisliKernel", "Protocol"}
                or name.startswith(("QleisliKernel.", "Protocol.", "Cli."))):
            sources[name] = path
    graph = {name: sorted(set(lean_imports(path.read_text())) & sources.keys())
             for name, path in sources.items()}
    ordered = list(TopologicalSorter(graph).static_order())
    return [["lake", "build", *("+" + name for name in ordered[start:start + 64])]
            for start in range(0, len(ordered), 64)]


def validate(package, validation):
    """Keep native build/audit in every lane; fresh replay belongs to full."""
    if validation not in ("tests", "model", "full"):
        raise ValueError(f"unknown validation lane: {validation}")
    commands = library_builds(package) + [
        ["lake", "build", "QleisliKernel"],
        ["lake", "build", "qleisli-kernel"],
        ["lake", "env", "lean", "-DwarningAsError=true", "Audit.lean"],
    ]
    if validation == "full":
        commands += [["lake", "env", "leanchecker", "--fresh", "QleisliKernel"],
                     ["lake", "env", "leanchecker", "--fresh", "Main"]]
    logs = []
    for command in commands:
        started = time.monotonic()
        result = subprocess.run(command, cwd=package, text=True, capture_output=True, timeout=600)
        logs.append(dict(command=command, exit_code=result.returncode,
                         seconds=round(time.monotonic() - started, 3),
                         stdout=result.stdout, stderr=result.stderr))
        if result.returncode:
            raise RuntimeError(json.dumps(logs[-1]))
        print("passed:", " ".join(command), flush=True)
    return logs


def parse_args(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True, help="new directory; never overwrites")
    parser.add_argument("--validation", choices=("tests", "model", "full"), default="full",
                        help="CI lane; every lane builds/audits, full also freshly replays both roots (default)")
    return parser.parse_args(argv)


def main(argv=None):
    args = parse_args(argv)
    output = args.output.resolve()
    if output.exists():
        raise ValueError("bundle destination already exists")
    errors, _ = check_kernel(ROOT)
    if errors:
        raise ValueError("\n".join(errors))
    sources = {path.relative_to(ROOT).as_posix(): digest(path)
               for path in (ROOT / "lean-kernel").rglob("*")
               if path.is_file() and ".lake" not in path.parts and
               (path.suffix == ".lean" or path.name in ("lakefile.toml", "lake-manifest.json", "lean-toolchain"))}
    sources.update((relative, digest(ROOT / relative)) for relative in sorted(NATIVE_BUILD_SUPPORT))
    with tempfile.TemporaryDirectory(prefix="qleisli-kernel-build-") as temporary:
        staged = Path(temporary)
        for relative in sources:
            target = staged / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(ROOT / relative, target)
        errors, _ = check_kernel(staged)
        if errors:
            raise ValueError("\n".join(errors))
        package = staged / "lean-kernel"
        logs = validate(package, args.validation)
        prefix = Path(subprocess.check_output(["lake", "env", "lean", "--print-prefix"], cwd=package, text=True).strip())
        # Claim an audited source identity only if original and staged sources
        # still have exactly the captured bytes after all fresh checks.
        for relative, expected in sources.items():
            if digest(ROOT / relative) != expected or digest(staged / relative) != expected:
                raise ValueError(f"source changed during packaging: {relative}")
        output.mkdir(parents=True, exist_ok=False)
        (output / "bin").mkdir()
        suffix = ".exe" if os.name == "nt" else ""
        binary = output / "bin" / ("qleisli-kernel" + suffix)
        shutil.copy2(package / ".lake/build/bin" / binary.name, binary)
        for name in ["LICENSE", "NOTICE"]:
            shutil.copy2(ROOT / name, output / name)
        licenses = output / "lean-runtime-licenses"
        licenses.mkdir()
        shutil.copy2(prefix / "LICENSE", licenses / "LICENSE")
        if (prefix / "LICENSES").is_dir():
            shutil.copytree(prefix / "LICENSES", licenses / "LICENSES")
        else:
            shutil.copy2(prefix / "LICENSES", licenses / "LICENSES")
        dependencies = (["otool", "-L", str(binary)] if platform.system() == "Darwin"
                        else ["ldd", str(binary)] if platform.system() == "Linux" else None)
        if dependencies:
            result = subprocess.run(dependencies, text=True, capture_output=True, check=True)
            if str(prefix) in result.stdout or str(package) in result.stdout or "not found" in result.stdout:
                raise ValueError("native bundle retains a build/toolchain library dependency")
            logs.append(dict(command=dependencies, exit_code=result.returncode,
                             stdout=result.stdout, stderr=result.stderr))
        # Only the bundle is present in this execution directory. No Lake,
        # checkout or project output is used by the selected native runtime.
        artifact = (ROOT / "tests/fixtures/verification_v022/finite/t.v2.qirf").read_bytes()
        environment = {key: value for key, value in os.environ.items()
                       if key not in ("LEAN_PATH", "LEAN_SRC_PATH", "LD_LIBRARY_PATH", "DYLD_LIBRARY_PATH")}
        environment["PATH"] = os.defpath
        for phases, accepted in [([0, 1], True), ([4, 5], False)]:
            request = json.dumps(dict(format="qleisli.request", version=1, signature=dict(tag="bit"),
                                      meaning=dict(tag="phase8", table=phases), source_snapshot=None)).encode()
            packet = b"QLV1" + len(artifact).to_bytes(4, "little") + len(request).to_bytes(4, "little") + artifact + request
            packet = envelope('2026', packet)
            result = subprocess.run([binary, "--qirf-native", PRODUCT_VERSION], input=packet, cwd=output,
                                    env=environment, capture_output=True, timeout=60)
            reply = parse_reply(result.stdout, edition="2026", product=PRODUCT_VERSION,
                                mode="--qirf-native", scope="inspection")
            if (result.returncode != (0 if accepted else 1) or result.stderr
                    or (reply.claim != "accepted" or len(reply.payload) != 2
                        or not 0 <= int(reply.payload[0]) <= 20_000_000
                        or reply.payload[1] != "1" if accepted else reply.error != "contract")):
                raise RuntimeError(f"relocated bundle smoke check failed: {result}")
            logs.append(dict(command=["bin/" + binary.name, "--qirf-native", PRODUCT_VERSION], exit_code=result.returncode,
                             expected_acceptance=accepted, input_sha256=hashlib.sha256(packet).hexdigest(),
                             stdout=result.stdout.decode(), stderr=result.stderr.decode()))
        manifest = dict(format="qleisli.native-bundle", version=1,
                        validation=dict(lane=args.validation, fresh_replay=args.validation == "full",
                                        scope="native package only; Mathlib proof maintenance is a separate CI job"),
                        package_version=tomllib.loads((ROOT / "Cargo.toml").read_text())["package"]["version"],
                        protocol="qleisli.native-result 3", toolchain=(package / "lean-toolchain").read_text().strip(),
                        platform=platform.system(), machine=platform.machine(), sources=sources,
                        files={p.relative_to(output).as_posix(): digest(p) for p in output.rglob("*") if p.is_file()},
                        checks=logs, authority="sole production acceptance implementation; no full S05/source/native-compiler proof")
        (output / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"Audited native bundle: {output}")


if __name__ == "__main__":
    main()
