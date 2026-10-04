#!/usr/bin/env python3
"""Record the bounded positive supplement to the immutable 799-pair corpus.

Runs actual Rust/native correspondence tests, retains their exact proposals,
and independently replays those bytes directly through the native checker.
This is test evidence, not a semantic preservation theorem or a legacy verifier.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time
import tomllib

ROOT = Path(__file__).resolve().parents[4]
BASE = ROOT / "tests/fixtures/verification_v029/equivalence"
FROZEN = {
    "results.json": "3b5f3bf8d5d7311114b302bfe78e3eb0ec76ef4700af6b8fe4cf339bf6d1c699",
    "inputs.jsonl.gz": "296c36efa109762fefe9386c9a5b53ac010f8aa94e7464f595c0bf3173f3fae1",
}
EXPECTED = {
    "nested-shared-dag", "certified-use-and-logical", "branch-true", "branch-false",
    "meaning/T", "meaning/S = T T", "meaning/Z", "meaning/X = H Z H", "meaning/X",
    "meaning/CNOT (low control)", "meaning/CZ",
}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_paths():
    registry = ROOT / "lean/schema-registry.json"
    registered = json.loads(registry.read_bytes())["source_revision"]["files"]
    paths = {ROOT / name for name in registered}
    paths |= set((ROOT / "src").rglob("*.rs"))
    # The full target also discovers source projects and embeds the stdlib.
    # Re-enumerate after execution so additions/removals cannot evade binding.
    for directory in ("examples", "corpus", "stdlib"):
        paths |= {path for path in (ROOT / directory).rglob("*")
                  if path.is_file() and (path.suffix == ".qli" or path.name == "Qargo.toml")}
    paths |= {ROOT / "Cargo.toml", ROOT / "Cargo.lock", registry,
              ROOT / "tests/native_roundtrip.rs", Path(__file__).resolve()}
    return sorted(paths)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--kernel", type=Path, default=ROOT / "lean-kernel/.lake/build/bin/qleisli-kernel")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    kernel = args.kernel.resolve()
    if {name: digest(BASE / name) for name in FROZEN} != FROZEN:
        raise ValueError("immutable baseline changed")
    sources = {str(path.relative_to(ROOT)): digest(path) for path in source_paths()}
    binary_hash = digest(kernel)
    version = tomllib.loads((ROOT / "Cargo.toml").read_text())["package"]["version"]
    args.output.mkdir(parents=True, exist_ok=False)
    command = ["cargo", "test", "--locked", "--test", "native_roundtrip", "--",
               "--nocapture", "--test-threads=1"]
    started = time.monotonic()
    result = subprocess.run(command, cwd=ROOT, env=os.environ | {"QLEISLI_KERNEL": str(kernel)},
                            capture_output=True, timeout=180, check=False)
    for stream in ("stdout", "stderr"):
        (args.output / f"cargo.{stream}.gz").write_bytes(
            gzip.compress(getattr(result, stream), mtime=0))
    if result.returncode:
        raise ValueError(f"Rust correspondence tests exited {result.returncode}; output retained")
    artifacts, coverage = {}, {}
    for line in result.stdout.decode().splitlines():
        if "ROUNDTRIP_ARTIFACT\t" in line:
            # libtest's single-threaded progress label prefixes the first line
            # of a test even with --nocapture; the hex payload is unambiguous.
            name, encoded = line.split("ROUNDTRIP_ARTIFACT\t", 1)[1].split("\t", 1)
            if name in artifacts:
                raise ValueError(f"duplicate proposal: {name}")
            artifacts[name] = bytes.fromhex(encoded)
        elif "ROUNDTRIP_COVERAGE\t" in line:
            name, encoded = line.split("ROUNDTRIP_COVERAGE\t", 1)[1].split("\t", 1)
            if name in coverage:
                raise ValueError(f"duplicate coverage: {name}")
            coverage[name] = json.loads(encoded)
    if set(artifacts) != EXPECTED or set(coverage) != EXPECTED:
        raise ValueError("missing or changed positive cases")
    observations = []
    for index, name in enumerate(sorted(EXPECTED)):
        artifact = artifacts[name]
        document = json.loads(artifact)
        entries = document["evidence"]
        counts = coverage[name]
        if not entries or counts.get("unique_receipts", 0) != len(entries):
            raise ValueError(f"zero or incomplete evidence coverage: {name}")
        expected_tag = "meaning" if name.startswith("meaning/") else "circuit"
        if any(entry["tag"] != expected_tag for entry in entries):
            raise ValueError(f"wrong evidence class: {name}")
        filename = f"{index:02d}.qirf"
        (args.output / filename).write_bytes(artifact)
        packet = b"QLV1" + len(artifact).to_bytes(4, "little") + bytes(4) + artifact
        native_command = [str(kernel), "--qirf-native", version]
        replay = subprocess.run(native_command, input=packet, capture_output=True, timeout=10, check=False)
        if replay.returncode or replay.stderr or not replay.stdout.startswith(b"qleisli.qirf-native 1\naccepted\n"):
            raise ValueError(f"native replay did not accept {name}: {replay.stdout!r}")
        observations.append(dict(name=name, artifact=filename, artifact_sha256=digest(args.output / filename),
                                 artifact_bytes=len(artifact), evidence_class=expected_tag,
                                 coverage=counts, native_command=native_command, exit_code=replay.returncode,
                                 stdout=replay.stdout.decode(), stderr=replay.stderr.decode()))
    if sources != {str(path.relative_to(ROOT)): digest(path) for path in source_paths()} or digest(kernel) != binary_hash:
        raise ValueError("source or native binary changed during recording")
    if {name: digest(BASE / name) for name in FROZEN} != FROZEN:
        raise ValueError("immutable baseline changed during recording")
    head = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True, text=True, check=False)
    report = dict(format="qleisli.positive-roundtrip-supplement", version=1, status="passed",
                  scope="11 accepted small artifacts: Rust/native canonical correspondence and exact cached implementation matrices; no universal equivalence or source preservation theorem",
                  base_commit=head.stdout.strip() if head.returncode == 0 else None,
                  source_identity="source_sha256 binds the actual files; base_commit alone does not describe uncommitted or archived test additions",
                  frozen_baseline_sha256=FROZEN, source_sha256=sources, kernel_sha256=binary_hash,
                  product_version=version, command=command, command_exit_code=result.returncode,
                  elapsed_seconds=time.monotonic() - started,
                  toolchains={tool: subprocess.check_output([tool, "--version"], cwd=ROOT, text=True).strip()
                              for tool in ("cargo", "rustc", "python3")},
                  observations=observations,
                  summary=dict(accepted_artifacts=11, circuit_artifacts=4, meaning_artifacts=7,
                               evidence_entries=sum(row["coverage"]["unique_receipts"] for row in observations),
                               maximum_live_qubits=2, frozen_baseline_unchanged=True),
                  files={path.name: digest(path) for path in sorted(args.output.iterdir()) if path.is_file()})
    (args.output / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report["summary"]))


if __name__ == "__main__":
    main()
