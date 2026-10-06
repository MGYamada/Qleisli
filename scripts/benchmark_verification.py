#!/usr/bin/env python3
"""Measure existing small .qli clients using environment and explicit native selection.

Build both binaries first; this harness deliberately does not build or simulate.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import platform
import random
import shlex
import statistics
import subprocess
import tempfile
import time

from check_input_corpus import check_manifest, current_project

ROOT = Path(__file__).resolve().parents[1]
CASES = [
    ("bell", "corpus/quantum_katas/bell_measure", 2),
    ("classical_branch", "tests/fixtures/frontend_v030/ordinary-type-cutover/current/authoring_sessions/dual-v028/attempt-02", 2),
    ("grover2", "corpus/quantum_katas/grover2", 2),
    ("qft2", "corpus/qualtran/qft2", 2),
    ("qpe3", "corpus/quantum_katas/qpe3", 4),
    ("add2", "corpus/qualtran/add2", 4),
    ("qaoa_path3", "corpus/pennylane_demos/qaoa_path_layer3", 3),
    ("negative_rotation", "corpus/pennylane_demos/rotation_both_negative", 1),
]


def digest(data):
    return hashlib.sha256(data).hexdigest()


def metadata(command, cwd=ROOT):
    return subprocess.check_output(command, cwd=cwd, text=True).strip()


def selected_cases(manifest):
    by_project = {case["project"]: case for case in manifest["cases"]}
    selected = []
    for name, source, qubits in CASES:
        if source.startswith("corpus/"):
            project = current_project(by_project[source.removeprefix("corpus/")], ROOT / "corpus")
        else:
            project = ROOT / source
        selected.append((name, project, qubits))
    return selected


def source_hashes(cases, manifest):
    paths = {ROOT / name for name in [
        "Cargo.toml", "Cargo.lock", "stdlib/Qargo.toml", "corpus/Qargo.toml",
        "corpus/manifest.json", "lean-kernel/lakefile.toml",
        "lean-kernel/lean-toolchain", "lean-kernel/lake-manifest.json",
        "scripts/benchmark_verification.py", "scripts/check_input_corpus.py",
    ]}
    paths.update(ROOT / "corpus" / name for name in manifest.get("source_migrations", []))
    for directory, suffix in [("src", "*.rs"), ("stdlib", "*.qli"),
                              ("lean-kernel", "*.lean")]:
        paths.update(path for path in (ROOT / directory).rglob(suffix)
                     if ".lake" not in path.parts)
    for _, source, _ in cases:
        paths.update(source.rglob("*.qli"))
        paths.update(source.rglob("Qargo.toml"))
    return {str(path.relative_to(ROOT)): digest(path.read_bytes())
            for path in sorted(paths)}


def summary(samples):
    values = [sample["elapsed_ns"] / 1e6 for sample in samples]
    quartiles = statistics.quantiles(values, n=4, method="inclusive")
    return dict(count=len(values), median_ms=statistics.median(values),
                min_ms=min(values), max_ms=max(values),
                p25_ms=quartiles[0], p75_ms=quartiles[2])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, default=ROOT / "target/release/qleisli")
    parser.add_argument("--kernel", type=Path,
                        default=ROOT / "lean-kernel/.lake/build/bin/qleisli-kernel")
    parser.add_argument("--warmups", type=int, default=3)
    parser.add_argument("--repeats", type=int, default=20)
    parser.add_argument("--record", type=Path, required=True)
    args = parser.parse_args()
    if args.repeats < 4 or args.warmups < 1:
        parser.error("use at least four measured repetitions and one warmup")
    binary, kernel = args.binary.resolve(), args.kernel.resolve()
    binaries = {str(p): digest(p.read_bytes()) for p in [binary, kernel]}
    manifest = check_manifest(ROOT / "corpus")
    cases = selected_cases(manifest)
    sources = source_hashes(cases, manifest)
    record = dict(
        status="running", started_utc=datetime.datetime.now(datetime.UTC).isoformat(),
        scope="Small finite CLI clients; both selections use the same native verifier",
        environment=dict(platform=platform.platform(), machine=platform.machine(),
                         logical_cpus=os.cpu_count(), python=platform.python_version(),
                         rustc=metadata(["rustc", "--version"]),
                         cargo=metadata(["cargo", "--version"]),
                         lean=metadata(["lake", "env", "lean", "--version"], ROOT / "lean-kernel")),
        git_head=metadata(["git", "rev-parse", "HEAD"]),
        git_diff_sha256=digest(subprocess.check_output(["git", "diff", "--binary"], cwd=ROOT)),
        source_sha256=sources, binary_sha256=binaries,
        method=dict(warmups=args.warmups, repeats=args.repeats, case_order_seed=2903,
                    clock="time.perf_counter_ns", sequential=True,
                    route_order="alternates each repetition and case",
                    included="process launch, source loading/checking, transport, JSON output; emit-ir also writes and syncs a fresh file",
                    excluded="binary builds, warmups, output equality assertions, untimed invocation counter",
                    cache="warm OS caches; fresh CLI/kernel processes; no persistent verifier",
                    controls="no concurrent jobs launched by the harness; no CPU pinning or control over external system load"),
        commands=dict(emit_ir=[str(binary), "emit-ir", "{source}", "--output={fresh_path}", "--format=json"],
                      verify_ir=[str(binary), "verify-ir", "{identical_artifact}", "--format=json"],
                      explicit_extra=[f"--lean-kernel={kernel}"], cwd=str(ROOT)),
        cases=[],
    )
    try:
        with tempfile.TemporaryDirectory(prefix="qleisli-verification-benchmark-") as tmp:
            tmp = Path(tmp)
            serial = 0
            artifacts = {}
            by_name = {}
            for name, source, qubits in cases:
                row = dict(name=name, source=source.relative_to(ROOT).as_posix(), qubits=qubits,
                           samples={action: {route: [] for route in ["environment", "explicit"]}
                                    for action in ["emit-ir", "verify-ir"]})
                record["cases"].append(row)
                by_name[name] = row

            def run(action, name, route, selected_kernel=kernel):
                nonlocal serial
                serial += 1
                row = by_name[name]
                output = tmp / f"output-{serial}.qirf"
                if action == "emit-ir":
                    command = [binary, action, ROOT / row["source"], f"--output={output}", "--format=json"]
                else:
                    command = [binary, action, artifacts[name], "--format=json"]
                if route == "explicit":
                    command.append(f"--lean-kernel={selected_kernel}")
                started = time.perf_counter_ns()
                result = subprocess.run(list(map(str, command)), cwd=ROOT,
                                        env=os.environ | {"QLEISLI_KERNEL": str(selected_kernel)},
                                        capture_output=True, timeout=90)
                elapsed = time.perf_counter_ns() - started
                if result.returncode != 0 or result.stderr:
                    raise RuntimeError((command, result.returncode, result.stdout, result.stderr))
                response = json.loads(result.stdout)
                if response["outcome"] != "ok":
                    raise RuntimeError(response)
                if action == "emit-ir":
                    data = output.read_bytes()
                    if name not in artifacts:
                        artifacts[name] = tmp / f"{name}.qirf"
                        artifacts[name].write_bytes(data)
                        row["artifact_sha256"] = digest(data)
                        row["artifact_bytes"] = len(data)
                    if data != artifacts[name].read_bytes():
                        raise RuntimeError(f"emitted artifact changed: {name}/{route}")
                    output.unlink()
                elif response != dict(format="qleisli.result", version=1, command="verify-ir",
                                      outcome="ok", diagnostics=[],
                                      result=dict(verified=True, request_checked=False)):
                    raise RuntimeError(response)
                return elapsed

            rng = random.Random(2903)
            for action in ["emit-ir", "verify-ir"]:
                for iteration in range(-args.warmups, args.repeats):
                    names = list(by_name)
                    rng.shuffle(names)
                    for index, name in enumerate(names):
                        routes = ["environment", "explicit"] if (iteration + index) % 2 else ["explicit", "environment"]
                        for position, route in enumerate(routes):
                            elapsed = run(action, name, route)
                            if iteration >= 0:
                                by_name[name]["samples"][action][route].append(
                                    dict(iteration=iteration, pair_position=position, elapsed_ns=elapsed))
                    if iteration in [-1, args.repeats - 1]:
                        print(f"{action}: {'warmups' if iteration == -1 else 'measurements'} complete", flush=True)

            # A separate transparent wrapper counts real native launches. Its
            # extra shell/file cost is never included in the timing samples.
            counter = tmp / "native-calls.txt"
            wrapper = tmp / "count-kernel"
            wrapper.write_text("#!/bin/sh\n" +
                               f"printf 'call\\n' >> {shlex.quote(str(counter))}\n" +
                               f"exec {shlex.quote(str(kernel))} \"$@\"\n")
            wrapper.chmod(0o700)
            for name, row in by_name.items():
                row["native_launches"] = {}
                row["summary"] = {}
                for action in ["emit-ir", "verify-ir"]:
                    counter.write_text("")
                    run(action, name, "explicit", wrapper)
                    row["native_launches"][action] = len(counter.read_text().splitlines())
                    stats = {route: summary(row["samples"][action][route])
                             for route in ["environment", "explicit"]}
                    stats["explicit_over_environment"] = stats["explicit"]["median_ms"] / stats["environment"]["median_ms"]
                    row["summary"][action] = stats
                row["all_emissions_byte_identical"] = True
            if source_hashes(cases, manifest) != sources or any(digest(Path(p).read_bytes()) != h for p, h in binaries.items()):
                raise RuntimeError("sources or binaries changed during measurement")
            record["status"] = "passed"
    except BaseException as error:
        record["status"] = "failed"
        record["error"] = repr(error)
        raise
    finally:
        record["finished_utc"] = datetime.datetime.now(datetime.UTC).isoformat()
        args.record.parent.mkdir(parents=True, exist_ok=True)
        args.record.write_text(json.dumps(record, indent=2) + "\n")
    for row in record["cases"]:
        stats = row["summary"]["emit-ir"]
        print(f"{row['name']}: Environment {stats['environment']['median_ms']:.2f} ms, "
              f"explicit {stats['explicit']['median_ms']:.2f} ms, "
              f"{stats['explicit_over_environment']:.1f}x; "
              f"{row['native_launches']['emit-ir']} native launches")


if __name__ == "__main__":
    main()
