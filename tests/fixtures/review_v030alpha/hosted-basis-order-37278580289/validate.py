"""Record real bounded tests for the adopted ordered-kind fixture migration."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[4]
PACKET = Path(__file__).resolve().parent
STAGE = sys.argv[1]
assert STAGE in {"before", "after"}
OUT = PACKET / STAGE
OUT.mkdir()
ENV = dict(os.environ)
ENV.update(
    CARGO_TARGET_DIR="/private/tmp/qleisli-bounded-validation-target",
    CARGO_INCREMENTAL="0",
    CARGO_PROFILE_DEV_DEBUG="0",
    CARGO_PROFILE_TEST_DEBUG="0",
    CARGO_BUILD_JOBS="2",
    QLEISLI_KERNEL=str(ROOT / "lean-kernel/.lake/build/bin/qleisli-kernel"),
)
MSRV = "/Users/masa/.rustup/toolchains/1.85.0-aarch64-apple-darwin/bin"
latest = shutil.which("cargo")
assert latest
plan = [("msrv", [str(Path(MSRV) / "cargo"), "test", "--offline", "--test", "sized_source", "forwarding_checks_callee_size_and_access_premises"])] if STAGE == "before" else [
    ("latest", [latest, "test", "--offline", "--test", "sized_source", "--test", "basis_polymorphism"]),
    ("msrv", [str(Path(MSRV) / "cargo"), "test", "--offline", "--test", "sized_source", "--test", "basis_polymorphism"]),
    ("latest", [latest, "clippy", "--offline", "--test", "sized_source", "--test", "basis_polymorphism", "--", "-D", "warnings"]),
    ("msrv", [str(Path(MSRV) / "cargo"), "clippy", "--offline", "--test", "sized_source", "--test", "basis_polymorphism", "--", "-D", "warnings"]),
    ("latest", [latest, "fmt", "--check"]),
    ("latest", ["python3", "scripts/check_constitution.py", "--base-ref", "faa5cfb5e7ea1cf3b39a43b80f7f2345e89197c2"]),
    ("latest", ["python3", "scripts/check_verification_inventory.py"]),
    ("latest", ["python3", "scripts/check_production_coverage.py"]),
    ("latest", ["python3", "scripts/check_docs.py"]),
]
paths = sorted(set([Path("Cargo.toml"), Path("Cargo.lock"), Path("tests/sized_source.rs"), Path("tests/basis_polymorphism.rs"), Path("docs/src/reference/type-model.md"), *Path(ROOT / "src").rglob("*.rs")]))
bindings = {}
for path in paths:
    local = path if path.is_absolute() else ROOT / path
    bindings[str(local.relative_to(ROOT))] = hashlib.sha256(local.read_bytes()).hexdigest()
(OUT / "source-files.json").write_text(json.dumps(bindings, indent=2) + "\n")
records = []
for index, (toolchain, argv) in enumerate(plan):
    env = dict(ENV)
    if toolchain == "msrv":
        env["PATH"] = MSRV + os.pathsep + env["PATH"]
    started = time.monotonic()
    result = subprocess.run(argv, cwd=ROOT, env=env, capture_output=True)
    stem = f"{index:02d}-{toolchain}"
    (OUT / (stem + ".stdout.txt")).write_bytes(result.stdout)
    (OUT / (stem + ".stderr.txt")).write_bytes(result.stderr)
    record = dict(argv=argv, toolchain=toolchain, exit_code=result.returncode, seconds=time.monotonic() - started, stdout=stem + ".stdout.txt", stderr=stem + ".stderr.txt")
    records.append(record)
    (OUT / "commands.json").write_text(json.dumps(records, indent=2) + "\n")
    print(json.dumps(record), flush=True)
versions = {}
for toolchain in ["latest", "msrv"]:
    env = dict(ENV)
    if toolchain == "msrv":
        env["PATH"] = MSRV + os.pathsep + env["PATH"]
    versions[toolchain] = {tool: subprocess.check_output([tool, "--version"], cwd=ROOT, env=env).decode().strip() for tool in ["cargo", "rustc"]}
(OUT / "toolchains.json").write_text(json.dumps(versions, indent=2) + "\n")
(OUT / "kernel-identity.json").write_text(json.dumps({"path": ENV["QLEISLI_KERNEL"], "sha256": hashlib.sha256(Path(ENV["QLEISLI_KERNEL"]).read_bytes()).hexdigest(), "claim": "Selected existing native executable identity only; no fresh local Lean replay."}, indent=2) + "\n")
expected = [101] if STAGE == "before" else [0] * len(plan)
actual = [record["exit_code"] for record in records]
print(json.dumps({"stage": STAGE, "expected_exit_codes": expected, "actual_exit_codes": actual, "matches": actual == expected}), flush=True)
sys.exit(0 if actual == expected else 1)
