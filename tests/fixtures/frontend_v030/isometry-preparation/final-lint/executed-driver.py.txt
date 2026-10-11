#!/usr/bin/env python3
"""Record final lint on fixed toolchains; never execute result metadata.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""
import datetime
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

packet = Path(__file__).resolve().parent
repo = packet.parents[3]
out = packet / "final-lint"
out.mkdir()
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
paths = set((repo / "src").rglob("*.rs")) | set((repo / "tests").glob("*.rs"))
paths |= set((repo / "tests/common").rglob("*.rs"))
paths |= set((repo / "tests/fixtures/authoring_sessions/isometry-preparation-v030/attempt-01").rglob("main.qli"))
paths |= set((packet / "supplemental-multi-init").glob("*"))
paths |= {repo / "Cargo.toml", repo / "Cargo.lock"}
source = lambda: {str(path.relative_to(repo)): sha(path) for path in sorted(paths) if path.is_file()}
inputs = source()
native = repo / "lean-kernel/.lake/build/bin/qleisli-kernel"
identity = {"source_files": inputs, "native_sha256": sha(native),
    "scope": "Bounded Rust/test/first-Iso-source map, not all dynamic runtime inputs or a complete source dependency closure."}
# This adds current observations for source inputs omitted by the original
# driver. It does not invent hashes captured before those earlier commands.
identity["current_stdlib_sources"] = {
    str(path.relative_to(repo)): sha(path) for path in sorted((repo / "stdlib").rglob("*.qli"))
}
(out / "identity.json").write_text(json.dumps(identity, indent=2) + "\n")
(out / "executed-driver.py.txt").write_bytes(Path(__file__).read_bytes())
rows = []
for label, bin_dir, expected in [("msrv", "/Users/masa/.rustup/toolchains/1.85.0-aarch64-apple-darwin/bin", "1.85.0"),
                                 ("latest", None, "1.98.1")]:
    env = dict(os.environ, CARGO_TARGET_DIR="/private/tmp/qleisli-bounded-validation-target",
        CARGO_INCREMENTAL="0", CARGO_PROFILE_DEV_DEBUG="0", CARGO_PROFILE_TEST_DEBUG="0", CARGO_BUILD_JOBS="2")
    if bin_dir is not None:
        env["PATH"] = bin_dir + ":" + env["PATH"]
    for command in [["cargo", "--version"],
                    ["cargo", "clippy", "--offline", "--all-targets", "--", "-D", "warnings"],
                    ["cargo", "fmt", "--all", "--", "--check"]]:
        start = time.monotonic()
        result = subprocess.run(command, cwd=repo, env=env, capture_output=True, timeout=900)
        name = f"{len(rows):02d}"
        (out / (name + ".stdout.txt")).write_bytes(result.stdout)
        (out / (name + ".stderr.txt")).write_bytes(result.stderr)
        rows.append({"toolchain": label, "command": command, "exit_code": result.returncode,
            "seconds": time.monotonic() - start,
            "recorded_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
            "stdout": name + ".stdout.txt", "stderr": name + ".stderr.txt"})
        (out / "commands.json").write_text(json.dumps(rows, indent=2) + "\n")
        print(label, command, result.returncode, flush=True)
        if result.returncode:
            raise SystemExit(result.returncode)
        if command == ["cargo", "--version"]:
            assert result.stdout.decode().split()[1] == expected
assert inputs == source()
assert identity["native_sha256"] == sha(native)
assert identity["current_stdlib_sources"] == {
    str(path.relative_to(repo)): sha(path) for path in sorted((repo / "stdlib").rglob("*.qli"))
}
