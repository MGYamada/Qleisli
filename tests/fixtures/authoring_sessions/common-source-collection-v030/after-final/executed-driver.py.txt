#!/usr/bin/env python3
"""Fixed small source-collection captures; metadata never selects commands.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""

import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

root = Path(__file__).resolve().parent
repo = root.parents[3]
phase, = sys.argv[1:]
if phase != "before" and not re.fullmatch(r"after(?:-[a-z0-9]+)?", phase):
    raise SystemExit("use before or a distinct after[-label] capture")
out = root / phase
out.mkdir()
binary = Path("/private/tmp/qleisli-bounded-validation-target/debug/qleisli")
native = repo / "lean-kernel/.lake/build/bin/qleisli-kernel"
wrapper = root / "native-log.py"
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
first_identity = json.loads((root / "identity-before.json").read_text())
frozen = json.loads((root / "first-files.json").read_text())["files"]


def current_identity():
    lean_paths = [p for p in (repo / "lean-kernel").rglob("*.lean")
                  if ".lake" not in p.relative_to(repo / "lean-kernel").parts]
    lean_paths += [repo / "lean-kernel/lean-toolchain", repo / "lean-kernel/lake-manifest.json"]
    return {
        "cli_sha256": sha(binary), "native_sha256": sha(native),
        "production_rust_sources": {str(p.relative_to(repo)): sha(p)
                                    for p in sorted((repo / "src").rglob("*.rs"))},
        "lean_kernel_sources": {str(p.relative_to(repo)): sha(p)
                                for p in sorted(set(lean_paths)) if p.is_file()},
        "stdlib_sources_and_manifest": {str(p.relative_to(repo)): sha(p)
                                        for p in sorted((repo / "stdlib").rglob("*"))
                                        if p.is_file() and p.suffix in {".qli", ".toml"}},
        "contract_files": {p: sha(repo / p) for p in first_identity["contract_files"]},
        "cargo_files": {p: sha(repo / p) for p in ("Cargo.toml", "Cargo.lock")},
    }


identity = current_identity()
if phase == "before":
    assert all(identity[key] == first_identity[key] for key in identity)
for key in ("native_sha256", "lean_kernel_sources", "stdlib_sources_and_manifest"):
    assert identity[key] == first_identity[key], "this collection study does not change native/std semantics"


def unchanged():
    assert all(sha(root / name) == digest for name, digest in frozen.items())
    assert current_identity() == identity, "source or executable changed during this capture"


unchanged()
(out / "executed-driver.py.txt").write_bytes(Path(__file__).read_bytes())
capture_identity = dict(identity, phase=phase,
                        captured_head=subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=repo, text=True).strip(),
                        cli_path=str(binary), native_path=str(native),
                        recorded_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                        scope="Current bytes, not compilation attestation, proof or acceptance authority. Baseline is never rewritten.")
(out / "identity.json").write_text(json.dumps(capture_identity, indent=2) + "\n")

# Every source mapping and entry is fixed here; no command is read from records.
cases = [
    ("finite-bundled-qft2", None),
    ("local-helper-private", [("main", "main.qli"), ("helper", "helper.qli")]),
    ("unused-invalid-sibling", [("main", "main.qli"), ("helper", "helper.qli")]),
    ("external-private-import", [("main", "main.qli"), ("helper", "helper.qli")]),
    ("unsupported-basis", [("main", "main.qli"), ("a_basis", "a_basis.qli")]),
    ("profile-before-late-parse", [("main", "main.qli"), ("a_basis", "a_basis.qli"), ("z_malformed", "z_malformed.qli")]),
    ("parse-before-late-profile", [("main", "main.qli"), ("a_malformed", "a_malformed.qli"), ("z_basis", "z_basis.qli")]),
    ("reserved-std-injection", [("main", "main.qli"), ("std::injected", "injected.qli")]),
]
session_path = root / "session.json"
session = json.loads(session_path.read_text())
attempt = session["attempts"][0]
assert not any(name.startswith(phase + "/") for name in attempt["observations"])
rows = []
for case, modules in cases:
    project = root / "attempt-01" / case
    actions = [("check", "text"), ("check", "json")]
    if modules is not None:
        actions.append(("emit-proposal", "json"))
    for action, presentation in actions:
        unchanged()
        label = case + "-" + action + "-" + presentation
        native_log = out / (label + ".native.jsonl")
        native_log.touch()
        if modules is None:
            command = [str(binary), action, str(project)]
        else:
            command = [str(binary), action, "--entry=main::entry"]
            command += ["--module=" + name + "=" + str(project / source)
                        for name, source in modules]
        proposal = out / (label + ".proposal.json")
        if action == "emit-proposal":
            command.append("--output=" + str(proposal))
        else:
            command.append("--lean-kernel=" + str(wrapper))
        if presentation == "json":
            command.append("--format=json")
        env = dict(os.environ, QLEISLI_STUDY_NATIVE=str(native),
                   QLEISLI_STUDY_NATIVE_LOG=str(native_log),
                   QLEISLI_KERNEL=str(wrapper), PYTHONDONTWRITEBYTECODE="1")
        start = time.monotonic()
        result = subprocess.run(command, cwd=repo, env=env, capture_output=True, timeout=90)
        (out / (label + ".stdout.txt")).write_bytes(result.stdout)
        (out / (label + ".stderr.txt")).write_bytes(result.stderr)
        event = {"command": command, "exit_code": result.returncode,
                 "stderr": result.stderr.decode(),
                 "native_invocations": len(native_log.read_text().splitlines()),
                 "seconds": time.monotonic() - start,
                 "recorded_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
                 "timestamp_note": "Clock after completion; not authenticated provenance.",
                 "proposal_emitted": proposal.exists()}
        if presentation == "json":
            try:
                event["stdout"] = json.loads(result.stdout)
            except ValueError as error:
                event["transcript"] = result.stdout.decode() + result.stderr.decode()
                event["json_parse_error"] = str(error)
        else:
            event["transcript"] = result.stdout.decode() + result.stderr.decode()
        if proposal.exists():
            event["proposal_file"] = str(proposal.relative_to(root))
            event["proposal_sha256"] = sha(proposal)
            event["proposal_bytes"] = proposal.stat().st_size
            event["proposal_authority"] = "Untrusted selected-source proposal; emission does not invoke native acceptance."
        path = out / (label + ".json")
        path.write_text(json.dumps(event, indent=2) + "\n")
        attempt["observations"].append(str(path.relative_to(root)))
        session_path.write_text(json.dumps(session, indent=2) + "\n")
        rows.append({"case": case, "action": action, "presentation": presentation,
                     "observation": str(path.relative_to(root)), "exit_code": result.returncode,
                     "native_invocations": event["native_invocations"],
                     "proposal_emitted": proposal.exists()})
        (out / "summary.json").write_text(json.dumps({"rows": rows}, indent=2) + "\n")
        unchanged()
        print(label, result.returncode, event["native_invocations"], proposal.exists(), flush=True)

if phase != "before":
    comparisons = []
    for row in rows:
        label = Path(row["observation"]).name
        old_path = root / "before" / label
        new_path = root / row["observation"]
        old = json.loads(old_path.read_text())
        new = json.loads(new_path.read_text())
        stem = label.removesuffix(".json")
        comparison = {"case": row["case"], "action": row["action"], "presentation": row["presentation"],
                      "same_exit_code": old["exit_code"] == new["exit_code"],
                      "same_stdout_bytes": (root / "before" / (stem + ".stdout.txt")).read_bytes() == (out / (stem + ".stdout.txt")).read_bytes(),
                      "same_stderr_bytes": (root / "before" / (stem + ".stderr.txt")).read_bytes() == (out / (stem + ".stderr.txt")).read_bytes(),
                      "same_native_call_count": old["native_invocations"] == new["native_invocations"],
                      "same_proposal_presence": old["proposal_emitted"] == new["proposal_emitted"],
                      "ordering_sensitive": row["case"] in {"profile-before-late-parse", "parse-before-late-profile"}}
        if old.get("proposal_file") and new.get("proposal_file"):
            comparison["same_proposal_bytes"] = (root / old["proposal_file"]).read_bytes() == (root / new["proposal_file"]).read_bytes()
        comparisons.append(comparison)
    (out / "comparison.json").write_text(json.dumps({
        "comparisons": comparisons,
        "scope": "Exact original output/proposal-byte comparisons; changes are recorded for review and never automatically waived or accepted as equivalent.",
    }, indent=2) + "\n")
unchanged()
print("completed", phase, len(rows), "observations", flush=True)
