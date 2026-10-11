#!/usr/bin/env python3
"""Audit this frozen hosted snapshot locally; never execute record-provided commands."""
from pathlib import Path
import gzip
import hashlib
import json

ROOT = Path(__file__).resolve().parent
RUN = 37336154083
HEAD = "9256fe9ef4ffa722066b0569ee37341cf65dea0d"
BASE = "ba83c5c97a9c67bf3904423745b3e9c019a083cb"
MERGE = "7549cecca246b9335a3e1b8f9e4a176df8827d0a"
PRODUCERS = {
    "check-rust", "check-rust-msrv", "check-macos-source", "check-interop",
    "check-lean", "check-lean-kernel", "check-distribution", "check-docs",
}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def read(name):
    return json.loads((ROOT / name).read_text())


def audit():
    run = read("run.api.json")
    merge = read("merge.api.json")
    jobs = read("jobs.connector.json")["structuredContent"]["jobs"]
    assert run["id"] == RUN and run["head_sha"] == HEAD
    assert run["status"] == "in_progress" and run["conclusion"] is None
    assert run["event"] == "pull_request" and run["run_attempt"] == 1
    assert merge["sha"] == MERGE
    assert [parent["sha"] for parent in merge["parents"]] == [BASE, HEAD]
    assert merge["tree"]["sha"] == run["head_commit"]["tree_id"]
    by_name = {job["name"]: job for job in jobs}
    assert len(by_name) == len(jobs) and set(by_name) == PRODUCERS | {"changes"}
    assert all(job["run_id"] == RUN for job in jobs)
    unfinished = sorted(name for name in PRODUCERS if by_name[name]["status"] != "completed")
    assert unfinished == ["check-distribution", "check-rust", "check-rust-msrv"]
    completed = sorted(name for name in PRODUCERS if by_name[name]["status"] == "completed")
    assert all(by_name[name]["conclusion"] == "success" for name in completed)
    checkout = []
    identities = read("decoded-log-identities.json")["files"]
    assert len(identities) == 6
    for identity in identities:
        compressed = (ROOT / identity["file"]).read_bytes()
        data = gzip.decompress(compressed)
        assert digest(compressed) == identity["compressed_sha256"]
        assert digest(data) == identity["decoded_sha256"]
        assert len(data) == identity["decoded_bytes"]
        lines = data.decode("utf-8").splitlines()
        assert len(lines) == identity["decoded_lines"]
        matches = [(index + 1, line) for index, line in enumerate(lines)
                   if line.endswith("Z " + MERGE)]
        assert len(matches) == 1
        number, line = matches[0]
        assert "git log -1 --format=%H" in lines[number - 2]
        head_lines = [(index + 1, value) for index, value in enumerate(lines)
                      if "HEAD is now at 7549cec Merge " + HEAD + " into " + BASE in value]
        assert len(head_lines) == 1
        checkout.append({
            "complete_log": identity["file"],
            "decoded_sha256": digest(data),
            "exact_sha_line": {"line": number, "text": line},
            "merge_message_line": {"line": head_lines[0][0], "text": head_lines[0][1]},
        })
    snapshot = read("snapshot.json")
    assert snapshot["run"]["published_head_sha"] == HEAD
    assert snapshot["completed_producers"] == len(completed) == 5
    assert set(snapshot["unfinished_producers"]) == set(unfinished)
    assert not snapshot["aggregate"]["aggregate_success_established"]
    assert not snapshot["aggregate"]["all_eight_producers_terminal"]
    assert snapshot["aggregate"]["observed_jobs"] == []
    for name in completed:
        skips = [step["name"] for step in by_name[name]["steps"]
                 if step["conclusion"] == "skipped"]
        assert "Bind successful producer evidence for scoped release readiness" in skips
        assert "Retain exact producer receipt and planned artifact bytes" in skips
    assert any(step["name"] == "Compile changed mathematical proofs and audit their declarations"
               and step["conclusion"] == "skipped"
               for step in by_name["check-lean"]["steps"])
    workflow = (ROOT / "workflow-9256fe9.yml").read_text()
    assert "check: [rust, rust-msrv, macos-source, interop, lean, lean-kernel, distribution, docs]" in workflow
    assert "needs: [changes, check-rust, check-rust-msrv, check-macos-source, check-interop, check-lean, check-lean-kernel, check-distribution, check-docs]" in workflow
    assert "github.event_name == 'workflow_dispatch' && inputs.release_readiness" in workflow
    output = {
        "format": "qleisli.hosted-checkout-artifact-audit", "version": 1,
        "run": RUN, "published_head": HEAD, "checked_merge": MERGE,
        "parents_in_order": [BASE, HEAD],
        "complete_successful_job_log_checkouts": checkout,
        "successful_terminal_producers": completed,
        "unfinished_producers_at_snapshot": unfinished,
        "required_aggregate_success_established": False,
        "release_readiness_established": False,
        "skipped_release_receipts_preserved": True,
        "changed_math_proof_compilation_skipped": True,
        "all_local_artifact_assertions_passed": True,
        "scope": "Frozen transport/data audit only; no fresh GitHub request, CI/test execution, source adequacy or constitutional discharge.",
    }
    (ROOT / "checkout-audit.json").write_text(json.dumps(output, indent=2) + "\n")
    print(json.dumps({"artifact_audit": "passed", "checked_logs": len(checkout),
                      "completed_producers": len(completed), "nonterminal_producers": unfinished}))


if __name__ == "__main__":
    audit()
