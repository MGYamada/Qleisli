"""Preserve #47's first source and diagnostic bytes without running records.

This is development-history integrity, not source preservation, binary
attestation, a blind authoring benchmark or proof of a generic family.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
"""

import hashlib
import json
from pathlib import Path, PurePosixPath


ROOT = Path(__file__).resolve().parent.parent
BUNDLE = "tests/fixtures/authoring_sessions/unified-requires-v030/first-observations.json"
CONTEXT = "tests/fixtures/authoring_sessions/unified-requires-v030/README.md"
DIGEST = "7516e49094c873a2e87cedaf56ebb14e8cd88ca116aaad2fc0762b0701ca8602"
BASELINE = "803b8512eeaad18c638c54c2446aa12d1727dd82"
CLI = "76d1d7300ff0bccf343edcd73250093df652a31976f1f29316134f8d990db56f"
CHECKER = "00a3a50c2f7c23c4b368377c77ebba7ede795becc51b821a08038ae5872c20b4"


def main():
    data = (ROOT / BUNDLE).read_bytes()
    assert hashlib.sha256(data).hexdigest() == DIGEST
    assert (ROOT / CONTEXT).read_text(encoding="utf-8").strip()
    bundle = json.loads(data)
    assert bundle["format"] == "qleisli.requires-first-observations"
    assert bundle["version"] == 1 and bundle["baseline_commit"] == BASELINE
    assert set(bundle["studies"]) == {"mixed", "order"}
    results = {}
    for label, count, file_count in (("mixed", 8, 51), ("order", 6, 38)):
        study = bundle["studies"][label]
        files = {}
        for entry in study["files"]:
            name = entry["path"]
            path = PurePosixPath(name)
            assert not path.is_absolute() and ".." not in path.parts
            assert name not in files and entry["mode"] == 0o644
            encoded = entry["utf8"].encode("utf-8")
            assert hashlib.sha256(encoded).hexdigest() == entry["sha256"], name
            files[name] = entry["utf8"]
        assert len(files) == file_count
        before = json.loads(files["study.before.json"])
        observations = json.loads(files["observations.json"])["observations"]
        assert before["kind"] == "informed-study"
        assert before["git_head"] == BASELINE
        assert before["cli_sha256"] == CLI and before["kernel_sha256"] == CHECKER
        assert before["maximum_quantum_width"] == 1
        assert len(before["cases"]) == count and len(observations) == count
        assert [c["name"] for c in before["cases"]] == [o["name"] for o in observations]
        expected_files = {"study.before.json", "observations.json"}
        if label == "mixed":
            expected_files.add("assessment.after.json")
        results[label] = {}
        for case, observed in zip(before["cases"], observations):
            name = case["name"]
            for suffix in ("main.qli", "Qargo.toml", "expectation.before.json",
                           "observation.json", "stdout.txt", "stderr.txt"):
                expected_files.add(name + "/" + suffix)
            source = files[name + "/main.qli"]
            assert hashlib.sha256(source.encode()).hexdigest() == case["source_sha256"]
            assert hashlib.sha256(files[name + "/Qargo.toml"].encode()).hexdigest() == case["manifest_sha256"]
            assert json.loads(files[name + "/observation.json"]) == observed
            assert observed["argv"] == case["argv"] and observed["cwd"] == case["cwd"]
            assert observed["git_head_after"] == BASELINE
            assert observed["cli_sha256_after"] == CLI
            assert observed["kernel_sha256_after"] == CHECKER
            assert observed["status"] in (0, 1)
            expected = case["expected_status"]
            if expected is not None:
                assert observed["status"] == expected
            stdout, stderr = files[name + "/stdout.txt"], files[name + "/stderr.txt"]
            if observed["status"] == 0:
                result = json.loads(stdout)
                assert result["status"] == "checked" and result["checker_identity"] == "unpinned"
                assert result["request_checked"] is False
                assert result["source_preservation_verified"] is False and stderr == ""
                assert result["verification"]["scope"] == "native-validity"
            else:
                assert stdout == "" and stderr.strip()
            results[label][name] = observed["status"]
        assert set(files) == expected_files
        if label == "mixed":
            assert files["02-closed-false-premise/stderr.txt"] == (
                "main:51..184: size: concrete function premise is false\n"
            )
            assert json.loads(files["assessment.after.json"])["all_sources_preserved"]
        else:
            expectation = json.loads(files["02-guard-after-subtraction/expectation.before.json"])
            assert expectation["expected_status"] is None
            assert "Unknown language-contract expectation" in expectation["expected_boundary"]
            assert files["02-guard-after-subtraction/stderr.txt"] == (
                "main:146..149: size: subtraction lacks a nonnegative guard\n"
            )
    assert sum(status == 0 for cases in results.values() for status in cases.values()) == 6
    print("Preserved #47's 14 first sources and actual diagnostics (89 original files); no recorded command executed.")


if __name__ == "__main__":
    main()
