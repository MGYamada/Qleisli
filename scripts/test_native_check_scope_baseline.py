"""Check the preserved #363 first observations without executing their commands.

These identity checks preserve development history; they do not authenticate
the author, attest a native binary or prove source/runtime correspondence.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
"""

from pathlib import Path
import hashlib
import json


ROOT = Path(__file__).resolve().parent.parent / "tests/fixtures/authoring_sessions/native-check-scope-v030"
BASELINE = "cebc5cf85b5267a35dd8b708ee12a354ece5f3ee"
CLI_SHA256 = "3d993f8d57cb67fb15143fea7d957555414ab402924bf663c4687921f7bf4cbb"
CHECKER_SHA256 = "00a3a50c2f7c23c4b368377c77ebba7ede795becc51b821a08038ae5872c20b4"


def read_json(name):
    return json.loads((ROOT / name).read_text(encoding="utf-8"))


def main():
    retention = read_json("retention.json")
    assert retention["format"] == "qleisli.cli-scope-retention"
    assert retention["version"] == 1 and retention["baseline_commit"] == BASELINE
    assert retention["context"] == "README.md"
    assert (ROOT / "README.md").read_text(encoding="utf-8").strip()
    expected = {
        "first/generic-library/main.qli", "first/generic-library/Qargo.toml",
        "first/closed-entry/main.qli", "first/closed-entry/Qargo.toml",
        "first/classical-library/main.qli", "first/classical-library/Qargo.toml",
        "observations-initial.json", "observations-with-classical.json",
        "classical-native-trace.json", "trace-checker.py",
    }
    assert set(retention["sha256"]) == expected
    for name, digest in retention["sha256"].items():
        assert hashlib.sha256((ROOT / name).read_bytes()).hexdigest() == digest, name

    sources = {
        "generic-library": "pub unitary fn identity[const n: Nat](q: Q<Bits<n>>) -> Q<Bits<n>> { q }\n",
        "closed-entry": "observe fn main() -> Bit { 0 }\n",
        "classical-library": "pub classical fn identity(x: Bit) -> Bit { x }\n",
    }
    for case, source in sources.items():
        assert (ROOT / "first" / case / "main.qli").read_text(encoding="utf-8") == source
        assert (ROOT / "first" / case / "Qargo.toml").read_text(encoding="utf-8") == (
            'schema-version = 2\n\n[qrate]\nedition = "2026"\n'
        )

    first = read_json("observations-initial.json")
    later = read_json("observations-with-classical.json")
    for record in (first, later):
        assert record["format"] == "qleisli.cli-scope-baseline" and record["version"] == 1
        assert record["commit"] == BASELINE
        assert record["cli_sha256"] == CLI_SHA256
        assert record["checker_sha256"] == CHECKER_SHA256
    assert len(first["observations"]) == 8 and len(later["observations"]) == 12
    assert later["observations"][:8] == first["observations"]
    successes = []
    for observation in later["observations"]:
        case, style = observation["source"], observation["format"]
        assert case in sources and style in {"text", "json"}
        assert observation["argv"][1] == "check"
        assert observation["argv"][2].endswith("/" + case)
        assert "--lean-kernel=" + observation["checker"] in observation["argv"]
        result = json.loads(observation["stdout"]) if style == "json" else None
        if result is not None:
            assert result["format"] == "qleisli.result" and result["version"] == 1
            assert result["command"] == "check"
            assert result["outcome"] == ("ok" if observation["exit_code"] == 0 else "error")
            assert observation["stderr"] == ""
        if case == "generic-library":
            assert observation["exit_code"] == 1
            if result is None:
                assert "main.qli:1:31: unsupported: finite profile does not support static Nat parameters" in observation["stderr"]
            else:
                diagnostic, = result["diagnostics"]
                assert diagnostic["code"] == "unsupported"
                assert diagnostic["primary"]["column"] == 31
                assert diagnostic["message"] == "finite profile does not support static Nat parameters"
        elif observation["exit_code"] == 0:
            successes.append((case, style))
            if result is None:
                assert observation["stdout"] == "checked source and verified IR: " + observation["argv"][2] + "\n"
                assert observation["stderr"] == ""
            else:
                assert result["result"] == {"verified": True} and result["diagnostics"] == []
        else:
            assert observation["exit_code"] == 1 and observation["checker"].endswith("/missing-checker")
            message = result["diagnostics"][0]["message"] if result else observation["stderr"]
            assert "cannot resolve Lean checker" in message
            assert ("std::gate::permute_axes" if case == "classical-library" else "main::main") in message
    assert set(successes) == {(case, style) for case in ("closed-entry", "classical-library") for style in ("text", "json")}

    trace = read_json("classical-native-trace.json")
    assert trace["exit_code"] == 0 and trace["stderr"] == ""
    assert trace["stdout"] == "checked source and verified IR: " + trace["argv"][2] + "\n"
    assert trace["argv"][2].endswith("/classical-library")
    decisions = trace["native_invocations"]
    assert len(decisions) == 18
    for decision in decisions:
        assert decision["args"] == ["--qirf-native", "0.3.0-beta"]
        assert decision["magic"] == "QLV2" and decision["scope"] == 2
        assert decision["graph_bytes"] > 0 and decision["caller_bytes"] > 0
        assert decision["request_bytes"] == 0 and decision["aliases"] == 0
    # Preserve the mistaken expectation as history; the observed trace is the
    # evidence for the distinction between zero requests and zero decisions.
    assert "zero-native-decision success path" in later["followup"]
    wrapper = (ROOT / "trace-checker.py").read_text(encoding="utf-8")
    assert "/tmp/qleisli-beta-362-qlv2-stable-kernel" in wrapper
    print("Preserved #363 first sources, 12 actual CLI observations and 18 request-free native decisions verified; no recorded command executed.")


if __name__ == "__main__":
    main()
