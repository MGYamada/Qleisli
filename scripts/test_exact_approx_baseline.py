"""Check captured #31/#163 history without executing any recorded program.

This static integrity check grants no approximation, source-preservation,
binary-attestation, exact admission, cleanup or constitutional authority.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
"""

from datetime import datetime
from fractions import Fraction
import hashlib
import json
from pathlib import Path, PurePosixPath


ROOT = Path(__file__).resolve().parent.parent
CONTEXT = "tests/fixtures/authoring_sessions/exact-approx-boundary-v030/README.md"
BUNDLE = "tests/fixtures/authoring_sessions/exact-approx-boundary-v030/first-observations.json"
DIGEST = "f8f8785f60154086d12bad2135eae9aec69094888f36d0e7c9635f2c6517ea4e"
FREEZE = "438f762756f5848770457e6fa1640a9a2b953c582ab2aa64eb0ce073eb9d4f06"
BASELINE = "a864a85f2160e5e83b0b6317bc70c54669ec4c64"
CLI = "66f9d4875f4bce44e3d07a6be066d3dfc243f1a68ca8bd9cc6f7681a3ff28e5a"
CHECKER = "00a3a50c2f7c23c4b368377c77ebba7ede795becc51b821a08038ae5872c20b4"
ORIGINAL = "/private/tmp/qleisli-beta-31-first-b4snigme/"
NAMES = ("01-ideal-t", "02-actual-identity", "03-wrong-sign-tdg",
         "04-controlled-scalar", "05-complete-z-contract", "06-wrong-residual-reference")


def digest(text):
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def safe_path(name):
    path = PurePosixPath(name)
    assert name and not path.is_absolute() and path.as_posix() == name
    assert all(part not in ("", ".", "..") for part in name.split("/"))
    assert "\\" not in name and not any(ord(char) < 32 for char in name)
    return name


def relative(original):
    # Map a historical label to the in-memory bundle; never open that path.
    assert original.startswith(ORIGINAL)
    return safe_path(original[len(ORIGINAL):])


def main():
    data = (ROOT / BUNDLE).read_bytes()
    assert len(data) == 269597 and hashlib.sha256(data).hexdigest() == DIGEST
    assert (ROOT / CONTEXT).read_text(encoding="utf-8").strip()
    bundle = json.loads(data.decode("utf-8"))
    assert bundle["format"] == "qleisli.exact-approx-first-capture"
    assert bundle["version"] == 1 and bundle["baseline_commit"] == BASELINE
    files = {}
    for entry in bundle["files"]:
        assert set(entry) == {"path", "mode", "sha256", "utf8"}
        name = safe_path(entry["path"])
        assert name not in files and type(entry["mode"]) is int and entry["mode"] == 0o644
        assert digest(entry["utf8"]) == entry["sha256"], name
        files[name] = entry["utf8"]
    assert len(files) == 145 and sum(len(text.encode("utf-8")) for text in files.values()) == 219501
    read = lambda name: json.loads(files[name])
    before = read("study.before.json")
    assert digest(files["study.before.json"]) == FREEZE
    assert before["format"] == "qleisli.exact-approx-first-study" and before["kind"] == "informed-study"
    assert before["git_head"] == BASELINE and before["cli_sha256"] == CLI
    assert before["kernel_sha256"] == CHECKER and before["maximum_physical_quantum_width"] == 2
    assert before["source_repairs"] == 0
    assert tuple(case["name"] for case in before["cases"]) == NAMES
    for case in before["cases"]:
        project = "attempt-01/" + case["name"]
        assert relative(case["source"]) == project + "/main.qli"
        for suffix, key in (("main.qli", "source_sha256"), ("Qargo.toml", "manifest_sha256"),
                            ("expectation.before.json", "expectation_sha256")):
            assert digest(files[project + "/" + suffix]) == case[key]
        expectation = read(project + "/expectation.before.json")
        assert expectation["kind"] == "mathematical-prediction-before-observation"
        assert 1 <= expectation["maximum_physical_quantum_width"] <= 2

    first = read("observations.json")["observations"]
    later = read("followup.observations.json")["observations"]
    assert len(first) == 28 and len(later) == 6
    assert read("observations.partial.json")["observations"] == first
    intended = read("commands.intended.json")
    assert [(o["case"], o["action"], o["argv"]) for o in first] == [
        (c["case"], c["action"], c["argv"]) for c in intended]
    followup = read("followup.before.json")
    assert followup["original_observations_sha256"] == digest(files["observations.json"])
    assert followup["kind"] == "repair-and-deliberate-counterexample" and followup["repairs"] == 1
    assert [(o["case"], o["action"], o["argv"], o["cwd"]) for o in later] == [
        (c["case"], c["action"], c["argv"], c["cwd"]) for c in followup["new_commands"]]
    repair = read("attempt-02/03-wrong-sign-phase/expectation.before.json")
    assert repair["recorded_before_check"] and repair["prior_sha256"] == before["cases"][2]["source_sha256"]
    assert relative(repair["prior_source"]) == "attempt-01/03-wrong-sign-tdg/main.qli"
    assert repair["source_sha256"] == digest(files["attempt-02/03-wrong-sign-phase/main.qli"])
    negative = read("counterexamples/wrong-residual-contract/expectation.before.json")
    assert negative["recorded_before_check"] and negative["expected_status"] == 1
    assert negative["expected_category"] == "contract"
    assert negative["source_sha256"] == digest(files["counterexamples/wrong-residual-contract/main.qli"])

    results = {}
    observations = first + later
    for observed in observations:
        key = (observed["case"], observed["action"])
        assert key not in results and observed["exit_code"] in (0, 1)
        # Follow-up observations have no timeout field; retained exits are terminal.
        assert observed.get("timeout", False) is False
        assert observed["cli_sha256_after"] == CLI and observed["kernel_sha256_after"] == CHECKER
        assert observed["git_head_after"] == BASELINE and observed["argv"][0] == before["cli"]
        project = relative(observed["cwd"])
        assert observed["source_sha256_after"] == digest(files[project + "/main.qli"])
        assert observed["manifest_sha256_after"] == digest(files[project + "/Qargo.toml"])
        created = before["created_utc"] if observed in first else followup["created_utc"]
        assert datetime.fromisoformat(created) < datetime.fromisoformat(observed["started_utc"])
        assert datetime.fromisoformat(observed["started_utc"]) <= datetime.fromisoformat(observed["finished_utc"])
        prefix = "observations/" + "/".join(key) + "/"
        assert read(prefix + "command.json") == observed
        for stream in ("stdout", "stderr"):
            assert digest(files[prefix + stream + ".txt"]) == observed[stream + "_sha256"]
        assert files[prefix + "stderr.txt"] == ""
        result = read(prefix + "stdout.txt")
        assert result["format"] == "qleisli.result" and result["version"] == 1
        assert result["outcome"] == ("ok" if observed["exit_code"] == 0 else "error")
        assert observed["exit_code"] == 0 or result["diagnostics"]
        results[key] = result
        if observed["exit_code"] == 0 and observed["action"] in ("project-emit-ir", "selected-emit-proposal"):
            target = next(arg[len("--output="):] for arg in observed["argv"] if arg.startswith("--output="))
            artifact = read(relative(target))
            assert artifact["format"] in ("qleisli.finite-ir", "qleisli.hierarchical-ir")
        if observed["exit_code"] == 0 and observed["action"] == "selected-emit-proposal":
            assert result["result"]["status"] == "untrusted-proposal"
            assert result["result"]["native_check_scope"] == "none"

    assert sum(o["exit_code"] == 0 for o in observations) == 28
    assert sum(o["exit_code"] == 1 for o in observations) == 6
    for action in ("selected-run-basis-one", "selected-emit-proposal"):
        diagnostic = results[(NAMES[2], action)]["diagnostics"][0]
        assert diagnostic["code"] == "unsupported" and "std::quantum::tdg" in diagnostic["message"]
    for action in ("project-check", "project-run"):
        diagnostic = results[("attempt-02-wrong-sign-phase", action)]["diagnostics"][0]
        assert diagnostic["code"] == "unsupported" and "finite lowering profile" in diagnostic["message"]
    for action in ("project-check", "selected-check-raw"):
        assert results[("counterexample-wrong-residual-contract", action)]["diagnostics"][0]["code"] == "contract"
    assert results[(NAMES[0], "selected-run-basis-one")]["result"]["amplitudes"][1][1] > 0
    assert results[("attempt-02-wrong-sign-phase", "selected-run-basis-one")]["result"]["amplitudes"][1][1] < 0

    assessment = read("assessment.after.json")
    for key, value in {"first_source_count": 6, "first_observation_count": 28,
                       "followup_observation_count": 6, "total_observation_count": 34,
                       "successes": 28, "refusals": 6, "timeouts": 0,
                       "source_repairs": 1, "curated_later_counterexamples": 1}.items():
        assert assessment[key] == value
    assert assessment["scope"] == bundle["claim_scope"]
    for key in ("all_first_sources_manifests_predictions_unchanged", "all_cli_identities_unchanged",
                "all_kernel_identities_unchanged", "all_observed_git_heads_equal_initial",
                "mathematical_predictions_remain_separate"):
        assert assessment[key] is True
    assert "No approximation API or metric/bound certificate" in assessment["engineering_contract_status"]
    assert "Not instrumented" in assessment["native_invocation_counts"]
    for name in NAMES:
        assert assessment["project_run_distributions"][name] == results[(name, "project-run")]["result"]["distribution"]

    host = read("bound-experiment.json")
    assert host["format"] == "qleisli.exact-host-bound-experiment" and host["version"] == 1
    assert host["first_source_record_sha256"] == FREEZE
    assert host["script_sha256"] == digest(files["bound-experiment.py"])
    assert host["coefficient_order"] == ["1", "sqrt(2)", "i", "i*sqrt(2)"]
    expected = (("2", "-1", "7/8", True), ("2", "-1", "1/2", False),
                ("2", "0", "7/8", False), ("4", "0", "1", False),
                ("0", "0", "0", True), ("4", "-2", "7/8", False),
                ("2", "0", "7/4", True))
    assert len(host["cases"]) == len(expected)
    for case, (a, b, epsilon, established) in zip(host["cases"], expected):
        assert case["squared_frobenius_difference"] == [a, b, "0", "0"]
        assert case["epsilon"] == epsilon and case["sufficient_witness_established"] is established
        margin = [str(Fraction(epsilon) ** 2 - Fraction(a)), str(-Fraction(b)), "0", "0"]
        assert case["epsilon_squared_minus_difference"] == margin
        assert "no general impossibility claim" in case["rejection_meaning"]
    assert "no production acceptance" in host["claims"][0]
    assert "refinement theorem" in host["claims"][1] and "checked isometry premises" in host["claims"][3]
    assert "zero case grants no exact correspondence" in host["claims"][4]
    assert "does not validate native arithmetic capacities or work limits" in host["claims"][5]
    print("Preserved #31/#163's six first sources, 34 observations and seven host calculations "
          "(145 original files); no recorded command or Python executed.")


if __name__ == "__main__":
    main()
