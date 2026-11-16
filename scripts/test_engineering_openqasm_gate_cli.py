#!/usr/bin/env python3
"""Exercise ordered, phase-sensitive gate reports through the real CLI.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
"""
from fractions import Fraction
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

from test_engineering_openqasm_native import ONE, ZERO, digest, dyadic, encoded, gate_matrix, gate_op, port

COMMAND = "engineering compare-openqasm3-gate"
RESOURCE_MODEL = "openqasm3-ordered-gate-literal-gates-v1"
PROFILES = dict(
    format="qleisli.engineering-openqasm-gate-request",
    version=1,
    claim_kind="engineering-target-operator-resource-bound",
    metric="pure-euclidean-operator-norm-v1",
    checker_profile="canonical-gate-frobenius-r8-v1",
    target_profile="openqasm3-canonical-ordered-gate-r8-v1",
    error_category="implementation-distance",
)


def gate_definition(ports, *lines):
    return "\n".join((
        "OPENQASM 3.0;", 'include "stdgates.inc";', f"gate implementation {ports} {{",
        *lines, "}", "",
    )).encode()


def ideal(gate=None):
    # Descriptors and matrices are authored independently of the actual target.
    operation = [] if gate is None else [gate_op(gate, 0, 1)]
    finish = int(gate is not None)
    basis = dict(tag="bit")
    program = dict(
        quantum_inputs=[port(0, [7])], classical_inputs=[], operations=operation,
        quantum_outputs=[finish], classical_outputs=[], declared_effect="unitary",
    )
    artifact = dict(
        format="qleisli.finite-ir", version=2, profile="finite-meaning-v1", programs=[program],
        evidence=[], sources=[], root=0, root_interface=dict(input=basis, output=basis),
    )
    entries = (ONE, ZERO, ZERO, ONE) if gate is None else gate_matrix(gate)
    matrix = dict(
        format="qleisli.finite-matrix", version=1, rows=2, cols=2, domain="zeta8-dyadic-v1",
        entries=[[dyadic(coefficient) for coefficient in scalar] for scalar in entries],
    )
    return dict(
        leaf=dict(input=port(0, [7]), output=port(finish, [7]), matrix=matrix),
        expected_artifact=encoded(artifact).decode() + "\n",
    )


def run(cli, kernel, directory):
    target = directory / "target.qasm"
    request = directory / "request.json"

    def invoke(actual, data, *, counts=None, status=0, text=False, extra=()):
        target.write_bytes(actual)
        # Keep these original bytes distinct from their parsed representation.
        request_bytes = b" " + encoded(data) + b"\n"
        request.write_bytes(request_bytes)
        result = subprocess.run(
            [cli, "engineering", "compare-openqasm3-gate", str(target), "--edition=2026",
             f"--against={request}", f"--lean-kernel={kernel}",
             *([] if text else ["--format=json"]), *extra],
            capture_output=True, timeout=60, check=False,
        )
        assert result.returncode == status and not result.stderr, result
        if text:
            stdout = result.stdout.decode()
            assert "split after 1 gates; component budgets: 7/2^3 + 0/2^0" in stdout
            assert "1 wires, 2 <= 2 gates, 1 <= 1 T/TDG gates" in stdout
            assert digest(actual) in stdout and digest(request_bytes) in stdout
            assert "constitutional PR/RS: not established" in stdout
            return

        output = json.loads(result.stdout)
        assert (output["format"], output["version"], output["command"]) == ("qleisli.result", 1, COMMAND)
        if status:
            assert output["outcome"] == "error" and output["result"] is None
            assert len(output["diagnostics"]) == 1
            if status == 2:
                assert output["diagnostics"][0]["code"] == "usage"
            return

        assert output["outcome"] == "ok" and not output["diagnostics"]
        report = output["result"]
        for key in ("claim_kind", "metric", "checker_profile", "target_profile",
                    "composition", "error_category", "epsilon"):
            assert report[key] == data[key]
        limits = data["resource_limits"]
        assert report["engineering_resource_model"] == limits["model"]
        assert report["engineering_resource_limits"] == dict(gates=limits["gates"], t_gates=limits["t_gates"])
        assert report["engineering_resource_counts"] == counts
        if "split" in data:
            ideals = [data[component]["ideal"] for component in ("first", "second")]
            assert report["composition_split"] == data["split"]
            assert report["component_epsilons"] == [data[component]["epsilon"] for component in ("first", "second")]
        else:
            ideals = [data["ideal"]]
            assert "composition_split" not in report and "component_epsilons" not in report
        assert report["target_artifact_sha256"] == digest(actual)
        assert report["request_sha256"] == digest(request_bytes)
        assert report["ideal_artifact_sha256"] == [digest(ideal["expected_artifact"].encode()) for ideal in ideals]
        assert report["checker_path"] == kernel and report["checker_identity"] == "unpinned"
        assert 0 < report["native_exact_work"] <= 20_000_000
        for field in ("target_artifact_bound_verified", "pure_phase_bound_verified", "resource_bound_verified"):
            assert report[field] is True
        for field in ("exact_source_correspondence_verified", "coherent_control_verified",
                      "constitutional_pr_verified", "constitutional_rs_verified"):
            assert report[field] is False

    limits = dict(model=RESOURCE_MODEL, gates=2, t_gates=1)
    epsilon = dyadic(Fraction(7, 8))
    sequential = dict(
        PROFILES, composition="ordered-sequential-two-v1", epsilon=epsilon, resource_limits=limits, split=1,
        first=dict(epsilon=epsilon, ideal=ideal()), second=dict(epsilon=dyadic(0), ideal=ideal("x")),
    )
    ordered = gate_definition("a", "t a;", "x a;")
    invoke(ordered, sequential, counts=dict(wires=1, gates=2, t_gates=1))
    invoke(ordered, sequential, text=True)
    invoke(ordered, sequential, status=2, extra=("--format=json",))
    invoke(gate_definition("a", "x a;", "t a;"), sequential, status=1)
    invoke(ordered, dict(sequential, split=0), status=1)
    invoke(ordered, dict(sequential, epsilon=dyadic(1)), status=1)
    for understated in (dict(limits, gates=1), dict(limits, t_gates=0)):
        invoke(ordered, dict(sequential, resource_limits=understated), status=1)
    for field, wrong in (
        ("metric", "complete-adjoint-euclidean-operator-norm-v1"),
        ("target_profile", "openqasm3-canonical-one-qubit-terminal-r8-v1"),
        ("composition", "single-component-v1"),
        ("epsilon", {"parameter": "runtime_precision"}),
        ("resource_limits", dict(limits, model="openqasm3-one-qubit-literal-gates-v1")),
    ):
        invoke(ordered, dict(sequential, **{field: wrong}), status=1)
        invoke(ordered, {name: value for name, value in sequential.items() if name != field}, status=1)

    original = sequential["second"]["ideal"]
    wrong_original = dict(original, expected_artifact=ideal("z")["expected_artifact"])
    invoke(ordered, dict(sequential, second=dict(epsilon=dyadic(0), ideal=wrong_original)), status=1)

    controlled = dict(
        PROFILES, composition="controlled-low-selector-v1", epsilon=dyadic(0),
        ideal=ideal("x"), resource_limits=limits,
    )
    invoke(gate_definition("a, b", "cx a, b;"), controlled, counts=dict(wires=2, gates=1, t_gates=0))
    invoke(gate_definition("a, b", "cx b, a;"), controlled, status=1)

    phase = dict(controlled, epsilon=dyadic(1), ideal=ideal("t"))
    target_phase = gate_definition("a, b", "t a;")
    invoke(target_phase, phase, counts=dict(wires=2, gates=1, t_gates=1))
    invoke(gate_definition("a, b", "tdg a;"), phase, status=1)
    invoke(target_phase, dict(phase, claim_kind="constitutional-target-rs"), status=1)


if __name__ == "__main__":
    with tempfile.TemporaryDirectory(prefix="qleisli-openqasm-gate-cli-") as temporary:
        run(sys.argv[1], str(Path(os.environ["QLEISLI_KERNEL"]).resolve()), Path(temporary))
