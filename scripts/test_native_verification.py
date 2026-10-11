#!/usr/bin/env python3
"""VM-28 small-system native/CLI comparisons and adversarial input binding.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile
import tomllib

from check_input_corpus import check_manifest, current_project

ROOT = Path(__file__).resolve().parents[1]
VERSION = tomllib.loads((ROOT / "Cargo.toml").read_text())["package"]["version"]
SOURCE = ROOT / "tests/fixtures/frontend_v030/ordinary-type-cutover/current/authoring_sessions/dual-v028/attempt-02"
FINITE = ROOT / "tests/fixtures/verification_v022/finite"


def encoded(value):
    return json.dumps(value, separators=(",", ":")).encode()


def packet(artifact, request=None):
    return b"QLV1" + len(artifact).to_bytes(4, "little") + len(request or b"").to_bytes(4, "little") + artifact + (request or b"")


def test_control_requests(kernel, run):
    """Fresh original-byte sector checks; no proposed matrix or cached decision."""
    def check(artifact, signature, axes, accepted, request=None, error=None):
        if request is None:
            request = dict(format="qleisli.native-contract", version=1, kind="control",
                           signature=signature, axes=axes)
        output = run([kernel, "--qirf-contract", VERSION], 0 if accepted else 1,
                     packet(encoded(artifact), encoded(request)))
        lines = output.decode().splitlines()
        assert lines[:2] == ["qleisli.qirf-native 1", "accepted" if accepted else "error"], output
        if accepted:
            assert len(lines) == 4 and 0 <= int(lines[2]) <= 10000000 and lines[3] == "1"
        elif error is not None:
            assert lines == ["qleisli.qirf-native 1", "error", error], output

    pair = dict(tag="pair", left=dict(tag="bit"), right=dict(tag="bit"))
    cnot = json.loads((FINITE / "raw_computed_target.v2.qirf").read_bytes())
    check(cnot, pair, [0], True)
    check(cnot, pair, [1], False, error="contract")  # Valid unitary, wrong sector.
    check(cnot, pair, [0, 0], False, error="contract")
    check(cnot, pair, [2], False, error="contract")
    check(cnot, dict(tag="bits", width=2), [0], False, error="contract")
    wrong_root = copy.deepcopy(cnot); wrong_root["root"] = 1
    check(wrong_root, pair, [0], False, error="invalid_ir")
    changed = copy.deepcopy(cnot)
    changed["programs"][0]["operations"] = [dict(tag="apply_unitary", input=0, output=5,
        steps=[dict(controls=[], action=dict(tag="hadamard", target=0))])]
    check(changed, pair, [0], False, error="contract")

    # Existing immutable first artifacts retain exact phases and zero-width owners.
    for name, signature, axes, accepted in [
            ("t", dict(tag="bit"), [0], True),
            ("h", dict(tag="bit"), [0], False),
            ("unit_phase", dict(tag="unit"), [], True),
            ("unit_phase", dict(tag="unit"), [0], False)]:
        check(json.loads((FINITE / f"{name}.v2.qirf").read_bytes()), signature, axes, accepted,
              error=None if accepted else "contract")

    # A dependency replacement is checked against its original independent circuit.
    direct = copy.deepcopy(cnot)
    direct["programs"][0]["operations"] = [dict(tag="apply_unitary", input=0, output=5,
        steps=[dict(controls=[], action=dict(tag="monomial", indices=[0, 1],
                                            permutation=[0, 3, 2, 1], phases=[0, 0, 0, 0]))])]
    dependency = copy.deepcopy(direct)
    dependency["programs"] = [copy.deepcopy(direct["programs"][0]) for _ in range(3)]
    dependency["root"] = 2
    dependency["programs"][2]["operations"][0]["steps"] = [dict(controls=[],
        action=dict(tag="contract", indices=[0, 1], evidence=0, adjoint=False))]
    dependency["evidence"] = [dict(tag="circuit", signature=pair, implementation=0,
        specification=1, identity=dict(implementation="original", specification="reference", sources=[]))]
    check(dependency, pair, [0], True)
    dependency["programs"][0] = copy.deepcopy(changed["programs"][0])
    check(dependency, pair, [0], False, error="contract")

    request = dict(format="qleisli.native-contract", version=1, kind="control",
                   signature=pair, axes=[0])
    for field in request:
        bad = copy.deepcopy(request); del bad[field]
        check(cnot, pair, [0], False, bad)
    for extra in [dict(matrix=[]), dict(accepted=True), dict(work=0)]:
        check(cnot, pair, [0], False, dict(request, **extra))
    for key, value in [("version", 2), ("axes", [-1]), ("axes", [True]), ("axes", "0"),
                       ("kind", "claimed-control")]:
        check(cnot, pair, [0], False, dict(request, **{key: value}))
    for data in [packet(encoded(cnot)), packet(encoded(cnot), b"\xff"),
                 packet(encoded(cnot), encoded(request)) + b"x"]:
        run([kernel, "--qirf-contract", VERSION], 1, data)


def test_control_owner_requests(kernel, run):
    """Bind an explicit ordered owner forest to the original multi-port action."""
    bit, unit = dict(tag="bit"), dict(tag="unit")
    cnot = json.loads((FINITE / "raw_computed_target.v2.qirf").read_bytes())
    cnot["root_interface"] = None
    program = cnot["programs"][0]
    program["quantum_inputs"] = [dict(token=0, wires=[7], shape=dict(bits=1)),
                                 dict(token=1, wires=[19], shape=dict(bits=1))]
    program["operations"] = [dict(tag="cnot", control=0, target=1,
                                  control_out=2, target_out=3)]
    program["quantum_outputs"] = [2, 3]
    request = dict(format="qleisli.native-contract", version=1, kind="control-owners",
                   signatures=[bit, bit], axes=[0])

    def check(artifact=cnot, obligation=request, accepted=False, error=None):
        output = run([kernel, "--qirf-contract", VERSION], 0 if accepted else 1,
                     packet(encoded(artifact), encoded(obligation)))
        lines = output.decode().splitlines()
        assert lines[:2] == ["qleisli.qirf-native 1", "accepted" if accepted else "error"], output
        if accepted:
            assert len(lines) == 4 and 0 <= int(lines[2]) <= 10000000 and lines[3] == "1"
        elif error is not None:
            assert lines == ["qleisli.qirf-native 1", "error", error], output

    check(accepted=True)
    for axes in [[1], [0, 0], [2]]:
        check(obligation=dict(request, axes=axes), error="contract")
    for forest in [[], [dict(tag="bits", width=2)], [unit, dict(tag="bits", width=2)]]:
        check(obligation=dict(request, signatures=forest), error="contract")
    swapped = copy.deepcopy(cnot); swapped["programs"][0]["quantum_outputs"] = [3, 2]
    check(swapped, error="contract")
    hadamard = copy.deepcopy(cnot)
    hadamard["programs"][0]["operations"] = [dict(tag="gate", gate="h", input=0, output=2)]
    hadamard["programs"][0]["quantum_outputs"] = [2, 1]
    check(hadamard, error="contract")
    wrong_root = copy.deepcopy(cnot); wrong_root["root"] = 1
    check(wrong_root, error="invalid_ir")
    wrapped = copy.deepcopy(cnot)
    pair = dict(tag="pair", left=bit, right=bit)
    wrapped["root_interface"] = dict(input=pair, output=pair)
    check(wrapped, error="contract")
    check(obligation=dict(request, signatures=[bit] * 65), error="invalid_ir")

    # Resolve real dependency evidence, not a producer's claimed callee effect.
    direct = json.loads((FINITE / "raw_computed_target.v2.qirf").read_bytes())
    direct["programs"][0]["operations"] = [dict(tag="apply_unitary", input=0, output=5,
        steps=[dict(controls=[], action=dict(tag="monomial", indices=[0, 1],
                                            permutation=[0, 3, 2, 1], phases=[0, 0, 0, 0]))])]
    dependency = copy.deepcopy(cnot)
    root = copy.deepcopy(program)
    root["operations"] = [dict(tag="join", left=0, right=1, output=4),
        dict(tag="apply_unitary", input=4, output=5, steps=[dict(controls=[],
            action=dict(tag="contract", indices=[0, 1], evidence=0, adjoint=False))]),
        dict(tag="split", input=5, left=6, right=7, left_bits=1)]
    root["quantum_outputs"] = [6, 7]
    dependency["programs"] = [copy.deepcopy(direct["programs"][0]),
                               copy.deepcopy(direct["programs"][0]), root]
    dependency["root"] = 2
    dependency["evidence"] = [dict(tag="circuit", signature=pair, implementation=0,
        specification=1, identity=dict(implementation="original", specification="reference", sources=[]))]
    check(dependency, accepted=True)
    dependency["programs"][0]["operations"][0]["steps"] = [dict(controls=[],
        action=dict(tag="hadamard", target=0))]
    check(dependency, error="contract")

    # A zero-width owner keeps its ordered position and its exact scalar phase.
    phase = json.loads((FINITE / "unit_phase.v2.qirf").read_bytes())
    phase["root_interface"] = None
    phase["programs"][0]["quantum_inputs"].append(dict(token=2, wires=[19], shape=dict(bits=1)))
    phase["programs"][0]["quantum_outputs"].append(2)
    phase_request = dict(request, signatures=[unit, bit], axes=[0])
    check(phase, phase_request, True)
    check(phase, dict(phase_request, signatures=[bit, unit]), error="contract")
    phase_swap = copy.deepcopy(phase); phase_swap["programs"][0]["quantum_outputs"] = [2, 1]
    check(phase_swap, phase_request, error="contract")

    for field in request:
        bad = copy.deepcopy(request); del bad[field]
        check(obligation=bad)
    for extra in [dict(matrix=[]), dict(accepted=True), dict(signature=bit)]:
        check(obligation=dict(request, **extra), error="invalid_ir")
    for key, value in [("version", 2), ("axes", [-1]), ("axes", [True]),
                       ("signatures", bit), ("signatures", [dict(tag="unknown")])]:
        check(obligation=dict(request, **{key: value}))


def test_instrument_requests(kernel, run):
    """Exact observing equations from two original graphs and a strict request.

    These small body changes have independent algebraic expectations: HH and
    a branch phase preserve Z readout; relabeling and replacing the residual
    state do not. Whole-root request-free disclosure is checked separately.
    """
    import test_lean_observation as observation
    import test_lean_raw as raw

    bit, unit = dict(tag="bit"), dict(tag="unit")
    qbit = dict(tag="quantum", basis=bit)
    port, op, program = raw.port, raw.op, observation.p

    def artifact(body):
        return dict(format="qleisli.finite-ir", version=1, profile="finite-v0", sources=[],
                    programs=[body], evidence=[], root=0, root_interface=None)

    z = artifact(program([port(0, [0])], operations=[op("measure_z", input=0, output=0)], results=[0]))
    signature = dict(input=bit, result=bit)
    request = dict(format="qleisli.native-contract", version=1, kind="instrument",
                   actual_signature=signature, expected_signature=signature,
                   identity=dict(implementation="implementation", specification="expected",
                                 sources=[dict(path="original.qli", text="retained source identity")]),
                   expected_artifact=encoded(z).decode())

    def check(actual=z, expected=z, sig=signature, accepted=False, obligation=None, error=None):
        if obligation is None:
            obligation = dict(request, actual_signature=sig, expected_signature=sig,
                              expected_artifact=encoded(expected).decode())
        output = run([kernel, "--qirf-contract", VERSION], 0 if accepted else 1,
                     packet(encoded(actual), encoded(obligation)))
        lines = output.decode().splitlines()
        assert lines[:2] == ["qleisli.qirf-native 1", "accepted" if accepted else "error"], output
        if accepted:
            assert len(lines) == 4 and 0 <= int(lines[2]) <= 10000000 and lines[3] == "1"
        elif error is not None:
            assert lines == ["qleisli.qirf-native 1", "error", error], output

    check(accepted=True)
    hh = artifact(program([port(0, [0])], operations=[op("gate", gate="h", input=0, output=1),
        op("gate", gate="h", input=1, output=2), op("measure_z", input=2, output=0)], results=[0]))
    phase = artifact(program([port(0, [0])], operations=[op("gate", gate="t", input=0, output=1),
        op("measure_z", input=1, output=0)], results=[0]))
    flipped = artifact(program([port(0, [0])], operations=[op("measure_z", input=0, output=0),
        op("classical_not", input=0, output=1)], results=[1]))
    check(hh, accepted=True)
    check(phase, accepted=True)
    check(flipped, error="contract")
    discard = artifact(program([port(0, [0])], operations=[op("discard", input=0)]))
    discard_h = artifact(program([port(0, [0])], operations=[op("gate", gate="h", input=0, output=1),
        op("discard", input=1)]))
    check(discard_h, discard, dict(input=bit, result=unit), accepted=True)
    nondestructive = artifact(program([port(0, [0])], operations=[op("init0", output=1, wire=1),
        op("cnot", control=0, target=1, control_out=2, target_out=3),
        op("measure_z", input=3, output=0)], outputs=[2], results=[0]))
    replacement = artifact(program([port(0, [0])], operations=[op("measure_z", input=0, output=0),
        op("init0", output=1, wire=1)], outputs=[1], results=[0]))
    residual = dict(input=bit, result=dict(tag="pair", left=qbit, right=bit))
    check(nondestructive, nondestructive, residual, accepted=True)
    check(replacement, nondestructive, residual, error="contract")
    ordered = copy.deepcopy(flipped); ordered["programs"][0]["classical_outputs"] = [0, 1]
    reversed_results = copy.deepcopy(ordered); reversed_results["programs"][0]["classical_outputs"] = [1, 0]
    check(ordered, reversed_results, dict(input=bit, result=dict(tag="pair", left=bit, right=bit)),
          error="contract")

    zero_owner = copy.deepcopy(z)
    zero_owner["programs"][0]["operations"].append(op("pack_unit", output=1))
    zero_owner["programs"][0]["quantum_outputs"] = [1]
    zero_signature = dict(input=bit, result=dict(tag="pair", left=dict(tag="quantum", basis=unit), right=bit))
    check(zero_owner, zero_owner, zero_signature, accepted=True)
    check(z, zero_owner, zero_signature, error="contract")
    check(zero_owner, error="contract")
    check(discard, discard, dict(input=bit, result=dict(tag="bits", width=0)), accepted=True)
    nested = dict(tag="tuple", fields=[unit, dict(tag="pair", left=unit, right=unit), unit])
    check(discard, discard, dict(input=bit, result=nested), accepted=True)

    pure = program([port(0, [0])], outputs=[0], effect="unitary")
    false_observe = artifact(dict(pure, declared_effect="observe"))
    check(false_observe, false_observe, dict(input=bit, result=qbit), error="contract")
    dependency = copy.deepcopy(z)
    dependency["programs"] = [copy.deepcopy(pure), copy.deepcopy(pure),
        program([port(0, [0])], operations=[op("apply_unitary", input=0, output=1,
            steps=[dict(controls=[], action=dict(tag="contract", indices=[0], evidence=0, adjoint=False))]),
            op("measure_z", input=1, output=0)], results=[0])]
    dependency["root"] = 2
    dependency["sources"] = [dict(path="dependency.qli", text="original dependency identity")]
    dependency["evidence"] = [dict(signature=bit, implementation=0, specification=1,
                                  identity=dict(implementation="id", specification="spec", sources=[0]))]
    check(dependency, accepted=True)
    changed = copy.deepcopy(dependency)
    hadamard = program([port(0, [0])], operations=[op("gate", gate="h", input=0, output=1)],
                      outputs=[1], effect="unitary")
    changed["programs"][0] = hadamard
    check(changed, error="contract")
    changed["programs"][1] = hadamard
    check(changed, error="contract")  # Dependency equation holds; whole instrument differs.
    check(expected=changed, error="contract")
    wrong_root = copy.deepcopy(z); wrong_root["root"] = 9
    check(wrong_root, error="invalid_ir")
    check(expected=wrong_root, error="invalid_ir")

    for field in request:
        bad = copy.deepcopy(request); del bad[field]
        check(obligation=bad)
    for extra in [dict(matrix=[]), dict(accepted=True), dict(work=0), dict(receipt="success")]:
        check(obligation=dict(request, **extra), error="invalid_ir")
    for key, value in [("format", "claimed"), ("version", 2), ("kind", "claimed-instrument"),
                       ("expected_artifact", ""), ("expected_artifact", {}),
                       ("expected_artifact", encoded(z).decode() + "x")]:
        check(obligation=dict(request, **{key: value}))
    for bad in [dict(input=dict(tag="bits", width=1), result=bit),
                dict(input=bit, result=dict(tag="bits", width=1)),
                dict(signature, extra=unit)]:
        check(obligation=dict(request, expected_signature=bad))
    for result in [dict(tag="bits", width=-1), dict(tag="bits", width=True),
                   dict(tag="bits", width=4294967296), dict(tag="bit", extra=0),
                   dict(tag="tuple", fields=[bit, unit]), dict(tag="pair", left=bit),
                   dict(tag="unknown")]:
        check(obligation=dict(request, actual_signature=dict(input=bit, result=result)), error="invalid_ir")
    deep = unit
    for _ in range(66):
        deep = dict(tag="pair", left=unit, right=deep)
    check(obligation=dict(request, expected_signature=dict(input=bit, result=deep)), error="invalid_ir")
    check(obligation=dict(request, identity=dict(request["identity"], implementation="")), error="limit")
    check(obligation=dict(request, identity=dict(request["identity"], matrix=[])), error="invalid_ir")
    for data in [packet(encoded(z)), packet(encoded(z), b"\xff"),
                 packet(encoded(z), encoded(request)) + b"x", packet(encoded(z), encoded(request))[:-1]]:
        run([kernel, "--qirf-contract", VERSION], 1, data)
    # A per-call contract does not turn request-free whole-root inspection into
    # an external functional specification certificate.
    output = run([kernel, "--qirf-native", VERSION], 0, packet(encoded(z)))
    assert output.decode().splitlines()[3] == "0", output


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, default=ROOT / "target/debug/qleisli")
    parser.add_argument("--kernel", type=Path, default=ROOT / "lean-kernel/.lake/build/bin/qleisli-kernel")
    parser.add_argument("--record", type=Path)
    args = parser.parse_args()
    binary, kernel = args.binary.resolve(), args.kernel.resolve()
    observations = []
    environment = dict(os.environ, QLEISLI_KERNEL=str(kernel))

    def run(command, expected=0, data=None):
        result = subprocess.run(list(map(str, command)), input=data, capture_output=True, timeout=70, cwd=ROOT, env=environment)
        row = dict(command=list(map(str, command)), exit_code=result.returncode,
                   stdout=result.stdout.decode(errors="replace"), stderr=result.stderr.decode(errors="replace"))
        if data is not None:
            row["input_sha256"] = hashlib.sha256(data).hexdigest()
        observations.append(row)
        assert (result.returncode == 0) == (expected == 0), row
        return result.stdout

    def native(artifact, request=None, accepted=True):
        data = packet(artifact, request)
        result = run([kernel, "--qirf-native", VERSION], 0 if accepted else 1, data)
        lines = result.decode().splitlines()
        assert lines[:2] == ["qleisli.qirf-native 1", "accepted" if accepted else "error"], result
        if accepted:
            assert len(lines) == 4 and 0 <= int(lines[2]) <= 10000000
            assert lines[3] == ("1" if request is not None else "0")

    try:
        with tempfile.TemporaryDirectory(prefix="qleisli-native-") as directory:
            directory = Path(directory)
            selected = f"--lean-kernel={kernel}"
            absent = {key: value for key, value in environment.items() if key != "QLEISLI_KERNEL"}
            missing = subprocess.run([str(binary), "check", str(SOURCE), "--format=json"],
                                     cwd=directory, env=absent, capture_output=True, timeout=60)
            assert missing.returncode == 1 and json.loads(missing.stdout)["diagnostics"][0]["code"] == "project"
            for mode in ["--qirf-native", "--qirf-contract", "--hierarchy-pending",
                         "--hierarchy-request-pending", "--hierarchy-fourier-pending",
                         "--readout-check", "--preparation-check", "--instrument-pending",
                         "--qpe-instrument-pending"]:
                wrong_version = run([kernel, mode, "0.0.0"], 1, b"")
                assert wrong_version == b"qleisli.qirf-native 1\nerror\nversion\n"
                # A missing version is not an implicit match for any native mode.
                missing_version = run([kernel, mode], 1, b"")
                assert missing_version == b"qleisli.qirf-native 1\nerror\nversion\n"
                matching_version = run([kernel, mode, VERSION], 1, b"")
                assert matching_version != b"qleisli.qirf-native 1\nerror\nversion\n"

            test_control_requests(kernel, run)
            test_control_owner_requests(kernel, run)
            test_instrument_requests(kernel, run)

            for command, extra in [("check", []), ("run", []), ("sample", ["--shots=64", "--seed=7"])]:
                base = json.loads(run([binary, command, SOURCE, "--format=json", *extra]))
                explicit = json.loads(run([binary, command, SOURCE, "--format=json", *extra, selected]))
                assert base == explicit, (command, base, explicit)
            distribution = json.loads(run([binary, "run", SOURCE, "--format=json", selected]))["result"]["distribution"]
            assert {tuple(row["bits"]) for row in distribution} == {(False, False), (True, True)}
            assert all(abs(row["probability"] - 0.5) < 1e-12 for row in distribution)
            run([binary, "check", SOURCE, selected])  # text and JSON share the gate
            outputs = [directory / "environment.qirf", directory / "explicit.qirf"]
            for path, extra in zip(outputs, [[], [selected]]):
                run([binary, "emit-ir", SOURCE, f"--output={path}", "--format=json", *extra])
            assert outputs[0].read_bytes() == outputs[1].read_bytes()
            run([binary, "verify-ir", outputs[1], selected, "--format=json"])
            run([binary, "verify-ir", outputs[1], selected])
            native(outputs[1].read_bytes())
            for command, extra in [("check", []), ("run", []), ("sample", ["--shots=1", "--seed=1"]),
                                   ("emit-ir", [f"--output={directory / 'blocked.qirf'}"])]:
                row = json.loads(run([binary, command, SOURCE, "--format=json", *extra,
                                      f"--lean-kernel={directory / 'absent'}"], 1))
                assert row["result"] is None
            assert not (directory / "blocked.qirf").exists()
            for flags in [[selected, selected], ["--lean-kernel="], [selected, "--against=x"]]:
                run([binary, "check", SOURCE, *flags], 1)
            run([binary, "doc", SOURCE / "main.qli", selected], 1)

            # Untouched VM-22 raw-only forms, empty owners, phases and QIRF1/2.
            for name in ["h", "t", "unit_phase", "toffoli", "raw_qif_unit", "raw_computed_target"]:
                for version in [1, 2]:
                    path = FINITE / f"{name}.v{version}.qirf"
                    native(path.read_bytes())
                    run([binary, "verify-ir", path, selected, "--format=json"])

            artifact = json.loads((FINITE / "t.v2.qirf").read_bytes())
            request = dict(format="qleisli.request", version=1, signature=dict(tag="bit"),
                           meaning=dict(tag="phase8", table=[0, 1]), source_snapshot=None)

            def compare(art, req, accepted):
                a, r = encoded(art), encoded(req)
                native(a, r, accepted)
                ap, rp = directory / "request-artifact.qirf", directory / "request.json"
                ap.write_bytes(a); rp.write_bytes(r)
                for extra in [[], [selected]]:
                    run([binary, "verify-ir", ap, f"--against={rp}", "--format=json", *extra], 0 if accepted else 1)

            compare(artifact, request, True)
            bad = copy.deepcopy(request); bad["meaning"]["table"] = [4, 5]
            compare(artifact, bad, False)  # same probabilities, wrong global phase
            bad = copy.deepcopy(request); bad["signature"] = dict(tag="pair", left=dict(tag="unit"), right=dict(tag="bit"))
            compare(artifact, bad, False)
            bad = copy.deepcopy(request); bad["source_snapshot"] = [dict(path="changed", text="changed")]
            compare(artifact, bad, False)
            supplied = copy.deepcopy(artifact); supplied["sources"] = [dict(path="original", text="original body")]
            matching = copy.deepcopy(request); matching["source_snapshot"] = supplied["sources"]
            compare(supplied, matching, False)  # matching text cannot legitimize unused sources
            matching = copy.deepcopy(request); matching["source_snapshot"] = []
            compare(artifact, matching, True)
            malformed = copy.deepcopy(artifact); malformed["programs"][0]["operations"][0]["input"] = 99
            native(encoded(malformed), accepted=False)
            invalid_arm = json.loads(outputs[0].read_bytes())
            for program in invalid_arm["programs"]:
                for op in program["operations"]:
                    if op["tag"] == "classical_branch":
                        op["else_ops"].append(dict(tag="discard", input=4294967295))
            native(encoded(invalid_arm), accepted=False)
            for data in [b"", b"QLV0" + packet(encoded(artifact))[4:],
                         packet(encoded(artifact)) + b"x", packet(encoded(artifact))[:-1],
                         b"QLV1" + (16777217).to_bytes(4, "little") + bytes(4),
                         packet(b'{"version":2,' + encoded(artifact)[1:]),
                         packet(encoded(artifact).replace(b'"version":2', b'"version":02'))]:
                run([kernel, "--qirf-native", VERSION], 1, data)

            # Both selection mechanisms use the same native verifier and execution view.
            # Independent mathematical oracles remain separate tests.
            cases = [case for case in check_manifest(ROOT / "corpus")["cases"]
                     if case["qubits"] <= 4]
            for case in cases:
                source = current_project(case, ROOT / "corpus")
                base = json.loads(run([binary, "run", source, "--format=json"]))
                explicit = json.loads(run([binary, "run", source, "--format=json", selected]))
                assert base == explicit, case["id"]
        status = "passed"
    except BaseException:
        status = "failed"
        raise
    finally:
        if args.record:
            args.record.mkdir(parents=True, exist_ok=True)
            (args.record / "native-validation.json").write_text(json.dumps(dict(
                status=status, scope="single native acceptance through both selection mechanisms; not S05 or source preservation",
                binaries={str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in [binary, kernel]},
                observations=observations), indent=2) + "\n")
    print(f"VM-28: {len(observations)} process checks, {len(cases)} small corpus clients; native acceptance required")


if __name__ == "__main__":
    main()
