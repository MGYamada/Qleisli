#!/usr/bin/env python3
"""VM-28 small-system native/CLI comparisons and adversarial input binding.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "tests/fixtures/authoring_sessions/dual-v028/attempt-02"
FINITE = ROOT / "tests/fixtures/verification_v022/finite"


def encoded(value):
    return json.dumps(value, separators=(",", ":")).encode()


def packet(artifact, request=None):
    return b"QLV1" + len(artifact).to_bytes(4, "little") + len(request or b"").to_bytes(4, "little") + artifact + (request or b"")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, default=ROOT / "target/debug/qleisli")
    parser.add_argument("--kernel", type=Path, default=ROOT / "lean-kernel/.lake/build/bin/qleisli-kernel")
    parser.add_argument("--record", type=Path)
    args = parser.parse_args()
    binary, kernel = args.binary.resolve(), args.kernel.resolve()
    observations = []

    def run(command, expected=0, data=None):
        result = subprocess.run(list(map(str, command)), input=data, capture_output=True, timeout=70, cwd=ROOT)
        row = dict(command=list(map(str, command)), exit_code=result.returncode,
                   stdout=result.stdout.decode(errors="replace"), stderr=result.stderr.decode(errors="replace"))
        if data is not None:
            row["input_sha256"] = hashlib.sha256(data).hexdigest()
        observations.append(row)
        assert (result.returncode == 0) == (expected == 0), row
        return result.stdout

    def native(artifact, request=None, accepted=True):
        data = packet(artifact, request)
        result = run([kernel, "--qirf-dual"], 0 if accepted else 1, data)
        lines = result.decode().splitlines()
        assert lines[:2] == ["qleisli.qirf-dual 1", "accepted" if accepted else "error"], result
        if accepted:
            assert len(lines) == 4 and 0 <= int(lines[2]) <= 10000000
            assert lines[3] == ("1" if request is not None else "0")

    try:
        with tempfile.TemporaryDirectory(prefix="qleisli-dual-") as directory:
            directory = Path(directory)
            selected = f"--lean-kernel={kernel}"
            for command, extra in [("check", []), ("run", []), ("sample", ["--shots=64", "--seed=7"])]:
                base = json.loads(run([binary, command, SOURCE, "--format=json", *extra]))
                dual = json.loads(run([binary, command, SOURCE, "--format=json", *extra, selected]))
                assert base == dual, (command, base, dual)
            distribution = json.loads(run([binary, "run", SOURCE, "--format=json", selected]))["result"]["distribution"]
            assert {tuple(row["bits"]) for row in distribution} == {(False, False), (True, True)}
            assert all(abs(row["probability"] - 0.5) < 1e-12 for row in distribution)
            run([binary, "check", SOURCE, selected])  # text and JSON share the gate
            outputs = [directory / "rust.qirf", directory / "dual.qirf"]
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
                run([kernel, "--qirf-dual"], 1, data)

            # Existing small source corpus, numerical results compared exactly
            # to the unchanged Rust path; mathematical oracles remain separate.
            cases = [case for case in json.loads((ROOT / "corpus/manifest.json").read_text())["cases"]
                     if case["qubits"] <= 4]
            for case in cases:
                source = ROOT / "corpus" / case["project"]
                base = json.loads(run([binary, "run", source, "--format=json"]))
                dual = json.loads(run([binary, "run", source, "--format=json", selected]))
                assert base == dual, case["id"]
        status = "passed"
    except BaseException:
        status = "failed"
        raise
    finally:
        if args.record:
            args.record.mkdir(parents=True, exist_ok=True)
            (args.record / "dual-validation.json").write_text(json.dumps(dict(
                status=status, scope="small QIRF/ordinary CLI dual gate; not S05 or source preservation",
                binaries={str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in [binary, kernel]},
                observations=observations), indent=2) + "\n")
    print(f"VM-28: {len(observations)} process checks, {len(cases)} small corpus clients; both gates required")


if __name__ == "__main__":
    main()
