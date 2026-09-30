#!/usr/bin/env python3
"""Independent symbolic-path and Fourier checks for the actual native kernel.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
The internal matcher is not an enabled external QFT schema.
"""
import argparse
import cmath
import hashlib
import json
import math
from pathlib import Path
import random
import subprocess
import tempfile

from test_lean_interference import ROOT, literal, execute, h, p, distance

FIXTURE = ROOT / "tests/fixtures/lean_qft"


def template(width):
    word = []
    for j in reversed(range(width)):
        word.append(h(j))
        for k in reversed(range(j)):
            word.append(p([(256 // (2 ** (j - k + 1)), [k, j])]))
    return word


def direct_path(word, width, input_value, choices):
    bits = [(input_value >> i) & 1 for i in range(width)]
    phase = count = 0
    for kind, data in word:
        if kind == "h":
            output = (choices >> count) & 1
            phase += 128 * bits[data] * output
            bits[data] = output
            count += 1
        else:
            for ticks, axes in data:
                if all(bits[i] for i in axes):
                    phase += ticks
    return bits, phase % 256, count


def symbolic_path(result, width, input_value, choices):
    values = input_value | (choices << width)
    bits = [(values >> i) & 1 for i in result["wires"]]
    phase = sum(ticks for ticks, axes in result["phases"] if all(values & (1 << i) for i in axes)) % 256
    return bits, phase, result["hadamards"]


def native(cases, log, semantic=False):
    with tempfile.TemporaryDirectory(prefix="qleisli-qft-native-") as directory:
        project = Path(directory)
        (project / "lean-toolchain").write_text((ROOT / "lean-kernel/lean-toolchain").read_text())
        (project / "lakefile.toml").write_text(
            'name = "qft_test"\nversion = "0.0.0"\ndefaultTargets = ["qft-test"]\n'
            '[[require]]\nname = "qleisli_kernel"\npath = ' + json.dumps(str(ROOT / "lean-kernel")) +
            '\n[[lean_exe]]\nname = "qft-test"\nroot = "Main"\n')
        rows = [f"({width}, {literal(word)}, {json.dumps(axes)})" for width, word, axes in cases]
        source = '''import QleisliKernel.Qft
open QleisliKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
def numbers (values : List Nat) : String := String.intercalate "," (values.map toString)
def cases : List (Nat × List Interference.Gate × List Nat) := [
''' + ",\n".join(rows) + ''']
def main : IO Unit := do
  for (width, word, axes) in cases do
    let matched := if Qft.matchCircuit width word axes then "1" else "0"
    match PathSum.compile width word with
    | none => IO.println (matched ++ "#none")
    | some result =>
      let phases := String.intercalate ";" (result.phases.map fun term =>
        toString term.ticks ++ ":" ++ numbers term.axes)
      IO.println (matched ++ "#" ++ toString result.hadamards ++ "#" ++
        numbers result.wires ++ "#" ++ phases)
'''
        if semantic:
            source = source.replace("Qft.matchCircuit", "Qft.matchCompiledCircuit")
        (project / "Main.lean").write_text(source)
        build = subprocess.run(["lake", "build"], cwd=project, capture_output=True, text=True, timeout=180)
        log.append(dict(command=["lake", "build"], cwd="temporary native QFT harness",
                        exit=build.returncode, stdout=build.stdout, stderr=build.stderr))
        assert build.returncode == 0, build.stdout + build.stderr
        binary = project / ".lake/build/bin/qft-test"
        run = subprocess.run([str(binary)], capture_output=True, text=True, timeout=15)
        log.append(dict(command=["qft-test"], exit=run.returncode, stderr=run.stderr,
                        executable_sha256=hashlib.sha256(binary.read_bytes()).hexdigest()))
        assert run.returncode == 0, run.stderr
        outputs = []
        for line in run.stdout.splitlines():
            pieces = line.split("#")
            if pieces[1] == "none":
                outputs.append((pieces[0] == "1", None))
            else:
                phases = []
                for term in pieces[3].split(";") if pieces[3] else []:
                    ticks, axes = term.split(":")
                    phases.append((int(ticks), [int(i) for i in axes.split(",")] if axes else []))
                outputs.append((pieces[0] == "1", dict(hadamards=int(pieces[1]),
                    wires=[int(i) for i in pieces[2].split(",")] if pieces[2] else [], phases=phases)))
        assert len(outputs) == len(cases)
        return outputs


def source_check(binary, log):
    source = FIXTURE / "first_source/main.qli"
    assert hashlib.sha256(source.read_bytes()).hexdigest() == json.loads(
        (FIXTURE / "baseline.json").read_text())["source_sha256"]
    command = [str(binary.resolve()), "run", str(source.parent), "--format=json"]
    run = subprocess.run(command, capture_output=True, text=True, timeout=15)
    log.append(dict(command=command, exit=run.returncode, stdout=run.stdout, stderr=run.stderr))
    assert run.returncode == 0, run.stderr
    assert json.loads(run.stdout)["result"]["distribution"] == [dict(bits=[True, False, False], probability=1)]
    wrong = FIXTURE / "wrong_reversal/main.qli"
    assert hashlib.sha256(wrong.read_bytes()).hexdigest() == json.loads(
        (FIXTURE / "wrong-reversal-baseline.json").read_text())["source_sha256"]
    command = [str(binary.resolve()), "run", str(wrong.parent), "--format=json"]
    run = subprocess.run(command, capture_output=True, text=True, timeout=15)
    log.append(dict(command=command, exit=run.returncode, stdout=run.stdout, stderr=run.stderr))
    assert run.returncode == 0, run.stderr
    actual = {sum(int(bit) << i for i, bit in enumerate(row["bits"])): row["probability"]
              for row in json.loads(run.stdout)["result"]["distribution"]}
    # Independent F† R F |1>, not either source body's circuit expansion.
    reverse = lambda value: int(f"{value:03b}"[::-1], 2)
    expected = {y: abs(sum(cmath.exp(2j * math.pi * (reverse(k) - k * y) / 8)
                           for k in range(8)) / 8) ** 2 for y in range(8)}
    assert all(abs(actual.get(y, 0) - expected[y]) < 1e-12 for y in range(8))
    assert expected[1] < 0.1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-only", type=Path)
    parser.add_argument("--record", type=Path)
    parser.add_argument("--small", action="store_true", help="generate only widths 1–4")
    parser.add_argument("--semantic", action="store_true", help="test the additive symbolic-path matcher")
    args = parser.parse_args()
    log, report = [], {}
    if args.source_only:
        source_check(args.source_only, log)
        report["source_round_trip"] = True
        report["wrong_reversal_outcomes"] = 8
    else:
        upper = 4 if args.small else 8
        cases = [(m, template(m), list(reversed(range(m)))) for m in range(1, upper + 1)]
        expected = [True] * len(cases)
        # Template mutations, all still well-formed primitive circuits except explicit bounds below.
        for width in range(2, upper + 1):
            original, axes = template(width), list(reversed(range(width)))
            wrong_phase = list(original)
            ticks, controls = wrong_phase[1][1][0]
            wrong_phase[1] = p([((256 - ticks) % 256, controls)])
            reordered = [original[1], original[0], *original[2:]]
            for word, output in [(wrong_phase, axes), (reordered, axes), (original[1:], axes),
                                 (original, list(range(width))), (original + [h(0)], axes)]:
                cases.append((width, word, output)); expected.append(False)
        if args.semantic:
            # Equal phase polynomials with changed literal syntax.
            for width in range(2, upper + 1):
                word = template(width)
                ticks, axes = word[1][1][0]
                changed = [word[0], p([(ticks // 2, axes), (ticks // 2, axes)]), *word[2:]]
                cases.append((width, changed, list(reversed(range(width))))); expected.append(True)
            word = template(3)
            word[1], word[2] = word[2], word[1]  # Adjacent diagonal phases commute.
            cases.append((3, word, [2, 1, 0])); expected.append(True)
        invalid_start = len(cases)
        for width, word, axes in [(1, [h(1)], [0]), (1, [p([(256, [0])])], [0]),
                                 (1, [p([(16, [1])])], [0])]:
            cases.append((width, word, axes)); expected.append(False)
        cases += [(0, [], []), (9, [], list(range(9))), (1, [], [0])]
        expected += [False] * 3
        rng = random.Random(2909202602)
        for _ in range(60):
            width = rng.randrange(1, 4)
            word = []
            for _ in range(rng.randrange(1, 12)):
                if rng.randrange(2):
                    word.append(h(rng.randrange(width)))
                else:
                    word.append(p([(rng.randrange(256), sorted(rng.sample(range(width), rng.randrange(width + 1))))
                                   for _ in range(rng.randrange(5))]))
            # Deliberately invalid final layout makes this a path-compiler-only case.
            cases.append((width, word, [])); expected.append(False)
        outputs = native(cases, log, semantic=args.semantic)
        path_checks = phase_checks = 0
        for index, ((width, word, _), (matched, result)) in enumerate(zip(cases, outputs)):
            assert matched == expected[index], index
            if result is None:
                assert invalid_start <= index < invalid_start + 3, index
                continue
            for _ in range(30):
                input_value = rng.randrange(1 << width)
                choices = rng.randrange(1 << result["hadamards"])
                assert symbolic_path(result, width, input_value, choices) == direct_path(word, width, input_value, choices)
                path_checks += 1
            if expected[index]:
                assert result["hadamards"] == width
                assert list(reversed(result["wires"])) == list(range(width, 2 * width))
                assert len(result["phases"]) == width * (width + 1) // 2
                for _ in range(200):
                    x, y = rng.randrange(1 << width), rng.randrange(1 << width)
                    bits, phase, _ = symbolic_path(result, width, x, y)
                    assert list(reversed(bits)) == [(y >> i) & 1 for i in range(width)]
                    assert phase == ((256 >> width) * x * y) % 256
                    phase_checks += 1
        matrix_entries = 0
        max_error = 0.0
        for width in range(1, 4):
            size = 1 << width
            reverse = lambda value: int(f"{value:0{width}b}"[::-1], 2)
            for x in range(size):
                state = execute(template(width), [int(i == x) for i in range(size)], width)
                for y in range(size):
                    error = abs(state[reverse(y)] - cmath.exp(2j * math.pi * x * y / size) / math.sqrt(size))
                    max_error = max(max_error, error); matrix_entries += 1
            for reference in range(3):
                joint = [complex(1 + i + reference * i * i, reference - 2 * i) for i in range(size)]
                state = execute(template(width), joint, width)
                actual = [state[reverse(y)] for y in range(size)]
                oracle = [sum(joint[x] * cmath.exp(2j * math.pi * x * y / size) for x in range(size)) /
                          math.sqrt(size) for y in range(size)]
                max_error = max(max_error, distance(actual, oracle))
        assert max_error < 1e-10, max_error
        report.update(native_cases=len(cases), direct_path_comparisons=path_checks,
                      modular_fourier_comparisons=phase_checks, complex_matrix_entries=matrix_entries,
                      joint_reference_cases=9, max_error=max_error, kernel_dense_dimension=0,
                      largest_dense_oracle_dimension=8)
        report.update(matcher="compiled-symbolic-path" if args.semantic else "literal-template",
                      maximum_generated_fourier_width=upper)
    report["commands"] = log
    report["source_sha256"] = {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in [ROOT / "lean-kernel/QleisliKernel/PathSum.lean", ROOT / "lean-kernel/QleisliKernel/Qft.lean",
                     ROOT / "lean/Qleisli/Qft.lean", Path(__file__).resolve()]}
    if args.record:
        args.record.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k not in {"commands", "source_sha256"}}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
