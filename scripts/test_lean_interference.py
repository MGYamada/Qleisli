#!/usr/bin/env python3
"""Native transformation differential checks against independent complex actions.

Build a temporary test executable importing the actual kernel definitions.
There is no new public checker protocol and numerical results issue no evidence.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import native_harness
import argparse
import cmath
import hashlib
import json
import math
from pathlib import Path
import random
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
FIXTURE = ROOT / "tests/fixtures/lean_interference"


def h(axis):
    return ("h", axis)


def p(terms):
    return ("p", terms)


def literal(word):
    gates = []
    for kind, value in word:
        if kind == "h":
            gates.append(f".hadamard {value}")
        else:
            terms = [f"⟨{json.dumps(axes)}, {ticks}⟩" for ticks, axes in value]
            gates.append(".diagonal [" + ", ".join(terms) + "]")
    return "[" + ", ".join(gates) + "]"


def parse(line):
    if not line:
        return []
    result = []
    for gate in line.split("|"):
        kind, value = gate.split("=", 1)
        if kind == "h":
            result.append(h(int(value)))
        else:
            assert kind == "p"
            terms = []
            for term in value.split(";") if value else []:
                ticks, axes = term.split(":", 1)
                terms.append((int(ticks), [int(x) for x in axes.split(",")] if axes else []))
            result.append(p(terms))
    return result


def execute(word, initial, width):
    """Direct forward state vector updates, not the kernel's function semantics."""
    state = list(initial)
    for kind, value in word:
        if kind == "h":
            mask = 1 << value
            assert value < width
            result = [0j] * len(state)
            for index, amplitude in enumerate(state):
                low = index & ~mask
                result[low] += amplitude / math.sqrt(2)
                result[low | mask] += (-1 if index & mask else 1) * amplitude / math.sqrt(2)
            state = result
        else:
            for index in range(len(state)):
                # Literal operations, no collection or normalization of phase terms.
                for ticks, axes in value:
                    if all(index & (1 << axis) for axis in axes):
                        state[index] *= cmath.exp(2j * math.pi * ticks / 256)
    return state


def distance(left, right):
    return max(abs(a - b) for a, b in zip(left, right))


def cases():
    result = [(1, []), (1, [h(0), h(0)]), (2, [h(0), h(1)]),
              (2, [h(0), h(1), h(1), h(0)])]
    for ticks in range(256):
        result.append((2, [h(0), h(1), p([(ticks, [0, 1]), (17, []), (239, [])]),
                           h(1), h(1), p([(ticks, [0]), (256 - ticks, [0])]), h(0)]))
    rng = random.Random(29092026)
    for _ in range(160):
        width = rng.randrange(1, 4)
        word = []
        for _ in range(rng.randrange(1, 30)):
            if rng.randrange(2):
                axis = rng.randrange(width)
                word.extend([h(axis)] * rng.randrange(1, 4))
            else:
                terms = [(rng.randrange(256), sorted(rng.sample(range(width), rng.randrange(width + 1))))
                         for _ in range(rng.randrange(6))]
                word.append(p(terms))
        result.append((width, word))
    return result


def native_normalize(words, log):
    with tempfile.TemporaryDirectory(prefix="qleisli-interference-native-") as directory:
        project = Path(directory)
        (project / "Main.lean").write_text('''import QleisliKernel.Interference
open QleisliKernel.Interference
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
def encode : Gate → String
  | .hadamard axis => "h=" ++ toString axis
  | .diagonal terms => "p=" ++ String.intercalate ";" (terms.map fun term =>
      toString term.ticks ++ ":" ++ String.intercalate "," (term.axes.map toString))
def cases : List (List Gate) := [
''' + ",\n".join(literal(word) for word in words) + ''']
def main : IO Unit := do
  for word in cases do
    IO.println (String.intercalate "|" ((normalize word).map encode))
''')
        binary = native_harness.build(project, log)
        run = subprocess.run([str(binary)], capture_output=True, text=True, timeout=15)
        log.append(dict(command=["interference-test"], exit=run.returncode,
                        executable_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(), stderr=run.stderr))
        assert run.returncode == 0, run.stderr
        output = [parse(line) for line in run.stdout.splitlines()]
        assert len(output) == len(words), (len(output), len(words))
        return output


def source_check(binary, log):
    for directory, record, width in [("first_source", "baseline.json", 1),
                                     ("reference_client", "reference-baseline.json", 2),
                                     ("wrong_order", "wrong-order-baseline.json", 1)]:
        baseline = json.loads((FIXTURE / record).read_text())
        source = FIXTURE / directory / "main.qli"
        assert hashlib.sha256(source.read_bytes()).hexdigest() == baseline["source_sha256"]
        command = [str(binary), "run", str(source.parent), "--format=json"]
        run = subprocess.run(command, capture_output=True, text=True, timeout=15)
        log.append(dict(command=command, exit=run.returncode, stdout=run.stdout, stderr=run.stderr))
        assert run.returncode == 0, run.stderr
        distribution = json.loads(run.stdout)["result"]["distribution"]
        assert {tuple(row["bits"]) for row in distribution} == {
            tuple(bool(index & (1 << axis)) for axis in range(width)) for index in range(1 << width)}
        if directory == "wrong_order":
            expected = {(False,): (2 + math.sqrt(2)) / 4, (True,): (2 - math.sqrt(2)) / 4}
            assert all(abs(row["probability"] - expected[tuple(row["bits"])]) < 1e-12
                       for row in distribution)
            assert all(abs(row["probability"] - 0.5) > 0.3 for row in distribution)
        else:
            assert all(abs(row["probability"] - 1 / (1 << width)) < 1e-12 for row in distribution)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-only", type=Path)
    parser.add_argument("--record", type=Path)
    args = parser.parse_args()
    log = []
    report = {}
    if args.source_only:
        source_check(args.source_only.resolve(), log)
        report["source_outcomes"] = 6
        report["type_correct_wrong_source_outcomes"] = 2
    else:
        small = cases()
        large = [[h(15)] * 4096, [h(1000000), h(1000000)]]
        actual = native_normalize([word for _, word in small] + large, log)
        assert actual[-2:] == [[], []]
        comparisons = 0
        max_error = 0.0
        for (width, word), normalized in zip(small, actual):
            for ref in range(3):
                # Nonfactorizing input/reference amplitudes. No normalization is needed
                # for this linear-map equality, and comparison retains global phase.
                initial = [complex(1 + i + ref * i * i, ref - 2 * i) for i in range(1 << width)]
                max_error = max(max_error, distance(execute(word, initial, width),
                                                    execute(normalized, initial, width)))
                comparisons += 1
        assert max_error < 1e-10, max_error
        # Witness wrong simplifications that a probability-only oracle would miss.
        faults = [([h(0), p([(32, [0])]), h(0)], [p([(32, [0])])]),
                  ([h(0), h(1)], []), ([p([(128, [])])], []),
                  ([h(0), p([(16, [0])])], [p([(16, [0])]), h(0)])]
        for correct, wrong in faults:
            assert distance(execute(correct, [1, 2j, 3, 4j], 2),
                            execute(wrong, [1, 2j, 3, 4j], 2)) > 0.1
        report.update(native_words=len(actual), joint_amplitude_comparisons=comparisons,
                      deliberate_semantic_faults=len(faults), max_error=max_error,
                      largest_dense_oracle_dimension=8, kernel_dense_dimension=0)
    report["commands"] = log
    report["source_sha256"] = {
        str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in [ROOT / "lean-kernel/QleisliKernel/Interference.lean",
                     ROOT / "lean/Qleisli/Interference.lean", Path(__file__).resolve()]
    }
    if args.record:
        args.record.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k != "commands"}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
