#!/usr/bin/env python3
"""Independent native tests for the bounded Lean phase-DAG composition slice.

Only the checker is under test; the test oracle expands SMALL generated words.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import argparse
import cmath
import json
from pathlib import Path
import random
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
HEADER = "qleisli.phase-dag 1 phase256-dag-v1\n"
IDENTITY = (0, 0, 0)
BINARY = ROOT / "lean-kernel/.lake/build/bin/qleisli-kernel"


def oracle(word):
    """Two basis trajectories, independent of summary composition and DAG caches."""
    values = []
    for original in [0, 1]:
        bit, phase = original, 0
        for gate in word:
            if gate == "x":
                bit ^= 1
            elif bit:
                phase = (phase + int(gate[1:])) % 256
        values.append((bit, phase))
    assert values[0][0] != values[1][0]
    return values[0][0], values[0][1], values[1][1]


def complex_oracle(word, result):
    """Separately evolve complex amplitude columns, retaining their global phase."""
    for original in [0, 1]:
        state = [complex(original == 0), complex(original == 1)]
        for gate in word:
            if gate == "x":
                state.reverse()
            else:
                state[1] *= cmath.exp(2j * cmath.pi * int(gate[1:]) / 256)
        expected = [0j, 0j]
        expected[original ^ result[0]] = cmath.exp(2j * cmath.pi * result[original + 1] / 256)
        assert all(abs(a - b) < 2e-11 for a, b in zip(state, expected))


def definition(body, claim=IDENTITY, shape="Bit"):
    return f"{shape} {' '.join(map(str, claim))} {body}"


def artifact(nodes, entry=None):
    if entry is None:
        entry = len(nodes) - 1
    return f"{HEADER}entry {entry}\nnodes {len(nodes)}\n" + "\n".join(nodes) + "\n"


def request(claim=IDENTITY, shape="Bit"):
    return f"{HEADER}{shape}\nexpect {' '.join(map(str, claim))}\n"


def no_duplicates(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate result key {key}")
        result[key] = value
    return result


class HierarchyTests(unittest.TestCase):
    decisions = 0

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="qleisli-hierarchy-")
        self.addCleanup(self.temp.cleanup)
        self.program = Path(self.temp.name) / "program.qhd"
        self.required = Path(self.temp.name) / "required.qhr"

    def invoke(self, program, required, accepted, code=None, stage="verification"):
        self.program.write_bytes(program.encode() if isinstance(program, str) else program)
        self.required.write_bytes(required.encode() if isinstance(required, str) else required)
        result = subprocess.run([str(BINARY), "--phase-dag", str(self.program), str(self.required)],
                                capture_output=True, timeout=5, check=False)
        type(self).decisions += 1
        self.assertEqual(result.stderr, b"")
        self.assertEqual(result.returncode, 0 if accepted else 1)
        data = json.loads(result.stdout, object_pairs_hook=no_duplicates)
        self.assertEqual(set(data), {"format", "version", "profile", "accepted", "code", "stage", "node", "stats"})
        self.assertEqual(data["format"], "qleisli.kernel-result")
        self.assertEqual(data["version"], 1)
        self.assertEqual(data["profile"], "phase256-dag-v1")
        self.assertIs(data["accepted"], accepted)
        self.assertEqual(data["stage"], stage)
        self.assertEqual(data["code"], code or ("accepted" if accepted else "contract"))
        if accepted:
            self.assertIsNone(data["node"])
            self.assertEqual(set(data["stats"]), {"nodes", "references", "work_units", "depth", "expanded_gates", "dense_dimension"})
            self.assertEqual(data["stats"]["dense_dimension"], 0)
        else:
            self.assertIsNone(data["stats"])
            if stage == "verification":
                self.assertIs(type(data["node"]), int)
            else:
                self.assertIsNone(data["node"])
        return data

    def test_immutable_first_artifacts(self):
        root = ROOT / "tests/fixtures/lean_hierarchy"
        import hashlib
        baseline = json.loads((root / "baseline.json").read_text())
        for name, digest in baseline["sources"].items():
            self.assertEqual(hashlib.sha256((root / name).read_bytes()).hexdigest(), digest)
        data = self.invoke((root / "shared.qhd").read_bytes(), (root / "identity.qhr").read_bytes(), True)
        self.assertEqual(data["stats"], dict(nodes=3, references=2, work_units=47,
                                             depth=3, expanded_gates=4096**2, dense_dimension=0))

    def test_small_shared_dags_against_expanded_and_complex_oracles(self):
        rng = random.Random(0xCD3)
        for case in range(100):
            with self.subTest(case=case):
                nodes, expanded = [], []
                for index in range(6):
                    tag = rng.choice(["leaf"] if index == 0 else ["leaf", "call", "repeat", "sequence"])
                    if tag == "leaf":
                        word = [rng.choice(["x", "p0", "p1", "p16", "p32", "p255"]) for _ in range(rng.randrange(5))]
                        body = f"leaf {len(word)}" + (" " + " ".join(word) if word else "")
                    elif tag == "call":
                        child = rng.randrange(index)
                        word = expanded[child]
                        body = f"call {child} 1 0 1 0"
                    elif tag == "repeat":
                        count, child = rng.randrange(5), rng.randrange(index)
                        word = expanded[child] * count
                        body = f"repeat {count} {child}"
                    else:
                        left, right = rng.randrange(index), rng.randrange(index)
                        word = expanded[left] + expanded[right]
                        body = f"sequence 2 {left} {right}"
                    self.assertLessEqual(len(word), 4096)
                    meaning = oracle(word)
                    complex_oracle(word, meaning)
                    nodes.append(definition(body, meaning))
                    expanded.append(word)
                # All definitions are reachable, including zero-repeat premises.
                root_word = sum(expanded, [])
                meaning = oracle(root_word)
                complex_oracle(root_word, meaning)
                nodes.append(definition("sequence 6 0 1 2 3 4 5", meaning))
                result = self.invoke(artifact(nodes), request(meaning), True)
                self.assertEqual(result["stats"]["expanded_gates"], len(root_word))
                self.assertEqual(result["stats"]["nodes"], 7)
                wrong = (meaning[0], (meaning[1] + 1) % 256, meaning[2])
                self.invoke(artifact(nodes), request(wrong), False)
                # A false intermediate receipt rejects even if the root is unchanged.
                changed = nodes[:]
                parts = changed[0].split(" ")
                parts[2] = str((int(parts[2]) + 1) % 256)
                changed[0] = " ".join(parts)
                rejected = self.invoke(artifact(changed), request(meaning), False)
                self.assertEqual(rejected["node"], 0)

    def test_global_phase_and_all_dyadic_angles(self):
        for tick in range(256):
            word = ["x", f"p{tick}", "x", f"p{tick}"]
            meaning = (0, tick, tick)
            complex_oracle(word, meaning)
            self.invoke(artifact([definition("leaf 4 " + " ".join(word), meaning),
                                  definition("call 0 1 0 1 0", meaning)]), request(meaning), True)
        self.invoke(artifact([definition("leaf 4 x p16 x p16", (0, 16, 16))]), request(), False)

    def test_body_count_dependency_and_request_mutations(self):
        original = [definition("leaf 1 p16", (0, 0, 16)), definition("repeat 2 0", (0, 0, 32))]
        self.invoke(artifact(original), request((0, 0, 32)), True)
        self.invoke(artifact([original[0], definition("repeat 3 0", (0, 0, 32))]), request((0, 0, 32)), False)
        self.invoke(artifact([definition("leaf 1 p17", (0, 0, 16)), original[1]]), request((0, 0, 32)), False)
        chain = [original[0], original[1], definition("call 1 1 0 1 0", (0, 0, 32)),
                 definition("sequence 2 1 2", (0, 0, 64))]
        self.invoke(artifact(chain), request((0, 0, 64)), True)
        chain[2] = definition("call 0 1 0 1 0", (0, 0, 32))
        self.invoke(artifact(chain), request((0, 0, 64)), False)
        self.invoke(artifact(original), request((0, 0, 32), "Bits1"), False, "invalid_ir")

    def test_closed_power_against_direct_boundary_execution(self):
        for word in [["p1"], ["x", "p17"], ["p255", "x", "p16"]]:
            leaf = definition(f"leaf {len(word)} " + " ".join(word), oracle(word))
            for count in [0, 1, 2, 255, 256, 4095, 4096]:
                # The oracle deliberately performs every gate, with no power formula.
                meaning = oracle(word * count)
                nodes = [leaf, definition(f"repeat {count} 0", meaning)]
                result = self.invoke(artifact(nodes), request(meaning), True)
                self.assertEqual(result["stats"]["expanded_gates"], len(word) * count)
                self.assertEqual(result["stats"]["work_units"], 23 + 3 * len(word))
        self.invoke(artifact([definition("leaf 0"), definition("repeat 4097 0")]),
                    request(), False, "limit", "artifact")

    def test_zero_repeat_checks_body_and_retains_reachability(self):
        self.invoke(artifact([definition("leaf 1 x", (1, 0, 0)), definition("repeat 0 0")]), request(), True)
        for nodes in [
            [definition("sequence 0"), definition("repeat 0 0")],
            [definition("leaf 1 x", (1, 0, 0), "Unit"), definition("repeat 0 0", shape="Unit")],
            [definition("repeat 0 0")],
            [definition("repeat 0 99")],
        ]:
            shape = "Unit" if nodes[0].startswith("Unit") else "Bit"
            self.invoke(artifact(nodes), request(shape=shape), False, "invalid_ir")
        self.invoke(artifact([definition("leaf 1 x"), definition("repeat 0 0")]), request(), False)

    def test_exact_shape_and_zero_width_owner_ports(self):
        for shape in ["Unit", "Bits0", "Bit", "Bits1"]:
            nodes = [definition("leaf 0", shape=shape), definition("call 0 1 0 1 0", shape=shape)]
            self.invoke(artifact(nodes), request(shape=shape), True)
            for call in ["call 0 0 0", "call 0 2 0 0 1 0", "call 0 1 1 1 0", "call 0 1 0 0"]:
                self.invoke(artifact([nodes[0], definition(call, shape=shape)]), request(shape=shape), False, "invalid_ir")
        for first, second in [("Unit", "Bits0"), ("Bit", "Bits1")]:
            nodes = [definition("leaf 0", shape=first), definition("call 0 1 0 1 0", shape=second)]
            self.invoke(artifact(nodes), request(shape=second), False, "invalid_ir")

    def test_dag_cycles_forward_references_and_unreachable_entries(self):
        for nodes in [
            [definition("call 0 1 0 1 0")],
            [definition("call 1 1 0 1 0"), definition("call 0 1 0 1 0")],
            [definition("call 1 1 0 1 0"), definition("leaf 0")],
            [definition("leaf 0"), definition("leaf 0")],
        ]:
            self.invoke(artifact(nodes), request(), False, "invalid_ir")
        self.invoke(artifact([definition("leaf 0")], entry=1), request(), False, "invalid_ir")

    def test_large_shared_work_and_depth_boundary(self):
        nodes = [definition("leaf 1 p1", (0, 0, 1))]
        for index in range(1, 64):
            nodes.append(definition(f"repeat 4096 {index - 1}"))
        result = self.invoke(artifact(nodes), request(), True)
        self.assertEqual(result["stats"]["nodes"], 64)
        self.assertEqual(result["stats"]["references"], 63)
        self.assertEqual(result["stats"]["depth"], 64)
        self.assertEqual(result["stats"]["expanded_gates"], 4096**63)
        self.assertLess(result["stats"]["work_units"], 1400)
        nodes.append(definition("repeat 4096 63"))
        self.invoke(artifact(nodes), request(), False, "limit")

    def test_node_reference_and_primitive_boundaries(self):
        nodes = [definition("leaf 0") for _ in range(255)]
        nodes.append(definition("sequence 255 " + " ".join(map(str, range(255)))))
        self.assertEqual(self.invoke(artifact(nodes), request(), True)["stats"]["nodes"], 256)
        self.invoke(artifact(nodes + [definition("call 255 1 0 1 0")]), request(), False, "limit", "artifact")
        self.invoke(artifact([definition("leaf 4096 " + " ".join(["x"] * 4096))]), request(), True)
        self.invoke(artifact([definition("leaf 4097 " + " ".join(["x"] * 4097))]), request(), False, "limit", "artifact")
        nodes = [definition("leaf 0"), definition("sequence 4096 " + " ".join(["0"] * 4096))]
        self.invoke(artifact(nodes), request(), True)
        nodes.append(definition("call 1 1 0 1 0"))
        self.invoke(artifact(nodes), request(), False, "limit")

    def test_strict_transport_and_no_schema_shortcuts(self):
        original = artifact([definition("leaf 1 p16", (0, 0, 16))])
        required = request((0, 0, 16))
        for bad in [original.replace("phase256-dag-v1", "qpe-dyadic8-v1"),
                    original.replace("dag 1", "dag 2"), original.replace("leaf 1 p16", "qft 1"),
                    original.replace("p16", "p016"), original.replace("p16", "p-1"),
                    original.replace("p16", "p1.6"), original.replace("Bit", "Bits8"),
                    original.replace("nodes 1", "nodes 01"), original.replace("nodes 1", "nodes 2"),
                    original.replace(" ", "  "), original.replace("\n", "\r\n"),
                    original + "\n", original[:-1], original + "\0", original + "\u2028",
                    b"\xff"]:
            self.invoke(bad, required, False, "syntax", "artifact")
        self.invoke(original.replace("p16", "p256"), required, False, "limit", "artifact")
        self.invoke(original, required.replace("expect", "claim"), False, "syntax", "requirement")
        self.invoke(" " * 65537, required, False, "limit", "artifact")
        self.invoke(original, " " * 65537, False, "limit", "requirement")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("binary", nargs="?", type=Path, default=BINARY)
    args = parser.parse_args()
    BINARY = args.binary.resolve()
    result = unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(HierarchyTests))
    print(f"Native DAG decisions: {HierarchyTests.decisions}")
    raise SystemExit(not result.wasSuccessful())
