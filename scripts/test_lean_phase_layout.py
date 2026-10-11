#!/usr/bin/env python3
"""Independent native typed phase/layout graph oracles and rejection tests.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
Complex amplitudes are an external test oracle, never acceptance evidence.
"""
import argparse
import cmath
import copy
import hashlib
import itertools
import json
import math
from pathlib import Path
from current_source_fixtures import current_source_fixture
import random
import subprocess
import tempfile
import unittest

from test_lean_layout import ROOT, layout, unique, encode as encode_layout
from test_lean_layout_dag import (leaf as wire_leaf, call as wire_call, then as wire_then,
                                  encode as encode_wiring, apply_ports)

BINARY = ROOT / "lean-kernel/.lake/build/bin/qleisli-kernel"


def normalize(terms):
    """Independent producer uses a dictionary, not Lean's insertion algorithm."""
    coefficients = {}
    for ticks, axes in terms:
        key = tuple(sorted(axes))
        coefficients[key] = (coefficients.get(key, 0) + ticks) % 256
    return [(coefficients[key], list(key)) for key in
            sorted(coefficients, key=lambda axes: sum(1 << a for a in axes)) if coefficients[key]]


def remap(terms, axes):
    return normalize([(ticks, [axes[i] for i in controls]) for ticks, controls in terms])


def leaf(value, phases):
    return dict(wiring=wire_leaf(value), source=phases, claim=normalize(phases))


def call(nodes, child, before=None, after=None):
    wiring = wire_call([node["wiring"] for node in nodes], child, before, after)
    return dict(wiring=wiring, source=[], claim=remap(nodes[child]["claim"], wiring["before"]["axes"]))


def then(nodes, first, second):
    wiring = wire_then([node["wiring"] for node in nodes], first, second)
    phases = nodes[first]["claim"] + remap(nodes[second]["claim"], nodes[first]["wiring"]["result"]["axes"])
    return dict(wiring=wiring, source=[], claim=normalize(phases))


def polynomial(tag, terms):
    return "\n".join([f"{tag} {len(terms)}"] +
                     [" ".join(["term", str(t), str(len(a)), *map(str, a)]) for t, a in terms]) + "\n"


def encode(nodes, entry=None):
    result = ("qleisli.phase-layout 1 typed-phase256-dag-v1\n"
              f"entry {len(nodes) - 1 if entry is None else entry}\ndefinitions {len(nodes)}\n")
    for node in nodes:
        result += "\n".join(encode_wiring([node["wiring"]], 0).splitlines()[3:]) + "\n"
        result += polynomial("source_phases", node["source"]) + polynomial("claim_phases", node["claim"])
    return result


def requirement(node):
    return ("qleisli.phase-layout-request 1 typed-phase256-dag-v1\n" +
            encode_layout(node["wiring"]["result"], True).split("\n", 1)[1] +
            polynomial("expect_phases", node["claim"]))


def execute(nodes, entry, state):
    """Expand small graphs and execute literal conditions one at a time, without claims."""
    node = nodes[entry]
    wiring = node["wiring"]
    owners, bits, phase = state
    if wiring["kind"] == "leaf":
        for ticks, controls in node["source"]:
            if all(bits[i] for i in controls):
                phase = (phase + ticks) % 256
        owners, bits = apply_ports(wiring["result"], (owners, bits))
        return owners, bits, phase
    if wiring["kind"] == "call":
        owners, bits = apply_ports(wiring["before"], (owners, bits))
        owners, bits, phase = execute(nodes, wiring["child"], (owners, bits, phase))
        owners, bits = apply_ports(wiring["after"], (owners, bits))
        return owners, bits, phase
    return execute(nodes, wiring["second"], execute(nodes, wiring["first"], state))


def oracle(nodes):
    final = nodes[-1]
    wiring = final["wiring"]["result"]
    n = len(wiring["axes"])
    assert n <= 6
    owners = tuple(range(len(wiring["owners"])))
    for bits in itertools.product([0, 1], repeat=n):
        for initial in [0, 17, 255]:
            moved_owners, moved_bits, phase = execute(nodes, len(nodes) - 1, (owners, bits, initial))
            expected_phase = (initial + sum(t for t, axes in final["claim"] if all(bits[i] for i in axes))) % 256
            assert (moved_owners, moved_bits) == apply_ports(wiring, (owners, bits))
            assert phase == expected_phase
            # Joint coefficients need not factor by bit, owner or reference.
            for ref in range(3):
                amplitude = complex(1 + sum((i + 2) * b for i, b in enumerate(bits)) + ref,
                                    2 * sum(bits) - ref)
                actual = amplitude * cmath.exp(2j * math.pi * phase / 256)
                expected = amplitude * cmath.exp(2j * math.pi * expected_phase / 256)
                assert abs(actual - expected) < 1e-12
                assert abs(abs(actual) - abs(amplitude)) < 1e-12


def check_source(binary):
    """Separate finite source experiment; no source-to-new-IR proof is implied."""
    source = current_source_fixture(ROOT / "tests/fixtures/lean_phase_layout/interference_client")
    result = subprocess.run([str(binary), "run", str(source), "--format=json"],
                            capture_output=True, text=True, timeout=15, check=False)
    assert result.returncode == 0, result
    data = json.loads(result.stdout, object_pairs_hook=unique)
    assert data["outcome"] == "ok" and data["diagnostics"] == []
    actual = {tuple(row["bits"]): row["probability"] for row in data["result"]["distribution"]}
    labels = list(itertools.product([0, 1], repeat=2))
    # H⊗H, then phase π/4(x0+x1+x0*x1), then H⊗H.
    expected = {y: abs(sum(((-1) ** sum(a * b for a, b in zip(x, y))) *
                          cmath.exp(1j * math.pi * (x[0] + x[1] + x[0] * x[1]) / 4)
                          for x in labels) / 4) ** 2 for y in labels}
    assert set(actual) == set(expected)
    assert all(abs(actual[y] - expected[y]) < 1e-12 for y in labels), (actual, expected)
    print("Finite source interference: all 4 outcomes match the independent Fourier formula.")
    return 0


class PhaseLayoutTests(unittest.TestCase):
    decisions = 0

    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix="qleisli-phase-layout-")
        self.addCleanup(self.directory.cleanup)
        self.artifact = Path(self.directory.name) / "artifact.qhd"
        self.request = Path(self.directory.name) / "request.qhr"

    def invoke(self, nodes, required=None, accepted=True, code=None, stage="verification", entry=None):
        program = encode(nodes, entry) if isinstance(nodes, list) else nodes
        if required is None:
            required = requirement(nodes[-1])
        elif isinstance(required, dict):
            required = requirement(required)
        self.artifact.write_bytes(program.encode() if isinstance(program, str) else program)
        self.request.write_bytes(required.encode() if isinstance(required, str) else required)
        result = subprocess.run([str(BINARY), "--phase-layout", str(self.artifact), str(self.request)],
                                capture_output=True, timeout=5, check=False)
        type(self).decisions += 1
        self.assertEqual(result.returncode, 0 if accepted else 1, result)
        self.assertEqual(result.stderr, b"")
        self.assertEqual(result.stdout.count(b"\n"), 1)
        data = json.loads(result.stdout, object_pairs_hook=unique)
        self.assertEqual(set(data), {"format", "version", "profile", "accepted", "code", "stage", "node", "stats"})
        self.assertEqual((data["format"], data["version"], data["profile"]),
                         ("qleisli.kernel-result", 1, "typed-phase256-dag-v1"))
        self.assertIs(data["accepted"], accepted)
        self.assertEqual(data["code"], code or ("accepted" if accepted else "invalid_ir"))
        self.assertEqual(data["stage"], stage)
        if accepted:
            self.assertIsNone(data["node"])
            self.assertEqual(set(data["stats"]), {"nodes", "references", "work_units", "phase_work_units",
                                                   "depth", "expanded_layouts", "expanded_phase_terms",
                                                   "terms", "dense_dimension"})
            self.assertEqual(data["stats"]["dense_dimension"], 0)
            self.assertLessEqual(data["stats"]["work_units"], 2000000)
        else:
            self.assertIsNone(data["stats"])
        return data

    def test_preserved_shared_source(self):
        path = ROOT / "tests/fixtures/lean_phase_layout"
        baseline = json.loads((path / "baseline.json").read_text())
        for relative, digest in {**baseline["sha256"], **baseline["initial_artifact_sha256"]}.items():
            self.assertEqual(hashlib.sha256((ROOT / relative).read_bytes()).hexdigest(), digest)
        client = json.loads((path / "interference-source.json").read_text())
        self.assertEqual(hashlib.sha256((path / "interference_client/main.qli").read_bytes()).hexdigest(),
                         client["sha256"])
        data = self.invoke((path / "shared.qhd").read_text(), (path / "expected.qhr").read_text())
        self.assertEqual(data["stats"]["terms"], 3)
        self.assertEqual(data["stats"]["nodes"], 5)
        self.assertEqual(data["stats"]["expanded_phase_terms"], 3)

    def test_all_dyadic_angles_and_global_phase(self):
        for ticks in range(256):
            # Condition [0,1] entangles |++>; [] retains the scalar phase.
            nodes = [leaf(layout(["Bit", "Bit", "Unit"]), [(ticks, [0, 1]), (17, [])])]
            oracle(nodes)
            self.invoke(nodes)
        good = [leaf(layout(["Bits0"]), [(1, [])])]
        self.invoke(good)
        for wrong in [[], [(255, [])]]:
            required = copy.deepcopy(good[0]); required["claim"] = wrong
            self.invoke(good, required, False, "contract")

    def test_shared_graph_oracle_noncommuting_layouts(self):
        rng = random.Random(2026092902)
        for n in range(1, 6):
            types = ["Bit"] * n + ["Unit", "Bits0"]
            for _ in range(12):
                def permutation():
                    p = rng.sample(range(n), n)
                    return layout(types, p + [n, n + 1], p)
                def phases():
                    return [(rng.randrange(256), sorted(rng.sample(range(n), rng.randrange(n + 1))))
                            for _ in range(7)]
                nodes = [leaf(permutation(), phases()), leaf(permutation(), phases())]
                nodes.append(call(nodes, 0, permutation(), permutation()))
                nodes.append(then(nodes, 1, 2))
                nodes.append(then(nodes, 3, 2))
                oracle(nodes)
                self.invoke(nodes)

    def test_leaf_and_receipt_phase_tampering(self):
        value = layout(["Bit", "Bit"])
        good = [leaf(value, [(16, [0]), (7, []), (3, [0, 1])])]
        for mutation in [[(16, [1]), (7, []), (3, [0, 1])],
                         [(16, [0]), (3, [0, 1])], [(240, [0]), (7, []), (3, [0, 1])]]:
            bad = [leaf(value, mutation)]
            oracle(bad)
            self.invoke(bad)
            self.invoke(bad, good[0], False, "contract")
        stale = copy.deepcopy(good); stale[0]["source"] = [(15, [0])]
        self.invoke(stale, accepted=False, code="contract")
        stale = copy.deepcopy(good); stale[0]["claim"] = []
        self.invoke(stale, accepted=False, code="contract")

    def test_call_phase_axis_and_order_binding(self):
        identity = layout(["Bit", "Bit", "Unit"])
        swap = layout(["Bit", "Bit", "Unit"], [1, 0, 2], [1, 0])
        nodes = [leaf(identity, [(16, [0])])]
        nodes.append(call(nodes, 0, swap, swap))
        self.assertEqual(nodes[-1]["claim"], [(16, [1])])
        oracle(nodes); self.invoke(nodes)
        wrong = copy.deepcopy(nodes)
        wrong[1] = call(wrong, 0)
        self.invoke(wrong)
        self.invoke(wrong, nodes[-1], False, "contract")
        nodes = [leaf(swap, []), leaf(identity, [(1, [0])])]
        nodes.append(then(nodes, 0, 1)); self.invoke(nodes)
        wrong = nodes[:2]; wrong.append(then(wrong, 1, 0))
        self.invoke(wrong, nodes[-1], False, "contract")
        # Wrong dependency is type-valid and still leaves every definition reachable.
        nodes.append(call(nodes, 1)); nodes.append(then(nodes, 2, 3))
        wrong = nodes[:3]; wrong.append(call(wrong, 0)); wrong.append(then(wrong, 2, 3))
        self.invoke(wrong, nodes[-1], False, "contract")

    def test_canonical_terms_controls_and_nonleaf_source(self):
        base = layout(["Bit", "Bit", "Bits0"])
        good = [leaf(base, [(1, [0]), (255, [0]), (0, []), (16, [0, 1])])]
        self.assertEqual(good[0]["claim"], [(16, [0, 1])]); self.invoke(good)
        for axes in [[0, 0], [1, 0], [2]]:
            bad = [leaf(base, [])]; bad[0]["source"] = [(16, axes)]
            self.invoke(bad, good[0], False)
        for claim in [[(0, [0])], [(1, [0]), (15, [0])], [(1, [1]), (1, [0])]]:
            bad = copy.deepcopy(good); bad[0]["claim"] = claim
            self.invoke(bad, good[0], False)
        good.append(call(good, 0))
        bad = copy.deepcopy(good); bad[1]["source"] = [(0, [])]
        self.invoke(bad, accepted=False)
        bad = copy.deepcopy(good); bad[1]["claim"] = []
        self.invoke(bad, accepted=False, code="contract")

    def test_structural_types_owners_and_graphs_remain_checked(self):
        value = layout([("Bit", "Unit", "Bit"), "Bits0"])
        nodes = [leaf(value, [(1, [0, 1])])]; nodes.append(call(nodes, 0))
        self.invoke(nodes)
        for side in ["before", "after", "result"]:
            bad = copy.deepcopy(nodes)
            bad[1]["wiring"][side]["outputs"][0] = (["t2", "t2", "Bit", "Unit", "Bit"], [0, 1])
            self.invoke(bad, nodes[-1], False)
            bad = copy.deepcopy(nodes); bad[1]["wiring"][side]["owners"] = [0, 0]
            self.invoke(bad, nodes[-1], False)
        for child in [1, 2, 255]:
            bad = copy.deepcopy(nodes); bad[1]["wiring"]["child"] = child
            self.invoke(bad, nodes[-1], False)
        self.invoke(nodes, nodes[0], False, entry=0)

    def test_shared_doubling_and_sparse_limits(self):
        nodes = [leaf(layout(["Bit"]), [(1, [0])])]
        for _ in range(63):
            nodes.append(then(nodes, len(nodes) - 1, len(nodes) - 1))
        data = self.invoke(nodes)
        self.assertEqual(data["stats"]["expanded_layouts"], 2 ** 63)
        self.assertEqual(data["stats"]["nodes"], 64)
        self.assertEqual(data["stats"]["terms"], 0)
        self.assertEqual(data["stats"]["expanded_phase_terms"], 2 ** 63)
        self.assertLess(data["stats"]["work_units"], 25000)
        nodes.append(then(nodes, 63, 63)); self.invoke(nodes, accepted=False, code="limit")
        value = layout(["Bits8", "Bits8", "Bits0"])
        terms = [(1, [bit for bit in range(16) if mask & (1 << bit)]) for mask in range(128)]
        nodes = [leaf(value, terms)]; self.invoke(nodes)
        nodes.append(then(nodes, 0, 0)); self.invoke(nodes, accepted=False, code="limit")
        nodes = [leaf(value, terms + [(1, [7])])]
        self.invoke(nodes, accepted=False, code="limit", stage="artifact")
        # A forged low count rejects before its consumers can exploit cheaper preflight.
        nodes = [leaf(layout(["Bit", "Bit"]), [(1, [0]), (1, [1])])]
        nodes[0]["claim"] = []
        for _ in range(63):
            nodes.append(then(nodes, len(nodes) - 1, len(nodes) - 1))
        self.invoke(nodes, accepted=False, code="contract")

    def test_sixteen_axes_without_basis_enumeration(self):
        for n, m in [(1, 3), (2, 4), (8, 8)]:
            value = layout([f"Bits{n}", f"Bits{m}", "Bits0"], [1, 0, 2],
                           list(range(n, n + m)) + list(range(n)))
            nodes = [leaf(value, [(1, [0, n]), (16, list(range(n + m))), (255, [])])]
            nodes.append(call(nodes, 0))
            self.invoke(nodes)
        # No quantum owner at all still cannot erase a submitted scalar phase.
        nodes = [leaf(layout([]), [(7, [])])]; self.invoke(nodes)
        required = copy.deepcopy(nodes[0]); required["claim"] = []
        self.invoke(nodes, required, False, "contract")

    def test_false_large_claims_are_charged_before_validation(self):
        value = layout(["Bits7"])
        claim = [(1, [i for i in range(7) if mask & (1 << i)]) for mask in range(128)]
        nodes = [leaf(value, []) for _ in range(14)]
        for node in nodes:
            node["claim"] = claim
        previous = 0
        for index in range(1, 14):
            nodes.append(then(nodes, previous, index))
            previous = len(nodes) - 1
        self.assertLess(len(encode(nodes).encode()), 65536)
        result = self.invoke(nodes, accepted=False, code="limit")
        # The false leaf claims alone exhaust the budget before any composition.
        self.assertLess(result["node"], 14)

    def test_strict_transport_independent_request(self):
        nodes = [leaf(layout(["Bit"]), [(16, [0])])]
        source, required = encode(nodes), requirement(nodes[0])
        for bad in [source[:-1], source + "\n", source.replace("entry 0", "entry 00"),
                    source.replace("term 16 1 0", "term 016 1 0", 1),
                    source.replace("source_phases 1", "source_phases 0"),
                    source.replace("term 16 1 0", "term -1 1 0", 1),
                    source.replace("\n", "\r\n"), source.replace("leaf\n", "hadamard\n"),
                    source.replace("typed-phase256-dag-v1", "qpe-dyadic8-v1"), b"\xff"]:
            self.invoke(bad, required, False, "syntax", "artifact")
        for bad in [source.replace("term 16 1 0", "term 256 1 0", 1),
                    source.replace("term 16 1 0", "term 16 1 16", 1), source + " " * 65536]:
            self.invoke(bad, required, False, "limit", "artifact")
        self.invoke(source, required + "\n", False, "syntax", "requirement")
        self.invoke(source, required + " " * 65536, False, "limit", "requirement")
        malformed = copy.deepcopy(nodes[0]); malformed["claim"] = [(0, [0])]
        self.invoke(nodes, malformed, False)


def main():
    global BINARY
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, default=BINARY)
    parser.add_argument("--source-only", type=Path, help="check the finite source client with this Rust binary")
    args, remaining = parser.parse_known_args()
    if args.source_only:
        if remaining:
            parser.error("unexpected source-only arguments")
        return check_source(args.source_only.resolve())
    BINARY = args.binary.resolve()
    program = unittest.main(argv=[__file__, *remaining], exit=False)
    print(f"Native typed-phase/layout decisions: {PhaseLayoutTests.decisions}")
    return 0 if program.result.wasSuccessful() else 1


if __name__ == "__main__":
    raise SystemExit(main())
