#!/usr/bin/env python3
"""Fresh-process typed-call checks with a direct owner-wise graph oracle.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
The graph oracle never reads the proposed summary of a call/composition.
"""
import argparse
import copy
import itertools
import json
from pathlib import Path
import random
import subprocess
import tempfile
import unittest

from test_lean_layout import ROOT, encode as encode_layout, inverse, layout, unique

BINARY = ROOT / "lean-kernel/.lake/build/bin/qleisli-kernel"


def identity(ports):
    n = sum(len(axes) for _, axes in ports)
    return dict(inputs=ports, outputs=ports, owners=list(range(len(ports))),
                axes=list(range(n)), inverse_owners=list(range(len(ports))),
                inverse_axes=list(range(n)))


def compose(first, second):
    """Producer only. The oracle below executes literal owner ports independently."""
    assert first["outputs"] == second["inputs"]
    owners = [first["owners"][i] for i in second["owners"]]
    axes = [first["axes"][i] for i in second["axes"]]
    return dict(inputs=first["inputs"], outputs=second["outputs"], owners=owners, axes=axes,
                inverse_owners=inverse(owners), inverse_axes=inverse(axes))


def leaf(value):
    return dict(kind="leaf", result=value)


def call(nodes, child, before=None, after=None):
    target = nodes[child]["result"]
    before = identity(target["inputs"]) if before is None else before
    after = identity(target["outputs"]) if after is None else after
    return dict(kind="call", child=child, before=before, after=after,
                result=compose(compose(before, target), after))


def then(nodes, first, second):
    return dict(kind="then", first=first, second=second,
                result=compose(nodes[first]["result"], nodes[second]["result"]))


def encode(nodes, entry=None):
    lines = ["qleisli.layout-dag 1 typed-layout-dag-v1",
             f"entry {len(nodes) - 1 if entry is None else entry}", f"definitions {len(nodes)}"]
    for node in nodes:
        if node["kind"] == "leaf":
            lines.append("leaf")
        elif node["kind"] == "call":
            lines.append(f"call {node['child']}")
            for key in ["before", "after"]:
                lines.extend(encode_layout(node[key]).splitlines()[1:])
        else:
            lines.append(f"then {node['first']} {node['second']}")
        lines.extend(encode_layout(node["result"]).splitlines()[1:])
    return "\n".join(lines) + "\n"


def apply_ports(value, state):
    """Forward action on arbitrary owner tokens and basis coordinates via ports."""
    owners, bits = state
    moved = [None] * len(bits)
    for out_owner, (_, output_axes) in enumerate(value["outputs"]):
        _, input_axes = value["inputs"][value["owners"][out_owner]]
        for target, source in zip(output_axes, input_axes):
            moved[target] = bits[source]
    return tuple(owners[i] for i in value["owners"]), tuple(moved)


def execute(nodes, entry, state):
    """Small-case operational oracle, expanding calls without looking at claims."""
    node = nodes[entry]
    if node["kind"] == "leaf":
        return apply_ports(node["result"], state)
    if node["kind"] == "call":
        state = apply_ports(node["before"], state)
        return apply_ports(node["after"], execute(nodes, node["child"], state))
    return execute(nodes, node["second"], execute(nodes, node["first"], state))


def independent_oracle(nodes):
    required = nodes[-1]["result"]
    n = len(required["axes"])
    assert n <= 6
    owners = tuple(range(len(required["owners"])))
    outputs = {}
    for bits in itertools.product([0, 1], repeat=n):
        state = owners, bits
        out = execute(nodes, len(nodes) - 1, state)
        assert out == apply_ports(required, state)
        assert len(set(out[0])) == len(owners)
        assert out[1] not in outputs
        outputs[out[1]] = bits
    # Joint coefficients need not factor by owner or by reference.
    coefficients = {(bits, r): complex(3 * sum(bits) + r, sum((i + 1) * b for i, b in enumerate(bits)) - r)
                    for bits in outputs.values() for r in range(3)}
    transported = {(out, r): coefficients[bits, r]
                   for out, bits in outputs.items() for r in range(3)}
    restored = {(outputs[out], r): c for (out, r), c in transported.items()}
    assert restored == coefficients


class LayoutDagTests(unittest.TestCase):
    decisions = 0

    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix="qleisli-layout-dag-")
        self.addCleanup(self.directory.cleanup)
        self.artifact = Path(self.directory.name) / "artifact.qhd"
        self.requirement = Path(self.directory.name) / "request.qhr"

    def invoke(self, nodes, required=None, accepted=True, code=None, stage="verification", entry=None):
        program = encode(nodes, entry) if isinstance(nodes, list) else nodes
        if required is None:
            required = nodes[-1]["result"]
        if isinstance(required, dict):
            required = encode_layout(required, True)
        self.artifact.write_bytes(program.encode() if isinstance(program, str) else program)
        self.requirement.write_bytes(required.encode() if isinstance(required, str) else required)
        result = subprocess.run([str(BINARY), "--layout-dag", str(self.artifact), str(self.requirement)],
                                capture_output=True, timeout=5, check=False)
        type(self).decisions += 1
        self.assertEqual(result.returncode, 0 if accepted else 1, result)
        self.assertEqual(result.stderr, b"")
        self.assertEqual(result.stdout.count(b"\n"), 1)
        data = json.loads(result.stdout, object_pairs_hook=unique)
        self.assertEqual(set(data), {"format", "version", "profile", "accepted", "code", "stage", "node", "stats"})
        self.assertEqual((data["format"], data["version"], data["profile"]),
                         ("qleisli.kernel-result", 1, "typed-layout-dag-v1"))
        self.assertIs(data["accepted"], accepted)
        self.assertEqual(data["code"], code or ("accepted" if accepted else "invalid_ir"))
        self.assertEqual(data["stage"], stage)
        if accepted:
            self.assertIsNone(data["node"])
            self.assertEqual(set(data["stats"]), {"nodes", "references", "work_units", "depth",
                                                   "expanded_layouts", "dense_dimension"})
            self.assertEqual(data["stats"]["dense_dimension"], 0)
        else:
            self.assertIsNone(data["stats"])
            if stage == "verification":
                self.assertIsInstance(data["node"], int)
            else:
                self.assertIsNone(data["node"])
        return data

    def test_saved_source_shared_calls(self):
        root = ROOT / "tests/fixtures/lean_layout_dag"
        data = self.invoke((root / "shared.qhd").read_text(), (root / "identity.qhr").read_text())
        self.assertEqual(data["stats"], dict(nodes=3, references=3, work_units=6927,
                                              depth=3, expanded_layouts=6, dense_dimension=0))

    def test_direct_oracle_calls_composition_reference(self):
        rng = random.Random(29092026)
        for n in range(5):
            for _ in range(16):
                types = ["Bit"] * n + ["Unit", "Bits0"]
                def permutation():
                    p = rng.sample(range(n), n)
                    return layout(types, p + [n, n + 1], p)
                nodes = [leaf(permutation()), leaf(permutation())]
                nodes.append(call(nodes, 0, permutation(), permutation()))
                nodes.append(then(nodes, 2, 1))
                nodes.append(then(nodes, 3, 2))
                independent_oracle(nodes)
                self.invoke(nodes)

    def test_valid_wrong_callee_adapter_and_order(self):
        a = layout(["Bit"] * 3, [1, 0, 2], [1, 0, 2])
        b = layout(["Bit"] * 3, [0, 2, 1], [0, 2, 1])
        base = [leaf(a), leaf(b)]
        base.append(then(base, 0, 1))
        base.append(call(base, 0))
        base.append(then(base, 2, 3))
        self.invoke(base)
        for mutation in ["callee", "before", "after", "order"]:
            bad = copy.deepcopy(base)
            if mutation == "order":
                bad[2] = then(bad, 1, 0)
            elif mutation == "callee":
                bad[3] = call(bad, 1)
            else:
                bad[3] = call(bad, 0, before=b if mutation == "before" else None,
                              after=b if mutation == "after" else None)
            bad[4] = then(bad, 2, 3)
            independent_oracle(bad)
            self.invoke(bad)  # Valid program with a different meaning.
            self.invoke(bad, base[-1]["result"], False, "contract")
        stale = copy.deepcopy(base)
        stale[3]["child"] = 1  # Even a matching independent forged root cannot fix stale receipts.
        self.invoke(stale, accepted=False, code="contract")

    def test_call_interfaces_types_zero_width_and_inverses(self):
        value = layout(["Unit", ("Bit", "Unit", "Bit"), "Bits0"])
        nodes = [leaf(value)]
        nodes.append(call(nodes, 0))
        self.invoke(nodes)
        for side in ["before", "after", "result"]:
            for key in ["owners", "inverse_owners", "axes", "inverse_axes"]:
                bad = copy.deepcopy(nodes)
                bad[1][side][key] = [0] * len(value[key])
                self.invoke(bad, value, False)
        # Each adapter remains valid by itself, but its exact callee boundary differs.
        for replacement in [layout(["Unit", (("Bit", "Unit"), "Bit"), "Bits0"]),
                            layout(["Unit", ("Bit", "Unit", "Bit"), "Unit"]),
                            layout(["Unit", ("Bit", "Unit", "Bit"), "Bits0"], input_axes=[1, 0])]:
            for side in ["before", "after"]:
                bad = copy.deepcopy(nodes)
                bad[1][side] = replacement
                self.invoke(bad, value, False)
        for side in ["before", "after", "result"]:
            bad = copy.deepcopy(nodes)
            del bad[1][side]["outputs"][2]
            bad[1][side]["owners"] = [0, 1]
            self.invoke(bad, value, False)

    def test_graph_binding_and_reachability(self):
        value = layout(["Bit"])
        nodes = [leaf(value)]
        nodes.append(call(nodes, 0))
        for child in [1, 2, 255]:
            bad = copy.deepcopy(nodes)
            bad[1]["child"] = child
            self.invoke(bad, value, False)
        self.invoke(nodes, value, False, entry=0)  # Unreachable declaration.
        self.invoke(nodes, value, False, entry=2)
        self.invoke([], value, False, "limit", entry=0)
        bad = nodes + [leaf(value)]
        self.invoke(bad, value, False)

    def test_maximum_definition_count(self):
        value = layout(["Bit"])
        nodes = [leaf(value) for _ in range(128)]
        level = list(range(128))
        while len(level) > 1:
            next_level = []
            for first, second in zip(level[::2], level[1::2]):
                next_level.append(len(nodes))
                nodes.append(then(nodes, first, second))
            level = next_level
        nodes.append(call(nodes, 254))
        self.assertEqual(len(nodes), 256)
        data = self.invoke(nodes)
        self.assertEqual(data["stats"]["depth"], 9)
        self.assertEqual(data["stats"]["references"], 255)
        nodes.append(call(nodes, 255))
        self.invoke(nodes, value, False, "limit", "artifact")

    def test_sharing_depth_and_aggregate_work(self):
        value = layout(["Bit"])
        nodes = [leaf(value)]
        for _ in range(63):
            nodes.append(then(nodes, len(nodes) - 1, len(nodes) - 1))
        data = self.invoke(nodes)
        self.assertEqual(data["stats"]["nodes"], 64)
        self.assertEqual(data["stats"]["references"], 126)
        self.assertEqual(data["stats"]["depth"], 64)
        self.assertEqual(data["stats"]["expanded_layouts"], 2 ** 63)
        self.assertLess(data["stats"]["work_units"], 20000)
        nodes.append(then(nodes, 63, 63))
        self.invoke(nodes, accepted=False, code="limit")
        heavy = layout([tuple(["Unit"] * n) for n in [63, 63, 63, 54]])
        nodes = [leaf(heavy)]
        self.invoke(nodes, accepted=False, code="limit")  # Includes final entry validation.
        # Small source, but repeated typed trees exhaust the shared work budget.
        medium = layout([tuple(["Unit"] * 50)])
        nodes = [leaf(medium)]
        for _ in range(24):
            nodes.append(call(nodes, len(nodes) - 1))
        self.invoke(nodes, accepted=False, code="limit")

    def test_sixteen_axes_and_type_boundaries(self):
        for n, m in [(1, 3), (2, 4), (8, 8)]:
            value = layout([f"Bits{n}", f"Bits{m}", "Bits0"], [1, 0, 2],
                           list(range(n, n + m)) + list(range(n)))
            nodes = [leaf(value)]
            nodes.append(call(nodes, 0))
            self.invoke(nodes)
        flat = layout([("Bit", "Unit", "Bit")])
        for type_atoms in [["t2", "t2", "Bit", "Unit", "Bit"], ["Bits2"]]:
            bad = copy.deepcopy(flat)
            bad["outputs"][0] = (type_atoms, [0, 1])
            self.invoke([leaf(bad)], flat, False)

    def test_strict_transport_and_request(self):
        nodes = [leaf(layout(["Bit"]))]
        source = encode(nodes)
        required = encode_layout(nodes[0]["result"], True)
        for bad in [source[:-1], source + "\n", source.replace("entry 0", "entry 00"),
                    source.replace("definitions 1", "definitions 2"),
                    source.replace("leaf\n", "repeat 0 0\n"), source.replace("\n", "\r\n"),
                    source.replace("entry 0", "entry -1"), source.replace("leaf\n", "leaf \n"),
                    source.replace("typed-layout-dag-v1", "qpe-v1"), b"\xff", source + "\u2028"]:
            self.invoke(bad, required, False, "syntax", "artifact")
        for bad in [source.replace("definitions 1", "definitions 257"), source + " " * 65536,
                    source.replace("entry 0", "entry 256")]:
            self.invoke(bad, required, False, "limit", "artifact")
        self.invoke(source, required + "\n", False, "syntax", "requirement")
        self.invoke(source, required + " " * 65536, False, "limit", "requirement")


def main():
    global BINARY
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, default=BINARY)
    args, remaining = parser.parse_known_args()
    BINARY = args.binary.resolve()
    program = unittest.main(argv=[__file__, *remaining], exit=False)
    print(f"Native typed-layout DAG decisions: {LayoutDagTests.decisions}")
    return 0 if program.result.wasSuccessful() else 1


if __name__ == "__main__":
    raise SystemExit(main())
