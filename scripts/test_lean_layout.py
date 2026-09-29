#!/usr/bin/env python3
"""Independent process, layout and reference-amplitude tests for the Lean component.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
No source compiler or upstream corpus framework is used as the semantic oracle.
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

ROOT = Path(__file__).resolve().parent.parent
BINARY = ROOT / "lean-kernel/.lake/build/bin/qleisli-kernel"


def atoms(ty):
    if isinstance(ty, str):
        return [ty]
    return [f"t{len(ty)}"] + [atom for child in ty for atom in atoms(child)]


def width(ty):
    if isinstance(ty, tuple):
        return sum(map(width, ty))
    return {"Unit": 0, "Bit": 1}.get(ty, int(ty[4:]) if ty.startswith("Bits") else 0)


def inverse(permutation):
    return [permutation.index(i) for i in range(len(permutation))]


def layout(types, owners=None, axes=None, input_axes=None):
    """An independent owner-wise construction, not a copy of the Lean checker."""
    sizes = list(map(width, types))
    n = sum(sizes)
    owners = list(range(len(types))) if owners is None else owners
    axes = list(range(n)) if axes is None else axes
    input_axes = list(range(n)) if input_axes is None else input_axes
    inputs, offset = [], 0
    for ty, size in zip(types, sizes):
        inputs.append((atoms(ty), input_axes[offset:offset + size]))
        offset += size
    back = inverse(axes)
    outputs = [(inputs[i][0], [back[a] for a in inputs[i][1]]) for i in owners]
    return dict(inputs=inputs, outputs=outputs, owners=owners, axes=axes,
                inverse_owners=inverse(owners), inverse_axes=back)


def vector(tag, values):
    return " ".join([tag, str(len(values)), *map(str, values)])


def encode(value, requirement=False):
    tag = "qleisli.layout-request" if requirement else "qleisli.layout"
    lines = [f"{tag} 1 typed-layout-v1"]
    for name in ["inputs", "outputs"]:
        lines.append(f"{name} {len(value[name])}")
        for ty, axes in value[name]:
            lines.append(" ".join(["port", str(len(ty)), *ty, str(len(axes)), *map(str, axes)]))
    for name in ["owners", "axes"] + ([] if requirement else ["inverse_owners", "inverse_axes"]):
        lines.append(vector(name, value[name]))
    return "\n".join(lines) + "\n"


def independent_columns(value):
    """Assign output bits owner by owner and compare to the submitted global map."""
    n = len(value["axes"])
    assert n <= 6  # Enumeration belongs only to the small external test oracle.
    forward = []
    for bits in itertools.product([0, 1], repeat=n):
        out = [None] * n
        for j, (_, out_axes) in enumerate(value["outputs"]):
            _, in_axes = value["inputs"][value["owners"][j]]
            for target, source in zip(out_axes, in_axes):
                out[target] = bits[source]
        expected = tuple(bits[i] for i in value["axes"])
        assert tuple(out) == expected
        assert tuple(out[i] for i in value["inverse_axes"]) == bits
        forward.append((bits, tuple(out)))
    assert len({output for _, output in forward}) == 2 ** n
    # No factorization assumption: amplitudes depend jointly on all bits and reference.
    amplitudes = {(bits, r): complex(1 + sum((i + 2) * b for i, b in enumerate(bits)) + r,
                                    sum(bits) - 3 * r)
                  for bits, _ in forward for r in range(3)}
    moved = {(out, r): amplitudes[(bits, r)] for bits, out in forward for r in range(3)}
    restored = {(tuple(out[i] for i in value["inverse_axes"]), r): coefficient
                for (out, r), coefficient in moved.items()}
    assert restored == amplitudes
    assert sum(abs(a) ** 2 for a in moved.values()) == sum(abs(a) ** 2 for a in amplitudes.values())


def unique(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate key {key}")
        result[key] = value
    return result


class LayoutTests(unittest.TestCase):
    decisions = 0

    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix="qleisli-layout-")
        self.addCleanup(self.directory.cleanup)
        self.artifact = Path(self.directory.name) / "artifact.qhl"
        self.requirement = Path(self.directory.name) / "requirement.qhr"

    def invoke(self, value, required=None, accepted=True, code=None, stage="verification"):
        program = encode(value) if isinstance(value, dict) else value
        if required is None:
            required = encode(value, True)
        elif isinstance(required, dict):
            required = encode(required, True)
        self.artifact.write_bytes(program.encode() if isinstance(program, str) else program)
        self.requirement.write_bytes(required.encode() if isinstance(required, str) else required)
        result = subprocess.run([str(BINARY), "--layout", str(self.artifact), str(self.requirement)],
                                capture_output=True, timeout=5, check=False)
        type(self).decisions += 1
        self.assertEqual(result.returncode, 0 if accepted else 1, result)
        self.assertEqual(result.stderr, b"")
        self.assertEqual(result.stdout.count(b"\n"), 1)
        data = json.loads(result.stdout, object_pairs_hook=unique)
        self.assertEqual(set(data), {"format", "version", "profile", "accepted", "code", "stage", "stats"})
        self.assertEqual(data["format"], "qleisli.kernel-result")
        self.assertEqual(data["version"], 1)
        self.assertEqual(data["profile"], "typed-layout-v1")
        self.assertIs(data["accepted"], accepted)
        self.assertEqual(data["code"], code or ("accepted" if accepted else "invalid_ir"))
        self.assertEqual(data["stage"], stage)
        if accepted:
            self.assertEqual(set(data["stats"]), {"owners", "axes", "type_atoms", "work_units", "dense_dimension"})
            self.assertEqual(data["stats"]["dense_dimension"], 0)
        else:
            self.assertIsNone(data["stats"])
        return data

    def test_preserved_source_layout(self):
        root = ROOT / "tests/fixtures/lean_layout"
        result = self.invoke((root / "reorder.qhl").read_text(), (root / "reorder.qhr").read_text())
        self.assertEqual(result["stats"], dict(owners=3, axes=3, type_atoms=12,
                                              work_units=2888, dense_dimension=0))

    def test_small_permutations_and_entangled_reference(self):
        rng = random.Random(20260929)
        type_sets = [["Unit", "Bit", ("Bit", "Unit", "Bit")],
                     ["Bits0", "Bits2", "Unit", "Bit"],
                     [(("Bit", "Unit"), "Bit"), "Bit"],
                     ["Bit"] * 4, ["Unit"] * 4, []]
        for types in type_sets:
            for _ in range(24):
                owners = rng.sample(range(len(types)), len(types))
                n = sum(map(width, types))
                axes = rng.sample(range(n), n)
                inputs = rng.sample(range(n), n)
                value = layout(types, owners, axes, inputs)
                independent_columns(value)
                self.invoke(value)

    def test_request_rejects_a_valid_wrong_permutation(self):
        identity = layout(["Bit", "Bit"])
        wrong = layout(["Bit", "Bit"], [1, 0], [1, 0])
        self.invoke(wrong)  # Structurally valid, but does not satisfy the identity request.
        self.invoke(wrong, identity, False, "contract")
        self.invoke(identity, wrong, False, "contract")

    def test_zero_width_owners_are_not_optional(self):
        good = layout(["Unit", "Bit", "Bits0"], [2, 0, 1])
        self.invoke(good)
        for mutation in ["omit", "duplicate", "invent", "wrong_unit_type"]:
            bad = copy.deepcopy(good)
            if mutation == "omit":
                del bad["outputs"][0]
                del bad["owners"][0]
            elif mutation == "duplicate":
                bad["owners"] = [0, 0, 1]
            elif mutation == "invent":
                bad["outputs"].append((["Unit"], []))
                bad["owners"].append(3)
            else:
                bad["outputs"][0] = (["Unit"], [])
            self.invoke(bad, good, False)
        changed = layout(["Unit", "Bit", "Unit"], [2, 0, 1])
        self.invoke(changed, good, False, "contract")

    def test_equal_width_types_and_order_stay_distinct(self):
        flat = layout([("Bit", "Unit", "Bit")])
        for shape in [["t2", "t2", "Bit", "Unit", "Bit"], ["Bits2"], ["t2", "Bit", "Bit"]]:
            bad = copy.deepcopy(flat)
            bad["outputs"][0] = (shape, [0, 1])
            self.invoke(bad, flat, False)
        for ty in ["Unit", "Bits0", "Bit", "Bits1"]:
            self.invoke(layout([ty]))
        for key in ["inputs", "outputs"]:
            bad = copy.deepcopy(flat)
            bad[key][0] = (bad[key][0][0], [1, 0])
            self.invoke(bad, flat, False)

    def test_maps_inverses_ranges_and_axis_partition(self):
        good = layout(["Bit", "Bit", "Bit"], [2, 0, 1], [1, 2, 0])
        for field in ["owners", "axes", "inverse_owners", "inverse_axes"]:
            for values in [[], [0, 1], [0, 0, 1], [0, 1, 3], [0, 1, 4096], [0, 1, 2, 3]]:
                bad = copy.deepcopy(good)
                bad[field] = values
                self.invoke(bad, good, False)
        for field in ["inputs", "outputs"]:
            for axes in [[], good[field][0][1], [3]]:
                bad = copy.deepcopy(good)
                bad[field][2] = (["Bit"], axes)
                self.invoke(bad, good, False)

    def test_prefix_tree_and_depth_boundaries(self):
        for shape in [[], ["t0"], ["t1", "Unit"], ["t3", "Bit", "Unit"],
                      ["Unit", "Unit"], ["Bits9"], ["t65"] + ["Unit"] * 65]:
            bad = layout(["Unit"])
            bad["inputs"][0] = bad["outputs"][0] = (shape, [])
            self.invoke(bad, accepted=False)
        for depth in [32, 33]:
            shape = ["t2", "Unit"] * depth + ["Unit"]
            value = layout(["Unit"])
            value["inputs"][0] = value["outputs"][0] = (shape, [])
            self.invoke(value, accepted=depth == 32)
        shape = ["t2", "t62"] + ["Unit"] * 62 + ["t63"] + ["Unit"] * 63
        self.assertEqual(len(shape), 128)
        good = layout(["Unit"])
        good["inputs"][0] = good["outputs"][0] = (shape, [])
        self.invoke(good)
        good["inputs"][0] = (shape + ["Unit"], [])
        self.invoke(good, accepted=False, code="limit", stage="artifact")

    def test_sixteen_axes_and_capacity_without_dense_matrices(self):
        for n, m in [(1, 3), (2, 4), (8, 8)]:
            value = layout([f"Bits{n}", f"Bits{m}"], [1, 0],
                           list(range(n, n + m)) + list(range(n)))
            result = self.invoke(value)
            self.assertEqual(result["stats"]["axes"], n + m)
            self.assertEqual(result["stats"]["type_atoms"], 4)
        too_wide = layout(["Bits8", "Bits8", "Bit"])
        self.invoke(too_wide, accepted=False, code="limit", stage="artifact")
        for owners in [64, 65]:
            value = layout(["Unit"] * owners)
            self.invoke(value, accepted=owners == 64,
                        code=None if owners == 64 else "limit",
                        stage="verification" if owners == 64 else "artifact")
        for last_arity in [54, 55]:
            value = layout([tuple(["Unit"] * k) for k in [63, 63, 63, last_arity]])
            self.invoke(value, accepted=last_arity == 54, code=None if last_arity == 54 else "limit")
        too_many_atoms = layout([tuple(["Unit"] * 63)] * 5)
        self.invoke(too_many_atoms, accepted=False, code="limit")

    def test_strict_transport_and_separate_request(self):
        good = layout(["Bit"])
        source, required = encode(good), encode(good, True)
        for bad in [source[:-1], source + "\n", source.replace("inputs 1", "inputs 01"),
                    source.replace("Bit", "QBit"), source.replace(" 1\n", " 1 \n", 1),
                    source.replace(" 1\n", "\t1\n", 1), source.replace("\n", "\r\n"),
                    source.replace("typed-layout-v1", "qpe-dyadic8-v1"),
                    source.replace("axes 1 0", "axes 1 -1", 1),
                    source.replace("port 1 Bit 1 0", "port 1 Bit 0 0"),
                    source + "extra 0\n", b"\xff", source + "\u2028"]:
            self.invoke(bad, required, False, "syntax", "artifact")
        self.invoke(source.replace("axes 1 0", "axes 1 99999", 1), required, False, "limit", "artifact")
        self.invoke(source + " " * 65536, required, False, "limit", "artifact")
        self.invoke(source, required + "\n", False, "syntax", "requirement")
        self.invoke(source, required + " " * 65536, False, "limit", "requirement")


def main():
    global BINARY
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, default=BINARY)
    args, remaining = parser.parse_known_args()
    BINARY = args.binary.resolve()
    program = unittest.main(argv=[__file__, *remaining], exit=False)
    print(f"Native typed-layout decisions: {LayoutTests.decisions}")
    return 0 if program.result.wasSuccessful() else 1


if __name__ == "__main__":
    raise SystemExit(main())
