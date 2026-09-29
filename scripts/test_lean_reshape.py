#!/usr/bin/env python3
"""Native canonical reshape checks against an independent recursive tree oracle.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
No source API or production semantic evidence is enabled by this experiment.
"""
import argparse
import copy
import hashlib
import itertools
import json
from pathlib import Path
import random

from test_hierarchical_artifact import ROOT, build_and_run

UNIT, BIT = ("unit", 0), ("bit", 0)


def tree(tokens):
    """Parse actual immediate children, independently of Lean's prefix fold."""
    if not 1 <= len(tokens) <= 128:
        raise ValueError("type storage")
    cursor = 0

    def take(depth):
        nonlocal cursor
        if cursor == len(tokens):
            raise ValueError("missing child")
        tag, n = tokens[cursor]
        cursor += 1
        if tag == "tuple":
            if not 2 <= n <= 64 or depth >= 32:
                raise ValueError("arity/depth")
            return tuple(take(depth + 1) for _ in range(n))
        if tag == "bits" and not 0 <= n <= 8:
            raise ValueError("sized atom")
        return (tag, n)

    result = take(0)
    if cursor != len(tokens):
        raise ValueError("trailing tree")
    return result


def leaf_types(node):
    if isinstance(node[0], str):
        return [] if node[0] == "unit" else [node]
    return [leaf for child in node for leaf in leaf_types(child)]


def encode_tree(node, values):
    """Each product uses its children's encodings and independently summed widths."""
    if isinstance(node[0], str):
        tag, n = node
        if tag == "unit":
            return 0, 0
        return next(values), 1 if tag == "bit" else n
    label = offset = 0
    for child in node:
        value, bits = encode_tree(child, values)
        label += value << offset
        offset += bits
    return label, offset


def port(tokens, owner, axes=None):
    if axes is None:
        types = leaf_types(tree(tokens))
        width = sum(1 if tag == "bit" else n for tag, n in types)
        axes = [100 + 3 * i for i in range(width)]
    return dict(tokens=tokens, owner=owner, axes=axes)


def request(source, target):
    return dict(source=port(source, 10), target=port(target, 11))


def charge(req):
    return 8 * (1 + sum(len(p[part]) for p in req.values()
                        for part in ("tokens", "axes"))) ** 2


def oracle(req, required, budget):
    cost = charge(req) + charge(required)
    if budget > 2000000 or cost > budget:
        return "limit"
    try:
        nodes = []
        for p in req.values():
            if not 0 <= p["owner"] <= 2**32 - 1:
                raise ValueError("owner bound")
            if any(not 0 <= a <= 2**32 - 1 for a in p["axes"]):
                raise ValueError("axis bound")
            t = tree(p["tokens"])
            leaves = leaf_types(t)
            _, width = encode_tree(t, iter([0] * len(leaves)))
            if width != len(p["axes"]) or width > 16:
                raise ValueError("width")
            nodes.append(leaves)
        a, b = req["source"], req["target"]
        if (a["owner"] == b["owner"] or a["axes"] != b["axes"]
                or len(set(a["axes"])) != len(a["axes"]) or nodes[0] != nodes[1]):
            raise ValueError("canonical adapter")
    except ValueError:
        return "invalid_ir"
    return "checked" if req == required else "contract"


def samples(req):
    leaves = leaf_types(tree(req["source"]["tokens"]))
    domains = [range(2 ** (1 if tag == "bit" else n)) for tag, n in leaves]
    width = len(req["source"]["axes"])
    if width <= 6:
        return list(itertools.product(*domains))
    rng = random.Random(291)
    return [tuple(0 for _ in domains), tuple(len(d) - 1 for d in domains)] + [
        tuple(rng.randrange(len(d)) for d in domains) for _ in range(14)]


def cases():
    rows = []

    def add(name, req, required=None, budget=2000000):
        expected = copy.deepcopy(req if required is None else required)
        rows.append(dict(name=name, request=req, required=expected, budget=budget,
                         status=oracle(req, expected, budget)))

    triples = [
        [("tuple", 3), BIT, BIT, BIT],
        [("tuple", 2), ("tuple", 2), BIT, BIT, BIT],
        [("tuple", 2), BIT, ("tuple", 2), BIT, BIT],
        [("tuple", 4), UNIT, BIT, ("tuple", 3), BIT, UNIT, BIT, UNIT],
    ]
    for i, a in enumerate(triples):
        for j, b in enumerate(triples):
            add(f"triple-{i}-{j}", request(a, b))
    for n in range(9):
        atoms = [("bits", n), BIT, ("bits", 0)]
        a = [("tuple", 3)] + atoms
        b = [("tuple", 3), UNIT, ("tuple", 2)] + atoms[:2] + [atoms[2]]
        add(f"sized-{n}", request(a, b))
        add(f"sized-inverse-{n}", request(b, a))
    units = [[UNIT], [("tuple", 2), UNIT, UNIT],
             [("tuple", 3), UNIT, ("tuple", 2), UNIT, UNIT, UNIT]]
    for i, a in enumerate(units):
        for j, b in enumerate(units):
            add(f"zero-width-{i}-{j}", request(a, b))
    for n in (6, 7, 12, 16):
        a = [("tuple", n)] + [BIT] * n
        b = [("tuple", 2), UNIT] + a
        add(f"width-{n}", request(a, b))
    # Reproducible varied arities and bracketing; actual trees, never a table.
    rng = random.Random(20260929)

    def regroup(atoms):
        if len(atoms) == 1:
            return [atoms[0]]
        cut = rng.randrange(1, len(atoms))
        return [("tuple", 3), UNIT] + regroup(atoms[:cut]) + regroup(atoms[cut:])

    for i in range(40):
        atoms = [rng.choice([BIT, ("bits", 0), ("bits", 2), UNIT])
                 for _ in range(rng.randrange(2, 7))]
        add(f"regroup-{i}", request([("tuple", len(atoms))] + atoms, regroup(atoms)))

    base = request(triples[0], triples[1])
    for name, change in [
        ("same-type-axis-swap", lambda r: r["target"]["axes"].reverse()),
        ("reused-owner", lambda r: r["target"].update(owner=10)),
        ("fresh-but-unbound-wire", lambda r: r["target"]["axes"].__setitem__(0, 900)),
        ("dropped-axis", lambda r: r["target"]["axes"].pop()),
        ("duplicate-axis", lambda r: [p.update(axes=[100, 100, 106]) for p in r.values()]),
        ("large-owner", lambda r: r["source"].update(owner=2**32)),
        ("large-axis", lambda r: [p["axes"].__setitem__(0, 2**32) for p in r.values()]),
    ]:
        changed = copy.deepcopy(base)
        change(changed)
        add(name, changed)
    for name, a, b in [
        ("bit-is-not-bits1", [BIT], [("bits", 1)]),
        ("bits0-is-not-unit", [("bits", 0)], [UNIT]),
        ("bits2-is-not-two-bits", [("bits", 2)], [("tuple", 2), BIT, BIT]),
        ("changed-atom-order", [("tuple", 2), BIT, ("bits", 1)],
         [("tuple", 2), ("bits", 1), BIT]),
        ("dropped-bits0", [("tuple", 2), BIT, ("bits", 0)], [BIT]),
    ]:
        add(name, request(a, b))
    malformed = [[], [BIT, BIT], [("tuple", 2), BIT], [("tuple", 1), BIT],
                 [("tuple", 0)], [("bits", 9)], [("tuple", 65)] + [UNIT] * 65,
                 [("tuple", 2), UNIT] * 33 + [BIT],
                 [("tuple", 64)] + [UNIT] * 63 + [("tuple", 64)] + [UNIT] * 64]
    for i, tokens in enumerate(malformed):
        changed = copy.deepcopy(base)
        changed["source"]["tokens"] = tokens
        add(f"malformed-{i}", changed)
    deep = [("tuple", 2), UNIT] * 32 + [BIT]
    add("depth-boundary", request(deep, [BIT]))
    add("width-too-large", request([("tuple", 17)] + [BIT] * 17,
                                   [("tuple", 17)] + [BIT] * 17))
    for name, target in [("wrong-required-type", [BIT]),
                          ("equal-leaves-wrong-required-tree", triples[2])]:
        required = copy.deepcopy(base)
        required["target"] = port(target, 11)
        add(name, base, required)
    required = copy.deepcopy(base)
    required["target"]["owner"] = 12
    add("wrong-required-owner", base, required)
    cost = 2 * charge(base)
    add("exact-budget", base, budget=cost)
    add("one-under-budget", base, budget=cost - 1)
    add("zero-budget", base, budget=0)
    add("profile-budget-excess", base, budget=2000001)
    huge = copy.deepcopy(base)
    huge["source"]["tokens"] = [UNIT] * 1000
    add("precharge-oversized", huge)
    return rows


PRELUDE = r'''import QleisliKernel
open QleisliKernel QleisliKernel.Reshape QleisliKernel.Hierarchical.Artifact
def coefficient (label reference : Nat) : Int × Int :=
  ((if label % 2 == 0 then 1 else -1) * (Int.ofNat label + 2 * Int.ofNat reference + 1),
    3 * Int.ofNat label - 5 * Int.ofNat reference)
def report (name : String) (request required : Reshape.Request) (budget : Nat)
    (samples : List (List Nat)) : IO Unit :=
  match accepted : Reshape.check request required budget with
  | .error e => IO.println s!"{name}|{match e with | .limit => "limit" | .invalidIr => "invalid_ir" | .contract => "contract"}"
  | .ok checked =>
    let values := samples.map fun labels =>
      let a := Reshape.encode request.source.basis.toList labels
      let b := Reshape.encode request.target.basis.toList labels
      let h := Reshape.check_leaves request required budget checked accepted
      let routed := if bounded : a < 2 ^ Reshape.width request.source.basis.toList then
          let out := Reshape.relabel _ _ h ⟨a,bounded⟩
          let back := Reshape.relabel _ _ h.symm out
          s!"{out.val},{back.val}"
        else "-1,-1"
      let cs := (List.range 3).map fun reference =>
        let c := coefficient b reference
        s!"[{c.1},{c.2}]"
      s!"[{a},{b},{routed},[{String.intercalate "," cs}]]"
    IO.println s!"{name}|checked|{checked.visits}|[{String.intercalate "," values}]"
'''


def lean_request(req):
    def p(port):
        atoms = [f".{tag}" + (f" {n}" if tag in ("bits", "tuple") else "")
                 for tag, n in port["tokens"]]
        return (f'⟨{port["owner"]},#[{",".join(atoms)}],'
                f'#[{",".join(map(str, port["axes"]))}]⟩')
    return f'⟨{p(req["source"])},{p(req["target"])}⟩'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record", type=Path)
    args = parser.parse_args()
    rows = cases()
    source = PRELUDE
    for i, row in enumerate(rows):
        row["samples"] = samples(row["request"]) if row["status"] == "checked" else []
        source += (f'def case{i} : IO Unit := report {json.dumps(row["name"])} '
                   f'({lean_request(row["request"])}) ({lean_request(row["required"])}) '
                   f'{row["budget"]} {json.dumps(row["samples"])}\n')
    source += "def main : IO Unit := do\n" + "\n".join(f"  case{i}" for i in range(len(rows))) + "\n"
    commands, binary = build_and_run(source, args.record)
    results = {}
    for line in commands[-1]["stdout"].splitlines():
        name, *fields = line.split("|")
        assert name not in results, name
        results[name] = fields
    assert len(results) == len(rows)
    probes = 0
    for row in rows:
        status, *rest = results[row["name"]]
        assert status == row["status"], (row["name"], status, row["status"])
        if status != "checked":
            continue
        assert int(rest[0]) == charge(row["request"]) + charge(row["required"])
        actual = json.loads(rest[1])
        assert len(actual) == len(row["samples"])
        for labels, (a, b, routed, restored, coefficients) in zip(row["samples"], actual, strict=True):
            for side, value in [("source", a), ("target", b)]:
                expected, _ = encode_tree(tree(row["request"][side]["tokens"]), iter(labels))
                assert value == expected, (row["name"], side, labels, value, expected)
            assert a == b == routed == restored
            assert coefficients == [[(-1 if a % 2 else 1) * (a + 2 * r + 1), 3 * a - 5 * r]
                                    for r in range(3)]
            probes += 1
    paths = [ROOT / 'lean-kernel/QleisliKernel/Reshape.lean',
             ROOT / 'lean-kernel/QleisliKernel/Layout.lean',
             ROOT / 'lean-kernel/QleisliKernel/Hierarchical/Artifact.lean',
             Path(__file__).resolve(), ROOT / 'scripts/test_hierarchical_artifact.py']
    report = dict(format="qleisli.reshape-validation", version=1, status="passed",
                  cases=len(rows), accepted=sum(r["status"] == "checked" for r in rows),
                  basis_probes=probes, reference_coefficients=3 * probes,
                  maximum_dense_dimension=0, external_semantic_evidence=False,
                  binary_sha256=binary, harness_sha256=hashlib.sha256(source.encode()).hexdigest(),
                  source_sha256={str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                                 for p in paths}, results=results, commands=commands)
    if args.record:
        args.record.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k not in ("results", "commands")}))


if __name__ == "__main__":
    main()
