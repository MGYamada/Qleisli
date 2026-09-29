#!/usr/bin/env python3
"""Native mutation/oracle checks for the actual typed QFT graph projection.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
No external schema or artifact format is enabled by this test harness.
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import random
import subprocess
import tempfile

from test_lean_interference import ROOT, literal
from test_lean_qft import template

FIXTURE = ROOT / "tests/fixtures/lean_qft_graph"


def case(width, calls=False, identities=0):
    nodes = []
    def add(kind, **fields):
        nodes.append(dict(kind=kind, **fields))
        return len(nodes) - 1
    prefix = None
    if identities:
        prefix = add("identity")
        for _ in range(identities - 1):
            prefix = add("sequence", first=prefix, second=prefix)
    root = None
    for gate in template(width):
        node = add("gate", gate=gate)
        if calls:
            node = add("call", child=node)
        root = node if root is None else add("sequence", first=root, second=node)
    if prefix is not None:
        root = add("sequence", first=prefix, second=root)
    permutation = add("permute", axes=list(reversed(range(width))))
    root = add("sequence", first=root, second=permutation)
    return dict(width=width, entry=root, nodes=nodes)


def body_literal(node, width):
    kind = node["kind"]
    if kind == "identity":
        return ".identity"
    if kind == "gate":
        return ".gate (" + literal([node["gate"]])[1:-1] + ")"
    if kind == "permute":
        return ".permute " + json.dumps(node["axes"])
    if kind == "sequence":
        return f'.sequence {node["first"]} {node["second"]}'
    port = f"QftGraph.interface {width}"
    return f'.call {node["child"]} ({node.get("input", port)}) ({node.get("output", port)})'


def case_literal(item, probes):
    width = item["width"]
    nodes = []
    for node in item["nodes"]:
        signature = node.get("signature", f"QftGraph.boundary {width}")
        nodes.append("⟨" + signature + ", " + body_literal(node, width) + "⟩")
    probe_literal = "[" + ",".join(f"({x},{y})" for x, y in probes) + "]"
    return f'({width}, {item["entry"]}, [' + ",".join(nodes) + f"], {probe_literal})"


def direct(item, input_value, choices):
    """Follow literal children and physical data permutations; ignore all summaries."""
    width = item["width"]
    bits = [(input_value >> i) & 1 for i in range(width)]
    phase = count = 0
    def visit(index):
        nonlocal bits, phase, count
        node = item["nodes"][index]
        kind = node["kind"]
        if kind == "identity":
            return
        if kind == "sequence":
            visit(node["first"])
            visit(node["second"])
        elif kind == "call":
            visit(node["child"])
        elif kind == "permute":
            bits = [bits[i] for i in node["axes"]]
        else:
            gate, data = node["gate"]
            if gate == "h":
                output = (choices >> count) & 1
                phase += 128 * bits[data] * output
                bits[data] = output
                count += 1
            else:
                phase += sum(t for t, axes in data if all(bits[i] for i in axes))
    visit(item["entry"])
    return sum(bit << i for i, bit in enumerate(bits)), phase % 256, count


def suite():
    cases = []
    def add(name, item, accepted, probes=True):
        width = item["width"]
        pairs = []
        if accepted and probes:
            if width <= 3:
                pairs = [(x, y) for x in range(1 << width) for y in range(1 << width)]
            else:
                rng = random.Random(9100 + width)
                pairs = [(rng.randrange(1 << width), rng.randrange(1 << width)) for _ in range(32)]
        cases.append((name, item, accepted, pairs))
    for width in range(1, 9):
        add(f"qft-{width}", case(width), True)
        add(f"calls-{width}", case(width, calls=True), True)
        add(f"shared-identity-{width}", case(width, calls=True, identities=5), True)
    large = case(8, calls=True, identities=60)
    add("no-expansion-2^59", large, True, probes=False)
    base = case(3, calls=True)
    def mutate(name, change):
        item = copy.deepcopy(base)
        change(item)
        add(name, item, False)
    def modify_node(item, kind, f):
        f(next(n for n in item["nodes"] if n["kind"] == kind))
    mutate("wrong-final-permutation", lambda c: modify_node(c, "permute", lambda n: n.update(axes=[0, 1, 2])))
    mutate("aliased-final-axes", lambda c: modify_node(c, "permute", lambda n: n.update(axes=[0, 0, 2])))
    mutate("outside-final-axis", lambda c: modify_node(c, "permute", lambda n: n.update(axes=[0, 1, 3])))
    mutate("wrong-h-axis", lambda c: modify_node(c, "gate", lambda n: n.update(gate=("h", 0))))
    mutate("outside-h-axis", lambda c: modify_node(c, "gate", lambda n: n.update(gate=("h", 3))))
    def phase_change(item, ticks):
        node = next(n for n in item["nodes"] if n["kind"] == "gate" and n["gate"][0] == "p")
        node["gate"] = ("p", [(ticks, node["gate"][1][0][1])])
    mutate("wrong-phase-sign", lambda c: phase_change(c, 192))
    mutate("invalid-phase-tick", lambda c: phase_change(c, 256))
    def swapped(item):
        nodes = [n for n in item["nodes"] if n["kind"] == "call"]
        nodes[0]["child"], nodes[1]["child"] = nodes[1]["child"], nodes[0]["child"]
        # Move both calls after both leaves so all changed dependencies remain prior.
        item["nodes"][1], item["nodes"][2] = item["nodes"][2], item["nodes"][1]
        for n in item["nodes"]:
            for key in ("child", "first", "second"):
                if key in n:
                    n[key] = {1: 2, 2: 1}.get(n[key], n[key])
    mutate("changed-valid-call-dependencies", swapped)
    for direction in ("input", "output"):
        mutate(f"wrong-call-{direction}-axes", lambda c, d=direction: modify_node(c, "call",
            lambda n: n.update({d: "[⟨[.bits 3], [2,1,0]⟩]"})))
    root_sig = "QftGraph.boundary 3"
    changes = {
        "observe-effect": f"{{ {root_sig} with effect := .observe }}",
        "iso-effect": f"{{ {root_sig} with effect := .iso }}",
        "classical-input": f"{{ {root_sig} with classicalInputs := [0] }}",
        "classical-output": f"{{ {root_sig} with classicalOutputs := [0] }}",
        "flat-tuple-type": f"{{ {root_sig} with inputs := [⟨[.tuple 3,.bit,.bit,.bit],[0,1,2]⟩] }}",
        "nested-tuple-type": f"{{ {root_sig} with inputs := [⟨[.tuple 2,.tuple 2,.bit,.bit,.bit],[0,1,2]⟩] }}",
        "extra-bits0-owner": f"{{ {root_sig} with outputs := QftGraph.interface 3 ++ [⟨[.bits 0],[]⟩] }}",
        "missing-owner": f"{{ {root_sig} with outputs := [] }}",
        "aliased-input-axis": f"{{ {root_sig} with inputs := [⟨[.bits 3],[0,0,2]⟩] }}",
        "changed-output-order": f"{{ {root_sig} with outputs := [⟨[.bits 3],[2,1,0]⟩] }}",
    }
    for name, signature in changes.items():
        for index in (0, base["entry"]):
            mutate(f"{name}-node{index}", lambda c, i=index, s=signature: c["nodes"][i].update(signature=s))
    mutate("cycle", lambda c: c["nodes"][0].update(kind="call", child=c["entry"]))
    mutate("dangling", lambda c: modify_node(c, "call", lambda n: n.update(child=999)))
    mutate("dead-node", lambda c: c["nodes"].append(dict(kind="identity")))
    mutate("bad-entry", lambda c: c.update(entry=len(c["nodes"])))
    mutate("permutation-before-gates", lambda c: c["nodes"][-1].update(
        first=c["nodes"][-1]["second"], second=c["nodes"][-1]["first"]))
    for width in (0, 9):
        bad = copy.deepcopy(base)
        bad["width"] = width
        add(f"width-{width}", bad, False)
    for depth in (64, 65):
        item = case(1)
        item["nodes"] = [dict(kind="gate", gate=("h", 0))]
        for _ in range(depth - 2):
            item["nodes"].append(dict(kind="call", child=len(item["nodes"]) - 1))
        last = len(item["nodes"]) - 1
        item["nodes"].extend([dict(kind="permute", axes=[0]),
                              dict(kind="sequence", first=last, second=last + 1)])
        item["entry"] = len(item["nodes"]) - 1
        add(f"depth-{depth}", item, depth == 64)
    for count in (255, 256, 257):
        nodes = [dict(kind="identity") for _ in range(126)]
        level = list(range(126))
        while len(level) > 1:
            next_level = []
            for i in range(0, len(level), 2):
                if i + 1 == len(level):
                    next_level.append(level[i])
                else:
                    nodes.append(dict(kind="sequence", first=level[i], second=level[i+1]))
                    next_level.append(len(nodes) - 1)
            level = next_level
        root = level[0]
        for _ in range(count - 255):
            nodes.append(dict(kind="call", child=root))
            root = len(nodes) - 1
        h_node = len(nodes)
        nodes.extend([dict(kind="gate", gate=("h", 0)),
                      dict(kind="sequence", first=root, second=h_node),
                      dict(kind="permute", axes=[0]),
                      dict(kind="sequence", first=h_node+1, second=h_node+2)])
        assert len(nodes) == count
        add(f"nodes-{count}", dict(width=1, entry=count-1, nodes=nodes), count <= 256)
    too_many = case(8)
    permutation = too_many["nodes"].pop()
    old_entry = permutation["first"]
    h_node = len(too_many["nodes"])
    too_many["nodes"].extend([dict(kind="gate", gate=("h", 0)),
        dict(kind="sequence", first=old_entry, second=h_node),
        dict(kind="sequence", first=h_node+1, second=permutation["second"])])
    too_many["entry"] = len(too_many["nodes"]) - 1
    add("37-gates", too_many, False)
    return cases


def native(cases, log):
    with tempfile.TemporaryDirectory(prefix="qleisli-qft-graph-") as directory:
        project = Path(directory)
        (project / "lean-toolchain").write_text((ROOT / "lean-kernel/lean-toolchain").read_text())
        (project / "lakefile.toml").write_text(
            'name = "qft_graph_test"\nversion = "0.0.0"\ndefaultTargets = ["graph-test"]\n'
            '[[require]]\nname = "qleisli_kernel"\npath = ' + json.dumps(str(ROOT / "lean-kernel")) +
            '\n[[lean_exe]]\nname = "graph-test"\nroot = "Main"\n')
        rows = [case_literal(item, probes) for _, item, _, probes in cases]
        (project / "Main.lean").write_text('''import QleisliKernel.QftGraph
open QleisliKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def cases : List (Nat × Nat × List QftGraph.Definition × List (Nat × Nat)) := [
''' + ",\n".join(rows) + ''']
def bits (value : Nat) : Interference.Bits := fun i => value / 2^i % 2 == 1
def main : IO Unit := do
  for (width, entry, definitions, probes) in cases do
    match QftGraph.check definitions entry width with
    | none =>
      let metadata := definitions.all (QftGraph.validDefinition width)
      IO.println ("reject," ++ toString (QftGraph.preflight definitions entry).isSome ++ "," ++
        toString metadata ++ "," ++ toString (QftGraph.evaluateFrom definitions #[]).isSome)
    | some receipt =>
      let s := receipt.stats
      let mut line := String.intercalate "," ([s.nodes,s.references,s.copiedGates,s.depth,s.expandedActions].map toString)
      if !probes.isEmpty then
        let some execute := QftGraph.denote definitions entry | throw (IO.userError "missing semantics")
        for (x,y) in probes do
          let state := execute (bits y) (PathSum.realize width (PathSum.initial width) (bits x) (bits y))
          let output := (List.range width).foldl (fun n i => n + if state.bits i then 2^i else 0) 0
          line := line ++ "#" ++ String.intercalate "," ([output,state.phase,state.hadamards].map toString)
      IO.println line
''')
        build = subprocess.run(["lake", "build"], cwd=project, capture_output=True, text=True, timeout=240)
        log.append(dict(command=["lake", "build"], cwd="temporary native QFT graph harness",
                        exit=build.returncode, stdout=build.stdout, stderr=build.stderr))
        assert build.returncode == 0, build.stdout + build.stderr
        binary = project / ".lake/build/bin/graph-test"
        run = subprocess.run([str(binary)], capture_output=True, text=True, timeout=30)
        log.append(dict(command=["graph-test"], exit=run.returncode, stderr=run.stderr,
                        executable_sha256=hashlib.sha256(binary.read_bytes()).hexdigest()))
        assert run.returncode == 0, run.stderr
        lines = run.stdout.splitlines()
        assert len(lines) == len(cases), (len(lines), len(cases))
        return lines


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record", type=Path)
    args = parser.parse_args()
    cases = suite()
    log = []
    lines = native(cases, log)
    decisions, comparisons, largest = [], 0, None
    for (name, item, accepted, probes), line in zip(cases, lines):
        assert (not line.startswith("reject,")) == accepted, (name, line)
        row = dict(name=name, accepted=accepted)
        if not accepted:
            preflight, metadata, evaluation = [value == "true" for value in line.split(",")[1:]]
            row.update(preflight=preflight, metadata=metadata, evaluation=evaluation)
            if name in {"wrong-final-permutation", "wrong-h-axis", "wrong-phase-sign",
                        "changed-valid-call-dependencies"}:
                assert preflight and metadata and evaluation, (name, line)
            if name == "permutation-before-gates":
                assert preflight and metadata and not evaluation
        if accepted:
            fields = line.split("#")
            nodes, refs, copies, depth, expanded = map(int, fields[0].split(","))
            row.update(nodes=nodes, references=refs, copied_gates=copies, depth=depth, expanded_actions=expanded)
            assert nodes == len(item["nodes"])
            assert len(fields) == len(probes) + 1
            for (x, y), encoded in zip(probes, fields[1:]):
                value = tuple(map(int, encoded.split(",")))
                expected = direct(item, x, y)
                assert value == expected, (name, x, y, value, expected)
                assert value == (y, ((1 << (8-item["width"])) * x * y) % 256, item["width"])
                comparisons += 1
            if name == "no-expansion-2^59":
                largest = row
                assert expanded == 2**59 + 37
                assert nodes < 256 and depth <= 64
        decisions.append(row)
    report = dict(native_decisions=len(cases), accepted=sum(c[2] for c in cases),
                  graph_path_comparisons=comparisons, runtime_dense_dimension=0,
                  sharing=largest, decisions=decisions, commands=log,
                  source_sha256={str(p): hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in
                      [Path("lean-kernel/QleisliKernel/QftGraph.lean"), Path("lean/Qleisli/QftGraph.lean"),
                       Path("scripts/test_lean_qft_graph.py")]})
    if args.record:
        args.record.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Typed QFT graph: {len(cases)} native decisions, {comparisons} independent literal paths; dense dimension 0")


if __name__ == "__main__":
    main()
