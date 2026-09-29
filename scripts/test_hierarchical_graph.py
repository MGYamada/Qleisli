#!/usr/bin/env python3
"""Native dependency schedules against an independent DFS and graph mutations.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
This checks graph scheduling, not external IR projection or quantum semantics.
"""
import argparse
import hashlib
import json
from pathlib import Path
import random
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def oracle(nodes, roots, order):
    count, edges = len(nodes), sum(map(len, nodes))
    visits = 10*count + 5*edges + 3*len(roots)
    if not 0 < count <= 100000 or not 0 < len(roots) <= count or edges > 1000000 or visits > 2000000:
        return "limit", None
    if sorted(order) != list(range(count)) or any(r >= count for r in roots):
        return "invalid_ir", None
    ranks = {node: index for index, node in enumerate(order)}
    if any(child >= count or ranks[child] >= ranks[parent]
           for parent, children in enumerate(nodes) for child in children):
        return "invalid_ir", None
    # DFS uses actual edges; it does not follow the proposed evaluation order.
    depths, seen = {}, set()
    def visit(node):
        seen.add(node)
        if node not in depths:
            depths[node] = 1 + max((visit(child) for child in nodes[node]), default=0)
        return depths[node]
    for node in range(count):
        visit(node)
    if max(depths.values()) > 256:
        return "limit", None
    seen.clear()
    def mark(node):
        if node not in seen:
            seen.add(node)
            for child in nodes[node]:
                mark(child)
    for root in roots:
        mark(root)
    if len(seen) != count:
        return "invalid_ir", None
    return "accepted", (count, edges, visits, max(depths.values()))


def suite():
    rows = [
        ("single", [[]], [0], [0]),
        ("forward-table-reference", [[1], []], [0], [1, 0]),
        ("shared-child", [[], [0, 0], [1, 1]], [2], [0, 1, 2]),
        ("unreachable", [[], []], [0], [0, 1]),
        ("self-dependency-even-in-unused-body", [[0]], [0], [0]),
        ("cycle", [[1], [0]], [0], [0, 1]),
        ("dangling", [[1]], [0], [0]),
        ("wrong-order", [[], [0]], [1], [1, 0]),
        ("duplicate-order", [[], [0]], [1], [0, 0]),
        ("missing-order", [[], [0]], [1], [0]),
        ("extra-order", [[], [0]], [1], [0, 1, 2]),
        ("invalid-order-index", [[], [0]], [1], [0, 2]),
        ("invalid-root", [[]], [1], [0]),
        ("empty-roots", [[]], [], [0]),
        ("empty-graph", [], [], []),
    ]
    rng = random.Random(9020)
    for case in range(64):
        count = rng.randrange(2, 65)
        original = [[]] + [[i-1] + [rng.randrange(i) for _ in range(rng.randrange(5))]
                          for i in range(1, count)]
        perm = list(range(count))
        rng.shuffle(perm)
        nodes = [[] for _ in range(count)]
        for old, children in enumerate(original):
            nodes[perm[old]] = [perm[c] for c in children]
        rows.append((f"permuted-{case}", nodes, [perm[-1]], perm))
        wrong = list(perm)
        wrong[0], wrong[1] = wrong[1], wrong[0]
        rows.append((f"dependency-before-body-{case}", nodes, [perm[-1]], wrong))
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record", type=Path)
    args = parser.parse_args()
    rows = suite()
    calls = [f'report {json.dumps(name)} #{json.dumps(nodes)} {json.dumps(roots)} #{json.dumps(order)}'
             for name, nodes, roots, order in rows]
    large = [
        ("max-nodes", "star 100000", "[99999]", "Array.range 100000", "accepted", (100000,99999,1499998,2)),
        ("too-many-nodes", "star 100001", "[100000]", "Array.range 100001", "limit", None),
        ("depth-256", "chain 256", "[255]", "Array.range 256", "accepted", (256,255,3838,256)),
        ("depth-257", "chain 257", "[256]", "Array.range 257", "limit", None),
        ("shared-exponential", "doubled 60", "[59]", "Array.range 60", "accepted", (60,118,1193,60)),
        ("last-work-budget", "#[[], List.replicate 399995 0]", "[1]", "#[0,1]", "accepted", (2,399995,1999998,2)),
        ("over-work-budget", "#[[], List.replicate 399996 0]", "[1]", "#[0,1]", "limit", None),
        ("over-reference-limit", "#[[], List.replicate 1000001 0]", "[1]", "#[0,1]", "limit", None),
        ("oversized-roots", "#[[]]", "List.replicate 1000001 0", "#[0]", "limit", None),
    ]
    calls += [f'report {json.dumps(name)} ({nodes}) ({roots}) ({order})'
              for name,nodes,roots,order,_,_ in large]
    source = '''import QleisliKernel.Hierarchical.Graph
open QleisliKernel.Hierarchical.Graph
def star (n : Nat) : Nodes := (Array.range n).map fun i => if i + 1 = n then List.range i else []
def chain (n : Nat) : Nodes := (Array.range n).map fun i => if i = 0 then [] else [i-1]
def doubled (n : Nat) : Nodes := (Array.range n).map fun i => if i = 0 then [] else [i-1,i-1]
def report (name : String) (nodes : Nodes) (roots : List Nat) (order : Array Nat) : IO Unit := do
  match check nodes roots order with
  | .error e => IO.println s!"{name}|{if e.kind == .limit then "limit" else "invalid_ir"}"
  | .ok s => IO.println s!"{name}|accepted|{s.stats.nodes}|{s.stats.references}|{s.stats.visits}|{s.stats.depth}"
''' + "\n".join(f"def case{i} : IO Unit := {call}" for i,call in enumerate(calls)) + "\n"
    groups = list(range(0, len(calls), 16))
    for first in groups:
        source += f"def group{first} : IO Unit := do\n" + \
            "\n".join(f"  case{i}" for i in range(first, min(first+16, len(calls)))) + "\n"
    source += "def main : IO Unit := do\n" + "\n".join(f"  group{i}" for i in groups) + "\n"
    commands = []
    with tempfile.TemporaryDirectory(prefix="qleisli-hierarchical-graph-") as directory:
        project = Path(directory)
        (project / "lean-toolchain").write_text((ROOT / "lean-kernel/lean-toolchain").read_text())
        (project / "lakefile.toml").write_text(
            'name = "hierarchical_graph_test"\nversion = "0.0.0"\n'
            'defaultTargets = ["graph-test"]\n[[require]]\nname = "qleisli_kernel"\n'
            f'path = {json.dumps(str(ROOT / "lean-kernel"))}\n'
            '[[lean_exe]]\nname = "graph-test"\nroot = "Main"\n')
        (project / "Main.lean").write_text(source)
        for command in (["lake", "build"], [str(project / ".lake/build/bin/graph-test")]):
            result = subprocess.run(command, cwd=project, capture_output=True, text=True, timeout=180)
            commands.append(dict(argv=command, exit_code=result.returncode,
                                 stdout=result.stdout, stderr=result.stderr))
            assert result.returncode == 0, commands[-1]
        binary_hash = hashlib.sha256((project / ".lake/build/bin/graph-test").read_bytes()).hexdigest()
    results = {}
    for line in commands[-1]["stdout"].splitlines():
        name, code, *stats = line.split("|")
        assert name not in results
        results[name] = (code, tuple(map(int, stats)) if stats else None)
    expected = {name: oracle(nodes,roots,order) for name,nodes,roots,order in rows}
    expected.update({name: (code,stats) for name,_,_,_,code,stats in large})
    assert results == expected, {name:(value,results.get(name)) for name,value in expected.items()
                                if results.get(name) != value}
    report = dict(format="qleisli.hierarchical-graph-validation", version=1,
                  cases=len(results), accepted=sum(code == "accepted" for code,_ in results.values()),
                  peak_nodes=100000, largest_checked_visits=1999998, dense_dimension=0,
                  binary_sha256=binary_hash, harness_sha256=hashlib.sha256(source.encode()).hexdigest(),
                  source_sha256={name:hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in (
                      "lean-kernel/QleisliKernel/Hierarchical/Graph.lean", "scripts/test_hierarchical_graph.py")},
                  results=results, commands=commands)
    if args.record:
        args.record.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k:v for k,v in report.items() if k not in {"results","commands"}}))


if __name__ == "__main__":
    main()
