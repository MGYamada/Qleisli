#!/usr/bin/env python3
"""Seeded source/CLI differential checks against an independent complex oracle.

No simulator, extractor or numpy code is imported. This is a bounded regression
exercise, not the reviewer's unprovided 6000-case harness or a soundness proof.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import argparse
import cmath
import hashlib
import itertools
import json
import math
from pathlib import Path
import random
import subprocess
import tempfile

SEED = 20260930021
IMPORTS = """use std::quantum::{init0,h,x,z,t,cnot,toffoli,split,join};
use std::observe::{measure_z,reset};
unitary fn pa(q:Q<Bit>)->Q<Bit>{t(h(q))}
unitary fn pb(q:Q<Bit>)->Q<Bit>{z(x(q))}
unitary fn apply[static U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Apply(U){U(q)}
"""


def gate(state, name, axes, inverse=False, outer=None):
    result = [0j] * len(state)
    for label, amplitude in enumerate(state):
        if outer is not None and not (label >> outer) & 1:
            result[label] += amplitude
            continue
        target = axes[-1]
        bit = (label >> target) & 1
        if name == "h":
            result[label & ~(1 << target)] += amplitude / math.sqrt(2)
            result[label | (1 << target)] += (-1 if bit else 1) * amplitude / math.sqrt(2)
        elif name in {"x", "cnot", "toffoli"}:
            enabled = all((label >> control) & 1 for control in axes[:-1])
            result[label ^ (1 << target) if enabled else label] += amplitude
        else:
            angle = math.pi if name == "z" else (-1 if inverse else 1) * math.pi / 4
            result[label] += amplitude * cmath.exp(1j * angle * bit)
    return result


def execute(state, word, inverse=False, outer=None):
    for name, axes in reversed(word) if inverse else word:
        state = gate(state, name, axes, inverse=inverse, outer=outer)
    return state


def split_source(width):
    return ["", "let a=q;", "let (a,b)=split(q);",
            "let (ab,c)=split(q); let (a,b)=split(ab);"][width]


def join_source(width):
    return ["", "a", "join(a,b)", "join(join(a,b),c)"][width]


def reference_source(width, sequence):
    """Explicit gate word, with no static transforms or provider constructors."""
    names, lines = "abc", []
    for name, axes, inverse in sequence:
        args = [names[i] for i in axes]
        if name == "toffoli":
            lines.append(f"let (({args[0]},{args[1]}),{args[2]})=toffoli({','.join(args)});")
        elif name == "cnot":
            lines.append(f"let ({','.join(args)})=cnot({','.join(args)});")
        else:
            # T^-1 = T^7, with exact scalar phase retained.
            for _ in range(7 if name == "t" and inverse else 1):
                lines.append(f"let {args[0]}={name}({args[0]});")
    return split_source(width) + "".join(lines) + join_source(width)


def rotation_source(name, basis):
    return name if basis == "z" else (f"h({name})" if basis == "x" else
                                     f"h(adjoint(t,adjoint(t,{name})))")


def rotate(state, axis, basis):
    if basis == "y":
        state = execute(state, [("t", [axis]), ("t", [axis])], inverse=True)
    return gate(state, "h", [axis]) if basis != "z" else state


def project(state, axis, bit):
    return [value if (label >> axis) & 1 == bit else 0j for label, value in enumerate(state)]


def make_case(rng, index):
    width = 1 + index % 3
    names = "abc"[:width]
    ty = ["", "Bit", "(Bit,Bit)", "((Bit,Bit),Bit)"][width]
    word, lines = [], []
    constructors = [
        ("then_op(pa,pb)", [("h", [0]), ("t", [0]), ("x", [0]), ("z", [0])]),
        ("inverse_op(pa)", [("t_inverse", [0]), ("h", [0])]),
        ("repeat_op(2,pa)", [("h", [0]), ("t", [0])] * 2),
        ("conjugate_op(pa,pb)", [("t_inverse", [0]), ("h", [0]), ("x", [0]), ("z", [0]), ("h", [0]), ("t", [0])]),
    ]
    for step in range(rng.randrange(3, 9)):
        options = ["h", "x", "z", "t", "op"] + (["cnot"] if width > 1 else []) + (["toffoli"] if width == 3 else [])
        name = rng.choice(options)
        axes = rng.sample(range(width), 3 if name == "toffoli" else (2 if name == "cnot" else 1))
        args = [names[i] for i in axes]
        if name == "op":
            expression, sequence = constructors[(index + step) % len(constructors)]
            lines.append(f"let {args[0]}=apply[{expression}]({args[0]});")
            word.extend((gate_name, [axes[0]]) for gate_name, _ in sequence)
        elif name == "toffoli":
            lines.append(f"let (({args[0]},{args[1]}),{args[2]})=toffoli({','.join(args)});")
            word.append((name, axes))
        elif name == "cnot":
            lines.append(f"let ({','.join(args)})=cnot({','.join(args)});")
            word.append((name, axes))
        else:
            lines.append(f"let {args[0]}={name}({args[0]});")
            word.append((name, axes))
    inverse = index % 5 == 1
    count = index % 4 if index % 5 == 2 else 1
    sequence = [
        ("t" if name == "t_inverse" else name, axes, inverse ^ (name == "t_inverse"))
        for _ in range(count) for name, axes in (list(reversed(word)) if inverse else word)
    ]
    expression = "adjoint(w,q)" if inverse else f"repeat_static({count},w,q)"
    definitions = f"""unitary fn w(q:Q<{ty}>)->Q<{ty}>{{{split_source(width)}{''.join(lines)}{join_source(width)}}}
unitary fn u(q:Q<{ty}>)->Q<{ty}>{{{expression}}}
unitary fn identity(q:Q<{ty}>)->Q<{ty}>{{q}}
unitary fn reference(q:Q<{ty}>)->Q<{ty}>{{{reference_source(width, sequence)}}}
unitary fn checked(q:Q<{ty}>)->Q<{ty}>{{apply_contract(u,reference,q)}}
"""
    state = [complex(label == 0) for label in range(1 << width)]
    preparation = []
    for axis, name in enumerate(names):
        initial = rng.choice(["init0()", "x(init0())", "h(init0())", "t(h(init0()))"])
        preparation.append(f"let {name}={initial};")
        if "x(" in initial:
            state = gate(state, "x", [axis])
        if "h(" in initial:
            state = gate(state, "h", [axis])
        if "t(" in initial:
            state = gate(state, "t", [axis])
    coherent = index % 2 == 0
    observing = width == 3 and index % 2 == 1
    if coherent:
        preparation.append(f"let (r,q)=qif(h(init0()),{join_source(width)}){{0=>identity,1=>checked}};")
        state = [v / math.sqrt(2) for v in state] * 2
    else:
        preparation.append(f"let q=checked({join_source(width)});")
    for gate_name, axes, inv in sequence:
        state = gate(state, gate_name, axes, inverse=inv, outer=width if coherent else None)
    preparation.append(split_source(width))
    ensemble = [(state, [])]
    if observing:
        preparation.append("let m=measure_z(a); let a=init0(); let b=if m{x(b)}else{z(b)}; let c=reset(c);")
        ensemble = []
        for measured, reset in itertools.product(range(2), repeat=2):
            branch = project(state, 0, measured)
            if measured:
                branch = gate(branch, "x", [0])
            branch = gate(branch, "x" if measured else "z", [1])
            branch = project(branch, 2, reset)
            if reset:
                branch = gate(branch, "x", [2])
            ensemble.append((branch, [bool(measured)]))
    measurements = [(width, "r")] if coherent else []
    measurements += list(enumerate(names))
    bases = [rng.choice("zxy") for _ in measurements]
    outcomes = []
    if observing:
        outcomes.append("m")
    for (axis, name), basis in zip(measurements, bases):
        outcomes.append(f"measure_z({rotation_source(name, basis)})")
        ensemble = [(rotate(branch, axis, basis), bits) for branch, bits in ensemble]
    expected = {}
    for branch, prefix in ensemble:
        for label, value in enumerate(branch):
            bits = tuple(prefix + [bool((label >> axis) & 1) for axis, _ in measurements])
            expected[bits] = expected.get(bits, 0.0) + abs(value) ** 2
    arity = len(outcomes)
    result_type = "CBit" if arity == 1 else "(" + ",".join(["CBit"] * arity) + ")"
    result = outcomes[0] if arity == 1 else "(" + ",".join(outcomes) + ")"
    source = IMPORTS + definitions + f"observe fn main()->{result_type}{{{''.join(preparation)}{result}}}"
    return source, expected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("binary", type=Path)
    parser.add_argument("--cases", type=int, default=96)
    parser.add_argument("--seed", type=int, default=SEED)
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    if not 1 <= args.cases <= 10000:
        parser.error("cases must be in 1..10000")
    binary, rng = args.binary.resolve(), random.Random(args.seed)
    source_hash, max_error = hashlib.sha256(), 0.0
    with tempfile.TemporaryDirectory(prefix="qleisli-source-differential-") as directory:
        root = Path(directory)
        for index in range(args.cases):
            source, expected = make_case(rng, index)
            (root / "main.qli").write_text(source)  # Save before checking.
            source_hash.update(len(source.encode()).to_bytes(8, "big") + source.encode())
            run = subprocess.run([str(binary), "run", str(root), "--format=json"], capture_output=True, text=True, timeout=30)
            assert run.returncode == 0, f"seed={args.seed}, case={index}\n{source}\n{run.stdout}\n{run.stderr}"
            actual = {tuple(row["bits"]): row["probability"] for row in json.loads(run.stdout)["result"]["distribution"]}
            error = max(abs(actual.get(bits, 0.0) - expected.get(bits, 0.0)) for bits in actual.keys() | expected.keys())
            assert error < 1e-11, f"seed={args.seed}, case={index}, error={error}\n{source}\nactual={actual}\nexpected={expected}"
            max_error = max(max_error, error)
    report = dict(seed=args.seed, cases=args.cases, max_probability_error=max_error, tolerance=1e-11,
                  maximum_live_qubits=4, binary_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),
                  harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  ordered_sources_sha256=source_hash.hexdigest(),
                  scope="exact extractor comparison against separately expanded gate-word contracts; source/CLI probabilities with independent X/Y/Z, coherent control, classical branch and reset oracles; regressions, not general proof")
    if args.report:
        args.report.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, sort_keys=True))


if __name__ == "__main__":
    main()
