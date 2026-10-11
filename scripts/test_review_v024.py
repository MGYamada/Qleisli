#!/usr/bin/env python3
"""Independent complex target oracle for the 0.2.4 export review.

Decode only the emitted twelve-gate terminal vocabulary; no Qleisli arithmetic,
simulator, importer or matrix reference is reused. Check every complex column,
including scalar phase, output axes and clean synthesis workspace. This is
finite validation, not a transformation proof or hardware execution.
"""
import argparse
import cmath
import math
from pathlib import Path
import re
import subprocess
import tempfile
import sys

sys.dont_write_bytecode = True

IMPORTS = "use std::quantum::{init0,h,x,z,t,s,sdg,tdg,id,phase_eighth,split,join}; use std::observe::measure_z;"


def decode(text):
    width = int(re.search(r"qubit\[(\d+)\] q;", text)[1])
    gates, outputs = [], []
    for line in text.splitlines():
        match = re.fullmatch(r"(h|x|y|z|s|sdg|t|tdg|cx|cz|swap|ccx) (.*);", line)
        if match:
            axes = [int(index) for index in re.findall(r"q\[(\d+)\]", match[2])]
            if match[2] != ", ".join(f"q[{axis}]" for axis in axes):
                raise AssertionError("unsupported emitted operands")
            gates.append((match[1], axes))
        elif re.fullmatch(r"c\[\d+\] = measure q\[\d+\];", line):
            outputs.append(int(re.search(r"measure q\[(\d+)\]", line)[1]))
        elif line and line != 'OPENQASM 3.0;' and line != 'include "stdgates.inc";' and line != 'reset q;' and not re.fullmatch(r"(qubit|bit)\[\d+\] [qc];", line):
            raise AssertionError(f"unknown target statement: {line}")
    return width, gates, outputs


def simulate(width, gates):
    state = [0j] * (1 << width)
    state[0] = 1
    omega = cmath.exp(1j * math.pi / 4)
    for gate, axes in gates:
        result = [0j] * len(state)
        for label, amplitude in enumerate(state):
            bits = [(label >> axis) & 1 for axis in axes]
            dest, phase = label, 1
            if gate == "h":
                result[label & ~(1 << axes[0])] += amplitude / math.sqrt(2)
                result[label | (1 << axes[0])] += amplitude * (-1 if bits[0] else 1) / math.sqrt(2)
                continue
            if gate in ("x", "y"):
                dest ^= 1 << axes[0]
                if gate == "y":
                    phase = -1j if bits[0] else 1j
            elif gate in ("z", "s", "sdg", "t", "tdg"):
                phase = omega ** ({"z": 4, "s": 2, "sdg": 6, "t": 1, "tdg": 7}[gate] * bits[0])
            elif gate in ("cx", "ccx"):
                if all(bits[:-1]):
                    dest ^= 1 << axes[-1]
            elif gate == "cz":
                phase = -1 if all(bits) else 1
            elif gate == "swap":
                if bits[0] != bits[1]:
                    dest ^= (1 << axes[0]) | (1 << axes[1])
            result[dest] += phase * amplitude
        state = result
    return state


def program(width, body, column):
    names = ["a", "b", "c"][:width]
    prepare = "".join(f"let {name}={'x(init0())' if (column >> i)&1 else 'init0()'};" for i, name in enumerate(names))
    join = "join(a,b)" if width == 2 else "join(join(a,b),c)"
    split = "let (a,b)=split(q);" if width == 2 else "let (ab,c)=split(q);let (a,b)=split(ab);"
    result = "(measure_z(a),measure_z(b))" if width == 2 else "((measure_z(a),measure_z(b)),measure_z(c))"
    result_ty = "(Bit,Bit)" if width == 2 else "((Bit,Bit),Bit)"
    return f"{IMPORTS}\n{body}\nobserve fn main()->{result_ty}{{{prepare}let q=apply({join});{split}{result}}}"


def check_case(example, width, body, reference, parse=None, check_qir=None):
    probes, largest = 0, 0
    with tempfile.TemporaryDirectory(prefix="qleisli-review-target-") as directory:
        root = Path(directory)
        (root / "Qargo.toml").write_text('schema-version=2\n[qrate]\nedition="2026"\n')
        for column in range(1 << width):
            (root / "main.qli").write_text(program(width, body, column))
            output = subprocess.run([str(example), "qli-to-qasm", str(root)], capture_output=True, text=True, timeout=20)
            if output.returncode:
                raise AssertionError(output.stderr)
            if parse is not None:
                parse(output.stdout)
            target_width, gates, axes = decode(output.stdout)
            if column == 0 and check_qir is not None:
                qir = subprocess.run([str(example), "qli-to-qir", str(root)], capture_output=True, text=True, timeout=20)
                if qir.returncode:
                    raise AssertionError(qir.stderr)
                check_qir(qir.stdout, target_width, width)
            largest = max(largest, target_width)
            state = simulate(target_width, gates)
            if len(axes) != width or len(set(axes)) != width:
                raise AssertionError("output interface changed")
            for row in range(1 << width):
                index = sum(((row >> i) & 1) << axis for i, axis in enumerate(axes))
                if abs(state[index] - reference(row, column)) > 2e-12:
                    raise AssertionError(f"wrong complex coefficient at ({row},{column}): {state[index]} != {reference(row,column)}")
                probes += 1
            hidden = ((1 << target_width) - 1) ^ sum(1 << axis for axis in axes)
            if any(abs(amplitude) > 2e-12 for label, amplitude in enumerate(state) if label & hidden):
                raise AssertionError("synthesis workspace did not return to zero")
    return probes, largest


def cases():
    omega = cmath.exp(1j * math.pi / 4)
    for width in [2, 3]:
        size = 1 << width
        ty = "Q<(Bit,Bit)>" if width == 2 else "Q<((Bit,Bit),Bit)>"
        yield f"QFT{width}", width, f"use std::transform::qft{width}; unitary fn apply(q:{ty})->{ty}{{qft{width}(q)}}", lambda row, col, size=size: cmath.exp(2j * math.pi * row * col / size) / math.sqrt(size)
    for negative in [False, True]:
        for gate, k in [("s", 2), ("sdg", 6), ("t", 1), ("tdg", 7), ("phase_eighth", 1)]:
            arms = f"0=>{gate},1=>id" if negative else f"0=>id,1=>{gate}"
            body = f"unitary fn apply(q:Q<(Bit,Bit)>)->Q<(Bit,Bit)>{{let (a,b)=split(q);let (a,b)=qif(a,b){{{arms}}};join(a,b)}}"
            def ref(row, col, negative=negative, k=k, scalar=gate == "phase_eighth"):
                active = bool(col & 1) != negative and (scalar or bool(col & 2))
                return (omega ** k if active else 1) if row == col else 0
            yield f"{'negative' if negative else 'positive'}-{gate}", 2, body, ref
        arms = "0=>h,1=>id" if negative else "0=>id,1=>h"
        body = f"unitary fn apply(q:Q<(Bit,Bit)>)->Q<(Bit,Bit)>{{let (a,b)=split(q);let (a,b)=qif(a,b){{{arms}}};join(a,b)}}"
        def ref_h(row, col, negative=negative):
            if (row & 1) != (col & 1):
                return 0
            if bool(col & 1) == negative:
                return int(row == col)
            return (-1 if row & col & 2 else 1) / math.sqrt(2)
        yield f"{'negative' if negative else 'positive'}-H", 2, body, ref_h
    body = "unitary fn apply(q:Q<(Bit,Bit)>)->Q<(Bit,Bit)>{let (a,b)=split(q);let (a,b)=qif(a,b){0=>tdg,1=>t};join(a,b)}"
    yield "both-phase-arms", 2, body, lambda row, col: (omega ** ((1 if col & 1 else -1) * bool(col & 2))) if row == col else 0
    body = """unitary fn inner(q:Q<(Bit,Bit)>)->Q<(Bit,Bit)>{let (b,c)=split(q);let (b,c)=qif(b,c){0=>id,1=>t};join(b,c)}
        unitary fn apply(q:Q<((Bit,Bit),Bit)>)->Q<((Bit,Bit),Bit)>{let (ab,c)=split(q);let (a,b)=split(ab);let (a,bc)=qif(a,join(b,c)){0=>id,1=>inner};let (b,c)=split(bc);join(join(a,b),c)}"""
    yield "nested-controlled-T", 3, body, lambda row, col: (omega if col == 7 else 1) if row == col else 0


def check_all(example, parse=None, check_qir=None):
    results = []
    for name, width, body, reference in cases():
        probes, largest = check_case(example, width, body, reference, parse, check_qir)
        if name == "QFT2" and largest != 2:
            raise AssertionError("even controlled phases acquired unnecessary workspace")
        if name == "both-phase-arms" and largest != 3:
            raise AssertionError("clean conjunction workspace was not reused across arms")
        results.append((name, probes, largest))
    return results


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("example", type=Path)
    options = parser.parse_args()
    results = check_all(options.example.resolve())
    print(f"{len(results)} target cases; {sum(row[1] for row in results)} complex entries; maximum {max(row[2] for row in results)} physical qubits; phases/axes/clean workspace agree")
