#!/usr/bin/env python3
"""Validate the frozen three-source intake and finite QLI translation semantics.

No upstream frameworks are imported or executed. Reference states are computed
from mathematical contracts, independently of QLI lowering, IR and simulation.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import argparse
import cmath
import datetime
from concurrent.futures import ThreadPoolExecutor
from collections import Counter
import hashlib
import json
import math
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
CORPUS = ROOT / "corpus"
APPROVED = {
    "quantum_katas": ("microsoft/QuantumKatas", "MIT"),
    "qualtran": ("quantumlib/Qualtran", "Apache-2.0"),
    "pennylane_demos": ("PennyLaneAI/demos", "Apache-2.0"),
}
TOLERANCE = 1e-11
IMPORTS = """use std::quantum::init0;
use std::quantum::h;
use std::quantum::x;
use std::quantum::t;
use std::quantum::cnot;
use std::quantum::join;
use std::quantum::split;
use std::observe::measure_z;
"""


def require(condition, message):
    if not condition:
        raise ValueError(message)


def local(base, relative):
    path = (base / relative).resolve()
    require(path.is_relative_to(base.resolve()), f"path escapes intake: {relative}")
    return path


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_manifest(corpus=CORPUS):
    manifest = json.loads((corpus / "manifest.json").read_text())
    require(manifest["format"] == 1, "unsupported corpus format")
    require({s["id"] for s in manifest["sources"]} == set(APPROVED), "closed source set changed")
    require(len(manifest["sources"]) == 3, "duplicate source")
    require((corpus / manifest["policy"]).is_file(), "missing adopted policy")
    inventoried = set()
    by_source = {}
    for source in manifest["sources"]:
        key = source["id"]
        require((source["repository"], source["license"]) == APPROVED[key], f"unapproved source/license: {key}")
        require(len(source["commit"]) == 40 and all(c in "0123456789abcdef" for c in source["commit"]), "unpinned source")
        paths = set()
        for entry in source["files"]:
            path = local(corpus, entry["local"])
            require(path.is_relative_to(corpus.resolve() / "upstream" / key), "wrong source directory")
            require(entry["path"] not in paths and path not in inventoried, "duplicate upstream file")
            paths.add(entry["path"])
            inventoried.add(path)
            require(sha256(path) == entry["sha256"], f"upstream hash mismatch: {entry['local']}")
        require("LICENSE" in paths and "README.md" in paths, f"missing license/permission record: {key}")
        by_source[key] = source
    actual = {p.resolve() for p in (corpus / "upstream").rglob("*") if p.is_file() and p.name != ".DS_Store"}
    require(actual == inventoried, "unrecorded or missing upstream file")
    ids = set()
    for case in manifest["cases"]:
        require(case["id"] not in ids, "duplicate case")
        ids.add(case["id"])
        source = by_source[case["source"]]
        require(case["license"] == source["license"], "translation license mismatch")
        require(case["upstream_path"] in {f["path"] for f in source["files"]}, "missing original source")
        require(bool(case["contract"]) and bool(case["limitations"]) and bool(case["symbol"]), "missing translation contract")
        project = local(corpus, case["project"])
        require(project.is_relative_to(corpus.resolve() / case["source"]), "wrong translation directory")
        for name in ["main.qli", "kernel.qli"]:
            text = (project / name).read_text()
            require(f"SPDX-License-Identifier: {case['license']}" in text, f"missing license: {case['id']}/{name}")
            require(f"/{source['commit']}/{case['upstream_path']}" in text, "missing pinned source attribution")
            require("translation/modifications" in text, "missing modification notice")
            if case["source"] == "quantum_katas":
                require("Copyright (c) Microsoft Corporation" in text, "lost Microsoft attribution")
            if case["source"] == "qualtran":
                require("Google LLC" in text, "lost Google attribution")
        require((project / "README.md").is_file(), "missing case explanation")
    # The 0.2.4 small-system extension reuses the reviewed frozen inputs.
    require(Counter(c["source"] for c in manifest["cases"]) == Counter({k: 16 for k in APPROVED}), "reviewed case inventory changed")
    projects = {str(p.parent.relative_to(corpus)) for key in APPROVED for p in (corpus / key).rglob("main.qli")}
    require(projects == {c["project"] for c in manifest["cases"]}, "unrecorded project")
    # Sized authoring experiments reuse the same frozen inputs, with a distinct
    # execution path; they do not silently increase the finite production cases.
    sized = manifest.get("sized_experiments", [])
    sized_sources = set()
    for case in sized:
        require(case["id"] not in ids, "duplicate sized case")
        ids.add(case["id"])
        require(case["source"] in by_source, "unapproved sized source")
        source = by_source[case["source"]]
        require(case["license"] == source["license"], "sized translation license mismatch")
        require(case["upstream_path"] in {f["path"] for f in source["files"]}, "missing sized original")
        require(case["status"] == "experimental-source-path" and bool(case["contract"]) and
                bool(case["limitations"]), "missing sized scope")
        path = local(corpus, case["file"])
        require(path.is_relative_to((corpus / "sized").resolve()) and path not in sized_sources,
                "duplicate or misplaced sized source")
        sized_sources.add(path)
        require(sha256(path) == case["sha256"], "sized source hash mismatch")
        content = path.read_text()
        require(f"SPDX-License-Identifier: {case['license']}" in content and
                "translation/modifications" in content, "missing sized license/modification notice")
        require(("Microsoft Corporation" if case["source"] == "quantum_katas" else "Google LLC")
                in content, "lost sized attribution")
    # Original Qleisli wrappers compose the pinned algorithms; they are not a
    # fourth upstream source or a translation attributed to a different author.
    compositions = manifest.get("sized_local_compositions", [])
    local_sources = set()
    for case in compositions:
        require(set(case) == {"id", "origin", "file", "license", "sha256",
                              "dependencies", "contract", "limitations"},
                "unknown local composition fields")
        require(case["id"] not in ids, "duplicate local composition")
        ids.add(case["id"])
        require(case["origin"] == "qleisli-authored-local-composition" and
                case["license"] == "Apache-2.0", "invalid local composition origin/license")
        require(bool(case["contract"]) and bool(case["limitations"]), "missing local composition scope")
        path = local(corpus, case["file"])
        require(path.is_relative_to((corpus / "sized").resolve()) and
                path not in sized_sources | local_sources, "duplicate or misplaced local composition")
        local_sources.add(path)
        require(sha256(path) == case["sha256"], "local composition hash mismatch")
        text = path.read_text()
        require("SPDX-License-Identifier: Apache-2.0" in text and
                "Copyright 2026 Masahiko G. Yamada" in text, "missing local composition attribution")
    for case in compositions:
        require(isinstance(case["dependencies"], list) and
                len(set(case["dependencies"])) == len(case["dependencies"]) and
                all(local(corpus, dep) in sized_sources | local_sources for dep in case["dependencies"]),
                "unregistered local composition dependency")
    require(sized_sources | local_sources == {p.resolve() for p in (corpus / "sized").rglob("*.qli")},
            "unrecorded sized source")
    session_paths = manifest["authoring_sessions"]
    require(len(set(session_paths)) == len(session_paths), "duplicate authoring session")
    require({local(corpus, p) for p in session_paths} ==
            {p.resolve() for p in (corpus / "authoring").rglob("session.json")},
            "unrecorded authoring session")
    recorded_sources = set()
    for session_path in session_paths:
        session_file = local(corpus, session_path)
        session = json.loads(session_file.read_text())
        require(session["kind"] == "informed_first_attempt" and bool(session["context"]), "missing authoring context")
        require(bool(session["attempts"]), "missing authoring attempt")
        for attempt in session["attempts"]:
            base = local(session_file.parent, attempt["id"])
            require({str(p.relative_to(base)) for p in base.rglob("*.qli")} == set(attempt["sha256"]), "snapshot inventory changed")
            for rel, digest in attempt["sha256"].items():
                require(sha256(local(base, rel)) == digest, f"authoring snapshot changed: {attempt['id']}/{rel}")
            # Historical observations cover their own frozen projects, not later additions.
            attempted = {str(Path(p).parent) for p in attempt["sha256"]}
            require(bool(attempted) and attempted <= projects, "unregistered authoring project")
            require(bool(attempt["observations"]), "unobserved authoring attempt")
            for record in attempt["observations"]:
                observation = json.loads(local(session_file.parent, record).read_text())
                if "results" in observation:
                    results = observation["results"]
                    require(len(results) == len(attempted) and
                            {r.get("project", r.get("case")) for r in results} == attempted,
                            "incomplete authoring check")
                    for result in results:
                        output = json.loads(result["stdout"])
                        require((result["exit_code"] == 0) == (output["outcome"] == "ok"), "contradictory observation")
        latest = session["attempts"][-1]
        for rel, digest in latest["sha256"].items():
            require(rel not in recorded_sources, "duplicate current authoring source")
            recorded_sources.add(rel)
            require(sha256(local(corpus, rel)) == digest, f"current source differs from latest attempt: {rel}")
    require(recorded_sources == {str(p.relative_to(corpus)) for project in projects
                                for p in (corpus / project).glob("*.qli")},
            "current sources missing authoring snapshots")
    faults = json.loads((corpus / "semantic_faults/manifest.json").read_text())
    require(faults["format"] == 1, "unsupported semantic fault format")
    fault_projects = set()
    for fault in faults["cases"]:
        require(fault["reference"] in ids and bool(fault["reason"]), "unregistered semantic fault reference")
        project = local(corpus, fault["project"])
        require(project.is_relative_to((corpus / "semantic_faults").resolve()) and
                project not in fault_projects, "duplicate or misplaced semantic fault")
        fault_projects.add(project)
        case = next(c for c in manifest["cases"] if c["id"] == fault["reference"])
        for name in ["kernel.qli", "main.qli"]:
            text = (project / name).read_text()
            require(f"SPDX-License-Identifier: {case['license']}" in text,
                    "semantic fault lost original license")
    require(fault_projects == {p.parent.resolve() for p in (corpus / "semantic_faults").rglob("main.qli")},
            "unrecorded semantic fault project")
    return manifest


def tuple_of(items, join=False):
    items = list(items)
    value = items[0]
    for item in items[1:]:
        value = f"join({value}, {item})" if join else f"({value}, {item})"
    return value


def split_register(n, register="q"):
    if n == 1:
        return f"let w0 = {register};\n"
    result = ""
    for i in reversed(range(1, n)):
        rest = "w0" if i == 1 else f"part{i}"
        result += f"let ({rest}, w{i}) = split({register});\n"
        register = rest
    return result


def measure(wire, basis):
    if basis == "x":
        wire = f"h({wire})"
    elif basis == "y":
        wire = f"h(t(t(t(t(t(t({wire})))))))"
    return f"measure_z({wire})"


def driver(n, column, row=None, axis="x"):
    """Probe an entry U[row,column] by interfering it with |row>.

    Branch 0 applies an independently written XOR to |column>; branch 1
    applies the corpus kernel. X and Y on the control reveal real and imaginary
    entries, including absolute phase. Data are measured in Z.
    """
    typ = tuple_of(["Bit"] * n)
    source = IMPORTS + "use kernel::kernel;\n"
    if row is not None:
        source += f"unitary fn reference(q: Q<{typ}>) -> Q<{typ}> {{\n" + split_register(n)
        source += tuple_of([f"x(w{i})" if ((column ^ row) >> i) & 1 else f"w{i}" for i in range(n)], join=True) + "\n}\n"
    outputs = n + (row is not None)
    source += f"observe fn main() -> {tuple_of(['CBit'] * outputs)} {{\n"
    source += "let q = " + tuple_of(["x(init0())" if column >> i & 1 else "init0()" for i in range(n)], join=True) + ";\n"
    if row is None:
        source += "let q = kernel(q);\n"
    else:
        source += "let (meter, q) = qif(h(init0()), q) { 0 => reference, 1 => kernel };\n"
    source += split_register(n)
    leaves = ([measure("meter", axis)] if row is not None else []) + [measure(f"w{i}", "z") for i in range(n)]
    return source + tuple_of(leaves) + "\n}\n"


def single(state, axis, matrix):
    result = state.copy()
    for i in range(len(state)):
        if i & (1 << axis):
            continue
        j = i | (1 << axis)
        result[i] = matrix[0][0] * state[i] + matrix[0][1] * state[j]
        result[j] = matrix[1][0] * state[i] + matrix[1][1] * state[j]
    return result


H = [[1 / math.sqrt(2), 1 / math.sqrt(2)], [1 / math.sqrt(2), -1 / math.sqrt(2)]]
RX = [[1 / math.sqrt(2), -1j / math.sqrt(2)], [-1j / math.sqrt(2), 1 / math.sqrt(2)]]
RY = [[1 / math.sqrt(2), -1 / math.sqrt(2)], [1 / math.sqrt(2), 1 / math.sqrt(2)]]


def permute(state, function):
    result = [0j] * len(state)
    for i, amplitude in enumerate(state):
        result[function(i)] += amplitude
    return result


def reference_column(case, column):
    """Mathematical column; does not inspect corpus code or compiled IR."""
    key, name = case["id"].split("/")
    n = case["qubits"]
    dim = 1 << n
    state = [complex(i == column) for i in range(dim)]
    if name == "global_phase":
        return [-a for a in state]
    if name == "zero_control_x2":
        return permute(state, lambda i: i ^ (2 if not i & 1 else 0))
    if name == "bell_change_zx2":
        return [((-1) ** (row & 1) if row == column ^ 1 else 0)
                for row in range(4)]
    if name == "swap2":
        return permute(state, lambda i: (i >> 1) | ((i & 1) << 1))
    if name == "fredkin3":
        return permute(state, lambda i: ((i & 1) | ((i & 2) << 1) | ((i & 4) >> 1))
                       if i & 1 else i)
    if name == "ghz3":
        return permute(single(state, 0, H), lambda i: i ^ (6 if i & 1 else 0))
    if name == "odd_parity3":
        # Closed signed coefficients of the recursive parity preparation.
        return [((-1) ** (((column & 3) & (row & 3)).bit_count()) / 2
                 if (row >> 2) == ((column >> 2) ^ (row & 3).bit_count() % 2 ^ 1)
                 else 0) for row in range(8)]
    if name == "bell_singlet2":
        return [((-1) ** ((column & 1) * (row & 1) + ((row >> 1) ^ 1)) / math.sqrt(2)
                 if ((row >> 1) ^ 1) == ((column >> 1) ^ (row & 1)) else 0)
                for row in range(4)]
    if name == "bernstein_vazirani":
        return permute(state, lambda i: i ^ 3)
    if name == "deutsch_jozsa3":
        return [sum((-1) ** (((column ^ row) & x).bit_count() + (x.bit_count() >= 2))
                    for x in range(8)) / 8 for row in range(8)]
    if name == "grover2":
        phased = [((-1) ** ((column & i).bit_count() + (i == 3))) / 2 for i in range(4)]
        return [sum(phased) / 2 - a for a in phased]
    if name.startswith("qpe"):
        precision = n - 1
        size = 1 << precision
        phase_power = 2 if n == 3 else (3 if key == "pennylane_demos" else 1)
        target, incoming = column // size, column % size
        for y in range(size):
            state[y + target * size] = sum((-1) ** ((incoming & r).bit_count()) * cmath.exp(2j * math.pi * r * (phase_power * target / 8 - y / size)) for r in range(size)) / size
        return state
    if name == "add2":
        return permute(state, lambda i: (i & 3) + (((i & 3) + (i >> 2)) % 4) * 4)
    if name == "add_constant3":
        return permute(state, lambda i: (i + 3) % 8)
    if name == "add_minus_one2":
        return permute(state, lambda i: (i - 1) % 4)
    if name == "equals2":
        return permute(state, lambda i: i ^ (16 if (i & 3) == ((i >> 2) & 3) else 0))
    if name == "less_than_constant2":
        return permute(state, lambda i: i ^ (4 if (i & 3) < 3 else 0))
    if name == "equals_constant2":
        return permute(state, lambda i: i ^ (4 if (i & 3) == 1 else 0))
    if name == "xor2":
        return permute(state, lambda i: (i & 3) + (((i >> 2) ^ (i & 3)) << 2))
    if name == "xor_constant2":
        return permute(state, lambda i: i ^ 1)
    if name == "bitwise_not2":
        return permute(state, lambda i: 3 - i)
    if name == "less_than2":
        return permute(state, lambda i: i ^ (16 if (i & 3) < ((i >> 2) & 3) else 0))
    if name == "qrom2":
        return permute(state, lambda i: i ^ ([1, 2, 3, 0][i & 3] << 2))
    if name == "qrom1":
        return permute(state, lambda i: i ^ ([2, 1][i & 1] << 1))
    if name == "and_phase":
        return [a * (-1 if i == 3 else 1) for i, a in enumerate(state)]
    if name == "qft2":
        return [cmath.exp(2j * math.pi * column * y / 4) / 2 for y in range(4)]
    if name == "reflection2":
        return [a - sum(state) / 2 for a in state]
    if name == "qubit_rotation":
        return single(single(state, 0, RX), 0, RY)
    if name == "rx_quarter":
        return single(state, 0, RX)
    if name == "ry_quarter":
        return single(state, 0, RY)
    if name == "rx_negative_quarter":
        return [(1 if row == column else 1j) / math.sqrt(2) for row in range(2)]
    if name == "ry_negative_quarter":
        return [(-1 if row == 1 and column == 0 else 1) / math.sqrt(2)
                for row in range(2)]
    if name == "ising_zz_quarter2":
        return [a * cmath.exp(-1j * math.pi / 4 * (-1) ** i.bit_count())
                for i, a in enumerate(state)]
    if name == "phase_kickback1":
        return permute(state, lambda i: i ^ ((i >> 1) & 1))
    if name == "kernel_overlap2":
        # Analytic RX(x1-x2) tensor RX(x1-x2), not the QLI gate decomposition.
        return [(-1j) ** ((row ^ column).bit_count()) / 2 for row in range(4)]
    if name == "lcu_projector":
        # The selected H completion has blocks P0, P1; data selects selector XOR.
        return permute(state, lambda i: i ^ ((i >> 1) & 1))
    if name.startswith("qaoa"):
        for axis in range(n):
            state = single(state, axis, H)
        for i in range(dim):
            signs = [1 - 2 * ((i >> j) & 1) for j in range(4)]
            if name == "qaoa_vertex_cover":
                cost = 3 * sum(signs[a] * signs[b] + signs[a] + signs[b] for a, b in [(0, 1), (1, 2), (2, 0), (2, 3)]) - sum(signs)
            else:
                cost = sum(signs[a] * signs[b] for a, b in [(0, 1), (0, 3), (1, 2), (2, 3)])
            state[i] *= cmath.exp(-1j * math.pi * cost / 4)
        for axis in range(n):
            state = single(state, axis, RX)
        return state
    if name == "vqe_excitation":
        state[3], state[12] = state[12], -state[3]
        return state
    if name == "classifier_layer":
        for axis in range(4):
            state = single(state, axis, RY)
        # Closed Boolean output equations for the ring, independent of gate expansion.
        def ring(i):
            a, b, c, d = [(i >> j) & 1 for j in range(4)]
            return (b ^ c ^ d) | ((a ^ b) << 1) | ((a ^ b ^ c) << 2) | ((a ^ b ^ c ^ d) << 3)
        return permute(state, ring)
    if name == "phase_lock":
        return permute(state, lambda i: i ^ (1 if i >> 1 == 14 else 0))
    raise ValueError(f"no mathematical oracle: {case['id']}")


def probabilities(state):
    return {tuple(bool(i >> j & 1) for j in range((len(state) - 1).bit_length())): abs(a) ** 2 for i, a in enumerate(state)}


def interference(column, row, axis):
    # First output/control wire is axis 0; data start at axis 1.
    state = [0j] * (2 * len(column))
    state[2 * row] = 1 / math.sqrt(2)
    for i, amplitude in enumerate(column):
        state[2 * i + 1] = amplitude / math.sqrt(2)
    if axis == "y":
        state = single(state, 0, [[1, 0], [0, -1j]])
    return probabilities(single(state, 0, H))


def run(binary, project):
    process = subprocess.run([str(binary), "run", str(project), "--format=json"], capture_output=True, text=True, timeout=30)
    require(process.returncode == 0 and not process.stderr, f"run failed ({project}): {process.stdout} {process.stderr}")
    result = json.loads(process.stdout)
    require(result["outcome"] == "ok" and not result["diagnostics"], "unexpected result envelope")
    rows = result["result"]["distribution"]
    require(all(isinstance(r["bits"], list) and all(type(b) is bool for b in r["bits"]) and isinstance(r["probability"], (int, float)) and math.isfinite(r["probability"]) and r["probability"] >= 0 for r in rows), "invalid numeric distribution")
    values = {tuple(r["bits"]): r["probability"] for r in rows}
    require(len(values) == len(rows), "duplicate distribution outcome")
    return values


class SemanticMismatch(ValueError):
    """A well-formed numerical result differs from the independent contract."""


def compare(actual, expected, label):
    require(abs(sum(actual.values()) - 1) < TOLERANCE, f"unnormalized output: {label}")
    require(abs(sum(expected.values()) - 1) < TOLERANCE, f"unnormalized oracle: {label}")
    for bits in actual.keys() | expected.keys():
        if not abs(actual.get(bits, 0) - expected.get(bits, 0)) < TOLERANCE:
            raise SemanticMismatch(f"{label}: {bits}: {actual.get(bits, 0)} != {expected.get(bits, 0)}")


def protocol_probes(case):
    if case["kind"] == "bell_measure":
        for phase in [False, True]:
            for parity in [False, True]:
                a = "x(init0())" if phase else "init0()"
                b = "x(init0())" if parity else "init0()"
                source = IMPORTS + "use kernel::bell_measure;\nobserve fn main() -> (CBit,CBit) {\n"
                source += f"let (a,b) = cnot(h({a}), {b});\nbell_measure(join(a,b))\n}}\n"
                yield source, {(phase, parity): 1.0}, f"Bell-label-{phase}-{parity}"
        # Choi probe: measure the two inputs of two Bell pairs, retaining both
        # reference wires. Nine Pauli pairs determine every conditional matrix.
        for left in "xyz":
            for right in "xyz":
                source = IMPORTS + "use kernel::bell_measure;\nobserve fn main() -> ((CBit,CBit),(CBit,CBit)) {\n"
                source += "let (r0,a) = cnot(h(init0()),init0());\nlet (r1,b) = cnot(h(init0()),init0());\nlet outcome = bell_measure(join(a,b));\n"
                source += f"(outcome, ({measure('r0', left)}, {measure('r1', right)}))\n}}\n"
                expected = {}
                for s in [False, True]:
                    for t in [False, True]:
                        correlation = {"x": (-1) ** s, "y": -(-1) ** (s + t), "z": (-1) ** t}[left] if left == right else 0
                        for a in [False, True]:
                            for b in [False, True]:
                                expected[(s, t, a, b)] = (1 + (-1) ** (a + b) * correlation) / 16
                yield source, expected, f"Bell-measure-Choi-{left}{right}"
        return
    if case["kind"] == "dense":
        for a in [False, True]:
            for b in [False, True]:
                yield IMPORTS + f"use kernel::send;\nobserve fn main() -> (CBit,CBit) {{ send({str(a).lower()}, {str(b).lower()}) }}\n", {(a, b): 1.0}, "classical-message"
        return
    if case["kind"] == "measure":
        for prep, expected in [("init0()", .5), ("x(init0())", .5), ("h(init0())", 1), ("h(x(init0()))", 0), ("t(t(h(init0())))", .5), ("t(h(init0()))", (2 + math.sqrt(2)) / 4)]:
            yield IMPORTS + f"use kernel::is_plus;\nobserve fn main() -> CBit {{ is_plus({prep}) }}\n", {(True,): expected, (False,): 1 - expected}, "plus-polarity"
        return
    require(case["kind"] == "teleport", f"unknown protocol oracle: {case['kind']}")
    # Tomography of the teleported half of a Bell pair, with both message bits.
    # Nine Pauli products determine the two-qubit output density matrix; test
    # every classical branch separately rather than marginalizing the message.
    for ref in "xyz":
        for target in "xyz":
            source = IMPORTS + "use kernel::teleport;\nobserve fn main() -> ((CBit,CBit),(CBit,CBit)) {\nlet (r,q) = cnot(h(init0()), init0());\nlet (message,bob) = teleport(q);\n" + f"(message, ({measure('r', ref)}, {measure('bob', target)}))\n}}\n"
            expected = {}
            for a in [False, True]:
                for b in [False, True]:
                    for r in [False, True]:
                        for q in [False, True]:
                            # Bell Phi+: XX=ZZ=+1, YY=-1, cross products=0.
                            p = (0.5 if (r != q) == (ref == 'y') else 0) if ref == target else .25
                            expected[(a, b, r, q)] = p / 4
            yield source, expected, f"branch-Bell-{ref}{target}"


def host_observables(case, values):
    """Classical aggregation boundary; no optimizer or molecular energy claim."""
    name = case["id"].split("/")[1]
    if case["source"] != "pennylane_demos" or case["kind"] != "unitary":
        return {}
    z0 = sum((1 - 2 * b[0]) * p for b, p in values.items())
    results = {"Z0": z0}
    if name == "kernel_overlap2":
        results["kernel_overlap"] = values.get((False, False), 0)
    if name == "lcu_projector":
        results["zero_selector_probability"] = sum(p for b, p in values.items() if not b[0])
    if name == "qaoa_maxcut":
        results["expected_cut_edges"] = sum(sum(b[a] != b[c] for a, c in [(0, 1), (0, 3), (1, 2), (2, 3)]) * p for b, p in values.items())
    if name == "qaoa_vertex_cover":
        def cost(bits):
            z = [1 - 2 * b for b in bits]
            return 3 * sum(z[a] * z[b] + z[a] + z[b] for a, b in [(0, 1), (1, 2), (2, 0), (2, 3)]) - sum(z)
        results["cost_expectation"] = sum(cost(b) * p for b, p in values.items())
    return results


def check_case(case, binary, exhaustive, project=None):
    project = CORPUS / case["project"] if project is None else project
    shipped = run(binary, project)
    probes = 0
    with tempfile.TemporaryDirectory(prefix="qleisli-corpus-") as temp:
        temp = Path(temp)
        shutil.copyfile(CORPUS / "Qargo.toml", temp / "Qargo.toml")
        shutil.copyfile(project / "kernel.qli", temp / "kernel.qli")
        def execute(source, expected, label):
            nonlocal probes
            (temp / "main.qli").write_text(source)
            compare(run(binary, temp), expected, f"{case['id']} {label}")
            probes += 1
        if case["kind"] == "unitary":
            n = case["qubits"]
            dim = 1 << n
            for x in range(dim):
                column = reference_column(case, x)
                execute(driver(n, x), probabilities(column), f"column {x}")
                rows = range(dim) if exhaustive else sorted({0, x, dim - 1})
                for y in rows:
                    for axis in "xy":
                        execute(driver(n, x, y, axis), interference(column, y, axis), f"entry {y},{x} {axis}")
            default = sum(b << j for j, b in enumerate(case["default_input"]))
            expected = probabilities(reference_column(case, default))
            compare(shipped, expected, f"{case['id']} shipped main")
            observed, wanted = host_observables(case, shipped), host_observables(case, expected)
            require(all(abs(v - wanted[k]) < TOLERANCE for k, v in observed.items()), "host expectation mismatch")
        else:
            for source, expected, label in protocol_probes(case):
                execute(source, expected, label)
            if case["kind"] == "dense":
                expected = {(True, False): 1.0}
            elif case["kind"] == "measure":
                expected = {(True,): 1.0}
            elif case["kind"] == "bell_measure":
                expected = {(False, False): 1.0}
            else:
                p = (2 + math.sqrt(2)) / 4
                expected = {(a, b, c): (p if not c else 1 - p) / 4 for a in [False, True] for b in [False, True] for c in [False, True]}
            compare(shipped, expected, f"{case['id']} shipped main")
            observed = {}
    return {"id": case["id"], "semantic_probes": probes, "shipped_main": "passed", "host_observables": observed}


def check_semantic_fault(fault, case, binary):
    project = local(CORPUS, fault["project"])
    process = subprocess.run([str(binary), "check", str(project), "--format=json"],
                             capture_output=True, text=True, timeout=30)
    require(process.returncode == 0 and not process.stderr,
            f"semantic fault must typecheck: {fault['id']}: {process.stdout} {process.stderr}")
    require(json.loads(process.stdout)["outcome"] == "ok", "semantic fault check envelope")
    try:
        check_case(case, binary, False, project=project)
    except SemanticMismatch as error:
        return {"id": fault["id"], "reference": case["id"], "typecheck": "passed",
                "semantic_mismatch": str(error)}
    raise ValueError(f"semantic fault escaped the oracle: {fault['id']}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("binary", nargs="?", type=Path)
    parser.add_argument("--case", help="single source/case ID")
    parser.add_argument("--exhaustive", action="store_true", help="check every complex matrix entry via X/Y interference")
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    manifest = check_manifest()
    if not args.binary:
        print(f"Corpus policy, provenance, notices and authoring snapshots: passed ({len(manifest['cases'])} cases / 3 sources)")
        return
    binary = args.binary.resolve()
    cases = [c for c in manifest["cases"] if not args.case or c["id"] == args.case]
    require(bool(cases), "unknown corpus case")
    with ThreadPoolExecutor(max_workers=4) as pool:
        results = list(pool.map(lambda case: check_case(case, binary, args.exhaustive), cases))
    by_id = {c["id"]: c for c in cases}
    faults = [f for f in json.loads((CORPUS / "semantic_faults/manifest.json").read_text())["cases"]
              if f["reference"] in by_id]
    fault_results = [check_semantic_fault(f, by_id[f["reference"]], binary) for f in faults]
    negative_results = []
    for case in json.loads((CORPUS / "negative/manifest.json").read_text())["cases"]:
        process = subprocess.run([str(binary), "check", str(local(CORPUS, case["project"])), "--format=json"], capture_output=True, text=True, timeout=30)
        require(process.returncode == 1 and not process.stderr, f"negative case accepted: {case['id']}")
        output = json.loads(process.stdout)
        require(output["outcome"] == "error" and output["result"] is None, "negative JSON result")
        require(output["diagnostics"][0]["code"] == case["expected_code"], f"wrong negative diagnostic: {case['id']}")
        negative_results.append({"id": case["id"], "code": case["expected_code"], "exit_code": process.returncode})
    report = {
        "format": 1,
        "created_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "project_version": re.search(
            r'^version\s*=\s*"([^"]+)"',
            (ROOT / "Cargo.toml").read_text().split("[package]", 1)[1].split("\n[", 1)[0],
            re.MULTILINE,
        ).group(1),
        "compiler_sha256": sha256(binary),
        "oracle_script_sha256": sha256(Path(__file__)),
        "manifest_sha256": sha256(CORPUS / "manifest.json"),
        "source_sha256": {str(p.relative_to(CORPUS)): sha256(p) for c in cases for p in sorted((CORPUS / c["project"]).glob("*.qli"))},
        "exhaustive_unitary_entries": args.exhaustive,
        "upstream_frameworks_executed": False,
        "tolerance": TOLERANCE,
        "cases": results,
        "negative_cases": negative_results,
        "semantic_faults": fault_results,
        "semantic_fault_manifest_sha256": sha256(CORPUS / "semantic_faults/manifest.json"),
        "semantic_fault_source_sha256": {str(p.relative_to(CORPUS)): sha256(p)
                                         for f in faults for p in sorted(local(CORPUS, f["project"]).glob("*.qli"))},
    }
    if args.report:
        args.report.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Passed {len(results)} cases, {sum(r['semantic_probes'] for r in results)} semantic probes, all shipped mains and {len(negative_results)} rejection cases; detected {len(fault_results)} type-correct semantic faults; upstream frameworks not executed.")


if __name__ == "__main__":
    main()
