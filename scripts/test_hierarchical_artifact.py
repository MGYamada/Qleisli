#!/usr/bin/env python3
"""Native typed-artifact projection, endpoint binding and shared-budget checks.

Success here means prepared data, never verified quantum meaning. In particular,
the deliberate phase mutation still needs the subsequent derivation checker.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import native_harness
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]

PRELUDE = r'''import QleisliKernel.Hierarchical.Ports
open QleisliKernel.Hierarchical.Artifact
def side (width : Nat) : Side := ⟨#[⟨0, #[.bits width], Array.range width⟩], #[]⟩
def signature (width : Nat) : Interface := ⟨side width, side width⟩
def identityMap (width : Nat) : PortMap := ⟨#[0], Array.range width, #[]⟩
def witness : Witness := ⟨1, #[], #[]⟩
def proof : Proof := ⟨.equation, .rewire, #[], 0, 0, 0, 0, witness⟩
def base (width : Nat) : Artifact :=
  ⟨#[⟨signature width, .unitary, .rewire (identityMap width)⟩],
   #[⟨signature width, .identity⟩], #[⟨side width, side width, .identity⟩], #[proof], ⟨0,0⟩⟩
def order : Array Nat := #[0,1,2,3]
def changeDef (a : Artifact) (f : Definition → Definition) : Artifact :=
  {a with definitions := a.definitions.map f}
def changeMeaning (a : Artifact) (f : Meaning → Meaning) : Artifact :=
  {a with meanings := a.meanings.map f}
def changeEncoding (a : Artifact) (f : Encoding → Encoding) : Artifact :=
  {a with encodings := a.encodings.map f}
def changeProof (a : Artifact) (f : Proof → Proof) : Artifact :=
  {a with proofs := a.proofs.map f}
def changedBasis (a : Artifact) (basis : Basis) : Artifact :=
  changeMeaning a fun m => {m with interface := {m.interface with inputs :=
    {m.interface.inputs with quantum := #[⟨0,basis,#[0,1,2]⟩]}}}
def repeated (count : Nat) : Artifact :=
  let a := base 1
  {a with definitions := a.definitions.push ⟨signature 1, .unitary, .repeatOp count 0⟩,
          proofs := #[{proof with implementation := 1}], entry := ⟨1,0⟩}
def invalidZero : Artifact :=
  {repeated 0 with definitions := #[⟨signature 1, .unitary, .dyadicPhase 0 1 9⟩,
    ⟨signature 1, .unitary, .repeatOp 0 0⟩]}
def zeroCycle : Artifact := changeDef (base 1) fun d => {d with body := .repeatOp 0 0}
def nested : Basis := #[.tuple 2,.tuple 2,.bit,.bit,.bit]
def flat : Basis := #[.tuple 3,.bit,.bit,.bit]
def typed (basis : Basis) (width : Nat) : Artifact :=
  let s : Side := ⟨#[⟨0,basis,Array.range width⟩],#[]⟩
  {base width with definitions := #[⟨⟨s,s⟩,.unitary,.rewire (identityMap width)⟩],
                   meanings := #[⟨⟨s,s⟩,.identity⟩],encodings := #[⟨s,s,.identity⟩]}
def withZero : Artifact :=
  let s : Side := ⟨#[⟨0,#[.bit],#[0]⟩,⟨1,#[.bits 0],#[]⟩],#[]⟩
  {base 1 with definitions := #[⟨⟨s,s⟩,.unitary,.rewire ⟨#[0,1],#[0],#[]⟩⟩],
               meanings := #[⟨⟨s,s⟩,.identity⟩],encodings := #[⟨s,s,.identity⟩]}
def duplicateZero : Artifact := changeDef withZero fun d =>
  {d with interface := {d.interface with inputs :=
    ⟨#[⟨0,#[.bit],#[0]⟩,⟨0,#[.bits 0],#[]⟩],#[]⟩}}
def dropZero : Artifact := changeMeaning withZero fun m =>
  {m with interface := {m.interface with inputs := ⟨#[⟨0,#[.bit],#[0]⟩],#[]⟩}}
def proofStar (n : Nat) : Artifact :=
  {base 8 with proofs := (Array.range n).map (fun i =>
    {proof with premises := if i+1=n then Array.range i else #[]}), entry := ⟨0,n-1⟩}
def bytes (n : Nat) : ByteArray := ⟨Array.replicate n 0⟩
def payload (n : Nat) : Artifact := changeDef (base 1) fun d => {d with body := .leaf (bytes n)}
def noPorts : Side := ⟨#[],#[]⟩
def oversizedPorts : Artifact := changeDef (base 0) fun d =>
  {d with interface := ⟨⟨Array.replicate 100000 ⟨0,#[.bits 0],#[]⟩,#[]⟩,noPorts⟩}
def oversizedReferences : Artifact := changeDef (base 1) fun d =>
  {d with body := .sequence (Array.replicate 1000001 0)}
def oversizedWitness : Artifact := changeProof (base 1) fun p =>
  {p with witness := {witness with references := Array.replicate 1000001 ⟨.definition,0⟩}}
def code (failure : Failure) : String := match failure.kind with
  | .limit => "limit" | .invalidIr => "invalid_ir" | .contract => "contract"
def graphText (nodes : QleisliKernel.Hierarchical.Graph.Nodes) : String :=
  "[" ++ String.intercalate "," (nodes.toList.map (fun edges =>
    "[" ++ String.intercalate "," (edges.map toString) ++ "]")) ++ "]"
def report (name : String) (a : Artifact) (schedule : Array Nat) : IO Unit := do
  match prepare a schedule with
  | .error e => IO.println s!"{name}|{code e}"
  | .ok p => IO.println s!"{name}|prepared|{p.totalVisits}|{p.projection.payloadBytes}|{graphText p.projection.nodes}"
def refText (ref : Ref) : String :=
  let table := match ref.table with
    | .definition => "d" | .meaning => "m" | .encoding => "e" | .proof => "p"
  s!"{table}{ref.index}"
def reportPorts (name : String) (source destination : Side) (map : PortMap) (budget : Nat) : IO Unit :=
  match QleisliKernel.Hierarchical.Ports.check source destination map budget with
  | .error e => IO.println s!"{name}|{code ⟨e,none⟩}"
  | .ok checked => IO.println s!"{name}|mapped|{checked.visits}"
def bitPair : Side := ⟨#[⟨7,#[.bit],#[5]⟩,⟨8,#[.bit],#[1]⟩],#[]⟩
def renamedPair : Side := ⟨#[⟨90,#[.bit],#[700]⟩,⟨91,#[.bit],#[300]⟩],#[]⟩
def zeroPair : Side := ⟨#[⟨7,#[.unit],#[]⟩,⟨8,#[.bits 0],#[]⟩],#[]⟩
def reversedZero : Side := ⟨#[⟨70,#[.bits 0],#[]⟩,⟨80,#[.unit],#[]⟩],#[]⟩
def tupleSide (basis : Basis) : Side := ⟨#[⟨0,basis,#[0,1,2]⟩],#[]⟩
def classicalSide : Side := ⟨#[],#[⟨7,#[.bit]⟩,⟨8,#[.bits 2]⟩]⟩
def reversedClassical : Side := ⟨#[],#[⟨70,#[.bits 2]⟩,⟨80,#[.bit]⟩]⟩
def hugeAxes : Side := ⟨#[⟨0,#[.bits 8],Array.replicate 1000000 0⟩],#[]⟩
def refs (name : String) (rs : Array Ref) : IO Unit :=
  IO.println s!"{name}|refs|{String.intercalate "," (rs.toList.map refText)}"
'''


def cases():
    rows = []
    def add(name, artifact, status, schedule="order", cost=None, payload=None):
        rows.append(dict(name=name, artifact=artifact, status=status, schedule=schedule,
                         cost=cost, payload=payload))
    for width in range(9):
        add(f"bits-{width}", f"base {width}", "prepared")
    add("bits-9", "base 9", "invalid_ir")
    add("reorder-without-rebinding", "{ repeated 0 with definitions := (repeated 0).definitions.reverse, "
        "proofs := #[proof], entry := ⟨0,0⟩ }", "invalid_ir", "#[1,0,2,3,4]")  # Still points at itself.
    add("forward-definition-reference", "{repeated 0 with definitions := "
        "#[⟨signature 1,.unitary,.repeatOp 0 1⟩,⟨signature 1,.unitary,.rewire (identityMap 1)⟩], "
        "proofs := #[proof], entry := ⟨0,0⟩}", "prepared", "#[1,0,2,3,4]")
    add("zero-repeat-keeps-body", "repeated 0", "prepared", "#[0,1,2,3,4]")
    add("repeat-4096", "repeated 4096", "prepared", "#[0,1,2,3,4]")
    add("repeat-4097", "repeated 4097", "invalid_ir", "#[0,1,2,3,4]")
    add("zero-repeat-invalid-body", "invalidZero", "invalid_ir", "#[0,1,2,3,4]")
    add("zero-repeat-cycle", "zeroCycle", "invalid_ir")
    add("definition-index-cannot-alias-meaning", "changeDef (base 1) (fun d => {d with body := .inverse 1})", "invalid_ir")
    add("meaning-index-cannot-alias-encoding", "changeMeaning (base 1) (fun m => {m with body := .inverse 1})", "invalid_ir")
    add("encoding-index-cannot-alias-proof", "changeEncoding (base 1) (fun e => {e with body := .rewire 1 (identityMap 1)})", "invalid_ir")
    add("proof-self-cycle", "changeProof (base 1) (fun p => {p with premises := #[0]})", "invalid_ir")
    add("encoding-self-cycle", "changeEncoding (base 1) (fun e => {e with body := .rewire 0 (identityMap 1)})", "invalid_ir")
    add("witness-self-cycle", "changeProof (base 1) (fun p => {p with witness := {witness with references := #[⟨.proof,0⟩]}})", "invalid_ir")
    add("witness-dangling", "changeProof (base 1) (fun p => {p with witness := {witness with references := #[⟨.definition,1⟩]}})", "invalid_ir")
    add("wrong-entry-proof", "{ repeated 0 with proofs := #[proof] }", "contract", "#[0,1,2,3,4]")
    add("unreachable-definition", "{base 1 with definitions := (base 1).definitions ++ (base 1).definitions}", "invalid_ir", "#[0,1,2,3,4]")
    add("wrong-schedule", "base 1", "invalid_ir", "#[3,0,1,2]")
    add("duplicate-schedule", "base 1", "invalid_ir", "#[0,0,2,3]")
    add("flat-tuple", "typed flat 3", "prepared")
    add("nested-tuple", "typed nested 3", "prepared")
    add("nested-vs-flat", "changedBasis (typed flat 3) nested", "contract")
    add("bits-vs-flat", "changedBasis (base 3) flat", "contract")
    add("bad-type-arity", "changedBasis (base 3) #[.tuple 2,.bit,.bit,.bit]", "invalid_ir")
    add("zero-owner", "withZero", "prepared")
    add("duplicate-zero-owner", "duplicateZero", "invalid_ir")
    add("lost-zero-owner-binding", "dropZero", "contract")
    add("wrong-physical-axis-binding", "changeEncoding (base 2) (fun e => {e with physical := ⟨#[⟨0,#[.bits 2],#[1,0]⟩],#[]⟩})", "contract")
    add("aliased-axes", "changeDef (base 2) (fun d => {d with interface := ⟨⟨#[⟨0,#[.bits 2],#[0,0]⟩],#[]⟩,(side 2)⟩})", "invalid_ir")
    add("observe-equation", "changeDef (base 1) (fun d => {d with effect := .observe})", "contract")
    add("instrument-cannot-use-unitary-meaning", "changeProof (base 1) (fun p => {p with kind := .instrument})", "contract")
    add("unknown-rule", 'changeProof (base 1) (fun p => {p with rule := .schema "unknown/1"})', "invalid_ir")
    add("declaration-name-is-not-rule", 'changeProof (base 1) (fun p => {p with rule := .schema "Qleisli.Schema.qft_sound"})', "invalid_ir")
    add("unknown-template", "changeProof (base 1) (fun p => {p with witness := {witness with templateVersion := 2}})", "invalid_ir")
    add("parameter-overflow", "changeProof (base 1) (fun p => {p with witness := {witness with parameters := #[4294967296]}})", "invalid_ir")
    add("angle-outside-profile", "changeDef (base 1) (fun d => {d with body := .dyadicPhase 0 1 1000000000})", "invalid_ir")
    add("oversized-interface", "oversizedPorts", "limit")
    add("oversized-references", "oversizedReferences", "limit")
    add("oversized-witness", "oversizedWitness", "limit")
    add("empty-finite-payload", "payload 0", "invalid_ir")
    add("payload-at-ceiling", "payload 16777216", "prepared", payload=16777216)
    add("payload-over-ceiling", "payload 16777217", "limit")
    # These expressions are well-formed data; the semantic pass must still reject
    # a wrong phase and must reconstruct opaque finite bytes before verification.
    add("phase-mutation-still-needs-semantic-check", "changeDef (typed #[.bit] 1) (fun d => {d with body := .dyadicPhase 0 1 3})", "prepared")
    add("last-shared-budget", "proofStar 4986", "prepared", "Array.range 4989", cost=1999681)
    add("shared-budget-overflow", "proofStar 4987", "limit", "Array.range 4990")
    return rows


def reference_cases():
    rows = [
        ("leaf", "(Body.leaf (bytes 1)).references", ""),
        ("sequence", "(Body.sequence #[2,0]).references", "d2,d0"),
        ("tensor", "(Body.tensor 2 0).references", "d2,d0"),
        ("call", "(Body.call 2 (identityMap 1) (identityMap 1)).references", "d2"),
        ("repeat-zero", "(Body.repeatOp 0 2).references", "d2"),
        ("inverse", "(Body.inverse 2).references", "d2"),
        ("control", "(Body.control 2 false).references", "d2"),
        ("rewire", "(Body.rewire (identityMap 1)).references", ""),
        ("phase", "(Body.dyadicPhase 0 1 8).references", ""),
        ("computed", "(Body.computed 1 2 3 4).references", "d1,d2,m3,e4"),
        ("observe", "(Body.observeZ 0 1).references", ""),
        ("init", "(Body.init0 0).references", ""),
        ("meaning-sequence", "(MeaningBody.sequence #[2,0]).references", "m2,m0"),
        ("meaning-tensor", "(MeaningBody.tensor 2 0).references", "m2,m0"),
        ("meaning-inverse", "(MeaningBody.inverse 2).references", "m2"),
        ("meaning-control", "(MeaningBody.control 2 true).references", "m2"),
        ("meaning-zero-power", "(MeaningBody.power 2 0).references", "m2"),
        ("meaning-instrument", "(MeaningBody.qpeInstrument 2 4 3).references", "m3"),
        ("encoding-tensor", "(EncodingBody.tensor 2 0).references", "e2,e0"),
        ("encoding-rewire", "(EncodingBody.rewire 2 (identityMap 1)).references", "e2"),
        ("encoding-zero-scratch", "(EncodingBody.zeroScratch 0 2).references", "d2"),
        ("proof-all-fields", "({proof with implementation := 1, meaning := 2, inputEncoding := 3, outputEncoding := 4, premises := #[6,5], witness := {witness with references := #[⟨.meaning,7⟩]}} : Proof).references", "d1,m2,e3,e4,p6,p5,m7"),
    ]
    return rows



def port_cases():
    rows = []
    def add(name, source, destination, mapping, status, budget=2000000, visits=None):
        rows.append(dict(name="ports-"+name, source=source, destination=destination,
                         mapping=mapping, status=status, budget=budget, visits=visits))
    for width in range(9):
        add(f"bits-{width}",f"side {width}",f"side {width}",f"identityMap {width}","mapped")
    add("local-ids-are-labels","bitPair","renamedPair","⟨#[0,1],#[0,1],#[]⟩","mapped")
    add("reorder-owners-and-axes","bitPair","renamedPair","⟨#[1,0],#[1,0],#[]⟩","mapped")
    add("owner-axis-disagreement","bitPair","renamedPair","⟨#[1,0],#[0,1],#[]⟩","invalid_ir")
    add("duplicate-owner","bitPair","renamedPair","⟨#[0,0],#[0,1],#[]⟩","invalid_ir")
    add("duplicate-axis","bitPair","renamedPair","⟨#[0,1],#[0,0],#[]⟩","invalid_ir")
    add("missing-owner","bitPair","renamedPair","⟨#[0],#[0,1],#[]⟩","invalid_ir")
    add("missing-axis","bitPair","renamedPair","⟨#[0,1],#[0],#[]⟩","invalid_ir")
    add("out-of-range-owner","bitPair","renamedPair","⟨#[0,2],#[0,1],#[]⟩","invalid_ir")
    add("ids-are-not-positions","bitPair","renamedPair","⟨#[7,8],#[5,1],#[]⟩","invalid_ir")
    add("zero-owner-reorder","zeroPair","reversedZero","⟨#[1,0],#[],#[]⟩","mapped")
    add("zero-owner-duplicate","zeroPair","reversedZero","⟨#[1,1],#[],#[]⟩","invalid_ir")
    add("zero-owner-drop","zeroPair","side 0","⟨#[1],#[],#[]⟩","invalid_ir")
    add("zero-owner-types","zeroPair","reversedZero","⟨#[0,1],#[],#[]⟩","invalid_ir")
    add("flat-identity","tupleSide flat","tupleSide flat","identityMap 3","mapped")
    add("nested-identity","tupleSide nested","tupleSide nested","identityMap 3","mapped")
    add("no-implicit-reassociation","tupleSide flat","tupleSide nested","identityMap 3","invalid_ir")
    add("bits-are-not-flat","side 3","tupleSide flat","identityMap 3","invalid_ir")
    add("bits1-is-not-bit","side 1","⟨#[⟨0,#[.bit],#[0]⟩],#[]⟩","identityMap 1","invalid_ir")
    add("within-register-order","side 2","side 2","⟨#[0],#[1,0],#[]⟩","invalid_ir")
    add("classical-reorder","classicalSide","reversedClassical","⟨#[],#[],#[1,0]⟩","mapped")
    add("classical-type-change","classicalSide","reversedClassical","⟨#[],#[],#[0,1]⟩","invalid_ir")
    add("classical-duplicate","classicalSide","reversedClassical","⟨#[],#[],#[1,1]⟩","invalid_ir")
    add("classical-drop","classicalSide","noPorts","⟨#[],#[],#[]⟩","invalid_ir")
    add("no-ports","noPorts","noPorts","⟨#[],#[],#[]⟩","mapped")
    add("budget-exact","side 0","side 0","identityMap 0","mapped",592,592)
    add("budget-short","side 0","side 0","identityMap 0","limit",591)
    add("budget-zero","side 0","side 0","identityMap 0","limit",0)
    add("budget-profile-overflow","side 0","side 0","identityMap 0","limit",2000001)
    add("oversized-axis-storage","hugeAxes","side 8","identityMap 8","limit")
    add("oversized-map","side 0","side 0","⟨Array.replicate 1000000 0,#[],#[]⟩","limit")
    return rows


def build_and_run(source, record=None):
    commands = []
    with tempfile.TemporaryDirectory(prefix="qleisli-hierarchical-artifact-") as directory:
        project = Path(directory)
        (project / "Main.lean").write_text(source)
        binary = native_harness.build(project, commands)
        for argv in ([str(binary)],):
            run = subprocess.run(argv, cwd=project, capture_output=True, text=True, timeout=240)
            commands.append(dict(argv=argv,exit_code=run.returncode,stdout=run.stdout,stderr=run.stderr))
            if run.returncode:
                if record:
                    record.write_text(json.dumps(dict(status="error",commands=commands),indent=2)+"\n")
                raise AssertionError(commands[-1])
        binary_hash = hashlib.sha256(binary.read_bytes()).hexdigest()
    return commands, binary_hash


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record", type=Path)
    args = parser.parse_args()
    rows, references, ports = cases(), reference_cases(), port_cases()
    calls = [f'report {json.dumps(r["name"])} ({r["artifact"]}) ({r["schedule"]})' for r in rows]
    calls += [f'refs {json.dumps(name)} ({expression})' for name,expression,_ in references]
    calls += [f'reportPorts {json.dumps(r["name"])} ({r["source"]}) ({r["destination"]}) '
              f'({r["mapping"]}) {r["budget"]}' for r in ports]
    source = PRELUDE + "\n".join(f"def case{i} : IO Unit := {call}" for i,call in enumerate(calls)) + "\n"
    groups = list(range(0, len(calls), 16))
    for first in groups:
        source += f"def group{first} : IO Unit := do\n" + \
            "\n".join(f"  case{i}" for i in range(first, min(first+16,len(calls)))) + "\n"
    source += "def main : IO Unit := do\n" + "\n".join(f"  group{i}" for i in groups) + "\n"
    commands, binary_hash = build_and_run(source, args.record)
    results = {}
    for line in commands[-1]["stdout"].splitlines():
        name,*fields = line.split("|")
        assert name not in results
        results[name] = fields
    if args.record:
        args.record.write_text(json.dumps(dict(status="observed-not-yet-compared",results=results,
                                              commands=commands),indent=2)+"\n")
    assert len(results) == len(rows) + len(references) + len(ports)
    for row in rows:
        fields = results[row["name"]]
        assert fields[0] == row["status"], (row["name"],fields,row["status"])
        if row["cost"] is not None:
            assert int(fields[1]) == row["cost"], (row["name"],fields)
        if row["payload"] is not None:
            assert int(fields[2]) == row["payload"]
    for name,_,expected in references:
        assert results[name] == ["refs",expected], (name,results[name],expected)
    for row in ports:
        fields = results[row["name"]]
        assert fields[0] == row["status"], (row["name"],fields,row["status"])
        if row["visits"] is not None:
            assert int(fields[1]) == row["visits"], (row["name"],fields)
    # Independent expected edges for the real four-table projection, including
    # both encoding fields when they happen to share one actual encoding node.
    assert json.loads(results["bits-1"][3]) == [[],[],[],[0,1,2,2]]
    assert json.loads(results["zero-repeat-keeps-body"][3]) == [[],[0],[],[],[1,2,3,3]]
    # Budget boundary from the specified field/endpoint and graph visit counts:
    # projection = 264 + 366*N; scheduling = 31 + 35*N.
    assert 264 + 366*4986 + 31 + 35*4986 == 1999681
    assert 264 + 366*4987 + 31 + 35*4987 > 2000000
    report = dict(format="qleisli.hierarchical-artifact-validation",version=1,status="passed",
                  structural_cases=len(rows), reference_cases=len(references), port_cases=len(ports),
                  prepared=sum(r["status"]=="prepared" for r in rows), semantic_evidence_issued=False,
                  largest_shared_visits=1999681,binary_sha256=binary_hash,
                  harness_sha256=hashlib.sha256(source.encode()).hexdigest(),results=results,commands=commands,
                  source_sha256={name:hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in (
                    "lean-kernel/QleisliKernel/Hierarchical/Artifact.lean",
                    "lean-kernel/QleisliKernel/Hierarchical/Graph.lean",
                      "lean-kernel/QleisliKernel/Hierarchical/Ports.lean","scripts/test_hierarchical_artifact.py")})
    if args.record:
        args.record.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps({k:v for k,v in report.items() if k not in {"results","commands"}}))


if __name__ == "__main__":
    main()
