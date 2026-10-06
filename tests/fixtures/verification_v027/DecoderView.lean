import Protocol.Qirf
import Protocol.Hierarchical
import Lean

/-! Test-only lossless views of actual decoded data. Not an acceptance API.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
open Lean QleisliKernel

def obj := Json.mkObj
def tag (name : String) (fields : List (String × Json) := []) : Json :=
  obj (("tag",toJson name) :: fields)
def js (values : List Json) : Json := Json.arr values.toArray

def step (s : Semantics.Finite.Step) : Json :=
  let action := match s.action with
    | .hadamard i => tag "hadamard" [("target",toJson i)]
    | .monomial axes permutation phases => tag "monomial"
        [("indices",toJson axes),("permutation",toJson permutation),("phases",toJson phases)]
    | .contract axes evidence adjoint => tag "contract"
        [("indices",toJson axes),("evidence",toJson evidence),("adjoint",toJson adjoint)]
  obj [("controls",js (s.controls.map fun c => obj [("index",toJson c.index),("when_one",toJson c.whenOne)])),
    ("action",action)]
def gate : Semantics.Raw.Gate → String | .h => "h" | .x => "x" | .z => "z" | .t => "t"
def phase : Semantics.Raw.Phase → String | .minusOne => "minus_one" | .eighthTurn => "eighth_turn"
def localOp : Semantics.Raw.UnitaryStep → Json
  | .gate g i => tag "gate" [("gate",toJson (gate g)),("target_index",toJson i)]
  | .cnot c t => tag "cnot" [("control_index",toJson c),("target_index",toJson t)]
  | .toffoli a b t => tag "toffoli" [("control_a_index",toJson a),("control_b_index",toJson b),("target_index",toJson t)]
  | .phase p => tag "scalar_phase" [("phase",toJson (phase p))]
def protectedBit (b : Semantics.Raw.ProtectedBit) : Json :=
  obj [("region",toJson (match b.region with | .source => "source" | .ancilla => "ancilla")),("index",toJson b.index)]
def protectedControls (cs : List Semantics.Raw.ProtectedControl) : Json :=
  js (cs.map fun c => obj [("bit",protectedBit c.bit),("when_one",toJson c.whenOne)])
def usage : Semantics.Raw.Use → Json
  | .protectedGate b g => tag "protected_gate" [("bit",protectedBit b),("gate",toJson (gate g))]
  | .targetGate cs i g => tag "controlled_target_gate"
      [("controls",protectedControls cs),("target_index",toJson i),("gate",toJson (gate g))]
  | .phase cs p => tag "controlled_phase" [("controls",protectedControls cs),("phase",toJson (phase p))]
def rawOp : Semantics.Raw.Op → Json
  | .init0 o w => tag "init0" [("output",toJson o),("wire",toJson w)]
  | .gate g i o => tag "gate" [("gate",toJson (gate g)),("input",toJson i),("output",toJson o)]
  | .cnot c t co tout => tag "cnot" [("control",toJson c),("target",toJson t),("control_out",toJson co),("target_out",toJson tout)]
  | .toffoli a b t ao bo tout => tag "toffoli" [("control_a",toJson a),("control_b",toJson b),("target",toJson t),
      ("control_a_out",toJson ao),("control_b_out",toJson bo),("target_out",toJson tout)]
  | .quantumIf c t co tout zero one => tag "quantum_if" [("control",toJson c),("target",toJson t),
      ("control_out",toJson co),("target_out",toJson tout),("zero_ops",js (zero.map localOp)),("one_ops",js (one.map localOp))]
  | .split i l r n => tag "split" [("input",toJson i),("left",toJson l),("right",toJson r),("left_bits",toJson n)]
  | .join l r o => tag "join" [("left",toJson l),("right",toJson r),("output",toJson o)]
  | .liftBasis i o wires table => tag "lift_basis" [("input",toJson i),("output",toJson o),("output_wires",toJson wires),("table",toJson table)]
  | .applyUnitary i o steps => tag "apply_unitary" [("input",toJson i),("output",toJson o),("steps",js (steps.map step))]
  | .certifiedCompute i o ancilla function uses logical => tag "certified_compute" [("source",toJson i),("source_out",toJson o),
      ("ancilla_wires",toJson ancilla),("function",toJson function),("use_steps",js (uses.map step)),("logical_steps",js (logical.map step))]
  | .computeUseUncompute i o targets ancilla function uses => tag "compute_use_uncompute" [("source",toJson i),("source_out",toJson o),
      ("targets",js (targets.map fun t => obj [("input",toJson t.input),("output",toJson t.output)])),
      ("ancilla_wires",toJson ancilla),("function",toJson function),("use_ops",js (uses.map usage))]
def operation (fuel : Nat) : Semantics.Observation.Op → Json :=
  Nat.rec (fun _ => Json.null) (fun _ recurse op => match op with
    | .pure op => rawOp op
    | .measure i o => tag "measure_z" [("input",toJson i),("output",toJson o)]
    | .reset i o w => tag "reset" [("input",toJson i),("output",toJson o),("fresh_wire",toJson w)]
    | .discard i => tag "discard" [("input",toJson i)]
    | .constant v o => tag "classical_const" [("value",toJson v),("output",toJson o)]
    | .not i o => tag "classical_not" [("input",toJson i),("output",toJson o)]
    | .xor l r o => tag "classical_xor" [("left",toJson l),("right",toJson r),("output",toJson o)]
    | .and l r o => tag "classical_and" [("left",toJson l),("right",toJson r),("output",toJson o)]
    | .branch c left right quantum classical => tag "classical_branch" [("condition",toJson c),
        ("then_ops",js (left.map recurse)),("else_ops",js (right.map recurse)),
        ("quantum_phis",js (quantum.map fun p => obj [("then_token",toJson p.thenToken),("else_token",toJson p.elseToken),
          ("output",toJson p.output),("output_wires",toJson p.wires)])),
        ("classical_phis",js (classical.map fun p => obj [("then_id",toJson p.thenId),("else_id",toJson p.elseId),("output",toJson p.output)]))]) fuel
def program (p : Semantics.Observation.Program) : Json :=
  obj [("quantum_inputs",js (p.inputs.map fun p => obj [("token",toJson p.token),("wires",toJson p.wires),("shape",obj [("bits",toJson p.bits)])])),
    ("classical_inputs",toJson p.classicalInputs),("operations",js (p.operations.map (operation 65))),
    ("quantum_outputs",toJson p.outputs),("classical_outputs",toJson p.classicalOutputs),
    ("declared_effect",toJson (match p.effect with | .unitary => "unitary" | .iso => "iso" | .observe => "observe"))]
def finiteBasis (b : Semantics.Finite.Basis) : Json :=
  js (b.map fun a => match a with
    | .unit => tag "unit"
    | .bit => tag "bit"
    | .bits n => tag "bits" [("width",toJson n)]
    | .pair => tag "tuple" [("arity",toJson (2 : Nat))]
    | .tuple n => tag "tuple" [("arity",toJson n)])
def qirf (a : Qirf.Artifact) : Json :=
  obj [("programs",Json.arr (a.programs.map program)),("sources",Json.arr (a.sources.map fun s => obj [("path",toJson s.1),("text",toJson s.2)])),
    ("evidence",Json.arr (a.entries.map fun e => obj [("signature",finiteBasis e.signature),("implementation",toJson e.implementation),
      ("target",match e.target with
        | .circuit i => tag "circuit" [("program",toJson i)]
        | .permutation table => tag "permutation" [("table",toJson table)]
        | .phase8 table => tag "phase8" [("table",toJson table)]),
      ("identity",obj [("implementation",toJson e.implementationName),("specification",toJson e.specificationName),("sources",toJson e.sources)])])),
    ("root",toJson a.root),("root_interface",match a.rootInterface with
      | none => Json.null
      | some (i,o) => obj [("input",finiteBasis i),("output",finiteBasis o)])]

open Hierarchical.Artifact in
def hierarchyBasis (b : Basis) : Json :=
  Json.arr (b.map fun a => match a with
    | .unit => tag "unit"
    | .bit => tag "bit"
    | .bits n => tag "bits" [("width",toJson n)]
    | .tuple n => tag "tuple" [("arity",toJson n)])
open Hierarchical.Artifact in
def side (s : Side) : Json := obj [("quantum",Json.arr (s.quantum.map fun p => obj [("owner",toJson p.owner),
    ("basis",hierarchyBasis p.basis),("axes",toJson p.axes)])),
  ("classical",Json.arr (s.classical.map fun p => obj [("value",toJson p.value),("basis",hierarchyBasis p.basis)]))]
def interface (i : Hierarchical.Artifact.Interface) : Json := obj [("inputs",side i.inputs),("outputs",side i.outputs)]
def portMap (m : Hierarchical.Artifact.PortMap) : Json := obj [("owners",toJson m.owners),("axes",toJson m.axes),("classical",toJson m.classical)]
def structural : Hierarchical.Artifact.StructuralOp → Json
  | .takeBit w p => tag "take_bit" [("width",toJson w),("position",toJson p)]
  | .putBit w p => tag "put_bit" [("width",toJson w),("position",toJson p)]
  | .splitTuple => tag "split_tuple" | .joinTuple => tag "join_tuple"
  | .bitToBits => tag "bit_to_bits" | .bitsToBit => tag "bits_to_bit"
  | .packUnit => tag "pack_unit" | .unpackUnit => tag "unpack_unit"
  | .packEmptyBits => tag "pack_empty_bits" | .unpackEmptyBits => tag "unpack_empty_bits"
def bytes (b : ByteArray) : Json := toJson (b.data.map UInt8.toNat)
def body : Hierarchical.Artifact.Body → Json
  | .leaf p => tag "leaf" [("program",bytes p)]
  | .sequence c => tag "sequence" [("children",toJson c)]
  | .tensor l r => tag "tensor" [("left",toJson l),("right",toJson r)]
  | .call d i o => tag "call" [("definition",toJson d),("input_map",portMap i),("output_map",portMap o)]
  | .repeatOp c d => tag "repeat" [("count",toJson c),("definition",toJson d)]
  | .inverse d => tag "inverse" [("definition",toJson d)]
  | .control d p => tag "control" [("definition",toJson d),("polarity",toJson p)]
  | .rewire p => tag "rewire" [("permutation",portMap p)]
  | .structural s => tag "structural" [("operation",structural s)]
  | .dyadicPhase t j k => tag "dyadic_phase" [("target",toJson t),("j",toJson j),("k",toJson k)]
  | .computed c u l e => tag "computed" [("compute",toJson c),("use",toJson u),("logical",toJson l),("encoding",toJson e)]
  | .observeZ i o => tag "observe_z" [("input",toJson i),("output",toJson o)]
  | .init0 o => tag "init0" [("output",toJson o)]
def meaningBody : Hierarchical.Artifact.MeaningBody → Json
  | .identity => tag "identity" | .finite d => tag "finite" [("description",bytes d)]
  | .sequence c => tag "sequence" [("children",toJson c)]
  | .tensor l r => tag "tensor" [("left",toJson l),("right",toJson r)]
  | .inverse c => tag "inverse" [("child",toJson c)]
  | .control c p => tag "control" [("child",toJson c),("polarity",toJson p)]
  | .power c n => tag "power" [("child",toJson c),("count",toJson n)]
  | .rewire p => tag "rewire" [("permutation",portMap p)]
  | .structural s => tag "structural" [("operation",structural s)]
  | .phase j k => tag "phase" [("j",toJson j),("k",toJson k)]
  | .qft w => tag "qft" [("width",toJson w)]
  | .qpeInstrument t p m => tag "qpe_instrument" [("target",toJson t),("precision",toJson p),("provider_meaning",toJson m)]
def encodingBody : Hierarchical.Artifact.EncodingBody → Json
  | .identity => tag "identity" | .tensor l r => tag "tensor" [("left",toJson l),("right",toJson r)]
  | .rewire c p => tag "rewire" [("child",toJson c),("permutation",portMap p)]
  | .zeroScratch s c => tag "zero_scratch" [("scratch_bits",toJson s),("compute",toJson c)]
def rule : Hierarchical.Artifact.Rule → String
  | .finite => "finite" | .sequence => "sequence" | .tensor => "tensor" | .inverse => "inverse" | .control => "control"
  | .repeatOp => "repeat" | .associativity => "associativity" | .rewire => "rewire" | .structural => "structural"
  | .phase => "phase" | .computed => "computed" | .conjugation => "conjugation" | .schema id => id
def hierarchy (a : Hierarchical.Artifact.Artifact) (order : Array Nat) : Json :=
  obj [("definitions",Json.arr (a.definitions.map fun d => obj [("interface",interface d.interface),
      ("effect",toJson (match d.effect with | .unitary => "unitary" | .iso => "iso" | .observe => "observe")),("body",body d.body)])),
    ("meanings",Json.arr (a.meanings.map fun m => obj [("interface",interface m.interface),("body",meaningBody m.body)])),
    ("encodings",Json.arr (a.encodings.map fun e => obj [("logical",side e.logical),("physical",side e.physical),("body",encodingBody e.body)])),
    ("proofs",Json.arr (a.proofs.map fun p => obj [("kind",toJson (match p.kind with | .equation => "equation" | .instrument => "instrument")),
      ("rule",tag (rule p.rule)),("premises",toJson p.premises),("implementation",toJson p.implementation),("meaning",toJson p.meaning),
      ("input_encoding",toJson p.inputEncoding),("output_encoding",toJson p.outputEncoding),
      ("witness",obj [("template_version",toJson p.witness.templateVersion),("parameters",toJson p.witness.parameters),
        ("references",Json.arr (p.witness.references.map fun r => obj [("table",toJson (match r.table with
          | .definition => "definition" | .meaning => "meaning" | .encoding => "encoding" | .proof => "proof")),("index",toJson r.index)]))])])),
    ("entry",obj [("implementation",toJson a.entry.implementation),("proof",toJson a.entry.proof)]),("order",toJson order)]

def execute (value : Json) : Except String Json := do
  let kind ← (← value.getObjVal? "kind").getStr?
  if kind == "qirf" then
    let text ← (← value.getObjVal? "text").getStr?
    return qirf (← Protocol.Qirf.artifact (← Protocol.FiniteCodec.parseWithDepth text 128))
  if kind == "hierarchy" then
    let numbers ← (← (← value.getObjVal? "bytes").getArr?).mapM Json.getNat?
    if !numbers.all (· ≤ 255) then throw "invalid byte"
    let data := ByteArray.mk (numbers.map UInt8.ofNat)
    let (a,order) ← (Protocol.Hierarchical.parse data).mapError (fun _ => "invalid hierarchy")
    return hierarchy a order
  throw "unknown view"

def main : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let result := do execute (← Json.parse line)
    let value := match result with | .ok value => obj [("ok",value)] | .error e => obj [("error",toJson e)]
    output.putStrLn value.compress
