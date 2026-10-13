import Protocol.ExecutionView
import QleisliKernel.Semantics.Observation
import QleisliKernel.Raw.BranchFunction

/-! Typed finite data views, independent of Rust's QIRF writer. These walkers
grant no acceptance authority; native comparison must bind the actual views.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Protocol.ExecutionView.FiniteView
open QleisliKernel.Semantics

private def record (name : String) (fields : List Value) : Value :=
  .array (.text name :: fields)
private def ns (values : List Nat) : Value := .array (values.map .natural)
private def n (value : Nat) : Value := .natural value

def basis (value : Finite.Basis) : Value := .array (value.map fun atom =>
  match atom with
  | .unit => record "unit" []
  | .bit => record "bit" []
  | .bits width => record "bits" [n width]
  | .pair => record "pair" []
  | .tuple arity => record "tuple" [n arity])

private def gate : Raw.Gate → Value
  | .h => n 0 | .x => n 1 | .z => n 2 | .t => n 3
private def phase : Raw.Phase → Value
  | .minusOne => n 0 | .eighthTurn => n 1

def step (value : Finite.Step) : Value :=
  let controls := .array (value.controls.map fun c => record "control" [n c.index,.boolean c.whenOne])
  let action := match value.action with
    | .hadamard target => record "hadamard" [n target]
    | .monomial indices permutation phases => record "monomial" [ns indices,ns permutation,ns phases]
    | .contract indices dependency adjoint => record "contract" [ns indices,n dependency,.boolean adjoint]
  record "step" [controls,action]

private def steps (values : List Finite.Step) : Value := .array (values.map step)

def circuit (value : Finite.Circuit) : Value := record "circuit" [basis value.basis,steps value.steps]

private def unitary : Raw.UnitaryStep → Value
  | .gate g target => record "gate" [gate g,n target]
  | .cnot control target => record "cnot" [n control,n target]
  | .toffoli a b target => record "toffoli" [n a,n b,n target]
  | .phase p => record "phase" [phase p]

private def protectedBit (value : Raw.ProtectedBit) : Value :=
  record "protected-bit" [n (match value.region with | .source => 0 | .ancilla => 1),n value.index]
private def controls (values : List Raw.ProtectedControl) : Value := .array (values.map fun c =>
  record "protected-control" [protectedBit c.bit,.boolean c.whenOne])
private def usage : Raw.Use → Value
  | .protectedGate bit g => record "protected-gate" [protectedBit bit,gate g]
  | .targetGate cs target g => record "target-gate" [controls cs,n target,gate g]
  | .phase cs p => record "protected-phase" [controls cs,phase p]

def pureOperation : Raw.Op → Value
  | .packUnit output => record "pack-unit" [n output]
  | .unpackUnit input => record "unpack-unit" [n input]
  | .init0 output wire => record "init0" [n output,n wire]
  | .gate g input output => record "gate" [gate g,n input,n output]
  | .cnot control target controlOut targetOut => record "cnot" [n control,n target,n controlOut,n targetOut]
  | .toffoli a b target aOut bOut targetOut => record "toffoli" [n a,n b,n target,n aOut,n bOut,n targetOut]
  | .quantumIf control target controlOut targetOut zero one =>
    record "quantum-if" [n control,n target,n controlOut,n targetOut,
      .array (zero.map unitary),.array (one.map unitary)]
  | .split input left right leftBits => record "split" [n input,n left,n right,n leftBits]
  | .join left right output => record "join" [n left,n right,n output]
  | .liftBasis input output wires table => record "lift-basis" [n input,n output,ns wires,ns table]
  | .applyUnitary input output body => record "apply-unitary" [n input,n output,steps body]
  | .certifiedCompute input output ancilla function useSteps logicalSteps =>
    record "certified-compute" [n input,n output,ns ancilla,ns function,steps useSteps,steps logicalSteps]
  | .computeUseUncompute input output targets ancilla function uses =>
    record "compute-use-uncompute" [n input,n output,
      .array (targets.map fun t => record "target" [n t.input,n t.output]),
      ns ancilla,ns function,.array (uses.map usage)]

def operation (fuel : Nat) : Observation.Op → Except String Value :=
  Nat.rec (fun _ => throw "finite view branch capacity") (fun _ recurse op => do
    match op with
    | .pure p => return pureOperation p
    | .measure input output => return record "measure" [n input,n output]
    | .reset input output wire => return record "reset" [n input,n output,n wire]
    | .discard input => return record "discard" [n input]
    | .constant value output => return record "constant" [.boolean value,n output]
    | .not input output => return record "not" [n input,n output]
    | .xor left right output => return record "xor" [n left,n right,n output]
    | .and left right output => return record "and" [n left,n right,n output]
    | .branch condition thenOps elseOps quantum classical =>
      return record "branch" [n condition,
        .array (← thenOps.mapM recurse),.array (← elseOps.mapM recurse),
        .array (quantum.map fun p => record "quantum-phi" [n p.thenToken,n p.elseToken,n p.output,ns p.wires]),
        .array (classical.map fun p => record "classical-phi" [n p.thenId,n p.elseId,n p.output])]) fuel

def program (value : Observation.Program) : Except String Value := do
  return record "program" [
    .array (value.inputs.map fun p => record "port" [n p.token,ns p.wires,n p.bits]),
    ns value.classicalInputs,.array (← value.operations.mapM (operation 65)),
    ns value.outputs,ns value.classicalOutputs,
    n (match value.effect with | .unitary => 0 | .iso => 1 | .observe => 2)]

def matrix (value : Exact.Matrix) : Value :=
  record "matrix" [n value.rows,n value.cols,.array (value.entries.map fun x =>
    .array ([x.a,x.b,x.c,x.d].map fun c => record "dyadic" [.text (toString c.numerator),n c.exponent]))]

/-- Derive the execution circuit from the original literal body. Branch frame
changes rename subsequent coordinates; only the final composite permutation
becomes a circuit action. This helper confers no acceptance authority. -/
def functionCircuit (signature : Finite.Basis) (implementation : Observation.Program) :
    Finite.WorkM Finite.Circuit := do
  let prepared ← Finite.lift (Finite.readOption (Observation.read implementation))
  let bits := Finite.width signature
  Finite.guard (prepared.inputBits == bits && bits ≤ 6) .limit
  let (_,events) ← Raw.BranchFunction.selected 65 prepared.events []
  let (body,route) ← events.foldlM (fun (body,route) event => do
    match event with
    | .reorder width axes =>
      Finite.guard (width == bits && axes.length == bits && axes.all (· < bits))
      pure (body,axes.map (fun axis => route[axis]?.getD 0))
    | _ => do
      let added ← Finite.lift (Finite.readOption (Function.extracted event))
      Finite.guard (body.length + added.length ≤ 1024) .limit
      Finite.exactWork (Exact.charge (1 + added.length))
      pure (body ++ added.map (RawTrace.localize route),route)) ([],List.range bits)
  let final := if route == List.range bits then [] else
    [Finite.Step.mk [] (.monomial (List.range bits)
      ((List.range (2^bits)).map fun label => Finite.gather label route)
      (List.replicate (2^bits) 0))]
  Finite.guard (body.length + final.length ≤ 1024) .limit
  return ⟨signature,body ++ final⟩

/-- A fresh native receipt supplies the independently checked matrix and
accounting. Its circuit is separately derived from its original implementation.
The eventual gate must retain and compare all graph entries, not accept a
host-supplied receipt through this data walker. -/
def functionEvidence (receipt : ObservingFunction.Receipt) : Finite.WorkM Value := do
  let implementation ← Finite.lift ((program receipt.input.implementation).mapError (fun _ => .invalid))
  let specification ← Finite.lift ((program receipt.input.specification).mapError (fun _ => .invalid))
  let actual ← functionCircuit receipt.input.signature receipt.input.implementation
  let identity := receipt.input.identity
  return record "function-evidence" [basis receipt.input.signature,implementation,specification,
    record "identity" [.text identity.implementation,.text identity.specification,
      .array (identity.sources.map fun source => record "source" [.text source.1,.text source.2])],
    circuit actual,matrix receipt.meaning,n receipt.depth,n receipt.expandedSteps]

end QleisliKernel.Protocol.ExecutionView.FiniteView
