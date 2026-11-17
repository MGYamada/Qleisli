import Protocol.EngineeringPure
import Protocol.EngineeringOpenQasm
import QleisliKernel.Qirf.EngineeringOpenQasmGate

/-! A strict request for an engineering operator/resource comparison. The
artifact body is the original literal OpenQASM gate definition. The ideal
requests retain their original finite QIRF texts and ordered pure leaf ports.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Protocol.EngineeringOpenQasmGate
open Lean Finite Semantics.Exact
open Target.CanonicalOpenQasm (GateCounts)
open Qirf.EngineeringOpenQasmGate (SequentialRequest ControlledRequest CheckedSequential CheckedControlled)
open Qirf.RuntimeInterval (Computed)
open SourceTypes.NaturalAffine (witness)
open EngineeringPure (adapt fields leaf readBound)

structure Ideal where
  leaf : EngineeringPure.Leaf
  original : String

def Ideal.read (ideal : Ideal) : WorkM Qirf.EngineeringPure.LeafRequest := do
  let (artifact,order) ← Qirf.read ideal.original.toUTF8
  return ⟨artifact,order,ideal.leaf.input,ideal.leaf.output,ideal.leaf.required⟩

private def readIdeal (value : Json) : WorkM Ideal := do
  adapt (fields value ["leaf","expected_artifact"])
  let leaf ← leaf (← adapt (value.getObjVal? "leaf"))
  let original ← adapt ((← adapt (value.getObjVal? "expected_artifact")).getStr?)
  guard (!original.isEmpty && original.utf8ByteSize ≤ Validity.maxFileBytes) .limit
  return ⟨leaf,original⟩

structure Component where
  expected : Ideal
  epsilon : Coefficient

private def readComponent (value : Json) : WorkM Component := do
  adapt (fields value ["ideal","epsilon"])
  let expected ← readIdeal (← adapt (value.getObjVal? "ideal"))
  let epsilon ← readBound (← adapt (value.getObjVal? "epsilon"))
  return ⟨expected,epsilon⟩

inductive Contract where
  | sequential (split : Nat) (first second : Component)
  | controlled (ideal : Ideal)

structure Decoded where
  limits : GateCounts
  epsilon : Coefficient
  contract : Contract

def format : String := "qleisli.engineering-openqasm-gate-request"
def claimKind : String := "engineering-target-operator-resource-bound"
def metric : String := "pure-euclidean-operator-norm-v1"
def checkerProfile : String := "canonical-gate-frobenius-r8-v1"
def targetProfile : String := "openqasm3-canonical-ordered-gate-r8-v1"
def resourceModel : String := "openqasm3-ordered-gate-literal-gates-v1"

def decode (value : Json) : WorkM Decoded := do
  let composition ← adapt ((← adapt (value.getObjVal? "composition")).getStr?)
  let common := ["format","version","claim_kind","metric","checker_profile","target_profile",
    "composition","error_category","epsilon","resource_limits"]
  let variant ←
    if composition == "ordered-sequential-two-v1" then pure ["split","first","second"]
    else if composition == "controlled-low-selector-v1" then pure ["ideal"]
    else throw .request
  adapt (fields value (common ++ variant))
  let profile ← adapt (do
    return (← (← value.getObjVal? "format").getStr?) == format &&
      (← (← value.getObjVal? "version").getNat?) == 1 &&
      (← (← value.getObjVal? "claim_kind").getStr?) == claimKind &&
      (← (← value.getObjVal? "metric").getStr?) == metric &&
      (← (← value.getObjVal? "checker_profile").getStr?) == checkerProfile &&
      (← (← value.getObjVal? "target_profile").getStr?) == targetProfile &&
      (← (← value.getObjVal? "error_category").getStr?) == "implementation-distance")
  guard profile .request
  let limits ← EngineeringOpenQasm.gateLimits resourceModel (← adapt (value.getObjVal? "resource_limits"))
  let epsilon ← readBound (← adapt (value.getObjVal? "epsilon"))
  let contract ←
    if composition == "ordered-sequential-two-v1" then do
      let split ← adapt ((← adapt (value.getObjVal? "split")).getNat?)
      let first ← readComponent (← adapt (value.getObjVal? "first"))
      let second ← readComponent (← adapt (value.getObjVal? "second"))
      pure (Contract.sequential split first second)
    else
      pure (Contract.controlled (← readIdeal (← adapt (value.getObjVal? "ideal"))))
  return ⟨limits,epsilon,contract⟩

def sequentialRequest (body : ByteArray) (limits : GateCounts) (total : Coefficient) (split : Nat)
    (first second : Component) (firstLeaf secondLeaf : Qirf.EngineeringPure.LeafRequest) :
    SequentialRequest :=
  ⟨body,limits,split,firstLeaf,secondLeaf,first.epsilon,second.epsilon,total⟩

def controlledRequest (body : ByteArray) (limits : GateCounts) (epsilon : Coefficient)
    (ideal : Qirf.EngineeringPure.LeafRequest) : ControlledRequest :=
  ⟨body,limits,ideal,epsilon⟩

inductive Result (body : ByteArray) (limits : GateCounts) (epsilon : Coefficient) : Contract → Type where
  | sequential {split : Nat} {first second : Component}
      (firstLeaf secondLeaf : Qirf.EngineeringPure.LeafRequest)
      (firstRead : Computed first.expected.read firstLeaf)
      (secondRead : Computed second.expected.read secondLeaf)
      (checked : CheckedSequential (sequentialRequest body limits epsilon split first second firstLeaf secondLeaf)) :
      Result body limits epsilon (.sequential split first second)
  | controlled {ideal : Ideal} (leaf : Qirf.EngineeringPure.LeafRequest)
      (original : Computed ideal.read leaf)
      (checked : CheckedControlled (controlledRequest body limits epsilon leaf)) :
      Result body limits epsilon (.controlled ideal)

def check (body : ByteArray) (decoded : Decoded) :
    WorkM (Result body decoded.limits decoded.epsilon decoded.contract) :=
  match decoded.contract with
  | .sequential split first second => do
    let firstLeaf ← witness first.expected.read
    let secondLeaf ← witness second.expected.read
    let checked ← Qirf.EngineeringOpenQasmGate.checkSequential
      (sequentialRequest body decoded.limits decoded.epsilon split first second firstLeaf.val secondLeaf.val)
    return .sequential firstLeaf.val secondLeaf.val firstLeaf.property secondLeaf.property checked
  | .controlled intended => do
    let ideal ← witness intended.read
    let checked ← Qirf.EngineeringOpenQasmGate.checkControlled
      (controlledRequest body decoded.limits decoded.epsilon ideal.val)
    return .controlled ideal.val ideal.property checked

structure Retained (bytes : ByteArray) where
  prepared : EngineeringPure.Prepared
  frame : EngineeringPure.prepare bytes = .ok prepared
  decoded : Decoded
  decodedRead : Computed (decode prepared.value) decoded
  result : Result prepared.body decoded.limits decoded.epsilon decoded.contract
  resultRead : Computed (check prepared.body decoded) result

def checkRetained (bytes : ByteArray) : WorkM (Retained bytes) := do
  match frame : EngineeringPure.prepare bytes with
  | .error _ => throw .invalid
  | .ok prepared =>
    let decoded ← witness (decode prepared.value)
    let result ← witness (check prepared.body decoded.val)
    return ⟨prepared,frame,decoded.val,decoded.property,result.val,result.property⟩

private theorem witnessed {α : Type} (action : WorkM α)
    (result : {value : α // Computed action value}) (work left : Nat)
    (ran : (witness action).run work = (.ok result,left)) :
    action.run work = (.ok result.val,left) := by
  change (match computed : action.run work with
    | (.error error,remaining) => (Except.error error,remaining)
    | (.ok value,remaining) => (Except.ok (⟨value,work,remaining,computed⟩ :
        {value : α // Computed action value}),remaining)) = (Except.ok result,left) at ran
  split at ran
  · cases ran
  · cases ran
    assumption

structure Binding {bytes : ByteArray} (retained : Retained bytes) (work left : Nat) : Prop where
  frame : EngineeringPure.PreparedBinding bytes retained.prepared
  stages : ∃ afterDecode,
    (decode retained.prepared.value).run work = (.ok retained.decoded,afterDecode) ∧
    (check retained.prepared.body retained.decoded).run afterDecode = (.ok retained.result,left)

/-- Both the parser and literal comparison run on the work state threaded
through this original invocation, with the original inner artifact bytes. -/
theorem checkRetained_bound (bytes : ByteArray) (retained : Retained bytes) (work left : Nat)
    (ran : (checkRetained bytes).run work = (.ok retained,left)) :
    Binding retained work left := by
  unfold checkRetained at ran
  split at ran
  · change (Except.error Error.invalid,work) = (Except.ok retained,left) at ran
    cases ran
  · rename_i prepared framed
    obtain ⟨decoded,afterDecode,decodeRan,rest⟩ := bind_success _ _ _ _ _ ran
    obtain ⟨result,afterCheck,checkRan,finished⟩ := bind_success _ _ _ _ _ rest
    rcases pure_success _ _ _ _ finished with ⟨rfl,rfl⟩
    exact ⟨EngineeringPure.prepare_bound _ _ framed,afterDecode,
      witnessed _ _ _ _ decodeRan,witnessed _ _ _ _ checkRan⟩

#print axioms checkRetained_bound

end QleisliKernel.Protocol.EngineeringOpenQasmGate
