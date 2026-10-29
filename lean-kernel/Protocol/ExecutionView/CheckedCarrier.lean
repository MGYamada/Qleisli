import Protocol.Carrier
import Protocol.ExecutionView.Graph
import Protocol.ExecutionView.Packet
import QleisliKernel.Raw.ObservationOwnership
import QleisliKernel.Raw.ObservationScope

/-! Execution-only typed pure gate. Compare the complete freshly checked graph,
both owner forests and logical matrix to the retained host view. The source
declaration reader and original-body gate remain actual computations, not flags.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Protocol.ExecutionView.CheckedCarrier
open Gate Semantics.FiniteCarrier Semantics.CarrierInterface
abbrev Checked := Protocol.Carrier.Checked

private def record (tag : String) (fields : List Value) : Value := .array (.text tag :: fields)

def origin (value : Origin) : Value :=
  record "origin" [.text value.moduleName,.text value.declarationName,.text value.source]

def atom : Atom → Value
  | .unit => record "unit" []
  | .bit => record "bit" []
  | .bits width => record "bits" [.natural width]
  | .pair => record "pair" []
  | .tuple arity => record "tuple" [.natural arity]
  | .enumeration source names => record "enum" [origin source,.array (names.map .text)]
  | .record source names => record "record" [origin source,.array (names.map .text)]

private def owner (value : Owner) : Value :=
  record "typed-owner" [record "port" [.natural value.port.token,
    .array (value.port.wires.map .natural),.natural value.port.bits],.array (value.basis.map atom)]

private def interface (value : Interface) : Value :=
  record "carrier-interface" [.array (value.inputs.map owner),.array (value.outputs.map owner),
    .natural (match value.publicEffect with | .unitary => 0 | .iso => 1 | .observe => 2)]

/-- One complete typed-interface view for the internal finite profiles. -/
def typedInterface (value : Interface) : Value := interface value

def description (checked : Checked) : Finite.WorkM Value := do
  let graph ← FiniteView.graph checked.artifact checked.result.root
  return record "finite-carrier-pure-v1" [graph,interface checked.request.attached,
    interface checked.request.required,FiniteView.matrix checked.request.logical]

def check (bytes supplied : ByteArray) : CheckM Checked := do
  guard (framed supplied) .invalidView
  let checked ← native (Protocol.Carrier.check bytes)
  let view ← native (description checked)
  let expected ← lift ((encode view).mapError fun _ => .encoding)
  guard (supplied.data == expected.data) .decodedView
  return checked

structure Binding (bytes supplied : ByteArray) (checked : Checked) (work left : Nat) where
  afterCore : Nat
  view : Value
  framed : framed supplied = true
  core : (Protocol.Carrier.check bytes).run work = (.ok checked,afterCore)
  described : (description checked).run afterCore = (.ok view,left)
  compared : encode view = .ok supplied

theorem check_binding (bytes supplied : ByteArray) (checked : Checked) (work left : Nat)
    (ok : (check bytes supplied).run work = (.ok checked,left)) :
    Nonempty (Binding bytes supplied checked work left) := by
  unfold check at ok
  obtain ⟨_,a,hf,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨result,b,hc,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨view,c,hv,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨expected,d,he,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,e,hs,h⟩ := bind_success _ _ _ _ _ h
  have final : checked = result ∧ left = e := by cases h; exact ⟨rfl,rfl⟩
  rcases final with ⟨rfl,rfl⟩
  have frame := guard_success _ _ _ _ hf
  have encoded := lift_success _ _ _ _ he
  have same := guard_success _ _ _ _ hs
  have equalData : supplied.data = expected.data := beq_iff_eq.mp same.1
  have equal : supplied = expected := by cases supplied; cases expected; cases equalData; rfl
  have encoding : encode view = .ok supplied := by
    cases value : encode view <;> simp_all [Except.mapError]
  have start := frame.2
  have encodedWork := encoded.2
  have comparedWork := same.2
  subst a; subst d; subst c
  exact ⟨⟨b,view,frame.1,native_success _ _ _ _ hc,native_success _ _ _ _ hv,encoding⟩⟩

theorem Binding.original {bytes supplied : ByteArray} {checked : Checked} {work left : Nat}
    (binding : Binding bytes supplied checked work left) :
    Protocol.Carrier.Binding bytes checked work binding.afterCore :=
  Protocol.Carrier.check_binding _ _ _ _ binding.core

/-- This new pure profile has the original root's independent structural
properties too. This theorem does not enlarge the human-admitted ledger scope. -/
theorem Binding.root_safe {bytes supplied : ByteArray} {checked : Checked} {work left : Nat}
    (binding : Binding bytes supplied checked work left) :
    checked.artifact.programs[checked.artifact.root]? = some checked.result.root.program ∧
      Semantics.Ownership.OwnershipSafe checked.result.root.program ∧
      Semantics.ClassicalScope.ScopeSafe checked.result.root.program := by
  obtain ⟨a,accepted⟩ := binding.original.core
  have facts := Qirf.Carrier.check_postcondition _ _ _ _ _ _ _ _ accepted
  obtain ⟨b,c,root⟩ := facts.root
  obtain ⟨after,checkedRoot⟩ := Qirf.Carrier.sourceRoot_result _ _ _ _ _ _ _ root
  have original := Qirf.Validity.checkRootWithSources_postcondition _ _ _ _ _ _ checkedRoot
  obtain ⟨d,e,verified⟩ := original.verification
  exact ⟨original.original,Raw.Observation.verify_ownershipSafe _ _ _ _ _ verified,
    Raw.Observation.verify_scopeSafe _ _ _ _ _ verified⟩

def input (value : Packet.Input) : CheckM Checked :=
  match value.scope with
  | .execution => check value.original value.graph
  | .inspection | .caller => throw .packet

def run (bytes : ByteArray) : CheckM Checked := do
  input (← lift (Packet.read bytes))

theorem run_binding (bytes : ByteArray) (checked : Checked) (work left : Nat)
    (ok : (run bytes).run work = (.ok checked,left)) :
    ∃ value, Packet.read bytes = .ok value ∧ value.scope = .execution ∧
      Nonempty (Binding value.original value.graph checked work left) := by
  obtain ⟨value,a,hp,h⟩ := bind_success _ _ _ _ _ ok
  have parsed := lift_success _ _ _ _ hp
  have same := parsed.2
  subst a
  cases scope : value.scope with
  | inspection => simp only [input,scope] at h; cases h
  | caller => simp only [input,scope] at h; cases h
  | execution =>
    simp only [input,scope] at h
    exact ⟨value,parsed.1,scope,check_binding _ _ _ _ _ h⟩

end QleisliKernel.Protocol.ExecutionView.CheckedCarrier
