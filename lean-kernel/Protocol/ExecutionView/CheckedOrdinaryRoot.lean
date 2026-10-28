import Protocol.OrdinaryRoot
import Protocol.ExecutionView.CheckedCarrier
import Protocol.ExecutionView.Graph
import Protocol.ExecutionView.Packet
import QleisliKernel.Raw.ObservationOwnership
import QleisliKernel.Raw.ObservationScope

/-! Execution-only ordinary-result gate. Compare the complete actual graph,
original selected entry, nominal type, storage tree and public effect with the
retained host objects after fresh complete-history checking.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Protocol.ExecutionView.CheckedOrdinaryRoot
open Gate Semantics.FiniteCarrier Semantics.CarrierInterface
abbrev Checked := Protocol.OrdinaryRoot.Checked

private def record (tag : String) (fields : List Value) : Value := .array (.text tag :: fields)

private def storage : Nat → Semantics.OrdinaryValue.Storage → Finite.WorkM Value :=
  Nat.rec (fun _ => throw .limit) (fun _ next value => do
    Finite.exactWork (Exact.charge 1)
    match value with
    | .unit => return record "unit" []
    | .bit id => return record "bit" [.natural id]
    | .bits ids => return record "bits" [.array (ids.map .natural)]
    | .enumeration source ids =>
      return record "enum" [CheckedCarrier.origin source,.array (ids.map .natural)]
    | .pair first second => return record "pair" [← next first,← next second]
    | .tuple fields => return record "tuple" [.array (← fields.mapM next)]
    | .record source fields =>
      let children ← fields.mapM fun (name,value) => do
        return record "field" [.text name,← next value]
      return record "record" [CheckedCarrier.origin source,.array children])

def description (checked : Checked) : Finite.WorkM Value := do
  let graph ← FiniteView.graph checked.artifact checked.result.root
  let request := checked.request
  let stored ← storage 33 request.storage
  let inputs ← request.inputStorage.mapM (storage 33)
  return record "finite-ordinary-root-v2" [graph,
    .text (match request.selection with
      | .project => "project" | .exported => "exported" | .internal => "internal"),
    .text request.moduleName,.text request.declarationName,
    .array (request.inputs.map (fun basis => .array (basis.map CheckedCarrier.atom))),
    .array inputs,.array (request.inputRows.map (fun row => .array (row.map .boolean))),
    .array (request.basis.map CheckedCarrier.atom),stored,
    .natural (match request.publicEffect with | .unitary => 0 | .iso => 1 | .observe => 2)]

def check (bytes supplied : ByteArray) : CheckM Checked := do
  guard (framed supplied) .invalidView
  let checked ← native (Protocol.OrdinaryRoot.check bytes)
  let view ← native (description checked)
  let expected ← lift ((encode view).mapError fun _ => .encoding)
  guard (supplied.data == expected.data) .decodedView
  return checked

structure Binding (bytes supplied : ByteArray) (checked : Checked) (work left : Nat) where
  afterCore : Nat
  view : Value
  framed : framed supplied = true
  core : (Protocol.OrdinaryRoot.check bytes).run work = (.ok checked,afterCore)
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
    Protocol.OrdinaryRoot.Binding bytes checked :=
  Protocol.OrdinaryRoot.check_binding _ _ _ _ binding.core

/-- This ordinary-result profile has the original root's independent structural
properties too. This theorem does not enlarge the human-admitted ledger scope. -/
theorem Binding.root_safe {bytes supplied : ByteArray} {checked : Checked} {work left : Nat}
    (_binding : Binding bytes supplied checked work left) :
    checked.artifact.programs[checked.artifact.root]? = some checked.result.root.program ∧
      Semantics.Ownership.OwnershipSafe checked.result.root.program ∧
      Semantics.ClassicalScope.ScopeSafe checked.result.root.program := by
  exact checked.result.original_safe

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

end QleisliKernel.Protocol.ExecutionView.CheckedOrdinaryRoot
