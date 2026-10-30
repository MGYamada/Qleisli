import Protocol.Qmatch
import Protocol.ExecutionView.CheckedCarrier
import Protocol.ExecutionView.Graph
import Protocol.ExecutionView.Packet
import QleisliKernel.Raw.ObservationOwnership
import QleisliKernel.Raw.ObservationScope

/-! Execution-view binding for the internal named-arm source component.
Compare the complete fresh graph, both typed interfaces, original source focus
and actual evidence/control indices. This module alone dispatches no native mode
and constructs no host execution handle.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Protocol.ExecutionView.CheckedQmatch
open Gate Semantics.FiniteCarrier Semantics.CarrierInterface
abbrev Checked := Protocol.Qmatch.Checked

private def record (tag : String) (fields : List Value) : Value := .array (.text tag :: fields)

def source (value : Protocol.Qmatch.SourceSite) : Value :=
  record "source-focus" [.text value.moduleName,.text value.functionName,.natural value.offset]

def arm (value : Qirf.SourceArm.Programs) : Value :=
  record "qmatch-arm" [.natural value.evidence,.natural value.controlled]

def description (checked : Checked) : Finite.WorkM Value := do
  let graph ← FiniteView.graph checked.artifact checked.result.body.root
  return record Protocol.Qmatch.profile [graph,CheckedCarrier.typedInterface checked.request.attached,
    CheckedCarrier.typedInterface checked.request.required,source checked.request.source,
    .array (checked.request.arms.map arm)]

def check (bytes supplied : ByteArray) : CheckM Checked := do
  guard (framed supplied) .invalidView
  let checked ← native (Protocol.Qmatch.check bytes)
  let view ← native (description checked)
  let expected ← lift ((encode view).mapError fun _ => .encoding)
  guard (supplied.data == expected.data) .decodedView
  return checked

structure Binding (bytes supplied : ByteArray) (checked : Checked) (work left : Nat) where
  afterCore : Nat
  view : Value
  framed : framed supplied = true
  core : (Protocol.Qmatch.check bytes).run work = (.ok checked,afterCore)
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
    Protocol.Qmatch.Binding bytes checked work binding.afterCore :=
  Protocol.Qmatch.check_binding _ _ _ _ binding.core

/-- This new pure profile has the original root's independent structural
properties too. This theorem does not enlarge the human-admitted ledger scope. -/
theorem Binding.root_safe {bytes supplied : ByteArray} {checked : Checked} {work left : Nat}
    (binding : Binding bytes supplied checked work left) :
    checked.artifact.programs[checked.artifact.root]? = some checked.result.body.root.program ∧
      Semantics.Ownership.OwnershipSafe checked.result.body.root.program ∧
      Semantics.ClassicalScope.ScopeSafe checked.result.body.root.program := by
  obtain ⟨a,accepted⟩ := binding.original.core
  obtain ⟨b,original⟩ := checked.result.originalRoot
  obtain ⟨c,d,verified⟩ := original.verification
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

end QleisliKernel.Protocol.ExecutionView.CheckedQmatch
