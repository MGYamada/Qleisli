import Protocol.ExecutionView.Gate
import Protocol.ExecutionView.Packet
import Protocol.ExecutionView.EngineeringInstrument

/-! Execution-only engineering dispatch with an exact comparison to both fresh
graphs and the typed request. It has no exact accepted-program constructor.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Protocol.ExecutionView.CheckedEngineeringInstrument
open Gate
abbrev Checked := Protocol.EngineeringInstrument.Retained

def check (bytes supplied : ByteArray) : CheckM Checked := do
  guard (framed supplied) .invalidView
  let checked ← native (Protocol.EngineeringInstrument.checkRetained bytes)
  let description ← native (FiniteView.engineeringInstrument checked)
  let expected ← lift ((encode description).mapError fun _ => .encoding)
  guard (supplied.data == expected.data) .decodedView
  return checked

structure Binding (bytes supplied : ByteArray) (checked : Checked) (work left : Nat) where
  afterCore : Nat
  description : Value
  framedView : framed supplied = true
  checkedBound : (Protocol.EngineeringInstrument.checkRetained bytes).run work = (.ok checked,afterCore)
  viewBound : (FiniteView.engineeringInstrument checked).run afterCore = (.ok description,left)
  compared : encode description = .ok supplied

theorem check_binding (bytes supplied : ByteArray) (checked : Checked) (work left : Nat)
    (ok : (check bytes supplied).run work = (.ok checked,left)) :
    Nonempty (Binding bytes supplied checked work left) := by
  unfold check at ok
  obtain ⟨_,a,hf,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨result,b,hc,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨description,c,hv,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨expected,d,he,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,e,hs,h⟩ := bind_success _ _ _ _ _ h
  have final : checked = result ∧ left = e := by cases h; exact ⟨rfl,rfl⟩
  rcases final with ⟨rfl,rfl⟩
  have frame := guard_success _ _ _ _ hf
  have encoded := lift_success _ _ _ _ he
  have same := guard_success _ _ _ _ hs
  have equalData : supplied.data = expected.data := beq_iff_eq.mp same.1
  have equal : supplied = expected := by
    cases supplied
    cases expected
    cases equalData
    rfl
  have encoding : encode description = .ok supplied := by
    cases h : encode description <;> simp_all [Except.mapError]
  have start := frame.2
  have encodedWork := encoded.2
  have comparedWork := same.2
  subst a
  subst d
  subst c
  exact ⟨⟨b,description,frame.1,native_success _ _ _ _ hc,
    native_success _ _ _ _ hv,encoding⟩⟩

theorem Binding.original {bytes supplied : ByteArray} {checked : Checked} {work left : Nat}
    (binding : Binding bytes supplied checked work left) :
    Protocol.EngineeringInstrument.Binding bytes checked work binding.afterCore :=
  Protocol.EngineeringInstrument.checkRetained_bound _ _ _ _ binding.checkedBound

def input (value : Packet.Input) : CheckM Checked :=
  match value.scope with
  | .execution => check value.original value.graph
  | .inspection | .caller => throw .packet

def run (bytes : ByteArray) : CheckM Checked := do
  input (← lift (Packet.read bytes))

/-- The actual outer native invocation selected execution, decoded the exact
inner original packet, and compared the returned engineering record's view. -/
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

end QleisliKernel.Protocol.ExecutionView.CheckedEngineeringInstrument
