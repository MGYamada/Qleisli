import Protocol.ExecutionView.Gate
import Protocol.ExecutionView.Packet
import Protocol.ExecutionView.EngineeringOpenQasmGate

/-! Execution-only dispatch for literal OpenQASM gate engineering. The exact
view compares the original target, typed request and independently decoded ideal
graphs under the same work state.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Protocol.ExecutionView.CheckedEngineeringOpenQasmGate
open Gate
open Protocol.EngineeringOpenQasmGate (Retained Result)
open Qirf.EngineeringOpenQasmGate (Block)

def check (bytes supplied : ByteArray) : CheckM (Retained bytes) := do
  guard (framed supplied) .invalidView
  let checked ← native (Protocol.EngineeringOpenQasmGate.checkRetained bytes)
  let description ← native (FiniteView.engineeringOpenQasmGate checked)
  let expected ← lift ((encode description).mapError fun _ => .encoding)
  guard (supplied.data == expected.data) .decodedView
  return checked

structure Binding (bytes supplied : ByteArray) (checked : Retained bytes) (work left : Nat) where
  afterCore : Nat
  description : Value
  framedView : framed supplied = true
  checkedBound : (Protocol.EngineeringOpenQasmGate.checkRetained bytes).run work = (.ok checked,afterCore)
  viewBound : (FiniteView.engineeringOpenQasmGate checked).run afterCore = (.ok description,left)
  compared : encode description = .ok supplied

theorem check_binding (bytes supplied : ByteArray) (checked : Retained bytes) (work left : Nat)
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

theorem Binding.original {bytes supplied : ByteArray} {checked : Retained bytes} {work left : Nat}
    (binding : Binding bytes supplied checked work left) :
    Protocol.EngineeringOpenQasmGate.Binding checked work binding.afterCore :=
  Protocol.EngineeringOpenQasmGate.checkRetained_bound _ _ _ _ binding.checkedBound

structure Checked where
  packet : Packet.Input
  retained : Retained packet.original

private def resultBlock {body limits epsilon contract} :
    Result body limits epsilon contract → Block
  | .sequential _ _ _ _ value => value.target.block
  | .controlled _ _ value => value.target.block

private theorem resultBlock_read {body limits epsilon contract}
    (result : Result body limits epsilon contract) :
    Qirf.EngineeringOpenQasmGate.decode body = some (resultBlock result) := by
  cases result with
  | sequential _ _ _ _ value => exact value.target.read
  | controlled _ _ value => exact value.target.read

private theorem resultBlock_bounds {body limits epsilon contract}
    (result : Result body limits epsilon contract) : (resultBlock result).counts.within limits = true := by
  cases result with
  | sequential _ _ _ _ value => exact value.target.within
  | controlled _ _ value => exact value.target.within

def Checked.block (checked : Checked) : Block := resultBlock checked.retained.result

theorem Checked.block_read (checked : Checked) :
    Qirf.EngineeringOpenQasmGate.decode checked.retained.prepared.body = some checked.block :=
  resultBlock_read checked.retained.result

theorem Checked.block_bounds (checked : Checked) :
    checked.block.counts.within checked.retained.decoded.limits = true :=
  resultBlock_bounds checked.retained.result

private def input (packet : Packet.Input) : CheckM Checked :=
  match packet.scope with
  | .execution => do return ⟨packet,← check packet.original packet.graph⟩
  | .inspection | .caller => throw .packet

def run (bytes : ByteArray) : CheckM Checked := do
  input (← lift (Packet.read bytes))

/-- This invocation selected execution, decoded the original artifact and
request, and independently reconstructed the exact supplied execution view. -/
theorem run_binding (bytes : ByteArray) (checked : Checked) (work left : Nat)
    (ok : (run bytes).run work = (.ok checked,left)) :
    Packet.read bytes = .ok checked.packet ∧ checked.packet.scope = .execution ∧
      Nonempty (Binding checked.packet.original checked.packet.graph checked.retained work left) := by
  obtain ⟨packet,a,hp,h⟩ := bind_success _ _ _ _ _ ok
  have parsed := lift_success _ _ _ _ hp
  have same := parsed.2
  subst a
  cases scope : packet.scope with
  | inspection => simp only [input,scope] at h; cases h
  | caller => simp only [input,scope] at h; cases h
  | execution =>
    simp only [input,scope] at h
    obtain ⟨retained,b,hc,hf⟩ := bind_success _ _ _ _ _ h
    have final : checked = ⟨packet,retained⟩ ∧ left = b := by cases hf; exact ⟨rfl,rfl⟩
    rcases final with ⟨rfl,rfl⟩
    exact ⟨parsed.1,scope,check_binding _ _ _ _ _ hc⟩

#print axioms run_binding

end QleisliKernel.Protocol.ExecutionView.CheckedEngineeringOpenQasmGate
