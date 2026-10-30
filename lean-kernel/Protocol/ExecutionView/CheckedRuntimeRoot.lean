import Protocol.RuntimeRoot
import Protocol.ExecutionView.CheckedOrdinaryRoot
import Protocol.ExecutionView.Graph
import Protocol.ExecutionView.Packet
import QleisliKernel.Raw.ObservationOwnership
import QleisliKernel.Raw.ObservationScope

/-! Execution-only mixed runtime gate. Compare the complete actual graph,
original selected entry, full parameter/result types, ordinary storage and quantum
ports with retained host objects after fresh complete-input/history checking.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Protocol.ExecutionView.CheckedRuntimeRoot
open Gate Semantics.FiniteCarrier Semantics.CarrierInterface
abbrev Checked := Protocol.RuntimeRoot.Checked

private def record (tag : String) (fields : List Value) : Value := .array (.text tag :: fields)

private def typeAtom : Semantics.RuntimeType.Atom → Value
  | .finite atom => record "finite" [CheckedCarrier.atom atom]
  | .quantum => record "quantum" []

private def storedAtom : Semantics.RuntimeStorage.Atom → Finite.WorkM Value
  | .ordinary basis stored => do
    return record "ordinary" [.array (basis.map CheckedCarrier.atom),
      ← CheckedOrdinaryRoot.storedValue stored]
  | .quantum owner => pure (record "quantum" [CheckedCarrier.typedOwner owner])
  | .tuple arity => pure (record "tuple" [.natural arity])

/-- Describe the actual typed request, not a replay of the submitted JSON. -/
def requestDescription (request : Qirf.RuntimeFamily.Request) : Finite.WorkM (List Value) := do
  let inputs ← request.inputStorage.mapM (fun value => do return .array (← value.mapM storedAtom))
  let stored ← request.storage.mapM storedAtom
  return [.text (match request.selection with
      | .project => "project" | .exported => "exported" | .internal => "internal"),
    .text request.moduleName,.text request.declarationName,
    .array (request.staticArguments.bases.map fun (name,basis) =>
      .array [.text name,.array (basis.map CheckedCarrier.atom)]),
    .array (request.staticArguments.naturals.map fun (name,value) =>
      .array [.text name,.natural value]),
    .array (request.parameters.map (fun tree => .array (tree.map typeAtom))),
    .array inputs,.array (request.inputRows.map (fun row => .array (row.map .boolean))),
    .array (request.result.map typeAtom),.array stored,
    .natural (match request.publicEffect with | .unitary => 0 | .iso => 1 | .observe => 2)]

def description (checked : Checked) : Finite.WorkM Value := do
  let graph ← FiniteView.graph checked.artifact checked.result.root
  return record "finite-runtime-root-v2" (graph :: (← requestDescription checked.request))

def check (bytes supplied : ByteArray) : CheckM Checked := do
  guard (framed supplied) .invalidView
  let checked ← native (Protocol.RuntimeRoot.check bytes)
  let view ← native (description checked)
  let expected ← lift ((encode view).mapError fun _ => .encoding)
  guard (supplied.data == expected.data) .decodedView
  return checked

structure Binding (bytes supplied : ByteArray) (checked : Checked) (work left : Nat) where
  afterCore : Nat
  view : Value
  framed : framed supplied = true
  core : (Protocol.RuntimeRoot.check bytes).run work = (.ok checked,afterCore)
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
    Protocol.RuntimeRoot.Binding bytes checked :=
  Protocol.RuntimeRoot.check_binding _ _ _ _ binding.core

/-- This mixed runtime profile has the original root's independent structural
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

end QleisliKernel.Protocol.ExecutionView.CheckedRuntimeRoot
