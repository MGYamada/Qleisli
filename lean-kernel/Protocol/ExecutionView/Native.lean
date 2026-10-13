import Protocol.ExecutionView.Packet
import Protocol.ExecutionView.CheckedCaller
import Protocol.ExecutionView.CheckedHierarchy

/-! Actual versioned native dispatch. A scope is a requested checking operation,
never a caller-supplied success receipt.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Protocol.ExecutionView.Native
open Gate

inductive Ordinary where
  | inspection (requested : Bool)
  | execution (checked : CheckedFinite.Checked)
  | caller (checked : CheckedFinite.Checked)

def Ordinary.scope : Ordinary → Packet.Scope
  | .inspection _ => .inspection | .execution _ => .execution | .caller _ => .caller

def Ordinary.requested : Ordinary → Bool
  | .inspection requested => requested
  | .execution checked | .caller checked => checked.requirement.isSome

def ordinaryInput (input : Packet.Input) : CheckM Ordinary := do
  match input.scope with
  | .inspection => return .inspection (← native (Validity.check input.original))
  | .execution => return .execution (← CheckedFinite.check input.original input.graph)
  | .caller => return .caller (← CheckedCaller.finite input.original input.graph input.caller input.indices)

def ordinary (bytes : ByteArray) : CheckM Ordinary := do
  ordinaryInput (← lift (Packet.read bytes))

def contractInput (input : Packet.Input) : CheckM NativeContract.Retained :=
  match input.scope with
  | .inspection => native (NativeContract.checkRetained input.original)
  | .execution => CheckedContract.check input.original input.graph
  | .caller => CheckedCaller.contract input.original input.graph input.caller input.indices

def contract (bytes : ByteArray) : CheckM (Packet.Scope × NativeContract.Retained) := do
  let input ← lift (Packet.read bytes)
  return (input.scope,← contractInput input)

def hierarchyInput (mode : CheckedHierarchy.Modes.Mode) (input : Packet.Input) :
    CheckM CheckedHierarchy.Modes.Inspected :=
  match input.scope with
  | .inspection => CheckedHierarchy.Modes.inspectMode mode input.original
  | .execution => CheckedHierarchy.Modes.checkMode mode input.original input.graph
  | .caller => throw .packet

def hierarchy (mode : CheckedHierarchy.Modes.Mode) (bytes : ByteArray) :
    CheckM (Packet.Scope × CheckedHierarchy.Modes.Inspected) := do
  let input ← lift (Packet.read bytes)
  return (input.scope,← hierarchyInput mode input)

def errorCode : Gate.Error → String
  | .packet | .invalidView | .encoding => "format"
  | .decodedView => "decoded_view"
  | .native .limit | .hierarchy .limit _ => "limit"
  | .native .request | .native .equation | .hierarchy .contract _ => "contract"
  | .native _ | .hierarchy .invalidIr _ => "invalid_ir"

/-- Outer framing preserves the exact original-packet witness in every ordinary
scope, including inspection without an executable host view. Comparison work
is accounted after the original core, not charged to a fictional second run. -/
theorem ordinaryInput_original (input : Packet.Input) (result : Ordinary) (work left : Nat)
    (ok : (ordinaryInput input).run work = (.ok result,left)) :
    ∃ coreLeft, Nonempty (Validity.Acceptance input.original result.requested work coreLeft) := by
  cases scope : input.scope <;> simp only [ordinaryInput,scope] at ok
  · obtain ⟨requested,w,hc,h⟩ := bind_success _ _ _ _ _ ok
    have eq : result = .inspection requested ∧ left = w := by cases h; exact ⟨rfl,rfl⟩
    rcases eq with ⟨rfl,rfl⟩
    exact ⟨left,Validity.check_acceptance _ _ _ _ (native_success _ _ _ _ hc)⟩
  · obtain ⟨checked,w,hc,h⟩ := bind_success _ _ _ _ _ ok
    have eq : result = .execution checked ∧ left = w := by cases h; exact ⟨rfl,rfl⟩
    rcases eq with ⟨rfl,rfl⟩
    obtain ⟨binding⟩ := CheckedFinite.check_binding _ _ _ _ _ hc
    exact ⟨binding.afterCore,⟨binding.original⟩⟩
  · obtain ⟨checked,w,hc,h⟩ := bind_success _ _ _ _ _ ok
    have eq : result = .caller checked ∧ left = w := by cases h; exact ⟨rfl,rfl⟩
    rcases eq with ⟨rfl,rfl⟩
    obtain ⟨binding⟩ := CheckedCaller.finite_binding _ _ _ _ _ _ _ hc
    obtain ⟨original,accepted⟩ := binding.original
    exact ⟨original.afterCore,accepted⟩

theorem ordinary_original (bytes : ByteArray) (result : Ordinary) (work left : Nat)
    (ok : (ordinary bytes).run work = (.ok result,left)) :
    ∃ input, Packet.read bytes = .ok input ∧
      ∃ coreLeft, Nonempty (Validity.Acceptance input.original result.requested work coreLeft) := by
  obtain ⟨input,w,hp,hc⟩ := bind_success _ _ _ _ _ ok
  have parsed := lift_success _ _ _ _ hp
  have same := parsed.2
  subst w
  exact ⟨input,parsed.1,ordinaryInput_original _ _ _ _ hc⟩

/-- Both admitted properties concern the decoded root selected by the original
inner packet witness obtained from this actual outer native invocation. -/
theorem ordinary_root_safe (bytes : ByteArray) (result : Ordinary) (work left : Nat)
    (ok : (ordinary bytes).run work = (.ok result,left)) :
    ∃ input, Packet.read bytes = .ok input ∧
      ∃ coreLeft, ∃ binding : Validity.Acceptance input.original result.requested work coreLeft,
        ∃ program, binding.artifact.programs[binding.artifact.root]? = some program ∧
          Semantics.Ownership.OwnershipSafe program ∧ Semantics.ClassicalScope.ScopeSafe program := by
  obtain ⟨input,parsed,coreLeft,⟨binding⟩⟩ := ordinary_original _ _ _ _ ok
  obtain ⟨checked,checkedBound,facts⟩ := Qirf.Validity.inspect_result _ _ _ _ _ binding.accepted
  obtain ⟨_,owned⟩ := Qirf.Validity.check_ownershipSafe _ _ _ _ _ _ checkedBound
  obtain ⟨a,b,verified⟩ := facts.root.verification
  exact ⟨input,parsed,coreLeft,binding,checked.root.program,facts.root.original,
    owned,Raw.Observation.verify_scopeSafe _ _ _ _ _ verified⟩

theorem contract_binding (bytes : ByteArray) (result : Packet.Scope × NativeContract.Retained)
    (work left : Nat) (ok : (contract bytes).run work = (.ok result,left)) :
    ∃ input, Packet.read bytes = .ok input ∧ result.1 = input.scope ∧
      (contractInput input).run work = (.ok result.2,left) := by
  obtain ⟨input,w,hp,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨checked,z,hc,h⟩ := bind_success _ _ _ _ _ h
  have final : result = (input.scope,checked) ∧ left = z := by cases h; exact ⟨rfl,rfl⟩
  rcases final with ⟨rfl,rfl⟩
  have parsed := lift_success _ _ _ _ hp
  have same := parsed.2
  subst w
  exact ⟨input,parsed.1,rfl,hc⟩

theorem hierarchy_binding (mode : CheckedHierarchy.Modes.Mode) (bytes : ByteArray)
    (result : Packet.Scope × CheckedHierarchy.Modes.Inspected) (work left : Nat)
    (ok : (hierarchy mode bytes).run work = (.ok result,left)) :
    ∃ input, Packet.read bytes = .ok input ∧ result.1 = input.scope ∧
      (hierarchyInput mode input).run work = (.ok result.2,left) := by
  obtain ⟨input,w,hp,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨checked,z,hc,h⟩ := bind_success _ _ _ _ _ h
  have final : result = (input.scope,checked) ∧ left = z := by cases h; exact ⟨rfl,rfl⟩
  rcases final with ⟨rfl,rfl⟩
  have parsed := lift_success _ _ _ _ hp
  have same := parsed.2
  subst w
  exact ⟨input,parsed.1,rfl,hc⟩

end QleisliKernel.Protocol.ExecutionView.Native
