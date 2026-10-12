import Protocol.ExecutionView.Gate
import Protocol.ExecutionView.Hierarchy

/-! Pure hierarchy inspection gate over one fresh structural result and its
exact finite leaves. Production modes and the protocol cutover remain separate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Protocol.ExecutionView.CheckedHierarchy
open Gate
abbrev Error := Gate.Error

structure Checked where
  artifact : Hierarchical.Artifact.Artifact
  order : Array Nat
  structural : Hierarchical.Conditional.Pending
  matrices : HierarchyView.Matrices

private def structureCheck (artifact : Hierarchical.Artifact.Artifact) (order : Array Nat) :
    Except Error Hierarchical.Conditional.Pending :=
  (Hierarchical.Conditional.checkAll artifact order).mapError
    (fun error => .hierarchy error.kind error.atNode)

/-- No intermediate checked record is supplied by the host. The exact leaves
returned here are the ones whose original bodies were checked in this call. -/
def checkInspect (bytes supplied : ByteArray) : CheckM Checked := do
  guard (framed supplied) .invalidView
  let (artifact,order) ← lift ((Protocol.Hierarchical.parse bytes).mapError fun _ => .packet)
  let structural ← lift (structureCheck artifact order)
  let matrices ← native (HierarchyView.reconstructLeaves structural.state.requests)
  let description ← native (HierarchyView.purePlan artifact matrices)
  let expected ← lift ((encode description).mapError fun _ => .encoding)
  guard (supplied.data == expected.data) .decodedView
  return ⟨artifact,order,structural,matrices⟩

structure Binding (bytes supplied : ByteArray) (checked : Checked) (work left : Nat) where
  afterLeaves : Nat
  description : Value
  framedView : framed supplied = true
  packetBound : Protocol.Hierarchical.parse bytes = .ok (checked.artifact,checked.order)
  structuralBound : Hierarchical.Conditional.checkAll checked.artifact checked.order = .ok checked.structural
  leavesBound : (HierarchyView.reconstructLeaves checked.structural.state.requests).run work =
    (.ok checked.matrices,afterLeaves)
  viewBound : (HierarchyView.purePlan checked.artifact checked.matrices).run afterLeaves = (.ok description,left)
  compared : encode description = .ok supplied

theorem checkInspect_binding (bytes supplied : ByteArray) (checked : Checked) (work left : Nat)
    (ok : (checkInspect bytes supplied).run work = (.ok checked,left)) :
    Nonempty (Binding bytes supplied checked work left) := by
  unfold checkInspect at ok
  obtain ⟨_,w₀,hf,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨input,w₁,hp,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨structural,w₂,hc,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨matrices,w₃,hm,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨description,w₄,hv,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨expected,w₅,he,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₆,hs,h⟩ := bind_success _ _ _ _ _ h
  cases h
  have frame := guard_success _ _ _ _ hf
  have packet := lift_success _ _ _ _ hp
  have core := lift_success _ _ _ _ hc
  have encoded := lift_success _ _ _ _ he
  have same := guard_success _ _ _ _ hs
  have bound : Protocol.Hierarchical.parse bytes = .ok input := by
    cases h : Protocol.Hierarchical.parse bytes <;> simp_all [Except.mapError]
  have checkedCore : Hierarchical.Conditional.checkAll input.1 input.2 = .ok structural := by
    cases h : Hierarchical.Conditional.checkAll input.1 input.2 <;>
      simp_all [structureCheck,Except.mapError]
  have equalData : supplied.data = expected.data := beq_iff_eq.mp same.1
  have equal : supplied = expected := by
    cases supplied; cases expected; cases equalData; rfl
  have encoding : encode description = .ok supplied := by
    cases h : encode description <;> simp_all [Except.mapError]
  have start := frame.2
  have packetWork := packet.2
  have coreWork := core.2
  have encodingWork := encoded.2
  have compareWork := same.2
  subst w₀; subst w₁; subst w₂; subst w₅; subst left
  exact ⟨⟨w₃,description,frame.1,bound,checkedCore,
    native_success _ _ _ _ hm,native_success _ _ _ _ hv,encoding⟩⟩

end QleisliKernel.Protocol.ExecutionView.CheckedHierarchy
