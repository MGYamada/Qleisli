import Qleisli.FiniteMatrixAction
import Qleisli.RawDenotation
import QleisliKernel.Target.CanonicalOpenQasmWorkspace
import Protocol.NativeContext.Bindings

/-! Relate a decoded target workspace slice to the actual checked Raw body
in its ordered data-then-scratch interface, including untouched references.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.WorkspaceTargetAction

open QleisliKernel Qirf Target.CanonicalOpenQasmWorkspace
open QleisliKernel.Semantics.Finite

private theorem rows {deps bits steps actual}
    (meaning : Qleisli.Semantics.Raw.CircuitMeaning deps bits steps actual) :
    actual.rows = 2^bits := by
  obtain ⟨_,_,matrix⟩ := meaning
  exact congrArg Semantics.Exact.Matrix.rows matrix

/-- The equality is on the complete local physical interface, including
scratch. The literal Raw body and the decoded target gates both realize the
original source body, retaining its phase on each joint reference column. -/
theorem decoded_action {sources caller deps program block sourceStart sourceCount event events
    original sourceInterval sourceBefore}
    {literal : @RuntimeWorkspace.Literal sources caller deps program block
      sourceStart sourceCount event events original sourceInterval sourceBefore}
    {map : RuntimeWorkspace.CallerMap literal}
    {bytes capacity} {target : Target.CanonicalOpenQasmResources.Checked bytes capacity}
    {layout start count} (checked : Checked map target layout start count)
    {R : Type} (joint : Nat → R → ℂ) (row : Nat) (reference : R)
    (inside : row < 2^(original.layout.bits+1)) :
    Semantics.RawAction.circuit deps checked.gates (fun input => joint input reference) row =
      Semantics.RawAction.circuit deps literal.emitted.steps (fun input => joint input reference) row := by
  obtain ⟨rawWork,rawLeft,rawRead⟩ := literal.equation.checked
  obtain ⟨targetWork,targetLeft,targetRead⟩ := checked.equation.checked
  obtain ⟨rawOriginal,rawAfter,rawChecked⟩ :=
    Raw.Workspace.checkOriginal_bound _ _ _ _ _ _ _ rawWork rawLeft rawRead
  obtain ⟨targetOriginal,targetAfter,targetChecked⟩ :=
    Raw.Workspace.checkOriginal_bound _ _ _ _ _ _ _ targetWork targetLeft targetRead
  obtain ⟨_,_,rawCircuitWork,rawCircuitLeft,_,_,_,_,_,rawCircuit,_,_,_⟩ :=
    Raw.Workspace.check_conditions _ _ _ _ _ _ rawWork rawAfter rawChecked
  obtain ⟨_,_,targetCircuitWork,targetCircuitLeft,_,_,_,_,_,targetCircuit,_,_,_⟩ :=
    Raw.Workspace.check_conditions _ _ _ _ _ _ targetWork targetAfter targetChecked
  have rawRows := rows (Qleisli.Raw.circuit_denotes _ _ _ _ _ _ rawCircuit)
  have targetRows := rows (Qleisli.Raw.circuit_denotes _ _ _ _ _ _ targetCircuit)
  have rawBound : row < literal.equation.actual.rows := rawRows.symm ▸ inside
  have targetBound : row < checked.equation.actual.rows := targetRows.symm ▸ inside
  have rawAction := Qleisli.Finite.circuitMatrix_action deps _ _
    rawCircuitWork rawCircuitLeft rawCircuit joint row reference rawBound
  have targetAction := Qleisli.Finite.circuitMatrix_action deps _ _
    targetCircuitWork targetCircuitLeft targetCircuit joint row reference targetBound
  rw [rawOriginal] at rawAction
  rw [targetOriginal] at targetAction
  exact targetAction.symm.trans rawAction

private theorem unique_slice {circuit scratch}
    {uses : List (CleanUse circuit scratch)} (ordered : uses.Pairwise CleanUse.before)
    {first second : CleanUse circuit scratch} (firstMember : first ∈ uses) (secondMember : second ∈ uses)
    {index : Nat} (firstStart : first.start ≤ index) (firstStop : index < first.start+first.count)
    (secondStart : second.start ≤ index) (secondStop : index < second.start+second.count) :
    first = second := by
  induction ordered with
  | nil => simp at firstMember
  | cons separate _ recurse =>
    simp only [List.mem_cons] at firstMember secondMember
    rcases firstMember with rfl | firstMember <;> rcases secondMember with rfl | secondMember
    · rfl
    · have gap := separate second secondMember
      unfold CleanUse.before at gap
      omega
    · have gap := separate first firstMember
      unfold CleanUse.before at gap
      omega
    · exact recurse firstMember secondMember

/-- Each gate touching a reused clean wire belongs to exactly one counted
restoration interval. The position is in the original target word, and the
interval contains its checked number of literal steps. -/
theorem clean_access_counted_once {bytes capacity}
    {target : Target.CanonicalOpenQasmResources.Checked bytes capacity}
    {scratch uses} (reuse : Reuse target scratch uses)
    (index : Nat) (gate : Target.CanonicalOpenQasmResources.Instruction)
    (actual : target.circuit.gates[index]? = some gate) (touches : scratch ∈ gate.wires) :
    ∃! use, use ∈ uses ∧ use.start ≤ index ∧ index < use.start+use.count ∧
      use.steps.length = use.count ∧ use.start+use.count ≤ target.circuit.counts.gates := by
  obtain ⟨use,member,start,stop,length,bounded⟩ :=
    reuse.prepared_and_counted.2.2 index gate actual touches
  refine ⟨use,⟨member,start,stop,length,bounded⟩,?_⟩
  rintro other ⟨present,otherStart,otherStop,_,_⟩
  exact unique_slice reuse.ordered present member otherStart otherStop start stop

/-- Successful native placement binds each use of the reserved clean
location to a unique restoration slice counted in the decoded artifact.
The wire is prepared by the literal reset and absent from terminal readout. -/
theorem native_clean_access_counted_once (product : String) (bytes : ByteArray)
    (decision : Protocol.NativeContext.Decision .openQasmPlacement) (work left : Nat)
    (ok : (Protocol.NativeContext.run .openQasmPlacement product bytes).run work = (.ok decision,left)) :
    let placed := decision.value.2
    let circuit := placed.target.circuit
    ∀ scratch ∈ placed.proposal.reserved,
      scratch < circuit.counts.reset ∧ scratch ∉ circuit.measurements ∧
      ∀ index gate, circuit.gates[index]? = some gate → scratch ∈ gate.wires →
        ∃! use, use ∈ placed.placement.trace.recorded.cleanUses scratch ∧
          use.start ≤ index ∧ index < use.start+use.count ∧ use.steps.length = use.count ∧
          use.start+use.count ≤ circuit.counts.gates := by
  obtain ⟨checked,_,_,rfl⟩ := Protocol.NativeContext.run_openqasm_placement_binding product bytes decision work left ok
  dsimp only
  intro scratch member
  obtain ⟨reuse⟩ := checked.placement.trace.restored scratch member
  exact ⟨reuse.prepared_and_counted.2.1,reuse.unmeasured,clean_access_counted_once reuse⟩

#print axioms native_clean_access_counted_once
#print axioms decoded_action
end Qleisli.WorkspaceTargetAction
