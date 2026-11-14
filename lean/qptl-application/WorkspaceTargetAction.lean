import Qleisli.FiniteMatrixAction
import Qleisli.RawDenotation
import QleisliKernel.Target.CanonicalOpenQasmWorkspace

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

#print axioms decoded_action
end Qleisli.WorkspaceTargetAction
