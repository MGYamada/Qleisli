import Qleisli.HierarchicalGradient
import QleisliKernel.Hierarchical.FourierControl

/-! Discharge actual Fourier control/gradient equations from bounded inspection.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
The exact diagonal is derived from physical bodies, not supplied as a premise. -/

namespace Qleisli.HierarchicalFourierControl
open QleisliKernel.Hierarchical
open Artifact HierarchicalSemantics HierarchicalOperators HierarchicalDiagonal HierarchicalGradient

theorem inspect_evaluates (leaves : HierarchicalFiniteEvaluation.Leaves Operator)
    (artifact : Artifact) (precision n index remaining : Nat) (pending : FourierControl.Pending)
    (accepted : FourierControl.inspect artifact precision n index remaining = .ok pending) :
    ∃ fuel actual, HierarchicalFiniteEvaluation.physical algebra leaves artifact fuel index = some actual ∧
      At (n+1) actual (fun bits => if bits 0 then
        phase (number n (fun i => bits i.succ)) (n+1) else 1) := by
  obtain ⟨_,_,_,enough,_,bound,valid,gradient⟩ :=
    FourierControl.inspect_sound artifact precision n index remaining pending accepted
  obtain ⟨root,rootBody,child,_,mode⟩ := bound
  have polarity : pending.request.polarity = true := by
    simp only [FourierControl.shape,Bool.and_eq_true] at valid
    tauto
  rw [polarity] at rootBody
  have ri : width pending.request.root.interface.inputs = n+1 := by
    simp only [FourierControl.shape,Bool.and_eq_true,beq_iff_eq] at valid
    tauto
  have ro : width pending.request.root.interface.outputs = n+1 := by
    simp only [FourierControl.shape,Bool.and_eq_true,beq_iff_eq] at valid
    tauto
  have cw := register_widths pending.request.child n (by
    simp only [FourierControl.shape,Bool.and_eq_true] at valid
    tauto)
  cases count : pending.request.count with
  | none =>
    rw [count] at mode
    have direct : precision = n+1 := by
      simp only [FourierControl.shape,count,Bool.and_eq_true,beq_iff_eq] at valid
      tauto
    rw [mode.1] at rootBody
    rw [direct] at gradient
    exact inspect_controlled leaves artifact n pending.request.gradientIndex
      (remaining-FourierControl.charge pending.request) index pending.gradient gradient
      pending.request.root root rootBody ri ro
  | some k =>
    rw [count] at mode
    have power : k = 2^(precision-(n+1)) := by
      simp only [FourierControl.shape,count,Bool.and_eq_true,beq_iff_eq] at valid
      tauto
    rw [power] at mode
    exact inspect_controlled_power leaves artifact precision n pending.request.gradientIndex
      (remaining-FourierControl.charge pending.request) index pending.request.childIndex pending.gradient gradient
      pending.request.root pending.request.child root rootBody child mode cw.1 cw.2 ri ro enough

end Qleisli.HierarchicalFourierControl
