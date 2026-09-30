import Qleisli.Semantics.InstrumentCoordinates
import Qleisli.HierarchicalFourier
/-! A phase-sensitive, reference-parametric calibration of the independent
instrument specification: CNOT into fresh zero followed by S on the old bit.
The measured bit is correlated with the retained bit; its phase cannot be
checked from uniform/diagonal probabilities alone.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.InstrumentExamples
open Qleisli.Semantics.Instrument
noncomputable def copyingPhase : Coefficient := fun output input =>
  match output,input with
  | [a,b],[c,d] => if a = c ∧ b = Bool.xor c d then (if c then Complex.I else 1) else 0
  | _,_ => 0
theorem copyingPhase_branch {R : Type} (input : Input R) (outcome residual : Coordinates) (reference : R) :
    specified [10] [7] [10,7] [10,7] [7] copyingPhase input outcome residual reference =
      if residual 10 = outcome 0 then
        (if outcome 0 then Complex.I else 1) * input [outcome 0] reference else 0 := by
  simp only [specified_coefficient, List.length_cons, List.length_nil]
  rw [Qleisli.HierarchicalFourier.sum_head_tail 1, Fintype.sum_bool]
  simp only [Qleisli.HierarchicalFourier.sum_head_tail 0, Fintype.sum_bool]
  cases h : residual 10 <;> cases k : outcome 0 <;>
    simp [copyingPhase, assignment, QleisliKernel.Semantics.Readout.select,
      List.ofFn_succ, h, k]

/-- Nonconsecutive physical labels do not change the logical branch matrix;
the retained target and measured result remain correlated with relative i. -/
theorem copyingPhase_branchMatrix (outcome output input : Fin 1 → Bool) :
    branchMatrix [10] [10] 1
      (execute [10] [7] [10,7] [10,7] [7] copyingPhase) outcome output input =
      if output 0 = input 0 ∧ outcome 0 = input 0 then
        (if input 0 then Complex.I else 1) else 0 := by
  have column := execute_branchMatrix [10] [7] [10,7] [7] [10] (by decide)
    copyingPhase outcome output input
  simpa [copyingPhase,assignment,QleisliKernel.Semantics.Readout.select,List.ofFn_succ] using column
end Qleisli.InstrumentExamples
