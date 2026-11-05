import Qleisli.FiniteMatrixPull
import Qleisli.RawActionLinear

/-! Successful kernel reconstruction denotes the complete literal complex
circuit action on arbitrary joint amplitudes. Linear extension takes place
only in the independent total complex reference; bounded scalar evaluation
on those inputs is neither assumed nor promised.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.Finite
open QleisliKernel.Semantics.Exact QleisliKernel.Semantics.Finite QleisliKernel.Finite
open Qleisli.Semantics.Exact

/-- Complete phase-sensitive action, including arbitrary untouched references.
The same native run supplies the original steps, dependencies and every matrix
column. No separability, normalization or finite reference premise is used. -/
theorem circuitMatrix_action {Reference : Type} (dependencies : List Dependency) (circuit : Circuit)
    (actual : Matrix) (work left : Nat)
    (accepted : (circuitMatrix dependencies circuit).run work = (.ok actual, left))
    (joint : Nat → Reference → ℂ) (row : Nat) (reference : Reference) (bound : row < actual.rows) :
    action actual joint row reference = Qleisli.Semantics.RawAction.circuit dependencies circuit.steps
      (fun input => joint input reference) row := by
  obtain ⟨rows, columns, entries⟩ := circuitMatrix_pull dependencies circuit actual work left accepted
  have rowBound : row < 2^width circuit.basis := by rw [← rows]; exact bound
  have valid := (circuitMatrix_columns dependencies circuit actual work left accepted).1
  have stepsValid : circuit.steps.all (stepValid dependencies (width circuit.basis)) = true := by
    simp only [circuitValid, Bool.and_eq_true] at valid
    tauto
  let values := fun column input => (if input = column then (1 : ℂ) else 0) * joint column reference
  let expanded := fun input => ((List.range (2^width circuit.basis)).map
    (fun column => values column input)).sum
  have same : ∀ input, input < 2^width circuit.basis → expanded input = joint input reference := by
    intro input inputBound
    dsimp only [expanded, values]
    have point (column : Nat) :
        (if input = column then (1 : ℂ) else 0) * joint column reference =
          if input = column then joint column reference else 0 := by
      by_cases selected : input = column <;> simp [selected]
    simp only [point]
    exact Exact.range_delta_sum _ _ _ inputBound
  calc
    action actual joint row reference = ((List.range (2^width circuit.basis)).map
        (fun column => Qleisli.Semantics.RawAction.circuit dependencies circuit.steps
          (fun input => if input = column then 1 else 0) row * joint column reference)).sum := by
      unfold action
      rw [columns]
      apply Exact.sum_map_congr
      intro column member
      rw [entries row column rowBound (List.mem_range.mp member)]
    _ = ((List.range (2^width circuit.basis)).map
        (fun column => Qleisli.Semantics.RawAction.circuit dependencies circuit.steps (values column) row)).sum := by
      apply Exact.sum_map_congr
      intro column _member
      exact (Qleisli.Semantics.RawAction.circuit_scale dependencies circuit.steps
        (fun input => if input = column then 1 else 0) (joint column reference) row).symm
    _ = Qleisli.Semantics.RawAction.circuit dependencies circuit.steps expanded row :=
      (Qleisli.Semantics.RawAction.circuit_sum dependencies circuit.steps
        (List.range (2^width circuit.basis)) values row).symm
    _ = Qleisli.Semantics.RawAction.circuit dependencies circuit.steps (fun input => joint input reference) row :=
      rawCircuit_congr dependencies (width circuit.basis) circuit.steps expanded
        (fun input => joint input reference) stepsValid same row rowBound

#print axioms circuitMatrix_action

end Qleisli.Finite
