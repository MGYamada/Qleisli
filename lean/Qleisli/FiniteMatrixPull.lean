import Qleisli.FiniteCircuitPull
import Mathlib.Data.List.Forall2

/-! Every entry of a successfully reconstructed finite kernel has the literal
complex action of its actual input basis column. Original steps, ordered axes,
dependency indices and adjoint flags are unchanged. This theorem neither
asserts bounded execution on other inputs nor replaces any Gram/native gate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.Finite
open QleisliKernel.Semantics.Exact QleisliKernel.Semantics.Finite QleisliKernel.Finite
open Qleisli.Semantics.Exact

namespace MatrixPull

private theorem map_runs {α β : Type} (step : α → Except Error β)
    (items : List α) (values : List β) (accepted : items.mapM step = .ok values) :
    List.Forall₂ (fun item value => step item = .ok value) items values := by
  induction items generalizing values with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at accepted
    subst values
    exact .nil
  | cons item items ih =>
    simp only [List.mapM_cons] at accepted
    obtain ⟨value, head, tail⟩ := QleisliKernel.Finite.except_bind_success _ _ _ accepted
    obtain ⟨rest, remaining, assembled⟩ := QleisliKernel.Finite.except_bind_success _ _ _ tail
    simp only [pure, Except.pure, Except.ok.injEq] at assembled
    subst values
    exact .cons head (ih rest remaining)

private theorem basis_meaning (dimension column input : Nat) (bound : column < dimension) :
    scalar (((List.range dimension).map
      (fun row => if row == column then Scalar.one else Scalar.zero))[input]?.getD Scalar.zero) =
        if input = column then (1 : ℂ) else 0 := by
  by_cases before : input < dimension
  · simp only [List.getElem?_map, List.getElem?_range, before,
      Option.map_some, Option.getD_some]
    by_cases same : input = column
    · simp [same, Exact.scalar_one_meaning]
    · simp [same, Exact.scalar_zero_meaning]
  · have different : input ≠ column := by
      intro same
      subst input
      exact before bound
    simp [before, different, Exact.scalar_zero_meaning]

end MatrixPull

/-- The actual shared reader supplies every original input column. No proposed
matrix, extracted tape or assumed operator correspondence occurs in the
premises. The one-dimensional zero-bit case retains its complete scalar phase. -/
theorem circuitMatrix_pull (dependencies : List Dependency) (circuit : Circuit)
    (actual : Matrix) (work left : Nat)
    (accepted : (circuitMatrix dependencies circuit).run work = (.ok actual, left)) :
    actual.rows = 2^width circuit.basis ∧ actual.cols = 2^width circuit.basis ∧
      ∀ row column, row < 2^width circuit.basis → column < 2^width circuit.basis →
        entry actual row column = Qleisli.Semantics.RawAction.circuit dependencies circuit.steps
          (fun input => if input = column then 1 else 0) row := by
  obtain ⟨valid, columns, read, actualEq⟩ := circuitMatrix_columns dependencies circuit actual work left accepted
  have stepsValid : circuit.steps.all (stepValid dependencies (width circuit.basis)) = true := by
    simp only [circuitValid, Bool.and_eq_true] at valid
    tauto
  refine ⟨congrArg Matrix.rows actualEq, congrArg Matrix.cols actualEq, ?_⟩
  intro row column rowBound columnBound
  have runs := MatrixPull.map_runs _ _ _ read
  have length : columns.length = 2^width circuit.basis := by
    simpa only [List.length_range] using runs.length_eq.symm
  have columnIn : column < columns.length := by rw [length]; exact columnBound
  have ran := runs.get (i := column) (by simpa only [List.length_range] using columnBound) columnIn
  simp only [List.get_eq_getElem, List.getElem_range] at ran
  let initial := (List.range (2^width circuit.basis)).map
    (fun input => if input == column then Scalar.one else Scalar.zero)
  have interpreted := circuit_pull dependencies (width circuit.basis) circuit.steps
    initial columns[column] stepsValid (by simp [initial]) ran
  have coefficient := interpreted.2 row rowBound
  have initialMeaning : (fun input => scalar (initial[input]?.getD Scalar.zero)) =
      (fun input => if input = column then (1 : ℂ) else 0) := by
    funext input
    exact MatrixPull.basis_meaning _ column input columnBound
  rw [initialMeaning] at coefficient
  have indexBound : row * (2^width circuit.basis) + column <
      (2^width circuit.basis) * (2^width circuit.basis) := by nlinarith
  have indexMod : (row * (2^width circuit.basis) + column) % (2^width circuit.basis) = column := by
    rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt columnBound]
  have indexDiv : (row * (2^width circuit.basis) + column) / (2^width circuit.basis) = row := by
    rw [Nat.add_comm, Nat.add_mul_div_right column row (Nat.two_pow_pos _),
      Nat.div_eq_of_lt columnBound, Nat.zero_add]
  rw [actualEq]
  simpa only [entry, Matrix.entry, List.getElem?_map, List.getElem?_range, indexBound,
    if_true, Option.map_some, Option.getD_some, indexMod, indexDiv,
    List.getElem?_eq_getElem columnIn] using coefficient

#print axioms circuitMatrix_pull

end Qleisli.Finite
