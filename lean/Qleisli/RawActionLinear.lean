import Qleisli.Semantics.RawAction
import Qleisli.ExactMatrix

/-! Finite linearity of the independent total complex Raw action.
These are mathematical laws of the literal action, including every control,
phase, ordered axis and original dependency entry. They make no assertion
about reassociating bounded scalar computations or their work/errors.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.Semantics.RawAction
open QleisliKernel.Semantics.Exact QleisliKernel.Semantics.Finite

theorem step_add (dependencies : List Dependency) (operation : Step)
    (left right : Nat → ℂ) (output : Nat) :
    step dependencies operation (fun input => left input + right input) output =
      step dependencies operation left output + step dependencies operation right output := by
  rcases operation with ⟨controls, action⟩
  simp only [step]
  by_cases disabled : (!enabled controls output) = true
  · simp only [disabled, if_true]
  · simp only [disabled, if_false]
    cases action with
    | hadamard axis =>
      by_cases high : bit output axis = 1 <;>
        simp [Protected.gate, high] <;> ring
    | monomial axes permutation phases =>
      rw [← List.sum_map_add]
      apply Qleisli.Exact.sum_map_congr
      intro input _member
      by_cases selected : permutation[input]? == some (gather output axes)
      · simp only [selected, if_true, add_mul]
      · simp only [selected, if_false, zero_add]
    | contract axes index adjoint =>
      cases dependencies[index]? with
      | none => simp only [zero_add]
      | some dependency =>
        rw [← List.sum_map_add]
        apply Qleisli.Exact.sum_map_congr
        intro input _member
        exact add_mul _ _ _

theorem step_scale (dependencies : List Dependency) (operation : Step)
    (values : Nat → ℂ) (factor : ℂ) (output : Nat) :
    step dependencies operation (fun input => values input * factor) output =
      step dependencies operation values output * factor := by
  rcases operation with ⟨controls, action⟩
  simp only [step]
  by_cases disabled : (!enabled controls output) = true
  · simp only [disabled, if_true]
  · simp only [disabled, if_false]
    cases action with
    | hadamard axis =>
      by_cases high : bit output axis = 1 <;>
        simp [Protected.gate, high] <;> ring
    | monomial axes permutation phases =>
      rw [← List.sum_map_mul_right]
      apply Qleisli.Exact.sum_map_congr
      intro input _member
      by_cases selected : permutation[input]? == some (gather output axes)
      · simp only [selected, if_true]
        ring
      · simp only [selected, if_false, zero_mul]
    | contract axes index adjoint =>
      cases dependencies[index]? with
      | none => simp only [zero_mul]
      | some dependency =>
        rw [← List.sum_map_mul_right]
        apply Qleisli.Exact.sum_map_congr
        intro input _member
        ring

theorem step_zero (dependencies : List Dependency) (operation : Step) (output : Nat) :
    step dependencies operation (fun _ => 0) output = 0 := by
  simpa only [mul_zero] using step_scale dependencies operation (fun _ => 0) 0 output

theorem step_sum {Index : Type} (dependencies : List Dependency) (operation : Step)
    (indices : List Index) (values : Index → Nat → ℂ) (output : Nat) :
    step dependencies operation (fun input => (indices.map (fun index => values index input)).sum) output =
      (indices.map (fun index => step dependencies operation (values index) output)).sum := by
  induction indices with
  | nil => exact step_zero dependencies operation output
  | cons index indices ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [step_add, ih]

theorem circuit_scale (dependencies : List Dependency) (operations : List Step)
    (values : Nat → ℂ) (factor : ℂ) (output : Nat) :
    circuit dependencies operations (fun input => values input * factor) output =
      circuit dependencies operations values output * factor := by
  induction operations generalizing values with
  | nil => rfl
  | cons operation operations ih =>
    change circuit dependencies operations
        (step dependencies operation (fun input => values input * factor)) output =
      circuit dependencies operations (step dependencies operation values) output * factor
    have scaled : step dependencies operation (fun input => values input * factor) =
        (fun input => step dependencies operation values input * factor) := by
      funext input
      exact step_scale dependencies operation values factor input
    rw [scaled]
    exact ih _

theorem circuit_sum {Index : Type} (dependencies : List Dependency) (operations : List Step)
    (indices : List Index) (values : Index → Nat → ℂ) (output : Nat) :
    circuit dependencies operations (fun input => (indices.map (fun index => values index input)).sum) output =
      (indices.map (fun index => circuit dependencies operations (values index) output)).sum := by
  induction operations generalizing values with
  | nil => rfl
  | cons operation operations ih =>
    change circuit dependencies operations
        (step dependencies operation (fun input => (indices.map (fun index => values index input)).sum)) output =
      (indices.map (fun index => circuit dependencies operations
        (step dependencies operation (values index)) output)).sum
    have summed : step dependencies operation (fun input => (indices.map (fun index => values index input)).sum) =
        (fun input => (indices.map (fun index => step dependencies operation (values index) input)).sum) := by
      funext input
      exact step_sum dependencies operation indices values input
    rw [summed]
    exact ih _

#print axioms step_add
#print axioms step_scale
#print axioms circuit_sum
#print axioms circuit_scale

end Qleisli.Semantics.RawAction
