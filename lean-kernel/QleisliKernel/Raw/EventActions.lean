import QleisliKernel.Raw.EventClean

/-! Dependency agreement for actual event matrices, including computed bodies.
This supplies no original source/event correspondence or accepted handle.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Raw.EventTransport
open QleisliKernel QleisliKernel.Semantics.Finite QleisliKernel.Semantics.Exact
open QleisliKernel.Raw.DependencyTransport

def ActionAgrees (left right : List Dependency) : Semantics.Raw.Event → Prop
  | .circuit _ steps => StepsAgree left right steps
  | .computed _ _ _ _ _ uses logical => StepsAgree left right uses ∧ StepsAgree left right logical
  | _ => True

theorem protected_event {left right event} (same : ActionAgrees left right event) :
    Raw.ProtectedEvaluation.eventMatrix left event =
      Raw.ProtectedEvaluation.eventMatrix right event := by
  cases event with
  | circuit bits steps =>
    change StepsAgree left right steps at same
    have equal := circuit_matrix (left := left) (right := right) (circuit := Raw.circuit bits steps) same
    change (do
      Finite.guard (bits ≤ 6) .limit
      Finite.circuitMatrix left (Raw.circuit bits steps)) = (do
      Finite.guard (bits ≤ 6) .limit
      Finite.circuitMatrix right (Raw.circuit bits steps))
    rw [equal]
  | computed bits axes source ancilla table uses logical =>
    change StepsAgree left right uses ∧ StepsAgree left right logical at same
    have equal := clean (left := left) (right := right) source axes.length ancilla table uses logical same.1 same.2
    change (do
      Finite.guard (bits ≤ 6) .limit
      let logical ← Raw.clean left source axes.length ancilla table uses logical
      Raw.promote bits axes logical) = (do
      Finite.guard (bits ≤ 6) .limit
      let logical ← Raw.clean right source axes.length ancilla table uses logical
      Raw.promote bits axes logical)
    rw [equal]
  | init0 _ => rfl
  | liftBasis _ _ _ _ _ => rfl
  | reorder _ _ => rfl
  | protectedComputed _ _ _ _ _ _ => rfl

end QleisliKernel.Raw.EventTransport
