import Qleisli.FinitePull

/-! One-way denotation of successful original finite circuit execution.
Every intermediate vector is from the actual ordered `applyStep` fold. The
independent complex action may be total while a bounded execution fails; no
reverse success implication or equality of bounded work/error behavior is used.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.Finite
open QleisliKernel.Semantics.Exact QleisliKernel.Semantics.Finite QleisliKernel.Finite
open Qleisli.Semantics.Exact

namespace CircuitPull

private theorem except_bind_success {α β : Type} (first : Except Error α)
    (next : α → Except Error β) (result : β) (accepted : (first >>= next) = .ok result) :
    ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first with
  | error error => simp [bind, Except.bind] at accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem fold_length {α : Type} (step : List Scalar → α → Except Error (List Scalar))
    (preserve : ∀ initial item result, step initial item = .ok result → result.length = initial.length)
    (items : List α) (initial result : List Scalar)
    (accepted : items.foldlM step initial = .ok result) : result.length = initial.length := by
  induction items generalizing initial with
  | nil =>
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at accepted
    subst result
    rfl
  | cons item items ih =>
    simp only [List.foldlM_cons] at accepted
    obtain ⟨next, head, tail⟩ := except_bind_success _ _ _ accepted
    exact (ih next tail).trans (preserve initial item next head)

private theorem addAt_length (initial result : List Scalar) (term : Nat × Scalar)
    (accepted : addAt initial term = .ok result) : result.length = initial.length := by
  have sizes := congrArg List.length (addAt_meaning initial result term accepted)
  simpa only [List.length_map, Qleisli.Semantics.Finite.addAt, List.length_set] using sizes

end CircuitPull

/-- The original accumulator preserves its vector dimension on success, even
before a circuit-validity or isometry claim is supplied. -/
theorem applyStep_length (dependencies : List Dependency) (step : Step)
    (values result : List Scalar) (accepted : applyStep dependencies step values = .ok result) :
    result.length = values.length := by
  have visit (initial : List Scalar) (item : Scalar × Nat) (next : List Scalar)
      (ran : (do
        let terms ← contributions dependencies step item.2 item.1
        terms.foldlM addAt initial) = .ok next) : next.length = initial.length := by
    obtain ⟨terms, _read, accumulated⟩ := CircuitPull.except_bind_success _ _ _ ran
    exact CircuitPull.fold_length addAt
      (fun input term output ran => CircuitPull.addAt_length input output term ran)
      terms initial next accumulated
  have sizes := CircuitPull.fold_length _ visit values.zipIdx
    (List.replicate values.length Scalar.zero) result accepted
  simpa only [List.length_replicate] using sizes

/-- A complete valid tape depends only on its actual finite input coordinates.
Controls, ordered axes, original dependencies and adjoints are unchanged. -/
theorem rawCircuit_congr (dependencies : List Dependency) (bits : Nat) (steps : List Step)
    (left right : Nat → ℂ) (valid : steps.all (stepValid dependencies bits) = true)
    (same : ∀ label, label < 2^bits → left label = right label)
    (row : Nat) (bound : row < 2^bits) :
    Qleisli.Semantics.RawAction.circuit dependencies steps left row =
      Qleisli.Semantics.RawAction.circuit dependencies steps right row := by
  induction steps generalizing left right with
  | nil => exact same row bound
  | cons step steps ih =>
    have checked := Bool.and_eq_true_iff.mp valid
    change Qleisli.Semantics.RawAction.circuit dependencies steps
        (Qleisli.Semantics.RawAction.step dependencies step left) row =
      Qleisli.Semantics.RawAction.circuit dependencies steps
        (Qleisli.Semantics.RawAction.step dependencies step right) row
    exact ih _ _ checked.2 (fun label before => rawStep_congr dependencies bits step
      left right checked.1 same label before)

/-- Every successful vector execution has the literal complex action of the
same complete original tape. Success of basis-column reconstruction is not
used to assert that bounded execution succeeds on other vectors. -/
theorem circuit_pull (dependencies : List Dependency) (bits : Nat) (steps : List Step)
    (values result : List Scalar) (valid : steps.all (stepValid dependencies bits) = true)
    (size : values.length = 2^bits)
    (accepted : steps.foldlM (fun values step => applyStep dependencies step values) values = .ok result) :
    result.length = 2^bits ∧ ∀ row, row < 2^bits →
      scalar (result[row]?.getD Scalar.zero) = Qleisli.Semantics.RawAction.circuit dependencies steps
        (fun input => scalar (values[input]?.getD Scalar.zero)) row := by
  induction steps generalizing values with
  | nil =>
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at accepted
    subst result
    exact ⟨size, fun _ _ => rfl⟩
  | cons step steps ih =>
    have checked := Bool.and_eq_true_iff.mp valid
    simp only [List.foldlM_cons] at accepted
    obtain ⟨next, head, tail⟩ := CircuitPull.except_bind_success _ _ _ accepted
    have nextSize := (applyStep_length dependencies step values next head).trans size
    obtain ⟨resultSize, interpreted⟩ := ih next checked.2 nextSize tail
    refine ⟨resultSize, ?_⟩
    intro row bound
    rw [interpreted row bound]
    change Qleisli.Semantics.RawAction.circuit dependencies steps
        (fun input => scalar (next[input]?.getD Scalar.zero)) row =
      Qleisli.Semantics.RawAction.circuit dependencies steps
        (Qleisli.Semantics.RawAction.step dependencies step
          (fun input => scalar (values[input]?.getD Scalar.zero))) row
    exact rawCircuit_congr dependencies bits steps _ _ checked.2
      (fun input before => applyStep_pull dependencies bits step values next input checked.1 size head before)
      row bound

/-- Every reference slice is independent. No factorization, normalization or
finite reference-domain premise is required for the successful-run relation. -/
theorem circuit_pull_reference {Reference : Type} (dependencies : List Dependency)
    (bits : Nat) (steps : List Step) (values result : Reference → List Scalar)
    (valid : steps.all (stepValid dependencies bits) = true)
    (sizes : ∀ reference, (values reference).length = 2^bits)
    (accepted : ∀ reference, steps.foldlM (fun values step => applyStep dependencies step values)
      (values reference) = .ok (result reference)) :
    ∀ reference row, row < 2^bits → scalar ((result reference)[row]?.getD Scalar.zero) =
      Qleisli.Semantics.RawAction.circuit dependencies steps
        (fun input => scalar ((values reference)[input]?.getD Scalar.zero)) row := by
  intro reference row bound
  exact (circuit_pull dependencies bits steps (values reference) (result reference)
    valid (sizes reference) (accepted reference)).2 row bound

#print axioms applyStep_length
#print axioms rawCircuit_congr
#print axioms circuit_pull
#print axioms circuit_pull_reference

end Qleisli.Finite
