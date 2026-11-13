import Qleisli.RawProtectedEvaluation
import QleisliKernel.Qirf.RuntimeComputedUse

/-! The actual checked protected use multiplies each selected source fibre
by the exact scalar recovered from its original auxiliary body. The
reference index remains arbitrary.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeComputedProtectedAction
open QleisliKernel Qirf.RuntimeComputedUse
open Qleisli.Semantics.Exact (scalar)
open Qleisli.Semantics.Protected (blockUse blocks)
open QleisliKernel.Semantics.Raw (Use)

private theorem blocks_diagonal (source aux : Nat) (uses : List Use)
    (noTarget : ∀ controls target gate, Use.targetGate controls target gate ∉ uses) :
    ∃ coefficient : ℂ, ∀ {R : Type} (ψ : Nat → R → ℂ) (target : Nat) (reference : R),
      blocks source aux uses ψ target reference = ψ target reference * coefficient := by
  induction uses with
  | nil => exact ⟨1,by intro; simp [blocks]⟩
  | cons first uses tail =>
    obtain ⟨coefficient,action⟩ := tail (fun controls target gate present =>
      noTarget controls target gate (List.mem_cons_of_mem _ present))
    cases first with
    | targetGate controls target gate => exact False.elim (noTarget controls target gate List.mem_cons_self)
    | protectedGate location gate =>
      refine ⟨(if QleisliKernel.Semantics.Protected.value source aux location then
        Qleisli.Semantics.Finite.phase (if gate == .z then 4 else 1) else 1) * coefficient,?_⟩
      intro R ψ target reference
      change blocks source aux uses (blockUse source aux (.protectedGate location gate) ψ) target reference = _
      rw [action]
      simp only [blockUse,mul_assoc]
    | phase controls operation =>
      refine ⟨(if QleisliKernel.Semantics.Protected.enabled source aux controls then
        Qleisli.Semantics.Finite.phase (QleisliKernel.Semantics.Protected.phaseExponent operation) else 1) * coefficient,?_⟩
      intro R ψ target reference
      change blocks source aux uses (blockUse source aux (.phase controls operation) ψ) target reference = _
      rw [action]
      simp only [blockUse,mul_assoc]

private theorem blocks_mul {R : Type} (source aux : Nat) (uses : List Use)
    (noTarget : ∀ controls target gate, Use.targetGate controls target gate ∉ uses)
    (ψ : Nat → R → ℂ) (target : Nat) (reference : R) :
    blocks source aux uses ψ target reference =
      ψ target reference * blocks source aux uses (fun _ (_ : Unit) => 1) 0 () := by
  obtain ⟨coefficient,action⟩ := blocks_diagonal source aux uses noTarget
  rw [action ψ target reference,action (fun _ (_ : Unit) => 1) 0 (),one_mul]

private theorem scalar_factor {uses : List Use} {source aux : Nat}
    {value : Semantics.Exact.Scalar}
    (computed : Qirf.RuntimeInterval.Computed (factor source aux uses) value) :
    scalar value = blocks source aux uses (fun _ (_ : Unit) => 1) 0 () := by
  obtain ⟨work,left,read⟩ := computed
  apply Qleisli.Raw.ProtectedEvaluation.run_meaning source aux uses _ (fun _ => 1) _ 0 value work left read
  intro label value work left read
  change ((Except.ok Semantics.Exact.Scalar.one : Except Finite.Error Semantics.Exact.Scalar),work) =
    (Except.ok value,left) at read
  have equal : Semantics.Exact.Scalar.one = value := Except.ok.inj (Prod.mk.inj read).1
  subst value
  exact Qleisli.Exact.scalar_one_meaning

theorem auxiliary_fibres {uses : List Use} (action : RawAction uses) (source : Nat)
    {R : Type} (ψ : Nat → R → ℂ) (target : Nat) (reference : R) :
    blocks source 0 uses ψ target reference = ψ target reference * scalar action.zero ∧
    blocks source 1 uses ψ target reference = ψ target reference * scalar action.one := by
  obtain ⟨zero,one⟩ := action.factors source
  constructor
  · rw [scalar_factor zero]
    exact blocks_mul source 0 uses action.noTarget ψ target reference
  · rw [scalar_factor one]
    exact blocks_mul source 1 uses action.noTarget ψ target reference


/-- Use the table evaluated from the original predicate and the full
diagonal of the original body. The same action applies to every reference
and target column of a correlated input. -/
theorem original_phase {sources caller dependencies program block start count event prepared interval before}
    (checked : @Checked sources caller dependencies program block start count event prepared interval before)
    {R : Type} (ψ : Qleisli.Semantics.Protected.Logical R) (source target : Nat) (reference : R)
    {choice : Nat} (chosen : prepared.predicate.table[source]? = some choice) (bit : choice = 0 ∨ choice = 1) :
    Qleisli.Semantics.Protected.logical (fun row => checked.literal.table[row]?.getD 0)
      checked.literal.uses ψ source target reference =
    ψ source target reference * scalar (prepared.action.matrix.entry choice choice) := by
  unfold Qleisli.Semantics.Protected.logical
  simp only [checked.literal.exactTable,chosen,Option.getD_some,← checked.equation]
  obtain ⟨zero,one⟩ := auxiliary_fibres checked.emitted source (ψ source) target reference
  rcases bit with rfl | rfl
  · exact zero
  · exact one

#print axioms auxiliary_fibres
#print axioms original_phase
end Qleisli.RuntimeComputedProtectedAction
