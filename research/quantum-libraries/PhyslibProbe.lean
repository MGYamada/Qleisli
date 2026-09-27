import QuantumInfo.Measurements.POVM

/-!
Original Qleisli interoperability probes, Apache-2.0.
Copyright 2026 Masahiko G. Yamada.
These test mathematical interfaces only, not source/IR correspondence.
Tensor factors remain typed; no physical bit flattening is selected here.
-/

noncomputable section

namespace QleisliPhyslibSurvey

open Matrix
open scoped BigOperators Kronecker

variable {A B C P Q R Ref Aux X : Type}
variable [Fintype A] [Fintype B] [Fintype C]
variable [Fintype P] [Fintype Q] [Fintype R]
variable [Fintype Ref] [Fintype Aux] [Fintype X]
variable [DecidableEq A] [DecidableEq B] [DecidableEq Ref]
variable [DecidableEq Aux] [DecidableEq X]

/-- Phase-sensitive encoded realization, on the library's matrix spaces. -/
def Encoded (U : Matrix Q P ℂ) (Ei : Matrix P A ℂ)
    (Eo : Matrix Q B ℂ) (u : Matrix B A ℂ) : Prop :=
  U * Ei = Eo * u

omit [Fintype A] [Fintype R] [DecidableEq A] [DecidableEq B] in
/-- Associativity proves composition for arbitrary finite index types.
Matrix multiplication is a denotation here, not a runtime evaluation step. -/
lemma encoded_seq (U : Matrix Q P ℂ) (V : Matrix R Q ℂ)
    (E0 : Matrix P A ℂ) (E1 : Matrix Q B ℂ) (E2 : Matrix R C ℂ)
    (u : Matrix B A ℂ) (v : Matrix C B ℂ)
    (hU : Encoded U E0 E1 u) (hV : Encoded V E1 E2 v) :
    Encoded (V * U) E0 E2 (v * u) := by
  unfold Encoded at *
  rw [Matrix.mul_assoc, hU, ← Matrix.mul_assoc, hV, Matrix.mul_assoc]

/-- The auxiliary is independent; A and Ref need not be independent.
This is a partial-trace statement, not a pure-release authorization. -/
lemma discard_independent_aux (σ : MState Aux) (ρ : MState (A × Ref)) :
    (σ ⊗ᴹ ρ).traceLeft = ρ :=
  MState.traceLeft_prod_eq σ ρ

omit [DecidableEq B] in
/-- A local Kraus action is CP even on the joint target/reference space.
Trace nonincrease requires an additional bound on K; no such claim is made. -/
lemma branch_with_reference_cp (K : Matrix B A ℂ) :
    (MatrixMap.conj (K ⊗ₖ (1 : Matrix Ref Ref ℂ))).IsCompletelyPositive :=
  MatrixMap.conj_isCompletelyPositive _

/-- The library's POVM chooses the square-root (Lüders) instrument.
This records the full quantum output and classical outcome, not just probabilities. -/
lemma lueders_output (Λ : POVM X A) (ρ : Matrix A A ℂ) :
    Λ.measurementMap.map ρ = ∑ x : X,
      (((Λ.mats x ^ (1 / 2 : ℝ)).mat * ρ * (Λ.mats x ^ (1 / 2 : ℝ)).mat)
        ⊗ₖ Matrix.single x x 1) :=
  Λ.measurementMap_apply_matrix ρ

/-- The channel accepts an arbitrary joint mixed input. No product-state
premise is introduced between the measured target and the reference. -/
def measurement_with_reference (Λ : POVM X A) (ρ : MState (A × Ref)) :
    MState ((A × X) × Ref) :=
  (Λ.measurementMap.prod (CPTPMap.id : CPTPMap Ref Ref)) ρ

#print axioms encoded_seq
#print axioms discard_independent_aux
#print axioms branch_with_reference_cp
#print axioms lueders_output
#print axioms measurement_with_reference

end QleisliPhyslibSurvey
