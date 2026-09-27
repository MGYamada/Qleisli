import Quantum.QuantumMechanics.QuantumChannel

/-!
Original Qleisli interoperability probes, Apache-2.0.
Copyright 2026 Masahiko G. Yamada.
These test mathematical interfaces only, not source/IR correspondence.
Tensor factors remain typed; no physical bit flattening is selected here.
-/

namespace QleisliSurvey

open QuantumState QuantumChannel TensorProduct

variable {A B C P Q R Ref Aux : Type}
variable [Qudit A] [Qudit B] [Qudit C] [Qudit P] [Qudit Q] [Qudit R]
variable [Qudit Ref] [Qudit Aux]

/-- Phase-sensitive encoded realization, on the library's linear-map spaces. -/
def Encoded (U : P →ₗ[ℂ] Q) (Ei : A →ₗ[ℂ] P)
    (Eo : B →ₗ[ℂ] Q) (u : A →ₗ[ℂ] B) : Prop :=
  U.comp Ei = Eo.comp u

/-- The same typed middle encoding allows composition without basis enumeration. -/
lemma encoded_seq (U : P →ₗ[ℂ] Q) (V : Q →ₗ[ℂ] R)
    (E0 : A →ₗ[ℂ] P) (E1 : B →ₗ[ℂ] Q) (E2 : C →ₗ[ℂ] R)
    (u : A →ₗ[ℂ] B) (v : B →ₗ[ℂ] C)
    (hU : Encoded U E0 E1 u) (hV : Encoded V E1 E2 v) :
    Encoded (V.comp U) E0 E2 (v.comp u) := by
  unfold Encoded at *
  rw [LinearMap.comp_assoc, hU, ← LinearMap.comp_assoc, hV,
    LinearMap.comp_assoc]

/-- Discarding an independent normalized auxiliary preserves the entire A/Ref
operator. A and Ref may be arbitrarily correlated; no product premise on them.
This is a partial-trace statement, not permission for pure auxiliary release. -/
lemma discard_independent_aux (σ : L Aux) (ρ : L (A ⊗[ℂ] Ref))
    (hσ : Tr σ = 1) :
    Tr₂ (TensorProduct.map σ ρ) = ρ := by
  rw [← l_tensor_equiv_symm_tmul, Tr₂_l_tensor_equiv_symm_tmul, hσ, one_smul]

/-- A local Kraus branch on an arbitrary pure joint input retains its full
unnormalized target/reference output, including a possible zero branch. -/
lemma branch_with_reference (K : A →ₗ[ℂ] B) (ψ : A ⊗[ℂ] Ref) :
    krausTerm (TensorProduct.map K (LinearMap.id : Ref →ₗ[ℂ] Ref))
      (outer_product ψ ψ) =
    outer_product (TensorProduct.map K LinearMap.id ψ)
      (TensorProduct.map K LinearMap.id ψ) := by
  simpa only [krausTerm, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_assoc]
    using comp_outer_product_adjoint
      (TensorProduct.map K (LinearMap.id : Ref →ₗ[ℂ] Ref)) ψ ψ

/-- The branch is completely positive; no trace-preservation of a single
outcome is claimed. Instrument completeness needs a separate condition. -/
lemma branch_with_reference_cp (K : A →ₗ[ℂ] B) :
    IsCompletelyPositive
      (krausTerm (TensorProduct.map K (LinearMap.id : Ref →ₗ[ℂ] Ref))) :=
  krausTerm_isCompletelyPositive _

#print axioms encoded_seq
#print axioms discard_independent_aux
#print axioms branch_with_reference
#print axioms branch_with_reference_cp

end QleisliSurvey
