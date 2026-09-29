import Qleisli.Qpe
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.LinearAlgebra.Matrix.Trace

/-! Completeness of the actual checked QPE instrument, conditional on the
independently verified provider's whole-space isometry equation.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.Qpe
open scoped BigOperators Matrix

variable {T : Type} [Fintype T] [DecidableEq T]

theorem character_star {N : Nat} [NeZero N] (j : ZMod N) :
    star (ZMod.stdAddChar j) = ZMod.stdAddChar (-j) := by
  simp only [ZMod.stdAddChar_apply, AddChar.map_neg_eq_inv]
  exact (Circle.coe_inv_eq_conj _).symm

theorem character_sum {N : Nat} [NeZero N] (j : ZMod N) :
    ∑ y : ZMod N, ZMod.stdAddChar (j * y) = if j = 0 then (N : ℂ) else 0 := by
  split_ifs with h
  · simp [h]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar N h)

/-- QPE uses 1/N, not the normalized QFT's 1/sqrt(N). -/
noncomputable def weight {N : Nat} [NeZero N] (y j : ZMod N) : ℂ :=
  ZMod.stdAddChar (-(j * y)) / N

theorem weight_orthogonal {N : Nat} [NeZero N] (j k : ZMod N) :
    ∑ y : ZMod N, star (weight y j) * weight y k =
      if j = k then (N : ℂ)⁻¹ else 0 := by
  simp only [weight, star_div₀, star_natCast, character_star, neg_neg,
    div_mul_div_comm, ← AddChar.map_add_eq_mul, ← sub_eq_add_neg, ← sub_mul,
    ← Finset.sum_div, character_sum, sub_eq_zero]
  split_ifs <;> simp

omit [DecidableEq T] in
/-- Mixing arbitrary operators exposes precisely the coefficient Gram matrix. -/
theorem mix_gram {I Y : Type} [Fintype I] [Fintype Y]
    (c : Y → I → ℂ) (A : I → Matrix T T ℂ) :
    ∑ y, (∑ j, c y j • A j)ᴴ * (∑ k, c y k • A k) =
      ∑ j, ∑ k, (∑ y, star (c y j) * c y k) • ((A j)ᴴ * A k) := by
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Matrix.sum_mul]
  simp only [Matrix.mul_sum]
  simp only [Matrix.smul_mul]
  simp only [Matrix.mul_smul, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]

theorem mixed_complete {N : Nat} [NeZero N] (A : ZMod N → Matrix T T ℂ)
    (isometries : ∀ j, (A j)ᴴ * A j = 1) :
    Kraus.Complete (fun y => ∑ j, weight y j • A j) := by
  unfold Kraus.Complete
  rw [mix_gram]
  simp only [weight_orthogonal, ite_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, isometries]
  have nonzero : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  simp [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, nonzero]

theorem power_isometry (U : Matrix T T ℂ) (isometry : Uᴴ * U = 1) (j : Nat) :
    (U^j)ᴴ * U^j = 1 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ]
    exact Kraus.isometry_comp U (U^j) isometry ih

theorem finite_index {N : Nat} [NeZero N] (j : Fin N) :
    (ZMod.finEquiv N j).val = j.val := by
  cases N with
  | zero => exact (Fin.elim0 j)
  | succ N => rfl

theorem finite_cast {N : Nat} [NeZero N] (j : Fin N) :
    (j.val : ZMod N) = ZMod.finEquiv N j := by
  simpa only [finite_index] using ZMod.natCast_zmod_val (ZMod.finEquiv N j)

theorem weight_exponential {N : Nat} [NeZero N] (y j : Fin N) :
    weight (ZMod.finEquiv N y) (ZMod.finEquiv N j) =
      Complex.exp (-2 * Real.pi * Complex.I * j.val * y.val / N) / N := by
  have character := ZMod.stdAddChar_coe (N := N) (-((j.val : Int) * y.val))
  push_cast at character
  rw [weight, ← finite_cast, ← finite_cast, character]
  congr 2
  ring

theorem kraus_modular (width : Nat) (U : Matrix T T ℂ) (y : Fin (2^width)) :
    kraus width U y.val =
      ∑ j : ZMod (2^width), weight (ZMod.finEquiv (2^width) y) j • U^j.val := by
  unfold kraus
  apply Fintype.sum_equiv (ZMod.finEquiv (2^width)).toEquiv
  intro j
  change _ = weight (ZMod.finEquiv (2^width) y) (ZMod.finEquiv (2^width) j) •
    U^(ZMod.finEquiv (2^width) j).val
  rw [weight_exponential, finite_index]
  simp only [Nat.cast_pow, Nat.cast_ofNat]

/-- All outcomes must be included, and the actual provider must be isometric.
The branch equation alone (which also holds for nonunitary U) is insufficient. -/
theorem kraus_complete (width : Nat) (U : Matrix T T ℂ) (isometry : Uᴴ * U = 1) :
    Kraus.Complete (fun y : Fin (2^width) => kraus width U y.val) := by
  have complete := mixed_complete (fun j : ZMod (2^width) => U^j.val)
    (fun j => power_isometry U isometry j.val)
  unfold Kraus.Complete at complete ⊢
  rw [← complete]
  apply Fintype.sum_equiv (ZMod.finEquiv (2^width)).toEquiv
  intro y
  dsimp only
  rw [kraus_modular]
  rfl

/-- temporary (TP-006), importance P1: Current QPE projection interface. Replacement: actual
hierarchical instrument acceptance with the same exact branches, all-outcome
completeness, trace and reference preservation, including verified provider
evidence. Retire after caller/registry migration and public API compatibility
review. Keep generic Kraus completeness, character and reference/trace laws.

Completeness for the actual accepted circuit components, in bit order. -/
theorem checked_complete (operations : Nat → Matrix T T ℂ) (width target : Nat)
    (stages : List QleisliKernel.ControlledPowers.Stage)
    (powers : QleisliKernel.ControlledPowers.check width target stages = true)
    (definitions : List QleisliKernel.QftGraph.Definition) (entry : Nat)
    (receipt : QleisliKernel.QftGraph.Receipt)
    (qft : QleisliKernel.QftGraph.check definitions entry width = some receipt)
    (actual : QleisliKernel.QftGraph.Action)
    (meaning : QleisliKernel.QftGraph.denote definitions entry = some actual)
    (isometry : (operations target)ᴴ * operations target = 1) :
    Kraus.Complete (branch width (QleisliKernel.Uniform.word width) stages operations actual) := by
  have complete := kraus_complete width (operations target) isometry
  unfold Kraus.Complete at complete ⊢
  rw [← complete]
  apply Fintype.sum_equiv (bitEquiv width)
  intro outcome
  dsimp only
  rw [checked_branch operations width target stages powers definitions entry receipt qft actual meaning,
    bitEquiv_value]

variable {R : Type} [Fintype R] [DecidableEq R]

omit [DecidableEq T] in
theorem withReference_mul (A B : Matrix T T ℂ) :
    withReference (R := R) (A * B) = withReference A * withReference B := by
  ext ⟨i, r⟩ ⟨j, s⟩
  by_cases h : r = s
  · subst s
    simp [withReference, Matrix.mul_apply, Fintype.sum_prod_type]
  · simp [withReference, Matrix.mul_apply, Fintype.sum_prod_type, h]

omit [Fintype T] [DecidableEq T] [Fintype R] in
theorem withReference_conj (A : Matrix T T ℂ) :
    withReference (R := R) Aᴴ = (withReference A)ᴴ := by
  ext ⟨i, r⟩ ⟨j, s⟩
  by_cases h : r = s
  · subst s
    simp [withReference, Matrix.conjTranspose_apply]
  · simp [withReference, Matrix.conjTranspose_apply, h, Ne.symm h]

omit [Fintype T] [Fintype R] in
theorem withReference_one :
    withReference (R := R) (1 : Matrix T T ℂ) = 1 := by
  ext ⟨i, r⟩ ⟨j, s⟩
  by_cases h : r = s <;> simp [withReference, Matrix.one_apply, Prod.ext_iff, h]

omit [Fintype T] [DecidableEq T] [Fintype R] in
theorem withReference_sum {Y : Type} [Fintype Y] (A : Y → Matrix T T ℂ) :
    withReference (R := R) (∑ y, A y) = ∑ y, withReference (A y) := by
  ext ⟨i, r⟩ ⟨j, s⟩
  by_cases h : r = s <;> simp [withReference, Matrix.sum_apply, h]

/-- Completeness holds after tensoring with any finite reference system. -/
theorem complete_withReference {Y : Type} [Fintype Y] (A : Y → Matrix T T ℂ)
    (complete : Kraus.Complete A) :
    Kraus.Complete (fun y => withReference (R := R) (A y)) := by
  unfold Kraus.Complete at complete ⊢
  simp only [← withReference_conj, ← withReference_mul, ← withReference_sum,
    complete, withReference_one]

/-- Total output trace is preserved for arbitrary joint input matrices; no
separability or eigenstate assumption is used. Each outcome remains distinct. -/
theorem complete_trace {Y : Type} [Fintype Y] (A : Y → Matrix T T ℂ)
    (complete : Kraus.Complete A) (rho : Matrix (T × R) (T × R) ℂ) :
    ∑ y, Matrix.trace (outcomeMap (A y) rho) = Matrix.trace rho := by
  have joint := complete_withReference (R := R) A complete
  unfold Kraus.Complete at joint
  calc
    _ = ∑ y, Matrix.trace ((withReference (A y))ᴴ * withReference (A y) * rho) :=
      Finset.sum_congr rfl (fun y _ => Matrix.trace_mul_cycle _ _ _)
    _ = _ := by
      rw [← Matrix.trace_sum, ← Matrix.sum_mul, joint, Matrix.one_mul]

/-- temporary (TP-006), importance P1: Current QPE projection interface. Replacement: actual
hierarchical instrument acceptance with the same exact branches, all-outcome
completeness, trace and reference preservation, including verified provider
evidence. Retire after caller/registry migration and public API compatibility
review. Keep generic Kraus completeness, character and reference/trace laws. -/
theorem checked_plan_complete (targetWidth precision provider : Nat)
    (operations : Nat → Matrix (Fin (2^targetWidth)) (Fin (2^targetWidth)) ℂ)
    (plan : QleisliKernel.Qpe.Plan) (receipt : QleisliKernel.QftGraph.Receipt)
    (accepted : QleisliKernel.Qpe.check targetWidth precision provider plan = some receipt)
    (actual : QleisliKernel.QftGraph.Action)
    (meaning : QleisliKernel.QftGraph.denote plan.fourier plan.fourierEntry = some actual)
    (isometry : (operations provider)ᴴ * operations provider = 1) :
    Kraus.Complete (branch precision plan.preparation plan.powers operations actual) := by
  obtain ⟨_, _, _, preparation, powers, qft⟩ :=
    QleisliKernel.Qpe.check_conditions targetWidth precision provider plan receipt accepted
  rw [preparation]
  exact checked_complete operations precision provider plan.powers powers plan.fourier
    plan.fourierEntry receipt qft actual meaning isometry

/-- temporary (TP-006), importance P1: Current QPE projection interface. Replacement: actual
hierarchical instrument acceptance with the same exact branches, all-outcome
completeness, trace and reference preservation, including verified provider
evidence. Retire after caller/registry migration and public API compatibility
review. Keep generic Kraus completeness, character and reference/trace laws.

Acceptance itself establishes an actual denotation; callers do not need to
assume that graph interpretation succeeds. The remaining provider premise is
explicit and must come from its independent evidence, not from a plan flag. -/
theorem accepted_plan (targetWidth precision provider : Nat)
    (operations : Nat → Matrix (Fin (2^targetWidth)) (Fin (2^targetWidth)) ℂ)
    (plan : QleisliKernel.Qpe.Plan) (receipt : QleisliKernel.QftGraph.Receipt)
    (accepted : QleisliKernel.Qpe.check targetWidth precision provider plan = some receipt)
    (isometry : (operations provider)ᴴ * operations provider = 1) :
    ∃ actual : QleisliKernel.QftGraph.Action,
      QleisliKernel.QftGraph.denote plan.fourier plan.fourierEntry = some actual ∧
      plan.boundary = QleisliKernel.Qpe.header targetWidth precision ∧
      plan.precisionInitial = List.replicate precision false ∧
      Kraus.Complete (branch precision plan.preparation plan.powers operations actual) ∧
      ∀ rho : Matrix (Fin (2^targetWidth) × R) (Fin (2^targetWidth) × R) ℂ,
        (∀ outcome : Fin precision → Bool,
          outcomeMap (branch precision plan.preparation plan.powers operations actual outcome) rho =
            outcomeMap (kraus precision (operations provider)
              (Qft.value precision (Qft.finiteBits outcome))) rho) ∧
        (∑ outcome : Fin precision → Bool,
          Matrix.trace (outcomeMap
            (branch precision plan.preparation plan.powers operations actual outcome) rho)) =
          Matrix.trace rho := by
  obtain ⟨_, boundary, fresh, _, _, qft⟩ :=
    QleisliKernel.Qpe.check_conditions targetWidth precision provider plan receipt accepted
  have meaning := (QleisliKernel.QftGraph.check_sound plan.fourier plan.fourierEntry
    precision receipt qft).2.1
  have complete := checked_plan_complete targetWidth precision provider operations plan receipt
    accepted _ meaning isometry
  refine ⟨_, meaning, boundary, fresh, complete, ?_⟩
  intro rho
  constructor
  · intro outcome
    exact (checked_plan targetWidth precision provider operations plan receipt
      accepted _ meaning outcome rho).2.2
  · exact complete_trace _ complete rho

end Qleisli.Qpe
