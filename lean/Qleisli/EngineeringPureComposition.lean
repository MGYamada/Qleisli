import Qleisli.NativeEngineeringPure
import Qleisli.ControlAccess

/-! Phase-sensitive composition of the engineering pure-operator metric.
All operators act on explicit finite Euclidean spaces. These norm inequalities
do not construct source Meaning, exact correspondence, inverse/control access,
cleanup, resource evidence or a constitutional guarantee. In particular a zero
budget has the same engineering-only status as every other budget.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.EngineeringPureComposition
open scoped BigOperators Matrix
open Qleisli.Semantics.EngineeringPure

noncomputable def operator {I O : Type} [Fintype I] [Fintype O]
    (matrix : Matrix O I ℂ) : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ O :=
  by
    classical
    exact LinearMap.toContinuousLinearMap (Matrix.toLpLin 2 2 matrix)

@[simp] theorem operator_apply {I O : Type} [Fintype I] [Fintype O]
    (matrix : Matrix O I ℂ) (vector : EuclideanSpace ℂ I) (row : O) :
    operator matrix vector row = ∑ col, matrix row col * vector col := by
  simp [operator, LinearMap.coe_toContinuousLinearMap', Matrix.toLpLin_apply,
    Matrix.mulVec, dotProduct]

@[simp] theorem operator_sub {I O : Type} [Fintype I] [Fintype O]
    (actual ideal : Matrix O I ℂ) : operator (actual - ideal) = operator actual - operator ideal := by
  ext vector row
  simp [operator_apply, Finset.sum_sub_distrib, sub_mul]

@[simp] theorem operator_mul {I M O : Type} [Fintype I] [Fintype M] [Fintype O]
    (after : Matrix O M ℂ) (before : Matrix M I ℂ) :
    operator (after * before) = (operator after).comp (operator before) := by
  ext vector row
  simp only [operator_apply, ContinuousLinearMap.comp_apply, Matrix.mul_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro middle _
  apply Finset.sum_congr rfl
  intro col _
  ring

/-- A genuinely matching intermediate Euclidean space is part of the type.
The two contraction premises come from exact isometries, independently of the
engineering inequalities. No dimension factor enters the telescoping bound. -/
theorem sequential {I M O : Type} [Fintype I] [Fintype M] [Fintype O]
    (actual₁ ideal₁ : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ M)
    (actual₂ ideal₂ : EuclideanSpace ℂ M →L[ℂ] EuclideanSpace ℂ O)
    (epsilon₁ epsilon₂ : ℝ) (nonnegative₁ : 0 ≤ epsilon₁) (nonnegative₂ : 0 ≤ epsilon₂)
    (actual₂_contracts : ‖actual₂‖ ≤ 1) (ideal₁_contracts : ‖ideal₁‖ ≤ 1)
    (bound₁ : ‖actual₁ - ideal₁‖ ≤ epsilon₁) (bound₂ : ‖actual₂ - ideal₂‖ ≤ epsilon₂) :
    ‖actual₂.comp actual₁ - ideal₂.comp ideal₁‖ ≤ epsilon₁ + epsilon₂ := by
  have telescope : actual₂.comp actual₁ - ideal₂.comp ideal₁ =
      actual₂.comp (actual₁ - ideal₁) + (actual₂ - ideal₂).comp ideal₁ := by
    ext vector
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply, map_sub]
    abel_nf
  rw [telescope]
  calc
    _ ≤ ‖actual₂.comp (actual₁ - ideal₁)‖ + ‖(actual₂ - ideal₂).comp ideal₁‖ := norm_add_le _ _
    _ ≤ ‖actual₂‖ * ‖actual₁ - ideal₁‖ + ‖actual₂ - ideal₂‖ * ‖ideal₁‖ :=
      add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) (ContinuousLinearMap.opNorm_comp_le _ _)
    _ ≤ 1 * epsilon₁ + epsilon₂ * 1 := add_le_add
      ((mul_le_mul_of_nonneg_left bound₁ (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_right actual₂_contracts nonnegative₁))
      (mul_le_mul bound₂ ideal₁_contracts (norm_nonneg _) nonnegative₂)
    _ = _ := by ring

/-- The existing exact Gram equation is sufficient for norm preservation on
the same Euclidean operator, including rectangular matrices. -/
theorem gram_isometry {I O : Type} [Fintype I] [Fintype O] [DecidableEq I]
    (matrix : Matrix O I ℂ) (gram : matrix.conjTranspose * matrix = 1) :
    ∀ vector : EuclideanSpace ℂ I, ‖operator matrix vector‖ = ‖vector‖ := by
  intro vector
  have inner : inner ℂ (operator matrix vector) (operator matrix vector) =
      inner ℂ vector vector := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct]
    rw [dotProduct_comm, dotProduct_comm (WithLp.ofLp vector)]
    change star (matrix *ᵥ WithLp.ofLp vector) ⬝ᵥ (matrix *ᵥ WithLp.ofLp vector) = _
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, gram,
      Matrix.vecMul_one]
  have squared : ‖operator matrix vector‖ ^ 2 = ‖vector‖ ^ 2 := by
    simpa [inner_self_eq_norm_sq_to_K, pow_two] using congrArg Complex.re inner
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp squared

theorem gram_contractive {I O : Type} [Fintype I] [Fintype O] [DecidableEq I]
    (matrix : Matrix O I ℂ) (gram : matrix.conjTranspose * matrix = 1) :
    ‖operator matrix‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro vector
  rw [gram_isometry matrix gram vector, one_mul]

noncomputable def liftLeft {I O R : Type} [Fintype I] [Fintype O] [Fintype R]
    (matrix : Matrix O I ℂ) : Matrix (O × R) (I × R) ℂ :=
  by
    classical
    exact fun row col => if row.2 = col.2 then matrix row.1 col.1 else 0

noncomputable def liftRight {I O R : Type} [Fintype I] [Fintype O] [Fintype R]
    (matrix : Matrix O I ℂ) : Matrix (R × O) (R × I) ℂ :=
  by
    classical
    exact fun row col => if row.1 = col.1 then matrix row.2 col.2 else 0

@[simp] theorem liftLeft_apply {I O R : Type} [Fintype I] [Fintype O] [Fintype R]
    (matrix : Matrix O I ℂ) (joint : EuclideanSpace ℂ (I × R)) (row : O) (reference : R) :
    operator (liftLeft matrix) joint (row,reference) =
      operator matrix (WithLp.toLp 2 (fun col => joint (col,reference))) row := by
  classical
  simp [operator_apply, liftLeft, Fintype.sum_prod_type]

@[simp] theorem liftRight_apply {I O R : Type} [Fintype I] [Fintype O] [Fintype R]
    (matrix : Matrix O I ℂ) (joint : EuclideanSpace ℂ (R × I)) (reference : R) (row : O) :
    operator (liftRight matrix) joint (reference,row) =
      operator matrix (WithLp.toLp 2 (fun col => joint (reference,col))) row := by
  classical
  simp [operator_apply, liftRight, Fintype.sum_prod_type]

/-- An arbitrary reference may be entangled with the system. Summing the
Euclidean fiber bounds preserves the same operator budget. -/
theorem liftLeft_bound {I O R : Type} [Fintype I] [Fintype O] [Fintype R]
    (matrix : Matrix O I ℂ) (epsilon : ℝ) (nonnegative : 0 ≤ epsilon)
    (bound : ‖operator matrix‖ ≤ epsilon) : ‖operator (liftLeft (R := R) matrix)‖ ≤ epsilon := by
  apply ContinuousLinearMap.opNorm_le_bound _ nonnegative
  intro joint
  have fiber (reference : R) :
      ‖operator matrix (WithLp.toLp 2 (fun col => joint (col,reference)))‖ ^ 2 ≤
        epsilon ^ 2 * ‖WithLp.toLp 2 (fun col => joint (col,reference))‖ ^ 2 := by
    have h := (operator matrix).le_opNorm (WithLp.toLp 2 (fun col => joint (col,reference)))
    have h' := h.trans (mul_le_mul_of_nonneg_right bound (norm_nonneg _))
    simpa only [mul_pow] using (sq_le_sq₀ (norm_nonneg _) (mul_nonneg nonnegative (norm_nonneg _))).mpr h'
  have output : ‖operator (liftLeft (R := R) matrix) joint‖ ^ 2 =
      ∑ reference : R, ‖operator matrix (WithLp.toLp 2 (fun col => joint (col,reference)))‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, Finset.sum_comm]
    simp only [liftLeft_apply, EuclideanSpace.norm_sq_eq]
  have input : ‖joint‖ ^ 2 =
      ∑ reference : R, ‖WithLp.toLp 2 (fun col => joint (col,reference))‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, Finset.sum_comm]
    simp only [EuclideanSpace.norm_sq_eq]
  have squared : ‖operator (liftLeft (R := R) matrix) joint‖ ^ 2 ≤ (epsilon * ‖joint‖) ^ 2 := by
    rw [output, mul_pow, input, Finset.mul_sum]
    exact Finset.sum_le_sum fun reference _ => fiber reference
  exact le_of_sq_le_sq squared (mul_nonneg nonnegative (norm_nonneg _))

theorem liftRight_bound {I O R : Type} [Fintype I] [Fintype O] [Fintype R]
    (matrix : Matrix O I ℂ) (epsilon : ℝ) (nonnegative : 0 ≤ epsilon)
    (bound : ‖operator matrix‖ ≤ epsilon) : ‖operator (liftRight (R := R) matrix)‖ ≤ epsilon := by
  apply ContinuousLinearMap.opNorm_le_bound _ nonnegative
  intro joint
  have fiber (reference : R) :
      ‖operator matrix (WithLp.toLp 2 (fun col => joint (reference,col)))‖ ^ 2 ≤
        epsilon ^ 2 * ‖WithLp.toLp 2 (fun col => joint (reference,col))‖ ^ 2 := by
    have h := (operator matrix).le_opNorm (WithLp.toLp 2 (fun col => joint (reference,col)))
    have h' := h.trans (mul_le_mul_of_nonneg_right bound (norm_nonneg _))
    simpa only [mul_pow] using (sq_le_sq₀ (norm_nonneg _) (mul_nonneg nonnegative (norm_nonneg _))).mpr h'
  have output : ‖operator (liftRight (R := R) matrix) joint‖ ^ 2 =
      ∑ reference : R, ‖operator matrix (WithLp.toLp 2 (fun col => joint (reference,col)))‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    simp only [liftRight_apply, EuclideanSpace.norm_sq_eq]
  have input : ‖joint‖ ^ 2 =
      ∑ reference : R, ‖WithLp.toLp 2 (fun col => joint (reference,col))‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    simp only [EuclideanSpace.norm_sq_eq]
  have squared : ‖operator (liftRight (R := R) matrix) joint‖ ^ 2 ≤ (epsilon * ‖joint‖) ^ 2 := by
    rw [output, mul_pow, input, Finset.mul_sum]
    exact Finset.sum_le_sum fun reference _ => fiber reference
  exact le_of_sq_le_sq squared (mul_nonneg nonnegative (norm_nonneg _))

@[simp] theorem liftLeft_sub {I O R : Type} [Fintype I] [Fintype O] [Fintype R]
    (actual ideal : Matrix O I ℂ) :
    liftLeft (R := R) (actual - ideal) = liftLeft actual - liftLeft ideal := by
  classical
  ext row col
  simp only [liftLeft, Matrix.sub_apply]
  split <;> simp

@[simp] theorem liftRight_sub {I O R : Type} [Fintype I] [Fintype O] [Fintype R]
    (actual ideal : Matrix O I ℂ) :
    liftRight (R := R) (actual - ideal) = liftRight actual - liftRight ideal := by
  classical
  ext row col
  simp only [liftRight, Matrix.sub_apply]
  split <;> simp

/-- Ordered product axes: the first component belongs to the left map and the
second to the right map. No flattening or unproved axis permutation occurs. -/
noncomputable def tensor {I₁ O₁ I₂ O₂ : Type}
    [Fintype I₁] [Fintype O₁] [Fintype I₂] [Fintype O₂]
    (left : Matrix O₁ I₁ ℂ) (right : Matrix O₂ I₂ ℂ) : Matrix (O₁ × O₂) (I₁ × I₂) ℂ :=
  fun row col => left row.1 col.1 * right row.2 col.2

theorem tensor_operator {I₁ O₁ I₂ O₂ : Type}
    [Fintype I₁] [Fintype O₁] [Fintype I₂] [Fintype O₂]
    (left : Matrix O₁ I₁ ℂ) (right : Matrix O₂ I₂ ℂ) :
    operator (tensor left right) =
      (operator (liftLeft (R := O₂) left)).comp (operator (liftRight (R := I₁) right)) := by
  classical
  ext joint row
  rcases row with ⟨row₁,row₂⟩
  simp [operator_apply, tensor, liftLeft, liftRight, Fintype.sum_prod_type,
    Finset.mul_sum, mul_assoc]

/-- Exact isometry evidence is separate for the actual and ideal pure maps. -/
structure IsometricPair {I O : Type} [Fintype I] [Fintype O] [DecidableEq I]
    (actual ideal : Matrix O I ℂ) : Prop where
  actualGram : actual.conjTranspose * actual = 1
  idealGram : ideal.conjTranspose * ideal = 1

theorem sequential_matrices {I M O : Type} [Fintype I] [Fintype M] [Fintype O]
    [DecidableEq I] [DecidableEq M]
    (actual₁ ideal₁ : Matrix M I ℂ) (actual₂ ideal₂ : Matrix O M ℂ)
    (pure₁ : IsometricPair actual₁ ideal₁) (pure₂ : IsometricPair actual₂ ideal₂)
    (epsilon₁ epsilon₂ : ℝ) (nonnegative₁ : 0 ≤ epsilon₁) (nonnegative₂ : 0 ≤ epsilon₂)
    (bound₁ : ‖operator (actual₁ - ideal₁)‖ ≤ epsilon₁)
    (bound₂ : ‖operator (actual₂ - ideal₂)‖ ≤ epsilon₂) :
    ‖operator (actual₂ * actual₁ - ideal₂ * ideal₁)‖ ≤ epsilon₁ + epsilon₂ := by
  simp only [operator_sub] at bound₁ bound₂ ⊢
  rw [operator_mul, operator_mul]
  exact sequential _ _ _ _ _ _ nonnegative₁ nonnegative₂
    (gram_contractive _ pure₂.actualGram) (gram_contractive _ pure₁.idealGram) bound₁ bound₂

theorem sequential_reference_bound {I M O R : Type}
    [Fintype I] [Fintype M] [Fintype O] [Fintype R] [DecidableEq I] [DecidableEq M]
    (actual₁ ideal₁ : Matrix M I ℂ) (actual₂ ideal₂ : Matrix O M ℂ)
    (pure₁ : IsometricPair actual₁ ideal₁) (pure₂ : IsometricPair actual₂ ideal₂)
    (epsilon₁ epsilon₂ : ℝ) (nonnegative₁ : 0 ≤ epsilon₁) (nonnegative₂ : 0 ≤ epsilon₂)
    (bound₁ : ‖operator (actual₁ - ideal₁)‖ ≤ epsilon₁)
    (bound₂ : ‖operator (actual₂ - ideal₂)‖ ≤ epsilon₂) :
    ‖operator (liftLeft (R := R) (actual₂ * actual₁ - ideal₂ * ideal₁))‖ ≤ epsilon₁ + epsilon₂ :=
  liftLeft_bound _ _ (add_nonneg nonnegative₁ nonnegative₂)
    (sequential_matrices _ _ _ _ pure₁ pure₂ _ _ nonnegative₁ nonnegative₂ bound₁ bound₂)

theorem tensor_bound {I₁ O₁ I₂ O₂ : Type}
    [Fintype I₁] [Fintype O₁] [Fintype I₂] [Fintype O₂]
    [DecidableEq I₁] [DecidableEq I₂]
    (actual₁ ideal₁ : Matrix O₁ I₁ ℂ) (actual₂ ideal₂ : Matrix O₂ I₂ ℂ)
    (pure₁ : IsometricPair actual₁ ideal₁) (pure₂ : IsometricPair actual₂ ideal₂)
    (epsilon₁ epsilon₂ : ℝ) (nonnegative₁ : 0 ≤ epsilon₁) (nonnegative₂ : 0 ≤ epsilon₂)
    (bound₁ : ‖operator (actual₁ - ideal₁)‖ ≤ epsilon₁)
    (bound₂ : ‖operator (actual₂ - ideal₂)‖ ≤ epsilon₂) :
    ‖operator (tensor actual₁ actual₂ - tensor ideal₁ ideal₂)‖ ≤ epsilon₁ + epsilon₂ := by
  have actualLeft := liftLeft_bound (R := O₂) actual₁ 1 (by norm_num)
    (gram_contractive actual₁ pure₁.actualGram)
  have idealRight := liftRight_bound (R := I₁) ideal₂ 1 (by norm_num)
    (gram_contractive ideal₂ pure₂.idealGram)
  have errorLeft := liftLeft_bound (R := O₂) (actual₁ - ideal₁) epsilon₁ nonnegative₁ bound₁
  have errorRight := liftRight_bound (R := I₁) (actual₂ - ideal₂) epsilon₂ nonnegative₂ bound₂
  simp only [liftLeft_sub, liftRight_sub, operator_sub] at errorLeft errorRight
  rw [operator_sub, tensor_operator, tensor_operator]
  have composed := sequential _ _ _ _ epsilon₂ epsilon₁ nonnegative₂ nonnegative₁
    actualLeft idealRight errorRight errorLeft
  simpa only [add_comm] using composed

/-- The tensor result retains its error budget for every finite reference and
every joint input, with no separability premise or reference-size multiplier. -/
theorem tensor_reference_bound {I₁ O₁ I₂ O₂ R : Type}
    [Fintype I₁] [Fintype O₁] [Fintype I₂] [Fintype O₂] [Fintype R]
    [DecidableEq I₁] [DecidableEq I₂]
    (actual₁ ideal₁ : Matrix O₁ I₁ ℂ) (actual₂ ideal₂ : Matrix O₂ I₂ ℂ)
    (pure₁ : IsometricPair actual₁ ideal₁) (pure₂ : IsometricPair actual₂ ideal₂)
    (epsilon₁ epsilon₂ : ℝ) (nonnegative₁ : 0 ≤ epsilon₁) (nonnegative₂ : 0 ≤ epsilon₂)
    (bound₁ : ‖operator (actual₁ - ideal₁)‖ ≤ epsilon₁)
    (bound₂ : ‖operator (actual₂ - ideal₂)‖ ≤ epsilon₂) :
    ‖operator (liftLeft (R := R)
      (tensor actual₁ actual₂ - tensor ideal₁ ideal₂))‖ ≤ epsilon₁ + epsilon₂ :=
  liftLeft_bound _ _ (add_nonneg nonnegative₁ nonnegative₂)
    (tensor_bound _ _ _ _ pure₁ pure₂ _ _ nonnegative₁ nonnegative₂ bound₁ bound₂)

noncomputable def block {C I O : Type} [Fintype C] [Fintype I] [Fintype O]
    (family : C → Matrix O I ℂ) : Matrix (C × O) (C × I) ℂ := by
  classical
  exact fun row col => if row.1 = col.1 then family row.1 row.2 col.2 else 0

@[simp] theorem block_apply {C I O : Type} [Fintype C] [Fintype I] [Fintype O]
    (family : C → Matrix O I ℂ) (joint : EuclideanSpace ℂ (C × I)) (control : C) (row : O) :
    operator (block family) joint (control,row) =
      operator (family control) (WithLp.toLp 2 (fun col => joint (control,col))) row := by
  classical
  simp [operator_apply, block, Fintype.sum_prod_type]

/-- Coherent blocks retain every complex coefficient. The input may correlate
control, target and reference; this estimate does not perform measurement. -/
theorem block_bound {C I O : Type} [Fintype C] [Fintype I] [Fintype O]
    (family : C → Matrix O I ℂ) (epsilon : ℝ) (nonnegative : 0 ≤ epsilon)
    (bound : ∀ control, ‖operator (family control)‖ ≤ epsilon) :
    ‖operator (block family)‖ ≤ epsilon := by
  apply ContinuousLinearMap.opNorm_le_bound _ nonnegative
  intro joint
  have fiber (control : C) :
      ‖operator (family control) (WithLp.toLp 2 (fun col => joint (control,col)))‖ ^ 2 ≤
        epsilon ^ 2 * ‖WithLp.toLp 2 (fun col => joint (control,col))‖ ^ 2 := by
    have h := (operator (family control)).le_opNorm (WithLp.toLp 2 (fun col => joint (control,col)))
    have h' := h.trans (mul_le_mul_of_nonneg_right (bound control) (norm_nonneg _))
    simpa only [mul_pow] using
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg nonnegative (norm_nonneg _))).mpr h'
  have output : ‖operator (block family) joint‖ ^ 2 =
      ∑ control : C, ‖operator (family control)
        (WithLp.toLp 2 (fun col => joint (control,col)))‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    simp only [block_apply, EuclideanSpace.norm_sq_eq]
  have input : ‖joint‖ ^ 2 =
      ∑ control : C, ‖WithLp.toLp 2 (fun col => joint (control,col))‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    simp only [EuclideanSpace.norm_sq_eq]
  have squared : ‖operator (block family) joint‖ ^ 2 ≤ (epsilon * ‖joint‖) ^ 2 := by
    rw [output, mul_pow, input, Finset.mul_sum]
    exact Finset.sum_le_sum fun control _ => fiber control
  exact le_of_sq_le_sq squared (mul_nonneg nonnegative (norm_nonneg _))

@[simp] theorem operator_zero {I O : Type} [Fintype I] [Fintype O] :
    operator (0 : Matrix O I ℂ) = 0 := by
  ext vector row
  simp [operator_apply]

noncomputable def controlled {I : Type} [Fintype I] [DecidableEq I]
    (matrix : Matrix I I ℂ) : Matrix (Bool × I) (Bool × I) ℂ :=
  block (fun flag => if flag then matrix else 1)

theorem controlled_gap {I : Type} [Fintype I] [DecidableEq I]
    (actual ideal : Matrix I I ℂ) :
    controlled actual - controlled ideal = block (fun flag => if flag then actual - ideal else 0) := by
  classical
  ext row col
  simp only [controlled, block, Matrix.sub_apply]
  by_cases same : row.1 = col.1
  · simp only [if_pos same]
    cases row.1 <;> simp
  · simp only [if_neg same, sub_self]

theorem controlled_bound {I : Type} [Fintype I] [DecidableEq I]
    (actual ideal : Matrix I I ℂ) (epsilon : ℝ) (nonnegative : 0 ≤ epsilon)
    (bound : ‖operator (actual - ideal)‖ ≤ epsilon) :
    ‖operator (controlled actual - controlled ideal)‖ ≤ epsilon := by
  rw [controlled_gap]
  apply block_bound _ _ nonnegative
  intro flag
  cases flag
  · simpa only [Bool.false_eq_true, if_false, operator_zero, norm_zero] using nonnegative
  · simpa only [if_true] using bound

theorem controlled_reference_bound {I R : Type} [Fintype I] [Fintype R] [DecidableEq I]
    (actual ideal : Matrix I I ℂ) (epsilon : ℝ) (nonnegative : 0 ≤ epsilon)
    (bound : ‖operator (actual - ideal)‖ ≤ epsilon) :
    ‖operator (liftLeft (R := R) (controlled actual - controlled ideal))‖ ≤ epsilon :=
  liftLeft_bound _ _ nonnegative (controlled_bound _ _ _ nonnegative bound)

noncomputable def matrixAt (rows cols : Nat) (matrix : QleisliKernel.Semantics.Exact.Matrix) :
    Matrix (Fin rows) (Fin cols) ℂ := fun row col => Qleisli.Semantics.Exact.entry matrix row col

/-- This is the already selected gapCLM metric, rather than another matrix norm. -/
theorem gap_operator (actual ideal : QleisliKernel.Semantics.Exact.Matrix) :
    operator (matrixAt actual.rows actual.cols actual - matrixAt actual.rows actual.cols ideal) =
      gapCLM actual ideal := by
  rfl

private theorem range_sum (n : Nat) (f : Nat → ℂ) :
    ((List.range n).map f).sum = ∑ index : Fin n, f index := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
    rw [Fin.sum_univ_castSucc]
    simpa only [Fin.val_castSucc, Fin.val_last] using congrArg (fun value => value + f n) ih

/-- The actual successful original-body gate supplies precisely the Gram
premise used in the composition theorems, including non-square preparations. -/
theorem leaf_gram (leaf : QleisliKernel.Qirf.EngineeringPure.LeafRequest)
    (domain codomain : QleisliKernel.Semantics.Finite.Basis)
    (checked : QleisliKernel.Qirf.PureLeaf.Checked)
    (meaning : Qleisli.NativeEngineeringPure.LeafMeaning leaf domain codomain checked) :
    (matrixAt leaf.required.rows leaf.required.cols leaf.required).conjTranspose *
      matrixAt leaf.required.rows leaf.required.cols leaf.required = 1 := by
  classical
  ext row col
  have gram := meaning.gram row col row.isLt col.isLt
  rw [range_sum] at gram
  simpa only [matrixAt, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
    Fin.ext_iff] using gram

noncomputable def portMatrix (domain codomain : QleisliKernel.Semantics.Finite.Basis)
    (matrix : QleisliKernel.Semantics.Exact.Matrix) :
    Matrix (Fin (2 ^ QleisliKernel.Semantics.Finite.width codomain))
      (Fin (2 ^ QleisliKernel.Semantics.Finite.width domain)) ℂ :=
  matrixAt _ _ matrix

theorem meaning_isometries (request : QleisliKernel.Qirf.EngineeringPure.Request)
    (checked : QleisliKernel.Qirf.EngineeringPure.Checked)
    (meaning : Qleisli.NativeEngineeringPure.Meaning request checked) :
    IsometricPair (portMatrix request.domain request.codomain request.actual.required)
      (portMatrix request.domain request.codomain request.ideal.required) := by
  constructor
  · have gram := leaf_gram _ _ _ _ meaning.actual
    rw [meaning.actual.rows, meaning.actual.cols] at gram
    exact gram
  · have gram := leaf_gram _ _ _ _ meaning.ideal
    rw [meaning.ideal.rows, meaning.ideal.cols] at gram
    exact gram

theorem meaning_bound (request : QleisliKernel.Qirf.EngineeringPure.Request)
    (checked : QleisliKernel.Qirf.EngineeringPure.Checked)
    (meaning : Qleisli.NativeEngineeringPure.Meaning request checked) :
    ‖operator (portMatrix request.domain request.codomain request.actual.required -
      portMatrix request.domain request.codomain request.ideal.required)‖ ≤
      (Qleisli.Semantics.Exact.rational request.epsilon : ℝ) := by
  have bound := meaning.bound.2.2.2
  rw [← gap_operator] at bound
  rw [meaning.actual.rows, meaning.actual.cols] at bound
  exact bound

/-- Two successful original-artifact comparisons compose on the literal shared
middle type tree. This is a mathematical consequence of those executions, not
a constructor for a native composition receipt or a check of a third artifact. -/
theorem checked_sequential_reference_bound {R : Type} [Fintype R]
    (domain middle codomain : QleisliKernel.Semantics.Finite.Basis)
    (actual₁ ideal₁ actual₂ ideal₂ : QleisliKernel.Qirf.EngineeringPure.LeafRequest)
    (epsilon₁ epsilon₂ : QleisliKernel.Semantics.Exact.Coefficient)
    (checked₁ checked₂ : QleisliKernel.Qirf.EngineeringPure.Checked)
    (work₁ left₁ work₂ left₂ : Nat)
    (ok₁ : (QleisliKernel.Qirf.EngineeringPure.check
      ⟨domain,middle,actual₁,ideal₁,epsilon₁⟩).run work₁ = (.ok checked₁,left₁))
    (ok₂ : (QleisliKernel.Qirf.EngineeringPure.check
      ⟨middle,codomain,actual₂,ideal₂,epsilon₂⟩).run work₂ = (.ok checked₂,left₂)) :
    ‖operator (liftLeft (R := R)
      (portMatrix middle codomain actual₂.required * portMatrix domain middle actual₁.required -
        portMatrix middle codomain ideal₂.required * portMatrix domain middle ideal₁.required))‖ ≤
      (Qleisli.Semantics.Exact.rational epsilon₁ : ℝ) +
        (Qleisli.Semantics.Exact.rational epsilon₂ : ℝ) := by
  have meaning₁ := Qleisli.NativeEngineeringPure.check_meaning _ _ _ _ ok₁
  have meaning₂ := Qleisli.NativeEngineeringPure.check_meaning _ _ _ _ ok₂
  exact sequential_reference_bound _ _ _ _ (meaning_isometries _ _ meaning₁)
    (meaning_isometries _ _ meaning₂) _ _ meaning₁.bound.2.2.1 meaning₂.bound.2.2.1
      (meaning_bound _ _ meaning₁) (meaning_bound _ _ meaning₂)

/-- Rectangular components retain the explicit left/right product order and
the arbitrary reference. Full type trees remain in the two executed requests. -/
theorem checked_tensor_reference_bound {R : Type} [Fintype R]
    (domain₁ codomain₁ domain₂ codomain₂ : QleisliKernel.Semantics.Finite.Basis)
    (actual₁ ideal₁ actual₂ ideal₂ : QleisliKernel.Qirf.EngineeringPure.LeafRequest)
    (epsilon₁ epsilon₂ : QleisliKernel.Semantics.Exact.Coefficient)
    (checked₁ checked₂ : QleisliKernel.Qirf.EngineeringPure.Checked)
    (work₁ left₁ work₂ left₂ : Nat)
    (ok₁ : (QleisliKernel.Qirf.EngineeringPure.check
      ⟨domain₁,codomain₁,actual₁,ideal₁,epsilon₁⟩).run work₁ = (.ok checked₁,left₁))
    (ok₂ : (QleisliKernel.Qirf.EngineeringPure.check
      ⟨domain₂,codomain₂,actual₂,ideal₂,epsilon₂⟩).run work₂ = (.ok checked₂,left₂)) :
    ‖operator (liftLeft (R := R)
      (tensor (portMatrix domain₁ codomain₁ actual₁.required) (portMatrix domain₂ codomain₂ actual₂.required) -
        tensor (portMatrix domain₁ codomain₁ ideal₁.required) (portMatrix domain₂ codomain₂ ideal₂.required)))‖ ≤
      (Qleisli.Semantics.Exact.rational epsilon₁ : ℝ) +
        (Qleisli.Semantics.Exact.rational epsilon₂ : ℝ) := by
  have meaning₁ := Qleisli.NativeEngineeringPure.check_meaning _ _ _ _ ok₁
  have meaning₂ := Qleisli.NativeEngineeringPure.check_meaning _ _ _ _ ok₂
  exact tensor_reference_bound _ _ _ _ (meaning_isometries _ _ meaning₁)
    (meaning_isometries _ _ meaning₂) _ _ meaning₁.bound.2.2.1 meaning₂.bound.2.2.1
      (meaning_bound _ _ meaning₁) (meaning_bound _ _ meaning₂)

/-- A proof record retains independently supplied original-artifact control
access for each body. It does not create access from an engineering bound, and
does not admit source control or assert preservation of a lowered control body. -/
structure ControlledOriginalBound {R : Type} [Fintype R]
    (basis : QleisliKernel.Semantics.Finite.Basis)
    (actual ideal : QleisliKernel.Qirf.EngineeringPure.LeafRequest)
    (epsilon : QleisliKernel.Semantics.Exact.Coefficient)
    (checked : QleisliKernel.Qirf.EngineeringPure.Checked) (axes : List Nat) : Prop where
  actualAccess : Qleisli.ControlAccess.OwnersMeaning actual.artifact actual.order
    checked.actual.root [basis] axes actual.required
  idealAccess : Qleisli.ControlAccess.OwnersMeaning ideal.artifact ideal.order
    checked.ideal.root [basis] axes ideal.required
  bound : ‖operator (liftLeft (R := R)
    (controlled (portMatrix basis basis actual.required) -
      controlled (portMatrix basis basis ideal.required)))‖ ≤
        (Qleisli.Semantics.Exact.rational epsilon : ℝ)

theorem checked_controlled_reference_bound {R : Type} [Fintype R]
    (basis : QleisliKernel.Semantics.Finite.Basis)
    (actual ideal : QleisliKernel.Qirf.EngineeringPure.LeafRequest)
    (epsilon : QleisliKernel.Semantics.Exact.Coefficient)
    (checked : QleisliKernel.Qirf.EngineeringPure.Checked) (axes : List Nat)
    (work left : Nat)
    (ok : (QleisliKernel.Qirf.EngineeringPure.check
      ⟨basis,basis,actual,ideal,epsilon⟩).run work = (.ok checked,left))
    (actualAccess : Qleisli.ControlAccess.OwnersMeaning actual.artifact actual.order
      checked.actual.root [basis] axes actual.required)
    (idealAccess : Qleisli.ControlAccess.OwnersMeaning ideal.artifact ideal.order
      checked.ideal.root [basis] axes ideal.required) :
    ControlledOriginalBound (R := R) basis actual ideal epsilon checked axes := by
  let request : QleisliKernel.Qirf.EngineeringPure.Request := ⟨basis,basis,actual,ideal,epsilon⟩
  have meaning : Qleisli.NativeEngineeringPure.Meaning request checked :=
    Qleisli.NativeEngineeringPure.check_meaning request checked work left ok
  refine ⟨actualAccess,idealAccess,?_⟩
  exact controlled_reference_bound (R := R) (portMatrix basis basis actual.required)
    (portMatrix basis basis ideal.required) (Qleisli.Semantics.Exact.rational epsilon : ℝ)
    meaning.bound.2.2.1 (meaning_bound request checked meaning)

end Qleisli.EngineeringPureComposition
