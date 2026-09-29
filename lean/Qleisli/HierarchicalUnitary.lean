import Qleisli.HierarchicalEvaluation

/-! Whole-space unitary laws for the hierarchy's actual complex operators.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
These are mathematical matrix laws, never a matrix-based runtime checker.
The connection to accepted full-profile derivations is a separate theorem. -/

namespace Qleisli.HierarchicalUnitary
open QleisliKernel.Hierarchical
open Artifact HierarchicalSemantics HierarchicalOperators
open scoped BigOperators Matrix

/-- Complete fixed-width interface and the first inverse law. For the finite
square basis, `unitary_laws` derives the second law without an extra premise. -/
def UnitaryAt (n : Nat) (operator : Operator) : Prop :=
  operator.inputWidth = n ∧ operator.outputWidth = n ∧
    (matrixAt n n operator)ᴴ * matrixAt n n operator = 1

theorem unitary_laws {n : Nat} {operator : Operator} (h : UnitaryAt n operator) :
    (matrixAt n n operator)ᴴ * matrixAt n n operator = 1 ∧
      matrixAt n n operator * (matrixAt n n operator)ᴴ = 1 :=
  ⟨h.2.2,mul_eq_one_comm.mp h.2.2⟩

theorem identity_unitary (n : Nat) : UnitaryAt n (identity n) := by
  refine ⟨rfl,rfl,?_⟩
  simp [matrix_identity]

theorem compose_unitary {n : Nat} {before after : Operator}
    (hb : UnitaryAt n before) (ha : UnitaryAt n after) :
    UnitaryAt n (compose after before) := by
  refine ⟨hb.1,ha.2.1,?_⟩
  have matrix := matrix_compose after before
  rw [hb.1,ha.1,ha.2.1] at matrix
  rw [matrix,Matrix.conjTranspose_mul]
  calc
    _ = (matrixAt n n before)ᴴ *
        ((matrixAt n n after)ᴴ * matrixAt n n after) * matrixAt n n before := by
      simp only [Matrix.mul_assoc]
    _ = 1 := by rw [ha.2.2,Matrix.mul_one,hb.2.2]

theorem power_output (child : Operator) (count : Nat)
    (same : child.outputWidth = child.inputWidth) :
    (power child count).outputWidth = child.inputWidth := by
  cases count with
  | zero => rfl
  | succ count => exact same

theorem power_unitary {n : Nat} {child : Operator}
    (h : UnitaryAt n child) (count : Nat) : UnitaryAt n (power child count) := by
  induction count with
  | zero => simpa only [power,h.1] using identity_unitary n
  | succ count ih => exact compose_unitary ih h

theorem sequence_unitary {n : Nat} (children : List Operator)
    (ready : ∀ child ∈ children, UnitaryAt n child) :
    UnitaryAt n (sequence n children) := by
  have fold : ∀ start, UnitaryAt n start →
      UnitaryAt n (children.foldl (fun current next => compose next current) start) := by
    induction children with
    | nil => intro start h; exact h
    | cons child rest ih =>
      intro start h
      apply ih (fun x hx => ready x (by simp [hx]))
      exact compose_unitary h (ready child (by simp))
  exact fold (identity n) (identity_unitary n)

theorem matrix_bounded (n : Nat) (f : Bits → Bits → ℂ) :
    matrixAt n n (bounded n n f) = fun output input => f (List.ofFn output) (List.ofFn input) := by
  ext output input
  simp [matrixAt,bounded]

theorem matrix_inverse (interface : Interface) (child : Operator) (n : Nat)
    (hi : width interface.inputs = n) (ho : width interface.outputs = n) :
    matrixAt n n (apply interface .inverse [child]) = (matrixAt n n child)ᴴ := by
  ext output input
  simp [matrixAt,apply,bounded,raw,hi,ho,Matrix.conjTranspose_apply]

theorem inverse_unitary (interface : Interface) {n : Nat} {child : Operator}
    (hi : width interface.inputs = n) (ho : width interface.outputs = n)
    (h : UnitaryAt n child) : UnitaryAt n (apply interface .inverse [child]) := by
  refine ⟨hi,ho,?_⟩
  rw [matrix_inverse interface child n hi ho,Matrix.conjTranspose_conjTranspose]
  exact (unitary_laws h).2

variable {I : Type} [Fintype I] [DecidableEq I]

/-- A basis permutation carries scalar +1; no phases are forgotten. -/
noncomputable def permutation (route : I ≃ I) : Matrix I I ℂ :=
  fun output input => if output = route input then 1 else 0

theorem permutation_isometry (route : I ≃ I) :
    (permutation route)ᴴ * permutation route = 1 := by
  ext a b
  simp [permutation,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.one_apply,eq_comm]

theorem diagonal_isometry (values : I → ℂ)
    (normalized : ∀ i, star (values i) * values i = 1) :
    (Matrix.diagonal values)ᴴ * Matrix.diagonal values = 1 := by
  rw [Matrix.diagonal_conjTranspose,Matrix.diagonal_mul_diagonal]
  have same : (fun i => star (values i) * values i) = fun _ => (1 : ℂ) :=
    funext normalized
  simp only [Pi.star_apply,same,Matrix.diagonal_one]

theorem phase_unit_norm (j k : Nat) : star (phase j k) * phase j k = 1 := by
  unfold phase
  rw [Complex.star_def,← Complex.exp_conj,← Complex.exp_add]
  have zero : starRingEnd ℂ (2 * Real.pi * Complex.I * (j : ℂ) / (2 : ℂ)^k) +
      (2 * Real.pi * Complex.I * (j : ℂ) / (2 : ℂ)^k) = 0 := by
    simp [map_ofNat,neg_div]
  rw [zero,Complex.exp_zero]

theorem phase_unitary (interface : Interface) (n owner j k : Nat)
    (hi : width interface.inputs = n) (ho : width interface.outputs = n) :
    UnitaryAt n (apply interface (.phase owner j k) []) := by
  refine ⟨hi,ho,?_⟩
  have matrix : matrixAt n n (apply interface (.phase owner j k) []) =
      Matrix.diagonal (fun input : Fin n → Bool =>
        if (List.ofFn input)[ownerAxis interface owner]?.getD false then phase j k else 1) := by
    ext output input
    simp [matrixAt,apply,bounded,raw,hi,ho,Matrix.diagonal_apply,List.ofFn_inj]
    split <;> simp_all
  rw [matrix]
  apply diagonal_isometry
  intro input
  split
  · exact phase_unit_norm j k
  · simp

theorem apply_identity_unitary (interface : Interface) (n : Nat)
    (hi : width interface.inputs = n) (ho : width interface.outputs = n) :
    UnitaryAt n (apply interface .identity []) := by
  simpa only [apply,raw,hi,ho] using identity_unitary n

theorem apply_sequence_unitary (interface : Interface) (n : Nat) (children : List Operator)
    (hi : width interface.inputs = n) (ho : width interface.outputs = n)
    (ready : ∀ child ∈ children, UnitaryAt n child) :
    UnitaryAt n (apply interface .sequence children) := by
  refine ⟨hi,ho,?_⟩
  have same : matrixAt n n (apply interface .sequence children) =
      matrixAt n n (sequence n children) := by
    ext output input
    simp [matrixAt,apply,bounded,raw,hi,ho]
  rw [same]
  exact (sequence_unitary children ready).2.2

theorem apply_power_unitary (interface : Interface) (n count : Nat) (child : Operator)
    (hi : width interface.inputs = n) (ho : width interface.outputs = n)
    (ready : UnitaryAt n child) :
    UnitaryAt n (apply interface (.power count) [child]) := by
  refine ⟨hi,ho,?_⟩
  have same : matrixAt n n (apply interface (.power count) [child]) =
      matrixAt n n (power child count) := by
    ext output input
    simp [matrixAt,apply,bounded,raw,hi,ho]
  rw [same]
  exact (power_unitary ready count).2.2

/-- Changing coordinates uses the same equivalence on both matrix axes. -/
theorem submatrix_isometry {J : Type} [Fintype J] [DecidableEq J]
    (route : J ≃ I) (matrix : Matrix I I ℂ) (h : matrixᴴ * matrix = 1) :
    (matrix.submatrix route route)ᴴ * matrix.submatrix route route = 1 := by
  rw [Matrix.conjTranspose_submatrix,Matrix.submatrix_mul_equiv,h]
  exact Matrix.submatrix_one_equiv route

def axisEquiv {n : Nat} {forward backward : List Nat}
    (h : QleisliKernel.Layout.Permutation n forward backward) :
    (Fin n → Bool) ≃ (Fin n → Bool) where
  toFun := QleisliKernel.Layout.reindex forward h.forwardBound
  invFun := QleisliKernel.Layout.reindex backward h.backwardBound
  left_inv := QleisliKernel.Layout.reindex_reverse_round_trip h
  right_inv := QleisliKernel.Layout.reindex_round_trip h

theorem axisEquiv_list {n : Nat} {forward backward : List Nat}
    (h : QleisliKernel.Layout.Permutation n forward backward) (input : Fin n → Bool) :
    List.ofFn (axisEquiv h input) = forward.map (fun i => (List.ofFn input)[i]?.getD false) := by
  apply List.ext_getElem
  · simp [h.1]
  · intro i left right
    have bound : QleisliKernel.Layout.indexAt forward i < n := h.forwardBound ⟨i,by simpa using left⟩
    have fi : i < forward.length := by simpa using right
    simp only [List.getElem_ofFn,List.getElem_map]
    change input ⟨QleisliKernel.Layout.indexAt forward i,_⟩ = _
    have idx : QleisliKernel.Layout.indexAt forward i = forward[i] := by
      simp [QleisliKernel.Layout.indexAt,List.getElem?_eq_getElem fi]
    rw [idx] at bound
    simp [idx,bound]

theorem rewire_unitary (interface : Interface) (n : Nat) (forward backward : List Nat)
    (hi : width interface.inputs = n) (ho : width interface.outputs = n)
    (h : QleisliKernel.Layout.Permutation n forward backward) :
    UnitaryAt n (apply interface (.rewire forward) []) := by
  refine ⟨hi,ho,?_⟩
  have matrix : matrixAt n n (apply interface (.rewire forward) []) = permutation (axisEquiv h) := by
    ext output input
    simp only [matrixAt,apply,bounded,raw,hi,ho,List.length_ofFn,and_self,ite_true]
    rw [← axisEquiv_list h]
    simp [permutation,List.ofFn_inj]
  rw [matrix]
  exact permutation_isometry _

/-- The low axes form the first register, including when either is empty. -/
def splitEquiv (m n : Nat) : (Fin (m+n) → Bool) ≃ ((Fin m → Bool) × (Fin n → Bool)) where
  toFun bits := (fun i => bits (Fin.castAdd n i), fun i => bits (Fin.natAdd m i))
  invFun pair := Fin.append pair.1 pair.2
  left_inv bits := Fin.append_castAdd_natAdd
  right_inv pair := by ext <;> simp

theorem split_list (m n : Nat) (bits : Fin (m+n) → Bool) :
    List.ofFn bits = List.ofFn (splitEquiv m n bits).1 ++ List.ofFn (splitEquiv m n bits).2 := by
  rw [← List.ofFn_fin_append]
  congr 1
  exact (splitEquiv m n).left_inv bits |>.symm

theorem tensor_unitary (interface : Interface) (m n : Nat) (first second : Operator)
    (hi : width interface.inputs = m+n) (ho : width interface.outputs = m+n)
    (hf : UnitaryAt m first) (hs : UnitaryAt n second) :
    UnitaryAt (m+n) (apply interface .tensor [first,second]) := by
  refine ⟨hi,ho,?_⟩
  have matrix : matrixAt (m+n) (m+n) (apply interface .tensor [first,second]) =
      (Matrix.kronecker (matrixAt m m first) (matrixAt n n second)).submatrix
        (splitEquiv m n) (splitEquiv m n) := by
    ext output input
    simp only [matrixAt,apply,bounded,raw,hi,ho,List.length_ofFn,and_self,ite_true,
      hf.1,hf.2.1]
    rw [split_list m n output,split_list m n input]
    simp [Matrix.submatrix,Matrix.kronecker,Matrix.kroneckerMap,matrixAt]
  rw [matrix]
  apply submatrix_isometry
  change (Matrix.kroneckerMap (· * ·) (matrixAt m m first) (matrixAt n n second))ᴴ *
    Matrix.kroneckerMap (· * ·) (matrixAt m m first) (matrixAt n n second) = 1
  rw [Matrix.conjTranspose_kronecker,← Matrix.mul_kronecker_mul,hf.2.2,hs.2.2]
  exact Matrix.one_kronecker_one

theorem control_unitary (interface : Interface) (n : Nat) (polarity : Bool) (child : Operator)
    (hi : width interface.inputs = n+1) (ho : width interface.outputs = n+1)
    (ready : UnitaryAt n child) :
    UnitaryAt (n+1) (apply interface (.control polarity) [child]) := by
  refine ⟨hi,ho,?_⟩
  let route := (Fin.consEquiv (fun _ : Fin (n+1) => Bool)).symm
  let blocks : Bool → Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
    fun b => if b = polarity then matrixAt n n child else 1
  have matrix : matrixAt (n+1) (n+1) (apply interface (.control polarity) [child]) =
      (ControlledPowers.block blocks).submatrix route route := by
    ext output input
    conv_lhs => rw [← Fin.cons_self_tail output,← Fin.cons_self_tail input]
    simp [matrixAt,apply,bounded,raw,hi,ho,route,blocks,
      ControlledPowers.block,Matrix.submatrix,List.ofFn_inj]
    by_cases same : output 0 = input 0
    · by_cases active : input 0 = polarity
      · simp only [same,active,ite_true,matrixAt]
        rfl
      · simp only [same,active,ite_true,ite_false,Matrix.one_apply]
        rfl
    · simp [same]
  rw [matrix]
  apply submatrix_isometry
  apply ControlledPowers.block_isometry
  intro bit
  dsimp [blocks]
  split
  · exact ready.2.2
  · simp

/-- Tensoring with the identity preserves the complete joint space. No input
separability or reference-state premise is needed. -/
theorem reference_isometry {R : Type} [Fintype R] [DecidableEq R]
    (matrix : Matrix I I ℂ) (h : matrixᴴ * matrix = 1) :
    (Matrix.kronecker matrix (1 : Matrix R R ℂ))ᴴ *
      Matrix.kronecker matrix (1 : Matrix R R ℂ) = 1 := by
  change (Matrix.kroneckerMap (· * ·) matrix (1 : Matrix R R ℂ))ᴴ *
    Matrix.kroneckerMap (· * ·) matrix (1 : Matrix R R ℂ) = 1
  rw [Matrix.conjTranspose_kronecker,← Matrix.mul_kronecker_mul,h]
  simp

theorem reference_unitary {R : Type} [Fintype R] [DecidableEq R]
    {n : Nat} {operator : Operator} (h : UnitaryAt n operator) :
    let joint := Matrix.kronecker (matrixAt n n operator) (1 : Matrix R R ℂ)
    jointᴴ * joint = 1 ∧ joint * jointᴴ = 1 := by
  have first := reference_isometry (R := R) _ h.2.2
  exact ⟨first,mul_eq_one_comm.mp first⟩

end Qleisli.HierarchicalUnitary
