import Qleisli.Semantics.EngineeringInstrument
import Qleisli.EngineeringPure
import QleisliKernel.Engineering.Instrument
import Qleisli.RawInstrumentEquality
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! Refinement of finite coefficient majorants to independent all-reference
instrument adjoint bounds. This engineering inequality supplies no exact
semantic equality, effect relabeling, cleanup certificate or constitutional
guarantee admission.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.EngineeringInstrument
open Qleisli.Semantics.EngineeringInstrument
open scoped BigOperators

@[simp] theorem projection_apply {I R : Type} [Fintype I] [Fintype R]
    (i : I) (v : Joint I R) (r : R) : projection i v r = v (i,r) := rfl

@[simp] theorem inclusion_apply {I R : Type} [Fintype I] [Fintype R]
    [DecidableEq I]
    (i : I) (v : EuclideanSpace ℂ R) (p : I × R) :
    inclusion i v p = if p.1 = i then v p.2 else 0 := by
  classical
  simp only [inclusion,LinearMap.coe_toContinuousLinearMap',LinearMap.coe_mk,
    AddHom.coe_mk,PiLp.toLp_apply]

theorem projection_norm_le {I R : Type} [Fintype I] [Fintype R] (i : I) :
    ‖(projection i : Joint I R →L[ℂ] EuclideanSpace ℂ R)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simp only [one_mul]
  apply le_of_sq_le_sq _ (norm_nonneg _)
  simp only [EuclideanSpace.norm_sq_eq,projection_apply,Fintype.sum_prod_type]
  exact Finset.single_le_sum (fun j _ => Finset.sum_nonneg fun r _ => sq_nonneg ‖v (j,r)‖)
    (Finset.mem_univ i)

theorem inclusion_norm_map {I R : Type} [Fintype I] [Fintype R]
    (i : I) (v : EuclideanSpace ℂ R) : ‖inclusion i v‖ = ‖v‖ := by
  classical
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq,inclusion_apply,Fintype.sum_prod_type]
  calc
    _ = ∑ j : I, if j = i then ∑ r : R, ‖v r‖ ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : j = i <;> simp [h]
    _ = _ := by simp

theorem inclusion_norm_le {I R : Type} [Fintype I] [Fintype R] (i : I) :
    ‖(inclusion i : EuclideanSpace ℂ R →L[ℂ] Joint I R)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simp only [one_mul,inclusion_norm_map]
  exact le_rfl

@[simp] theorem inclusion_adjoint {I R : Type} [Fintype I] [Fintype R] (i : I) :
    (inclusion i : EuclideanSpace ℂ R →L[ℂ] Joint I R).adjoint = projection i := by
  classical
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro v w
  simp [PiLp.inner_apply,Fintype.sum_prod_type,projection_apply,inclusion_apply]

@[simp] theorem projection_adjoint {I R : Type} [Fintype I] [Fintype R] (i : I) :
    (projection i : Joint I R →L[ℂ] EuclideanSpace ℂ R).adjoint = inclusion i := by
  rw [← inclusion_adjoint i,ContinuousLinearMap.adjoint_adjoint]

/-- The system matrix acts on each reference fiber with its original complex
entries and axis order. The joint vector need not be a product vector. -/
theorem liftLeft_apply {I O R : Type} [Fintype I] [Fintype O] [Fintype R]
    (operator : Matrix O I ℂ) (joint : Joint I R) (o : O) (r : R) :
    liftLeft operator R joint (o,r) = ∑ i, operator o i * joint (i,r) := by
  classical
  change EuclideanSpace.proj (o,r) (liftLeft operator R joint) = _
  simp [liftLeft,projection,inclusion,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply,map_sum,map_smul]

noncomputable def sandwich {I O R : Type} [Fintype I] [Fintype O] [Fintype R]
    (observable : Joint O R →L[ℂ] Joint O R) (o : O) (i : I) (p : O) (j : I) :
    Joint I R →L[ℂ] Joint I R :=
  inclusion i ∘L projection o ∘L observable ∘L inclusion p ∘L projection j

theorem sandwich_norm_le {I O R : Type} [Fintype I] [Fintype O] [Fintype R]
    (observable : Joint O R →L[ℂ] Joint O R) (o : O) (i : I) (p : O) (j : I) :
    ‖sandwich observable o i p j‖ ≤ ‖observable‖ := by
  unfold sandwich
  calc
    _ ≤ ‖(inclusion i : EuclideanSpace ℂ R →L[ℂ] Joint I R)‖ *
        (‖(projection o : Joint O R →L[ℂ] EuclideanSpace ℂ R)‖ *
        (‖observable‖ * (‖(inclusion p : EuclideanSpace ℂ R →L[ℂ] Joint O R)‖ *
        ‖(projection j : Joint I R →L[ℂ] EuclideanSpace ℂ R)‖))) := by
      grw [ContinuousLinearMap.opNorm_comp_le,ContinuousLinearMap.opNorm_comp_le,
        ContinuousLinearMap.opNorm_comp_le,ContinuousLinearMap.opNorm_comp_le]
    _ ≤ 1 * (1 * (‖observable‖ * (1 * 1))) := by
      gcongr
      · exact inclusion_norm_le i
      · exact projection_norm_le o
      · exact inclusion_norm_le p
      · exact projection_norm_le j
    _ = _ := by ring

/-- Conjugation uses the conjugate of the forward Choi coefficient. Keeping
this conjugation explicit avoids a hidden transpose or a probability quotient. -/
theorem conjugation_coefficients {I O R : Type} [Fintype I] [Fintype O] [Fintype R]
    (operator : Matrix O I ℂ) (observable : Joint O R →L[ℂ] Joint O R) :
    (liftLeft operator R).adjoint ∘L observable ∘L liftLeft operator R =
      ∑ o, ∑ i, ∑ p, ∑ j,
        star (operator o i * star (operator p j)) • sandwich observable o i p j := by
  simp only [liftLeft,map_sum,map_smulₛₗ,ContinuousLinearMap.adjoint_comp,
    inclusion_adjoint,projection_adjoint,
    ContinuousLinearMap.comp_finsetSum,ContinuousLinearMap.finsetSum_comp,
    ContinuousLinearMap.smul_comp,ContinuousLinearMap.comp_smul,Finset.smul_sum,smul_smul,
    sandwich,ContinuousLinearMap.comp_assoc,starRingEnd_apply]
  calc
    _ = ∑ a : O × I, ∑ b : O × I,
        (operator a.1 a.2 * star (operator b.1 b.2)) •
          (inclusion b.2 ∘L projection b.1 ∘L observable ∘L inclusion a.1 ∘L projection a.2) := by
      simp only [Fintype.sum_prod_type]
    _ = ∑ b : O × I, ∑ a : O × I,
        (operator a.1 a.2 * star (operator b.1 b.2)) •
          (inclusion b.2 ∘L projection b.1 ∘L observable ∘L inclusion a.1 ∘L projection a.2) :=
      Finset.sum_comm
    _ = _ := by simp only [Fintype.sum_prod_type,star_mul,star_star]

theorem adjoint_coefficients {X Y H I O R : Type}
    [Fintype Y] [Fintype H] [Fintype I] [Fintype O] [Fintype R]
    (operators : Kraus X Y H I O) (observables : Observable Y O R) (input : X) :
    adjointWithReference operators observables input =
      ∑ y, ∑ o, ∑ i, ∑ p, ∑ j,
        star (choi operators input y (o,i) (p,j)) • sandwich (observables y) o i p j := by
  simp only [adjointWithReference,conjugation_coefficients,choi,
    Qleisli.Semantics.InstrumentEquality.choi,star_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro o _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact (Finset.sum_smul (R := ℂ) (M := Joint I R →L[ℂ] Joint I R)
    (s := Finset.univ) (f := fun h => star (operators input y h o i *
      star (operators input y h p j))) (x := sandwich (observables y) o i p j)).symm

theorem adjoint_difference_coefficients {X Y H K I O R : Type}
    [Fintype Y] [Fintype H] [Fintype K] [Fintype I] [Fintype O] [Fintype R]
    (actual : Kraus X Y H I O) (ideal : Kraus X Y K I O)
    (observables : Observable Y O R) (input : X) :
    adjointWithReference actual observables input - adjointWithReference ideal observables input =
      ∑ y, ∑ o, ∑ i, ∑ p, ∑ j,
        star (choi actual input y (o,i) (p,j) - choi ideal input y (o,i) (p,j)) •
          sandwich (observables y) o i p j := by
  rw [adjoint_coefficients,adjoint_coefficients]
  simp only [star_sub]
  simp_rw [sub_smul (R := ℂ) (M := Joint I R →L[ℂ] Joint I R)]
  simp only [Finset.sum_sub_distrib]

/-- Full complex Choi majorants imply an all-reference adjoint bound. The
hidden-history counts may differ and no positivity or normalization premise
on the input observable is required. -/
theorem completeAdjointBound_of_majorants {X Y H K I O : Type}
    [Fintype Y] [Fintype H] [Fintype K] [Fintype I] [Fintype O]
    (actual : Kraus X Y H I O) (ideal : Kraus X Y K I O) (epsilon : ℝ)
    (majorant : X → Y → O → I → O → I → ℝ)
    (epsilon_nonnegative : 0 ≤ epsilon)
    (majorant_nonnegative : ∀ x y o i p j, 0 ≤ majorant x y o i p j)
    (coefficient_bound : ∀ x y o i p j,
      ‖choi actual x y (o,i) (p,j) - choi ideal x y (o,i) (p,j)‖ ≤ majorant x y o i p j)
    (sum_bound : ∀ x, (∑ y, ∑ o, ∑ i, ∑ p, ∑ j, majorant x y o i p j) ≤ epsilon) :
    CompleteAdjointBound actual ideal epsilon := by
  refine ⟨epsilon_nonnegative,?_⟩
  intro R _ observables input
  rw [adjoint_difference_coefficients]
  calc
    _ ≤ ∑ y, ∑ o, ∑ i, ∑ p, ∑ j,
        majorant input y o i p j * ‖observables‖ := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun o _ => ?_)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [norm_smul,norm_star]
      exact mul_le_mul (coefficient_bound input y o i p j)
        ((sandwich_norm_le _ o i p j).trans (norm_le_pi_norm observables y))
        (norm_nonneg _) (majorant_nonnegative input y o i p j)
    _ = (∑ y, ∑ o, ∑ i, ∑ p, ∑ j, majorant input y o i p j) * ‖observables‖ := by
      simp only [Finset.sum_mul]
    _ ≤ epsilon * ‖observables‖ := mul_le_mul_of_nonneg_right (sum_bound input) (norm_nonneg _)

/-- A checked one-cell Frobenius inequality is the unsquared complex norm
inequality used by the instrument metric. -/
theorem scalarBound (actual ideal : QleisliKernel.Semantics.Exact.Scalar)
    (majorant : QleisliKernel.Semantics.Exact.Coefficient)
    (checked : QleisliKernel.Engineering.Pure.Checked) (work left : Nat)
    (ok : (QleisliKernel.Engineering.Pure.checkMatrices ⟨1,1,[actual]⟩ ⟨1,1,[ideal]⟩
      majorant).run work = (.ok checked,left)) :
    0 ≤ (Qleisli.Semantics.Exact.rational majorant : ℝ) ∧
      ‖Qleisli.Semantics.Exact.scalar actual - Qleisli.Semantics.Exact.scalar ideal‖ ≤
        (Qleisli.Semantics.Exact.rational majorant : ℝ) := by
  have facts := Qleisli.EngineeringPure.checkMatrices_squaredDistance _ _ _ _ _ _ ok
  refine ⟨facts.2.2.1,?_⟩
  apply le_of_sq_le_sq _ facts.2.2.1
  simpa [Qleisli.Semantics.EngineeringPure.squaredDistance,
    Qleisli.Semantics.EngineeringPure.gapMatrix,Qleisli.Semantics.Exact.entry,
    QleisliKernel.Semantics.Exact.Matrix.entry,Complex.normSq_eq_norm_sq] using facts.2.2.2

theorem checkCell_bound (actual ideal : List QleisliKernel.Raw.InstrumentEquality.History)
    (cell : QleisliKernel.Engineering.Instrument.Cell)
    (majorant : QleisliKernel.Semantics.Exact.Coefficient) (work left : Nat)
    (ok : (QleisliKernel.Engineering.Instrument.checkCell actual ideal cell majorant).run work =
      (.ok (),left)) :
    0 ≤ (Qleisli.Semantics.Exact.rational majorant : ℝ) ∧
      ‖Qleisli.Raw.InstrumentEquality.meaning actual cell.outcome cell.row cell.col
          cell.otherRow cell.otherCol -
        Qleisli.Raw.InstrumentEquality.meaning ideal cell.outcome cell.row cell.col
          cell.otherRow cell.otherCol‖ ≤ (Qleisli.Semantics.Exact.rational majorant : ℝ) := by
  obtain ⟨accepted⟩ := QleisliKernel.Engineering.Instrument.checkCell_acceptance _ _ _ _ _ _ ok
  have bounded := scalarBound _ _ _ _ _ _ accepted.bounded
  rw [Qleisli.Raw.InstrumentEquality.coefficient_meaning _ _ _ _ _ _ _ _ _ accepted.actualComputed,
    Qleisli.Raw.InstrumentEquality.coefficient_meaning _ _ _ _ _ _ _ _ _ accepted.expectedComputed]
    at bounded
  exact bounded

private theorem sumMajorants_fold_meaning
    (majorants : List QleisliKernel.Semantics.Exact.Coefficient)
    (initial total : QleisliKernel.Semantics.Exact.Coefficient) (work left : Nat)
    (ok : (majorants.foldlM (fun acc q => do
      QleisliKernel.Finite.exactWork (QleisliKernel.Exact.charge 8)
      QleisliKernel.Finite.lift (QleisliKernel.Finite.arithmetic
        (QleisliKernel.Exact.Coefficient.add acc q))) initial).run work = (.ok total,left)) :
    (Qleisli.Semantics.Exact.rational total : ℝ) =
      (Qleisli.Semantics.Exact.rational initial : ℝ) +
        (majorants.map fun q => (Qleisli.Semantics.Exact.rational q : ℝ)).sum := by
  induction majorants generalizing initial work left with
  | nil =>
    have same := (QleisliKernel.Finite.pure_success _ _ _ _ ok).1
    simp [← same]
  | cons q rest ih =>
    simp only [List.foldlM_cons] at ok
    obtain ⟨next,middle,hn,ht⟩ := QleisliKernel.Finite.bind_success _ _ _ _ _ ok
    obtain ⟨_,after,_,hn⟩ := QleisliKernel.Finite.bind_success _ _ _ _ _ hn
    have add := Qleisli.Exact.coefficient_add_preserves _ _ _
      (QleisliKernel.Finite.arithmetic_success _ _
        (QleisliKernel.Finite.lift_success _ _ _ _ hn).1)
    have addReal : (Qleisli.Semantics.Exact.rational next : ℝ) =
        (Qleisli.Semantics.Exact.rational initial : ℝ) +
          (Qleisli.Semantics.Exact.rational q : ℝ) := by exact_mod_cast add
    rw [ih next middle left ht,addReal]
    simp [add_assoc]

theorem sumMajorants_meaning
    (majorants : List QleisliKernel.Semantics.Exact.Coefficient)
    (total : QleisliKernel.Semantics.Exact.Coefficient) (work left : Nat)
    (ok : (QleisliKernel.Engineering.Instrument.sumMajorants majorants).run work =
      (.ok total,left)) :
    (Qleisli.Semantics.Exact.rational total : ℝ) =
      (majorants.map fun q => (Qleisli.Semantics.Exact.rational q : ℝ)).sum := by
  have value := sumMajorants_fold_meaning majorants (.integer 0) total work left ok
  simpa [Qleisli.Semantics.Exact.rational,QleisliKernel.Semantics.Exact.Coefficient.integer]
    using value

noncomputable def historyOperators (rows cols results : Nat)
    (histories : List QleisliKernel.Raw.InstrumentEquality.History) :
    Kraus Unit (Fin results → Bool) (Fin histories.length) (Fin cols) (Fin rows) :=
  fun _ outcome => Qleisli.Raw.InstrumentEquality.operators histories (List.ofFn outcome) rows cols

theorem historyOperators_choi (rows cols results : Nat)
    (histories : List QleisliKernel.Raw.InstrumentEquality.History)
    (outcome : Fin results → Bool) (row otherRow : Fin rows) (col otherCol : Fin cols) :
    choi (historyOperators rows cols results histories) () outcome (row,col) (otherRow,otherCol) =
      Qleisli.Raw.InstrumentEquality.meaning histories (List.ofFn outcome)
        row.val col.val otherRow.val otherCol.val :=
  Qleisli.Raw.InstrumentEquality.choi_meaning histories (List.ofFn outcome) rows cols
    row otherRow col otherCol

private theorem meaning_zero_of_absent
    (histories : List QleisliKernel.Raw.InstrumentEquality.History) (outcome : List Bool)
    (row col otherRow otherCol : Nat) (absent : outcome ∉ histories.map (·.outcome)) :
    Qleisli.Raw.InstrumentEquality.meaning histories outcome row col otherRow otherCol = 0 := by
  induction histories with
  | nil => simp [Qleisli.Raw.InstrumentEquality.meaning]
  | cons history rest ih =>
    have distinct : history.outcome ≠ outcome := by
      intro same
      exact absent (by simp [same])
    have remaining : outcome ∉ rest.map (·.outcome) := by
      intro member
      exact absent (by simp [member])
    simpa [Qleisli.Raw.InstrumentEquality.meaning,Qleisli.Raw.InstrumentEquality.contribution,
      distinct] using ih remaining

private theorem sum_zip_bound {A B : Type} (xs : List A) (ys : List B)
    (f : A → ℝ) (g : B → ℝ) (length : xs.length = ys.length)
    (bound : ∀ a b, (a,b) ∈ xs.zip ys → f a ≤ g b) :
    (xs.map f).sum ≤ (ys.map g).sum := by
  induction xs generalizing ys with
  | nil =>
    have same : ys = [] := List.length_eq_zero_iff.mp (by simpa using length.symm)
    simp [same]
  | cons a rest ih =>
    cases ys with
    | nil => simp at length
    | cons b tail =>
      have head := bound a b (by simp)
      have restBound : ∀ a b, (a,b) ∈ rest.zip tail → f a ≤ g b := by
        intro a b member
        exact bound a b (by simp [member])
      have tail := ih tail (by simpa using length) restBound
      simpa using add_le_add head tail

private theorem range_sum (n : Nat) (f : Nat → ℝ) :
    ((List.range n).map f).sum = ∑ k : Fin n, f k := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.range_succ,List.map_append,List.sum_append,List.map_singleton,List.sum_singleton]
    rw [Fin.sum_univ_castSucc]
    simpa only [Fin.val_castSucc,Fin.val_last] using congrArg (fun z => z + f n) ih

private theorem product_sum {A B : Type} (xs : List A) (ys : List B) (f : A × B → ℝ) :
    ((xs.product ys).map f).sum =
      (xs.map fun x => (ys.map fun y => f (x,y)).sum).sum := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simpa only [List.product,List.flatMap_cons,List.map_append,List.sum_append,List.map_map,
      List.map_cons,List.sum_cons] using
      congrArg (fun z => (ys.map fun y => f (x,y)).sum + z) ih

theorem cells_sum (rows cols : Nat) (labels : List (List Bool))
    (f : QleisliKernel.Engineering.Instrument.Cell → ℝ) :
    ((QleisliKernel.Engineering.Instrument.cells rows cols labels).map f).sum =
      (labels.map fun label => ∑ row : Fin rows, ∑ col : Fin cols,
        ∑ otherRow : Fin rows, ∑ otherCol : Fin cols,
          f ⟨label,row,col,otherRow,otherCol⟩).sum := by
  unfold QleisliKernel.Engineering.Instrument.cells
  simp only [List.map_map]
  change ((((labels.product ((List.range rows).product (List.range cols))).product
    ((List.range rows).product (List.range cols))).map fun pair =>
      f ⟨pair.1.1,pair.1.2.1,pair.1.2.2,pair.2.1,pair.2.2⟩).sum) = _
  let indices := (List.range rows).product (List.range cols)
  rw [product_sum (labels.product indices) indices
    (fun pair => f ⟨pair.1.1,pair.1.2.1,pair.1.2.2,pair.2.1,pair.2.2⟩)]
  rw [product_sum labels indices (fun pair =>
    (indices.map fun other => f ⟨pair.1,pair.2.1,pair.2.2,other.1,other.2⟩).sum)]
  apply congrArg List.sum
  apply List.map_congr_left
  intro label _
  dsimp only [indices]
  rw [product_sum (List.range rows) (List.range cols) (fun pair =>
    (((List.range rows).product (List.range cols)).map fun other =>
      f ⟨label,pair.1,pair.2,other.1,other.2⟩).sum)]
  rw [range_sum rows]
  apply Finset.sum_congr rfl
  intro row _
  rw [range_sum cols]
  apply Finset.sum_congr rfl
  intro col _
  rw [product_sum (List.range rows) (List.range cols)
    (fun pair => f ⟨label,row,col,pair.1,pair.2⟩)]
  rw [range_sum rows]
  apply Finset.sum_congr rfl
  intro otherRow _
  rw [range_sum cols]

private theorem sum_toFinset_le_list (labels : List (List Bool))
    (f : List Bool → ℝ) (nonnegative : ∀ l, 0 ≤ f l) :
    labels.toFinset.sum f ≤ (labels.map f).sum := by
  classical
  induction labels with
  | nil => simp
  | cons label rest ih =>
    by_cases member : label ∈ rest
    · simpa [member] using ih.trans (le_add_of_nonneg_left (nonnegative label))
    · simpa [member] using add_le_add_left ih (f label)

/-- An injective public-label map retains all outcomes. Outside the original
support, the full coefficient is zero; no normalized selected branch replaces
the complete instrument. -/
theorem sum_labels_le {Y : Type} [Fintype Y]
    (labels : List (List Bool))
    (label : Y → List Bool) (injective : Function.Injective label) (f : List Bool → ℝ)
    (nonnegative : ∀ l, 0 ≤ f l) (absent : ∀ y, label y ∉ labels → f (label y) = 0) :
    (∑ y, f (label y)) ≤ (labels.map f).sum := by
  classical
  let supported := Finset.univ.filter (fun y => label y ∈ labels)
  have zeros : ∀ y ∈ Finset.univ, y ∉ supported → f (label y) = 0 := by
    intro y _ outside
    exact absent y (by simpa [supported] using outside)
  have restricted : supported.sum (fun y => f (label y)) = ∑ y, f (label y) :=
    Finset.sum_subset (Finset.filter_subset _ _) zeros
  have image_subset : supported.image label ⊆ labels.toFinset := by
    intro l member
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp member
    simpa [supported] using hy
  calc
    _ = supported.sum (fun y => f (label y)) := restricted.symm
    _ = (supported.image label).sum f := by
      rw [Finset.sum_image]
      exact fun _ _ _ _ same => injective same
    _ ≤ labels.toFinset.sum f :=
      Finset.sum_le_sum_of_subset_of_nonneg image_subset (fun l _ _ => nonnegative l)
    _ ≤ _ := sum_toFinset_le_list labels f nonnegative

theorem checkHistories_majorant_sum (rows cols results : Nat)
    (actual ideal : List QleisliKernel.Raw.InstrumentEquality.History)
    (epsilon : QleisliKernel.Semantics.Exact.Coefficient)
    (majorants : List QleisliKernel.Semantics.Exact.Coefficient)
    (checked : QleisliKernel.Engineering.Instrument.Checked) (work left : Nat)
    (ok : (QleisliKernel.Engineering.Instrument.checkHistories rows cols results actual ideal
      epsilon majorants).run work = (.ok checked,left)) :
    (majorants.map fun q => (Qleisli.Semantics.Exact.rational q : ℝ)).sum ≤
      (Qleisli.Semantics.Exact.rational epsilon : ℝ) := by
  have facts := QleisliKernel.Engineering.Instrument.checkHistories_conditions _ _ _ _ _ _ _ _ _ _ ok
  obtain ⟨before,after,hs⟩ := facts.summed
  have sum := sumMajorants_meaning _ _ _ _ hs
  obtain ⟨negative,margin,hn,hm,hpos⟩ := facts.margin
  have marginValue : Qleisli.Semantics.Exact.rational margin =
      Qleisli.Semantics.Exact.rational epsilon - Qleisli.Semantics.Exact.rational checked.total := by
    rw [Qleisli.Exact.coefficient_add_preserves _ _ _ hm,
      Qleisli.Exact.coefficient_neg_preserves _ _ hn]
    ring
  have marginReal : (Qleisli.Semantics.Exact.rational margin : ℝ) =
      (Qleisli.Semantics.Exact.rational epsilon : ℝ) -
        (Qleisli.Semantics.Exact.rational checked.total : ℝ) := by exact_mod_cast marginValue
  have nonnegative := (Qleisli.EngineeringPure.dyadic_nonneg margin).mpr hpos
  rw [marginReal,sum] at nonnegative
  linarith

/-- The actual bounded history checker establishes the complete all-reference
instrument bound with the original public Boolean result type. Every absent
public label remains quantified and has its independently specified zero map. -/
theorem checkHistories_bound (rows cols results : Nat)
    (actual ideal : List QleisliKernel.Raw.InstrumentEquality.History)
    (epsilon : QleisliKernel.Semantics.Exact.Coefficient)
    (majorants : List QleisliKernel.Semantics.Exact.Coefficient)
    (checked : QleisliKernel.Engineering.Instrument.Checked) (work left : Nat)
    (ok : (QleisliKernel.Engineering.Instrument.checkHistories rows cols results actual ideal
      epsilon majorants).run work = (.ok checked,left)) :
    CompleteAdjointBound (historyOperators rows cols results actual)
      (historyOperators rows cols results ideal) (Qleisli.Semantics.Exact.rational epsilon : ℝ) := by
  classical
  have facts := QleisliKernel.Engineering.Instrument.checkHistories_conditions _ _ _ _ _ _ _ _ _ _ ok
  let gap : QleisliKernel.Engineering.Instrument.Cell → ℝ := fun cell =>
    ‖Qleisli.Raw.InstrumentEquality.meaning actual cell.outcome cell.row cell.col
        cell.otherRow cell.otherCol -
      Qleisli.Raw.InstrumentEquality.meaning ideal cell.outcome cell.row cell.col
        cell.otherRow cell.otherCol‖
  let byLabel : List Bool → ℝ := fun label =>
    ∑ row : Fin rows, ∑ col : Fin cols, ∑ otherRow : Fin rows, ∑ otherCol : Fin cols,
      gap ⟨label,row,col,otherRow,otherCol⟩
  have label_nonnegative (label : List Bool) : 0 ≤ byLabel label := by
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have gap_sum : ((QleisliKernel.Engineering.Instrument.cells rows cols checked.outcomes).map gap).sum ≤
      (majorants.map fun q => (Qleisli.Semantics.Exact.rational q : ℝ)).sum := by
    apply sum_zip_bound _ _ gap _ facts.length.symm
    intro cell q member
    obtain ⟨before,after,h⟩ := facts.bounded
    obtain ⟨start,finish,hcell⟩ := Qleisli.Raw.InstrumentEquality.forM_member _ _ _ _ h (cell,q) member
    exact (checkCell_bound actual ideal cell q start finish hcell).2
  have absent (outcome : Fin results → Bool) (outside : List.ofFn outcome ∉ checked.outcomes) :
      byLabel (List.ofFn outcome) = 0 := by
    rw [facts.labels] at outside
    have absentActual : List.ofFn outcome ∉ actual.map (·.outcome) := by
      intro member
      exact outside (by simp [QleisliKernel.Engineering.Instrument.outcomes,List.map_append,member])
    have absentIdeal : List.ofFn outcome ∉ ideal.map (·.outcome) := by
      intro member
      exact outside (by simp [QleisliKernel.Engineering.Instrument.outcomes,List.map_append,member])
    dsimp [byLabel,gap]
    simp_rw [meaning_zero_of_absent actual (List.ofFn outcome) _ _ _ _ absentActual,
      meaning_zero_of_absent ideal (List.ofFn outcome) _ _ _ _ absentIdeal]
    simp
  apply completeAdjointBound_of_majorants _ _ _
    (fun x y o i p j => ‖choi (historyOperators rows cols results actual) x y (o,i) (p,j) -
      choi (historyOperators rows cols results ideal) x y (o,i) (p,j)‖)
    ((Qleisli.EngineeringPure.dyadic_nonneg epsilon).mpr facts.epsilonNonnegative)
    (fun _ _ _ _ _ _ => norm_nonneg _) (fun _ _ _ _ _ _ => le_rfl)
  intro input
  cases input
  simp only [historyOperators_choi]
  change (∑ y, byLabel (List.ofFn y)) ≤ (Qleisli.Semantics.Exact.rational epsilon : ℝ)
  calc
    _ ≤ (checked.outcomes.map byLabel).sum := sum_labels_le checked.outcomes
      List.ofFn List.ofFn_injective byLabel label_nonnegative absent
    _ = ((QleisliKernel.Engineering.Instrument.cells rows cols checked.outcomes).map gap).sum :=
      (cells_sum rows cols checked.outcomes gap).symm
    _ ≤ (majorants.map fun q => (Qleisli.Semantics.Exact.rational q : ℝ)).sum := gap_sum
    _ ≤ _ := checkHistories_majorant_sum _ _ _ _ _ _ _ _ _ _ ok

end Qleisli.EngineeringInstrument
