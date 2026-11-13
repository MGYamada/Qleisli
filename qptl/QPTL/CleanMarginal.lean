/-
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
-/
import QPTL.FiniteMatrix
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Exact clean support for finite Kraus families. Choose the clean state as
one vector in the orthonormal scratch basis. The live output can include the
complete classical outcome register. -/
namespace QPTL.FiniteMatrix
open scoped BigOperators

variable {K A O I R : Type*}

/-- The diagonal entry of the scratch marginal for one basis input. The
family already includes the insertion of the fixed clean input. -/
noncomputable def scratchPopulation [Fintype K] [Fintype O]
    (kraus : K → A → O → I → ℂ) (a : A) (i : I) : ℝ :=
  ∑ k, ∑ o, Complex.normSq (kraus k a o i)

/-- The finite Kraus action tensored with identity on the reference. The
reference coordinates are retained on both sides of every density entry. -/
noncomputable def jointOutput [Fintype K] [Fintype I]
    (kraus : K → A → O → I → ℂ) (input : Matrix (I × R) (I × R) ℂ)
    (left right : A × O × R) : ℂ :=
  ∑ k, ∑ i, ∑ j,
    kraus k left.1 left.2.1 i * input (i,left.2.2) (j,right.2.2) * star (kraus k right.1 right.2.1 j)

/-- Exact vanishing of each unwanted marginal population forces every Kraus
coefficient on that scratch row to vanish. This uses positivity before any
sum over histories or output coordinates can conceal a contribution. -/
theorem scratchPopulation_eq_zero_iff [Fintype K] [Fintype O]
    (kraus : K → A → O → I → ℂ) (a : A) (i : I) :
    scratchPopulation kraus a i = 0 ↔ ∀ k o, kraus k a o i = 0 := by
  unfold scratchPopulation
  constructor
  · intro zero k o
    have row := (Finset.sum_eq_zero_iff_of_nonneg
      (fun k _ => Finset.sum_nonneg fun o _ => Complex.normSq_nonneg (kraus k a o i))).mp zero k (Finset.mem_univ _)
    exact Complex.normSq_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg
      (fun o _ => Complex.normSq_nonneg (kraus k a o i))).mp row o (Finset.mem_univ _))
  · intro zero
    simp [zero]

/-- A scratch marginal supported on the designated basis state for every
basis input gives separation for every joint reference density, including
entangled inputs. The retained block is the live Kraus action obtained by
restricting the output coefficients to the designated scratch state. -/
theorem fixedScratch_separates [Fintype K] [Fintype O] [Fintype I] [DecidableEq A]
    (kraus : K → A → O → I → ℂ) (clean : A)
    (marginal : ∀ a ≠ clean, ∀ i, scratchPopulation kraus a i = 0)
    (input : Matrix (I × R) (I × R) ℂ) (a b : A) (o p : O) (r s : R) :
    jointOutput kraus input (a,o,r) (b,p,s) =
      if a = clean ∧ b = clean then jointOutput kraus input (clean,o,r) (clean,p,s) else 0 := by
  by_cases left : a = clean
  · subst a
    by_cases right : b = clean
    · subst b
      simp
    · have zero (k : K) (j : I) := (scratchPopulation_eq_zero_iff kraus b j).mp (marginal b right j) k p
      simp [jointOutput,right,zero]
  · have zero (k : K) (i : I) := (scratchPopulation_eq_zero_iff kraus a i).mp (marginal a left i) k o
    simp [jointOutput,left,zero]

/-- Unit total output population on a basis input makes the exact scratch
support condition a unit population in the designated clean state. -/
theorem scratchPopulation_clean [Fintype K] [Fintype O] [Fintype A] [DecidableEq A]
    (kraus : K → A → O → I → ℂ) (clean : A) (i : I)
    (normalized : (∑ a, scratchPopulation kraus a i) = 1)
    (marginal : ∀ a ≠ clean, scratchPopulation kraus a i = 0) :
    scratchPopulation kraus clean i = 1 := by
  have onlyClean (a : A) : scratchPopulation kraus a i =
      if a = clean then scratchPopulation kraus clean i else 0 := by
    by_cases h : a = clean
    · subst a; simp
    · simp [h,marginal a h]
  calc
    scratchPopulation kraus clean i =
        ∑ a, if a = clean then scratchPopulation kraus clean i else 0 := by simp
    _ = ∑ a, scratchPopulation kraus a i := Finset.sum_congr rfl (fun a _ => (onlyClean a).symm)
    _ = 1 := normalized

/-- A basis input is enough to recover each diagonal marginal from the
reference-separation equation. Together with `fixedScratch_separates` this
makes the exact support criterion equivalent to separation. -/
theorem fixedScratch_iff [Fintype K] [Fintype O] [Fintype I] [DecidableEq I] [DecidableEq A]
    (kraus : K → A → O → I → ℂ) (clean : A) :
    (∀ a ≠ clean, ∀ i, scratchPopulation kraus a i = 0) ↔
    ∀ (R : Type) (input : Matrix (I × R) (I × R) ℂ) a b o p r s,
      jointOutput kraus input (a,o,r) (b,p,s) =
        if a = clean ∧ b = clean then jointOutput kraus input (clean,o,r) (clean,p,s) else 0 := by
  constructor
  · intro marginal R input a b o p r s
    exact fixedScratch_separates kraus clean marginal input a b o p r s
  · intro separates a different i
    classical
    unfold scratchPopulation
    have zero (o : O) : (∑ k, Complex.normSq (kraus k a o i)) = 0 := by
      let input : Matrix (I × Unit) (I × Unit) ℂ := fun x y => if x.1 = i ∧ y.1 = i then 1 else 0
      have diagonal := separates Unit input a a o o () ()
      have asComplex : (∑ k, (Complex.normSq (kraus k a o i) : ℂ)) = 0 := by
        have term (k : K) (l j : I) :
            kraus k a o l * input (l,()) (j,()) * star (kraus k a o j) =
              if l = i then (if j = i then (Complex.normSq (kraus k a o i) : ℂ) else 0) else 0 := by
          by_cases h : l = i <;> by_cases h' : j = i <;>
            simp [input,h,h',Complex.mul_conj]
        simpa only [jointOutput,different,false_and,if_false,term,Finset.sum_ite_irrel,
          Finset.sum_ite_eq',Finset.mem_univ,Finset.sum_const_zero,if_true] using diagonal
      have casted := congrArg Complex.re asComplex
      have realSum (indices : Finset K) :
          (∑ k ∈ indices, (Complex.normSq (kraus k a o i) : ℂ)).re =
            ∑ k ∈ indices, Complex.normSq (kraus k a o i) := by
        induction indices using Finset.induction_on with
        | empty => simp
        | insert k indices fresh ih => simp [Finset.sum_insert fresh,ih]
      simpa only [realSum,Complex.zero_re] using casted
    rw [Finset.sum_comm]
    simp [zero]

#print axioms fixedScratch_iff

end QPTL.FiniteMatrix
