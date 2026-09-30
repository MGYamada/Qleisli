import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic

/-! Phase-preserving coordinate-local operators and explicit wire permutations.
This reference algebra has no circuit/checker imports. Ordered positions select
the local matrix coordinates; all other bits are retained by an exact delta.
Actual artifact typing must establish the positions' bounds and distinctness.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.CoordinateOperators
open scoped BigOperators Matrix

abbrev Bits (n : Nat) := Fin n → Bool

def outside {n k : Nat} (positions : Fin k → Fin n) (output input : Bits n) : Prop :=
  ∀ axis, (∀ selected, positions selected ≠ axis) → output axis = input axis

noncomputable def lift {n k : Nat} (positions : Fin k → Fin n)
    (operator : Matrix (Bits k) (Bits k) ℂ) : Matrix (Bits n) (Bits n) ℂ := by
  classical
  exact fun output input => if outside positions output input then
    operator (output ∘ positions) (input ∘ positions) else 0

/-- A route maps each output position to its old input position. -/
def basisEquiv {n : Nat} (route : Equiv.Perm (Fin n)) : Equiv.Perm (Bits n) where
  toFun bits := bits ∘ route
  invFun bits := bits ∘ route.symm
  left_inv bits := by funext axis; simp
  right_inv bits := by funext axis; simp

noncomputable def routeMatrix {n : Nat} (route : Equiv.Perm (Fin n)) :
    Matrix (Bits n) (Bits n) ℂ := by
  classical
  exact fun output input => if output = basisEquiv route input then 1 else 0

theorem outside_route {n k : Nat} (positions : Fin k → Fin n)
    (route : Equiv.Perm (Fin n)) (output input : Bits n) :
    outside positions (output ∘ route) (input ∘ route) ↔
      outside (route ∘ positions) output input := by
  constructor
  · intro same axis unselected
    have absent : ∀ selected, positions selected ≠ route.symm axis := by
      intro selected equal
      apply unselected selected
      simp only [Function.comp_apply,equal,route.apply_symm_apply]
    simpa only [Function.comp_apply,route.apply_symm_apply] using same (route.symm axis) absent
  · intro same axis unselected
    apply same (route axis)
    intro selected equal
    exact unselected selected (route.injective equal)

theorem local_reindex {n k : Nat} (positions : Fin k → Fin n)
    (operator : Matrix (Bits k) (Bits k) ℂ) (route : Equiv.Perm (Fin n)) :
    (lift positions operator).submatrix (basisEquiv route) (basisEquiv route) =
      lift (route ∘ positions) operator := by
  ext output input
  simp only [lift,Matrix.submatrix,Matrix.of_apply,basisEquiv,Equiv.coe_fn_mk,outside_route,
    Function.comp_assoc]
  split_ifs with first second second
  · rfl
  · exact False.elim (second ((outside_route positions route output input).mp first))
  · exact False.elim (first ((outside_route positions route output input).mpr second))
  · rfl

theorem mul_route {n : Nat} (operator : Matrix (Bits n) (Bits n) ℂ)
    (route : Equiv.Perm (Fin n)) (output input : Bits n) :
    (operator * routeMatrix route) output input = operator output (basisEquiv route input) := by
  classical
  simp [Matrix.mul_apply,routeMatrix,mul_ite]

theorem route_mul {n : Nat} (operator : Matrix (Bits n) (Bits n) ℂ)
    (route : Equiv.Perm (Fin n)) (output input : Bits n) :
    (routeMatrix route * operator) output input = operator ((basisEquiv route).symm output) input := by
  classical
  have match_input (middle : Bits n) : output = basisEquiv route middle ↔
      middle = (basisEquiv route).symm output := by
    exact ⟨fun h => (Equiv.eq_symm_apply _).mpr h.symm,
      fun h => (h ▸ (basisEquiv route).apply_symm_apply output).symm⟩
  simp [Matrix.mul_apply,routeMatrix,match_input,ite_mul]

/-- Moving a local operation across an earlier route transports every selected
position through that route. This is an exact matrix equation, including phase. -/
theorem local_route {n k : Nat} (positions : Fin k → Fin n)
    (operator : Matrix (Bits k) (Bits k) ℂ) (route : Equiv.Perm (Fin n)) :
    lift positions operator * routeMatrix route =
      routeMatrix route * lift (route ∘ positions) operator := by
  ext output input
  rw [mul_route,route_mul]
  have reindexed := congrFun (congrFun (local_reindex positions operator route)
    ((basisEquiv route).symm output)) input
  simpa only [Matrix.submatrix,Matrix.of_apply,Equiv.apply_symm_apply] using reindexed

theorem route_one (n : Nat) : routeMatrix (Equiv.refl (Fin n)) = 1 := by
  classical
  ext output input
  simp [routeMatrix,basisEquiv,Matrix.one_apply]

theorem route_comp {n : Nat} (first second : Equiv.Perm (Fin n)) :
    routeMatrix first * routeMatrix second = routeMatrix (first.trans second) := by
  ext output input
  rw [mul_route]
  rfl

theorem outside_comp {n k j : Nat} (outer : Fin k → Fin n)
    (injective : Function.Injective outer) (inner : Fin j → Fin k) (output input : Bits n) :
    outside (outer ∘ inner) output input ↔
      outside outer output input ∧ outside inner (output ∘ outer) (input ∘ outer) := by
  constructor
  · intro same
    constructor
    · intro axis absent
      exact same axis (fun selected => absent (inner selected))
    · intro axis absent
      exact same (outer axis) (fun selected equal => absent selected (injective equal))
  · rintro ⟨outerSame,innerSame⟩ axis absent
    by_cases present : ∃ selected, outer selected = axis
    · obtain ⟨selected,rfl⟩ := present
      exact innerSame selected (fun i equal => absent i (congrArg outer equal))
    · exact outerSame axis (fun selected equal => present ⟨selected,equal⟩)

/-- Local embedding composes through a distinct outer coordinate selection. -/
theorem lift_compose {n k j : Nat} (outer : Fin k → Fin n)
    (injective : Function.Injective outer) (inner : Fin j → Fin k)
    (operator : Matrix (Bits j) (Bits j) ℂ) :
    lift outer (lift inner operator) = lift (outer ∘ inner) operator := by
  classical
  ext output input
  have same := outside_comp outer injective inner output input
  by_cases a : outside outer output input <;>
    by_cases b : outside inner (output ∘ outer) (input ∘ outer) <;>
    simp [lift,same,a,b,Function.comp_assoc]

theorem lift_one {n k : Nat} (positions : Fin k → Fin n) :
    lift positions (1 : Matrix (Bits k) (Bits k) ℂ) = 1 := by
  classical
  ext output input
  by_cases same : output = input
  · subst input
    simp [lift,outside]
  · have impossible : outside positions output input → output ∘ positions ≠ input ∘ positions := by
      intro unchanged selected
      apply same
      funext axis
      by_cases present : ∃ i, positions i = axis
      · obtain ⟨i,rfl⟩ := present
        exact congrFun selected i
      · exact unchanged axis (fun i equal => present ⟨i,equal⟩)
    by_cases unchanged : outside positions output input <;>
      simp [lift,unchanged,same,impossible]

theorem lift_all (n : Nat) (operator : Matrix (Bits n) (Bits n) ℂ) :
    lift (id : Fin n → Fin n) operator = operator := by
  ext output input
  have unchanged : outside (id : Fin n → Fin n) output input := by
    intro axis absent
    exact False.elim (absent axis rfl)
  simp [lift,unchanged]

theorem outside_left (n m : Nat) (output input : Bits (n+m)) :
    outside (Fin.castAdd m : Fin n → Fin (n+m)) output input ↔
      (fun i : Fin m => output (i.natAdd n)) = (fun i => input (i.natAdd n)) := by
  constructor
  · intro same
    funext i
    apply same (i.natAdd n)
    intro selected equal
    have values := congrArg Fin.val equal
    simp only [Fin.val_castAdd,Fin.val_natAdd] at values
    omega
  · intro same axis
    refine Fin.addCases (fun i absent => ?_) (fun i _ => ?_) axis
    · exact False.elim (absent i rfl)
    · exact congrFun same i

theorem outside_right (n m : Nat) (output input : Bits (n+m)) :
    outside (Fin.natAdd n : Fin m → Fin (n+m)) output input ↔
      (fun i : Fin n => output (i.castAdd m)) = (fun i => input (i.castAdd m)) := by
  constructor
  · intro same
    funext i
    apply same (i.castAdd m)
    intro selected equal
    have values := congrArg Fin.val equal
    simp only [Fin.val_castAdd,Fin.val_natAdd] at values
    omega
  · intro same axis
    refine Fin.addCases (fun i _ => ?_) (fun i absent => ?_) axis
    · exact congrFun same i
    · exact False.elim (absent i rfl)

theorem lift_left (n m : Nat) (operator : Matrix (Bits n) (Bits n) ℂ)
    (output input : Bits (n+m)) :
    lift (Fin.castAdd m) operator output input =
      if (fun i : Fin m => output (i.natAdd n)) = (fun i => input (i.natAdd n)) then
        operator (fun i => output (i.castAdd m)) (fun i => input (i.castAdd m)) else 0 := by
  classical
  simp only [lift,outside_left,Function.comp_def]

theorem lift_right (n m : Nat) (operator : Matrix (Bits m) (Bits m) ℂ)
    (output input : Bits (n+m)) :
    lift (Fin.natAdd n) operator output input =
      if (fun i : Fin n => output (i.castAdd m)) = (fun i => input (i.castAdd m)) then
        operator (fun i => output (i.natAdd n)) (fun i => input (i.natAdd n)) else 0 := by
  classical
  simp only [lift,outside_right,Function.comp_def]

noncomputable def tensor {n m : Nat} (left : Matrix (Bits n) (Bits n) ℂ)
    (right : Matrix (Bits m) (Bits m) ℂ) : Matrix (Bits (n+m)) (Bits (n+m)) ℂ :=
  fun output input =>
    left (fun i => output (i.castAdd m)) (fun i => input (i.castAdd m)) *
    right (fun i => output (i.natAdd n)) (fun i => input (i.natAdd n))

/-- Tensoring disjoint operations equals sequential execution of their exact
coordinate lifts. This includes zero-width factors and arbitrary scalar phases. -/
theorem tensor_lifts {n m : Nat} (left : Matrix (Bits n) (Bits n) ℂ)
    (right : Matrix (Bits m) (Bits m) ℂ) :
    lift (Fin.natAdd n) right * lift (Fin.castAdd m) left = tensor left right := by
  classical
  ext output input
  rw [Matrix.mul_apply]
  rw [← (Equiv.sum_comp (Fin.appendEquiv n m)
    (fun middle => lift (Fin.natAdd n) right output middle * lift (Fin.castAdd m) left middle input))]
  simp [Fintype.sum_prod_type,lift_left,lift_right,Fin.appendEquiv,tensor,
    mul_ite,mul_comm]

theorem tensor_mul {n m : Nat} (a c : Matrix (Bits n) (Bits n) ℂ)
    (b d : Matrix (Bits m) (Bits m) ℂ) :
    tensor a b * tensor c d = tensor (a*c) (b*d) := by
  ext output input
  rw [Matrix.mul_apply]
  rw [← (Equiv.sum_comp (Fin.appendEquiv n m)
    (fun middle => tensor a b output middle * tensor c d middle input))]
  simp only [Fintype.sum_prod_type,tensor,Fin.appendEquiv,Equiv.coe_fn_mk,
    Fin.append_left,Fin.append_right,Matrix.mul_apply]
  simp only [Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  ring

theorem tensor_one_right {n m : Nat} (operator : Matrix (Bits n) (Bits n) ℂ) :
    tensor operator (1 : Matrix (Bits m) (Bits m) ℂ) = lift (Fin.castAdd m) operator := by
  classical
  ext output input
  simp [tensor,lift_left,Matrix.one_apply,mul_ite]

theorem tensor_one_left {n m : Nat} (operator : Matrix (Bits m) (Bits m) ℂ) :
    tensor (1 : Matrix (Bits n) (Bits n) ℂ) operator = lift (Fin.natAdd n) operator := by
  classical
  ext output input
  simp [tensor,lift_right,Matrix.one_apply,ite_mul]

theorem lift_left_mul {n m : Nat} (a b : Matrix (Bits n) (Bits n) ℂ) :
    lift (Fin.castAdd m) (a*b) = lift (Fin.castAdd m) a * lift (Fin.castAdd m) b := by
  rw [← tensor_one_right,← tensor_one_right,← tensor_one_right,tensor_mul,Matrix.one_mul]

theorem lift_left_fold {n m : Nat} (operators : List (Matrix (Bits n) (Bits n) ℂ))
    (initial : Matrix (Bits n) (Bits n) ℂ) :
    lift (Fin.castAdd m) (operators.foldl (fun before operator => operator * before) initial) =
      operators.foldl (fun before operator => lift (Fin.castAdd m) operator * before)
        (lift (Fin.castAdd m) initial) := by
  induction operators generalizing initial with
  | nil => rfl
  | cons operator operators ih =>
    simp only [List.foldl_cons,ih,lift_left_mul]

theorem lift_right_mul {n m : Nat} (a b : Matrix (Bits m) (Bits m) ℂ) :
    lift (Fin.natAdd n) (a*b) = lift (Fin.natAdd n) a * lift (Fin.natAdd n) b := by
  rw [← tensor_one_left,← tensor_one_left,← tensor_one_left,tensor_mul,Matrix.one_mul]

def appendRoute {n m : Nat} (first : Equiv.Perm (Fin n)) (second : Equiv.Perm (Fin m)) :
    Equiv.Perm (Fin (n+m)) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr first second).trans finSumFinEquiv)

theorem appendRoute_left {n m : Nat} (first : Equiv.Perm (Fin n)) (second : Equiv.Perm (Fin m))
    (axis : Fin n) : appendRoute first second (axis.castAdd m) = (first axis).castAdd m := by
  simp [appendRoute]

theorem appendRoute_right {n m : Nat} (first : Equiv.Perm (Fin n)) (second : Equiv.Perm (Fin m))
    (axis : Fin m) : appendRoute first second (axis.natAdd n) = (second axis).natAdd n := by
  simp [appendRoute]

theorem tensor_route {n m : Nat} (first : Equiv.Perm (Fin n)) (second : Equiv.Perm (Fin m)) :
    tensor (routeMatrix first) (routeMatrix second) = routeMatrix (appendRoute first second) := by
  classical
  ext output input
  have same : output = basisEquiv (appendRoute first second) input ↔
      (fun i => output (i.castAdd m)) = basisEquiv first (fun i => input (i.castAdd m)) ∧
      (fun i => output (i.natAdd n)) = basisEquiv second (fun i => input (i.natAdd n)) := by
    constructor
    · intro equal
      subst output
      constructor <;> (funext axis; simp [basisEquiv,appendRoute_left,appendRoute_right])
    · rintro ⟨left,right⟩
      funext axis
      refine Fin.addCases (fun i => ?_) (fun i => ?_) axis
      · simpa only [basisEquiv,Equiv.coe_fn_mk,Function.comp_apply,appendRoute_left] using congrFun left i
      · simpa only [basisEquiv,Equiv.coe_fn_mk,Function.comp_apply,appendRoute_right] using congrFun right i
  simp only [tensor,routeMatrix]
  split_ifs <;> simp_all

end Qleisli.CoordinateOperators
