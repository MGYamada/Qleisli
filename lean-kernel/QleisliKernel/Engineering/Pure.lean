import QleisliKernel.Finite

/-! Bounded engineering inequalities in the existing exact R8 carrier.
These components issue no accepted program, Meaning, capability, cleanup,
constitutional PR/RS evidence or serialized receipt. Separate adapters bind
original artifacts, requests and execution views; this arithmetic component
does not certify resources. Exact PureLeaf/equality acceptance remains unchanged.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Engineering.Pure
open Semantics.Exact

/-- Exact a² - 2b². Capacity failures remain errors, never comparison answers. -/
def squareGap (a b : Coefficient) : Except Exact.Error Coefficient := do
  let aa ← Exact.Coefficient.mul a a
  let bb ← Exact.Coefficient.mul b b
  let twice ← Exact.Coefficient.mul (.integer 2) bb
  let negative ← Exact.Coefficient.neg twice
  Exact.Coefficient.add aa negative

/-- Arithmetic sign test for a+b√2, not an acceptance or evidence authority. -/
def realNonneg (a b : Coefficient) : Except Exact.Error Bool :=
  if !(Exact.Coefficient.valid a && Exact.Coefficient.valid b) then
    .error .arithmeticCapacity
  else if 0 ≤ a.numerator then
    if 0 ≤ b.numerator then .ok true
    else do
      let gap ← squareGap a b
      return decide (0 ≤ gap.numerator)
  else
    if b.numerator ≤ 0 then .ok false
    else do
      let gap ← squareGap a b
      return decide (gap.numerator ≤ 0)

def coordinates (rows cols : Nat) : List (Nat × Nat) :=
  (List.range rows).flatMap fun row => (List.range cols).map fun col => (row,col)

def accumulate (actual ideal : Matrix) (sum : Scalar) (index : Nat × Nat) :
    Exact.WorkM Scalar := do
  let negative ← Exact.liftExact (Exact.Scalar.neg (ideal.entry index.1 index.2))
  let difference ← Exact.liftExact (Exact.Scalar.add (actual.entry index.1 index.2) negative)
  let conjugate ← Exact.liftExact (Exact.Scalar.conjugate difference)
  let term ← Exact.liftExact (Exact.Scalar.mul conjugate difference)
  Exact.liftExact (Exact.Scalar.add sum term)

/-- Inputs have passed matrixRead; dimensions are bounded again before any
coordinate allocation. Precharge covers all bounded scalar calls in the fold.
This work counter is checker work, never a quantum target resource measure. -/
def normSqDifferenceWork (actual ideal : Matrix) : Exact.WorkM Scalar :=
  if !Exact.matrixValid actual.rows actual.cols ||
      !Exact.matrixValid ideal.rows ideal.cols then throw .dimension
  else if actual.rows ≠ ideal.rows || actual.cols ≠ ideal.cols then throw .shapeMismatch
  else if actual.entries.length ≠ actual.rows * actual.cols ||
      ideal.entries.length ≠ ideal.rows * ideal.cols then throw .entryCount
  else do
    Exact.charge (4 * (actual.entries.length + ideal.entries.length))
    if !(actual.entries.all Exact.Scalar.valid && ideal.entries.all Exact.Scalar.valid) then
      throw .arithmeticCapacity
    else do
      Exact.charge (128 * actual.rows * actual.cols)
      (coordinates actual.rows actual.cols).foldlM (accumulate actual ideal) Scalar.zero

structure Checked where
  squaredError : Scalar
  margin : Scalar
  deriving Repr

/-- A sufficient Frobenius-square witness for a phase-sensitive Euclidean
operator bound on arbitrary rectangular matrices. This proves no isometry;
original pure artifacts must independently pass their existing exact gates. -/
def checkMatrices (actual ideal : Matrix) (epsilon : Coefficient) : Finite.WorkM Checked := do
  Finite.guard (Exact.Coefficient.valid epsilon) .invalid
  Finite.guard (0 ≤ epsilon.numerator) .request
  let actual ← Finite.matrixRead actual
  let ideal ← Finite.matrixRead ideal
  Finite.guard (actual.rows == ideal.rows && actual.cols == ideal.cols) .request
  let squaredError ← Finite.exactWork (normSqDifferenceWork actual ideal)
  Finite.exactWork (Exact.charge 128)
  let squaredBudget ← Finite.lift (Finite.arithmetic (Exact.Coefficient.mul epsilon epsilon))
  let negative ← Finite.lift (Finite.arithmetic (Exact.Scalar.neg squaredError))
  let zero := Coefficient.integer 0
  let margin ← Finite.lift (Finite.arithmetic
    (Exact.Scalar.add ⟨squaredBudget,zero,zero,zero⟩ negative))
  Finite.guard (margin.c.numerator == 0 && margin.d.numerator == 0) .equation
  let nonnegative ← Finite.lift (Finite.arithmetic (realNonneg margin.a margin.b))
  Finite.guard nonnegative .equation
  return ⟨squaredError,margin⟩

structure Conditions (actual ideal : Matrix) (epsilon : Coefficient) (checked : Checked) : Prop where
  epsilonValid : Exact.Coefficient.valid epsilon = true
  epsilonNonnegative : 0 ≤ epsilon.numerator
  rows : actual.rows = ideal.rows
  cols : actual.cols = ideal.cols
  sum : ∃ before after, (normSqDifferenceWork actual ideal).run before =
    (.ok checked.squaredError,after)
  budget : ∃ squaredBudget negative,
    Exact.Coefficient.mul epsilon epsilon = .ok squaredBudget ∧
    Exact.Scalar.neg checked.squaredError = .ok negative ∧
    Exact.Scalar.add ⟨squaredBudget,.integer 0,.integer 0,.integer 0⟩ negative = .ok checked.margin
  real : checked.margin.c.numerator = 0 ∧ checked.margin.d.numerator = 0
  nonnegative : realNonneg checked.margin.a checked.margin.b = .ok true

/-- Facts are extracted from this actual execution, not a producer receipt. -/
theorem checkMatrices_conditions (actual ideal : Matrix) (epsilon : Coefficient)
    (checked : Checked) (work left : Nat)
    (ok : (checkMatrices actual ideal epsilon).run work = (.ok checked,left)) :
    Conditions actual ideal epsilon checked := by
  unfold checkMatrices at ok
  obtain ⟨_,w₁,hv,h⟩ := Finite.bind_success _ _ _ _ _ ok
  obtain ⟨_,w₂,hn,h⟩ := Finite.bind_success _ _ _ _ _ h
  obtain ⟨a,w₃,ha,h⟩ := Finite.bind_success _ _ _ _ _ h
  obtain ⟨u,w₄,hu,h⟩ := Finite.bind_success _ _ _ _ _ h
  have ae := (Finite.matrixRead_value _ _ _ _ ha).1
  have ue := (Finite.matrixRead_value _ _ _ _ hu).1
  subst a; subst u
  obtain ⟨_,w₅,hs,h⟩ := Finite.bind_success _ _ _ _ _ h
  obtain ⟨sum,w₆,hf,h⟩ := Finite.bind_success _ _ _ _ _ h
  obtain ⟨_,w₇,_,h⟩ := Finite.bind_success _ _ _ _ _ h
  obtain ⟨budget,w₈,hb,h⟩ := Finite.bind_success _ _ _ _ _ h
  obtain ⟨negative,w₉,he,h⟩ := Finite.bind_success _ _ _ _ _ h
  obtain ⟨margin,w₁₀,hm,h⟩ := Finite.bind_success _ _ _ _ _ h
  obtain ⟨_,w₁₁,hr,h⟩ := Finite.bind_success _ _ _ _ _ h
  obtain ⟨nonnegative,w₁₂,hp,h⟩ := Finite.bind_success _ _ _ _ _ h
  obtain ⟨_,w₁₃,hg,h⟩ := Finite.bind_success _ _ _ _ _ h
  have result := (Finite.pure_success _ _ _ _ h).1
  subst checked
  have shapes := (Finite.guard_success _ _ _ _ hs).1
  have real := (Finite.guard_success _ _ _ _ hr).1
  simp only [Bool.and_eq_true,beq_iff_eq] at shapes real
  have nonnegativeEq := (Finite.guard_success _ _ _ _ hg).1
  subst nonnegative
  exact ⟨(Finite.guard_success _ _ _ _ hv).1,
    of_decide_eq_true (Finite.guard_success _ _ _ _ hn).1,
    shapes.1,shapes.2,⟨w₅,w₆,Finite.exactWork_success _ _ _ _ hf⟩,
    ⟨budget,negative,Finite.arithmetic_success _ _ (Finite.lift_success _ _ _ _ hb).1,
      Finite.arithmetic_success _ _ (Finite.lift_success _ _ _ _ he).1,
      Finite.arithmetic_success _ _ (Finite.lift_success _ _ _ _ hm).1⟩,
    real,Finite.arithmetic_success _ _ (Finite.lift_success _ _ _ _ hp).1⟩

end QleisliKernel.Engineering.Pure
