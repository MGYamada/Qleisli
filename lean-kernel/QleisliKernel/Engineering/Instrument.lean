import QleisliKernel.Engineering.Pure
import QleisliKernel.Raw.InstrumentEquality

/-! Bounded engineering inequalities for complete observing instruments.
Every public outcome and all four input/residual coordinates are retained.
The closed dyadic majorants and epsilon bound unsquared complex norms. These
components issue no program acceptance, Meaning, coherent control, cleanup,
resource certificate or constitutional PR/RS evidence, including at epsilon zero.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Engineering.Instrument
open Semantics.Exact Finite

structure Cell where
  outcome : List Bool
  row : Nat
  col : Nat
  otherRow : Nat
  otherCol : Nat
  deriving BEq, DecidableEq, Repr

/-- Support is derived from both original families, without relabeling or
normalizing hidden histories. Every absent public outcome has zero coefficients. -/
def outcomes (actual expected : List Raw.InstrumentEquality.History) : List (List Bool) :=
  ((actual ++ expected).map (·.outcome)).eraseDups

/-- Fixed witness order: outcome, row, column, other row, other column. -/
def pairs {A B : Type} (left : List A) (right : List B) : List (A × B) :=
  left.flatMap fun a => right.map fun b => (a,b)

theorem pairs_length {A B : Type} (left : List A) (right : List B) :
    (pairs left right).length = left.length * right.length := by
  induction left with
  | nil => simp [pairs]
  | cons a rest ih =>
    simp only [pairs, List.flatMap_cons, List.length_append, List.length_map] at ih ⊢
    rw [ih]
    simp [Nat.add_mul, Nat.add_comm]

def cells (rows cols : Nat) (labels : List (List Bool)) : List Cell :=
  ((pairs (pairs labels (pairs (List.range rows) (List.range cols)))
      (pairs (List.range rows) (List.range cols))).map fun pair =>
    ⟨pair.1.1,pair.1.2.1,pair.1.2.2,pair.2.1,pair.2.2⟩)

theorem cells_length (rows cols : Nat) (labels : List (List Bool)) :
    (cells rows cols labels).length = labels.length * rows * cols * rows * cols := by
  simp [cells, pairs_length, Nat.mul_assoc]

/-- Both coefficients are freshly streamed over all matching hidden histories.
The existing exact pure arithmetic checks a one-cell complex norm inequality;
this neither asserts that these scalar matrices are pure programs nor accepts
an instrument from a producer-supplied probability or coefficient summary. -/
def checkCell (actual expected : List Raw.InstrumentEquality.History)
    (cell : Cell) (majorant : Coefficient) : WorkM Unit := do
  let a ← Raw.InstrumentEquality.coefficient actual cell.outcome
    cell.row cell.col cell.otherRow cell.otherCol
  let b ← Raw.InstrumentEquality.coefficient expected cell.outcome
    cell.row cell.col cell.otherRow cell.otherCol
  let _ ← Pure.checkMatrices ⟨1,1,[a]⟩ ⟨1,1,[b]⟩ majorant
  pure ()

/-- Exact summation preserves arithmetic capacity failures and shared work.
The caller validates every canonical nonnegative dyadic before this fold. -/
def sumMajorants (majorants : List Coefficient) : WorkM Coefficient :=
  majorants.foldlM (fun total majorant => do
    exactWork (Exact.charge 8)
    lift (arithmetic (Exact.Coefficient.add total majorant))) (.integer 0)

structure Checked where
  outcomes : List (List Bool)
  total : Coefficient
  deriving Repr

/-- Sufficient complete coefficient majorants, separate from exact instrument
equality. Dimensions and scalar capacities are unchanged. Precharging precedes
witness traversal and coordinate allocation; missing/extra witnesses fail. -/
def checkHistories (rows cols results : Nat)
    (actual expected : List Raw.InstrumentEquality.History)
    (epsilon : Coefficient) (majorants : List Coefficient) : WorkM Checked := do
  guard (Exact.matrixValid rows cols) .limit
  guard (Exact.Coefficient.valid epsilon) .invalid
  guard (0 ≤ epsilon.numerator) .request
  exactWork (Exact.charge (1 + majorants.length))
  guard (majorants.all Exact.Coefficient.valid) .invalid
  guard (majorants.all fun q => decide (0 ≤ q.numerator)) .request
  Raw.InstrumentEquality.validate rows cols results actual
  Raw.InstrumentEquality.validate rows cols results expected
  let count := actual.length + expected.length
  exactWork (Exact.charge (count * count * (1 + results)))
  let labels := outcomes actual expected
  let required := labels.length * rows * cols * rows * cols
  guard (majorants.length == required) .request
  exactWork (Exact.charge required)
  -- Each successful Pure.checkMatrices one-cell run necessarily charges 128
  -- in normSqDifferenceWork and 128 for the squared budget. Refuse an
  -- inevitably exhausted computation before allocating its Cartesian cells.
  -- This checks remaining shared work, never a maximum starting allowance.
  let remaining ← get
  guard (256 * required ≤ remaining) .limit
  ((cells rows cols labels).zip majorants).forM fun pair =>
    checkCell actual expected pair.1 pair.2
  let total ← sumMajorants majorants
  exactWork (Exact.charge 8)
  let negative ← lift (arithmetic (Exact.Coefficient.neg total))
  let margin ← lift (arithmetic (Exact.Coefficient.add epsilon negative))
  guard (0 ≤ margin.numerator) .equation
  return ⟨labels,total⟩

structure CellAcceptance (actual expected : List Raw.InstrumentEquality.History)
    (cell : Cell) (majorant : Coefficient) (work left : Nat) where
  actualCoefficient : Scalar
  expectedCoefficient : Scalar
  checked : Pure.Checked
  afterActual : Nat
  afterExpected : Nat
  actualComputed : (Raw.InstrumentEquality.coefficient actual cell.outcome
    cell.row cell.col cell.otherRow cell.otherCol).run work = (.ok actualCoefficient,afterActual)
  expectedComputed : (Raw.InstrumentEquality.coefficient expected cell.outcome
    cell.row cell.col cell.otherRow cell.otherCol).run afterActual = (.ok expectedCoefficient,afterExpected)
  bounded : (Pure.checkMatrices ⟨1,1,[actualCoefficient]⟩ ⟨1,1,[expectedCoefficient]⟩
    majorant).run afterExpected = (.ok checked,left)

theorem checkCell_acceptance (actual expected : List Raw.InstrumentEquality.History)
    (cell : Cell) (majorant : Coefficient) (work left : Nat)
    (ok : (checkCell actual expected cell majorant).run work = (.ok (),left)) :
    Nonempty (CellAcceptance actual expected cell majorant work left) := by
  obtain ⟨a,w₁,ha,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨b,w₂,hb,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨checked,w₃,hc,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).2
  subst w₃
  exact ⟨⟨a,b,checked,w₁,w₂,ha,hb,hc⟩⟩

/-- Facts are obtained from actual successful executions. No caller can supply
these as a replacement for the executable checks or original-body wrapper. -/
structure Conditions (rows cols results : Nat)
    (actual expected : List Raw.InstrumentEquality.History)
    (epsilon : Coefficient) (majorants : List Coefficient) (checked : Checked) : Prop where
  epsilonValid : Exact.Coefficient.valid epsilon = true
  epsilonNonnegative : 0 ≤ epsilon.numerator
  majorantsValid : majorants.all Exact.Coefficient.valid = true
  majorantsNonnegative : majorants.all (fun q => decide (0 ≤ q.numerator)) = true
  actualValidated : ∃ before after,
    (Raw.InstrumentEquality.validate rows cols results actual).run before = (.ok (),after)
  expectedValidated : ∃ before after,
    (Raw.InstrumentEquality.validate rows cols results expected).run before = (.ok (),after)
  labels : checked.outcomes = outcomes actual expected
  length : majorants.length = (cells rows cols checked.outcomes).length
  bounded : ∃ before after,
    (((cells rows cols checked.outcomes).zip majorants).forM fun pair =>
      checkCell actual expected pair.1 pair.2).run before = (.ok (),after)
  summed : ∃ before after,
    (sumMajorants majorants).run before = (.ok checked.total,after)
  margin : ∃ negative margin,
    Exact.Coefficient.neg checked.total = .ok negative ∧
    Exact.Coefficient.add epsilon negative = .ok margin ∧ 0 ≤ margin.numerator

theorem checkHistories_conditions (rows cols results : Nat)
    (actual expected : List Raw.InstrumentEquality.History)
    (epsilon : Coefficient) (majorants : List Coefficient) (checked : Checked) (work left : Nat)
    (ok : (checkHistories rows cols results actual expected epsilon majorants).run work =
      (.ok checked,left)) : Conditions rows cols results actual expected epsilon majorants checked := by
  unfold checkHistories at ok
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,_,hev,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,hen,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,hqv,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,hqn,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₁,hav,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₂,hev',h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,hl,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₃,hb,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨total,w₄,hs,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨negative,_,hn,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨margin,_,hm,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,hpos,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  subst checked
  refine ⟨(guard_success _ _ _ _ hev).1,of_decide_eq_true (guard_success _ _ _ _ hen).1,
    (guard_success _ _ _ _ hqv).1,(guard_success _ _ _ _ hqn).1,
    ⟨_,w₁,hav⟩,⟨w₁,w₂,hev'⟩,rfl,?_,⟨_,w₃,hb⟩,⟨w₃,w₄,hs⟩,
    ⟨negative,margin,arithmetic_success _ _ (lift_success _ _ _ _ hn).1,
      arithmetic_success _ _ (lift_success _ _ _ _ hm).1,
      of_decide_eq_true (guard_success _ _ _ _ hpos).1⟩⟩
  simpa only [cells_length] using (beq_iff_eq.mp (guard_success _ _ _ _ hl).1)

end QleisliKernel.Engineering.Instrument
