import QleisliKernel.Raw.Instrument

/-! Bounded exact CP-coefficient comparison, an unwired component for #46.
Callers must reconstruct both original bodies and bind their complete source
signatures/effects/dependencies separately. This module creates no accepted
handle, decoder, public request mode or source-preservation claim.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Raw.InstrumentEquality
open Semantics.Exact Finite

structure History where
  outcome : List Bool
  operator : Matrix
  deriving Repr

/-- Read the actual ordered public result projection. Hidden histories remain
separate terms; they are never converted into public labels or normalized. -/
def prepare (outputs : List Nat) (histories : List Instrument.History) : WorkM (List History) :=
  histories.mapM fun history => do
    exactWork (Exact.charge (1 + outputs.length * (1 + history.values.length)))
    let outcome ← outputs.mapM (Instrument.lookup history.values)
    return ⟨outcome,history.operator⟩

/-- One exact Choi coefficient, streamed over all matching hidden histories.
Charging precedes label comparison and arithmetic; a large combined Choi matrix
is never allocated and the scalar carrier's existing capacities are retained. -/
def coefficient (histories : List History) (outcome : List Bool)
    (row col otherRow otherCol : Nat) : WorkM Scalar :=
  histories.foldlM (fun sum history => do
    exactWork (Exact.charge (1 + history.outcome.length))
    if history.outcome != outcome then return sum
    exactWork (Exact.charge 40)
    let conjugate ← lift (arithmetic (Exact.Scalar.conjugate (history.operator.entry otherRow otherCol)))
    let product ← lift (arithmetic (Exact.Scalar.mul (history.operator.entry row col) conjugate))
    lift (arithmetic (Exact.Scalar.add sum product))) Scalar.zero

def validate (rows cols results : Nat) (histories : List History) : WorkM Unit := do
  guard (!histories.isEmpty)
  histories.forM fun history => do
    exactWork (Exact.charge (1 + results + 4 * rows * cols))
    guard (history.outcome.length == results)
    guard (history.operator.rows == rows && history.operator.cols == cols)
    guard (history.operator.entries.length == rows * cols)
    guard (history.operator.entries.all Exact.Scalar.valid)

/-- This is coefficient equality only, not a complete source/artifact gate.
Full physical dimensions and classical arity are supplied by checked original
interfaces. Equal physical sizes alone never establish source type equality. -/
def compare (rows cols results : Nat) (actual expected : List History) : WorkM Unit := do
  guard (Exact.matrixValid rows cols) .limit
  validate rows cols results actual
  validate rows cols results expected
  let count := actual.length + expected.length
  exactWork (Exact.charge (count * count * (1 + results)))
  let outcomes := ((actual ++ expected).map (·.outcome)).eraseDups
  outcomes.forM fun outcome => do
    -- Fail before building coordinate lists when the full comparison cannot
    -- fit even one unit of work per coefficient. Each list has at most 64 cells.
    exactWork (Exact.charge (rows * cols * rows * cols))
    (List.range rows).forM fun row =>
      (List.range cols).forM fun col =>
        (List.range rows).forM fun otherRow =>
          (List.range cols).forM fun otherCol => do
            let left ← coefficient actual outcome row col otherRow otherCol
            let right ← coefficient expected outcome row col otherRow otherCol
            guard (left == right) .equation

end QleisliKernel.Raw.InstrumentEquality
