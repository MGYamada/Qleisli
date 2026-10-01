import QleisliKernel.Semantics.Function
import Qleisli.Semantics.Raw
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Matrix.Mul

/-! Independent retained-graph meanings, exact attachment data and capacities.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.Raw.Function
open scoped Matrix
open QleisliKernel.Semantics.Exact QleisliKernel.Semantics.Finite QleisliKernel.Semantics.Raw
open QleisliKernel.Semantics.Function Qleisli.Semantics.Raw Qleisli.Semantics.Exact

noncomputable def square (matrix : Matrix) : _root_.Matrix (Fin matrix.cols) (Fin matrix.cols) ℂ :=
  fun row col => entry matrix row col

noncomputable def EntryMeaning (before : List Receipt) (receipt : Receipt) : Prop :=
  ProgramMeaning (before.map Receipt.dependency) receipt.input.body.implementation receipt.meaning ∧
  ProgramMeaning (before.map Receipt.dependency) receipt.input.body.specification receipt.meaning ∧
  (square receipt.meaning)ᴴ * square receipt.meaning = 1 ∧
  square receipt.meaning * (square receipt.meaning)ᴴ = 1 ∧
  receipt.depth ≤ 32 ∧ receipt.expandedSteps ≤ 1000000 ∧
  ∃ implementation specification specificationCount,
    QleisliKernel.Semantics.RawTrace.run receipt.input.body.implementation = some implementation ∧
    QleisliKernel.Semantics.RawTrace.run receipt.input.body.specification = some specification ∧
    QleisliKernel.Semantics.Function.expansion (before.map (·.expandedSteps)) implementation.events = some receipt.expandedSteps ∧
    QleisliKernel.Semantics.Function.expansion (before.map (·.expandedSteps)) specification.events = some specificationCount ∧
    specificationCount ≤ 1000000

inductive GraphMeaning : List Receipt → Prop
  | nil : GraphMeaning []
  | snoc (before receipt) (prefixMeaning : GraphMeaning before) (entryMeaning : EntryMeaning before receipt) :
    GraphMeaning (before ++ [receipt])

end Qleisli.Raw.Function
