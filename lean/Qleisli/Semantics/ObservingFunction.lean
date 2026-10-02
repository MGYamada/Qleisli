import QleisliKernel.Semantics.ObservingFunction
import Qleisli.Semantics.RawInstrument
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Matrix.Mul

/-! Independent full original closed-branch function meaning. The graph fixes
original attachments and complete phase-sensitive operators, never receipts.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.Semantics.ObservingFunction
open QleisliKernel.Semantics.ObservingFunction QleisliKernel.Semantics.Finite
open scoped Matrix

noncomputable def BodyMeaning (dependencies : List Dependency)
    (program : QleisliKernel.Semantics.Observation.Program) (operator : QleisliKernel.Semantics.Exact.Matrix) : Prop :=
  ∃ values, RawInstrument.ProgramMeaning dependencies program [] [⟨values,[],operator⟩]

noncomputable def square (matrix : QleisliKernel.Semantics.Exact.Matrix) :
    _root_.Matrix (Fin matrix.cols) (Fin matrix.cols) ℂ :=
  fun row col => Exact.entry matrix row col

noncomputable def EntryMeaning (before : List Receipt) (receipt : Receipt) : Prop :=
  BodyMeaning (before.map Receipt.dependency) receipt.input.implementation receipt.meaning ∧
  BodyMeaning (before.map Receipt.dependency) receipt.input.specification receipt.meaning ∧
  (square receipt.meaning)ᴴ * square receipt.meaning = 1 ∧
  square receipt.meaning * (square receipt.meaning)ᴴ = 1 ∧
  receipt.depth ≤ 32 ∧ receipt.expandedSteps ≤ 1000000

inductive GraphMeaning : List Receipt → Prop
  | nil : GraphMeaning []
  | snoc (before receipt) (previous : GraphMeaning before) (node : EntryMeaning before receipt) :
      GraphMeaning (before ++ [receipt])

end Qleisli.Semantics.ObservingFunction
