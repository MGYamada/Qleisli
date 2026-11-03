import Qleisli.ExactMatrix
import QleisliKernel.CodeSpace

/-! Complex reference action of the actual code-space composition receipts.
Both bounded matrix products in the existing Map equation denote the same
operator on every joint amplitude family. This does not establish the Raw
program's matrix, a whole forest factorization or a Gram/isometry property.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.CodeSpace
open QleisliKernel.Semantics.Exact Qleisli.Semantics.Exact

/-- The exact native composition witnesses preserve complete phase and
arbitrary untouched references. No separability or bounded input evaluation
premise replaces either actual matrix-product receipt. -/
theorem map_reference_action {Reference : Type} {inputCode outputCode physical : Matrix}
    (checked : QleisliKernel.CodeSpace.Map inputCode outputCode physical)
    (joint : Nat → Reference → ℂ) (row : Nat) (reference : Reference)
    (bound : row < physical.rows) :
    action physical (fun input ref => action inputCode joint input ref) row reference =
      action outputCode (fun output ref => action checked.logical joint output ref) row reference := by
  obtain ⟨actual,a,b,c,d,left,right⟩ := checked.equation
  have outputBound : row < outputCode.rows := by
    rw [← checked.physicalShape.2]
    exact bound
  calc
    _ = action actual joint row reference :=
      (Qleisli.Exact.compose_action physical inputCode actual a b left joint row reference bound).symm
    _ = _ := Qleisli.Exact.compose_action outputCode checked.logical actual c d right
      joint row reference outputBound

#print axioms map_reference_action

end Qleisli.CodeSpace
