import Qleisli.Semantics.EngineeringInstrument

/-! Independent Kraus constructions for engineering composition. These
reference definitions retain all public results and hidden histories. They do
not import acceptance, construct source Meaning or issue checked handles.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.Semantics.EngineeringInstrumentComposition
open Qleisli.Semantics.EngineeringInstrument
open scoped BigOperators

/-- Full, unnormalized Kraus completeness for every classical input. -/
def GramComplete {X Y H I O : Type} [Fintype Y] [Fintype H] [Fintype O]
    [Fintype I] [DecidableEq I] (operators : Kraus X Y H I O) : Prop :=
  ∀ input, ∑ y, ∑ h, (operators input y h).conjTranspose * operators input y h = 1

noncomputable def singleton {I O : Type} (matrix : Matrix O I ℂ) :
    Kraus Unit Unit Unit I O := fun _ _ _ => matrix

/-- The entire pair of public results remains public. The second instrument
uses the first public result as its classical input; hidden histories are paired. -/
noncomputable def feedForward {X Y Z H K I M O : Type} [Fintype M]
    (first : Kraus X Y H I M) (second : Kraus Y Z K M O) :
    Kraus X (Y × Z) (H × K) I O :=
  fun input outcomes hidden => second outcomes.1 outcomes.2 hidden.2 *
    first input outcomes.1 hidden.1

noncomputable def liftLeftMatrix {I O S : Type} (matrix : Matrix O I ℂ) :
    Matrix (O × S) (I × S) ℂ := by
  classical
  exact fun row col => if row.2 = col.2 then matrix row.1 col.1 else 0

noncomputable def liftRightMatrix {I O S : Type} (matrix : Matrix O I ℂ) :
    Matrix (S × O) (S × I) ℂ := by
  classical
  exact fun row col => if row.1 = col.1 then matrix row.2 col.2 else 0

noncomputable def extendLeft {X Y H I O S : Type} (operators : Kraus X Y H I O) :
    Kraus X Y H (I × S) (O × S) :=
  fun x y h => liftLeftMatrix (operators x y h)

noncomputable def extendRight {X Y H I O S : Type} (operators : Kraus X Y H I O) :
    Kraus X Y H (S × I) (S × O) :=
  fun x y h => liftRightMatrix (operators x y h)

/-- Ordered axes are part of the type; this does not flatten or swap them. -/
noncomputable def tensorMatrix {I₁ I₂ O₁ O₂ : Type}
    (left : Matrix O₁ I₁ ℂ) (right : Matrix O₂ I₂ ℂ) :
    Matrix (O₁ × O₂) (I₁ × I₂) ℂ :=
  fun output input => left output.1 input.1 * right output.2 input.2

noncomputable def tensor {X₁ X₂ Y₁ Y₂ H₁ H₂ I₁ I₂ O₁ O₂ : Type}
    (left : Kraus X₁ Y₁ H₁ I₁ O₁) (right : Kraus X₂ Y₂ H₂ I₂ O₂) :
    Kraus (X₁ × X₂) (Y₁ × Y₂) (H₁ × H₂) (I₁ × I₂) (O₁ × O₂) :=
  fun inputs outputs histories => tensorMatrix
    (left inputs.1 outputs.1 histories.1) (right inputs.2 outputs.2 histories.2)

end Qleisli.Semantics.EngineeringInstrumentComposition
