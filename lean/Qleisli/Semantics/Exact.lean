import QleisliKernel.Semantics.Exact
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Independent R8 denotation. This specification imports data only, never
the executable normalizer, arithmetic, work accounting or acceptance.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.Semantics.Exact
open QleisliKernel.Semantics.Exact

def rational (x : Coefficient) : ℚ := (x.numerator : ℚ) / 2 ^ x.exponent

noncomputable def scalar (x : Scalar) : ℂ :=
  (rational x.a : ℂ) + (rational x.b : ℂ) * (Real.sqrt 2 : ℂ) +
    Complex.I * ((rational x.c : ℂ) + (rational x.d : ℂ) * (Real.sqrt 2 : ℂ))

noncomputable def basisWeight : Nat → ℂ
  | 0 => 1 | 1 => (Real.sqrt 2 : ℂ) | 2 => Complex.I | _ => Complex.I * (Real.sqrt 2 : ℂ)


noncomputable def entry (x : Matrix) (row col : Nat) : ℂ := scalar (x.entry row col)

/-- Finite matrix action, preserving the entire complex scalar and reference. -/
noncomputable def action (x : Matrix) {R : Type} (joint : Nat → R → ℂ)
    (row : Nat) (reference : R) : ℂ :=
  ((List.range x.cols).map (fun col => entry x row col * joint col reference)).sum

end Qleisli.Semantics.Exact
