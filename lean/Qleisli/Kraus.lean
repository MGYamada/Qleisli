import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
Finite Kraus completeness over actual complex matrices. These local algebraic
results support fixed finite quantum interfaces and require the displayed
completeness or isometry equations. They do not formalize source typing, Rust compilation,
positive density operators, or the full semantics of a source program.
-/

namespace Qleisli.Kraus

open scoped BigOperators Matrix

variable {ι κ input middle output : Type*}
variable [Fintype ι] [Fintype κ]
variable [Fintype middle] [Fintype output]

/-- The finite Kraus completeness equation, with rows indexing the output and
columns indexing the input. -/
def Complete [DecidableEq input] (A : ι → Matrix middle input ℂ) : Prop :=
  ∑ i, (A i)ᴴ * A i = 1

/-- A single isometry is a complete one-outcome family. -/
theorem singleton_complete [DecidableEq input]
    (V : Matrix middle input ℂ) (hV : Vᴴ * V = 1) :
    Complete (fun _ : Unit => V) := by
  simpa [Complete] using hV

/-- The exact Gram matrix of a composite with an isometric second stage. -/
theorem isometry_postcompose_gram [DecidableEq middle] (A : Matrix middle input ℂ)
    (P : Matrix output middle ℂ) (hP : Pᴴ * P = 1) :
    (P * A)ᴴ * (P * A) = Aᴴ * A := by
  rw [Matrix.conjTranspose_mul]
  calc
    Aᴴ * Pᴴ * (P * A) = Aᴴ * (Pᴴ * P) * A := by
      simp only [Matrix.mul_assoc]
    _ = Aᴴ * A := by rw [hP, Matrix.mul_one]

/-- The matrix composite of two isometries is an isometry. -/
theorem isometry_comp [DecidableEq input] [DecidableEq middle]
    (A : Matrix middle input ℂ) (P : Matrix output middle ℂ)
    (hA : Aᴴ * A = 1) (hP : Pᴴ * P = 1) :
    (P * A)ᴴ * (P * A) = 1 := by
  rw [isometry_postcompose_gram A P hP, hA]

/-- A complete output-interface transport for each outcome preserves
completeness. A unitary phi transport satisfies the weaker isometry premise
used here. The equation must hold on the entire intermediate interface. -/
theorem complete_postcompose [DecidableEq input] [DecidableEq middle]
    (A : ι → Matrix middle input ℂ)
    (P : ι → Matrix output middle ℂ) (hA : Complete A)
    (hP : ∀ i, (P i)ᴴ * P i = 1) :
    Complete (fun i => P i * A i) := by
  simpa only [Complete, isometry_postcompose_gram _ _ (hP _)] using hA

/-- Adaptive composition: after first-stage outcome `i`, use the complete
second-stage family `B i`. Every history `(i,j)` is retained in the sum.
No relation between the second stages at different first outcomes is needed. -/
theorem adaptive_complete [DecidableEq input] [DecidableEq middle]
    (A : ι → Matrix middle input ℂ)
    (B : ι → κ → Matrix output middle ℂ)
    (hA : Complete A) (hB : ∀ i, Complete (B i)) :
    ∑ i, ∑ j, (B i j * A i)ᴴ * (B i j * A i) = 1 := by
  calc
    ∑ i, ∑ j, (B i j * A i)ᴴ * (B i j * A i) =
        ∑ i, (A i)ᴴ * (∑ j, (B i j)ᴴ * B i j) * A i := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [Matrix.conjTranspose_mul, Matrix.mul_sum, Matrix.sum_mul,
        Matrix.mul_assoc]
    _ = ∑ i, (A i)ᴴ * A i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show ∑ j, (B i j)ᴴ * B i j = 1 from hB i, Matrix.mul_one]
    _ = 1 := hA

end Qleisli.Kraus
