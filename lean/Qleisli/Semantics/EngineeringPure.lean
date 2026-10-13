import Qleisli.Semantics.Exact
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Independent phase-sensitive engineering metric on exact finite matrices.
Only coefficient data and complex meaning are imported, never the checker.
This inequality does not identify either artifact's exact Meaning with the
other and supplies no constitutional PR/RS, cleanup or capability authority.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.Semantics.EngineeringPure
open QleisliKernel.Semantics.Exact Qleisli.Semantics.Exact
open scoped BigOperators

noncomputable def realPair (a b : Coefficient) : ℝ :=
  (rational a : ℝ) + (rational b : ℝ) * Real.sqrt 2

noncomputable def gapMatrix (rows cols : Nat) (actual ideal : Matrix) :
    _root_.Matrix (Fin rows) (Fin cols) ℂ :=
  fun row col => entry actual row col - entry ideal row col

noncomputable def squaredDistance (actual ideal : Matrix) : ℝ :=
  ∑ row : Fin actual.rows, ∑ col : Fin actual.cols,
    Complex.normSq (gapMatrix actual.rows actual.cols actual ideal row col)

/-- Explicit Euclidean operator norm: ordinary Matrix norm instances are not
used, and no minimization over global phase or projective quotient occurs. -/
noncomputable def gapCLM (actual ideal : Matrix) :
    EuclideanSpace ℂ (Fin actual.cols) →L[ℂ] EuclideanSpace ℂ (Fin actual.rows) :=
  LinearMap.toContinuousLinearMap
    (Matrix.toLpLin 2 2 (gapMatrix actual.rows actual.cols actual ideal))

def OperatorBound (actual ideal : Matrix) (epsilon : Coefficient) : Prop :=
  actual.rows = ideal.rows ∧ actual.cols = ideal.cols ∧
    0 ≤ (rational epsilon : ℝ) ∧ ‖gapCLM actual ideal‖ ≤ (rational epsilon : ℝ)

end Qleisli.Semantics.EngineeringPure
