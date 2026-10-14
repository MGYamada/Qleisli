import Qleisli.Semantics.InstrumentEquality
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Independent finite instrument engineering bounds. The norm is explicitly
the Euclidean operator norm, with the supremum norm on public-outcome families.
All hidden Kraus histories contribute without renormalization. These definitions
grant no exact Meaning, capability, cleanup or constitutional PR/RS authority,
including when the engineering budget is zero.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.Semantics.EngineeringInstrument
open scoped BigOperators

abbrev Kraus (X Y H I O : Type) := X → Y → H → Matrix O I ℂ
abbrev Joint (I R : Type) := EuclideanSpace ℂ (I × R)
abbrev Observable (Y O R : Type) := Y → Joint O R →L[ℂ] Joint O R

noncomputable def choi {X Y H I O : Type} [Fintype H]
    (operators : Kraus X Y H I O) (input : X) (outcome : Y) :
    Matrix (O × I) (O × I) ℂ :=
  InstrumentEquality.choi (operators input outcome)

noncomputable def projection {I R : Type} [Fintype I] [Fintype R] (i : I) :
    Joint I R →L[ℂ] EuclideanSpace ℂ R :=
  LinearMap.toContinuousLinearMap {
    toFun := fun v => WithLp.toLp 2 (fun r => v (i,r))
    map_add' := by intros; ext; rfl
    map_smul' := by intros; ext; rfl }

noncomputable def inclusion {I R : Type} [Fintype I] [Fintype R] (i : I) :
    EuclideanSpace ℂ R →L[ℂ] Joint I R := by
  classical
  exact LinearMap.toContinuousLinearMap {
    toFun := fun v => WithLp.toLp 2 (fun p => if p.1 = i then v p.2 else 0)
    map_add' := by intros; ext p; by_cases h : p.1 = i <;> simp [h]
    map_smul' := by intros; ext p; by_cases h : p.1 = i <;> simp [h] }

/-- The exact matrix acts on the system and preserves every reference fiber.
This definition uses explicit Euclidean continuous linear maps. -/
noncomputable def liftLeft {I O : Type} [Fintype I] [Fintype O]
    (operator : Matrix O I ℂ) (R : Type) [Fintype R] :
    Joint I R →L[ℂ] Joint O R :=
  ∑ o, ∑ i, operator o i • ((inclusion o).comp (projection i))

/-- The adjoint of the complete unnormalized instrument, with every public
outcome tested by its own observable and every hidden history retained. -/
noncomputable def adjointWithReference {X Y H I O R : Type}
    [Fintype Y] [Fintype H] [Fintype I] [Fintype O] [Fintype R]
    (operators : Kraus X Y H I O) (observables : Observable Y O R) (input : X) :
    Joint I R →L[ℂ] Joint I R :=
  ∑ y, ∑ h, (liftLeft (operators input y h) R).adjoint ∘L
    observables y ∘L liftLeft (operators input y h) R

/-- All finite references and all joint observables are quantified. The
budget is an unsquared norm, and no reference-dimension factor is introduced.
Actual and ideal instruments may have different hidden-history types. -/
def CompleteAdjointBound {X Y H K I O : Type}
    [Fintype Y] [Fintype H] [Fintype K] [Fintype I] [Fintype O]
    (actual : Kraus X Y H I O) (ideal : Kraus X Y K I O) (epsilon : ℝ) : Prop :=
  0 ≤ epsilon ∧ ∀ (R : Type) [Fintype R] (observables : Observable Y O R) (input : X),
    ‖adjointWithReference actual observables input -
      adjointWithReference ideal observables input‖ ≤ epsilon * ‖observables‖

end Qleisli.Semantics.EngineeringInstrument
