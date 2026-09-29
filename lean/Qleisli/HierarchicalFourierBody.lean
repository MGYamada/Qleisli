import Qleisli.HierarchicalFourierBase
import Qleisli.HierarchicalHadamard
import Qleisli.HierarchicalFourierControl
import QleisliKernel.Hierarchical.FourierBody

/-! Complete actual recursive Fourier body under only bound finite H equations.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
Recursive-child and controlled-gradient matrices are derived, never assumed.
Final outer reversal/request binding and native/finite-reader correspondence
are separate obligations; this theorem does not issue production evidence. -/

namespace Qleisli.HierarchicalFourierBody
open QleisliKernel.Hierarchical
open Artifact HierarchicalOperators HierarchicalFourier
open scoped BigOperators Matrix

def IsBody (width : Nat) (actual : Operator) : Prop :=
  actual.inputWidth = width ∧ actual.outputWidth = width ∧
    matrixAt width width actual = reversedFourier width

theorem matched_evaluates (leaves : HierarchicalFiniteEvaluation.Leaves Operator)
    (artifact : Artifact) (precision width index : Nat) (requests : List Hadamard.Request)
    (matched : FourierBody.Matches artifact precision width index requests)
    (equations : ∀ request ∈ requests, HierarchicalHadamard.Equation leaves request) :
    ∃ fuel actual, HierarchicalFiniteEvaluation.physical algebra leaves artifact fuel index = some actual ∧
      IsBody width actual := by
  revert equations
  induction matched with
  | one index remaining base h bc hc =>
    intro equations
    obtain ⟨hValue,he,hModel⟩ := HierarchicalHadamard.inspect_evaluates leaves artifact
      base.step.hIndex (remaining-base.visits) h hc (equations h.request (by simp))
    obtain ⟨actual,evaluated,ai,ao,matrix⟩ := HierarchicalFourierBase.inspect_evaluates leaves artifact
      index remaining 2 base bc hValue he hModel.1 hModel.2.1 hModel.2.2
    exact ⟨5,actual,evaluated,ai,ao,matrix⟩
  | step n index remaining stage h control requests sc hc cc _ ih =>
    intro equations
    obtain ⟨hValue,he,hModel⟩ := HierarchicalHadamard.inspect_evaluates leaves artifact
      stage.step.hIndex (remaining-stage.visits) h hc (equations h.request (by simp))
    obtain ⟨gradientFuel,gradient,ge,diagonal⟩ := HierarchicalFourierControl.inspect_evaluates leaves artifact
      _ (n+1) stage.step.gradientIndex (remaining-stage.visits-h.visits) control cc
    obtain ⟨childFuel,child,ce,childModel⟩ := ih (fun r member => equations r (by simp [member]))
    let fuel := 2+gradientFuel+childFuel
    have hMore := HierarchicalFiniteEvaluation.evaluate_more algebra
      (HierarchicalFiniteEvaluation.definition leaves artifact) 2 stage.step.hIndex hValue he fuel (by omega)
    have gMore := HierarchicalFiniteEvaluation.evaluate_more algebra
      (HierarchicalFiniteEvaluation.definition leaves artifact) gradientFuel stage.step.gradientIndex gradient ge fuel (by omega)
    have cMore := HierarchicalFiniteEvaluation.evaluate_more algebra
      (HierarchicalFiniteEvaluation.definition leaves artifact) childFuel stage.step.childIndex child ce fuel (by omega)
    obtain ⟨actual,evaluated,ai,ao,matrix⟩ := HierarchicalFourierStage.inspect_evaluates leaves artifact
      (n+1) index remaining fuel stage sc hValue gradient child hMore gMore cMore
      hModel.1 hModel.2.1 hModel.2.2 diagonal childModel.2.2
    exact ⟨fuel+3,actual,evaluated,ai,ao,matrix⟩

theorem inspect_evaluates (leaves : HierarchicalFiniteEvaluation.Leaves Operator)
    (artifact : Artifact) (precision width index remaining : Nat) (pending : FourierBody.Pending)
    (accepted : FourierBody.inspect artifact precision width index remaining = .ok pending)
    (equations : ∀ request ∈ pending.requests, HierarchicalHadamard.Equation leaves request) :
    ∃ fuel actual, HierarchicalFiniteEvaluation.physical algebra leaves artifact fuel index = some actual ∧
      IsBody width actual := by
  obtain ⟨_,_,_,_,_,matched⟩ := FourierBody.inspect_sound artifact precision width index remaining pending accepted
  exact matched_evaluates leaves artifact precision width index pending.requests matched equations

/-- Any successful evaluation of these exact bodies has the proved coefficients,
including on arbitrary superpositions entangled with reference systems. -/
theorem inspect_joint_amplitude (leaves : HierarchicalFiniteEvaluation.Leaves Operator)
    (artifact : Artifact) (precision width index remaining fuel : Nat) (pending : FourierBody.Pending)
    (accepted : FourierBody.inspect artifact precision width index remaining = .ok pending)
    (equations : ∀ request ∈ pending.requests, HierarchicalHadamard.Equation leaves request)
    (actual : Operator)
    (evaluated : HierarchicalFiniteEvaluation.physical algebra leaves artifact fuel index = some actual)
    {R : Type} (joint : (Fin width → Bool) → R → ℂ) (output : Fin width → Bool) (reference : R) :
    (∑ input, matrixAt width width actual output input * joint input reference) =
      ∑ input, reversedFourier width output input * joint input reference := by
  obtain ⟨more,value,computed,model⟩ := inspect_evaluates leaves artifact precision width index remaining pending accepted equations
  have same := HierarchicalFiniteEvaluation.evaluate_unique algebra
    (HierarchicalFiniteEvaluation.definition leaves artifact) more fuel index value actual computed evaluated
  subst value
  rw [model.2.2]

end Qleisli.HierarchicalFourierBody
