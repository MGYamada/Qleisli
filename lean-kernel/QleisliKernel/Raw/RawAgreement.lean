import QleisliKernel.Raw.EventTransport

/-! Original-operation dependency references determine agreement of their
localized actions. Axis localization retains the original dependency index.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Raw.RawAgreement
open QleisliKernel QleisliKernel.Semantics.Finite
open QleisliKernel.Raw.DependencyTransport QleisliKernel.Raw.EventTransport

theorem steps_of_indices {left right : List Dependency} (steps : List Step)
    (same : ∀ index, index ∈ steps.filterMap (fun step => match step.action with
      | .contract _ index _ => some index | _ => none) → left[index]? = right[index]?) :
    StepsAgree left right steps := by
  intro step member axes index adjoint action
  exact same index (List.mem_filterMap.mpr ⟨step,member,by simp [action]⟩)

theorem localize {left right step} (same : StepAgrees left right step) (indices : List Nat) :
    StepAgrees left right (Semantics.RawTrace.localize indices step) := by
  intro axes index adjoint matched
  cases action : step.action with
  | hadamard _ => simp [Semantics.RawTrace.localize,action] at matched
  | monomial _ _ _ => simp [Semantics.RawTrace.localize,action] at matched
  | contract targets dependency inverse =>
    have fields : targets.map (fun index => indices[index]?.getD 0) = axes ∧
        dependency = index ∧ inverse = adjoint := by
      simpa [Semantics.RawTrace.localize,action] using matched
    rcases fields with ⟨_,rfl,rfl⟩
    exact same targets dependency inverse action

theorem localize_steps {left right : List Dependency} (steps : List Step)
    (same : StepsAgree left right steps) (indices : List Nat) :
    StepsAgree left right (steps.map (Semantics.RawTrace.localize indices)) := by
  intro step member
  obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
  exact localize (same original present) indices

theorem with_controls {left right step} (same : StepAgrees left right step)
    (controls : List Control) : StepAgrees left right {step with controls} := same

theorem gate (left right : List Dependency) (gate : Semantics.Raw.Gate) (axis : Nat) :
    StepAgrees left right (Semantics.RawTrace.gate gate axis) := by
  cases gate <;> simp [StepAgrees,Semantics.RawTrace.gate]

theorem unitary (left right : List Dependency) (operation : Semantics.Raw.UnitaryStep) :
    StepAgrees left right (Semantics.RawTrace.unitary operation) := by
  cases operation with
  | gate value axis => exact gate left right value axis
  | cnot control target =>
    exact with_controls (gate left right .x target) _
  | toffoli first second target =>
    exact with_controls (gate left right .x target) _
  | phase phase => simp [StepAgrees,Semantics.RawTrace.unitary]

def OpAgrees (left right : List Dependency) : Semantics.Raw.Op → Prop
  | .applyUnitary _ _ steps => StepsAgree left right steps
  | .certifiedCompute _ _ _ _ uses logical => StepsAgree left right uses ∧ StepsAgree left right logical
  | _ => True

/-- Use the production graph's actual reference enumeration. Both physical and
logical computed bodies contribute; unused vector entries need not agree. -/
theorem operation_of_indices (left right : List Dependency) (operation : Semantics.Raw.Op)
    (same : ∀ index, index ∈ Semantics.ObservingFunction.references 1 [.pure operation] →
      left[index]? = right[index]?) : OpAgrees left right operation := by
  cases operation <;> try exact True.intro
  case applyUnitary input output steps =>
    apply steps_of_indices
    intro index member
    exact same index (by
      change index ∈ steps.filterMap (fun step => match step.action with
        | .contract _ index _ => some index | _ => none) ++ []
      simpa only [List.append_nil] using member)
  case certifiedCompute input output ancilla table uses logical =>
    have whole : StepsAgree left right (uses ++ logical) := by
      apply steps_of_indices
      intro index member
      exact same index (by
        change index ∈ (uses ++ logical).filterMap (fun step => match step.action with
          | .contract _ index _ => some index | _ => none) ++ []
        simpa only [List.append_nil] using member)
    exact ⟨fun step member => whole step (List.mem_append.mpr (Or.inl member)),
      fun step member => whole step (List.mem_append.mpr (Or.inr member))⟩

end QleisliKernel.Raw.RawAgreement
