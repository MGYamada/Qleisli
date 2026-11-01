import QleisliKernel.Raw.ObservationReader

/-! The production graph reference enumeration supplies the reader invariant.
Both branch subtrees and physical/logical computed bodies are accounted for.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Raw.ObservationAgreement
open QleisliKernel QleisliKernel.Semantics.Finite

def opReferences (recurse : List Op → List Nat) : Op → List Nat
  | .pure operation => (match operation with
      | .applyUnitary _ _ steps => steps
      | .certifiedCompute _ _ _ _ uses logical => uses ++ logical
      | _ => []).filterMap (fun (step : Step) => match step.action with
        | .contract _ index _ => some index | _ => none)
  | .branch _ zero one _ _ => recurse zero ++ recurse one
  | _ => []

theorem references_succ (fuel : Nat) (operations : List Op) :
    Semantics.ObservingFunction.references (fuel+1) operations =
      operations.flatMap (opReferences (Semantics.ObservingFunction.references fuel)) := rfl

theorem of_references (left right : List Dependency) (fuel : Nat) :
    ∀ operations, (∀ index, index ∈ Semantics.ObservingFunction.references fuel operations →
      left[index]? = right[index]?) → OpsAgree left right fuel operations := by
  induction fuel with
  | zero => intro operations same; exact True.intro
  | succ fuel ih =>
    intro operations same op member
    have localAgreement : ∀ index,
        index ∈ opReferences (Semantics.ObservingFunction.references fuel) op →
        left[index]? = right[index]? := by
      intro index present
      apply same index
      rw [references_succ]
      exact List.mem_flatMap.mpr ⟨op,member,present⟩
    cases op with
    | pure operation =>
      apply QleisliKernel.Raw.RawAgreement.operation_of_indices
      intro index present
      exact localAgreement index (by
        rw [references_succ] at present
        simpa only [List.flatMap_cons,List.flatMap_nil,List.append_nil] using present)
    | branch condition zero one quantum classical =>
      constructor
      · apply ih
        intro index present
        exact localAgreement index (List.mem_append.mpr (Or.inl present))
      · apply ih
        intro index present
        exact localAgreement index (List.mem_append.mpr (Or.inr present))
    | measure _ _ => exact True.intro
    | reset _ _ _ => exact True.intro
    | discard _ => exact True.intro
    | constant _ _ => exact True.intro
    | not _ _ => exact True.intro
    | xor _ _ _ => exact True.intro
    | and _ _ _ => exact True.intro

end QleisliKernel.Raw.ObservationAgreement
