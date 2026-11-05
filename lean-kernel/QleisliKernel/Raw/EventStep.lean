import QleisliKernel.Raw.EventActions

/-! One actual instrument step, with recursive computations kept opaque.
Both branch subtrees retain their actual history and phi routing.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Raw.EventTransport
open QleisliKernel QleisliKernel.Semantics.Finite QleisliKernel.Semantics.Exact
abbrev Recurse := List Semantics.Observation.Event → Raw.Instrument.History →
  Finite.WorkM (List Raw.Instrument.History)

def PureAgrees (left right : List Dependency) : Semantics.Observation.Event → Prop
  | .pure operation => ActionAgrees left right operation
  | _ => True

def BranchesAgree (first second : Recurse) : Semantics.Observation.Event → Prop
  | .branch _ zero one _ =>
    (∀ history, first zero history = second zero history) ∧
    (∀ history, first one history = second one history)
  | _ => True

theorem step_event {left right : List Dependency} (first second : Recurse)
    (event : Semantics.Observation.Event) (actions : PureAgrees left right event)
    (branches : BranchesAgree first second event) :
    Raw.Instrument.stepEvent left first event = Raw.Instrument.stepEvent right second event := by
  funext history
  cases event with
  | pure operation =>
    change ActionAgrees left right operation at actions
    have equal := protected_event (left := left) (right := right) (event := operation) actions
    simp only [Raw.Instrument.stepEvent,equal]
  | erase _ _ _ => rfl
  | classical _ _ => rfl
  | branch condition zero one phis =>
    change (∀ history, first zero history = second zero history) ∧
      (∀ history, first one history = second one history) at branches
    let recipe : (Bool → Finite.WorkM (List Raw.Instrument.History)) →
        Finite.WorkM (List Raw.Instrument.History) := fun recurse => do
      Finite.exactWork (Exact.charge 1)
      let choice ← Raw.Instrument.lookup history.values condition
      let next ← recurse choice
      next.mapM (Raw.Instrument.mergeClassical choice phis)
    change recipe (fun choice => first (if choice then zero else one) history) =
      recipe (fun choice => second (if choice then zero else one) history)
    apply congrArg recipe
    funext choice
    cases choice with
    | false => exact branches.2 history
    | true => exact branches.1 history

end QleisliKernel.Raw.EventTransport
