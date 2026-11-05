import QleisliKernel.Raw.EventStep

/-! Structural induction over the actual depth-bounded instrument interpreter.
All histories, exact operators, errors and remaining work are preserved.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Raw.EventTransport
open QleisliKernel QleisliKernel.Semantics.Finite
open QleisliKernel.Raw.DependencyTransport

def layer (dependencies : List Dependency) (recurse : Recurse)
    (events : List Semantics.Observation.Event) (initial : Raw.Instrument.History) :
    Finite.WorkM (List Raw.Instrument.History) :=
  events.foldlM (fun histories event => do
    let next ← histories.mapM (Raw.Instrument.stepEvent dependencies recurse event)
    return next.flatten) [initial]

theorem run_zero (dependencies : List Dependency)
    (events : List Semantics.Observation.Event) (initial : Raw.Instrument.History) :
    Raw.Instrument.runEvents dependencies 0 events initial = throw Finite.Error.limit := rfl

theorem run_succ (dependencies : List Dependency) (fuel : Nat)
    (events : List Semantics.Observation.Event) (initial : Raw.Instrument.History) :
    Raw.Instrument.runEvents dependencies (fuel+1) events initial =
      layer dependencies (Raw.Instrument.runEvents dependencies fuel) events initial := rfl

theorem layer_same (left right : List Dependency) (first second : Recurse)
    (events : List Semantics.Observation.Event)
    (same : ∀ event, event ∈ events →
      PureAgrees left right event ∧ BranchesAgree first second event)
    (initial : Raw.Instrument.History) :
    layer left first events initial = layer right second events initial := by
  unfold layer
  apply fold_same
  intro event member histories
  rw [step_event (left := left) (right := right) first second event
    (same event member).1 (same event member).2]

def EventsAgree (left right : List Dependency) : Nat → List Semantics.Observation.Event → Prop :=
  Nat.rec (fun _ => True) (fun _ recurse events => ∀ event, event ∈ events → match event with
    | .pure operation => ActionAgrees left right operation
    | .branch _ zero one _ => recurse zero ∧ recurse one
    | _ => True)

/-- Entire WorkM computations agree, including all hidden outcomes, values,
exact phases, errors and remaining work. Both original branch subtrees are
premises; no observed input or producer-selected history supplies them. -/
theorem run_events (left right : List Dependency) (fuel : Nat) :
    ∀ events, EventsAgree left right fuel events → ∀ initial,
      Raw.Instrument.runEvents left fuel events initial =
        Raw.Instrument.runEvents right fuel events initial := by
  induction fuel with
  | zero => intro events same initial; rfl
  | succ fuel ih =>
    intro events same initial
    rw [run_succ left fuel events initial,run_succ right fuel events initial]
    apply layer_same
    intro event member
    have localAgreement := same event member
    cases event with
    | pure operation => exact ⟨localAgreement,True.intro⟩
    | erase _ _ _ => exact ⟨True.intro,True.intro⟩
    | classical _ _ => exact ⟨True.intro,True.intro⟩
    | branch condition zero one phis =>
      exact ⟨True.intro,⟨fun history => ih zero localAgreement.1 history,
        fun history => ih one localAgreement.2 history⟩⟩

end QleisliKernel.Raw.EventTransport
