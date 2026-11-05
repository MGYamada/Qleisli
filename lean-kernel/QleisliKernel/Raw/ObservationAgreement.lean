import QleisliKernel.Raw.RawTraceAgreement

/-! Structural invariants for the actual observing reader. Original reference
agreement and both original branch subtrees remain explicit premises.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Raw.ObservationAgreement
open QleisliKernel QleisliKernel.Semantics.Finite
open QleisliKernel.Raw.DependencyTransport QleisliKernel.Raw.EventTransport QleisliKernel.Raw.RawAgreement
abbrev Interface := Semantics.RawTrace.Interface
abbrev Event := Semantics.Observation.Event
abbrev Op := Semantics.Observation.Op
abbrev Result := Interface × List Event
abbrev Reader := Interface → List Op → Option Result

theorem events_nil (left right : List Dependency) (fuel : Nat) :
    EventsAgree left right fuel [] := by
  cases fuel with
  | zero => exact True.intro
  | succ _ => intro event member; cases member

theorem events_append {left right : List Dependency} (fuel : Nat) (first second : List Event)
    (a : EventsAgree left right fuel first) (b : EventsAgree left right fuel second) :
    EventsAgree left right fuel (first ++ second) := by
  cases fuel with
  | zero => exact True.intro
  | succ _ =>
    intro event member
    rcases List.mem_append.mp member with firstMember | secondMember
    · exact a event firstMember
    · exact b event secondMember

theorem pure_events {left right : List Dependency} (fuel : Nat) (events : List Semantics.Raw.Event)
    (same : ∀ event, event ∈ events → ActionAgrees left right event) :
    EventsAgree left right (fuel+1) (events.map Semantics.Observation.Event.pure) := by
  intro event member
  obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
  exact same original present

theorem reorder (left right : List Dependency) (fuel bits : Nat) (axes : List Nat) :
    EventsAgree left right fuel [.pure (.reorder bits axes)] := by
  cases fuel with
  | zero => exact True.intro
  | succ _ =>
    intro event member
    have equal := List.mem_singleton.mp member
    subst event
    exact True.intro

def ReadAgrees (left right : List Dependency) (fuel : Nat) (result : Option Result) : Prop :=
  ∀ actual, result = some actual → EventsAgree left right fuel actual.2

theorem returned {left right : List Dependency} (fuel : Nat) (state : Interface) (events : List Event)
    (same : EventsAgree left right fuel events) :
    ReadAgrees left right fuel (some (state,events)) := by
  intro actual original
  have equal := Option.some.inj original
  subst actual
  exact same

theorem bind_agrees {left right : List Dependency} {α : Type} (fuel : Nat)
    (input : Option α) (next : α → Option Result)
    (same : ∀ actual, ReadAgrees left right fuel (next actual)) :
    ReadAgrees left right fuel (input.bind next) := by
  cases input with
  | none => intro actual impossible; cases impossible
  | some actual => exact same actual

/-- Generic Option fold induction, with no matrix evaluation or fixed case list. -/
theorem fold_property {α β : Type} (items : List α) (next : β → α → Option β) (property : β → Prop)
    (preserves : ∀ item, item ∈ items → ∀ before, property before → ∀ after,
      next before item = some after → property after)
    (initial : β) (held : property initial) :
    ∀ final, items.foldlM next initial = some final → property final := by
  induction items generalizing initial with
  | nil =>
    intro final same
    have equal : initial = final := Option.some.inj same
    subst final
    exact held
  | cons item rest ih =>
    intro final same
    change (next initial item >>= fun after => rest.foldlM next after) = some final at same
    obtain ⟨after,first,remaining⟩ := Option.bind_eq_some_iff.mp same
    exact ih (fun item member => preserves item (List.mem_cons_of_mem _ member)) after
      (preserves item (by simp) initial held after first) final remaining

def OpsAgree (left right : List Dependency) : Nat → List Op → Prop :=
  Nat.rec (fun _ => True) (fun _ recurse ops => ∀ op, op ∈ ops → match op with
    | .pure original => OpAgrees left right original
    | .branch _ zero one _ _ => recurse zero ∧ recurse one
    | _ => True)

end QleisliKernel.Raw.ObservationAgreement
