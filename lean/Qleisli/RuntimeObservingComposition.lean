import Qleisli.RuntimeNamedThreePackedInstrument

/-! The actual independent observing fold composes over ordered event lists.
Every intermediate history runs the same suffix, and its results keep their
relative order when flattened.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeObservingComposition
open QleisliKernel.Semantics.Finite (Dependency)
open QleisliKernel.Semantics.Observation (Event)
open Qleisli.Semantics.ObservingAction (History run)
open Qleisli.RuntimeNamedThreePackedInstrument (advance)

private theorem advance_append (dependencies : List Dependency)
    (recurse : List Event → History → Option (List History))
    (left right : List History) (event : Event) :
    advance dependencies recurse (left++right) event = (do
      let before ← advance dependencies recurse left event
      let after ← advance dependencies recurse right event
      return before++after) := by
  simp only [advance,List.mapM_append,bind_assoc,pure_bind,List.flatten_append]

private noncomputable def fold (dependencies : List Dependency)
    (recurse : List Event → History → Option (List History))
    (events : List Event) (histories : List History) : Option (List History) :=
  events.foldlM (advance dependencies recurse) histories

private theorem fold_empty (dependencies : List Dependency)
    (recurse : List Event → History → Option (List History)) (events : List Event) :
    fold dependencies recurse events [] = some [] := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
    change (advance dependencies recurse [] event >>= fold dependencies recurse rest) = some []
    exact ih

private theorem fold_append_histories (dependencies : List Dependency)
    (recurse : List Event → History → Option (List History))
    (events : List Event) (left right : List History) :
    fold dependencies recurse events (left++right) = (do
      let before ← fold dependencies recurse events left
      let after ← fold dependencies recurse events right
      return before++after) := by
  induction events generalizing left right with
  | nil => rfl
  | cons event rest ih =>
    simp only [fold,List.foldlM_cons,advance_append]
    cases first : advance dependencies recurse left event with
    | none => rfl
    | some before =>
      cases second : advance dependencies recurse right event with
      | none =>
        change none = (fold dependencies recurse rest before >>= fun _ => none)
        cases fold dependencies recurse rest before <;> rfl
      | some after => exact ih before after

noncomputable def runHistories (dependencies : List Dependency) (fuel : Nat)
    (events : List Event) (histories : List History) : Option (List History) := do
  let groups ← histories.mapM (run dependencies fuel events)
  return groups.flatten

theorem runHistories_singleton (dependencies : List Dependency) (fuel : Nat)
    (events : List Event) (history : History) :
    runHistories dependencies fuel events [history] = run dependencies fuel events history := by
  cases produced : run dependencies fuel events history <;> simp [runHistories,produced]

private theorem fold_groups (dependencies : List Dependency) (fuel : Nat)
    (events : List Event) (histories : List History) :
    fold dependencies (run dependencies fuel) events histories =
      runHistories dependencies (fuel+1) events histories := by
  unfold runHistories
  induction histories with
  | nil => exact fold_empty _ _ _
  | cons first rest ih =>
    change fold dependencies (run dependencies fuel) events ([first]++rest) = _
    rw [fold_append_histories,ih,List.mapM_cons]
    simp only [bind_assoc,pure_bind,List.flatten_cons]
    rfl

theorem runHistories_nil (dependencies : List Dependency) (fuel : Nat) (histories : List History) :
    runHistories dependencies (fuel+1) [] histories = some histories := by
  rw [← fold_groups]
  rfl

/-- The original run of two consecutive chunks equals the actual first
run followed by a suffix run for each of its histories, in order. -/
theorem runHistories_append (dependencies : List Dependency) (fuel : Nat)
    (earlier later : List Event) (initial : List History) :
    runHistories dependencies (fuel+1) (earlier++later) initial = (do
      let histories ← runHistories dependencies (fuel+1) earlier initial
      runHistories dependencies (fuel+1) later histories) := by
  simp only [← fold_groups,fold,List.foldlM_append]

#print axioms runHistories_append
end Qleisli.RuntimeObservingComposition
