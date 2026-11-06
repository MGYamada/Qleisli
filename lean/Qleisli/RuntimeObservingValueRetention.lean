import Qleisli.RuntimeNamedThreePackedInstrument
import Qleisli.HierarchicalSemantics
import Qleisli.Semantics.OrdinaryValue

/-! Every actual observing history retains each incoming ordinary SSA value.
The proof follows the same child recursion and ordered event fold.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeObservingValueRetention
open QleisliKernel.Semantics.Observation (Event ClassicalPhi)
open QleisliKernel.Semantics.Finite (Dependency)
open QleisliKernel.Semantics.OrdinaryValue (Extends append_extends)
open Qleisli.Semantics.ObservingAction (History merge step run)
open Qleisli.Semantics.OrdinaryValue (phiBindings)
open Qleisli.RuntimeNamedThreePackedInstrument (advance)
open Qleisli.HierarchicalSemantics (mapM_members)

private theorem merge_retains (choice : Bool) (phis : List ClassicalPhi) {before after : History}
    (merged : merge choice phis before = some after) : Extends before.values after.values := by
  change (do
    let added ← phiBindings choice phis before.values
    some {before with values := before.values ++ added}) = _ at merged
  cases read : phiBindings choice phis before.values with
  | none => simp [read] at merged
  | some added =>
    simp only [read,bind,Option.bind,Option.some.injEq] at merged
    rw [← merged]
    exact append_extends _ _

private theorem step_retains (dependencies : List Dependency) (recurse : List Event → History → Option (List History))
    (children : ∀ events before after, recurse events before = some after →
      ∀ result ∈ after, Extends before.values result.values)
    (event : Event) (before : History) {after : List History}
    (executed : step dependencies recurse event before = some after) :
    ∀ result ∈ after, Extends before.values result.values := by
  cases event with
  | pure raw =>
    simp only [step,Option.some.injEq] at executed
    subst after
    intro result member
    have same := List.mem_singleton.mp member
    subst result
    exact fun _ _ found => found
  | erase bits axes output =>
    simp only [step,Option.some.injEq] at executed
    subst after
    intro result member
    obtain ⟨outcome,_present,rfl⟩ := List.mem_map.mp member
    cases output with
    | none => exact fun _ _ found => found
    | some id => exact append_extends before.values [(id,outcome == 1)]
  | classical expression output =>
    cases evaluated : Qleisli.Semantics.RawInstrument.expression before.values expression with
    | none => simp [step,evaluated] at executed
    | some value =>
      simp only [step,evaluated,bind,Option.bind,Option.some.injEq] at executed
      subst after
      intro result member
      have same := List.mem_singleton.mp member
      subst result
      exact append_extends before.values [(output,value)]
  | branch condition left right phis =>
    cases selected : Qleisli.Semantics.RawInstrument.value before.values condition with
    | none => simp [step,selected] at executed
    | some choice =>
      cases ran : recurse (if choice then left else right) before with
      | none => simp [step,selected,ran] at executed
      | some arm =>
        have joined : arm.mapM (merge choice phis) = some after := by
          simpa only [step,selected,ran,bind,Option.bind] using executed
        intro result member
        obtain ⟨source,present,merged⟩ := mapM_members _ _ _ joined result member
        have keeps := children _ _ _ ran source present
        exact fun id bit found => merge_retains choice phis merged id bit (keeps id bit found)

private theorem advance_retains (dependencies : List Dependency) (recurse : List Event → History → Option (List History))
    (children : ∀ events before after, recurse events before = some after →
      ∀ result ∈ after, Extends before.values result.values)
    (seed : History) (event : Event) {before after : List History}
    (prior : ∀ initial ∈ before, Extends seed.values initial.values)
    (read : advance dependencies recurse before event = some after) :
    ∀ result ∈ after, Extends seed.values result.values := by
  unfold advance at read
  cases grouped : before.mapM (step dependencies recurse event) with
  | none => simp [grouped] at read
  | some groups =>
    simp only [grouped,bind,Option.bind,pure,Option.some.injEq] at read
    subst after
    intro result member
    obtain ⟨group,present,contains⟩ := List.mem_flatten.mp member
    obtain ⟨input,actual,ran⟩ := mapM_members _ _ _ grouped group present
    have old := prior input actual
    have next := step_retains dependencies recurse children event input ran result contains
    exact fun id bit found => next id bit (old id bit found)

private theorem fold_retains (dependencies : List Dependency) (recurse : List Event → History → Option (List History))
    (children : ∀ events before after, recurse events before = some after →
      ∀ result ∈ after, Extends before.values result.values)
    (seed : History) (events : List Event) {before after : List History}
    (prior : ∀ initial ∈ before, Extends seed.values initial.values)
    (read : events.foldlM (advance dependencies recurse) before = some after) :
    ∀ result ∈ after, Extends seed.values result.values := by
  induction events generalizing before with
  | nil =>
    have same : before = after := Option.some.inj read
    subst after
    exact prior
  | cons event rest ih =>
    rw [List.foldlM_cons] at read
    cases advanced : advance dependencies recurse before event with
    | none => simp [advanced] at read
    | some next =>
      have restRead : rest.foldlM (advance dependencies recurse) next = some after := by
        simpa only [advanced,bind,Option.bind] using read
      exact ih (advance_retains dependencies recurse children seed event prior advanced) restRead

/-- A successful original observing arm or root execution never shadows or
loses any of its incoming actual values. -/
theorem run_retains_values (dependencies : List Dependency) (fuel : Nat) (events : List Event)
    (before : History) {after : List History} (read : run dependencies fuel events before = some after) :
    ∀ result ∈ after, Extends before.values result.values := by
  induction fuel generalizing events before after with
  | zero => cases read
  | succ fuel ih =>
    change events.foldlM (advance dependencies (run dependencies fuel)) [before] = some after at read
    apply fold_retains dependencies (run dependencies fuel) (fun _ _ _ ran => ih _ _ ran) before events _ read
    intro initial member
    have same := List.mem_singleton.mp member
    subst initial
    exact fun _ _ found => found

#print axioms run_retains_values
end Qleisli.RuntimeObservingValueRetention
