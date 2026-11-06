import Qleisli.RuntimeNamedThreePackedInstrument
import Qleisli.RuntimeObservingWrites
import Qleisli.HierarchicalSemantics
import Qleisli.Semantics.OrdinaryValue

/-! Every actual observing history retains each incoming ordinary SSA value
and adds only identities written by the trace. Both laws follow the same
child recursion and ordered event fold.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeObservingValueRetention
open QleisliKernel.Semantics.Observation (Event ClassicalPhi)
open QleisliKernel.Semantics.Finite (Dependency)
open QleisliKernel.Semantics.OrdinaryValue (Extends append_extends)
open Qleisli.Semantics.ObservingAction (History merge step run)
open Qleisli.Semantics.OrdinaryValue (phiBindings)
open Qleisli.RuntimeNamedThreePackedInstrument (advance)
open Qleisli.HierarchicalSemantics (mapM_members)
open Qleisli.RuntimeObservingWrites (WritesId WritesWithin)
open Qleisli.RuntimeObservingPrefix (Issued verify_reference_with_writes)

def Supports (allowed : Nat → Prop) (history : History) : Prop :=
  ∀ ⦃id⦄, id ∈ history.values.map Prod.fst → allowed id

private theorem append_support {allowed : Nat → Prop} {before : History} (extra : List (Nat × Bool))
    (supported : Supports allowed before)
    (writes : ∀ ⦃id⦄, id ∈ extra.map Prod.fst → allowed id) :
    Supports allowed {before with values := before.values ++ extra} := by
  intro id member
  change id ∈ (before.values++extra).map Prod.fst at member
  rw [List.map_append] at member
  rcases List.mem_append.mp member with old | new
  · exact supported old
  · exact writes new

private theorem merge_values (choice : Bool) (phis : List ClassicalPhi) {before after : History}
    {allowed : Nat → Prop} (supported : Supports allowed before)
    (writes : ∀ phi ∈ phis, allowed phi.output)
    (merged : merge choice phis before = some after) :
    Extends before.values after.values ∧ Supports allowed after := by
  change (do
    let added ← phiBindings choice phis before.values
    some {before with values := before.values ++ added}) = _ at merged
  cases read : phiBindings choice phis before.values with
  | none => simp [read] at merged
  | some added =>
    simp only [read,bind,Option.bind,Option.some.injEq] at merged
    rw [← merged]
    refine ⟨append_extends _ _,append_support added supported ?_⟩
    intro id member
    obtain ⟨binding,inside,rfl⟩ := List.mem_map.mp member
    unfold phiBindings at read
    obtain ⟨phi,present,evaluated⟩ := mapM_members _ _ _ read binding inside
    cases value : Qleisli.Semantics.RawInstrument.value before.values (if choice then phi.thenId else phi.elseId) with
    | none => simp [value] at evaluated
    | some bit =>
      have actual : (phi.output,bit) = binding := by simpa [value] using evaluated
      subst binding
      exact writes phi present

private theorem step_values (dependencies : List Dependency) (recurse : List Event → History → Option (List History))
    (allowed : Nat → Prop)
    (children : ∀ events before after, WritesWithin events allowed → Supports allowed before →
      recurse events before = some after →
      ∀ result ∈ after, Extends before.values result.values ∧ Supports allowed result)
    (event : Event) (before : History) {after : List History}
    (supported : Supports allowed before) (writes : ∀ ⦃id⦄, WritesId event id → allowed id)
    (executed : step dependencies recurse event before = some after) :
    ∀ result ∈ after, Extends before.values result.values ∧ Supports allowed result := by
  cases event with
  | pure raw =>
    simp only [step,Option.some.injEq] at executed
    subst after
    intro result member
    have same := List.mem_singleton.mp member
    subst result
    exact ⟨fun _ _ found => found,supported⟩
  | erase bits axes output =>
    simp only [step,Option.some.injEq] at executed
    subst after
    intro result member
    obtain ⟨outcome,_present,rfl⟩ := List.mem_map.mp member
    cases output with
    | none => exact ⟨fun _ _ found => found,supported⟩
    | some output =>
      refine ⟨append_extends _ _,append_support [(output,outcome == 1)] supported ?_⟩
      intro id written
      have same : id = output := List.mem_singleton.mp written
      subst id
      exact writes (.measure bits axes output)
  | classical expression output =>
    cases evaluated : Qleisli.Semantics.RawInstrument.expression before.values expression with
    | none => simp [step,evaluated] at executed
    | some value =>
      simp only [step,evaluated,bind,Option.bind,Option.some.injEq] at executed
      subst after
      intro result member
      have same := List.mem_singleton.mp member
      subst result
      refine ⟨append_extends _ _,append_support [(output,value)] supported ?_⟩
      intro id written
      have same : id = output := List.mem_singleton.mp written
      subst id
      exact writes (.classical expression output)
  | branch condition left right phis =>
    cases selected : Qleisli.Semantics.RawInstrument.value before.values condition with
    | none => simp [step,selected] at executed
    | some choice =>
      cases ran : recurse (if choice then left else right) before with
      | none => simp [step,selected,ran] at executed
      | some arm =>
        have joined : arm.mapM (merge choice phis) = some after := by
          simpa only [step,selected,ran,bind,Option.bind] using executed
        have armWrites : WritesWithin (if choice then left else right) allowed := by
          intro event member id emitted
          cases choice
          · exact writes (.elseArm member emitted)
          · exact writes (.thenArm member emitted)
        intro result member
        obtain ⟨source,present,merged⟩ := mapM_members _ _ _ joined result member
        obtain ⟨keeps,sourceSupported⟩ := children _ _ _ armWrites supported ran source present
        obtain ⟨joinedKeeps,resultSupported⟩ := merge_values choice phis sourceSupported
          (fun _ member => writes (.phi member)) merged
        exact ⟨fun id bit found => joinedKeeps id bit (keeps id bit found),resultSupported⟩

private theorem advance_values (dependencies : List Dependency) (recurse : List Event → History → Option (List History))
    (allowed : Nat → Prop)
    (children : ∀ events before after, WritesWithin events allowed → Supports allowed before →
      recurse events before = some after →
      ∀ result ∈ after, Extends before.values result.values ∧ Supports allowed result)
    (seed : History) (event : Event) {before after : List History}
    (prior : ∀ initial ∈ before, Extends seed.values initial.values ∧ Supports allowed initial)
    (writes : ∀ ⦃id⦄, WritesId event id → allowed id)
    (read : advance dependencies recurse before event = some after) :
    ∀ result ∈ after, Extends seed.values result.values ∧ Supports allowed result := by
  unfold advance at read
  cases grouped : before.mapM (step dependencies recurse event) with
  | none => simp [grouped] at read
  | some groups =>
    simp only [grouped,bind,Option.bind,pure,Option.some.injEq] at read
    subst after
    intro result member
    obtain ⟨group,present,contains⟩ := List.mem_flatten.mp member
    obtain ⟨input,actual,ran⟩ := mapM_members _ _ _ grouped group present
    obtain ⟨old,supported⟩ := prior input actual
    obtain ⟨next,final⟩ := step_values dependencies recurse allowed children event input supported writes ran result contains
    exact ⟨fun id bit found => next id bit (old id bit found),final⟩

private theorem fold_values (dependencies : List Dependency) (recurse : List Event → History → Option (List History))
    (allowed : Nat → Prop)
    (children : ∀ events before after, WritesWithin events allowed → Supports allowed before →
      recurse events before = some after →
      ∀ result ∈ after, Extends before.values result.values ∧ Supports allowed result)
    (seed : History) (events : List Event) {before after : List History}
    (prior : ∀ initial ∈ before, Extends seed.values initial.values ∧ Supports allowed initial)
    (writes : WritesWithin events allowed)
    (read : events.foldlM (advance dependencies recurse) before = some after) :
    ∀ result ∈ after, Extends seed.values result.values ∧ Supports allowed result := by
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
      have headWrites : ∀ ⦃id⦄, WritesId event id → allowed id := writes List.mem_cons_self
      have tailWrites : WritesWithin rest allowed := by
        intro event member id emitted
        exact writes (List.mem_cons_of_mem _ member) emitted
      exact ih (advance_values dependencies recurse allowed children seed event prior headWrites advanced)
        tailWrites restRead

/-- Every successful literal history retains its incoming values. Its actual
classical IDs stay within any set that covers the input and trace writes. -/
theorem run_values (dependencies : List Dependency) (fuel : Nat) (events : List Event)
    (before : History) {after : List History} (allowed : Nat → Prop)
    (writes : WritesWithin events allowed) (supported : Supports allowed before)
    (read : run dependencies fuel events before = some after) :
    ∀ result ∈ after, Extends before.values result.values ∧ Supports allowed result := by
  induction fuel generalizing events before after with
  | zero => cases read
  | succ fuel ih =>
    change events.foldlM (advance dependencies (run dependencies fuel)) [before] = some after at read
    apply fold_values dependencies (run dependencies fuel) allowed
      (fun _ _ _ writes supported ran => ih _ _ writes supported ran) before events _ writes read
    intro initial member
    have same := List.mem_singleton.mp member
    subst initial
    exact ⟨fun _ _ found => found,supported⟩

/-- A successful original observing arm or root execution never shadows or
loses any of its incoming actual values. -/
theorem run_retains_values (dependencies : List Dependency) (fuel : Nat) (events : List Event)
    (before : History) {after : List History} (read : run dependencies fuel events before = some after) :
    ∀ result ∈ after, Extends before.values result.values := by
  intro result member
  exact (run_values dependencies fuel events before (fun _ => True)
    (by intro event member id emitted; exact True.intro)
    (by intro id member; exact True.intro) read result member).1

/-- The actual original program starts with its own classical inputs and
returns histories whose IDs all belong to the successful native check. -/
theorem checked_program_values (dependencies : List Dependency) (program : QleisliKernel.Semantics.Observation.Program)
    (checked : QleisliKernel.Raw.Observation.Checked) (work left : Nat)
    (verified : (QleisliKernel.Raw.Observation.verify dependencies program).run work = (.ok checked,left))
    (classical : List Bool) {after : List History}
    (read : Qleisli.Semantics.ObservingAction.program dependencies program classical = some after) :
    ∀ result ∈ after, Extends (program.classicalInputs.zip classical) result.values ∧
      Supports (Issued checked.state) result := by
  obtain ⟨inputs,writes⟩ := verify_reference_with_writes dependencies program checked work left verified
  have original := (QleisliKernel.Raw.Observation.verify_postcondition _ _ _ _ _ verified).reader
  let before := Qleisli.Semantics.ObservingAction.initial (program.classicalInputs.zip classical)
  have supported : Supports (Issued checked.state) before := by
    intro id member
    obtain ⟨pair,present,rfl⟩ := List.mem_map.mp member
    exact inputs _ (List.of_mem_zip present).1
  simp only [Qleisli.Semantics.ObservingAction.program,original,bind,Option.bind] at read
  exact run_values dependencies 65 checked.prepared.events before _ writes supported read

#print axioms run_values
#print axioms run_retains_values
#print axioms checked_program_values
end Qleisli.RuntimeObservingValueRetention
