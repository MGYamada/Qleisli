import Qleisli.ObservingActionLinear
import Qleisli.RuntimeCallHistoryEntry

/-! The exact child input encoding supplies the weights of the literal
child run. The resulting logical spectator components are shared by every
physical spectator slice.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeCallHistory
open QleisliKernel QleisliKernel.Qirf
open RuntimeOwnerMap (Map)
open RuntimeForestCode (embed sparseEntry)
open Qleisli.RuntimeSemanticForest (Frame action product)
open Qleisli.RuntimeNamedHeadCoefficients (fibre)
open Qleisli.RuntimeForestRegroup (sourceDimension)
open Qleisli.MixedRadix (recode)
open Qleisli.Semantics.Exact (scalar)
open Qleisli.Semantics.RawAction (combination)
open Qleisli.Semantics.ObservingAction (History run WeightedHistory run_weighted)

private theorem encode_combination {Index Reference : Type} {bindings : Map}
    (frame : Frame bindings) (physical : List Nat) (indices : List Index)
    (weight : Index → ℂ) (values : Index → Nat → Reference → ℂ) (row : Nat) (reference : Reference) :
    action frame physical (fun digit ref => combination indices weight (fun index => values index digit ref))
      row reference =
    combination indices weight (fun index => action frame physical (values index) row reference) := by
  unfold action combination
  simp_rw [← List.sum_map_mul_left]
  rw [Qleisli.Exact.sum_swap]
  apply Qleisli.Exact.sum_map_congr
  intro index _
  rw [← List.sum_map_mul_right]
  apply Qleisli.Exact.sum_map_congr
  intro digit _
  exact (mul_assoc _ _ _).symm

noncomputable def spectatorWeight (spectators : Map) (physical logical : Nat) : ℂ :=
  scalar (sparseEntry (.ofLayout (product spectators)) physical logical)

/-- The logical spectator ordinal fixes only the untouched owner labels.
The child and external reference amplitudes can still be correlated. -/
noncomputable def componentInput {bindings : Map}
    (frame : Frame bindings) (physical : List Nat) (incoming selected spectators : Map)
    (joint : Nat → Nat → ℂ) (actual : History) (logical : Nat) : History :=
  let component := fun digit ref => joint
    (recode (selected++spectators) incoming (sourceDimension incoming)
      (digit+(product selected).labels.length*logical)) ref
  {actual with operator := action frame physical component}

theorem child_input_weighted {bindings : Map} (frame : Frame bindings) (physical : List Nat)
    (incoming selected spectators : Map) (joint : Nat → Nat → ℂ) (actual : History) (high : Nat) :
    WeightedHistory (List.range (product spectators).labels.length)
      (fun _ => spectatorWeight spectators high)
      (inputHistory frame physical incoming selected spectators joint actual high)
      (componentInput frame physical incoming selected spectators joint actual) := by
  refine ⟨fun _ => rfl,fun _ => rfl,?_⟩
  intro row col
  have exactInput : coordinateFibre incoming selected spectators high joint =
      fun digit ref => combination (List.range (product spectators).labels.length) (spectatorWeight spectators high)
        (fun index => joint (recode (selected++spectators) incoming (sourceDimension incoming)
          (digit+(product selected).labels.length*index)) ref) := by
    funext digit ref
    unfold coordinateFibre fibre combination spectatorWeight
    apply Qleisli.Exact.sum_map_congr
    intro _ _
    exact mul_comm _ _
  change action frame physical (coordinateFibre incoming selected spectators high joint) row col = _
  rw [exactInput]
  exact encode_combination frame physical _ _ _ row col

private theorem families_unique {α : Type} {first second : List (Nat → α)}
    (same : ∀ index, first.map (fun result => result index) = second.map (fun result => result index)) :
    first = second := by
  induction first generalizing second with
  | nil =>
    cases second with
    | nil => rfl
    | cons _ _ => cases same 0
  | cons first rest ih =>
    cases second with
    | nil => cases same 0
    | cons second tail =>
      have head : first = second := funext fun index => (List.cons.inj (same index)).1
      have later : rest = tail := ih (fun index => (List.cons.inj (same index)).2)
      rw [head,later]

/-- The same ordered logical component family reconstructs every physical
child result list. Its actual execution is independent of the slice weights. -/
theorem CheckedCallRun.weighted_children
    {dependencies program block start count inputs ordinary effect}
    {scope : @RuntimeCallScope.Checked dependencies program block start count inputs ordinary effect}
    {bindings} (frame : Frame bindings) (incoming selected spectators : Map)
    (joint : Nat → Nat → ℂ) (actual : History) {parentEvents childEvents parents children}
    (checked : CheckedCallRun scope (spectators.map (·.port)) actual
      (inputHistory frame scope.prepared.block.entry.quantum.frame incoming selected spectators joint actual)
      parentEvents childEvents parents children) :
    ∃ family : List (Nat → History),
      (∀ logical, run dependencies scope.prepared.block.fuel childEvents
        (componentInput frame scope.prepared.block.entry.quantum.frame incoming selected spectators joint actual logical) =
        some (family.map (fun result => result logical))) ∧
      ∀ high, List.Forall₂
        (WeightedHistory (List.range (product spectators).labels.length) (fun _ => spectatorWeight spectators high))
        (children.map (fun result => result high)) family := by
  have law (high : Nat) := run_weighted _ _ dependencies scope.prepared.block.fuel childEvents _ _
    (child_input_weighted frame scope.prepared.block.entry.quantum.frame incoming selected spectators joint actual high)
    (checked.paired.childRun high)
  obtain ⟨family,reads,_⟩ := law 0
  refine ⟨family,reads,?_⟩
  intro high
  obtain ⟨other,otherReads,paired⟩ := law high
  have same : other = family := families_unique (fun logical =>
    Option.some.inj ((otherReads logical).symm.trans (reads logical)))
  exact same ▸ paired

#print axioms child_input_weighted
#print axioms CheckedCallRun.weighted_children
end Qleisli.RuntimeCallHistory
