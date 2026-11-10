import Qleisli.ObservingActionLinear
import Qleisli.RuntimeCallHistoryReturn

/-! The exact child input encoding supplies the weights of the literal
child run. The resulting logical spectator components are shared by every
physical spectator slice.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeCallHistory
open QleisliKernel QleisliKernel.Qirf
open RuntimeOwnerMap (Map)
open RuntimeForestCode (embed sparseEntry)
open Qleisli.RuntimeSemanticForest (Frame action product)
open Qleisli.RuntimeStructuralHistory (Represents)
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
noncomputable def componentJoint (incoming selected spectators : Map) (joint : Nat → Nat → ℂ)
    (logical digit reference : Nat) : ℂ :=
  joint (recode (selected++spectators) incoming (sourceDimension incoming)
    (digit+(product selected).labels.length*logical)) reference

noncomputable def componentInput {bindings : Map}
    (frame : Frame bindings) (physical : List Nat) (incoming selected spectators : Map)
    (joint : Nat → Nat → ℂ) (actual : History) (logical : Nat) : History :=
  {actual with operator := action frame physical (componentJoint incoming selected spectators joint logical)}

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
        (fun index => componentJoint incoming selected spectators joint index digit ref) := by
    funext digit ref
    unfold coordinateFibre fibre combination spectatorWeight componentJoint
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

/-- Reconstruct one physical child return with the same exact spectator
coefficients as at entry and the written return encoding of each component. -/
theorem weighted_return_represents {bindings state} (frame : Frame bindings)
    (spectators : Map) (high : Nat) {actual : History} {parts : Nat → History} {joint : Nat → Nat → Nat → ℂ}
    (weighted : WeightedHistory (List.range (product spectators).labels.length)
      (fun _ => spectatorWeight spectators high) actual parts)
    (logical : ∀ index < (product spectators).labels.length,
      Represents frame state (parts index) (fun digit reference => joint digit index reference)) :
    Represents frame state actual (returnFibre spectators high joint) := by
  intro col row bounded
  have fibreEq : returnFibre spectators high joint =
      fun digit ref => combination (List.range (product spectators).labels.length) (spectatorWeight spectators high)
        (fun index => joint digit index ref) := by
    funext digit ref
    unfold returnFibre combination spectatorWeight
    apply Qleisli.Exact.sum_map_congr
    intro _ _
    exact mul_comm _ _
  rw [fibreEq,weighted.operator,encode_combination]
  unfold combination
  apply Qleisli.Exact.sum_map_congr
  intro index member
  exact congrArg (fun value => value * spectatorWeight spectators high index)
    (logical index (List.mem_range.mp member) col row bounded)

private theorem return_families {bindings state} (frame : Frame bindings) (spectators : Map)
    {children family : List (Nat → History)} {joints : List (Nat → Nat → Nat → ℂ)}
    (mixed : ∀ high, List.Forall₂
      (WeightedHistory (List.range (product spectators).labels.length) (fun _ => spectatorWeight spectators high))
      (children.map (fun result => result high)) family)
    (logical : List.Forall₂ (fun parts joint =>
      ∀ index < (product spectators).labels.length,
      Represents frame state (parts index) (fun digit reference => joint digit index reference)) family joints) :
    List.Forall₂ (fun actual joint =>
      ∀ high, Represents frame state (actual high) (returnFibre spectators high joint)) children joints := by
  induction logical generalizing children with
  | nil =>
    cases children with
    | nil => exact .nil
    | cons _ _ => cases mixed 0
  | @cons parts joint family joints represented _ ih =>
    cases children with
    | nil => cases mixed 0
    | cons first rest =>
      refine .cons ?_ (ih ?_)
      · intro high
        have pair := mixed high
        cases pair with
        | cons head _ => exact weighted_return_represents frame spectators high head represented
      · intro high
        have pair := mixed high
        cases pair with
        | cons _ tail => exact tail

/-- Transport every logical result to the caller's written owner order,
keeping the complete ordered parent histories. -/
theorem original_weighted_call_returns
    {dependencies program block start count inputs ordinary effect sources caller before child retired value}
    {event : SourceTypes.SourceRuntimeContext.NamedEvent sources caller}
    (scope : @RuntimeCallScope.Checked dependencies program block start count inputs ordinary effect)
    (boundary : RuntimeNamedBoundary.Checked scope.interval inputs event before child retired value)
    {roles} (checked : RuntimeOwnerMap.Checked roles scope.interval.before)
    (parent : Frame checked.bindings) (sameBindings : checked.bindings = before.bindings)
    (returned : Frame child.bindings)
    {parents : List History} {children family : List (Nat → History)} {joints : List (Nat → Nat → Nat → ℂ)} :
    let spectators := RuntimeSelectionPartition.complement checked.bindings boundary.input.ordered
    List.Forall₂ (Agrees scope.interval.after.quantum.reference scope.localAfter.quantum.reference
      (spectators.map (·.port))) parents children →
    (∀ high, List.Forall₂
      (WeightedHistory (List.range (product spectators).labels.length) (fun _ => spectatorWeight spectators high))
      (children.map (fun result => result high)) family) →
    List.Forall₂ (fun parts joint =>
      ∀ index < (product spectators).labels.length,
        Represents returned scope.localAfter (parts index) (fun digit reference => joint digit index reference))
      family joints →
    ∃ output : Frame boundary.afterFrame.bindings,
      List.Forall₂ (fun actual joint => Represents output scope.interval.after actual
        (returnedOperator child.bindings boundary.afterFrame.bindings boundary.mapped spectators joint)) parents joints := by
  intro spectators paired mixed logical
  exact original_call_returns scope boundary checked parent sameBindings returned paired
    (return_families returned spectators mixed logical)

#print axioms child_input_weighted
#print axioms CheckedCallRun.weighted_children
#print axioms original_weighted_call_returns
end Qleisli.RuntimeCallHistory
