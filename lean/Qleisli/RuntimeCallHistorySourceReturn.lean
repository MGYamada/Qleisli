import Qleisli.RuntimeCallHistorySourceRefinement

/-! A child source return determines the caller operator on the original
owner order. The same checked sparse frame represents every component
of the actual ordered history family.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeCallHistory
open QleisliKernel QleisliKernel.Qirf
open Qleisli.RuntimeLiteralBody (SourceHistory SemanticHistoryAgreesWithInherited)
open Qleisli.RuntimeObservingPrefix (Issued issued_mono)
open Qleisli.RuntimeObservingValueRetention (Supports)
open RuntimeOwnerMap (Map)
open Qleisli.RuntimeSemanticForest (Frame product)
open Qleisli.RuntimeStructuralHistory (Represents)
open Qleisli.Semantics.ObservingAction (History WeightedHistory)

private theorem same_frame {bindings} (first second : Frame bindings) : first = second := by
  cases first with
  | mk code original available =>
    cases second with
    | mk other otherOriginal otherAvailable =>
      have same : code = other := Option.some.inj (original.symm.trans otherOriginal)
      subst other
      rfl

private noncomputable def jointReturn (spectators : Map) (source : Nat → SourceHistory)
    (digit logical reference : Nat) : ℂ :=
  if logical < (product spectators).labels.length then (source logical).operator digit reference else 0

/-- The original child's checked source returns determine the caller's
operator in its written owner order for every actual result. The result
list retains the multiplicity of the original execution. -/
theorem source_returns_in_caller_frame
    {dependencies program block start count inputs ordinary effect sources caller before child retired value}
    {event : SourceTypes.SourceRuntimeContext.NamedEvent sources caller}
    (scope : @RuntimeCallScope.Checked dependencies program block start count inputs ordinary effect)
    (boundary : RuntimeNamedBoundary.Checked scope.interval inputs event before child retired value)
    {roles} (checked : RuntimeOwnerMap.Checked roles scope.interval.before)
    (parent : Frame checked.bindings) (sameBindings : checked.bindings = before.bindings)
    (ordinals : List Nat) (inherited : Option (Nat → Prop)) (finalOrdinary : RuntimeOrdinaryBody.State)
    {parents : List History} {children nativeFamily : List (Nat → History)}
    {sourceFamily : List (Nat → SourceHistory)} :
    let spectators := RuntimeSelectionPartition.complement checked.bindings boundary.input.ordered
    List.Forall₂ (Agrees scope.interval.after.quantum.reference scope.localAfter.quantum.reference
      (spectators.map (·.port))) parents children →
    (∀ high, List.Forall₂
      (WeightedHistory (List.range (product spectators).labels.length) (fun _ => spectatorWeight spectators high))
      (children.map (fun result => result high)) nativeFamily) →
    List.Forall₂ (fun logical native => ∀ index,
      SemanticHistoryAgreesWithInherited inherited ordinals scope.localAfter child finalOrdinary
        (logical index) (native index)) sourceFamily nativeFamily →
    List.Forall₂ (fun actual logical => ∃ output : Frame boundary.afterFrame.bindings,
      Represents output scope.interval.after actual
        (returnedOperator child.bindings boundary.afterFrame.bindings boundary.mapped spectators (jointReturn spectators logical)))
      parents sourceFamily := by
  intro spectators paired weights returned
  cases sourceFamily with
  | nil =>
    have nativeEmpty := List.forall₂_nil_left_iff.mp returned
    have empty := weights 0
    rw [nativeEmpty] at empty
    have childrenEmpty : children = [] := by
      have nilMap := List.forall₂_nil_right_iff.mp empty
      cases children with
      | nil => rfl
      | cons _ _ => cases nilMap
    rw [childrenEmpty] at paired
    have parentsEmpty := List.forall₂_nil_right_iff.mp paired
    rw [parentsEmpty]
    exact .nil
  | cons first rest =>
    have existsFrame : Nonempty (Frame child.bindings) := by
      cases returned with
      | cons firstPair _ =>
        obtain ⟨_,_,_,frame,_⟩ := (firstPair 0).2.2.2.2
        exact ⟨frame⟩
    obtain ⟨frame⟩ := existsFrame
    have encodes : List.Forall₂ (fun native joint =>
        ∀ index < (product spectators).labels.length,
          Represents frame scope.localAfter (native index) (fun digit reference => joint digit index reference))
        nativeFamily ((first::rest).map (jointReturn spectators)) := by
      rw [List.forall₂_map_right_iff]
      apply returned.flip.imp
      intro native logical represented index bounded
      obtain ⟨_,_,_,localFrame,encoded⟩ := (represented index).2.2.2.2
      simpa only [jointReturn,if_pos bounded] using (same_frame localFrame frame ▸ encoded)
    obtain ⟨output,operators⟩ :=
      original_weighted_call_returns scope boundary checked parent sameBindings frame paired weights encodes
    rw [List.forall₂_map_right_iff] at operators
    exact operators.imp (fun _ _ represents => ⟨output,represents⟩)

/-- Use the source metadata at the original zero spectator ordinal and the
operator assembled from all the logical ordinals. The caller retains its
own checked owner state and return order. -/
noncomputable def callerSourceResult
    {dependencies program start count inputs sources caller block before child retired value}
    {event : SourceTypes.SourceRuntimeContext.NamedEvent sources caller}
    {interval : @RuntimeInterval.Checked dependencies program block start count}
    (boundary : RuntimeNamedBoundary.Checked interval inputs event before child retired value)
    (spectators : Map) (logical : Nat → SourceHistory) : SourceHistory :=
  let operator := returnedOperator child.bindings boundary.afterFrame.bindings boundary.mapped spectators (jointReturn spectators logical)
  { (logical 0) with owners := boundary.after, operator }

/-- Only the finite spectator columns and the source metadata at ordinal
zero contribute to the caller result. -/
theorem callerSourceResult_congr
    {dependencies program start count inputs sources caller block before child retired value}
    {event : SourceTypes.SourceRuntimeContext.NamedEvent sources caller}
    {interval : @RuntimeInterval.Checked dependencies program block start count}
    (boundary : RuntimeNamedBoundary.Checked interval inputs event before child retired value)
    (spectators : Map) {first second : Nat → SourceHistory}
    (metadata : first 0 = second 0)
    (columns : ∀ index < (product spectators).labels.length, first index = second index) :
    callerSourceResult boundary spectators first = callerSourceResult boundary spectators second := by
  have operators : jointReturn spectators first = jointReturn spectators second := by
    funext digit index reference
    by_cases bounded : index < (product spectators).labels.length
    · simp only [jointReturn,if_pos bounded,columns index bounded]
    · simp only [jointReturn,if_neg bounded]
  simp only [callerSourceResult,metadata,operators]

/-- The paired call transports its original source result back to the
caller's history, including the same SSA valuation and hidden outcomes.
The inherited-ID bound uses the actual enclosing interval's issued state. -/
theorem CheckedCallRun.caller_history_after_return
    {dependencies program block start count inputs ordinary effect sources caller before child retired value}
    {event : SourceTypes.SourceRuntimeContext.NamedEvent sources caller}
    {scope : @RuntimeCallScope.Checked dependencies program block start count inputs ordinary effect}
    (boundary : RuntimeNamedBoundary.Checked scope.interval inputs event before child retired value)
    {roles} (checked : RuntimeOwnerMap.Checked roles scope.interval.before)
    (parent : Frame checked.bindings) (sameBindings : checked.bindings = before.bindings)
    {actual localHistory parentEvents childEvents parents children}
    (run : CheckedCallRun scope
      ((RuntimeSelectionPartition.complement checked.bindings boundary.input.ordered).map (·.port))
      actual localHistory parentEvents childEvents parents children)
    (ordinals : List Nat) (inherited : Option (Nat → Prop)) (finalOrdinary : RuntimeOrdinaryBody.State)
    (incoming : Supports (fun id => match inherited with
      | none => Issued scope.interval.before id
      | some held => held id ∨ Issued scope.interval.before id) actual)
    {nativeFamily : List (Nat → History)} {sourceFamily : List (Nat → SourceHistory)} :
    let spectators := RuntimeSelectionPartition.complement checked.bindings boundary.input.ordered
    (∀ high, List.Forall₂
      (WeightedHistory (List.range (product spectators).labels.length) (fun _ => spectatorWeight spectators high))
      (children.map (fun result => result high)) nativeFamily) →
    List.Forall₂ (fun logical native => ∀ index,
      SemanticHistoryAgreesWithInherited (some (fun id => id ∈ actual.values.map Prod.fst))
        ordinals scope.localAfter child finalOrdinary (logical index) (native index)) sourceFamily nativeFamily →
    List.Forall₂ (SemanticHistoryAgreesWithInherited inherited ordinals scope.interval.after boundary.after finalOrdinary)
      (sourceFamily.map (callerSourceResult boundary spectators)) parents := by
  intro spectators weights returned
  have reconstructed := source_returns_in_caller_frame scope boundary checked parent sameBindings ordinals
    (some (fun id => id ∈ actual.values.map Prod.fst)) finalOrdinary run.paired.paired weights returned
  have indexed := List.forall₂_map_left_iff.mp (weights 0)
  have preserves : scope.interval.before.classical ⊆ scope.interval.after.classical := by
    obtain ⟨_,_,receipt⟩ := scope.interval.intervalRead
    exact (Raw.Observation.checkOps_history _ _ _ _ _ _ _ receipt).2.2
  rw [List.forall₂_map_left_iff]
  refine List.forall₂_of_length_eq_of_get reconstructed.length_eq.symm ?_
  intro index sourceBound parentBound
  have childBound : index < children.length := by simpa only [← run.paired.paired.length_eq] using parentBound
  have componentBound : index < nativeFamily.length := by simpa only [← returned.length_eq] using sourceBound
  have callPair := run.paired.paired.get parentBound childBound
  have weightPair := indexed.get childBound componentBound
  have sourceResult := (returned.get sourceBound componentBound) 0
  have equalValues := (callPair.values 0).trans (weightPair.values 0).symm
  have equalHidden := (callPair.hidden 0).trans (weightPair.hidden 0).symm
  obtain ⟨output,represented⟩ := reconstructed.get parentBound sourceBound
  let parentResult := parents.get ⟨index,parentBound⟩
  have allowed := (run.parentValues parentResult (List.get_mem _ _)).2
  refine ⟨rfl,equalHidden.trans sourceResult.2.1,?_,⟨?_,?_⟩,_,boundary.afterFrame,boundary.sameAfter,
    boundary.sameAfter ▸ output,?_⟩
  · rw [equalValues]
    exact sourceResult.2.2.1
  · rw [equalValues]
    exact sourceResult.2.2.2.1.1
  · intro id present
    rcases allowed present with input | wrote
    · cases inherited with
      | none => exact issued_mono preserves (incoming input)
      | some held => exact (incoming input).imp (fun old => old) (issued_mono preserves)
    · cases inherited with
      | none => exact wrote
      | some held => exact .inr wrote
  · exact Qleisli.RuntimeLiteralBody.cast_represents boundary.sameAfter output represented

#print axioms source_returns_in_caller_frame
#print axioms CheckedCallRun.caller_history_after_return
end Qleisli.RuntimeCallHistory
