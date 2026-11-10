import Qleisli.RuntimeCallHistorySourceRefinement

/-! A child source return determines the caller operator on the original
owner order. The same checked sparse frame represents every component
of the actual ordered history family.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeCallHistory
open QleisliKernel QleisliKernel.Qirf
open Qleisli.RuntimeLiteralBody (SourceHistory SemanticHistoryAgreesWithInherited)
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

private noncomputable def jointReturn (source : Nat → SourceHistory)
    (digit logical reference : Nat) : ℂ :=
  (source logical).operator digit reference

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
        (returnedOperator child.bindings boundary.afterFrame.bindings boundary.mapped spectators (jointReturn logical)))
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
        ∀ index, Represents frame scope.localAfter (native index) (fun digit reference => joint digit index reference))
        nativeFamily ((first::rest).map jointReturn) := by
      rw [List.forall₂_map_right_iff]
      apply returned.flip.imp
      intro native logical represented index
      obtain ⟨_,_,_,localFrame,encoded⟩ := (represented index).2.2.2.2
      exact (same_frame localFrame frame) ▸ encoded
    obtain ⟨output,operators⟩ :=
      original_weighted_call_returns scope boundary checked parent sameBindings frame paired weights encodes
    rw [List.forall₂_map_right_iff] at operators
    exact operators.imp (fun _ _ represents => ⟨output,represents⟩)

#print axioms source_returns_in_caller_frame
end Qleisli.RuntimeCallHistory
