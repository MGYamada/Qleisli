import Qleisli.RuntimePrimitiveSplitEvidence
import Qleisli.RuntimePairBasesLayout

/-! Semantic layouts from the same original join/split evaluation.
The event's erased successful evaluator equation fixes its actual source
arguments, result owners and child trees. Split completeness uses the actual
pair parser, not a supplied flattened boundary. No bounded carrier read,
matrix, output-code availability or new source/native check is introduced.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimePrimitiveSemanticLayouts
open QleisliKernel QleisliKernel.SourceTypes
open SourceRuntimeValues
open Semantics.FiniteCarrier (Layout tensor)

private theorem apply_join (site : Site) (arguments : List Value) (initial : Nat)
    (value : Value) (allocated consumed : List Semantics.SourceOwners.Owner) (after : Nat)
    (ran : SourceRuntimePrimitive.apply .join site arguments initial = .ok (value,allocated,consumed,after)) :
    ∃ first second result, arguments = [[.owner first],[.owner second]] ∧
      value = [.owner result] ∧ result.basis = .pair :: first.basis ++ second.basis ∧
      allocated = [result] ∧ consumed = [first,second] ∧ result.ordinal = initial ∧ after = initial+1 := by
  cases arguments with
  | nil => simp [SourceRuntimePrimitive.apply] at ran
  | cons firstArgument rest =>
    cases rest with
    | nil => simp [SourceRuntimePrimitive.apply] at ran
    | cons secondArgument rest =>
      cases rest with
      | cons third rest => simp [SourceRuntimePrimitive.apply] at ran
      | nil =>
        cases firstArgument with
        | nil => simp [SourceRuntimePrimitive.apply] at ran
        | cons firstAtom tail =>
          cases tail with
          | cons another rest => simp [SourceRuntimePrimitive.apply] at ran
          | nil =>
            cases firstAtom with
            | ordinary basis expression => simp [SourceRuntimePrimitive.apply] at ran
            | tuple arity => simp [SourceRuntimePrimitive.apply] at ran
            | owner first =>
              cases secondArgument with
              | nil => simp [SourceRuntimePrimitive.apply] at ran
              | cons secondAtom tail =>
                cases tail with
                | cons another rest => simp [SourceRuntimePrimitive.apply] at ran
                | nil =>
                  cases secondAtom with
                  | ordinary basis expression => simp [SourceRuntimePrimitive.apply] at ran
                  | tuple arity => simp [SourceRuntimePrimitive.apply] at ran
                  | owner second =>
                    by_cases aliased : (first.ordinal == second.ordinal) = true
                    · simp [SourceRuntimePrimitive.apply,aliased,Functor.map,Except.map] at ran
                    · let result : Semantics.SourceOwners.Owner :=
                        ⟨initial,.pair :: first.basis ++ second.basis⟩
                      have fields : value = [.owner result] ∧ allocated = [result] ∧
                          consumed = [first,second] ∧ after = initial+1 := by
                        simpa [SourceRuntimePrimitive.apply,aliased,result,Functor.map,Except.map,
                          Pure.pure,Except.pure,Bind.bind,Except.bind] using ran.symm
                      exact ⟨first,second,result,rfl,fields.1,rfl,fields.2.1,fields.2.2.1,rfl,fields.2.2.2⟩

/-- Actual join allocation and ordered pair basis from the event's retained
single evaluator result. The containing body still authenticates its caller. -/
theorem join_bases {sources caller} (event : SourceRuntimeContext.PrimitiveEvent sources caller)
    (selected : event.kind = .join) :
    ∃ first second result initial,
      event.arguments = [[.owner first],[.owner second]] ∧ event.value = [.owner result] ∧
      result.basis = .pair :: first.basis ++ second.basis ∧
      event.allocated = [result] ∧ event.consumed = [first,second] ∧
      result.ordinal = initial ∧ event.nextOrdinal = initial+1 := by
  obtain ⟨callerName,initial,evaluated⟩ := event.evaluated
  rw [selected] at evaluated
  obtain ⟨first,second,result,arguments,value,basis,allocated,consumed,ordinal,after⟩ :=
    apply_join ⟨caller,callerName,event.call.calleeOffset⟩ event.arguments initial event.value
      event.allocated event.consumed event.nextOrdinal evaluated
  exact ⟨first,second,result,initial,arguments,value,basis,allocated,consumed,ordinal,after⟩

/-- Every real joined result has its independently interpreted original pair
tree. Input owners of width zero remain distinct ordered source children. -/
theorem join_result_layout {sources caller} (event : SourceRuntimeContext.PrimitiveEvent sources caller)
    (selected : event.kind = .join)
    (available : ∀ owner ∈ event.arguments.flatMap valueOwners,
      ∃ layout, Semantics.FiniteCarrier.layout owner.basis = some layout) :
    ∀ owner ∈ valueOwners event.value,
      ∃ layout, Semantics.FiniteCarrier.layout owner.basis = some layout := by
  obtain ⟨first,second,result,_initial,arguments,value,basis,_allocated,_consumed,_ordinal,_after⟩ :=
    join_bases event selected
  obtain ⟨left,leftRead⟩ := available first (by simp [arguments,valueOwners])
  obtain ⟨right,rightRead⟩ := available second (by simp [arguments,valueOwners])
  intro owner member
  have same : owner = result := by simpa [value,valueOwners] using member
  subst owner
  refine ⟨tensor left right,?_⟩
  rw [basis]
  exact QleisliKernel.Qirf.RuntimeForestCode.layout_pair_reference
    first.basis second.basis left right leftRead rightRead

/-- The actual successful pair parser supplies both complete child layouts.
The parent interpretation does not itself pick a flattened split boundary. -/
theorem split_result_layout {sources caller} (event : SourceRuntimeContext.PrimitiveEvent sources caller)
    (selected : event.kind = .split)
    (available : ∀ owner ∈ event.arguments.flatMap valueOwners,
      ∃ layout, Semantics.FiniteCarrier.layout owner.basis = some layout) :
    ∀ owner ∈ valueOwners event.value,
      ∃ layout, Semantics.FiniteCarrier.layout owner.basis = some layout := by
  obtain ⟨input,left,right,_initial,arguments,value,parsed,_allocated,_consumed,_leftOrdinal,_rightOrdinal,_after⟩ :=
    Qleisli.RuntimePrimitiveSplitEvidence.split_bases event selected
  obtain ⟨parent,parentRead⟩ := available input (by simp [arguments,valueOwners])
  obtain ⟨leftLayout,rightLayout,leftRead,rightRead,_tensor⟩ :=
    Qleisli.RuntimePairBasesLayout.pairBases_layout input.basis left.basis right.basis parent parsed parentRead
  intro owner member
  have present : owner = left ∨ owner = right := by simpa [value,valueOwners] using member
  rcases present with same | same
  · subst owner
    exact ⟨leftLayout,leftRead⟩
  · subst owner
    exact ⟨rightLayout,rightRead⟩

#print axioms join_bases
#print axioms join_result_layout
#print axioms split_result_layout

end Qleisli.RuntimePrimitiveSemanticLayouts
