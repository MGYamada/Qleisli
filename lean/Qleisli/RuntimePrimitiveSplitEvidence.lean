import QleisliKernel.SourceTypes.SourceRuntimeContext

/-! Exact split results from the retained original primitive evaluation.
The existential caller name is used only to recover this result property;
the actual containing body read retains its separate authenticity duty. No
source evaluation, parser, guard, bounded reader or native check is rerun here.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimePrimitiveSplitEvidence
open QleisliKernel QleisliKernel.SourceTypes
open SourceRuntimeValues

private theorem apply_split (site : Site) (arguments : List Value) (initial : Nat)
    (value : Value) (allocated consumed : List Semantics.SourceOwners.Owner) (after : Nat)
    (ran : SourceRuntimePrimitive.apply .split site arguments initial = .ok (value,allocated,consumed,after)) :
    ∃ input left right, arguments = [[.owner input]] ∧ value = [.tuple 2,.owner left,.owner right] ∧
      pairBases input.basis = .ok (left.basis,right.basis) ∧
      allocated = [left,right] ∧ consumed = [input] ∧
      left.ordinal = initial ∧ right.ordinal = initial+1 ∧ after = initial+2 := by
  cases arguments with
  | nil => simp [SourceRuntimePrimitive.apply] at ran
  | cons argument arguments =>
    cases arguments with
    | cons second rest => simp [SourceRuntimePrimitive.apply] at ran
    | nil =>
      cases argument with
      | nil => simp [SourceRuntimePrimitive.apply] at ran
      | cons atom tail =>
        cases tail with
        | cons second rest => simp [SourceRuntimePrimitive.apply] at ran
        | nil =>
          cases atom with
          | ordinary basis expression => simp [SourceRuntimePrimitive.apply] at ran
          | tuple arity => simp [SourceRuntimePrimitive.apply] at ran
          | owner input =>
            cases parsed : pairBases input.basis with
            | error error => simp [SourceRuntimePrimitive.apply,parsed,Functor.map,Except.map] at ran
            | ok parts =>
              obtain ⟨first,second⟩ := parts
              let left : Semantics.SourceOwners.Owner := ⟨initial,first⟩
              let right : Semantics.SourceOwners.Owner := ⟨initial+1,second⟩
              have result : value = [.tuple 2,.owner left,.owner right] ∧
                  allocated = [left,right] ∧ consumed = [input] ∧ after = initial+2 := by
                simpa [SourceRuntimePrimitive.apply,parsed,left,right,Functor.map,Except.map] using ran.symm
              exact ⟨input,left,right,rfl,result.1,parsed,result.2.1,result.2.2.1,
                rfl,rfl,result.2.2.2⟩

/-- A real split event retains the same successful pairBases result for both
actual returned source owners, together with its allocation, consumption and
ordinal results. No flattened-pair or child-layout assumption is supplied. -/
theorem split_bases {sources caller} (event : SourceRuntimeContext.PrimitiveEvent sources caller)
    (selected : event.kind = .split) :
    ∃ input left right initial,
      event.arguments = [[.owner input]] ∧ event.value = [.tuple 2,.owner left,.owner right] ∧
      pairBases input.basis = .ok (left.basis,right.basis) ∧
      event.allocated = [left,right] ∧ event.consumed = [input] ∧
      left.ordinal = initial ∧ right.ordinal = initial+1 ∧ event.nextOrdinal = initial+2 := by
  obtain ⟨callerName,initial,evaluated⟩ := event.evaluated
  rw [selected] at evaluated
  obtain ⟨input,left,right,arguments,value,bases,allocated,consumed,leftOrdinal,rightOrdinal,after⟩ :=
    apply_split ⟨caller,callerName,event.call.calleeOffset⟩ event.arguments initial event.value
      event.allocated event.consumed event.nextOrdinal evaluated
  exact ⟨input,left,right,initial,arguments,value,bases,allocated,consumed,leftOrdinal,rightOrdinal,after⟩

#print axioms split_bases

end Qleisli.RuntimePrimitiveSplitEvidence
