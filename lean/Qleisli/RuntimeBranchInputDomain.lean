import QleisliKernel.Qirf.RuntimeBranchCondition

/-! The ordinary input row used by a condition is the actual original root
row. Independently read layouts and a different successful starting budget
cannot change its decoded source ordinals.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeBranchInputDomain
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Finite QleisliKernel.SourceTypes
open RuntimeOrdinaryInputs (Fields decode)
open RuntimeBranchCondition (rootEntries)

theorem root_entries {sources owner name signature}
    (body : @SourceRuntimeTrace.Body sources owner name signature) :
    rootEntries (.root body) =
      (RuntimeSourceBoundary.summary body).parameterValues.flatMap SourceRuntimeValues.ordinary := by
  unfold rootEntries
  rw [WellFounded.fix_eq]
  cases body with
  | mk checked originalSignature =>
    cases originalSignature
    rfl

theorem named_entries {sources rootOwner rootName caller}
    (event : SourceRuntimeContext.NamedEvent sources caller)
    (body : SourceRuntimeTrace.Body event.target.signature)
    (read : RuntimeInterval.Computed (SourceRuntimeTrace.readNamedBody event) body)
    (parent : RuntimeOrdinaryBody.CallPath sources rootOwner rootName caller event.target.callerName) :
    rootEntries (.named event body read parent) = rootEntries parent := by
  unfold rootEntries
  rw [WellFounded.fix_eq]

private theorem field_unique {entry} (first second : RuntimeOrdinaryInputs.Field entry) :
    first = second := by
  have ordinal := Semantics.SourceOrdinary.Expression.input.inj (first.seeded.symm.trans second.seeded)
  obtain ⟨firstWork,firstLeft,firstRead⟩ := first.original
  obtain ⟨secondWork,secondLeft,secondRead⟩ := second.original
  have same := Option.some.inj ((FiniteCarrier.read_reference _ _ firstWork firstLeft firstRead).symm.trans
    (FiniteCarrier.read_reference _ _ secondWork secondLeft secondRead))
  cases first
  cases second
  cases ordinal
  cases same
  rfl

private theorem fields_unique (first second : Fields)
    (same : first.map Sigma.fst = second.map Sigma.fst) : first = second := by
  induction first generalizing second with
  | nil => cases second <;> simp_all
  | cons first tail ih =>
    cases second with
    | nil => simp at same
    | cons second rest =>
      obtain ⟨head,tail⟩ := List.cons.inj same
      have field : first = second := by
        cases first with
        | mk entry a =>
          cases second with
          | mk other b =>
            change entry = other at head
            subst other
            exact congrArg (Sigma.mk entry) (field_unique a b)
      rw [field,ih rest tail]

private theorem decode_unique (fields : Fields) (assignment : List Bool) {first second : List Nat}
    (left : RuntimeInterval.Computed (decode fields assignment) first)
    (right : RuntimeInterval.Computed (decode fields assignment) second) :
    first = second := by
  induction fields generalizing assignment first second with
  | nil =>
    obtain ⟨before,after,left⟩ := left
    obtain ⟨other,final,right⟩ := right
    unfold decode at left right
    rw [WellFounded.fix_eq] at left right
    obtain ⟨_,_,_,finishLeft⟩ := bind_success _ _ _ _ _ left
    obtain ⟨_,_,_,finishRight⟩ := bind_success _ _ _ _ _ right
    exact (pure_success _ _ _ _ finishLeft).1.trans (pure_success _ _ _ _ finishRight).1.symm
  | cons field fields ih =>
    obtain ⟨before,after,left⟩ := left
    obtain ⟨other,final,right⟩ := right
    unfold decode at left right
    rw [WellFounded.fix_eq] at left right
    obtain ⟨_,_,_,left⟩ := bind_success _ _ _ _ _ left
    obtain ⟨_,_,_,left⟩ := bind_success _ _ _ _ _ left
    obtain ⟨_,_,_,left⟩ := bind_success _ _ _ _ _ left
    obtain ⟨a,middle,leftRead,finishLeft⟩ := bind_success _ _ _ _ _ left
    obtain ⟨_,_,_,right⟩ := bind_success _ _ _ _ _ right
    obtain ⟨_,_,_,right⟩ := bind_success _ _ _ _ _ right
    obtain ⟨_,_,_,right⟩ := bind_success _ _ _ _ _ right
    obtain ⟨b,last,rightRead,finishRight⟩ := bind_success _ _ _ _ _ right
    have tails : a = b := ih _ ⟨_,middle,leftRead⟩ ⟨_,last,rightRead⟩
    rw [(pure_success _ _ _ _ finishLeft).1,(pure_success _ _ _ _ finishRight).1,tails]

private theorem decoded_member (fields : Fields) (assignments : List (List Bool))
    {assignment : List Bool} {ordinals : List Nat} {rows : List (List Nat)}
    (member : assignment ∈ assignments)
    (row : RuntimeInterval.Computed (decode fields assignment) ordinals)
    (all : RuntimeInterval.Computed (assignments.mapM (decode fields)) rows) : ordinals ∈ rows := by
  induction assignments generalizing rows with
  | nil => cases member
  | cons first rest ih =>
    obtain ⟨work,left,read⟩ := all
    simp only [List.mapM_cons] at read
    obtain ⟨head,middle,headRead,read⟩ := bind_success _ _ _ _ _ read
    obtain ⟨tail,last,tailRead,returned⟩ := bind_success _ _ _ _ _ read
    rw [(pure_success _ _ _ _ returned).1]
    rcases List.mem_cons.mp member with equal | later
    · subst first
      exact List.mem_cons.mpr (.inl (decode_unique fields assignment row ⟨work,middle,headRead⟩))
    · exact List.mem_cons_of_mem _ (ih later ⟨middle,last,tailRead⟩)

private theorem decoded_rows_unique (fields : Fields) (assignments : List (List Bool))
    {first second : List (List Nat)}
    (left : RuntimeInterval.Computed (assignments.mapM (decode fields)) first)
    (right : RuntimeInterval.Computed (assignments.mapM (decode fields)) second) : first = second := by
  induction assignments generalizing first second with
  | nil =>
    obtain ⟨before,after,left⟩ := left
    obtain ⟨other,final,right⟩ := right
    exact (pure_success _ _ _ _ left).1.trans (pure_success _ _ _ _ right).1.symm
  | cons assignment rest ih =>
    obtain ⟨before,after,left⟩ := left
    obtain ⟨other,final,right⟩ := right
    simp only [List.mapM_cons] at left right
    obtain ⟨firstHead,a,headLeft,left⟩ := bind_success _ _ _ _ _ left
    obtain ⟨firstTail,b,tailLeft,left⟩ := bind_success _ _ _ _ _ left
    obtain ⟨secondHead,c,headRight,right⟩ := bind_success _ _ _ _ _ right
    obtain ⟨secondTail,e,tailRight,right⟩ := bind_success _ _ _ _ _ right
    have heads := decode_unique fields assignment ⟨before,a,headLeft⟩ ⟨other,c,headRight⟩
    have tails := ih ⟨a,b,tailLeft⟩ ⟨c,e,tailRight⟩
    rw [(pure_success _ _ _ _ left).1,(pure_success _ _ _ _ right).1,heads,tails]

/-- The same original input forest gives the same ordered table in a child
condition. This uses both actual successful reads, with their own budgets. -/
theorem same_input_rows {firstSources firstRootOwner firstRootName firstOwner firstName
    secondSources secondRootOwner secondRootName secondOwner secondName}
    {leftPath : RuntimeOrdinaryBody.CallPath firstSources firstRootOwner firstRootName firstOwner firstName}
    {rightPath : RuntimeOrdinaryBody.CallPath secondSources secondRootOwner secondRootName secondOwner secondName}
    (left : RuntimeBranchCondition.Inputs leftPath) (right : RuntimeBranchCondition.Inputs rightPath)
    (original : rootEntries leftPath = rootEntries rightPath) : left.rows = right.rows := by
  have fields : left.fields = right.fields :=
    fields_unique _ _ (left.originalFields.trans (original.trans right.originalFields.symm))
  have sameForest := congrArg (fun entries => Semantics.OrdinaryInputs.forest (entries.map Prod.fst)) original
  have layout := Option.some.inj (left.domain.reference.symm.trans (sameForest.trans right.domain.reference))
  have assignments : OrdinaryDomain.assignments left.domain = OrdinaryDomain.assignments right.domain := by
    unfold OrdinaryDomain.assignments
    rw [layout]
  exact decoded_rows_unique left.fields _ left.original (by rw [fields,assignments]; exact right.original)

/-- The exact checked root row occurs in the condition's input table.
The original call path must reach that root's complete source input forest. -/
theorem original_row_member {sources rootOwner rootName signature dependencies program
    branchSources branchRootOwner branchRootName owner name}
    {body : @SourceRuntimeTrace.Body sources rootOwner rootName signature}
    {prepared : RuntimeInterval.Prepared dependencies program} {runtime inputs}
    {initial : RuntimeOrdinaryInputs.Checked body prepared runtime inputs}
    {assignment : List Bool} (row : RuntimeOrdinaryInputs.Row initial assignment)
    {path : RuntimeOrdinaryBody.CallPath branchSources branchRootOwner branchRootName owner name}
    (branch : RuntimeBranchCondition.Inputs path) (original : rootEntries path = rootEntries (.root body)) :
    row.ordinals ∈ branch.rows := by
  rw [root_entries body] at original
  have fields : branch.fields = initial.fields :=
    fields_unique _ _ (branch.originalFields.trans (original.trans initial.originalFields.symm))
  have source := (congrArg (fun entries => Semantics.OrdinaryInputs.forest (entries.map Prod.fst)) original).symm.trans
    branch.domain.reference
  have layout := Option.some.inj (source.symm.trans initial.sourceCode)
  have assignments : OrdinaryDomain.assignments branch.domain = OrdinaryDomain.assignments initial.domain := by
    unfold OrdinaryDomain.assignments
    rw [layout]
  have member := row.originalAssignment
  rw [← assignments] at member
  have decoded := row.decoded
  rw [← fields] at decoded
  exact decoded_member branch.fields _ member decoded branch.original

#print axioms original_row_member
end Qleisli.RuntimeBranchInputDomain
