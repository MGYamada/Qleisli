import Qleisli.RuntimeOwnerFlowExtension

/-! Spectator extension for the actual multi-owner flow and operation folds.
Both local and caller executions use the same original operations. Complete
Tree identities and the same spectator cells are retained; no width-based
owner identification, code equation or runtime acceptance rule is added.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeOwnerFlowSteps
open QleisliKernel.Semantics Qleisli.RuntimeOwnerFlowExtension

private theorem takeMany_extension (targets : List Raw.Target)
    {values partBefore wholeBefore spectators partValues wholeValues partAfter wholeAfter : RawOwnerFlow.Frame}
    (context : wholeBefore.Perm (partBefore ++ spectators))
    (unique : (wholeBefore.map Prod.fst).Nodup)
    (partRead : targets.foldlM (fun (values,current) target => do
      let (tree,remaining) ← RawOwnerFlow.take target.input current
      pure ((target.output,tree) :: values,remaining)) (values,partBefore) = some (partValues,partAfter))
    (wholeRead : targets.foldlM (fun (values,current) target => do
      let (tree,remaining) ← RawOwnerFlow.take target.input current
      pure ((target.output,tree) :: values,remaining)) (values,wholeBefore) = some (wholeValues,wholeAfter)) :
    wholeValues = partValues ∧ wholeAfter.Perm (partAfter ++ spectators) ∧
      (wholeAfter.map Prod.fst).Nodup := by
  induction targets generalizing values partBefore wholeBefore partValues wholeValues partAfter wholeAfter with
  | nil =>
    change some (values,partBefore) = some (partValues,partAfter) at partRead
    change some (values,wholeBefore) = some (wholeValues,wholeAfter) at wholeRead
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj partRead)
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj wholeRead)
    exact ⟨rfl,context,unique⟩
  | cons target rest ih =>
    rw [List.foldlM_cons] at partRead wholeRead
    obtain ⟨⟨partAccum,partNext⟩,partStep,partTail⟩ := Option.bind_eq_some_iff.mp partRead
    obtain ⟨⟨wholeAccum,wholeNext⟩,wholeStep,wholeTail⟩ := Option.bind_eq_some_iff.mp wholeRead
    obtain ⟨⟨partTree,partRest⟩,partTaken,partReturned⟩ := Option.bind_eq_some_iff.mp partStep
    obtain ⟨⟨wholeTree,wholeRest⟩,wholeTaken,wholeReturned⟩ := Option.bind_eq_some_iff.mp wholeStep
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj partReturned)
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj wholeReturned)
    have taken := take_extension context unique partTaken wholeTaken
    rw [taken.1] at wholeTail
    exact ih taken.2.1 taken.2.2 partTail wholeTail

private theorem putMany_extension (values : RawOwnerFlow.Frame)
    {partBefore wholeBefore spectators partAfter wholeAfter : RawOwnerFlow.Frame}
    (context : wholeBefore.Perm (partBefore ++ spectators))
    (unique : (wholeBefore.map Prod.fst).Nodup)
    (partRead : values.foldlM (fun current cell => RawOwnerFlow.put cell.1 cell.2 current)
      partBefore = some partAfter)
    (wholeRead : values.foldlM (fun current cell => RawOwnerFlow.put cell.1 cell.2 current)
      wholeBefore = some wholeAfter) :
    wholeAfter.Perm (partAfter ++ spectators) ∧ (wholeAfter.map Prod.fst).Nodup := by
  induction values generalizing partBefore wholeBefore partAfter wholeAfter with
  | nil =>
    change some partBefore = some partAfter at partRead
    change some wholeBefore = some wholeAfter at wholeRead
    cases Option.some.inj partRead
    cases Option.some.inj wholeRead
    exact ⟨context,unique⟩
  | cons cell rest ih =>
    rw [List.foldlM_cons] at partRead wholeRead
    obtain ⟨partNext,partPut,partTail⟩ := Option.bind_eq_some_iff.mp partRead
    obtain ⟨wholeNext,wholePut,wholeTail⟩ := Option.bind_eq_some_iff.mp wholeRead
    have inserted := put_extension context unique partPut wholePut
    exact ih inserted.1 inserted.2 partTail wholeTail

/-- The same original ordered target list moves the same complete Trees in
both runs. Duplicate/colliding tokens are decided by those actual executions;
no target is dropped, deduplicated or selected by width. -/
theorem moveMany_extension (targets : List Raw.Target)
    {partBefore wholeBefore spectators partAfter wholeAfter : RawOwnerFlow.Frame}
    (context : wholeBefore.Perm (partBefore ++ spectators))
    (unique : (wholeBefore.map Prod.fst).Nodup)
    (partRead : RawOwnerFlow.moveMany targets partBefore = some partAfter)
    (wholeRead : RawOwnerFlow.moveMany targets wholeBefore = some wholeAfter) :
    wholeAfter.Perm (partAfter ++ spectators) ∧ (wholeAfter.map Prod.fst).Nodup := by
  unfold RawOwnerFlow.moveMany at partRead wholeRead
  obtain ⟨⟨partValues,partRest⟩,partTaken,partPut⟩ := Option.bind_eq_some_iff.mp partRead
  obtain ⟨⟨wholeValues,wholeRest⟩,wholeTaken,wholePut⟩ := Option.bind_eq_some_iff.mp wholeRead
  have taken := takeMany_extension targets context unique partTaken wholeTaken
  rw [taken.1] at wholePut
  exact putMany_extension partValues taken.2.1 taken.2.2 partPut wholePut

/-- The actual join retains both complete ordered child Trees. Spectators
remain the same cells even when either child has zero physical width. -/
theorem join_extension (left right output : Nat)
    {partBefore wholeBefore spectators partAfter wholeAfter : RawOwnerFlow.Frame}
    (context : wholeBefore.Perm (partBefore ++ spectators))
    (unique : (wholeBefore.map Prod.fst).Nodup)
    (partRead : RawOwnerFlow.step partBefore (.join left right output) = some partAfter)
    (wholeRead : RawOwnerFlow.step wholeBefore (.join left right output) = some wholeAfter) :
    wholeAfter.Perm (partAfter ++ spectators) ∧ (wholeAfter.map Prod.fst).Nodup := by
  simp only [RawOwnerFlow.step] at partRead wholeRead
  obtain ⟨⟨partLeft,partNext⟩,partLeftRead,partTail⟩ := Option.bind_eq_some_iff.mp partRead
  obtain ⟨⟨partRight,partRest⟩,partRightRead,partPut⟩ := Option.bind_eq_some_iff.mp partTail
  obtain ⟨⟨wholeLeft,wholeNext⟩,wholeLeftRead,wholeTail⟩ := Option.bind_eq_some_iff.mp wholeRead
  obtain ⟨⟨wholeRight,wholeRest⟩,wholeRightRead,wholePut⟩ := Option.bind_eq_some_iff.mp wholeTail
  have first := take_extension context unique partLeftRead wholeLeftRead
  have second := take_extension first.2.1 first.2.2 partRightRead wholeRightRead
  have callerPut : RawOwnerFlow.put output
      (.pair partLeft partRight (partLeft.width+partRight.width)) wholeRest = some wholeAfter := by
    simpa only [first.1,second.1] using wholePut
  exact put_extension second.2.1 second.2.2 partPut callerPut

private theorem split_read (input left right leftBits : Nat)
    {before after : RawOwnerFlow.Frame}
    (ran : RawOwnerFlow.step before (.split input left right leftBits) = some after) :
    ∃ first second bits remaining middle,
      RawOwnerFlow.take input before = some (.pair first second bits,remaining) ∧
      RawOwnerFlow.put left first remaining = some middle ∧
      RawOwnerFlow.put right second middle = some after := by
  simp only [RawOwnerFlow.step] at ran
  obtain ⟨⟨tree,remaining⟩,taken,tail⟩ := Option.bind_eq_some_iff.mp ran
  cases tree with
  | owner role bits => cases tail
  | pair first second bits =>
    by_cases width : (first.width != leftBits) = true
    · simp only [width,ite_true] at tail
      cases tail
    · simp only [width] at tail
      obtain ⟨middle,leftPut,rightPut⟩ := Option.bind_eq_some_iff.mp tail
      exact ⟨first,second,bits,remaining,middle,taken,leftPut,rightPut⟩

/-- A successful split recovers the identical original pair and its ordered
children from the two runs. Equal widths cannot select a different owner. -/
theorem split_extension (input left right leftBits : Nat)
    {partBefore wholeBefore spectators partAfter wholeAfter : RawOwnerFlow.Frame}
    (context : wholeBefore.Perm (partBefore ++ spectators))
    (unique : (wholeBefore.map Prod.fst).Nodup)
    (partRead : RawOwnerFlow.step partBefore (.split input left right leftBits) = some partAfter)
    (wholeRead : RawOwnerFlow.step wholeBefore (.split input left right leftBits) = some wholeAfter) :
    wholeAfter.Perm (partAfter ++ spectators) ∧ (wholeAfter.map Prod.fst).Nodup := by
  obtain ⟨partLeft,partRight,partBits,partRest,partMiddle,partTaken,partFirst,partLast⟩ :=
    split_read input left right leftBits partRead
  obtain ⟨wholeLeft,wholeRight,wholeBits,wholeRest,wholeMiddle,wholeTaken,wholeFirst,wholeLast⟩ :=
    split_read input left right leftBits wholeRead
  have taken := take_extension context unique partTaken wholeTaken
  have same := RawOwnerFlow.Tree.pair.inj taken.1
  have firstPut : RawOwnerFlow.put left partLeft wholeRest = some wholeMiddle := by
    simpa only [same.1] using wholeFirst
  have first := put_extension taken.2.1 taken.2.2 partFirst firstPut
  have lastPut : RawOwnerFlow.put right partRight wholeMiddle = some wholeAfter := by
    simpa only [same.2.1] using wholeLast
  exact put_extension first.1 first.2 partLast lastPut

/-- Every actual successful owner-flow constructor extends through the same
spectators. The original operation is used on both sides, including every
moveMany target and the original join/split tree structure. -/
theorem step_extension (operation : Raw.Op)
    {partBefore wholeBefore spectators partAfter wholeAfter : RawOwnerFlow.Frame}
    (context : wholeBefore.Perm (partBefore ++ spectators))
    (unique : (wholeBefore.map Prod.fst).Nodup)
    (partRead : RawOwnerFlow.step partBefore operation = some partAfter)
    (wholeRead : RawOwnerFlow.step wholeBefore operation = some wholeAfter) :
    wholeAfter.Perm (partAfter ++ spectators) ∧ (wholeAfter.map Prod.fst).Nodup := by
  cases operation with
  | gate value input output => exact move_extension context unique partRead wholeRead
  | applyUnitary input output steps => exact move_extension context unique partRead wholeRead
  | certifiedCompute input output ancilla function uses logical =>
    exact move_extension context unique partRead wholeRead
  | liftBasis input output wires table =>
    simp only [RawOwnerFlow.step] at partRead wholeRead
    obtain ⟨⟨partTree,partRest⟩,partTaken,partTail⟩ := Option.bind_eq_some_iff.mp partRead
    obtain ⟨⟨wholeTree,wholeRest⟩,wholeTaken,wholeTail⟩ := Option.bind_eq_some_iff.mp wholeRead
    split at partTail
    · cases partTail
    · split at wholeTail
      · cases wholeTail
      · have taken := take_extension context unique partTaken wholeTaken
        rw [taken.1] at wholeTail
        exact put_extension taken.2.1 taken.2.2 partTail wholeTail
  | cnot control target controlOut targetOut =>
    exact moveMany_extension [⟨control,controlOut⟩,⟨target,targetOut⟩] context unique partRead wholeRead
  | quantumIf control target controlOut targetOut zero one =>
    exact moveMany_extension [⟨control,controlOut⟩,⟨target,targetOut⟩] context unique partRead wholeRead
  | toffoli a b target aOut bOut targetOut =>
    exact moveMany_extension [⟨a,aOut⟩,⟨b,bOut⟩,⟨target,targetOut⟩] context unique partRead wholeRead
  | computeUseUncompute input output targets ancilla function uses =>
    exact moveMany_extension (⟨input,output⟩ :: targets) context unique partRead wholeRead
  | join left right output => exact join_extension left right output context unique partRead wholeRead
  | split input left right leftBits => exact split_extension input left right leftBits context unique partRead wholeRead
  | init0 output wire => cases partRead
  | packUnit output => cases partRead
  | unpackUnit input => cases partRead

/-- The same complete literal operation list extends through the unchanged
spectator cells. This proves no source-binding or physical code equation; its
initial context/uniqueness must come from the authentic selected/caller seeds. -/
theorem fold_extension (operations : List Raw.Op)
    {partBefore wholeBefore spectators partAfter wholeAfter : RawOwnerFlow.Frame}
    (context : wholeBefore.Perm (partBefore ++ spectators))
    (unique : (wholeBefore.map Prod.fst).Nodup)
    (partRead : operations.foldlM RawOwnerFlow.step partBefore = some partAfter)
    (wholeRead : operations.foldlM RawOwnerFlow.step wholeBefore = some wholeAfter) :
    wholeAfter.Perm (partAfter ++ spectators) ∧ (wholeAfter.map Prod.fst).Nodup := by
  induction operations generalizing partBefore wholeBefore partAfter wholeAfter with
  | nil =>
    change some partBefore = some partAfter at partRead
    change some wholeBefore = some wholeAfter at wholeRead
    cases Option.some.inj partRead
    cases Option.some.inj wholeRead
    exact ⟨context,unique⟩
  | cons operation rest ih =>
    rw [List.foldlM_cons] at partRead wholeRead
    obtain ⟨partNext,partStep,partTail⟩ := Option.bind_eq_some_iff.mp partRead
    obtain ⟨wholeNext,wholeStep,wholeTail⟩ := Option.bind_eq_some_iff.mp wholeRead
    have first := step_extension operation context unique partStep wholeStep
    exact ih first.1 first.2 partTail wholeTail

#print axioms moveMany_extension
#print axioms join_extension
#print axioms split_extension
#print axioms step_extension
#print axioms fold_extension

end Qleisli.RuntimeOwnerFlowSteps
