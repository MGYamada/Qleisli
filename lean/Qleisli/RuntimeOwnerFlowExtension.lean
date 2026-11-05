import QleisliKernel.Semantics.RawOwnerFlow

/-! One-step extension of the actual logical-owner flow through spectators.
The two successful executions consume the same original token. Token uniqueness
identifies the complete Tree, including empty owners; no width or separability
assumption identifies a source owner. The context permutation is an induction
invariant for the future local/global fold, not a supplied code equation.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeOwnerFlowExtension
open QleisliKernel.Semantics

private theorem take_fold_first (token : Nat) (values : RawOwnerFlow.Frame) :
    (values.foldr (fun cell (rest,result) =>
      (cell :: rest,if cell.1 == token then some (cell.2,rest)
        else result.map fun (tree,remaining) => (tree,cell :: remaining))) ([],none)).1 = values := by
  induction values with
  | nil => rfl
  | cons first rest ih => exact congrArg (List.cons first) ih

private theorem take_cons (token : Nat) (cell : Nat × RawOwnerFlow.Tree) (rest : RawOwnerFlow.Frame) :
    RawOwnerFlow.take token (cell :: rest) =
      if cell.1 == token then some (cell.2,rest)
      else (RawOwnerFlow.take token rest).map fun (tree,remaining) => (tree,cell :: remaining) := by
  simp only [RawOwnerFlow.take,List.foldr_cons,take_fold_first]

private theorem take_perm {token : Nat} {before : RawOwnerFlow.Frame}
    {tree : RawOwnerFlow.Tree} {remaining : RawOwnerFlow.Frame}
    (ran : RawOwnerFlow.take token before = some (tree,remaining)) :
    before.Perm ((token,tree) :: remaining) := by
  induction before generalizing tree remaining with
  | nil => cases ran
  | cons first rest ih =>
    rw [take_cons] at ran
    split at ran
    · rename_i chosen
      have equal := Option.some.inj ran
      have sameCell : first = (token,tree) :=
        Prod.ext (beq_iff_eq.mp chosen) (congrArg Prod.fst equal)
      have sameRest : rest = remaining := congrArg Prod.snd equal
      simpa only [sameCell,sameRest] using (List.Perm.refl (first :: rest))
    · obtain ⟨⟨found,tail⟩,taken,equal⟩ := Option.map_eq_some_iff.mp ran
      have sameTree : found = tree := congrArg Prod.fst equal
      have sameRest : first :: tail = remaining := congrArg Prod.snd equal
      have moved := (List.Perm.cons first (ih taken)).trans (List.Perm.swap (token,found) first tail)
      simpa only [sameTree,sameRest] using moved

private theorem take_unique {token : Nat} {before : RawOwnerFlow.Frame}
    {tree : RawOwnerFlow.Tree} {remaining : RawOwnerFlow.Frame}
    (unique : (before.map Prod.fst).Nodup)
    (ran : RawOwnerFlow.take token before = some (tree,remaining)) :
    (remaining.map Prod.fst).Nodup := by
  have all := (List.Perm.map Prod.fst (take_perm ran)).nodup unique
  change (token :: remaining.map Prod.fst).Nodup at all
  exact (List.nodup_cons.mp all).2

/-- The actual take removes exactly its original token/Tree cell. This
partition also accounts for empty owners when a returned list is consumed. -/
theorem take_partition {token : Nat} {before : RawOwnerFlow.Frame}
    {tree : RawOwnerFlow.Tree} {remaining : RawOwnerFlow.Frame}
    (ran : RawOwnerFlow.take token before = some (tree,remaining)) :
    before.Perm ((token,tree) :: remaining) :=
  take_perm ran

private theorem map_unique {α β : Type} (f : α → β) (values : List α) :
    (values.map f).Nodup → ∀ first ∈ values,∀ second ∈ values,f first = f second → first = second := by
  induction values with
  | nil => intro _unique first member; cases member
  | cons head rest ih =>
    intro unique first firstMember second secondMember equal
    have separate := List.nodup_cons.mp unique
    rcases List.mem_cons.mp firstMember with same | firstLater
    · subst first
      rcases List.mem_cons.mp secondMember with same | secondLater
      · exact same.symm
      · exact False.elim (separate.1 (List.mem_map.mpr ⟨second,secondLater,equal.symm⟩))
    · rcases List.mem_cons.mp secondMember with same | secondLater
      · subst second
        exact False.elim (separate.1 (List.mem_map.mpr ⟨first,firstLater,equal⟩))
      · exact ih separate.2 first firstLater second secondLater equal

/-- Removing the same actual token from a local frame and its complete caller
recovers the same original Tree and leaves precisely the same spectator cells.
The caller's token uniqueness is the original ownership premise. -/
theorem take_extension {token : Nat}
    {partBefore wholeBefore spectators partAfter wholeAfter : RawOwnerFlow.Frame}
    {partTree wholeTree : RawOwnerFlow.Tree}
    (context : wholeBefore.Perm (partBefore ++ spectators))
    (unique : (wholeBefore.map Prod.fst).Nodup)
    (partRead : RawOwnerFlow.take token partBefore = some (partTree,partAfter))
    (wholeRead : RawOwnerFlow.take token wholeBefore = some (wholeTree,wholeAfter)) :
    wholeTree = partTree ∧ wholeAfter.Perm (partAfter ++ spectators) ∧
      (wholeAfter.map Prod.fst).Nodup := by
  have partMember : (token,partTree) ∈ partBefore :=
    (take_perm partRead).mem_iff.mpr List.mem_cons_self
  have originalMember : (token,partTree) ∈ wholeBefore :=
    context.mem_iff.mpr (List.mem_append.mpr (Or.inl partMember))
  have wholeMember : (token,wholeTree) ∈ wholeBefore :=
    (take_perm wholeRead).mem_iff.mpr List.mem_cons_self
  have sameCell := map_unique Prod.fst wholeBefore unique
    (token,wholeTree) wholeMember (token,partTree) originalMember rfl
  have sameTree : wholeTree = partTree := congrArg Prod.snd sameCell
  have wholePerm := take_perm wholeRead
  rw [sameTree] at wholePerm
  have partPerm := (take_perm partRead).append_right spectators
  have after : wholeAfter.Perm (partAfter ++ spectators) :=
    List.Perm.cons_inv (wholePerm.symm.trans (context.trans partPerm))
  exact ⟨sameTree,after,take_unique unique wholeRead⟩

private theorem put_result {token : Nat} {tree : RawOwnerFlow.Tree} {before after : RawOwnerFlow.Frame}
    (ran : RawOwnerFlow.put token tree before = some after) : after = (token,tree) :: before := by
  unfold RawOwnerFlow.put at ran
  split at ran
  · cases ran
  · exact (Option.some.inj ran).symm

private theorem put_unique {token : Nat} {tree : RawOwnerFlow.Tree} {before after : RawOwnerFlow.Frame}
    (unique : (before.map Prod.fst).Nodup)
    (ran : RawOwnerFlow.put token tree before = some after) : (after.map Prod.fst).Nodup := by
  unfold RawOwnerFlow.put at ran
  split at ran
  · cases ran
  · rename_i absent
    have same : after = (token,tree) :: before := (Option.some.inj ran).symm
    rw [same]
    change (token :: before.map Prod.fst).Nodup
    apply List.nodup_cons.mpr
    constructor
    · intro member
      obtain ⟨cell,present,key⟩ := List.mem_map.mp member
      exact absent (List.any_eq_true.mpr ⟨cell,present,beq_iff_eq.mpr key⟩)
    · exact unique

/-- Inserting the same complete Tree in both actual flows preserves every
spectator cell. A collision is excluded by the actual successful caller put,
not by a new freshness or width assumption. -/
theorem put_extension {output : Nat} {tree : RawOwnerFlow.Tree}
    {partBefore wholeBefore spectators partAfter wholeAfter : RawOwnerFlow.Frame}
    (context : wholeBefore.Perm (partBefore ++ spectators))
    (unique : (wholeBefore.map Prod.fst).Nodup)
    (partRead : RawOwnerFlow.put output tree partBefore = some partAfter)
    (wholeRead : RawOwnerFlow.put output tree wholeBefore = some wholeAfter) :
    wholeAfter.Perm (partAfter ++ spectators) ∧ (wholeAfter.map Prod.fst).Nodup := by
  refine ⟨?_,put_unique unique wholeRead⟩
  rw [put_result wholeRead,put_result partRead]
  exact List.Perm.cons (output,tree) context

/-- One actual move extends through the untouched caller forest. This is the
owner-flow step used by gate/applyUnitary; it grants no operation equation or
new native execution path. It preserves distinct empty spectators as cells. -/
theorem move_extension {input output : Nat}
    {partBefore wholeBefore spectators partAfter wholeAfter : RawOwnerFlow.Frame}
    (context : wholeBefore.Perm (partBefore ++ spectators))
    (unique : (wholeBefore.map Prod.fst).Nodup)
    (partRead : RawOwnerFlow.move input output partBefore = some partAfter)
    (wholeRead : RawOwnerFlow.move input output wholeBefore = some wholeAfter) :
    wholeAfter.Perm (partAfter ++ spectators) ∧ (wholeAfter.map Prod.fst).Nodup := by
  unfold RawOwnerFlow.move at partRead wholeRead
  obtain ⟨⟨partTree,partRest⟩,partTaken,partPut⟩ := Option.bind_eq_some_iff.mp partRead
  obtain ⟨⟨wholeTree,wholeRest⟩,wholeTaken,wholePut⟩ := Option.bind_eq_some_iff.mp wholeRead
  have taken := take_extension context unique partTaken wholeTaken
  have afterUnique := put_unique taken.2.2 wholePut
  refine ⟨?_,afterUnique⟩
  rw [put_result wholePut,put_result partPut,taken.1]
  exact List.Perm.cons (output,partTree) taken.2.1

#print axioms take_extension
#print axioms take_partition
#print axioms put_extension
#print axioms move_extension

end Qleisli.RuntimeOwnerFlowExtension
