import QleisliKernel.Qirf.RuntimeInterval

/-! Successful boundary states are independent of the budget on which each
original mixed check returned. Nothing here states that two budgets have the
same failures, or the same work remaining.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeAdjacentSlices
open QleisliKernel QleisliKernel.Finite QleisliKernel.Qirf
open QleisliKernel.Semantics.Finite
open RuntimeInterval (Computed)

private def Single {α : Type} (action : WorkM α) : Prop :=
  ∀ {x y}, Computed action x → Computed action y → x = y

private theorem singleUnit (action : WorkM Unit) : Single action :=
  fun {_ _} _ _ => Subsingleton.elim _ _

private theorem singlePure {α : Type} (x : α) : Single (pure x : WorkM α) := by
  rintro a b ⟨w,l,ha⟩ ⟨v,k,hb⟩
  exact (pure_success _ _ _ _ ha).1.trans (pure_success _ _ _ _ hb).1.symm

private theorem singleThrow {α : Type} (e : Error) : Single (throw e : WorkM α) := by
  rintro a _ ⟨w,l,ha⟩
  cases ha

private theorem singleLift {α : Type} (read : Except Error α) : Single (lift read) := by
  rintro a b ⟨w,l,ha⟩ ⟨v,k,hb⟩
  exact Except.ok.inj ((lift_success read a w l ha).1.symm.trans (lift_success read b v k hb).1)

private theorem singleBind {α β : Type} {first : WorkM α} {next : α → WorkM β}
    (one : Single first) (more : ∀ x, Single (next x)) : Single (first >>= next) := by
  rintro a b ⟨w,l,ha⟩ ⟨v,k,hb⟩
  obtain ⟨x,i,firstA,nextA⟩ := bind_success first next w l a ha
  obtain ⟨y,j,firstB,nextB⟩ := bind_success first next v k b hb
  have same := one ⟨w,i,firstA⟩ ⟨v,j,firstB⟩
  subst y
  exact more x ⟨i,l,nextA⟩ ⟨j,k,nextB⟩

private theorem singleFold {α β : Type} (step : β → α → WorkM β)
    (one : ∀ state op, Single (step state op)) (ops : List α) (entry : β) :
    Single (ops.foldlM step entry) := by
  induction ops generalizing entry with
  | nil => exact singlePure entry
  | cons op rest ih =>
    rw [List.foldlM_cons]
    exact singleBind (one entry op) ih

private theorem singleAction (deps : List Dependency)
    (recurse : Raw.Observation.State → List Semantics.Observation.Op → WorkM Raw.Observation.State)
    (one : ∀ state ops, Single (recurse state ops))
    (state : Raw.Observation.State) (op : Semantics.Observation.Op) :
    Single (Raw.Observation.checkAction deps recurse state op) := by
  cases op <;> unfold Raw.Observation.checkAction <;>
    repeat' first
      | with_reducible exact singleUnit _
      | with_reducible exact singlePure _
      | with_reducible exact singleLift _
      | with_reducible exact one _ _
      | with_reducible apply singleBind
      | rintro (⟨_, _⟩ : Prod _ _)
      | intro x
      | split

private theorem singleStep (deps : List Dependency)
    (recurse : Raw.Observation.State → List Semantics.Observation.Op → WorkM Raw.Observation.State)
    (one : ∀ state ops, Single (recurse state ops))
    (state : Raw.Observation.State) (op : Semantics.Observation.Op) :
    Single (Raw.Observation.checkStep deps recurse state op) := by
  unfold Raw.Observation.checkStep
  apply singleBind (singleUnit _)
  intro _
  apply singleBind (singleUnit _)
  intro _
  apply singleBind (singleAction deps recurse one state op)
  intro result
  exact singleBind (singleUnit _) (fun _ => singlePure result)

private theorem singleOps (deps : List Dependency) (fuel : Nat) (state : Raw.Observation.State)
    (ops : List Semantics.Observation.Op) : Single (Raw.Observation.checkOps deps fuel state ops) := by
  induction fuel generalizing state ops with
  | zero => exact singleThrow .limit
  | succ fuel ih =>
    let step := Raw.Observation.checkStep deps (Raw.Observation.checkOps deps fuel)
    apply singleBind (singleFold step (singleStep deps _ ih) ops state)
    intro result
    exact singleBind (singleUnit _) (fun _ => singlePure result)

private theorem underlying {deps fuel initial ops result}
    (read : Computed (Raw.Observation.checkOps deps (fuel+1) initial ops) result) :
    Computed (ops.foldlM (Raw.Observation.checkStep deps (Raw.Observation.checkOps deps fuel)) initial) result := by
  obtain ⟨w,l,ran⟩ := read
  obtain ⟨state,i,fold,rest⟩ := bind_success _ _ _ _ _ ran
  obtain ⟨_,j,_,done_⟩ := bind_success _ _ _ _ _ rest
  have same := (pure_success state result j l done_).1
  subst result
  exact ⟨w,i,fold⟩

theorem prefixSplit {α : Type} (xs : List α) (offset count : Nat) :
    xs.take (offset+count) = xs.take offset ++ (xs.drop offset).take count := by
  induction offset generalizing xs with
  | zero => simp
  | succ offset ih =>
    cases xs with
    | nil => simp
    | cons x xs => simpa only [Nat.succ_add,List.take_succ_cons,List.drop_succ_cons,List.cons_append,
        List.cons.injEq,true_and] using ih xs

/-- Adjacency is by position in one actual block, not by comparison of printed
frames. The equality is of the full observing state, including history. -/
theorem adjacent {deps program} {block : RuntimeInterval.Block deps program} {start count nextCount}
    (first : RuntimeInterval.Checked block start count) (next : RuntimeInterval.Checked block (start+count) nextCount) :
    first.after = next.before := by
  cases depth : block.fuel with
  | zero =>
    obtain ⟨w,l,ran⟩ := first.prefixRead
    rw [depth] at ran
    cases ran
  | succ fuel =>
    have firstPrefix := first.prefixRead
    have firstInterval := first.intervalRead
    have secondPrefix := next.prefixRead
    rw [depth] at firstPrefix firstInterval secondPrefix
    let step := Raw.Observation.checkStep deps (Raw.Observation.checkOps deps fuel)
    have one := singleFold step (singleStep deps _ (singleOps deps fuel))
    obtain ⟨w,l,long⟩ := underlying secondPrefix
    rw [prefixSplit block.operations start count,List.foldlM_append] at long
    obtain ⟨middle,i,pre,slice⟩ := bind_success _ _ w l next.before long
    have atStart := one (block.operations.take start) block.entry (underlying firstPrefix) ⟨w,i,pre⟩
    subst middle
    exact one ((block.operations.drop start).take count) first.before (underlying firstInterval) ⟨i,l,slice⟩

#print axioms adjacent
end Qleisli.RuntimeAdjacentSlices
