import QleisliKernel.Raw.Observation
import QleisliKernel.Semantics.ClassicalScope

/-! The actual original-operation verifier establishes lexical classical SSA.
Both exclusive arms are checked and share the global issued-name history.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Raw.Observation
open Semantics.Raw Semantics.Observation Semantics.Finite Finite
namespace Scope

def view (state : State) : Semantics.ClassicalScope.State :=
  ⟨state.classical,state.active,state.scope,state.nextScope⟩

theorem visible (state : State) (value : Nat) (ok : Observation.visible state value = true) :
    Semantics.ClassicalScope.Visible (view state) value := by
  simp only [Observation.visible,List.any_eq_true,Bool.and_eq_true,beq_iff_eq,List.contains_iff_mem] at ok
  obtain ⟨⟨actual,scope⟩,member,same,active⟩ := ok
  exact ⟨scope,same ▸ member,active⟩

theorem visibleArm (state : State) (arm value : Nat) (ok : Observation.visibleArm state arm value = true) :
    Semantics.ClassicalScope.ArmVisible (view state) arm value := by
  simp only [Observation.visibleArm,List.any_eq_true,Bool.and_eq_true,Bool.or_eq_true,
    beq_iff_eq,List.contains_iff_mem] at ok
  obtain ⟨⟨actual,scope⟩,member,same,active⟩ := ok
  exact ⟨scope,same ▸ member,active⟩

theorem insert (state next : State) (value : Nat) (ok : insertClassical state value = .ok next) :
    Semantics.ClassicalScope.Insert (view state) value (view next) := by
  obtain ⟨_,condition,h⟩ := except_bind_success _ _ _ ok
  have same := Except.ok.inj h
  subst next
  have valid := Raw.require_success _ condition
  simp only [Bool.and_eq_true] at valid
  exact ⟨by simpa [view] using valid.2,rfl⟩

theorem inserts {A : Type} (items : List A) (value : A → Nat) (state next : State)
    (ok : items.foldlM (fun state item => insertClassical state (value item)) state = .ok next) :
    Semantics.ClassicalScope.Inserts (view state) (items.map value) (view next) := by
  induction items generalizing state with
  | nil => have same := Except.ok.inj ok; subst next; exact .nil _
  | cons item items ih =>
    simp only [List.foldlM_cons] at ok
    obtain ⟨middle,hi,rest⟩ := except_bind_success _ _ _ ok
    exact .cons _ _ _ _ _ (insert _ _ _ hi) (ih middle rest)

theorem consume (state next : State) (input : Nat) (port : Port)
    (ok : Observation.consume state input = .ok (port,next)) : view next = view state := by
  obtain ⟨⟨found,after⟩,_,h⟩ := except_bind_success _ _ _ ok
  have same := Except.ok.inj h
  cases same
  rfl

end Scope
open Scope (view)

theorem checkStep_scope (dependencies : List Dependency)
    (recurse : State → List Semantics.Observation.Op → WorkM State)
    (sound : ∀ state ops next work left, (recurse state ops).run work = (.ok next,left) →
      Semantics.ClassicalScope.Run (view state) ops (view next))
    (state next : State) (op : Semantics.Observation.Op) (work left : Nat)
    (ok : (checkStep dependencies recurse state op).run work = (.ok next,left)) :
    Semantics.ClassicalScope.Step (view state) op (view next) := by
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨result,_,hbody,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  subst next
  cases op with
  | pure operation =>
    obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ hbody
    obtain ⟨transition,_,_,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
    have same := (pure_success _ _ _ _ h).1
    subst result
    exact .pure _ _
  | measure input output =>
    obtain ⟨⟨port,consumed⟩,_,hc,h⟩ := bind_success _ _ _ _ _ hbody
    obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨fresh,_,hf,h⟩ := bind_success _ _ _ _ _ h
    have same := (pure_success _ _ _ _ h).1
    subst result
    have issued := Scope.insert _ _ _ (lift_success _ _ _ _ hf).1
    rw [Scope.consume _ _ _ _ (lift_success _ _ _ _ hc).1] at issued
    exact .measure _ _ _ _ issued
  | reset input output wire =>
    obtain ⟨⟨port,consumed⟩,_,hc,h⟩ := bind_success _ _ _ _ _ hbody
    obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨quantum,_,_,h⟩ := bind_success _ _ _ _ _ h
    have same := (pure_success _ _ _ _ h).1
    subst result
    change Semantics.ClassicalScope.Step (view state) _ (view consumed)
    rw [Scope.consume _ _ _ _ (lift_success _ _ _ _ hc).1]
    exact .reset _ _ _ _
  | discard input =>
    obtain ⟨⟨port,consumed⟩,_,hc,h⟩ := bind_success _ _ _ _ _ hbody
    have same := (pure_success _ _ _ _ h).1
    subst result
    change Semantics.ClassicalScope.Step (view state) _ (view consumed)
    rw [Scope.consume _ _ _ _ (lift_success _ _ _ _ hc).1]
    exact .discard _ _
  | constant value output => exact .constant _ _ _ _ (Scope.insert _ _ _ (lift_success _ _ _ _ hbody).1)
  | not input output =>
    obtain ⟨_,_,hg,h⟩ := bind_success _ _ _ _ _ hbody
    exact .not _ _ _ _ (Scope.visible _ _ (guard_success _ _ _ _ hg).1)
      (Scope.insert _ _ _ (lift_success _ _ _ _ h).1)
  | xor l r output | and l r output =>
    obtain ⟨_,_,hg,h⟩ := bind_success _ _ _ _ _ hbody
    have access := (guard_success _ _ _ _ hg).1
    simp only [Bool.and_eq_true] at access
    first
    | exact .xor _ _ _ _ _ (Scope.visible _ _ access.1) (Scope.visible _ _ access.2)
        (Scope.insert _ _ _ (lift_success _ _ _ _ h).1)
    | exact .and _ _ _ _ _ (Scope.visible _ _ access.1) (Scope.visible _ _ access.2)
        (Scope.insert _ _ _ (lift_success _ _ _ _ h).1)
  | branch condition thenOps elseOps quantum classical =>
    obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ hbody
    obtain ⟨_,_,hg,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨thenState,_,ht,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨elseState,_,he,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨_,_,hp,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨merged,_,_,h⟩ := bind_success _ _ _ _ _ h
    have destinations := Scope.inserts _ ClassicalPhi.output _ _ (lift_success _ _ _ _ h).1
    have operands := (guard_success _ _ _ _ hp).1
    simp only [List.all_eq_true,Bool.and_eq_true] at operands
    exact .branch _ _ _ _ _ _ (view thenState) (view elseState) _
      (Scope.visible _ _ (guard_success _ _ _ _ hg).1) (sound _ _ _ _ _ ht)
      (sound _ _ _ _ _ he)
      (fun phi member => ⟨Scope.visibleArm _ _ _ (operands phi member).1,
        Scope.visibleArm _ _ _ (operands phi member).2⟩) destinations

private theorem fold_scope (dependencies : List Dependency)
    (recurse : State → List Semantics.Observation.Op → WorkM State)
    (sound : ∀ state ops next work left, (recurse state ops).run work = (.ok next,left) →
      Semantics.ClassicalScope.Run (view state) ops (view next))
    (ops : List Semantics.Observation.Op) (state next : State) (work left : Nat)
    (ok : (ops.foldlM (checkStep dependencies recurse) state).run work = (.ok next,left)) :
    Semantics.ClassicalScope.Run (view state) ops (view next) := by
  induction ops generalizing state work with
  | nil => have same := (pure_success _ _ _ _ ok).1; subst next; exact .nil _
  | cons op ops ih =>
    simp only [List.foldlM_cons] at ok
    obtain ⟨middle,b,head,rest⟩ := bind_success _ _ _ _ _ ok
    exact .cons _ _ _ _ _ (checkStep_scope _ _ sound _ _ _ _ _ head) (ih middle b rest)

theorem checkOps_scope (dependencies : List Dependency) (fuel : Nat)
    (state next : State) (ops : List Semantics.Observation.Op) (work left : Nat)
    (ok : (checkOps dependencies fuel state ops).run work = (.ok next,left)) :
    Semantics.ClassicalScope.Run (view state) ops (view next) := by
  induction fuel generalizing state next ops work left with
  | zero => cases ok
  | succ fuel ih =>
    obtain ⟨result,b,hops,h⟩ := bind_success _ _ _ _ _ ok
    obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
    have same := (pure_success _ _ _ _ h).1
    subst next
    exact fold_scope _ _ (fun state ops next work left ok => ih state next ops work left ok)
      ops state result work b hops

theorem verify_scopeSafe (dependencies : List Dependency) (program : Semantics.Observation.Program)
    (checked : Checked) (work left : Nat)
    (ok : (verify dependencies program).run work = (.ok checked,left)) :
    Semantics.ClassicalScope.ScopeSafe program := by
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨quantum,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨initial,a,hi,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨state,b,hops,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,hout,_⟩ := bind_success _ _ _ _ _ h
  have inputs := Scope.inserts _ id _ _ (lift_success _ _ _ _ hi).1
  have outputs := (guard_success _ _ _ _ hout).1
  simp only [outputValid,Bool.and_eq_true,List.all_eq_true] at outputs
  refine ⟨view initial,view state,?_,checkOps_scope _ _ _ _ _ _ _ hops,?_⟩
  · simpa only [List.map_id] using inputs
  · intro value member
    exact Scope.visible _ _ (outputs.1.1.2 value member)

end QleisliKernel.Raw.Observation
