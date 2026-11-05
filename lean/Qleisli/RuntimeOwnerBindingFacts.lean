import QleisliKernel.Qirf.RuntimeOwnerTransition
import QleisliKernel.Qirf.RuntimeSelectionPartition

/-! Lightweight facts for the same original seed/resolve/order receipts.
These are the unchanged technical definitions and proofs used by the concrete
owner-transition consumers. They add no acceptance, frame transport or code
equation and import no complex-action or Mathlib proof closure.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeOwnerTransitionAction
open QleisliKernel QleisliKernel.Finite
open QleisliKernel.Semantics
open QleisliKernel.Qirf
open QleisliKernel.Qirf.RuntimeOwnerMap (Binding Map)

def seedCell (binding : Binding) : Nat × RawOwnerFlow.Tree :=
  (binding.port.token,.owner binding.owner binding.port.bits)

theorem put_result (token : Nat) (tree : RawOwnerFlow.Tree) (before after : RawOwnerFlow.Frame)
    (ran : RawOwnerFlow.put token tree before = some after) : after = (token,tree)::before := by
  unfold RawOwnerFlow.put at ran
  split at ran
  · cases ran
  · exact (Option.some.inj ran).symm

private theorem seed_fold (bindings : Map) : ∀ initial final : RawOwnerFlow.Frame,
    bindings.foldlM (fun current binding => RawOwnerFlow.put binding.port.token
      (.owner binding.owner binding.port.bits) current) initial = some final →
    ∀ cell ∈ final,cell ∈ initial ∨ ∃ binding ∈ bindings,cell = seedCell binding := by
  induction bindings with
  | nil =>
    intro initial final ran cell member
    have same : initial = final := Option.some.inj ran
    subst final
    exact Or.inl member
  | cons first rest ih =>
    intro initial final ran cell member
    simp only [List.foldlM_cons] at ran
    obtain ⟨next,head,tail⟩ := Option.bind_eq_some_iff.mp ran
    have same := put_result first.port.token (.owner first.owner first.port.bits) initial next head
    rcases ih next final tail cell member with present | supplied
    · rw [same] at present
      rcases List.mem_cons.mp present with equal | old
      · exact Or.inr ⟨first,List.mem_cons_self,equal⟩
      · exact Or.inl old
    · obtain ⟨binding,inside,equal⟩ := supplied
      exact Or.inr ⟨binding,List.mem_cons_of_mem _ inside,equal⟩

theorem seed_origins (bindings : Map) (initial : RawOwnerFlow.Frame)
    (ran : RawOwnerFlow.seed (bindings.map (·.owner)) (bindings.map (·.port)) = some initial) :
    ∀ cell ∈ initial,∃ binding ∈ bindings,cell = seedCell binding := by
  have folded : bindings.foldlM (fun current binding => RawOwnerFlow.put binding.port.token
      (.owner binding.owner binding.port.bits) current) [] = some initial := by
    simpa [RawOwnerFlow.seed,List.zip_map',List.foldlM_map] using ran
  intro cell member
  rcases seed_fold bindings [] initial folded cell member with impossible | supplied
  · cases impossible
  · exact supplied

private theorem resolve_result (state : QleisliKernel.Raw.Observation.State) (cell : Nat × RawOwnerFlow.Tree)
    (binding : Binding) (work left : Nat)
    (ran : (RuntimeOwnerTransition.resolve state cell).run work = (.ok binding,left)) :
    cell = (binding.port.token,.owner binding.owner binding.port.bits) ∧ binding.port ∈ state.quantum.live := by
  obtain ⟨token,tree⟩ := cell
  cases tree with
  | pair _ _ _ =>
    have impossible : (Except.error Error.request : Except Error Binding) = .ok binding := congrArg Prod.fst ran
    cases impossible
  | owner role bits =>
    cases found : state.quantum.live.find? (fun port => port.token == token) with
    | none =>
      have impossible : (Except.error Error.request : Except Error Binding) = .ok binding := by
        simpa only [RuntimeOwnerTransition.resolve,found] using congrArg Prod.fst ran
      cases impossible
    | some port =>
      have performed : ((do
          guard (port.bits == bits) .request
          pure (⟨role,port⟩ : Binding)) : Finite.WorkM Binding).run work = (.ok binding,left) := by
        simpa only [RuntimeOwnerTransition.resolve,found] using ran
      obtain ⟨_unit,middle,guardRead,returned⟩ := bind_success _ _ _ _ _ performed
      have same : binding = ⟨role,port⟩ := (pure_success _ _ _ _ returned).1
      subst binding
      have sameBits : port.bits = bits := beq_iff_eq.mp (guard_success _ _ _ _ guardRead).1
      have sameToken : port.token = token := beq_iff_eq.mp
        (List.find?_some (p := fun candidate : QleisliKernel.Semantics.Raw.Port => candidate.token == token) found)
      exact ⟨by simp only [sameToken,sameBits],List.mem_of_find?_eq_some found⟩

theorem resolved_origins (state : QleisliKernel.Raw.Observation.State) (cells : RawOwnerFlow.Frame) :
    ∀ (moved : Map) work left,
      ((cells.mapM (RuntimeOwnerTransition.resolve state)).run work = (.ok moved,left)) →
        ∀ binding ∈ moved,∃ cell ∈ cells,
          cell = (binding.port.token,.owner binding.owner binding.port.bits) ∧ binding.port ∈ state.quantum.live := by
  induction cells with
  | nil =>
    intro moved work left ran binding member
    have same : moved = [] := (pure_success _ _ _ _ ran).1
    subst moved
    cases member
  | cons cell cells ih =>
    intro moved work left ran binding member
    simp only [List.mapM_cons] at ran
    obtain ⟨first,middle,head,rest⟩ := bind_success _ _ _ _ _ ran
    obtain ⟨tail,last,tailRead,returned⟩ := bind_success _ _ _ _ _ rest
    have same : moved = first::tail := (pure_success _ _ _ _ returned).1
    subst moved
    rcases List.mem_cons.mp member with equal | later
    · subst binding
      exact ⟨cell,List.mem_cons_self,resolve_result state cell first work middle head⟩
    · obtain ⟨entry,present,facts⟩ := ih tail middle last tailRead binding later
      exact ⟨entry,List.mem_cons_of_mem _ present,facts⟩

theorem map_unique {α β : Type} (f : α → β) (values : List α) :
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

end Qleisli.RuntimeOwnerTransitionAction
