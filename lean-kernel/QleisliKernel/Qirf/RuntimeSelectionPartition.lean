import QleisliKernel.Qirf.RuntimeLocalEvents
import QleisliKernel.Raw.Ownership

/-! Partition an authentic runtime interval's complete owner map. Uniqueness
comes from its actual Raw input gate, including owners with no wires; distinct
physical axes alone cannot supply it. Selected bindings come from the existing
original-owner lookup, and every spectator keeps its original relative order.
This proof adds no reject gate, code availability, logical recoding, Gram
check or accepted handle. Mixed-radix and physical permutations remain separate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace QleisliKernel.Qirf.RuntimeSelectionPartition
open QleisliKernel Finite
open RuntimeOwnerMap (Binding Map Owner)

private theorem inputs_live {before ports after} (read : Semantics.Ownership.Inputs before ports after) :
    after.live = before.live ++ ports := by
  induction read with
  | nil => simp
  | cons before port middle ports after head tail ih =>
    rw [ih,head.result]
    simp only [List.append_assoc,List.cons_append,List.nil_append]

/-- The same successful pureRead rejects duplicate owner tokens even when
the selected owners have empty wire lists. There is no new uniqueness check. -/
theorem interval_selected_tokens {dependencies program block arity start count inputs outputs roles}
    (interval : @RuntimePureInterval.Checked dependencies program block arity start count inputs outputs roles) :
    (interval.selected.map (·.token)).Nodup := by
  obtain ⟨work,left,ran⟩ := interval.pureRead
  have prepared := (Raw.Pure.verify_conditions _ _ _ work left ran).1
  obtain ⟨initial,_body,initialized,_operations,_outputs,_state,_trace⟩ := Raw.prepare_conditions _ _ _ prepared
  have valid := Raw.inputs_valid interval.selected {} initial (by decide) initialized
  have unique := (Raw.Ownership.valid initial valid).owners
  have original : initial.live = interval.selected := by
    simpa only [Raw.Ownership.view,List.nil_append] using
      inputs_live (Raw.Ownership.inputs interval.selected {} initial initialized)
  change (initial.live.map (·.token)).Nodup at unique
  simpa only [original] using unique

private theorem order_map_values (all : Map) (roles : List Owner) : ∀ (selected : Map) (work left : Nat),
    ((roles.mapM (fun owner => do
      let some binding := RuntimeOwnerMap.byOwner all owner | throw .request
      pure binding) : WorkM Map).run work = (.ok selected,left)) →
      selected ⊆ all ∧ selected.map (·.owner) = roles := by
  induction roles with
  | nil =>
    intro selected work left ran
    have same : selected = [] := (pure_success _ _ _ _ ran).1
    subst selected
    exact ⟨by simp,rfl⟩
  | cons owner roles ih =>
    intro selected work left ran
    simp only [List.mapM_cons] at ran
    obtain ⟨first,middle,firstRead,rest⟩ := bind_success _ _ _ _ _ ran
    obtain ⟨tail,last,tailRead,returned⟩ := bind_success _ _ _ _ _ rest
    have same : selected = first::tail := (pure_success _ _ _ _ returned).1
    subst selected
    have firstFacts : first ∈ all ∧ first.owner = owner := by
      cases found : RuntimeOwnerMap.byOwner all owner with
      | none =>
        have impossible : (Except.error Error.request : Except Error Binding) = .ok first := by
          simpa only [found] using congrArg Prod.fst firstRead
        cases impossible
      | some original =>
        have performed : (pure original : WorkM Binding).run work = (.ok first,middle) := by
          simpa only [found] using firstRead
        have equal : first = original := (pure_success _ _ _ _ performed).1
        subst first
        have lookup : all.find? (fun binding => binding.owner == owner) = some original := found
        exact ⟨List.mem_of_find?_eq_some lookup,
          beq_iff_eq.mp (List.find?_some (p := fun binding : Binding => binding.owner == owner) lookup)⟩
    have tailFacts := ih tail middle last tailRead
    constructor
    · intro binding member
      rcases List.mem_cons.mp member with equal | later
      · subst binding
        exact firstFacts.1
      · exact tailFacts.1 later
    · simp only [List.map_cons,firstFacts.2,tailFacts.2]

/-- Preserve the exact original binding and source-owner result of the same
budgeted order invocation, including unused and zero-width selected owners. -/
theorem order_values (all : Map) (roles : List Owner) (selected : Map)
    (read : RuntimeInterval.Computed (RuntimeOwnerMap.order roles all) selected) :
    selected ⊆ all ∧ selected.map (·.owner) = roles := by
  obtain ⟨work,left,ran⟩ := read
  unfold RuntimeOwnerMap.order at ran
  obtain ⟨_charged,middle,_charge,mapped⟩ := bind_success _ _ _ _ _ ran
  exact order_map_values all roles selected middle left mapped

private theorem nodup_of_tokens (bindings : Map) (unique : (bindings.map (fun binding => binding.port.token)).Nodup) :
    bindings.Nodup :=
  List.Pairwise.of_map (fun binding : Binding => binding.port.token)
    (fun _ _ different equal => different (congrArg (fun binding : Binding => binding.port.token) equal)) unique

private theorem nodup_perm {α : Type} [DecidableEq α] (first : List α) : ∀ second : List α,
    first.Nodup → second.Nodup → (∀ value,value ∈ first ↔ value ∈ second) → first.Perm second := by
  induction first with
  | nil =>
    intro second _firstUnique _secondUnique members
    cases second with
    | nil => exact .refl _
    | cons value rest =>
      have impossible := (members value).mpr (List.mem_cons_self)
      cases impossible
  | cons head first ih =>
    intro second firstUnique secondUnique members
    obtain ⟨before,after,equal⟩ := List.append_of_mem ((members head).mp (List.mem_cons_self))
    subst second
    have moved : (before ++ head::after).Perm (head::(before ++ after)) := List.perm_middle
    have remaining := List.nodup_cons.mp (moved.nodup secondUnique)
    have original := List.nodup_cons.mp firstUnique
    have restMembers : ∀ value,value ∈ first ↔ value ∈ before ++ after := by
      intro value
      by_cases same : value = head
      · subst value
        exact iff_of_false original.1 remaining.1
      · have relation := (members value).trans moved.mem_iff
        simpa only [List.mem_cons,same,false_or] using relation
    exact ((ih _ original.2 remaining.2 restMembers).cons head).trans moved.symm

/-- Exact binding membership, rather than physical axes, determines the
spectators. Filtering retains their original order and every zero-width entry. -/
def complement (all selected : Map) : Map :=
  all.filter (fun binding => !decide (binding ∈ selected))

theorem complement_original (all selected : Map) : (complement all selected).Sublist all :=
  List.filter_sublist

private theorem partition_perm (all selected : Map) (allUnique : all.Nodup) (selectedUnique : selected.Nodup)
    (subset : selected ⊆ all) : (selected ++ complement all selected).Perm all := by
  let chosen : Binding → Bool := fun binding => decide (binding ∈ selected)
  have selectedPerm : selected.Perm (all.filter chosen) := by
    apply nodup_perm selected _ selectedUnique (List.Pairwise.filter chosen allUnique)
    intro binding
    simp only [List.mem_filter,chosen,decide_eq_true_eq]
    exact ⟨fun member => ⟨subset member,member⟩,fun member => member.2⟩
  exact (selectedPerm.append_right (complement all selected)).trans (List.filter_append_perm chosen all)

/-- This consumes the authentic interval's existing selectedPorts equality
and pureRead. No fresh or caller-supplied uniqueness invariant is admitted. -/
theorem selection_partition {dependencies program block arity start count inputs outputs roles}
    (interval : @RuntimePureInterval.Checked dependencies program block arity start count inputs outputs roles)
    {beforeRoles} (before : RuntimeOwnerMap.Checked beforeRoles interval.interval.before)
    (selection : RuntimeScatterTransport.Selection before)
    (selectedPorts : selection.selected.map (·.port) = interval.selected) :
    (selection.selected.map (fun binding => binding.port.token)).Nodup ∧
      selection.selected.Nodup ∧ selection.selected ⊆ before.bindings ∧
      selection.selected.map (·.owner) = selection.selectedRoles ∧
      (complement before.bindings selection.selected).Sublist before.bindings ∧
      (selection.selected ++ complement before.bindings selection.selected).Perm before.bindings := by
  have unique : (selection.selected.map (fun binding => binding.port.token)).Nodup := by
    have authentic := interval_selected_tokens interval
    rw [← selectedPorts,List.map_map] at authentic
    exact authentic
  have distinct := nodup_of_tokens selection.selected unique
  have original := order_values _ _ _ selection.selectedRead
  exact ⟨unique,distinct,original.1,original.2,complement_original _ _,
    partition_perm _ _ (nodup_of_tokens before.bindings before.tokensDistinct) distinct original.1⟩

/-- Literal local-event subjects already retain all inputs of the derived
partition theorem. The full original owner/wire identities are unchanged. -/
theorem literal_partition
    {dependencies program block start count inputs outputs roles frame selectorBits targetBits retained restricted
      beforeRoles afterRoles before after}
    (checked : @RuntimeLocalEvents.Literal dependencies program block start count inputs outputs roles frame selectorBits
      targetBits retained restricted beforeRoles afterRoles before after) :
    (checked.selection.selected.map (fun binding => binding.port.token)).Nodup ∧
      checked.selection.selected.Nodup ∧ checked.selection.selected ⊆ before.bindings ∧
      checked.selection.selected.map (·.owner) = checked.selection.selectedRoles ∧
      (complement before.bindings checked.selection.selected).Sublist before.bindings ∧
      (checked.selection.selected ++ complement before.bindings checked.selection.selected).Perm before.bindings :=
  selection_partition frame before checked.selection checked.selectedPorts

private theorem find_port (live : List Semantics.Raw.Port) (port : Semantics.Raw.Port)
    (unique : (live.map (·.token)).Nodup) (present : port ∈ live) :
    live.find? (fun p => p.token == port.token) = some port := by
  induction live with
  | nil => cases present
  | cons first rest ih =>
    have distinct := List.nodup_cons.mp unique
    rcases List.mem_cons.mp present with same | member
    · subst first
      simp
    · have different : first.token ≠ port.token := by
        intro equal
        apply distinct.1
        change first.token ∈ rest.map (·.token)
        rw [equal]
        exact List.mem_map_of_mem member
      have skip : (first.token == port.token) = false :=
        Bool.eq_false_iff.mpr (fun equal => different (beq_iff_eq.mp equal))
      simpa only [List.find?, skip] using ih distinct.2 member

private theorem pair_ports {roles state requested} (caller : RuntimeOwnerMap.Checked roles state)
    (pair : RuntimeOwnerTransition.Pair requested caller.bindings) :
    PureInterval.ports state [pair.first.port.token,pair.second.port.token] =
      some [pair.first.port,pair.second.port] := by
  have contained := (order_values _ _ _ pair.ordered).1
  have live (b : Binding) (h : b ∈ [pair.first,pair.second]) : b.port ∈ state.quantum.live :=
    caller.complete.mem_iff.mp (List.mem_map_of_mem (contained h))
  have distinct : (state.quantum.live.map (·.token)).Nodup :=
    (caller.complete.map (fun p => p.token)).nodup_iff.mp
      (by simpa only [List.map_map, Function.comp_def] using caller.tokensDistinct)
  have first := find_port _ _ distinct (live pair.first (by simp))
  have second := find_port _ _ distinct (live pair.second (by simp))
  simp [PureInterval.ports, PureInterval.portsOf, List.mapM_cons, first, second]

/-- The ports used in the local sector are the original source-role lookups
on both sides, down to the wire vectors and tokens of zero-width owners. -/
theorem source_ports {dependencies program block start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs roles)
    (source : RuntimeOwnerTransition.Selection frame.interval inputs outputs roles) :
    frame.selected = [source.selected.first.port,source.selected.second.port] ∧
    frame.returned = [source.returned.first.port,source.returned.second.port] := by
  have entry := congrArg (PureInterval.ports frame.interval.before) source.inputTokens
  have exit := congrArg (PureInterval.ports frame.interval.after) source.outputTokens
  exact ⟨Option.some.inj (frame.atEntry.symm.trans (entry.trans (pair_ports source.before source.selected))),
    Option.some.inj (frame.atExit.symm.trans (exit.trans (pair_ports source.transport.after source.returned)))⟩

/-- The actual pure-program output check supplies distinct returned tokens.
This includes separate zero-width owners. -/
private theorem output_tokens {dependencies program block arity start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block arity start count inputs outputs roles) :
    outputs.Nodup := by
  obtain ⟨work,left,ran⟩ := frame.pureRead
  have prepared := (Raw.Pure.verify_conditions _ _ _ work left ran).1
  obtain ⟨_,_,_,_,valid,_,_⟩ := Raw.prepare_conditions _ _ _ prepared
  simp only [Raw.outputValid, Bool.and_eq_true, RuntimePureInterval.fragment] at valid
  exact Raw.Ownership.unique_nodup outputs valid.1.1.1.1

/-- Gather the two source returns first and keep their spectators in the
original output order. Every original binding occurs exactly once. -/
theorem source_output_partition {dependencies program block start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs roles)
    (source : RuntimeOwnerTransition.Selection frame.interval inputs outputs roles) :
    (source.returned.toList ++ complement source.transport.after.bindings source.returned.toList).Perm
      source.transport.after.bindings := by
  have distinct := output_tokens frame
  rw [source.outputTokens] at distinct
  apply partition_perm _ _ (nodup_of_tokens _ source.transport.after.tokensDistinct)
  · exact nodup_of_tokens _ distinct
  · exact (order_values _ _ _ source.returned.ordered).1

#print axioms source_output_partition
#print axioms source_ports
#print axioms interval_selected_tokens
#print axioms order_values
#print axioms literal_partition

end QleisliKernel.Qirf.RuntimeSelectionPartition
