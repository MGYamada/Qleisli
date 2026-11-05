import Qleisli.RuntimeOwnerBindingFacts
import Qleisli.RuntimeOwnerFlowExtension

/-! Authentic input and return facts for local/caller owner-flow transport.
The original seed executions determine complete token/Tree cells. The actual
return fold consumes every cell, including separate empty owners; no physical
width, final code equation or selected lowering shape identifies a source owner.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeOwnerFlowSeeds
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Semantics
open RuntimeOwnerMap (Binding Map)
open Qleisli.RuntimeOwnerTransitionAction (seedCell put_result)
open Qleisli.RuntimeOwnerFlowExtension (take_partition)

private theorem seed_fold_partition (bindings : Map) :
    ∀ initial final : RawOwnerFlow.Frame,
      bindings.foldlM (fun current binding => RawOwnerFlow.put binding.port.token
        (.owner binding.owner binding.port.bits) current) initial = some final →
      final.Perm (bindings.map seedCell ++ initial) := by
  induction bindings with
  | nil =>
    intro initial final ran
    have same : initial = final := Option.some.inj ran
    subst final
    exact List.Perm.refl _
  | cons binding rest ih =>
    intro initial final ran
    rw [List.foldlM_cons] at ran
    obtain ⟨next,inserted,tail⟩ := Option.bind_eq_some_iff.mp ran
    have nextEq : next = seedCell binding :: initial :=
      put_result _ _ _ _ inserted
    have later := ih next final tail
    rw [nextEq] at later
    exact later.trans List.perm_middle

/-- The exact original seed contains precisely the original binding cells.
Its internal reverse insertion order is immaterial to the context permutation. -/
theorem seed_partition (bindings : Map) (initial : RawOwnerFlow.Frame)
    (ran : RawOwnerFlow.seed (bindings.map (·.owner)) (bindings.map (·.port)) = some initial) :
    initial.Perm (bindings.map seedCell) := by
  have folded : bindings.foldlM (fun current binding => RawOwnerFlow.put binding.port.token
      (.owner binding.owner binding.port.bits) current) [] = some initial := by
    simpa [RawOwnerFlow.seed,List.zip_map',List.foldlM_map] using ran
  simpa only [List.append_nil] using seed_fold_partition bindings [] initial folded

/-- The original source-selected pair and both actual seed runs supply the
extension invariant. No caller supplies a final forest or a new uniqueness gate. -/
theorem selection_seed_context {dependencies program block start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs roles)
    (source : RuntimeOwnerTransition.Selection frame.interval inputs outputs roles)
    (initial selected : RawOwnerFlow.Frame)
    (callerRead : RawOwnerFlow.seed (source.before.bindings.map (·.owner))
      (source.before.bindings.map (·.port)) = some initial)
    (selectedRead : RawOwnerFlow.seed (source.selected.toList.map (·.owner))
      (source.selected.toList.map (·.port)) = some selected) :
    initial.Perm (selected ++
      (RuntimeSelectionPartition.complement source.before.bindings source.selected.toList).map seedCell) ∧
      (initial.map Prod.fst).Nodup := by
  have caller := seed_partition source.before.bindings initial callerRead
  have chosen := seed_partition source.selected.toList selected selectedRead
  have partition := RuntimeSelectionPartition.source_input_partition frame source
  have mapped := List.Perm.map seedCell partition.symm
  rw [List.map_append] at mapped
  have context := caller.trans (mapped.trans (chosen.symm.append_right _))
  have cellsUnique : ((source.before.bindings.map seedCell).map Prod.fst).Nodup := by
    simpa only [List.map_map,Function.comp_def,seedCell] using source.before.tokensDistinct
  exact ⟨context,(List.Perm.map Prod.fst caller.symm).nodup cellsUnique⟩

private theorem returned_fold (outputs : List Nat)
    {values result : List SourceOwners.Owner} {before remaining : RawOwnerFlow.Frame}
    (ran : outputs.foldlM (fun (values,current) token => do
      let (.owner owner _,after) ← RawOwnerFlow.take token current | none
      pure (owner :: values,after)) (values,before) = some (result,remaining)) :
    values ⊆ result ∧ ∀ cell ∈ before,
      cell ∈ remaining ∨ ∃ token owner bits,cell = (token,.owner owner bits) ∧ owner ∈ result := by
  induction outputs generalizing values result before remaining with
  | nil =>
    change some (values,before) = some (result,remaining) at ran
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj ran)
    constructor
    · intro value member; exact member
    · intro cell member; exact Or.inl member
  | cons token rest ih =>
    rw [List.foldlM_cons] at ran
    obtain ⟨⟨nextValues,nextFrame⟩,head,tail⟩ := Option.bind_eq_some_iff.mp ran
    obtain ⟨⟨tree,after⟩,taken,returned⟩ := Option.bind_eq_some_iff.mp head
    cases tree with
    | pair first second bits => cases returned
    | owner owner bits =>
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj returned)
      have later := ih tail
      constructor
      · intro value member
        exact later.1 (List.mem_cons_of_mem _ member)
      · intro cell member
        rcases List.mem_cons.mp ((take_partition taken).mem_iff.mp member) with same | remaining
        · exact Or.inr ⟨token,owner,bits,same,later.1 List.mem_cons_self⟩
        · exact later.2 cell remaining

/-- A successful actual return consumes the entire local frame. Every original
cell is an owner leaf whose full source identity occurs in that returned list. -/
theorem returned_cells (outputs : List Nat) {before : RawOwnerFlow.Frame} {owners : List SourceOwners.Owner}
    (ran : RawOwnerFlow.returned outputs before = some owners) :
    ∀ cell ∈ before,∃ token owner bits,cell = (token,.owner owner bits) ∧ owner ∈ owners := by
  unfold RawOwnerFlow.returned at ran
  obtain ⟨⟨values,remaining⟩,folded,returned⟩ := Option.bind_eq_some_iff.mp ran
  cases remaining with
  | cons first rest => cases returned
  | nil =>
    have same : values.reverse = owners := Option.some.inj returned
    have facts := returned_fold outputs folded
    intro cell member
    rcases facts.2 cell member with impossible | original
    · cases impossible
    · obtain ⟨token,owner,bits,equal,present⟩ := original
      refine ⟨token,owner,bits,equal,?_⟩
      rw [← same]
      exact List.mem_reverse.mpr present

#print axioms seed_partition
#print axioms selection_seed_context
#print axioms returned_cells

end Qleisli.RuntimeOwnerFlowSeeds
