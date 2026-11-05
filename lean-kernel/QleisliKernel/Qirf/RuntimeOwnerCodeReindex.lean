import QleisliKernel.Qirf.RuntimeSelectionPartition
import QleisliKernel.Qirf.RuntimeForestFactorization

/-! Constructive reindexing of the same retained owner-code receipts. Exact
Binding equality retains source ordinal, full nominal tree, port token and
ordered wires. A missing binding yields none; no carrier read, default owner,
accepted handle or new source/Gram/availability check is manufactured here.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace QleisliKernel.Qirf.RuntimeOwnerCodeReindex
open RuntimeOwnerMap (Binding Map)
open RuntimeForestCode

def lookup {bindings : Map} (owners : OwnerCodes bindings) (wanted : Binding) : Option (OwnerCode wanted) :=
  (Nat.rec (motive := fun fuel => (bindings : Map) → bindings.length ≤ fuel →
      OwnerCodes bindings → (wanted : Binding) → Option (OwnerCode wanted))
    (fun _ bound actual _ => match actual with
      | .nil => none
      | @OwnerCodes.cons _ rest _ _ => False.elim (Nat.not_succ_le_zero rest.length bound))
    (fun _ next _ bound actual wanted => match actual with
      | .nil => none
      | @OwnerCodes.cons binding rest first tail =>
        if same : binding = wanted then some (same ▸ first)
        else next rest (Nat.le_of_succ_le_succ bound) tail wanted)
    bindings.length) bindings (Nat.le_refl _) owners wanted

theorem lookup_nil (wanted : Binding) : lookup .nil wanted = none := rfl

theorem lookup_cons {binding bindings} (first : OwnerCode binding) (rest : OwnerCodes bindings) (wanted : Binding) :
    lookup (.cons first rest) wanted =
      if same : binding = wanted then some (same ▸ first) else lookup rest wanted := rfl

theorem lookup_exists {bindings} (owners : OwnerCodes bindings) (wanted : Binding) :
    wanted ∈ bindings → ∃ retained,lookup owners wanted = some retained := by
  induction owners with
  | nil => intro member; cases member
  | @cons binding bindings first rest ih =>
    intro member
    by_cases same : binding = wanted
    · subst wanted
      exact ⟨first,by rw [lookup_cons]; exact dif_pos rfl⟩
    · have later : wanted ∈ bindings := by
        rcases List.mem_cons.mp member with equal | later
        · exact False.elim (same equal.symm)
        · exact later
      obtain ⟨retained,ran⟩ := ih later
      exact ⟨retained,by rw [lookup_cons,dif_neg same]; exact ran⟩

/-- Missing source identity has dimension zero, never a fabricated singleton.
The equality below is used only after an actual retained lookup succeeds. -/
def dimensionAt {bindings} (owners : OwnerCodes bindings) (wanted : Binding) : Nat :=
  ((lookup owners wanted).map (fun code => code.layout.labels.length)).getD 0

theorem layout_unique {binding} (first second : OwnerCode binding) : first.layout = second.layout :=
  Option.some.inj (first.reference.1.symm.trans second.reference.1)

theorem dimensionAt_eq {bindings} (owners : OwnerCodes bindings) (wanted : Binding)
    (member : wanted ∈ bindings) (actual : OwnerCode wanted) :
    dimensionAt owners wanted = actual.layout.labels.length := by
  obtain ⟨retained,ran⟩ := lookup_exists owners wanted member
  simp only [dimensionAt,ran,Option.map_some,Option.getD_some,layout_unique retained actual]

def reindex {bindings} (owners : OwnerCodes bindings) (wanted : Map) : Option (OwnerCodes wanted) :=
  (Nat.rec (motive := fun fuel => (wanted : Map) → wanted.length ≤ fuel → Option (OwnerCodes wanted))
    (fun wanted bound => match wanted with
      | [] => some .nil
      | _ :: rest => False.elim (Nat.not_succ_le_zero rest.length bound))
    (fun _ next wanted bound => match wanted with
      | [] => some .nil
      | binding :: rest => do
        let first ← lookup owners binding
        let tail ← next rest (Nat.le_of_succ_le_succ bound)
        pure (.cons first tail)) wanted.length) wanted (Nat.le_refl _)

theorem reindex_nil {bindings} (owners : OwnerCodes bindings) : reindex owners [] = some .nil := rfl

theorem reindex_cons {bindings} (owners : OwnerCodes bindings) (binding : Binding) (rest : Map) :
    reindex owners (binding::rest) = (do
      let first ← lookup owners binding
      let tail ← reindex owners rest
      pure (.cons first tail)) := rfl

theorem reindex_exists {bindings} (owners : OwnerCodes bindings) (wanted : Map) :
    wanted ⊆ bindings → ∃ retained,reindex owners wanted = some retained := by
  induction wanted with
  | nil => intro _subset; exact ⟨.nil,rfl⟩
  | cons binding rest ih =>
    intro subset
    obtain ⟨first,firstRead⟩ := lookup_exists owners binding (subset (List.mem_cons_self))
    obtain ⟨tail,tailRead⟩ := ih (fun {_} member => subset (List.mem_cons_of_mem _ member))
    exact ⟨.cons first tail,by simp only [reindex_cons,firstRead,tailRead,bind,Option.bind,pure]⟩

structure Retained {bindings} (owners : OwnerCodes bindings) (wanted : Map) where
  codes : OwnerCodes wanted
  original : reindex owners wanted = some codes

/-- This pure data reindexing returns only the existing receipts selected by
the actual equality-based lookup above. It checks no new program or root. -/
def retain {bindings} (owners : OwnerCodes bindings) (wanted : Map) : Option (Retained owners wanted) :=
  match original : reindex owners wanted with
  | none => none
  | some codes => some ⟨codes,original⟩

theorem literal_reindex_exists
    {dependencies program block start count inputs outputs roles frame selectorBits targetBits retained restricted
      beforeRoles afterRoles before after}
    (checked : @RuntimeLocalEvents.Literal dependencies program block start count inputs outputs roles frame selectorBits
      targetBits retained restricted beforeRoles afterRoles before after) :
    ∃ codes,reindex checked.inputCode.owners
      (checked.selection.selected ++ RuntimeSelectionPartition.complement before.bindings checked.selection.selected) = some codes := by
  obtain ⟨_tokens,_unique,_subset,_roles,_spectators,partition⟩ := RuntimeSelectionPartition.literal_partition checked
  exact reindex_exists checked.inputCode.owners _ partition.subset

end QleisliKernel.Qirf.RuntimeOwnerCodeReindex
