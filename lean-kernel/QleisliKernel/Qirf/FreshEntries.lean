import QleisliKernel.Qirf

/-! Fresh receipts at their actual original evidence indices, including the
complete checked input and the dependency snapshot used at that graph node.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf
open Semantics.ObservingFunction

def EntryOrigin (artifact : Artifact) (index : Nat) (receipt : Receipt) : Prop :=
  ∃ entry actual previous a b c d,
    artifact.entries[index]? = some entry ∧
    (input artifact entry).run a = (.ok actual,b) ∧
    (Raw.BranchFunction.checkEntry (before previous) actual actual).run c = (.ok receipt,d)

def EntryOrigins (artifact : Artifact) (slots : Slots) : Prop :=
  ∀ index receipt, slots[index]?.join = some receipt → EntryOrigin artifact index receipt

theorem CheckedNode.entryOrigins {artifact : Artifact} {slots next : Slots} {node : Nat}
    (step : CheckedNode artifact slots node next) (held : EntryOrigins artifact slots) :
    EntryOrigins artifact next := by
  cases step with
  | program => exact held
  | entry entry actual produced a b c d outside found decoded ready verified =>
    intro index receipt present
    rw [Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds] at present
    by_cases same : index = node - artifact.programs.size
    · subst index
      by_cases inside : node - artifact.programs.size < slots.size
      · simp only [ite_true,inside,Option.join_some,Option.some.injEq] at present
        subst receipt
        exact ⟨entry,actual,slots,a,b,c,d,found,decoded,verified⟩
      · simp [inside] at present
    · simp only [Ne.symm same,ite_false] at present
      exact held index receipt present

theorem CheckedGraph.entryOrigins {artifact : Artifact} {slots final : Slots} {nodes : List Nat}
    (graph : CheckedGraph artifact slots nodes final) (held : EntryOrigins artifact slots) :
    EntryOrigins artifact final := by
  induction graph with
  | nil => exact held
  | cons slots node rest next final checked remaining ih =>
    exact ih (checked.entryOrigins held)

theorem empty_entryOrigins (artifact : Artifact) :
    EntryOrigins artifact (Array.replicate artifact.entries.size none) := by
  intro index receipt present
  by_cases inside : index < artifact.entries.size <;> simp [inside] at present

theorem CheckedGraph.originalEntry {artifact : Artifact} {final : Slots} {nodes : List Nat}
    (graph : CheckedGraph artifact (Array.replicate artifact.entries.size none) nodes final)
    (index : Nat) (receipt : Receipt) (present : final[index]?.join = some receipt) :
    EntryOrigin artifact index receipt :=
  graph.entryOrigins (empty_entryOrigins artifact) index receipt present

open Finite

theorem identity_value (artifact : Artifact) (entry : Entry) (value : Semantics.Function.Identity)
    (work left : Nat) (ok : (identity artifact entry).run work = (.ok value,left)) :
    value = ⟨entry.implementationName,entry.specificationName,
      entry.sources.map (fun index => artifact.sources[index]?.getD ("",""))⟩ := by
  obtain ⟨_,w₁,_,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,w₂,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₃,_,h⟩ := bind_success _ _ _ _ _ h
  exact (pure_success _ _ _ _ h).1

theorem input_original (artifact : Artifact) (entry : Entry) (value : Input) (work left : Nat)
    (ok : (input artifact entry).run work = (.ok value,left)) :
    value.signature = entry.signature ∧
    artifact.programs[entry.implementation]? = some value.implementation ∧
    ∃ a b, (identity artifact entry).run a = (.ok value.identity,b) := by
  obtain ⟨implementation,w₁,hp,h⟩ := bind_success _ _ _ _ _ ok
  cases target : entry.target <;> simp only [target] at h
  all_goals
    obtain ⟨specification,w₂,_,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨ident,w₃,hi,h⟩ := bind_success _ _ _ _ _ h
    have same := (pure_success _ _ _ _ h).1
    subst value
    have present : artifact.programs[entry.implementation]? = some implementation := by
      have found := (lift_success _ _ _ _ hp).1
      cases selected : artifact.programs[entry.implementation]? <;> simp_all [readOption]
    exact ⟨rfl,present,w₂,w₃,hi⟩

end QleisliKernel.Qirf
