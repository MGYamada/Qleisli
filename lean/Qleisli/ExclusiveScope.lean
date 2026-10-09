import Qleisli.Scope

/-!
# Explicit updates at lexical scope closure

Lookup-level composition of authorized whole-owner replacement with the existing
scope projection. Names denote structural binder identities, not spellings.
The Resource model represents Unit/Bit/binary-product bases; embeddings of other
source types, hidden bindings, finite maps, update provenance, complete holder
coverage and actual Rust execution remain implementation-adequacy premises.
This proves no source preservation, quantum action or quantitative resource bound.
-/

namespace Qleisli.Scope

def alignBinding (entry current : Lookup) (updated : Bool) : Lookup :=
  if updated then
    match entry, current with
    | some (some (.quantum old)), some (some (.quantum next)) =>
      if old.basis = next.basis then current else entry
    | _, _ => entry
  else entry

noncomputable def align {Name : Type} (entry current : Env Name) (updates : Set Name) :
    Env Name := by
  classical
  exact fun n => alignBinding (entry n) (current n) (decide (n ∈ updates))

/-- An absent entry is not promoted into an outer owner. A subsequent consuming
transition remains spent. Every live replacement is one exact quantum basis. -/
def ValidUpdates {Name : Type} (entry current : Env Name) (updates : Set Name) : Prop :=
  ∀ n ∈ updates, entry n = none ∨ current n = some none ∨
    ∃ old next, entry n = some (some (.quantum old)) ∧
      current n = some (some (.quantum next)) ∧ old.basis = next.basis

noncomputable def closeUpdated {Name : Type} (entry current : Env Name)
    (updates : Set Name) : Option (Env Name) := by
  classical
  exact if ValidUpdates entry current updates then close (align entry current updates) current ∅
    else none

theorem align_domain {Name : Type} (entry current : Env Name) (updates : Set Name) :
    domain (align entry current updates) = domain entry := by
  classical
  ext n
  cases he : entry n with
  | none => simp [domain, align, alignBinding, he]
  | some e =>
    cases e with
    | none => simp [domain, align, alignBinding, he]
    | some v =>
      cases v <;> cases hc : current n with
      | none => simp [domain, align, alignBinding, he, hc]
      | some c =>
        cases c with
        | none => simp [domain, align, alignBinding, he, hc]
        | some w =>
          cases w <;> simp [domain, align, alignBinding, he, hc] <;>
            (split_ifs <;> simp)

theorem closeUpdated_preserves {Name : Type} {entry current output : Env Name}
    {updates : Set Name} (h : closeUpdated entry current updates = some output) :
    domain output = domain entry ∧ ∀ n, footprint (output n) = footprint (current n) := by
  classical
  simp only [closeUpdated] at h
  split_ifs at h with valid
  · obtain ⟨hd, hf⟩ := close_preserves h
    exact ⟨hd.trans (align_domain entry current updates), hf⟩

theorem closeUpdated_cannot_revive {Name : Type} {entry current output : Env Name}
    {updates : Set Name} {n : Name} (spent : entry n = some none)
    (h : closeUpdated entry current updates = some output) : output n = some none := by
  classical
  simp only [closeUpdated] at h
  split_ifs at h with valid
  · obtain ⟨_, rfl⟩ := (close_eq_some_iff _ _ _ output).mp h
    apply exit_spent
    simp [align, alignBinding, spent]

theorem align_quantum_update {Name : Type} {entry current : Env Name}
    {updates : Set Name} {n : Name} {old next : Port}
    (hu : n ∈ updates) (he : entry n = some (some (.quantum old)))
    (hc : current n = some (some (.quantum next))) (hb : old.basis = next.basis) :
    align entry current updates n = some (some (.quantum next)) := by
  classical
  simp [align, alignBinding, hu, he, hc, hb]

/-- Retain the new value, rather than restoring the original slot snapshot. -/
theorem closeUpdated_retains_current {Name : Type} {entry current output : Env Name}
    {updates : Set Name} {n : Name} {next : Port}
    (hc : current n = some (some (.quantum next)))
    (h : closeUpdated entry current updates = some output) :
    output n = some (some (.quantum next)) := by
  classical
  simp only [closeUpdated] at h
  split_ifs at h with valid
  obtain ⟨approved, rfl⟩ := (close_eq_some_iff _ _ _ output).mp h
  exact approved_quantum_retained approved hc rfl

end Qleisli.Scope
