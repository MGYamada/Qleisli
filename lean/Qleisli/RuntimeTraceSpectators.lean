import Init.Data.List.Perm
import Init.Data.List.Find
import QleisliKernel.Semantics.RawTrace

/-! Exact token lookup through the original local/caller spectator relation.
Every moved value is the same complete Raw Port, including empty wire lists.
Actual take/insert keep each interface's original frame list. No width equality,
code-space premise, supplied final relation, checker or accepted gate is used.
Per-operation event localization remains a subsequent obligation.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeTraceSpectators
open QleisliKernel.Semantics QleisliKernel.Semantics.Raw

private theorem take_fields {before after : RawTrace.Interface} {token : Nat} {port : Port}
    (read : RawTrace.take before token = some (port,after)) :
    before.live.find? (fun value => value.token == token) = some port ∧
      after = {before with live := before.live.filter (fun value => value.token != token)} := by
  unfold RawTrace.take at read
  obtain ⟨found,lookup,finished⟩ := Option.bind_eq_some_iff.mp read
  have values := Prod.mk.inj (Option.some.inj finished)
  exact ⟨lookup.trans (congrArg some values.1),values.2.symm⟩

private theorem find_port (live : List Port) (port : Port)
    (unique : (live.map (·.token)).Nodup) (present : port ∈ live) :
    live.find? (fun value => value.token == port.token) = some port := by
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
      simpa only [List.find?,skip] using ih distinct.2 member

/-- Taking a local token from the actual caller returns the SAME Port and
leaves precisely the local remainder plus the unchanged spectator Port list.
Uniqueness comes from the original caller tokens, including zero-width cells. -/
theorem take_spectators (caller selected : RawTrace.Interface) (spectators : List Port)
    (embedded : caller.live.Perm (selected.live ++ spectators))
    (unique : (caller.live.map (·.token)).Nodup) {token : Nat} {port : Port} {selectedAfter : RawTrace.Interface}
    (localRead : RawTrace.take selected token = some (port,selectedAfter)) :
    ∃ callerAfter, RawTrace.take caller token = some (port,callerAfter) ∧
      callerAfter.live.Perm (selectedAfter.live ++ spectators) ∧
      callerAfter.frame = caller.frame ∧ selectedAfter.frame = selected.frame ∧
      (callerAfter.live.map (·.token)).Nodup := by
  obtain ⟨localFound,localAfter⟩ := take_fields localRead
  have present := List.mem_of_find?_eq_some localFound
  have tokenRead : port.token = token :=
    beq_iff_eq.mp (List.find?_some (p := fun value : Port => value.token == token) localFound)
  have callerPresent : port ∈ caller.live :=
    embedded.mem_iff.mpr (List.mem_append.mpr (Or.inl present))
  have callerFound : caller.live.find? (fun value => value.token == token) = some port := by
    simpa only [tokenRead] using find_port caller.live port unique callerPresent
  have joinedUnique : ((selected.live ++ spectators).map (·.token)).Nodup :=
    (embedded.map (fun value => value.token)).nodup_iff.mp unique
  rw [List.map_append] at joinedUnique
  have separate := (List.nodup_append.mp joinedUnique).2.2
  have untouched : spectators.filter (fun value => value.token != token) = spectators := by
    apply List.filter_eq_self.mpr
    intro value member
    simp only [bne_iff_ne]
    intro same
    exact separate port.token (List.mem_map_of_mem present) value.token (List.mem_map_of_mem member)
      (tokenRead.trans same.symm)
  let callerAfter : RawTrace.Interface :=
    {caller with live := caller.live.filter (fun value => value.token != token)}
  refine ⟨callerAfter,?_,?_,rfl,?_,?_⟩
  · unfold RawTrace.take
    rw [callerFound]
    rfl
  · change (caller.live.filter (fun value => value.token != token)).Perm (selectedAfter.live ++ spectators)
    rw [localAfter]
    change (caller.live.filter (fun value => value.token != token)).Perm
      (selected.live.filter (fun value => value.token != token) ++ spectators)
    simpa only [List.filter_append,untouched] using embedded.filter (fun value => value.token != token)
  · rw [localAfter]
  · change ((caller.live.filter (fun value => value.token != token)).map (·.token)).Nodup
    exact List.Nodup.sublist (List.Sublist.map _ List.filter_sublist) unique

/-- The actual insert appends the same token/wires/bit-count cell in both
interfaces. Its relation is derived from the previous one; both frame lists
remain fixed. Freshness belongs to the existing Raw checker, not this lemma. -/
theorem insert_spectators (caller selected : RawTrace.Interface) (spectators : List Port)
    (embedded : caller.live.Perm (selected.live ++ spectators)) (token : Nat) (wires : List Nat) :
    (RawTrace.insert caller token wires).live.Perm
        ((RawTrace.insert selected token wires).live ++ spectators) ∧
      (RawTrace.insert caller token wires).frame = caller.frame ∧
      (RawTrace.insert selected token wires).frame = selected.frame := by
  refine ⟨?_,rfl,rfl⟩
  let added : Port := ⟨token,wires,wires.length⟩
  change (caller.live ++ [added]).Perm ((selected.live ++ [added]) ++ spectators)
  have moved : ((selected.live ++ spectators) ++ [added]).Perm ((selected.live ++ [added]) ++ spectators) := by
    simpa only [List.append_assoc] using
      (List.perm_append_comm : (spectators ++ [added]).Perm ([added] ++ spectators)).append_left selected.live
  exact (embedded.append_right [added]).trans moved

#print axioms take_spectators
#print axioms insert_spectators

end Qleisli.RuntimeTraceSpectators
