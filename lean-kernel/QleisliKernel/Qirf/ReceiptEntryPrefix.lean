import QleisliKernel.Qirf.ReceiptPrefix

/-! Recover an actual entry step from the same successful graph, retaining
its historical readiness and extension into the final receipt snapshot.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.ReceiptTransport
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Finite
open QleisliKernel.Semantics.ObservingFunction

theorem successful_entry_step {artifact order extra roots final work left} {index : Nat} {receipt : Receipt}
    (ok : (checkGraphReceiptsFromRoots artifact order extra roots).run work = (.ok final,left))
    (present : final[index]?.join = some receipt) :
    ∃ frontNodes suffix previous next,
      order.toList = frontNodes ++ (artifact.programs.size+index) :: suffix ∧
      CheckedGraph artifact (Array.replicate artifact.entries.size none) frontNodes previous ∧
      CheckedNode artifact previous (artifact.programs.size+index) next ∧
      CheckedGraph artifact next suffix final ∧ Extends previous final ∧
      next[index]?.join = some receipt := by
  have graph := (checkGraphReceiptsFromRoots_fresh _ _ _ _ _ _ _ ok).1
  have member := fresh_present_written graph present
  obtain ⟨frontNodes,suffix,split⟩ := List.append_of_mem member
  obtain ⟨previous,front,back,extension⟩ :=
    successful_prefix ok frontNodes ((artifact.programs.size+index) :: suffix) split
  obtain ⟨schedule,scheduled,_⟩ := checkGraphReceiptsFromRoots_schedule _ _ _ _ _ _ _ ok
  have unique := graphCheck_nodup scheduled
  rw [split] at unique
  have absent : artifact.programs.size+index ∉ suffix :=
    (List.nodup_cons.mp (List.nodup_append.mp unique).2.1).1
  cases back with
  | cons previous node suffix next final step remaining =>
    have same := graph_unchanged remaining absent
    exact ⟨frontNodes,suffix,previous,next,split,front,step,remaining,extension,
      by simpa only [same] using present⟩

/-- The historical snapshot comes from the actual entry node in the successful
run. Readiness and extension refer to that same snapshot, rather than separately
chosen existentials. No equality of the whole dependency vectors is claimed. -/
theorem successful_entry_origin {artifact order extra roots final work left} {index : Nat} {receipt : Receipt}
    (ok : (checkGraphReceiptsFromRoots artifact order extra roots).run work = (.ok final,left))
    (present : final[index]?.join = some receipt) :
    ∃ entry actual previous a b c d,
      artifact.entries[index]? = some entry ∧
      (input artifact entry).run a = (.ok actual,b) ∧
      (Raw.BranchFunction.checkEntry (before previous) actual actual).run c = (.ok receipt,d) ∧
      receipt.input = actual ∧
      Qirf.ready previous actual.implementation = true ∧
      Qirf.ready previous actual.specification = true ∧
      Extends previous final := by
  obtain ⟨frontNodes,suffix,previous,next,split,front,step,back,extension,presentNext⟩ :=
    successful_entry_step ok present
  cases step with
  | program program checked a b found ready verified =>
    have outside : ¬artifact.programs.size+index < artifact.programs.size := by omega
    simp [outside] at found
  | entry entry actual produced a b c d outside found decoded ready verified =>
    have same : produced = receipt := by
      simp only [Nat.add_sub_cancel_left,Array.set!_eq_setIfInBounds,
        Array.getElem?_setIfInBounds] at presentNext
      by_cases inside : index < previous.size
      · simpa [inside] using presentNext
      · simp [inside] at presentNext
    subst produced
    exact ⟨entry,actual,previous,a,b,c,d,by simpa using found,decoded,verified,
      (Raw.BranchFunction.checkEntry_conditions _ _ _ _ _ _ verified).2.1,
      ready.1,ready.2,extension⟩

/-- This is the agreement needed by a later body-preservation bridge. It covers
both full original operation lists, including references in either branch.
The theorem does not itself transport all Raw checker computations or matrices. -/
theorem successful_entry_references {artifact order extra roots final work left} {index : Nat} {receipt : Receipt}
    (ok : (checkGraphReceiptsFromRoots artifact order extra roots).run work = (.ok final,left))
    (present : final[index]?.join = some receipt) :
    ∃ entry actual previous a b c d,
      artifact.entries[index]? = some entry ∧
      (input artifact entry).run a = (.ok actual,b) ∧
      (Raw.BranchFunction.checkEntry (before previous) actual actual).run c = (.ok receipt,d) ∧
      receipt.input = actual ∧
      ∀ dependency,
        dependency ∈ references 65 actual.implementation.operations ++
          references 65 actual.specification.operations →
        ((before previous).map Receipt.dependency)[dependency]? =
          ((before final).map Receipt.dependency)[dependency]? := by
  obtain ⟨entry,actual,previous,a,b,c,d,found,decoded,verified,original,impl,spec,extension⟩ :=
    successful_entry_origin ok present
  refine ⟨entry,actual,previous,a,b,c,d,found,decoded,verified,original,?_⟩
  intro dependency member
  rcases List.mem_append.mp member with implementation | specification
  · exact ready_dependency_agreement extension impl dependency implementation
  · exact ready_dependency_agreement extension spec dependency specification

end QleisliKernel.Qirf.ReceiptTransport
