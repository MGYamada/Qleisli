import QleisliKernel.Qirf.RuntimeLocalEvents
import QleisliKernel.Raw.Sector

/-! Literal circuit chunks from the same actual sector read.
The original event/piece relation determines chunk extraction in source order.
An empty circuit remains an empty chunk; the identity finish reorder contributes
none. This proves no caller-trace localization, full owner-code availability,
lowering shape, readSource work sufficiency, acceptance or execution handle.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeSectorChunks
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Semantics.Finite

private theorem read_circuit (bits : Nat) (steps : List Step) (events : List Semantics.Raw.Event) :
    RuntimeLocalEvents.readChunks bits (.circuit bits steps :: events) = (do
      let rest ← RuntimeLocalEvents.readChunks bits events
      pure (steps :: rest)) := by
  simp [RuntimeLocalEvents.readChunks,List.mapM_cons]

private theorem read_reorder (bits : Nat) (events : List Semantics.Raw.Event) :
    RuntimeLocalEvents.readChunks bits (.reorder bits (List.range bits) :: events) =
      RuntimeLocalEvents.readChunks bits events := by
  simp [RuntimeLocalEvents.readChunks,List.mapM_cons]

/-- The exact successful sector event relation implies the existing literal
reader succeeds. Circuit chunks keep their individual boundaries, even when
empty, whereas identity reorder pieces contribute no chunk. -/
theorem eventPieces_chunks (bits : Nat) (events : List Semantics.Raw.Event) (pieces : List (List Step))
    (related : QleisliKernel.Exact.ListRel (Raw.Sector.EventPiece bits) events pieces) :
    ∃ chunks, RuntimeLocalEvents.readChunks bits events = .ok chunks ∧ chunks.flatten = pieces.flatten := by
  induction events generalizing pieces with
  | nil =>
    cases pieces with
    | nil => exact ⟨[],rfl,rfl⟩
    | cons first rest => exact False.elim related
  | cons event events ih =>
    cases pieces with
    | nil => exact False.elim related
    | cons first rest =>
      obtain ⟨chunks,read,flat⟩ := ih rest related.2
      rcases related.1 with original | ⟨original,empty⟩
      · subst event
        refine ⟨first :: chunks,?_,?_⟩
        · rw [read_circuit,read]
          rfl
        · simp only [List.flatten_cons,flat]
      · subst event
        subst first
        refine ⟨chunks,?_,?_⟩
        · rw [read_reorder]
          exact read
        · simpa only [List.flatten_cons,List.nil_append] using flat

/-- Only the SAME retained sector read supplies the original events and steps.
No new read, event proposal, discarded circuit or synthesized success is used. -/
theorem retained_chunks {dependencies : List Dependency} {selector target : Basis}
    {program : Semantics.Raw.Program} {retained : Raw.Sector.Retained}
    (restricted : RuntimeInterval.Computed (Raw.Sector.read dependencies selector target program) retained) :
    ∃ chunks, RuntimeLocalEvents.readChunks (width selector+width target) retained.prepared.events = .ok chunks ∧
      chunks.flatten = retained.steps := by
  obtain ⟨work,left,ran⟩ := restricted
  have binding := Raw.Sector.read_bound dependencies selector target program retained work left ran
  obtain ⟨pieces,related,flatten⟩ := binding.2.2.2.2.2.1
  obtain ⟨chunks,read,flat⟩ := eventPieces_chunks _ _ _ related
  exact ⟨chunks,read,flat.trans flatten.symm⟩

/-- The actual selection node's stored read discharges both localRead and
localSteps of its Literal record without assuming that Literal exists. -/
theorem selection_chunks {dependencies program block start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs roles)
    {selectorBits targetBits : Nat} {retained : Raw.Sector.Retained}
    (restricted : RuntimeInterval.Computed (Raw.Sector.read dependencies [.bits selectorBits] [.bits targetBits]
      (RuntimePureInterval.fragment frame.selected frame.operations outputs)) retained) :
    ∃ chunks, RuntimeLocalEvents.readChunks (selectorBits+targetBits) retained.prepared.events = .ok chunks ∧
      chunks.flatten = retained.steps := by
  simpa only [width,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using
    retained_chunks restricted

#print axioms eventPieces_chunks
#print axioms retained_chunks
#print axioms selection_chunks

end Qleisli.RuntimeSectorChunks
