import QleisliKernel.Qirf.RuntimeSelectionPartition

/-! Ordered source-owner wires at one authentic literal sector boundary.
The actual local pure verification and sector reconstruction must read the
same prepared original fragment. No caller supplies a wire correspondence.
Separate zero-width owners retain their identities. This does not identify
spectator source owners merely from their unchanged Raw ports, establish a
full output-code equation, transfer Gram checks or issue an accepted handle.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace QleisliKernel.Qirf.RuntimeSelectionWires
open QleisliKernel Finite
open RuntimeOwnerMap (Binding Map)

private theorem pair_found (live : List Semantics.Raw.Port) (a b : Nat)
    (first second : Semantics.Raw.Port)
    (ran : PureInterval.portsOf live [a,b] = some [first,second]) :
    live.find? (fun port => port.token == a) = some first ∧
      live.find? (fun port => port.token == b) = some second := by
  cases left : live.find? (fun port => port.token == a) with
  | none => simp [PureInterval.portsOf,List.mapM_cons,left] at ran
  | some l =>
    cases right : live.find? (fun port => port.token == b) with
    | none => simp [PureInterval.portsOf,List.mapM_cons,left,right] at ran
    | some r =>
      have same : l = first ∧ r = second := by
        simpa [PureInterval.portsOf,List.mapM_cons,left,right] using ran
      exact ⟨congrArg some same.1,congrArg some same.2⟩

/-- The actual retained sector read already fixes both ordered source returns.
No successful Literal/readSource invocation or lowering-shape premise is needed
for this wire boundary; the complete native spectator check is retained. -/
theorem source_boundary_of_read
    {dependencies program block start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs roles)
    (source : RuntimeOwnerTransition.Selection frame.interval inputs outputs roles)
    {selectorBits targetBits : Nat} {retained : Raw.Sector.Retained}
    (restricted : RuntimeInterval.Computed (Raw.Sector.read dependencies [.bits selectorBits] [.bits targetBits]
      (RuntimePureInterval.fragment frame.selected frame.operations outputs)) retained) :
    source.returned.toList.map (fun binding => (binding.owner,binding.port.wires)) =
      source.selected.toList.map (fun binding => (binding.owner,binding.port.wires)) ∧
      PureInterval.spectators frame.interval.before inputs =
        PureInterval.spectators frame.interval.after outputs := by
  obtain ⟨sectorWork,sectorLeft,sectorRead⟩ := restricted
  have read := Raw.Sector.read_bound _ _ _ _ _ sectorWork sectorLeft sectorRead
  obtain ⟨work,left,ran⟩ := frame.pureRead
  have purePrepared := (Raw.Pure.verify_conditions _ _ _ work left ran).1
  have samePrepared : frame.pureBody = retained.prepared :=
    Except.ok.inj (purePrepared.symm.trans read.2.2.1)
  have ports := RuntimeSelectionPartition.source_ports frame source
  have exit : PureInterval.portsOf retained.prepared.state.live
      [source.returned.first.port.token,source.returned.second.port.token] =
        some [source.returned.first.port,source.returned.second.port] := by
    rw [← samePrepared]
    simpa only [source.outputTokens,ports.2] using frame.rawExit
  have found := pair_found _ _ _ _ _ exit
  have interface := read.2.2.2.2.1
  simp only [RuntimePureInterval.fragment,ports.1,source.outputTokens,Raw.Sector.ownerInterface,
    found.1,found.2,Option.map_some,Option.getD_some,Bool.and_eq_true,beq_iff_eq] at interface
  have firstWires : source.returned.first.port.wires = source.selected.first.port.wires :=
    interface.1.2.2
  have secondWires : source.returned.second.port.wires = source.selected.second.port.wires :=
    interface.2.2
  have selectedOwners := (RuntimeSelectionPartition.order_values _ _ _ source.selected.ordered).2
  have returnedOwners := (RuntimeSelectionPartition.order_values _ _ _ source.returned.ordered).2
  have sameOwners : source.returned.first.owner = source.selected.first.owner ∧
      source.returned.second.owner = source.selected.second.owner := by
    simpa only [List.map_cons,List.map_nil,List.cons.injEq,and_true] using
      returnedOwners.trans selectedOwners.symm
  exact ⟨by simp only [RuntimeOwnerTransition.Pair.toList,List.map_cons,List.map_nil,
    sameOwners.1,sameOwners.2,firstWires,secondWires],frame.spectators⟩

/-- Compatibility with existing literal consumers. The ordered wire result
is supplied by the same actual sector read; Literal keeps its other duties. -/
theorem source_boundary
    {dependencies program block start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs roles)
    (source : RuntimeOwnerTransition.Selection frame.interval inputs outputs roles)
    {selectorBits targetBits retained restricted}
    (_literal : RuntimeLocalEvents.Literal frame selectorBits targetBits retained restricted
      source.before source.transport.after) :
    source.returned.toList.map (fun binding => (binding.owner,binding.port.wires)) =
      source.selected.toList.map (fun binding => (binding.owner,binding.port.wires)) ∧
      PureInterval.spectators frame.interval.before inputs =
        PureInterval.spectators frame.interval.after outputs :=
  source_boundary_of_read frame source restricted

#print axioms source_boundary_of_read
#print axioms source_boundary

end QleisliKernel.Qirf.RuntimeSelectionWires
