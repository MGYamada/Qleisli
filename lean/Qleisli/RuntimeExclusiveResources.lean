import Qleisli.RawAccessCommutation
import QleisliKernel.Raw.WorkspaceResources

/-! Live-wire accounting at the literal routing bounds of an indexed access.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeExclusiveResources
open QleisliKernel QleisliKernel.Qirf
open RuntimeOwnerMap (Map)
open Qleisli.RuntimeCallTraceFrames (WireOrder native_wires)

/-- Every wire in the complete live Raw frame occurs once in the source map.
Port identities, including ports with zero physical wires, are retained by the
original checked owner map. -/
structure LiveWires (bindings : Map) (state : RuntimeInterval.State) : Prop where
  coverage : (WireOrder (bindings.map (·.port))).Perm state.quantum.frame
  distinct : (WireOrder (bindings.map (·.port))).Nodup
  count : (WireOrder (bindings.map (·.port))).length = state.quantum.frame.length

theorem checked_live_wires {roles state} (owners : RuntimeOwnerMap.Checked roles state)
    (valid : QleisliKernel.Raw.stateValid state.quantum = true) : LiveWires owners.bindings state := by
  have cover := (owners.complete.flatMap_right Semantics.Raw.Port.wires).trans
    (native_wires state.quantum valid)
  exact ⟨cover,cover.symm.nodup (QleisliKernel.Raw.Ownership.valid state.quantum valid).frame,cover.length_eq⟩

/-- Each successfully checked prefix of the actual split/join route has the
same ordered frame, and its live ports count each physical wire once. -/
theorem routed_prefix_live_wires {dependencies fuel before} {original : List RuntimeInterval.Op}
    (routes : original.all RuntimeAccessPartition.isRoute = true) (size : Nat)
    {after : RuntimeInterval.State}
    (prefixRun : RuntimeInterval.Computed
      (QleisliKernel.Raw.Observation.checkOps dependencies fuel before (original.take size)) after) :
    (WireOrder after.quantum.live).Perm before.quantum.frame ∧
      (WireOrder after.quantum.live).Nodup ∧
      (WireOrder after.quantum.live).length = before.quantum.frame.length := by
  have prefixRoutes : (original.take size).all RuntimeAccessPartition.isRoute = true :=
    List.all_eq_true.mpr (fun op member => List.all_eq_true.mp routes op (List.mem_of_mem_take member))
  obtain ⟨_,_,_,same⟩ := Qleisli.Raw.AccessCommutation.structural_trace prefixRun prefixRoutes
  obtain ⟨work,left,ran⟩ := prefixRun
  have valid := (QleisliKernel.Raw.Observation.checkOps_invariants _ _ _ _ _ _ _ ran).1
  have cover := native_wires after.quantum valid
  exact ⟨same ▸ cover,(QleisliKernel.Raw.Ownership.valid after.quantum valid).exclusive,
    cover.length_eq.trans (congrArg List.length same)⟩

/-- Extraction and reassembly count every live wire once at their actual
boundaries. The inner call retains its own independent resource obligation. -/
theorem indexed_access_live_wires {sources caller dependencies program block start count access interval suspended before
    child childRetired}
    {opening : @RuntimeExclusiveAction.Opened sources caller dependencies program block start count
      access interval suspended before}
    (closing : RuntimeExclusiveAction.Closed opening child childRetired) :
    LiveWires before.bindings opening.route.preamble.before ∧
    LiveWires opening.initial.bindings interval.before ∧
    LiveWires child.bindings interval.after ∧
    LiveWires closing.after.bindings closing.route.after ∧
    interval.before.quantum.frame.length = opening.route.preamble.before.quantum.frame.length ∧
    closing.route.after.quantum.frame.length = interval.after.quantum.frame.length := by
  obtain ⟨⟨_,_,_,enter⟩,⟨_,_,_,leave⟩⟩ :=
    Qleisli.Raw.AccessCommutation.active_routing_traces opening.route closing.route
  refine ⟨?_,?_,?_,?_,congrArg List.length enter,congrArg List.length leave⟩
  · simpa only [opening.route.originalFrame] using
      checked_live_wires opening.route.frame opening.route.preamble.history.1
  · simpa only [opening.nativeBindings] using checked_live_wires opening.frame interval.history.1
  · simpa only [closing.childBindings] using checked_live_wires closing.childFrame interval.history.2.2.1
  · obtain ⟨work,left,ran⟩ := closing.route.original
    have valid := (QleisliKernel.Raw.Observation.checkOps_invariants _ _ _ _ _ _ _ ran).1
    have accounting := checked_live_wires closing.route.frame valid
    have ports : closing.after.bindings.map (·.port) = closing.route.frame.bindings.map (·.port) := by
      rw [closing.bindings,closing.route.originalFrame,List.map_map]
      rfl
    exact ⟨by rw [ports]; exact accounting.coverage,by rw [ports]; exact accounting.distinct,
      by rw [ports]; exact accounting.count⟩

/-- The resource model reads the same literal Core interval with the same
entry frame and dependency receipts. The checked trace uniquely fixes its
event counts. -/
theorem same_core_interval_counts {receipts before after ops}
    (first second : QleisliKernel.Raw.WorkspaceResources.Checked receipts before after ops) :
    first.counts = second.counts := by
  have trace := Option.some.inj (first.originalTrace.symm.trans second.originalTrace)
  rw [first.measured,second.measured,trace]

#print axioms indexed_access_live_wires
#print axioms routed_prefix_live_wires
#print axioms same_core_interval_counts
end Qleisli.RuntimeExclusiveResources
