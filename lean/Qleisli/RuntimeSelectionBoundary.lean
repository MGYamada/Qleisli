import Qleisli.RuntimeLiteralFrame
import QleisliKernel.Qirf.RuntimeSelectionWires

/-! Ordered selected axes from the same literal Raw interval and source owners.
No lowering shape or proposed axis equation identifies the returned interface.
This result does not establish the spectator forest or complete code equality.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeSelectionBoundary
open QleisliKernel QleisliKernel.Qirf RuntimeForestCode

/-- Literal circuit execution preserves the original frame order; the actual
sector reader identifies both selected returns in that same frame. -/
theorem literal_axes
    {dependencies program block start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs roles)
    (source : RuntimeOwnerTransition.Selection frame.interval inputs outputs roles)
    {selectorBits targetBits retained restricted}
    (literal : RuntimeLocalEvents.Literal frame selectorBits targetBits retained restricted
      source.before source.transport.after) :
    forestAxes frame.interval.before.quantum.frame literal.selection.selected =
      forestAxes frame.interval.after.quantum.frame source.returned.toList := by
  have selectedPorts := literal.selectedPorts.trans (RuntimeSelectionPartition.source_ports frame source).1
  have selectedWires := congrArg (List.flatMap (fun port : Semantics.Raw.Port => port.wires)) selectedPorts
  have returnedWires := congrArg (List.flatMap (fun pair : RuntimeOwnerMap.Owner × List Nat => pair.2))
    (RuntimeSelectionWires.source_boundary frame source literal).1
  simp only [List.flatMap_map] at selectedWires returnedWires
  unfold forestAxes
  rw [RuntimeLiteralFrame.literal_frame literal,returnedWires,selectedWires]
  rfl

#print axioms literal_axes

end Qleisli.RuntimeSelectionBoundary
