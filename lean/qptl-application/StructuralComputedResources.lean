import Qleisli.StructuralComputedRestoration
import QleisliKernel.Raw.WorkspaceResources

/-! Relate resource counts to the actual source-checked structural compute
interval. The trace uses the whole caller frame and retains both circuit passes.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeComputedResources
open QleisliKernel Qirf
open Raw.WorkspaceResources (Checked readCounts)

/-- The structural predicate prepares and releases one private clean wire.
Both ordered predicate circuits and each protected use contribute their literal
steps. The resource read covers the same source-bound Raw interval and counts
the scratch alongside all live caller wires, including spectators. -/
theorem structural_counts {sources caller deps program block start count before receipts}
    {event : SourceTypes.SourceRuntimeContext.ComputedEvent sources caller}
    {interval : @RuntimeInterval.Checked deps program block start count}
    (checked : StructuralComputedRaw.IntervalChecked event interval before)
    (resource : Checked receipts interval.before.quantum.reference interval.after.quantum.reference
      [checked.packet.operation]) :
    resource.counts =
      ⟨interval.before.quantum.frame.length + 1, 1, 1, 2,
        checked.packet.forward.length + checked.packet.inverse.length + checked.packet.uses.length, 0⟩ := by
  have original := (StructuralComputedRestoration.interval_trace checked).2
  have trace := Option.some.inj (resource.originalTrace.symm.trans original)
  rw [resource.measured, trace]
  have entryWidth : interval.before.quantum.reference.frame.length =
      interval.before.quantum.frame.length := rfl
  simp [readCounts, Raw.WorkspaceResources.Counts.then_, Raw.WorkspaceResources.eventCounts,
    entryWidth]

#print axioms structural_counts
end Qleisli.RuntimeComputedResources
