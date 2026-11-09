import Qleisli.RuntimeCallBranchStep

/-! Bind the paired history fold to the two retained native reads of the
actual named call. Each reader uses its own original nesting depth.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeCallHistory
open QleisliKernel QleisliKernel.Qirf
open Semantics.Observation (readOps)
open Semantics.Raw (Port)
open RuntimeCallTraceFrames (Partition)
open Qleisli.RuntimeObservingPrefix (Issued checkOps_reference_with_writes)
open Qleisli.RuntimeObservingWrites (WritesWithin)

/-- The parent interval and the fresh local check use the same slice of the
original operation list. The local reader starts at the actual prepared
child frame, with the depth of the original local check. -/
theorem actual_call_segment {dependencies program block start count inputs ordinary effect}
    (scope : @RuntimeCallScope.Checked dependencies program block start count inputs ordinary effect)
    (parentDepth : Nat) (depth : block.fuel = parentDepth+1) (spectators : List Port)
    (partition : Partition scope.interval.before.quantum.reference scope.prepared.block.entry.quantum.reference
      spectators) :
    ∃ parentEvents childEvents,
      readOps block.fuel scope.interval.before.quantum.reference ((block.operations.drop start).take count) =
        some (scope.interval.after.quantum.reference,parentEvents) ∧
      readOps scope.prepared.block.fuel scope.prepared.block.entry.quantum.reference scope.prepared.block.operations =
        some (scope.localAfter.quantum.reference,childEvents) ∧
      WritesWithin parentEvents (Issued scope.interval.after) ∧
      WritesWithin childEvents (Issued scope.localAfter) ∧
      Segment dependencies parentDepth 64 scope.interval.before.quantum.reference
        scope.prepared.block.entry.quantum.reference scope.interval.after.quantum.reference
        scope.localAfter.quantum.reference spectators parentEvents childEvents := by
  have input := (RuntimeNamedFrameAxes.mixedAxes_input scope).2
  have entry := input.1.trans input.2.1.symm
  have parentRead := scope.interval.intervalRead
  rw [depth] at parentRead
  have initial : Partition scope.interval.before.quantum.reference scope.localEntry.quantum.reference spectators :=
    entry.symm ▸ partition
  obtain ⟨parentEvents,childEvents,parent,child,segment⟩ :=
    checked_operations ((block.operations.drop start).take count) parentRead scope.nativeRead initial
      (fun op _ => operation_step_law dependencies parentDepth 64 spectators op)
  obtain ⟨pWork,pLeft,pRan⟩ := parentRead
  obtain ⟨cWork,cLeft,cRan⟩ := scope.nativeRead
  obtain ⟨_,pEvents,pRead,pWrites⟩ := checkOps_reference_with_writes _ _ _ _ _ pWork pLeft pRan
  obtain ⟨_,cEvents,cRead,cWrites⟩ := checkOps_reference_with_writes _ _ _ _ _ cWork cLeft cRan
  have pEq : pEvents = parentEvents := congrArg Prod.snd (Option.some.inj (pRead.symm.trans parent))
  have cEq : cEvents = childEvents := congrArg Prod.snd (Option.some.inj (cRead.symm.trans child))
  refine ⟨parentEvents,childEvents,?_,?_,pEq ▸ pWrites,cEq ▸ cWrites,?_⟩
  · rwa [depth]
  · change readOps 65 scope.prepared.block.entry.quantum.reference ((block.operations.drop start).take count) = _
    rwa [← entry]
  · rw [← entry]
    exact segment

#print axioms actual_call_segment
end Qleisli.RuntimeCallHistory
