import Qleisli.RuntimeCallBranchStep
import Qleisli.RuntimeObservingReadWrites
import QleisliKernel.Qirf.RuntimeCallInterval

/-! Bind the paired history fold to the two retained native reads of the
actual named call. Each reader uses its own original nesting depth.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeCallHistory
open QleisliKernel QleisliKernel.Qirf
open Semantics.Observation (readOps)
open Semantics.Raw (Port)
open RuntimeCallTraceFrames (Partition)
open Qleisli.RuntimeObservingPrefix (Issued FreshWrites checkOps_reference_with_writes
  checkOps_reference_with_fresh_writes)
open Qleisli.RuntimeObservingWrites (WritesWithin readOps_same_writes)

abbrev CallSegment {dependencies program block start count childProgram}
    (interval : @RuntimeInterval.Checked dependencies program block start count)
    (prepared : RuntimeInterval.Prepared dependencies childProgram) (localAfter : RuntimeInterval.State)
    (parentDepth : Nat) (spectators : List Port) : Prop :=
    ∃ parentEvents childEvents,
      readOps block.fuel interval.before.quantum.reference ((block.operations.drop start).take count) =
        some (interval.after.quantum.reference,parentEvents) ∧
      readOps prepared.block.fuel prepared.block.entry.quantum.reference prepared.block.operations =
        some (localAfter.quantum.reference,childEvents) ∧
      FreshWrites interval.before interval.after parentEvents ∧
      WritesWithin childEvents (Issued localAfter) ∧
      (∀ allowed, WritesWithin parentEvents allowed ↔ WritesWithin childEvents allowed) ∧
      Segment dependencies parentDepth 64 interval.before.quantum.reference
        prepared.block.entry.quantum.reference interval.after.quantum.reference
        localAfter.quantum.reference spectators parentEvents childEvents

private theorem call_segment_from_reads {dependencies program block start count childProgram}
    (interval : @RuntimeInterval.Checked dependencies program block start count)
    (prepared : RuntimeInterval.Prepared dependencies childProgram) (localEntry localAfter : RuntimeInterval.State)
    (entry : localEntry.quantum.reference = prepared.block.entry.quantum.reference)
    (literal : prepared.block.operations = (block.operations.drop start).take count)
    (localRead : RuntimeInterval.Computed (Raw.Observation.checkOps dependencies 65 localEntry
      ((block.operations.drop start).take count)) localAfter)
    (parentDepth : Nat) (depth : block.fuel = parentDepth+1) (spectators : List Port)
    (partition : Partition interval.before.quantum.reference prepared.block.entry.quantum.reference spectators) :
    CallSegment interval prepared localAfter parentDepth spectators := by
  have parentRead := interval.intervalRead
  rw [depth] at parentRead
  have initial : Partition interval.before.quantum.reference localEntry.quantum.reference spectators :=
    entry.symm ▸ partition
  obtain ⟨parentEvents,childEvents,parent,child,segment⟩ :=
    checked_operations ((block.operations.drop start).take count) parentRead localRead initial
      (fun op _ => operation_step_law dependencies parentDepth 64 spectators op)
  obtain ⟨pWork,pLeft,pRan⟩ := parentRead
  obtain ⟨cWork,cLeft,cRan⟩ := localRead
  obtain ⟨_,pEvents,pRead,pWrites⟩ := checkOps_reference_with_fresh_writes _ _ _ _ _ pWork pLeft pRan
  obtain ⟨_,cEvents,cRead,cWrites⟩ := checkOps_reference_with_writes _ _ _ _ _ cWork cLeft cRan
  have pEq : pEvents = parentEvents := congrArg Prod.snd (Option.some.inj (pRead.symm.trans parent))
  have cEq : cEvents = childEvents := congrArg Prod.snd (Option.some.inj (cRead.symm.trans child))
  refine ⟨parentEvents,childEvents,?_,?_,pEq ▸ pWrites,cEq ▸ cWrites,?_,?_⟩
  · rwa [depth]
  · change readOps 65 prepared.block.entry.quantum.reference prepared.block.operations = _
    rwa [← entry,literal]
  · intro allowed
    exact readOps_same_writes allowed (parentDepth+1) 65 _ parent child
  · rw [← entry]
    exact segment

/-- Both readers of a mixed call use the actual original operation slice,
with the local reader starting from the prepared child entry. -/
theorem actual_call_segment {dependencies program block start count inputs ordinary effect}
    (scope : @RuntimeCallScope.Checked dependencies program block start count inputs ordinary effect)
    (parentDepth : Nat) (depth : block.fuel = parentDepth+1) (spectators : List Port)
    (partition : Partition scope.interval.before.quantum.reference scope.prepared.block.entry.quantum.reference spectators) :
    CallSegment scope.interval scope.prepared scope.localAfter parentDepth spectators := by
  have input := (RuntimeNamedFrameAxes.mixedAxes_input scope).2
  exact call_segment_from_reads scope.interval scope.prepared scope.localEntry scope.localAfter
    (input.1.trans input.2.1.symm) rfl scope.nativeRead parentDepth depth spectators partition

/-- A pure callback uses the very same literal fold while the enclosing
state can retain classical values from the original caller. -/
theorem actual_pure_call_segment {dependencies program block start count inputs}
    (scope : @RuntimeCallInterval.Checked dependencies program block start count inputs)
    (parentDepth : Nat) (depth : block.fuel = parentDepth+1) (spectators : List Port)
    (partition : Partition scope.interval.before.quantum.reference scope.prepared.block.entry.quantum.reference spectators) :
    CallSegment scope.interval scope.prepared scope.localAfter parentDepth spectators := by
  have entry := (RuntimeNamedFrameAxes.initialized scope.entryRead).1.trans
    (RuntimeNamedFrameAxes.child_interface scope).symm
  have nativeRead := scope.nativeRead
  rw [← scope.literal] at nativeRead
  exact call_segment_from_reads scope.interval scope.prepared scope.localEntry scope.localAfter
    entry scope.literal.symm nativeRead parentDepth depth spectators partition

#print axioms actual_call_segment
#print axioms actual_pure_call_segment
end Qleisli.RuntimeCallHistory
