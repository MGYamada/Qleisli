import Qleisli.RuntimeRoutedBranchRun
import Qleisli.RuntimeRoutedPhiSpectators
import Qleisli.RuntimeCallBranchStep

/-! Relate the full original literal branch to the independently checked
selected projection. The actual source callee runs on the selected scope.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeCallHistory
open QleisliKernel QleisliKernel.Qirf
open Semantics.Raw (Port)
open Semantics.RawTrace (Interface axes)
open Semantics.Observation (Op phiWires phiInterface)
open RuntimeCallTraceFrames (Partition)
open RuntimeOriginalBranch (Trace armFinish branchEvent original_branch_events original_branch_phi_checks)
open Qleisli.RuntimeNamedThreePackedInstrument (pureHistory)

private theorem valid_at {dependencies fuel before after ops}
    (read : RuntimeInterval.Computed (Raw.Observation.checkOps dependencies fuel before ops) after) :
    Raw.stateValid after.quantum = true := by
  obtain ⟨work,left,ran⟩ := read
  exact (Raw.Observation.checkOps_invariants _ _ _ _ _ work left ran).1

private theorem positive {dependencies fuel before after ops}
    (read : RuntimeInterval.Computed (Raw.Observation.checkOps dependencies fuel before ops) after) :
    ∃ depth, fuel = depth+1 := by
  cases fuel with
  | zero => obtain ⟨_,_,refused⟩ := read; cases refused
  | succ depth => exact ⟨depth,rfl⟩

theorem projected_branch_fields {dependencies program block offset roles inputTokens ordinary}
    {actual : @RuntimeInterval.Branch dependencies program block offset}
    {entry : RuntimeOwnerMap.Checked roles actual.interval.before}
    (frame : RuntimeBranchProjection.Checked actual entry inputTokens ordinary)
    (child : RuntimeInterval.Branch frame.prepared.block 0) :
    actual.condition = child.condition ∧ actual.thenOps = child.thenOps ∧
      actual.elseOps = child.elseOps ∧ child.quantum ⊆ actual.quantum ∧ actual.classical = child.classical := by
  have original := child.original
  change some (Op.branch actual.condition actual.thenOps actual.elseOps (actual.quantum.filter _) actual.classical) =
    _ at original
  obtain ⟨condition,thenOps,elseOps,phis,classical⟩ := Op.branch.inj (Option.some.inj original)
  exact ⟨condition,thenOps,elseOps,fun phi member => (List.mem_filter.mp (phis.symm ▸ member)).1,classical⟩

private theorem valid_arm {dependencies program block offset}
    (actual : @RuntimeInterval.Branch dependencies program block offset) (choice : Bool) :
    Raw.stateValid (if choice then actual.thenState.quantum else actual.elseState.quantum) = true := by
  cases choice
  · exact valid_at actual.elseRead
  · exact valid_at actual.thenRead

private theorem phi_frame_nodup {dependencies program block offset}
    {actual : @RuntimeInterval.Branch dependencies program block offset} (read : Trace actual) :
    (phiInterface actual.quantum).frame.Nodup := by
  rw [← read.joined]
  exact (Raw.Ownership.valid _ (valid_at actual.interval.intervalRead)).frame

/-- All rows and reference columns transport through the actual full and
selected joins using the checked parked owner permutation. -/
theorem original_routed_phi_reorder {dependencies program block offset roles inputTokens ordinary}
    {actual : @RuntimeInterval.Branch dependencies program block offset}
    {entry : RuntimeOwnerMap.Checked roles actual.interval.before}
    (frame : RuntimeBranchProjection.Checked actual entry inputTokens ordinary)
    (child : RuntimeInterval.Branch frame.prepared.block 0) (choice : Bool)
    (parentRead : Trace actual) (childRead : Trace child)
    {actualHistory : Qleisli.Semantics.ObservingAction.History}
    {localHistory : Nat → Qleisli.Semantics.ObservingAction.History} :
    let beforeSpectators := frame.moves.map (·.2.original.thenBinding.port)
    let afterSpectators := frame.moves.map (·.2.original.binding.port)
    let parentArm := (if choice then actual.thenState.quantum else actual.elseState.quantum).reference
    let childArm := (if choice then child.thenState.quantum else child.elseState.quantum).reference
    Partition parentArm childArm beforeSpectators →
    Agrees parentArm childArm beforeSpectators actualHistory localHistory →
    Agrees actual.interval.after.quantum.reference child.interval.after.quantum.reference afterSpectators
      (pureHistory dependencies [.reorder parentArm.frame.length (axes parentArm (phiWires parentArm actual.quantum choice))]
        actualHistory)
      (fun high => pureHistory dependencies [.reorder childArm.frame.length (axes childArm (phiWires childArm child.quantum choice))]
        (localHistory high)) := by
  intro beforeSpectators afterSpectators parentArm childArm partition paired
  have parentPhis := (original_branch_phi_checks actual).1
  have childPhis := (original_branch_phi_checks child).1
  have parentValid := valid_arm actual choice
  have childValid := valid_arm child choice
  have parentGeometry := phi_arm_geometry actual.thenState.quantum actual.elseState.quantum actual.quantum
    parentPhis choice parentValid
  have childGeometry := phi_arm_geometry child.thenState.quantum child.elseState.quantum child.quantum
    childPhis choice childValid
  have parentDistinct := phi_frame_nodup parentRead
  have parentOrder : (axes parentArm (phiWires parentArm actual.quantum choice)).Perm
      (List.range parentArm.frame.length) :=
    (parentGeometry.1.map parentArm.frame.idxOf).trans
      (List.Perm.of_eq (RuntimeNamedCallerAction.self_indices _ (Raw.Ownership.valid _ parentValid).frame))
  have childOrder : (axes childArm (phiWires childArm child.quantum choice)).Perm
      (List.range childArm.frame.length) :=
    (childGeometry.1.map childArm.frame.idxOf).trans
      (List.Perm.of_eq (RuntimeNamedCallerAction.self_indices _ (Raw.Ownership.valid _ childValid).frame))
  have parentWidth := parentGeometry.2.symm.trans parentGeometry.1.length_eq
  have childWidth := childGeometry.2.symm.trans childGeometry.1.length_eq
  have spectators := checked_spectator_phi_slots frame choice parentValid parentDistinct
  have selected := selected_phi_slots actual.thenState.quantum actual.elseState.quantum child.thenState.quantum
    child.elseState.quantum actual.quantum child.quantum choice (projected_branch_fields frame child).2.2.2.1
    parentPhis childPhis parentValid childValid parentDistinct partition
  rw [parentRead.joined,childRead.joined]
  exact reorder_join_with_spectator_phis dependencies _ _ parentOrder childOrder parentWidth childWidth
    spectators selected paired

/-- Relate both fully checked source/Raw branch histories to the exact
selected checker scope, preserving original ordinary and hidden histories.
Only the caller supplies the actual entry partition. -/
theorem original_routed_branch_run {dependencies program block offset roles inputTokens ordinary}
    {actual : @RuntimeInterval.Branch dependencies program block offset}
    {entry : RuntimeOwnerMap.Checked roles actual.interval.before}
    (frame : RuntimeBranchProjection.Checked actual entry inputTokens ordinary)
    (child : RuntimeInterval.Branch frame.prepared.block 0)
    (parentRead : Trace actual) (childRead : Trace child)
    (partition : Partition actual.interval.before.quantum.reference child.interval.before.quantum.reference
      (frame.moves.map (·.2.original.thenBinding.port))) :
    RoutedSegment dependencies actual.childFuel child.childFuel actual.interval.before.quantum.reference
      child.interval.before.quantum.reference actual.interval.after.quantum.reference child.interval.after.quantum.reference
      (frame.moves.map (·.2.original.thenBinding.port)) (frame.moves.map (·.2.original.binding.port))
      [branchEvent actual parentRead.left parentRead.right] [branchEvent child childRead.left childRead.right] := by
  obtain ⟨parentDepth,pDepth⟩ := positive actual.thenRead
  obtain ⟨childDepth,cDepth⟩ := positive child.thenRead
  obtain ⟨cond,thenOps,elseOps,_,classic⟩ := projected_branch_fields frame child
  let before := frame.moves.map (·.2.original.thenBinding.port)
  let after := frame.moves.map (·.2.original.binding.port)
  have arm (choice : Bool) :
      RoutedSegment dependencies parentDepth childDepth actual.interval.before.quantum.reference
        child.interval.before.quantum.reference actual.interval.after.quantum.reference child.interval.after.quantum.reference
        before after (parentRead.armEvents choice) (childRead.armEvents choice) := by
    let pArm := (if choice then actual.thenState.quantum else actual.elseState.quantum).reference
    let cArm := (if choice then child.thenState.quantum else child.elseState.quantum).reference
    have reads : Segment dependencies parentDepth childDepth actual.interval.before.quantum.reference
        child.interval.before.quantum.reference pArm cArm before (parentRead.armBody choice) (childRead.armBody choice) := by
      cases choice
      · have p := actual.elseRead
        have c := child.elseRead
        rw [pDepth] at p
        rw [cDepth,← elseOps] at c
        obtain ⟨pEvents,cEvents,pRead,cRead,run⟩ := checked_operations actual.elseOps p c partition
          (fun op _ => operation_step_law dependencies parentDepth childDepth before op)
        have previousP := parentRead.rightRead
        have previousC := childRead.rightRead
        rw [pDepth] at previousP
        rw [cDepth,← elseOps] at previousC
        have pEq : pEvents = parentRead.right := congrArg Prod.snd (Option.some.inj (pRead.symm.trans previousP))
        have cEq : cEvents = childRead.right := congrArg Prod.snd (Option.some.inj (cRead.symm.trans previousC))
        subst pEvents
        subst cEvents
        exact run
      · have p := actual.thenRead
        have c := child.thenRead
        rw [pDepth] at p
        rw [cDepth,← thenOps] at c
        obtain ⟨pEvents,cEvents,pRead,cRead,run⟩ := checked_operations actual.thenOps p c partition
          (fun op _ => operation_step_law dependencies parentDepth childDepth before op)
        have previousP := parentRead.leftRead
        have previousC := childRead.leftRead
        rw [pDepth] at previousP
        rw [cDepth,← thenOps] at previousC
        have pEq : pEvents = parentRead.left := congrArg Prod.snd (Option.some.inj (pRead.symm.trans previousP))
        have cEq : cEvents = childRead.left := congrArg Prod.snd (Option.some.inj (cRead.symm.trans previousC))
        subst pEvents
        subst cEvents
        exact run
    have routed := reads.finish_routed_arm
      (.reorder pArm.frame.length (axes pArm (phiWires pArm actual.quantum choice)))
      (.reorder cArm.frame.length (axes cArm (phiWires cArm child.quantum choice)))
      (fun _ _ => original_routed_phi_reorder frame child choice parentRead childRead reads.partition)
    cases choice <;> exact routed
  rw [pDepth,cDepth]
  unfold branchEvent
  rw [← cond,← classic]
  exact branch_from_routed_arms actual.condition actual.classical (arm true) (arm false)

#print axioms original_routed_phi_reorder
#print axioms original_routed_branch_run
end Qleisli.RuntimeCallHistory
