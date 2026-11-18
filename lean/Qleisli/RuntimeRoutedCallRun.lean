import Qleisli.RuntimeRoutedAccessHistory
import Qleisli.RuntimeCallHistoryRun
import Qleisli.RuntimeRoutedReturn

/-! Connect the exact original branch and its projected arm histories to
the established named-call source refinement interface.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeCallHistory
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Finite
open Semantics.Observation (Event readOps)
open RuntimeCallTraceFrames (Partition)
open RuntimeObservingPrefix (Issued FreshWrites checkOps_reference_with_fresh_writes)
open RuntimeObservingWrites (WritesWithin readOps_same_writes)
open RuntimeObservingValueRetention (Supports run_values)
open Qleisli.Semantics.ObservingAction (History run)
open RuntimeSemanticForest (product ownerLayout)

/-- The two spectator lists have the same ordered logical product. A raw
phi can change an owner token and its physical wires, but the checked
spectator role carries the same basis at each logical slot. -/
theorem routed_spectator_product {dependencies program block offset roles inputTokens ordinary}
    {actual : @RuntimeInterval.Branch dependencies program block offset}
    {entry : RuntimeOwnerMap.Checked roles actual.interval.before}
    (frame : RuntimeBranchProjection.Checked actual entry inputTokens ordinary) :
    product (frame.moves.map (·.2.original.binding)) =
      product (frame.moves.map (·.2.original.thenBinding)) := by
  unfold product
  rw [List.map_map,List.map_map]
  congr 1
  apply List.map_congr_left
  intro pair _
  simp only [Function.comp_def,ownerLayout,RuntimeBranchProjection.Move.owner]

private theorem prepared_body {dependencies program} (prepared : RuntimeInterval.Prepared dependencies program) :
    RuntimeInterval.Computed (Raw.Observation.checkOps dependencies 65 prepared.entry program.operations)
      prepared.whole.state := by
  obtain ⟨_,_,verified⟩ := prepared.verified
  unfold Raw.Observation.verify at verified
  obtain ⟨_,_,_,verified⟩ := bind_success _ _ _ _ _ verified
  obtain ⟨quantum,_,quantumRead,verified⟩ := bind_success _ _ _ _ _ verified
  obtain ⟨initial,work,ordinaryRead,verified⟩ := bind_success _ _ _ _ _ verified
  obtain ⟨state,left,ran,verified⟩ := bind_success _ _ _ _ _ verified
  obtain ⟨_,_,_,verified⟩ := bind_success _ _ _ _ _ verified
  obtain ⟨_,_,_,verified⟩ := bind_success _ _ _ _ _ verified
  obtain ⟨_,_,_,verified⟩ := bind_success _ _ _ _ _ verified
  have stateAt : prepared.whole.state = state :=
    congrArg Raw.Observation.Checked.state (pure_success _ _ _ _ verified).1
  obtain ⟨_,_,preparedEntry⟩ := prepared.inputRead
  unfold PureInterval.initial at preparedEntry
  obtain ⟨otherQuantum,_,otherQuantumRead,otherOrdinaryRead⟩ := bind_success _ _ _ _ _ preparedEntry
  have sameQuantum : quantum = otherQuantum := Except.ok.inj
    ((lift_success _ _ _ _ quantumRead).1.symm.trans (lift_success _ _ _ _ otherQuantumRead).1)
  subst otherQuantum
  have sameEntry : initial = prepared.entry := Except.ok.inj
    ((lift_success _ _ _ _ ordinaryRead).1.symm.trans (lift_success _ _ _ _ otherOrdinaryRead).1)
  exact ⟨work,left,by rwa [← sameEntry,stateAt]⟩

private theorem projected_exit_state {dependencies program block offset roles inputTokens ordinary}
    {actual : @RuntimeInterval.Branch dependencies program block offset}
    {entry : RuntimeOwnerMap.Checked roles actual.interval.before}
    (frame : RuntimeBranchProjection.Checked actual entry inputTokens ordinary)
    (child : RuntimeInterval.Branch frame.prepared.block 0) :
    child.interval.after = frame.prepared.whole.state := by
  have actualRead := child.interval.intervalRead
  rw [projected_entry_state frame child] at actualRead
  change RuntimeInterval.Computed (Raw.Observation.checkOps dependencies 65 frame.prepared.entry frame.program.operations)
    child.interval.after at actualRead
  exact RuntimeAdjacentSlices.checkOps_unique actualRead (prepared_body frame.prepared)

private theorem allowed_finish (allowed : Nat → Prop) (body : List Event) (finish : Semantics.Raw.Event) :
    WritesWithin (body++[.pure finish]) allowed ↔ WritesWithin body allowed := by
  refine ⟨fun writes _ present _ write => writes (List.mem_append_left _ present) write,?_⟩
  exact fun writes => writes.append (WritesWithin.pures [finish] allowed)

private theorem allowed_branch (allowed : Nat → Prop) (condition : Nat) (yes no : List Event)
    (phis : List Semantics.Observation.ClassicalPhi) :
    WritesWithin [.branch condition yes no phis] allowed ↔
      WritesWithin yes allowed ∧ WritesWithin no allowed ∧ ∀ phi ∈ phis, allowed phi.output := by
  refine ⟨fun writes => ⟨?_,?_,?_⟩,fun held => WritesWithin.singleton ?_⟩
  · exact fun _ present _ write => writes List.mem_cons_self (.thenArm present write)
  · exact fun _ present _ write => writes List.mem_cons_self (.elseArm present write)
  · exact fun _ present => writes List.mem_cons_self (.phi present)
  · intro _ write
    cases write with
    | thenArm present write => exact held.1 present write
    | elseArm present write => exact held.2.1 present write
    | phi present => exact held.2.2 _ present

private theorem original_routed_writes {dependencies program block offset roles inputTokens ordinary}
    {actual : @RuntimeInterval.Branch dependencies program block offset}
    {entry : RuntimeOwnerMap.Checked roles actual.interval.before}
    (frame : RuntimeBranchProjection.Checked actual entry inputTokens ordinary)
    (child : RuntimeInterval.Branch frame.prepared.block 0)
    (parentRead : RuntimeOriginalBranch.Trace actual) (childRead : RuntimeOriginalBranch.Trace child)
    (allowed : Nat → Prop) :
    WritesWithin [RuntimeOriginalBranch.branchEvent actual parentRead.left parentRead.right] allowed ↔
      WritesWithin [RuntimeOriginalBranch.branchEvent child childRead.left childRead.right] allowed := by
  obtain ⟨_,yes,no,_,classical⟩ := projected_branch_fields frame child
  have childYes := childRead.leftRead
  have childNo := childRead.rightRead
  rw [← yes] at childYes
  rw [← no] at childNo
  have left := readOps_same_writes allowed _ _ _ parentRead.leftRead childYes
  have right := readOps_same_writes allowed _ _ _ parentRead.rightRead childNo
  unfold RuntimeOriginalBranch.branchEvent RuntimeOriginalBranch.armFinish
  rw [allowed_branch,allowed_branch,allowed_finish,allowed_finish,allowed_finish,allowed_finish,left,right,classical]

/-- Convert the witnessed pair of native branches to the shared run
interface used for (weighted) original-source refinements. The input
spectators and output spectators may have different physical ports. -/
theorem original_routed_call_run {dependencies program block offset roles inputTokens ordinary}
    {actual : @RuntimeInterval.Branch dependencies program block offset}
    {entry : RuntimeOwnerMap.Checked roles actual.interval.before}
    (frame : RuntimeBranchProjection.Checked actual entry inputTokens ordinary)
    (child : RuntimeInterval.Branch frame.prepared.block 0)
    (parentRead : RuntimeOriginalBranch.Trace actual) (childRead : RuntimeOriginalBranch.Trace child)
    (history : History) (localHistory : Nat → History)
    (agrees : Agrees actual.interval.before.quantum.reference child.interval.before.quantum.reference
      (frame.moves.map (·.2.original.thenBinding.port)) history localHistory)
    {parents : List History}
    (executed : run dependencies block.fuel [RuntimeOriginalBranch.branchEvent actual parentRead.left parentRead.right]
      history = some parents) :
    ∃ children, CallRunOn actual.interval frame.prepared child.interval.after
      (frame.moves.map (·.2.original.binding.port)) history localHistory
      [RuntimeOriginalBranch.branchEvent actual parentRead.left parentRead.right]
      [RuntimeOriginalBranch.branchEvent child childRead.left childRead.right] parents children := by
  have actualRun := executed
  rw [actual.depth] at actualRun
  obtain ⟨children,paired⟩ := original_routed_branch_run frame child parentRead childRead
    (routed_entry_partition frame child) history localHistory agrees parents actualRun
  have pNative := actual.interval.intervalRead
  have cNative := child.interval.intervalRead
  obtain ⟨pWork,pLeft,pRan⟩ := pNative
  obtain ⟨cWork,cLeft,cRan⟩ := cNative
  obtain ⟨_,pEvents,pRead,pWrites⟩ := checkOps_reference_with_fresh_writes _ _ _ _ _ pWork pLeft pRan
  obtain ⟨_,cEvents,cRead,cWrites⟩ := RuntimeObservingPrefix.checkOps_reference_with_writes _ _ _ _ _ cWork cLeft cRan
  have pEq : pEvents = [RuntimeOriginalBranch.branchEvent actual parentRead.left parentRead.right] :=
    congrArg Prod.snd (Option.some.inj (pRead.symm.trans parentRead.parentRead))
  have cEq : cEvents = [RuntimeOriginalBranch.branchEvent child childRead.left childRead.right] :=
    congrArg Prod.snd (Option.some.inj (cRead.symm.trans childRead.parentRead))
  subst pEvents
  subst cEvents
  have out : Partition actual.interval.after.quantum.reference child.interval.after.quantum.reference
      (frame.moves.map (·.2.original.binding.port)) := by
    apply Partition.of_native _ _ _ actual.interval.history.2.2.1 child.interval.history.2.2.1
    rw [projected_exit_state frame child]
    exact frame.completeExit.symm
  have localRead := childRead.parentRead
  rw [projected_entry_state frame child] at localRead
  change readOps frame.prepared.block.fuel frame.prepared.block.entry.quantum.reference
    frame.prepared.block.operations = _ at localRead
  refine ⟨children,⟨out,localRead,?_,pWrites,original_routed_writes frame child parentRead childRead,?_,?_⟩⟩
  · simpa only [actual.depth,child.depth] using paired
  · exact run_values dependencies block.fuel _ history _
      (pWrites.mono (fun _ written => Or.inr written.1)) (fun _ present => Or.inl present) executed
  · intro high result member
    let allowed := fun id => id ∈ history.values.map Prod.fst ∨ Issued child.interval.after id
    have support : Supports allowed (localHistory high) := by
      intro id present
      rw [← agrees.values high] at present
      exact .inl present
    have retained := run_values dependencies _ _ (localHistory high) allowed
      (cWrites.mono (fun _ written => Or.inr written)) support (paired.childRun high) result member
    rw [← agrees.values high] at retained
    exact retained

/-- The child return receipt reads the same projected program at its real
endpoint, including the issued classical state. -/
theorem projected_child_endpoints {dependencies program block offset roles inputTokens ordinary}
    {actual : @RuntimeInterval.Branch dependencies program block offset}
    {entry : RuntimeOwnerMap.Checked roles actual.interval.before}
    (frame : RuntimeBranchProjection.Checked actual entry inputTokens ordinary)
    (child : RuntimeInterval.Branch frame.prepared.block 0)
    (native : RuntimeInterval.Checked frame.prepared.block frame.prepared.block.operations.length 0) :
    native.before = child.interval.after ∧ native.after = child.interval.after := by
  rw [projected_exit_state frame child]
  exact child_endpoints_of_reads frame.prepared (prepared_body frame.prepared) native

/-- Prepare the selected child's history from the complete original input.
The literal prefix checks the coordinate change and the ordered projection
retains the correlated operator on each physically parked spectator slice. -/
theorem original_routed_named_input {dependencies program block sources caller}
    (access : @RuntimePureBody.RoutedAccess dependencies program block sources caller)
    {inherited inputs source history}
    (agrees : RuntimeLiteralBody.SemanticHistoryAgreesWithInherited inherited inputs
      access.closed.route.literal.before access.before access.ordinary source history)
    (input : RuntimeOwnerMap.Checked (SourceTypes.SourceRuntimeScope.Subject.whole access.source).initialRoles
      access.frame.prepared.block.entry)
    {assigned : RuntimeOwnerMap.Map}
    (assignedRead : RuntimeInterval.Computed (RuntimeSourceBoundary.bindings
      (SourceTypes.SourceRuntimeScope.Subject.whole access.source).initialRoles
      ((access.frame.selected.zip (access.boundary.input.ordered.map (·.owner))).map fun (port,role) =>
        (⟨port,role.basis⟩ : Semantics.CarrierInterface.Owner))) assigned)
    (ordered : RuntimeInterval.Computed
      (RuntimePureBody.reordered (SourceTypes.SourceRuntimeScope.Subject.whole access.source).initialRoles
        access.frame.prepared.block.entry assigned) input) :
    let entered := RuntimeExclusiveCoordinates.enterHistory access.opening source
    let parked := access.frame.moves.map (·.2.original.thenBinding)
    RuntimeLiteralBody.SemanticHistoryAgreesWithInherited inherited inputs access.actual.interval.before
      access.opening.initial access.ordinary entered history ∧
    RuntimeSemanticForest.Available access.opening.frame.bindings ∧
    ∃ frame : RuntimeSemanticForest.Frame input.bindings,
      Agrees access.actual.interval.before.quantum.reference access.frame.prepared.block.entry.quantum.reference
        (parked.map (·.port)) history
        (inputHistory frame access.frame.prepared.block.entry.quantum.frame access.opening.frame.bindings
          access.boundary.input.ordered parked entered.operator history) := by
  intro entered parked
  have atEntry : RuntimeLiteralBody.SemanticHistoryAgreesWithInherited inherited inputs
      access.actual.interval.before access.opening.initial access.ordinary entered history :=
    RuntimeExclusiveCoordinates.enter_history_agrees access.opening
      (by simpa only [access.closed.route.literalBefore] using agrees)
  refine ⟨atEntry,?_⟩
  obtain ⟨_,_,_,_,_,_,_,encoded,represented⟩ := atEntry
  let parent : RuntimeSemanticForest.Frame access.opening.frame.bindings := access.opening.nativeBindings.symm ▸ encoded
  refine ⟨parent.available,?_⟩
  exact prepared_routed_history access input assigned assignedRead ordered access.opening.frame rfl parent history
    entered.operator (RuntimeLiteralBody.cast_represents access.opening.nativeBindings.symm encoded represented)

/-- The full literal parent chunk has exactly the original branch event.
The two routing slices contribute only checked owner moves. Use that event
and the actual projected child in the shared call-run relation. -/
theorem original_routed_named_run {dependencies program block sources caller}
    (access : @RuntimePureBody.RoutedAccess dependencies program block sources caller)
    (history : History) (localHistory : Nat → History)
    (agrees : Agrees access.actual.interval.before.quantum.reference
      access.frame.prepared.block.entry.quantum.reference
      (access.frame.moves.map (·.2.original.thenBinding.port)) history localHistory)
    {events : List Event} {parents : List History}
    (read : readOps block.fuel access.closed.route.literal.before.quantum.reference
      ((block.operations.drop (access.offset-RuntimeAccessPartition.activeCount (RuntimeExclusiveAction.places access.access))).take
        (RuntimeAccessPartition.activeCount (RuntimeExclusiveAction.places access.access)+1+
          RuntimeAccessPartition.activeCount (RuntimeExclusiveAction.places access.access))) =
      some (access.closed.route.literal.after.quantum.reference,events))
    (executed : run dependencies block.fuel events history = some parents) :
    ∃ childEvents children,
      CallRunOn access.actual.interval access.frame.prepared access.projected.interval.after
        (access.frame.moves.map (·.2.original.binding.port)) history localHistory
        events childEvents parents children := by
  obtain ⟨parentRead⟩ := RuntimeOriginalBranch.original_branch_events access.actual
  obtain ⟨childRead⟩ := RuntimeOriginalBranch.original_branch_events access.projected
  have literal := routed_checked_events access.opening.route access.closed.route parentRead.parentRead
  rw [access.closed.route.literalBefore,access.closed.route.literalAfter] at read
  have sameEvents : [RuntimeOriginalBranch.branchEvent access.actual parentRead.left parentRead.right] = events :=
    congrArg Prod.snd (Option.some.inj (literal.symm.trans read))
  subst events
  rw [← projected_entry_state access.frame access.projected] at agrees
  obtain ⟨children,paired⟩ := original_routed_call_run access.frame access.projected parentRead childRead
    history localHistory agrees executed
  exact ⟨_,children,paired⟩

#print axioms original_routed_named_input
#print axioms projected_child_endpoints
#print axioms original_routed_named_run
#print axioms original_routed_call_run
#print axioms routed_spectator_product
end Qleisli.RuntimeCallHistory
