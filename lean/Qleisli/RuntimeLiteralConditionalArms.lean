import Qleisli.RuntimeLiteralBodyRefinement
import Qleisli.RuntimeOriginalBranchJoin
import Qleisli.RuntimeIntervalStates
import Qleisli.RuntimeOwnerTransitionAction

/-! Recover the exact checked child traversal of each original ordinary arm.
Its native entry, complete exit, and independently read events are those of
the actual branch. The final source order agrees with the frame used by phis.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeLiteralBody
open QleisliKernel QleisliKernel.Qirf QleisliKernel.SourceTypes QleisliKernel.Finite
open QleisliKernel.Semantics.Observation (Event readOps)
open RuntimePureBody (BlockRunner BlockResult Step Steps reordered runBlockCore)
open RuntimeOwnerMap (Binding Owner)
open Qleisli.RuntimeNamedChildRuns (ConditionalRun Flow core_flow)

private def stepList {dependencies program block} :
    @Steps dependencies program block → List (@Step dependencies program block)
  | .nil => []
  | .cons first rest => first :: stepList rest

private theorem stepList_ofList {dependencies program block} (steps : List (@Step dependencies program block)) :
    stepList (Steps.ofList steps) = steps := by
  induction steps with
  | nil => rfl
  | cons first rest ih => exact congrArg (List.cons first) ih

/-- The actual recursive run supplies the ordered input, flow, exact Raw
events and ordered output. The phi input frame is the same checked result. -/
structure ArmFlow {artifact root mode} (next : BlockRunner artifact root mode)
    {program block} (inputRoles : List Owner) {outputRoles : List Owner}
    (before after : RuntimeStructuralAction.SourceState) (ordinary finalOrdinary : RuntimeOrdinaryBody.State)
    (steps : List (Step root.dependencies program block)) (parent : Raw.Observation.State)
    {rawExit : Raw.Observation.State}
    (output : RuntimeOwnerMap.Checked outputRoles rawExit) (events : List Event) where
  live : block.entry.quantum.live = parent.quantum.live
  axes : block.entry.quantum.frame = parent.quantum.frame
  issued : parent.classical ⊆ block.entry.classical
  input : RuntimeOwnerMap.Checked inputRoles block.entry
  inputRead : RuntimeInterval.Computed (reordered inputRoles block.entry before.bindings) input
  beforeReturn : RuntimeStructuralAction.SourceState
  flow : Flow next {before with bindings := input.bindings} steps beforeReturn ordinary finalOrdinary
    block.operations.length
  last : RuntimeInterval.Checked block block.operations.length 0
  sameExit : last.before = rawExit
  trace : Trace block.entry steps last.before events
  outputRead : RuntimeInterval.Computed (reordered outputRoles rawExit beforeReturn.bindings) output
  returned : after = {beforeReturn with bindings := output.bindings}

private theorem same_checked_map {roles state}
    (first second : RuntimeOwnerMap.Checked roles state) (same : first.bindings.Perm second.bindings) :
    first = second := by
  have unique : (second.bindings.map (fun binding : Binding => binding.owner.ordinal)).Nodup := by
    simpa only [← second.ordered,List.map_map,Function.comp_def] using second.ownersDistinct
  have bindings := RuntimeOwnerTransitionAction.owner_order_eq second.bindings first.bindings
    unique same.subset (first.ordered.trans second.ordered.symm)
  cases first
  cases second
  cases bindings
  rfl

private theorem checked_arm {artifact : Artifact} {root : Validity.Root}
    {mode : RuntimePureBody.ExecutionMode artifact root} {fuel rootOwner rootName owner name program block}
    (source : SourceRuntimeScope.Subject artifact.sources owner name)
    (path : RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName owner name)
    (request : RuntimePureBody.Context) (plan : mode.queries.BodyData source request)
    (before : RuntimeStructuralAction.SourceState) (ordinary : RuntimeOrdinaryBody.State)
    (result : BlockResult root.dependencies program block × List mode.Receipt)
    (child : RuntimeInterval.Computed
      (runBlockCore artifact root mode (fuel+1) .runtimeBody .frame source path program request
        plan before ordinary block) result)
    {rawExit : Raw.Observation.State} (output : RuntimeOwnerMap.Checked source.outputRoles rawExit)
    (sameOutput : output.bindings.Perm result.1.history.bindings)
    {parent : Raw.Observation.State} (live : block.entry.quantum.live = parent.quantum.live)
    (axes : block.entry.quantum.frame = parent.quantum.frame) (issued : parent.classical ⊆ block.entry.classical)
    (rawRead : RuntimeInterval.Computed (Raw.Observation.checkOps root.dependencies block.fuel
      block.entry block.operations) rawExit)
    {events : List Event}
    (literalRead : readOps block.fuel block.entry.quantum.reference block.operations =
      some (rawExit.quantum.reference,events)) :
    Nonempty (ArmFlow (runBlockCore artifact root mode fuel) source.initialRoles before result.1.history
      ordinary result.1.ordinary result.1.steps parent output events) := by
  obtain ⟨input,inputRead,ownerEnd,flow,last,lastRead,returned⟩ :=
    core_flow artifact root mode fuel .frame source path program request plan before ordinary block result child
  have prefixRead : RuntimeInterval.Computed (Raw.Observation.checkOps root.dependencies block.fuel
      block.entry (block.operations.take block.operations.length)) rawExit := by
    simpa only [List.take_length] using rawRead
  have exit := RuntimeIntervalStates.prefix_unique block block.operations.length (Nat.le_refl _)
    last.before rawExit last.prefixRead prefixRead
  have after := (Qleisli.RuntimeOwnerTransitionAction.empty_state last).trans exit
  obtain ⟨otherEvents,trace,read⟩ := flow.literal.original_trace last
  have sameEvents : otherEvents = events :=
    congrArg Prod.snd (Option.some.inj (read.symm.trans literalRead))
  subst otherEvents
  have order : ∃ frame : RuntimeOwnerMap.Checked source.outputRoles rawExit,
      RuntimeInterval.Computed (reordered source.outputRoles rawExit ownerEnd.bindings) frame ∧
        result.1.history = {ownerEnd with bindings := frame.bindings} := by
    rw [← after]
    exact returned
  obtain ⟨frame,orderRead,final⟩ := order
  have same : output.bindings.Perm frame.bindings := by
    have bindings := congrArg RuntimeStructuralAction.SourceState.bindings final
    exact sameOutput.trans (List.Perm.of_eq bindings)
  cases same_checked_map output frame same
  exact ⟨⟨live,axes,issued,input,inputRead,ownerEnd,flow,last,exit,trace,orderRead,final⟩⟩

private theorem else_keeps_issued {dependencies program block offset}
    (actual : @RuntimeInterval.Branch dependencies program block offset) :
    actual.interval.before.classical ⊆ actual.elseBlock.entry.classical := by
  obtain ⟨work,left,read⟩ := actual.thenRead
  exact (Raw.Observation.checkOps_history _ _ _ _ _ work left read).2.2

def ConditionalArms {artifact root mode} (next : BlockRunner artifact root mode)
    {program block} (step : Step root.dependencies program block) : Prop :=
  match step with
  | .conditional (before := before) (left := left) (right := right) (ordinary := ordinary)
      (leftOrdinary := leftOrdinary) (rightOrdinary := rightOrdinary) _ event _ actual _ action thenSteps elseSteps =>
    ∀ trace : Qleisli.RuntimeOriginalBranch.Trace actual,
      Nonempty (ArmFlow next (event.held ++ SourceRuntimeValues.owners event.before)
        before left ordinary leftOrdinary (stepList thenSteps) actual.interval.before action.thenFrame trace.left) ∧
      Nonempty (ArmFlow next (event.held ++ SourceRuntimeValues.owners event.before)
        before right ordinary rightOrdinary (stepList elseSteps) actual.interval.before action.elseFrame trace.right)
  | _ => True

/-- The exact receipt stored at the parent step supplies both child runs.
Both proofs use the same original block traversal as the parent proof. -/
theorem conditional_arms {artifact root mode fuel program block step}
    (call : @ConditionalRun artifact root mode (runBlockCore artifact root mode (fuel+1)) program block step) :
    ConditionalArms (runBlockCore artifact root mode fuel) step := by
  cases call with
  | @checked offset rootOwner rootName caller name path event source sameName actual actualRead
      leftRequest rightRequest leftPlan rightPlan before ordinary left right leftReceipts rightReceipts
      action beforeThen afterThen afterElse afterJoin thenRead elseRead joinRead =>
    intro trace
    constructor
    · simpa only [stepList_ofList] using
        checked_arm (mode := mode) (fuel := fuel) (block := actual.thenBlock)
          (.arm event sameName source.bodies source.original true) path leftRequest leftPlan before ordinary
          (left,leftReceipts) ⟨beforeThen,afterThen,thenRead⟩ action.thenFrame action.thenMap
          (parent := actual.interval.before) rfl rfl (fun _ found => found) actual.thenRead trace.leftRead
    · simpa only [stepList_ofList] using
        checked_arm (mode := mode) (fuel := fuel) (block := actual.elseBlock)
          (.arm event sameName source.bodies source.original false) path rightRequest rightPlan before ordinary
          (right,rightReceipts) ⟨afterThen,afterElse,elseRead⟩ action.elseFrame action.elseMap
          (parent := actual.interval.before) rfl rfl (else_keeps_issued actual) actual.elseRead trace.rightRead

#print axioms conditional_arms
end Qleisli.RuntimeLiteralBody
