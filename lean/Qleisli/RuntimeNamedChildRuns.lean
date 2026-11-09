import Qleisli.RuntimeNamedSourceFlow
import Qleisli.RuntimeLiteralBody
import QleisliKernel.Qirf.RuntimeBodyOperations

/-! Retain actual recursive runs of original named callees and their inputs.
The complete source-state chain and each named child's actual binding/callback
reads follow one proof of the real common loop, retaining actual primitive
histories and selection input/return maps. Other step constructors receive
no child-provenance assertion. This is not a whole logical-action theorem.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeNamedChildRuns
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Finite
open RuntimePureBody
open RuntimeNamedSourceFlow (NodeAligned)
open RuntimeLiteralBody (At Partition)

/-- The original callee, its complete real argument binding, visible ordinary
SSA and actual recursive result determine this named step's stored child.
The two successful reads share the same remaining-work counter. -/
inductive ChildRun (artifact : Artifact) (root : Validity.Root)
    (execution : ExecutionMode artifact root) (next : BlockRunner artifact root execution) :
    {program : Semantics.Observation.Program} →
    {block : RuntimeInterval.Block root.dependencies program} →
    Step root.dependencies program block → Prop where
  | named {program : Semantics.Observation.Program}
      {block : RuntimeInterval.Block root.dependencies program} {start count inputs caller before ordinary}
      {event : SourceTypes.SourceRuntimeContext.NamedEvent artifact.sources caller}
      {scope : RuntimeCallScope.Checked block start count inputs ordinary event.effect}
      {body : SourceTypes.SourceRuntimeTrace.Body event.target.signature}
      {bodyRead : RuntimeInterval.Computed (SourceTypes.SourceRuntimeTrace.readNamedBody event) body}
      {rootOwner rootName : String}
      {path : RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName
        event.target.resolution.moduleName event.target.resolution.declaration.name}
      {request : Context} {plan : execution.queries.BodyData (.whole body) request}
      {initialBindings : RuntimeOwnerMap.Map}
      {result : BlockResult root.dependencies scope.program scope.prepared.block}
      {receipts : List execution.Receipt}
      {boundary : RuntimeNamedBoundary.Checked scope.interval inputs event before
        result.history result.retired body.checked.summary.value}
      {beforeInput afterInput afterChild : Nat}
      (inputRead : (RuntimeSourceBoundary.bindings
          (body.checked.summary.parameterValues.flatMap SourceTypes.SourceRuntimeValues.valueOwners)
          ((scope.selected.zip event.inputOwners).map fun (port,role) =>
            (⟨port,role.basis⟩ : Semantics.CarrierInterface.Owner))).run beforeInput =
        (.ok initialBindings,afterInput))
      (read : (next .runtimeBody .localScope (.whole body) path scope.program request plan
          ⟨initialBindings,body.checked.summary.parameterValues.flatMap SourceTypes.SourceRuntimeValues.valueOwners,
            body.checked.summary.nextOwner⟩
          scope.visible.ssa scope.prepared.block).run afterInput = (.ok (result,receipts),afterChild)) :
      ChildRun artifact root execution next
        (.named event scope body bodyRead boundary result.ordinary (Steps.ofList result.steps))

/-- Both original recursive arm reads and their checked join share the
remaining-work counters of the original conditional step. -/
inductive ConditionalRun (artifact : Artifact) (root : Validity.Root)
    (execution : ExecutionMode artifact root) (next : BlockRunner artifact root execution) :
    {program : Semantics.Observation.Program} →
    {block : RuntimeInterval.Block root.dependencies program} →
    Step root.dependencies program block → Prop where
  | checked {program : Semantics.Observation.Program}
      {block : RuntimeInterval.Block root.dependencies program} {offset rootOwner rootName caller name}
      {path : RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName caller name}
      {event : SourceTypes.SourceRuntimeContext.BranchEvent artifact.sources caller}
      {source : RuntimeBranchAction.Source event} {sameName : event.callerName = name}
      {actual : @RuntimeInterval.Branch root.dependencies program block offset}
      {actualRead : RuntimeInterval.Computed (RuntimeInterval.readBranch block offset) actual}
      {leftRequest rightRequest : Context}
      {leftPlan : execution.queries.BodyData (.arm event sameName source.bodies source.original true) leftRequest}
      {rightPlan : execution.queries.BodyData (.arm event sameName source.bodies source.original false) rightRequest}
      {before ordinary}
      {left : BlockResult root.dependencies program actual.thenBlock}
      {right : BlockResult root.dependencies program actual.elseBlock}
      {leftReceipts rightReceipts : List execution.Receipt}
      {action : RuntimeBranchAction.Checked path event source actual before left.history right.history
        ordinary left.ordinary right.ordinary}
      {beforeThen afterThen afterElse afterJoin : Nat}
      (thenRead : (next .runtimeBody .frame (.arm event sameName source.bodies source.original true)
          path program leftRequest leftPlan before ordinary actual.thenBlock).run beforeThen =
        (.ok (left,leftReceipts),afterThen))
      (elseRead : (next .runtimeBody .frame (.arm event sameName source.bodies source.original false)
          path program rightRequest rightPlan before ordinary actual.elseBlock).run afterThen =
        (.ok (right,rightReceipts),afterElse))
      (joinRead : (RuntimeBranchAction.read path event source actual before left.history right.history
          ordinary left.ordinary right.ordinary).run afterElse = (.ok action,afterJoin)) :
      ConditionalRun artifact root execution next (.conditional path event source actual actualRead action
        (Steps.ofList left.steps) (Steps.ofList right.steps))

def CheckedStep {artifact root execution} (next : BlockRunner artifact root execution)
    {program block} (step : Step root.dependencies program block) : Prop :=
  match step with
  | .named .. => ChildRun artifact root execution next step
  | .conditional .. => ConditionalRun artifact root execution next step
  | .pure .. | .gap .. | .observation .. => True

/-- The ordinary states belong to the same stored steps as the owner
states. A pure step leaves the complete table and measurement keys intact. -/
def OrdinaryAligned {dependencies program block} (before after : RuntimeOrdinaryBody.State)
    (step : @Step dependencies program block) : Prop :=
  match step with
  | .pure _ => after = before
  | .gap (ordinary := original) gap => before = original ∧ after = gap.ssa
  | .observation (ordinary := original) observation =>
    before = original ∧ after = observation.ordinary
  | .named (ordinary := original) _ _ _ _ _ final _ => before = original ∧ after = final
  | .conditional _ _ _ _ _ (ordinary := original) action _ _ =>
    before = original ∧ after = action.ordinaryAfter

inductive OrdinaryRun {dependencies program block} : RuntimeOrdinaryBody.State →
    List (@Step dependencies program block) → RuntimeOrdinaryBody.State → Prop where
  | nil (state : RuntimeOrdinaryBody.State) : OrdinaryRun state [] state
  | cons {initial middle final first rest}
      (head : OrdinaryAligned initial middle first) (tail : OrdinaryRun middle rest final) :
      OrdinaryRun initial (first :: rest) final

theorem OrdinaryRun.snoc {dependencies program block initial middle final steps step}
    (run : @OrdinaryRun dependencies program block initial steps middle)
    (last : OrdinaryAligned middle final step) :
    OrdinaryRun initial (steps ++ [step]) final := by
  induction run with
  | nil => exact .cons last (.nil _)
  | cons head _ ih => exact .cons head (ih last)

structure Flow {artifact root execution} (next : BlockRunner artifact root execution)
    {program block} (initial : RuntimeStructuralAction.SourceState)
    (steps : List (Step root.dependencies program block)) (final : RuntimeStructuralAction.SourceState)
    (initialOrdinary finalOrdinary : RuntimeOrdinaryBody.State) (cursor : Nat) : Prop where
  source : RuntimeNamedSourceFlow.Run initial steps final
  calls : ∀ step ∈ steps,CheckedStep next step
  ordinary : OrdinaryRun initialOrdinary steps finalOrdinary
  literal : Partition 0 steps cursor

theorem Flow.nil {artifact root execution} (next : BlockRunner artifact root execution)
    {program block} (state : RuntimeStructuralAction.SourceState) (ordinary : RuntimeOrdinaryBody.State) :
    @Flow artifact root execution next program block state [] state ordinary ordinary 0 :=
  ⟨.nil _,(by intro step member; cases member),.nil _,.nil _⟩

theorem Flow.snoc {artifact root execution} {next : BlockRunner artifact root execution}
    {program block initial middle final steps step initialOrdinary middleOrdinary finalOrdinary middleCursor finalCursor}
    (flow : @Flow artifact root execution next program block initial steps middle initialOrdinary middleOrdinary
      middleCursor)
    (source : RuntimeNamedSourceFlow.Aligned middle final step) (call : CheckedStep next step)
    (ordinary : OrdinaryAligned middleOrdinary finalOrdinary step) (literal : At middleCursor finalCursor step) :
    Flow next initial (steps ++ [step]) final initialOrdinary finalOrdinary finalCursor := by
  refine ⟨flow.source.snoc source,?_,flow.ordinary.snoc ordinary,flow.literal.snoc literal⟩
  intro current member
  rcases List.mem_append.mp member with old | last
  · exact flow.calls current old
  · have same : current = step := List.mem_singleton.mp last
    subst current
    exact call

def Invariant {artifact root execution} (next : BlockRunner artifact root execution)
    {program block} (initial : RuntimeStructuralAction.SourceState) (initialOrdinary : RuntimeOrdinaryBody.State)
    (state : QueryState root.dependencies program block execution.queries.Cursor execution.Receipt) : Prop :=
  match state with
  | (history,_,ordinary,_,steps,_,cursor,_,_) => Flow next initial steps history initialOrdinary ordinary cursor

private def cursorOf {dependencies program block Cursor Receipt} :
    @QueryState dependencies program block Cursor Receipt → Nat
  | (_,_,_,_,_,_,cursor,_,_) => cursor

open RuntimeNamedSourceFlow (Returned reordered_self)

private theorem primitive_aligned {sources caller dependencies program block start count}
    (interval : @RuntimeInterval.Checked dependencies program block start count)
    (history : RuntimeStructuralAction.SourceState)
    (frame : {frame : RuntimeOwnerMap.Checked (history.bindings.map (·.owner)) interval.before //
      frame.bindings = history.bindings})
    (event : SourceTypes.SourceRuntimeContext.Event sources caller)
    (location : Option (RuntimeSourceEvent.Location event start count))
    (result : RuntimeStructuralAction.SourceState × Node dependencies program block)
    (checked : RuntimeInterval.Computed (primitiveAt interval history frame event location) result) :
    NodeAligned history result.1 result.2 ∧ At start (start+count) (.pure result.2) := by
  obtain ⟨work,left,ran⟩ := checked
  unfold primitiveAt at ran
  obtain ⟨owners,a,_owners,h⟩ := bind_success _ _ _ _ _ ran
  cases event
  case phase event =>
    obtain ⟨input,b,_input,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨output,c,_output,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨action,d,_action,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨_,e,_charge,h⟩ := bind_success _ _ _ _ _ h
    have same := (pure_success _ _ _ _ h).1
    subst result
    exact ⟨⟨rfl,rfl⟩,rfl,rfl⟩
  case primitive event =>
    obtain ⟨preserving,b,_preserving,h⟩ := bind_success _ _ _ _ _ h
    split at h
    next operand argument =>
      obtain ⟨kind,c,_kind,h⟩ := bind_success _ _ _ _ _ h
      rcases kind with ⟨kind,selection⟩
      obtain ⟨input,d,_input,h⟩ := bind_success _ _ _ _ _ h
      obtain ⟨output,e,_output,h⟩ := bind_success _ _ _ _ _ h
      obtain ⟨action,f,_action,h⟩ := bind_success _ _ _ _ _ h
      obtain ⟨_,g,_charge,h⟩ := bind_success _ _ _ _ _ h
      have same := (pure_success _ _ _ _ h).1
      subst result
      exact ⟨⟨rfl,rfl⟩,rfl,rfl⟩
    all_goals cases h
  all_goals cases h

private theorem operation_aligned {dependencies program}
    (block : RuntimeInterval.Block dependencies program) (position : Position)
    (roles : List RuntimeOwnerMap.Owner) (before after : RuntimeOwnerMap.Map)
    (expected : Semantics.Exact.Matrix) (node : Node dependencies program block)
    (initial final : RuntimeStructuralAction.SourceState)
    (checked : RuntimeInterval.Computed (operationNode block position roles before after expected) node) :
    NodeAligned initial final node ∧ At position.start (position.start+position.count) (.pure node) := by
  obtain ⟨work,left,ran⟩ := checked
  unfold operationNode at ran
  obtain ⟨inputs,a,_inputs,h⟩ := bind_success _ _ _ _ _ ran
  obtain ⟨outputs,b,_outputs,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨frame,c,_frame,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨inputCode,d,_input,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨outputCode,e,_output,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨physical,f,_physical,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨action,g,_action,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,i,_charge,h⟩ := bind_success _ _ _ _ _ h
  split at h
  · have same := (pure_success _ _ _ _ h).1
    subst node
    exact ⟨True.intro,rfl,rfl⟩
  · cases h

private theorem selection_before_transport
    {dependencies program block start count inputs outputs selector target inputCode outputCode}
    {left right : @RuntimeInterval.Checked dependencies program block start count}
    (same : left = right)
    (codes : SelectionCodes left inputs outputs selector target inputCode outputCode) :
    (same ▸ codes).owners.before.bindings = codes.owners.before.bindings := by
  cases same
  rfl

private theorem selection_after_transport
    {dependencies program block start count inputs outputs selector target inputCode outputCode}
    {left right : @RuntimeInterval.Checked dependencies program block start count}
    (same : left = right)
    (codes : SelectionCodes left inputs outputs selector target inputCode outputCode) :
    (same ▸ codes).owners.transport.after.bindings = codes.owners.transport.after.bindings := by
  cases same
  rfl

private theorem selection_aligned {α : Type} (artifact : Artifact)
    {dependencies program block start count roles}
    (interval : @RuntimeInterval.Checked dependencies program block start count)
    (frame : RuntimeOwnerMap.Checked roles interval.before)
    (owners : RuntimeOwnerTransition.Checked interval frame.bindings)
    (selector target : RuntimeOwnerMap.Owner) {moduleName name offset}
    (table : SourceTypes.QuantumArms.Table artifact.sources moduleName name offset selector.basis target.basis)
    (site : RuntimeContextRequest.Site) (initial : α)
    (realize : Fin table.arms.length →
      SourceTypes.QuantumArms.BoundArm artifact.sources moduleName selector.basis target.basis →
      α → WorkM (Semantics.Exact.Matrix × α))
    (result : Node dependencies program block × α)
    (before : RuntimeStructuralAction.SourceState)
    (sameBindings : frame.bindings = before.bindings)
    (checked : RuntimeInterval.Computed
      (selectionNode artifact interval frame owners selector target table site initial realize) result) :
    NodeAligned before {before with bindings := owners.after.bindings} result.1 ∧
      At start (start+count) (.pure result.1) := by
  obtain ⟨work,left,ran⟩ := checked
  unfold selectionNode at ran
  obtain ⟨_,a,_count,h⟩ := bind_success _ _ _ _ _ ran
  obtain ⟨entry,b,_entry,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨exit,c,_exit,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,d,_interface,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨inputCode,e,_input,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨outputCode,f,_output,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨selectorRead,g,_selector,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨targetRead,i,_target,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨walk,j,_walk,h⟩ := bind_success _ _ _ _ _ h
  rcases walk with ⟨meanings,remaining⟩
  obtain ⟨expected,k,_expected,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨attached,l,_attached,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨restriction,m,_restriction,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨logical,n,_logical,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  subst result
  refine ⟨?_,rfl,rfl⟩
  simp only [NodeAligned,selection_before_transport,selection_after_transport]
  exact ⟨sameBindings.symm,True.intro⟩


/-- One proof of the actual iteration retains both the complete state chain
and its named-child computations. The recursive caller is explicit here;
core_flow fixes it to the real previous fuel level. -/
theorem step_flow (artifact : Artifact) (root : Validity.Root)
    (execution : ExecutionMode artifact root) (next : BlockRunner artifact root execution) (outputBoundary : OutputBoundary)
    {rootOwner rootName owner name : String}
    (source : SourceTypes.SourceRuntimeScope.Subject artifact.sources owner name)
    (path : RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName owner name)
    (program : Semantics.Observation.Program) (request : Context)
    (sourcePlan : execution.queries.BodyData source request)
    (initialHistory : RuntimeStructuralAction.SourceState) (initialOrdinary : RuntimeOrdinaryBody.State)
    (block : RuntimeInterval.Block root.dependencies program)
    (result : BlockResult root.dependencies program block × List execution.Receipt)
    (checked : RuntimeInterval.Computed
      (runBlockStep artifact root execution next .runtimeBody outputBoundary source path program request
        sourcePlan initialHistory initialOrdinary block) result) :
    ∃ initial : RuntimeOwnerMap.Checked source.initialRoles block.entry,
      RuntimeInterval.Computed (reordered source.initialRoles block.entry initialHistory.bindings) initial ∧
      ∃ last, Flow next {initialHistory with bindings := initial.bindings} result.1.steps last
        initialOrdinary result.1.ordinary block.operations.length ∧
        Returned block source.outputRoles last result.1.history := by
  obtain ⟨work,left,ran⟩ := checked
  simp (config := {zeta := false}) only [runBlockStep] at ran
  obtain ⟨_,w₁,_signature,rest⟩ := bind_success _ _ _ _ _ ran
  obtain ⟨_,w₂,_effect,rest⟩ := bind_success _ _ _ _ _ rest
  obtain ⟨_,w₃,_ordinal,rest⟩ := bind_success _ _ _ _ _ rest
  obtain ⟨initial,w₄,_initial,rest⟩ := bind_success _ _ _ _ _ rest
  extract_lets historyStart checkFresh consumeGraph advance step pureOnly outerStep at rest
  refine ⟨initial,⟨w₃,w₄,_initial⟩,?_⟩
  obtain ⟨opening,w₅,_opening,rest⟩ := bind_success _ _ _ _ _ rest
  obtain ⟨prefixState,w₆,_prefix,rest⟩ := bind_success _ _ _ _ _ rest
  rcases prefixState with ⟨obligations,sourceCursor,receipts⟩
  obtain ⟨_,w₇,_charge,rest⟩ := bind_success _ _ _ _ _ rest
  obtain ⟨_,w₈,_positions,rest⟩ := bind_success _ _ _ _ _ rest
  obtain ⟨walk,w₉,walked,rest⟩ := bind_success _ _ _ _ _ rest
  rcases walk with ⟨history,retired,ordinaryAfter,actions,steps,obligationsAfter,cursor,sourceCursorAfter,receiptsAfter⟩
  obtain ⟨_,w₁₀,_cursor,rest⟩ := bind_success _ _ _ _ _ rest
  have inBlock : cursor ≤ block.operations.length := by
    have valid := (guard_success _ _ _ _ _cursor).1
    simp only [Bool.and_eq_true] at valid
    exact of_decide_eq_true valid.1
  extract_lets finish at rest
  have finish_steps (pair : RuntimeOrdinaryBody.State × List (Step root.dependencies program block))
      (value : BlockResult root.dependencies program block × List execution.Receipt)
      (budget remaining : Nat)
      (read : (finish pair).run budget = (.ok value,remaining)) :
      value.1.steps = pair.2 ∧ value.1.ordinary = pair.1 ∧ Returned block source.outputRoles history value.1.history := by
    rcases pair with ⟨ordinaryResult,actualSteps⟩
    dsimp only [finish] at read
    obtain ⟨_,a,_,h⟩ := bind_success _ _ _ _ _ read
    obtain ⟨native,b,nativeRead,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨_,c,_,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨owners,d,ownersRead,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨_,e,_,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨_,f,_,h⟩ := bind_success _ _ _ _ _ h
    have same := (pure_success _ _ _ _ h).1
    subst value
    exact ⟨rfl,rfl,native,⟨a,b,nativeRead⟩,owners,⟨c,d,ownersRead⟩,rfl⟩
  suffices connected : Flow next historyStart steps history initialOrdinary ordinaryAfter cursor by
    have chain := connected
    split at rest
    · rename_i atEnd
      have full : cursor = block.operations.length := beq_iff_eq.mp atEnd
      obtain ⟨pair,budget,opened,finished⟩ := bind_success _ _ _ _ _ rest
      have same := (pure_success _ _ _ _ opened).1
      subst pair
      have finishedData := finish_steps (ordinaryAfter,steps) result budget left finished
      exact ⟨history,finishedData.1.symm ▸ finishedData.2.1.symm ▸ full ▸ chain,finishedData.2.2⟩
    · obtain ⟨gap,budget,_gap,rest⟩ := bind_success _ _ _ _ _ rest
      obtain ⟨pair,afterGap,opened,finished⟩ := bind_success _ _ _ _ _ rest
      have same := (pure_success _ _ _ _ opened).1
      subst pair
      let gapStep : Step root.dependencies program block :=
        @Step.gap root.dependencies program block cursor (block.operations.length-cursor) history ordinaryAfter gap
      have finishedData := finish_steps (gap.ssa,steps ++ [gapStep]) result afterGap left finished
      exact ⟨history,finishedData.1.symm ▸ finishedData.2.1.symm ▸
        chain.snoc ⟨rfl,rfl⟩ True.intro ⟨rfl,rfl⟩ ⟨rfl,by
          change cursor+(block.operations.length-cursor) = block.operations.length
          omega⟩,finishedData.2.2⟩
  have advances (before after : QueryState root.dependencies program block execution.queries.Cursor execution.Receipt)
      (start budget remaining : Nat) (incoming : Invariant next historyStart initialOrdinary before)
      (read : (advance before start).run budget = (.ok after,remaining)) :
      Invariant next historyStart initialOrdinary after ∧ cursorOf after = start := by
    rcases before with ⟨history,retired,ordinary,actions,steps,obligations,cursor,sourceCursor,receipts⟩
    dsimp only [advance] at read
    obtain ⟨_,middle,guarded,h⟩ := bind_success _ _ _ _ _ read
    have within : cursor ≤ start := of_decide_eq_true (guard_success _ _ _ _ guarded).1
    split at h
    · rename_i noGap
      have same := (pure_success _ _ _ _ h).1
      subst after
      exact ⟨incoming,beq_iff_eq.mp noGap⟩
    · obtain ⟨gap,afterGap,_gap,h⟩ := bind_success _ _ _ _ _ h
      have same := (pure_success _ _ _ _ h).1
      subst after
      have chain := incoming
      exact ⟨chain.snoc ⟨rfl,rfl⟩ True.intro ⟨rfl,rfl⟩ ⟨rfl,by
        change cursor+(start-cursor) = start
        omega⟩,rfl⟩
  have named_preserves
      (event : SourceTypes.SourceRuntimeContext.NamedEvent artifact.sources owner)
      (position : Position) (origin : RuntimeSourceEvent.Origin (.named event) position)
      (data : execution.queries.EventData source (.named event) position)
      (before after : QueryState root.dependencies program block execution.queries.Cursor execution.Receipt)
      (budget remaining : Nat) (incoming : Invariant next historyStart initialOrdinary before)
      (read : (step (.named event) position origin data before).run budget = (.ok after,remaining)) :
      Invariant next historyStart initialOrdinary after := by
    dsimp only [step] at read
    obtain ⟨advanced,a,advanceRead,h⟩ := bind_success _ _ _ _ _ read
    obtain ⟨entered,atStart⟩ := advances before advanced position.start budget a incoming advanceRead
    rcases advanced with ⟨history,retired,ordinary,actions,steps,obligations,cursor,sourceCursor,receipts⟩
    obtain ⟨_,b,_charge,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨interval,c,_interval,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨certificate,d,_frame,h⟩ := bind_success _ _ _ _ _ h
    rcases certificate with ⟨frame,sameBindings⟩
    obtain ⟨named,e,_named,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨ordered,f,_ordered,h⟩ := bind_success _ _ _ _ _ h
    split at h
    · obtain ⟨opened,g,_opened,h⟩ := bind_success _ _ _ _ _ h
      obtain ⟨bound,i,_bound,h⟩ := bind_success _ _ _ _ _ h
      obtain ⟨childInitial,j,_initial,h⟩ := bind_success _ _ _ _ _ h
      obtain ⟨children,k,_children,h⟩ := bind_success _ _ _ _ _ h
      rcases children with ⟨nested,childReceipts⟩
      obtain ⟨boundary,l,_boundary,returned⟩ := bind_success _ _ _ _ _ h
      have same := (pure_success _ _ _ _ returned).1
      subst after
      have chain := entered
      refine chain.snoc ?_ ?_ ⟨rfl,rfl⟩ ⟨atStart.symm,rfl⟩
      · constructor
        · change history = {history with bindings := frame.bindings}
          rw [sameBindings]
        · rfl
      · exact .named _initial _children
    · cases h
  have steps_preserve
      (event : SourceTypes.SourceRuntimeContext.Event artifact.sources owner)
      (position : Position) (origin : RuntimeSourceEvent.Origin event position)
      (data : execution.queries.EventData source event position)
      (before after : QueryState root.dependencies program block execution.queries.Cursor execution.Receipt)
      (budget remaining : Nat) (incoming : Invariant next historyStart initialOrdinary before)
      (read : (step event position origin data before).run budget = (.ok after,remaining)) :
      Invariant next historyStart initialOrdinary after := by
    cases event
    case named event =>
      exact named_preserves event position origin data before after budget remaining incoming read
    all_goals
      dsimp only [step] at read
      obtain ⟨advanced,a,advanceRead,h⟩ := bind_success _ _ _ _ _ read
      obtain ⟨entered,atStart⟩ := advances before advanced position.start budget a incoming advanceRead
      rcases advanced with ⟨history,retired,ordinary,actions,steps,obligations,cursor,sourceCursor,receipts⟩
      obtain ⟨_,b,_charge,h⟩ := bind_success _ _ _ _ _ h
      obtain ⟨interval,c,_interval,h⟩ := bind_success _ _ _ _ _ h
      obtain ⟨certificate,d,_frame,h⟩ := bind_success _ _ _ _ _ h
      rcases certificate with ⟨frame,sameBindings⟩
    case phase =>
      obtain ⟨performed,e,_performed,returned⟩ := bind_success _ _ _ _ _ h
      rcases performed with ⟨nextHistory,node⟩
      have same := (pure_success _ _ _ _ returned).1
      subst after
      have chain := entered
      obtain ⟨aligned,first,last⟩ := primitive_aligned interval history ⟨frame,sameBindings⟩ _ _ _ ⟨d,e,_performed⟩
      exact chain.snoc aligned True.intro rfl ⟨first.trans atStart.symm,last⟩
    case operation =>
      obtain ⟨owners,e,_owners,h⟩ := bind_success _ _ _ _ _ h
      obtain ⟨_,f,_shape,h⟩ := bind_success _ _ _ _ _ h
      obtain ⟨operation,g,_operation,h⟩ := bind_success _ _ _ _ _ h
      obtain ⟨performed,i,_performed,h⟩ := bind_success _ _ _ _ _ h
      rcases performed with ⟨expected,children,receipts⟩
      obtain ⟨node,j,_node,returned⟩ := bind_success _ _ _ _ _ h
      have same := (pure_success _ _ _ _ returned).1
      subst after
      have chain := entered
      obtain ⟨aligned,first,last⟩ := operation_aligned block position _ _ _ _ node history _ ⟨i,j,_node⟩
      exact chain.snoc aligned True.intro rfl ⟨first.trans atStart.symm,last⟩
    case selection =>
      obtain ⟨owners,e,_owners,h⟩ := bind_success _ _ _ _ _ h
      obtain ⟨selected,f,_selected,h⟩ := bind_success _ _ _ _ _ h
      obtain ⟨performed,g,_performed,h⟩ := bind_success _ _ _ _ _ h
      rcases performed with ⟨logicals,children,cursor,receipts⟩
      obtain ⟨actual,i,_node,returned⟩ := bind_success _ _ _ _ _ h
      rcases actual with ⟨node,extra⟩
      have same := (pure_success _ _ _ _ returned).1
      subst after
      have chain := entered
      obtain ⟨aligned,first,last⟩ := selection_aligned artifact interval frame owners _ _ _ _ _ _
        (node,extra) history sameBindings ⟨g,i,_node⟩
      exact chain.snoc (by simpa only [sameBindings] using aligned) True.intro rfl
        ⟨first.trans atStart.symm,last⟩
    case primitive =>
      split at h
      · obtain ⟨action,e,_action,returned⟩ := bind_success _ _ _ _ _ h
        have same := (pure_success _ _ _ _ returned).1
        subst after
        have chain := entered
        exact chain.snoc True.intro True.intro rfl ⟨atStart.symm,rfl⟩
      · split at h
        · obtain ⟨action,e,_action,returned⟩ := bind_success _ _ _ _ _ h
          have same := (pure_success _ _ _ _ returned).1
          subst after
          have chain := entered
          refine chain.snoc ⟨?_,rfl⟩ True.intro ⟨rfl,rfl⟩ ⟨atStart.symm,rfl⟩
          change history = {history with bindings := frame.bindings}
          rw [sameBindings]
        · obtain ⟨performed,e,_performed,returned⟩ := bind_success _ _ _ _ _ h
          rcases performed with ⟨nextHistory,node⟩
          have same := (pure_success _ _ _ _ returned).1
          subst after
          have chain := entered
          obtain ⟨aligned,first,last⟩ := primitive_aligned interval history ⟨frame,sameBindings⟩ _ _ _ ⟨d,e,_performed⟩
          exact chain.snoc aligned True.intro rfl ⟨first.trans atStart.symm,last⟩
    case conditional =>
      obtain ⟨_,e,_count,h⟩ := bind_success _ _ _ _ _ h
      have one : position.count = 1 := beq_iff_eq.mp (guard_success _ _ _ _ _count).1
      obtain ⟨selected,f,_selected,h⟩ := bind_success _ _ _ _ _ h
      obtain ⟨actual,g,_actual,h⟩ := bind_success _ _ _ _ _ h
      split at h
      · obtain ⟨left,i,_left,h⟩ := bind_success _ _ _ _ _ h
        obtain ⟨right,j,_right,h⟩ := bind_success _ _ _ _ _ h
        rcases left with ⟨thenResult,thenReceipts⟩
        rcases right with ⟨elseResult,elseReceipts⟩
        obtain ⟨action,k,_action,h⟩ := bind_success _ _ _ _ _ h
        obtain ⟨_,l,_charge,returned⟩ := bind_success _ _ _ _ _ h
        have same := (pure_success _ _ _ _ returned).1
        subst after
        have chain := entered
        refine chain.snoc ⟨?_,rfl⟩ (ConditionalRun.checked _left _right _action) ⟨rfl,rfl⟩
          ⟨atStart.symm,by change position.start+1 = position.start+position.count; rw [one]⟩
        change history = {history with bindings := frame.bindings}
        rw [sameBindings]
      · cases h
    all_goals
      obtain ⟨_,e,_owners,failed⟩ := bind_success _ _ _ _ _ h
      cases failed
  have outer_preserves
      (event : SourceTypes.SourceRuntimeContext.Event artifact.sources owner)
      (position : Position) (entry : RuntimeSourceEvent.At (source.events.zip request.positions) event position)
      (data : execution.queries.EventData source event position)
      (before after : QueryState root.dependencies program block execution.queries.Cursor execution.Receipt)
      (budget remaining : Nat) (incoming : Invariant next historyStart initialOrdinary before)
      (read : (outerStep event position entry data before).run budget = (.ok after,remaining)) :
      Invariant next historyStart initialOrdinary after := by
    cases event
    case staticConditional event children =>
      rcases before with ⟨initialHistory,initialRetired,incomingOrdinary,initialActions,initialSteps,initialObligations,initialCursor,initialSourceCursor,initialReceipts⟩
      dsimp only [outerStep] at read
      obtain ⟨actual,a,_actual,h⟩ := bind_success _ _ _ _ _ read
      obtain ⟨advanced,b,advancedRead,h⟩ := bind_success _ _ _ _ _ h
      have entered := (advances (initialHistory,initialRetired,incomingOrdinary,initialActions,initialSteps,
        initialObligations,initialCursor,initialSourceCursor,initialReceipts) advanced position.start a b incoming advancedRead
        ).1
      rcases advanced with ⟨history,retired,ordinary,actions,steps,obligations,cursor,sourceCursor,receipts⟩
      obtain ⟨interval,c,_interval,h⟩ := bind_success _ _ _ _ _ h
      obtain ⟨ordered,d,orderedRead,h⟩ := bind_success _ _ _ _ _ h
      have sameMap : ordered.bindings = history.bindings := reordered_self ⟨c,d,orderedRead⟩
      obtain ⟨_,e,_before,h⟩ := bind_success _ _ _ _ _ h
      obtain ⟨_,f,_charge,h⟩ := bind_success _ _ _ _ _ h
      obtain ⟨walk,g,walked,h⟩ := bind_success _ _ _ _ _ h
      rcases walk with ⟨nextHistory,nextRetired,nextOrdinary,nextActions,nextSteps,nextObligations,nextCursor,nextSourceCursor,nextReceipts⟩
      obtain ⟨_,i,_cursor,h⟩ := bind_success _ _ _ _ _ h
      obtain ⟨_,j,_after,returned⟩ := bind_success _ _ _ _ _ h
      have same := (pure_success _ _ _ _ returned).1
      subst after
      have trace := RuntimeBodyQueries.foldEvents_trace execution.queries source
        (actual.val.sequence.selected.result.events.zip actual.val.positions) _ actual.val.events _ _ f g walked
      apply trace.invariant (Invariant next historyStart initialOrdinary)
      · simpa only [sameMap] using entered
      · intro child position inner data before after budget remaining incoming childRead
        exact steps_preserve child position _ data before after budget remaining incoming childRead
    all_goals
      exact steps_preserve _ position (.direct source request.positions entry)
        data before after budget remaining incoming read
  have trace := RuntimeBodyQueries.foldEvents_trace execution.queries source
    (source.events.zip request.positions) outerStep opening.events _ _ w₈ w₉ walked
  exact trace.invariant (Invariant next historyStart initialOrdinary) (Flow.nil next historyStart initialOrdinary)
    (fun event position entry data before after budget remaining incoming read =>
      outer_preserves event position entry data before after budget remaining incoming read)

/-- Instantiate the callback with the actual previous fuel level, retaining
computed child runs of the real original recursion. -/
theorem core_flow (artifact : Artifact) (root : Validity.Root)
    (execution : ExecutionMode artifact root) (fuel : Nat) (outputBoundary : OutputBoundary)
    {rootOwner rootName owner name : String}
    (source : SourceTypes.SourceRuntimeScope.Subject artifact.sources owner name)
    (path : RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName owner name)
    (program : Semantics.Observation.Program) (request : Context)
    (sourcePlan : execution.queries.BodyData source request)
    (initialHistory : RuntimeStructuralAction.SourceState) (ordinary : RuntimeOrdinaryBody.State)
    (block : RuntimeInterval.Block root.dependencies program)
    (result : BlockResult root.dependencies program block × List execution.Receipt)
    (checked : RuntimeInterval.Computed
      (runBlockCore artifact root execution (fuel+1) .runtimeBody outputBoundary source path program request
        sourcePlan initialHistory ordinary block) result) :
    ∃ initial : RuntimeOwnerMap.Checked source.initialRoles block.entry,
      RuntimeInterval.Computed (reordered source.initialRoles block.entry initialHistory.bindings) initial ∧
      ∃ last, Flow (runBlockCore artifact root execution fuel)
        {initialHistory with bindings := initial.bindings} result.1.steps last ordinary result.1.ordinary
        block.operations.length ∧
        Returned block source.outputRoles last result.1.history :=
  step_flow artifact root execution (runBlockCore artifact root execution fuel) outputBoundary
    source path program request sourcePlan initialHistory ordinary block result checked

/-- The actual root keeps computed runs of all its named children on their
original callees and real native blocks, in addition to full source-state flow.
This does not supply source provenance for other step constructors. -/
theorem original_body {artifact owner name arguments request prepared order runtime}
    (body : @RuntimeBodyOperations.Checked artifact owner name arguments request prepared order runtime) :
    let source := SourceTypes.SourceRuntimeScope.Subject.whole prepared.source.body
    let execution := ExecutionMode.planned
      (RuntimeBodyOperations.preparation artifact prepared.source.catalogue)
      (RuntimeBodyOperations.stagedConsumption artifact prepared.source.catalogue body.root)
    let initialHistory := RuntimeBodyOperations.initialHistory prepared body.checked.native runtime body.checked.inputs
    ∃ initial : RuntimeOwnerMap.Checked source.initialRoles body.checked.native.block.entry,
      RuntimeInterval.Computed (reordered source.initialRoles body.checked.native.block.entry initialHistory.bindings) initial ∧
      ∃ last, Flow (runBlockCore artifact body.root execution 127)
        {initialHistory with bindings := initial.bindings} body.checked.result.steps last
        body.checked.initial.ssa body.checked.result.ordinary body.checked.native.block.operations.length ∧
        Returned body.checked.native.block source.outputRoles last body.checked.result.history := by
  exact core_flow artifact body.root
    (.planned (RuntimeBodyOperations.preparation artifact prepared.source.catalogue)
      (RuntimeBodyOperations.stagedConsumption artifact prepared.source.catalogue body.root))
    127 .rootOrder (.whole prepared.source.body) (.root prepared.source.body) body.root.program request
    prepared.planned.plan _ body.checked.initial.ssa body.checked.native.block
    (body.checked.result,body.checked.receipts) body.checked.traversed

#print axioms step_flow
#print axioms core_flow
#print axioms original_body
end Qleisli.RuntimeNamedChildRuns
