import Qleisli.RuntimeNamedSourceFlow
import QleisliKernel.Qirf.RuntimeBodyOperations

/-! Retain actual recursive runs of original named callees and their inputs.
The complete source-state chain and each named child's actual binding/callback
reads follow one proof of the real common loop. Other step constructors receive
no child-provenance assertion. This is not a whole logical-action theorem.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeNamedChildRuns
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Finite
open RuntimePureBody

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

def CheckedStep {artifact root execution} (next : BlockRunner artifact root execution)
    {program block} (step : Step root.dependencies program block) : Prop :=
  match step with
  | .named .. => ChildRun artifact root execution next step
  | .pure .. | .gap .. | .observation .. | .conditional .. => True

structure Flow {artifact root execution} (next : BlockRunner artifact root execution)
    {program block} (initial : RuntimeStructuralAction.SourceState)
    (steps : List (Step root.dependencies program block)) (final : RuntimeStructuralAction.SourceState) : Prop where
  source : RuntimeNamedSourceFlow.Run initial steps final
  calls : ∀ step ∈ steps,CheckedStep next step

theorem Flow.nil {artifact root execution} (next : BlockRunner artifact root execution)
    {program block} (state : RuntimeStructuralAction.SourceState) :
    @Flow artifact root execution next program block state [] state :=
  ⟨.nil _,by intro step member; cases member⟩

theorem Flow.snoc {artifact root execution} {next : BlockRunner artifact root execution}
    {program block initial middle final steps step}
    (flow : @Flow artifact root execution next program block initial steps middle)
    (source : RuntimeNamedSourceFlow.Aligned middle final step) (call : CheckedStep next step) :
    Flow next initial (steps ++ [step]) final := by
  refine ⟨flow.source.snoc source,?_⟩
  intro current member
  rcases List.mem_append.mp member with old | last
  · exact flow.calls current old
  · have same : current = step := List.mem_singleton.mp last
    subst current
    exact call

def Invariant {artifact root execution} (next : BlockRunner artifact root execution)
    {program block} (initial : RuntimeStructuralAction.SourceState)
    (state : QueryState root.dependencies program block execution.queries.Cursor execution.Receipt) : Prop :=
  match state with
  | (history,_,_,_,steps,_,_,_,_) => Flow next initial steps history

open RuntimeNamedSourceFlow (Returned reordered_self)

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
    (initialHistory : RuntimeStructuralAction.SourceState) (ordinary : RuntimeOrdinaryBody.State)
    (block : RuntimeInterval.Block root.dependencies program)
    (result : BlockResult root.dependencies program block × List execution.Receipt)
    (checked : RuntimeInterval.Computed
      (runBlockStep artifact root execution next .runtimeBody outputBoundary source path program request
        sourcePlan initialHistory ordinary block) result) :
    ∃ initial : RuntimeOwnerMap.Checked source.initialRoles block.entry,
      RuntimeInterval.Computed (reordered source.initialRoles block.entry initialHistory.bindings) initial ∧
      ∃ last, Flow next {initialHistory with bindings := initial.bindings} result.1.steps last ∧
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
  extract_lets finish at rest
  have finish_steps (pair : RuntimeOrdinaryBody.State × List (Step root.dependencies program block))
      (value : BlockResult root.dependencies program block × List execution.Receipt)
      (budget remaining : Nat)
      (read : (finish pair).run budget = (.ok value,remaining)) :
      value.1.steps = pair.2 ∧ Returned block source.outputRoles history value.1.history := by
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
    exact ⟨rfl,native,⟨a,b,nativeRead⟩,owners,⟨c,d,ownersRead⟩,rfl⟩
  suffices connected : Flow next historyStart steps history by
    have chain := connected
    split at rest
    · obtain ⟨pair,budget,opened,finished⟩ := bind_success _ _ _ _ _ rest
      have same := (pure_success _ _ _ _ opened).1
      subst pair
      have finishedData := finish_steps (ordinaryAfter,steps) result budget left finished
      exact ⟨history,finishedData.1.symm ▸ chain,finishedData.2⟩
    · obtain ⟨gap,budget,_gap,rest⟩ := bind_success _ _ _ _ _ rest
      obtain ⟨pair,afterGap,opened,finished⟩ := bind_success _ _ _ _ _ rest
      have same := (pure_success _ _ _ _ opened).1
      subst pair
      let gapStep : Step root.dependencies program block :=
        @Step.gap root.dependencies program block cursor (block.operations.length-cursor) history ordinaryAfter gap
      have finishedData := finish_steps (gap.ssa,steps ++ [gapStep]) result afterGap left finished
      exact ⟨history,finishedData.1.symm ▸ chain.snoc True.intro True.intro,finishedData.2⟩
  have advances (before after : QueryState root.dependencies program block execution.queries.Cursor execution.Receipt)
      (start budget remaining : Nat) (incoming : Invariant next historyStart before)
      (read : (advance before start).run budget = (.ok after,remaining)) : Invariant next historyStart after := by
    rcases before with ⟨history,retired,ordinary,actions,steps,obligations,cursor,sourceCursor,receipts⟩
    dsimp only [advance] at read
    obtain ⟨_,middle,_,h⟩ := bind_success _ _ _ _ _ read
    split at h
    · have same := (pure_success _ _ _ _ h).1
      subst after
      exact incoming
    · obtain ⟨gap,afterGap,_gap,h⟩ := bind_success _ _ _ _ _ h
      have same := (pure_success _ _ _ _ h).1
      subst after
      have chain := incoming
      exact chain.snoc True.intro True.intro
  have named_preserves
      (event : SourceTypes.SourceRuntimeContext.NamedEvent artifact.sources owner)
      (position : Position) (origin : RuntimeSourceEvent.Origin (.named event) position)
      (data : execution.queries.EventData source (.named event) position)
      (before after : QueryState root.dependencies program block execution.queries.Cursor execution.Receipt)
      (budget remaining : Nat) (incoming : Invariant next historyStart before)
      (read : (step (.named event) position origin data before).run budget = (.ok after,remaining)) :
      Invariant next historyStart after := by
    dsimp only [step] at read
    obtain ⟨advanced,a,advanceRead,h⟩ := bind_success _ _ _ _ _ read
    have entered := advances before advanced position.start budget a incoming advanceRead
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
      refine chain.snoc ?_ ?_
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
      (budget remaining : Nat) (incoming : Invariant next historyStart before)
      (read : (step event position origin data before).run budget = (.ok after,remaining)) :
      Invariant next historyStart after := by
    cases event
    case named event =>
      exact named_preserves event position origin data before after budget remaining incoming read
    all_goals
      dsimp only [step] at read
      obtain ⟨advanced,a,advanceRead,h⟩ := bind_success _ _ _ _ _ read
      have entered := advances before advanced position.start budget a incoming advanceRead
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
      exact chain.snoc True.intro True.intro
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
      exact chain.snoc True.intro True.intro
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
      exact chain.snoc True.intro True.intro
    case primitive =>
      split at h
      · obtain ⟨action,e,_action,returned⟩ := bind_success _ _ _ _ _ h
        have same := (pure_success _ _ _ _ returned).1
        subst after
        have chain := entered
        exact chain.snoc True.intro True.intro
      · split at h
        · obtain ⟨action,e,_action,returned⟩ := bind_success _ _ _ _ _ h
          have same := (pure_success _ _ _ _ returned).1
          subst after
          have chain := entered
          exact chain.snoc True.intro True.intro
        · obtain ⟨performed,e,_performed,returned⟩ := bind_success _ _ _ _ _ h
          rcases performed with ⟨nextHistory,node⟩
          have same := (pure_success _ _ _ _ returned).1
          subst after
          have chain := entered
          exact chain.snoc True.intro True.intro
    case conditional =>
      obtain ⟨_,e,_count,h⟩ := bind_success _ _ _ _ _ h
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
        exact chain.snoc True.intro True.intro
      · cases h
    all_goals
      obtain ⟨_,e,_owners,failed⟩ := bind_success _ _ _ _ _ h
      cases failed
  have outer_preserves
      (event : SourceTypes.SourceRuntimeContext.Event artifact.sources owner)
      (position : Position) (entry : RuntimeSourceEvent.At (source.events.zip request.positions) event position)
      (data : execution.queries.EventData source event position)
      (before after : QueryState root.dependencies program block execution.queries.Cursor execution.Receipt)
      (budget remaining : Nat) (incoming : Invariant next historyStart before)
      (read : (outerStep event position entry data before).run budget = (.ok after,remaining)) :
      Invariant next historyStart after := by
    cases event
    case staticConditional event children =>
      rcases before with ⟨initialHistory,initialRetired,initialOrdinary,initialActions,initialSteps,initialObligations,initialCursor,initialSourceCursor,initialReceipts⟩
      dsimp only [outerStep] at read
      obtain ⟨actual,a,_actual,h⟩ := bind_success _ _ _ _ _ read
      obtain ⟨advanced,b,advancedRead,h⟩ := bind_success _ _ _ _ _ h
      have entered := advances (initialHistory,initialRetired,initialOrdinary,initialActions,initialSteps,
        initialObligations,initialCursor,initialSourceCursor,initialReceipts) advanced position.start a b incoming advancedRead
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
      apply trace.invariant (Invariant next historyStart)
      · simpa only [sameMap] using entered
      · intro child position inner data before after budget remaining incoming childRead
        exact steps_preserve child position _ data before after budget remaining incoming childRead
    all_goals
      exact steps_preserve _ position (.direct source request.positions entry)
        data before after budget remaining incoming read
  have trace := RuntimeBodyQueries.foldEvents_trace execution.queries source
    (source.events.zip request.positions) outerStep opening.events _ _ w₈ w₉ walked
  exact trace.invariant (Invariant next historyStart) (Flow.nil next historyStart)
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
        {initialHistory with bindings := initial.bindings} result.1.steps last ∧
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
        {initialHistory with bindings := initial.bindings} body.checked.result.steps last ∧
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
