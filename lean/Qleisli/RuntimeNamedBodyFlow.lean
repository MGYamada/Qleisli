import Qleisli.RuntimeNamedSourceFlow
import QleisliKernel.Qirf.RuntimeBodyOperations

/-! Named-boundary source-state continuity for the actual body reader.
The proof follows the real loop, its original source queries and its unchanged
work counter. It supplies no logical action, encoding equality or new acceptance.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeNamedSourceFlow
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Finite
open RuntimePureBody

/-- Every successful actual iteration retains its original entry read, the
complete ordered step list, and the actual final source-return read. The named
state invariant asserts no physical action for the other step constructors. -/
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
      ∃ last, Run {initialHistory with bindings := initial.bindings} result.1.steps last ∧
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
  suffices connected : Run historyStart steps history by
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
      exact ⟨history,finishedData.1.symm ▸ chain.snoc True.intro,finishedData.2⟩
  have advances (before after : QueryState root.dependencies program block execution.queries.Cursor execution.Receipt)
      (start budget remaining : Nat) (incoming : Invariant historyStart before)
      (read : (advance before start).run budget = (.ok after,remaining)) : Invariant historyStart after := by
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
      exact chain.snoc True.intro
  have named_preserves
      (event : SourceTypes.SourceRuntimeContext.NamedEvent artifact.sources owner)
      (position : Position) (origin : RuntimeSourceEvent.Origin (.named event) position)
      (data : execution.queries.EventData source (.named event) position)
      (before after : QueryState root.dependencies program block execution.queries.Cursor execution.Receipt)
      (budget remaining : Nat) (incoming : Invariant historyStart before)
      (read : (step (.named event) position origin data before).run budget = (.ok after,remaining)) :
      Invariant historyStart after := by
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
      refine chain.snoc ?_
      constructor
      · change history = {history with bindings := frame.bindings}
        rw [sameBindings]
      · rfl
    · cases h
  have steps_preserve
      (event : SourceTypes.SourceRuntimeContext.Event artifact.sources owner)
      (position : Position) (origin : RuntimeSourceEvent.Origin event position)
      (data : execution.queries.EventData source event position)
      (before after : QueryState root.dependencies program block execution.queries.Cursor execution.Receipt)
      (budget remaining : Nat) (incoming : Invariant historyStart before)
      (read : (step event position origin data before).run budget = (.ok after,remaining)) :
      Invariant historyStart after := by
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
      exact chain.snoc True.intro
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
      exact chain.snoc True.intro
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
      exact chain.snoc True.intro
    case primitive =>
      split at h
      · obtain ⟨action,e,_action,returned⟩ := bind_success _ _ _ _ _ h
        have same := (pure_success _ _ _ _ returned).1
        subst after
        have chain := entered
        exact chain.snoc True.intro
      · split at h
        · obtain ⟨action,e,_action,returned⟩ := bind_success _ _ _ _ _ h
          have same := (pure_success _ _ _ _ returned).1
          subst after
          have chain := entered
          exact chain.snoc True.intro
        · obtain ⟨performed,e,_performed,returned⟩ := bind_success _ _ _ _ _ h
          rcases performed with ⟨nextHistory,node⟩
          have same := (pure_success _ _ _ _ returned).1
          subst after
          have chain := entered
          exact chain.snoc True.intro
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
        exact chain.snoc True.intro
      · cases h
    all_goals
      obtain ⟨_,e,_owners,failed⟩ := bind_success _ _ _ _ _ h
      cases failed
  have outer_preserves
      (event : SourceTypes.SourceRuntimeContext.Event artifact.sources owner)
      (position : Position) (entry : RuntimeSourceEvent.At (source.events.zip request.positions) event position)
      (data : execution.queries.EventData source event position)
      (before after : QueryState root.dependencies program block execution.queries.Cursor execution.Receipt)
      (budget remaining : Nat) (incoming : Invariant historyStart before)
      (read : (outerStep event position entry data before).run budget = (.ok after,remaining)) :
      Invariant historyStart after := by
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
      apply trace.invariant (Invariant historyStart)
      · simpa only [sameMap] using entered
      · intro child position inner data before after budget remaining incoming childRead
        exact steps_preserve child position _ data before after budget remaining incoming childRead
    all_goals
      exact steps_preserve _ position (.direct source request.positions entry)
        data before after budget remaining incoming read
  have trace := RuntimeBodyQueries.foldEvents_trace execution.queries source
    (source.events.zip request.positions) outerStep opening.events _ _ w₈ w₉ walked
  exact trace.invariant (Invariant historyStart) (Run.nil historyStart)
    (fun event position entry data before after budget remaining incoming read =>
      outer_preserves event position entry data before after budget remaining incoming read)

/-- The same property holds for the actual fuelled recursion, for every
successful original work budget. Recursive child results remain the actual
loop's results; there is no alternate traversal or reset of exact work. -/
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
      (runBlockCore artifact root execution fuel .runtimeBody outputBoundary source path program request
        sourcePlan initialHistory ordinary block) result) :
    ∃ initial : RuntimeOwnerMap.Checked source.initialRoles block.entry,
      RuntimeInterval.Computed (reordered source.initialRoles block.entry initialHistory.bindings) initial ∧
      ∃ last, Run {initialHistory with bindings := initial.bindings} result.1.steps last ∧
        Returned block source.outputRoles last result.1.history := by
  cases fuel with
  | zero =>
    obtain ⟨work,left,ran⟩ := checked
    cases ran
  | succ fuel =>
    exact step_flow artifact root execution (runBlockCore artifact root execution fuel) outputBoundary
      source path program request sourcePlan initialHistory ordinary block result checked

/-- The retained successful traversal of this original project body supplies
its own entry/return reads and state chain. A producer-supplied success or an
assumed equality between adjacent source maps is not a premise. -/
theorem original_body {artifact owner name arguments request prepared order runtime}
    (body : @RuntimeBodyOperations.Checked artifact owner name arguments request prepared order runtime) :
    let source := SourceTypes.SourceRuntimeScope.Subject.whole prepared.source.body
    let initialHistory := RuntimeBodyOperations.initialHistory prepared body.checked.native runtime body.checked.inputs
    ∃ initial : RuntimeOwnerMap.Checked source.initialRoles body.checked.native.block.entry,
      RuntimeInterval.Computed (reordered source.initialRoles body.checked.native.block.entry initialHistory.bindings) initial ∧
      ∃ last, Run {initialHistory with bindings := initial.bindings} body.checked.result.steps last ∧
        Returned body.checked.native.block source.outputRoles last body.checked.result.history := by
  exact core_flow artifact body.root
    (.planned (RuntimeBodyOperations.preparation artifact prepared.source.catalogue)
      (RuntimeBodyOperations.stagedConsumption artifact prepared.source.catalogue body.root))
    128 .rootOrder (.whole prepared.source.body) (.root prepared.source.body) body.root.program request
    prepared.planned.plan _ body.checked.initial.ssa body.checked.native.block
    (body.checked.result,body.checked.receipts) body.checked.traversed

#print axioms step_flow
#print axioms core_flow
#print axioms original_body
end Qleisli.RuntimeNamedSourceFlow
