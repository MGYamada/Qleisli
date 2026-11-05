import Qleisli.RuntimeNamedSelectionWholeOutput

/-! Compose the original pre, choose and post calls at their actual source
and Raw state boundaries. Input storage and retained owner receipts supply
the intermediate frames used by the three actions.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeNamedThreeFrameChain
open QleisliKernel QleisliKernel.Qirf
open RuntimeOwnerMap (Binding Map)
open RuntimeForestCode RuntimeOwnerCodeReindex
open Qleisli.RuntimeForestProduct Qleisli.RuntimeNamedBlockEncoding
open Qleisli.RuntimeNamedSelectionReturnOrder

/-- The reader depends on the complete basis and valid port shape. A primitive
may change the returned source ordinal and the native token. -/
theorem primitive_owner_code {beforeRoles before afterRoles after}
    (input : RuntimeOwnerMap.Checked beforeRoles before)
    (output : RuntimeOwnerMap.Checked afterRoles after)
    (validBefore : Raw.stateValid before.quantum = true) (validAfter : Raw.stateValid after.quantum = true)
    (old current : Binding) (oldMember : old ∈ input.bindings) (currentMember : current ∈ output.bindings)
    (sameBasis : current.owner.basis = old.owner.basis)
    (sameWires : current.port.wires = old.port.wires)
    (code : OwnerCode old) : Nonempty (OwnerCode current) := by
  have oldPort : old.port ∈ before.quantum.live := input.complete.mem_iff.mp (List.mem_map_of_mem oldMember)
  have currentPort : current.port ∈ after.quantum.live := output.complete.mem_iff.mp (List.mem_map_of_mem currentMember)
  have oldShape := ((Raw.Ownership.valid before.quantum validBefore).ports old.port oldPort).1
  have currentShape := ((Raw.Ownership.valid after.quantum validAfter).ports current.port currentPort).1
  have bits : current.port.bits = old.port.bits := currentShape.trans
    ((congrArg List.length sameWires).trans oldShape.symm)
  refine ⟨⟨code.layout,?_⟩⟩
  have read : Carrier.readOwner ⟨current.port,current.owner.basis⟩ =
      Carrier.readOwner ⟨old.port,old.owner.basis⟩ := by
    unfold Carrier.readOwner
    rw [sameBasis,bits,sameWires]
  rw [read]
  exact code.original

def PrimitiveAfterFrame {dependencies program block step}
    (held : @RuntimeNamedPrimitiveOccurrence.Occurrence dependencies program block step) : Prop :=
  match held with
  | .named (before := before) (scope := scope) (boundary := boundary) _ _ =>
    ∀ {roles} (checked : RuntimeOwnerMap.Checked roles scope.interval.before) (_input : Frame checked),
      checked.bindings = before.bindings → Nonempty (Frame boundary.afterFrame)

/-- Recover each primitive caller after-Frame from its actual input receipts
and the original returned owner. -/
theorem primitive_after_frame {artifact root execution fuel program block step}
    (held : @RuntimeNamedPrimitiveOccurrence.Occurrence root.dependencies program block step)
    (call : RuntimeNamedChildRuns.ChildRun artifact root execution
      (RuntimePureBody.runBlockCore artifact root execution (fuel+1)) step)
    (events : List Semantics.Raw.Event) (on : RuntimeNamedOccurrenceAction.On held events) :
    PrimitiveAfterFrame held := by
  have geometry := RuntimeNamedCallerGeometry.actual_geometry held call events on
  cases held with
  | @named start count inputs sources caller before childHistory childRetired ordinary first size inputToken outputToken role kind
      event scope body read boundary finalOrdinary primitive original bound =>
    intro roles checked input same
    obtain ⟨target,mapped,basis,wires,_frame,spectators⟩ := geometry checked same
    have targetMember : target ∈ boundary.afterFrame.bindings := by
      rw [boundary.sameAfter,boundary.afterBindings,mapped]
      exact List.mem_append_right _ List.mem_cons_self
    have selectedMember : bound.binding ∈ checked.bindings := by
      rw [same]
      apply (RuntimeSelectionPartition.order_values _ _ _ boundary.input.orderRead).1
      exact (congrArg (fun bindings => bound.binding ∈ bindings) bound.singleton).mpr
        (List.mem_singleton_self _)
    obtain ⟨oldCode,_⟩ := lookup_exists input.owners bound.binding selectedMember
    obtain ⟨newCode⟩ := primitive_owner_code checked boundary.afterFrame
      scope.interval.history.1 scope.interval.history.2.2.1 bound.binding target
      selectedMember targetMember basis wires oldCode
    obtain ⟨rest,_⟩ := reindex_exists input.owners (checked.bindings.erase bound.binding) List.erase_subset
    have retained := (spectators.symm ▸ rest)
    obtain ⟨all,_⟩ := reindex_exists (.cons newCode retained) boundary.afterFrame.bindings
      (List.perm_cons_erase targetMember).subset
    exact RuntimeForestFrameEvidence.of_ownerCodes boundary.afterFrame ⟨all⟩

/-- Map the actual returned child codes and retain the same caller spectators.
The actual after-map fixes their order. -/
theorem selection_after_frame
    {dependencies program block callStart callCount inputs ordinary effect sources caller before child retired value}
    {event : SourceTypes.SourceRuntimeContext.NamedEvent sources caller}
    (scope : @RuntimeCallScope.Checked dependencies program block callStart callCount inputs ordinary effect)
    (boundary : RuntimeNamedBoundary.Checked scope.interval inputs event before child retired value)
    {childRoles childState childChecked} (childOutput : @Frame childRoles childState childChecked)
    (returned : child.bindings.Perm childChecked.bindings)
    {roles} (checked : RuntimeOwnerMap.Checked roles scope.interval.before) (input : Frame checked)
    (same : checked.bindings = before.bindings) : Nonempty (Frame boundary.afterFrame) := by
  let spectators := RuntimeSelectionPartition.complement checked.bindings boundary.input.ordered
  have subset : spectators ⊆ checked.bindings := by
    intro b member
    exact (List.mem_filter.mp member).1
  obtain ⟨beforeCodes,_⟩ := reindex_exists input.owners spectators subset
  obtain ⟨returnedCodes,_⟩ := reindex_exists childOutput.owners child.bindings returned.subset
  obtain ⟨mappedCodes⟩ := RuntimeNamedSelectionFrames.carrier_codes
    (RuntimeNamedCodeTransport.returned_carriers boundary) returnedCodes
  have order := (caller_after_order scope boundary checked same).1
  exact RuntimeForestFrameEvidence.of_ownerCodes boundary.afterFrame
    ⟨(order.symm ▸ append beforeCodes mappedCodes)⟩

#print axioms primitive_after_frame
#print axioms selection_after_frame

def checkedAt {roles before after}
    (same : before = after) (checked : RuntimeOwnerMap.Checked roles before) :
    RuntimeOwnerMap.Checked roles after := same ▸ checked

def frameAt {roles before after} (same : before = after)
    {checked : RuntimeOwnerMap.Checked roles before} (frame : Frame checked) :
    Frame (checkedAt same checked) := by
  cases same
  exact frame

theorem checkedAt_bindings {roles before after} (same : before = after)
    (checked : RuntimeOwnerMap.Checked roles before) :
    (checkedAt same checked).bindings = checked.bindings := by cases same; rfl

theorem frameAt_action {roles before after} (same : before = after)
    {checked : RuntimeOwnerMap.Checked roles before} (frame : Frame checked)
    {Reference : Type} (joint : Nat → Reference → ℂ) (physical : Nat) (ref : Reference) :
    referenceAction (frameAt same frame) joint physical ref =
      referenceAction frame joint physical ref := by cases same; rfl

open Qleisli.RuntimeNamedSelectionWholeOutput
open Qleisli.RuntimeNamedCallerAction (updatedJoint)
open Qleisli.RuntimeForestOrderedProduct
open Qleisli.RuntimeNamedSourceFlow (entryState exitState)

def Composed {dependencies program block preStep centerStep postStep rootItem rootCount}
    {witness : @RuntimeSelectionSteps.Witness dependencies rootItem rootCount}
    (pre : @RuntimeNamedPrimitiveOccurrence.Occurrence dependencies program block preStep)
    (center : @RuntimeNamedThreeOccurrence.Middle dependencies program block centerStep)
    (post : @RuntimeNamedPrimitiveOccurrence.Occurrence dependencies program block postStep)
    (held : RuntimeNamedThreeOccurrence.RetainedData witness center)
    (a b c : List Semantics.Raw.Event) : Prop :=
  match preStep,centerStep,postStep,pre,center,post,held with
  | _,_,_,.named (before := before) (scope := preScope) (boundary := preBoundary) (action := preOp) _ preBound,
    .named (childHistory := child) (scope := centerScope) (boundary := centerBoundary) _ _,
    .named (scope := postScope) (boundary := postBoundary) (action := postOp) _ postBound,held =>
    match held.literal with
    | .selection (frame := frame) (inputCode := inCode) (outputCode := outCode)
        (retained := retained) (labels := labels) (expected := expected)
        (codes := codes) (layouts := layouts) literal _ =>
      ∀ {roles} (checked : RuntimeOwnerMap.Checked roles preScope.interval.before)
        (input : Frame checked), checked.bindings = before.bindings →
        ∃ firstState : preScope.interval.after = centerScope.interval.before,
        ∃ secondState : centerScope.interval.after = postScope.interval.before,
        ∃ first : Frame preBoundary.afterFrame,
        ∃ second : Frame centerBoundary.afterFrame,
        ∃ output : Frame postBoundary.afterFrame,
        ∃ preReturned postReturned : Binding,
          preBoundary.mapped = [preReturned] ∧ postBoundary.mapped = [postReturned] ∧
          let centerInput := frameAt firstState first
          let postInput := frameAt secondState second
          let selected := centerBoundary.input.ordered
          let spectators := RuntimeSelectionPartition.complement
            (checkedAt firstState preBoundary.afterFrame).bindings selected
          ∃ selectedCodes : OwnerCodes selected, ∃ beforeCodes : OwnerCodes spectators,
            reindex centerInput.owners (selected++spectators) = some (append selectedCodes beforeCodes) ∧
            ∃ mappedCodes : OwnerCodes centerBoundary.mapped, ∃ afterCodes : OwnerCodes spectators,
              reindex second.owners (centerBoundary.mapped++spectators) = some (append mappedCodes afterCodes) ∧
              ∃ table : Qleisli.RuntimeMultiwayGram.OrdinalTable inCode outCode retained.sectors labels expected,
              ∀ {Reference : Type} (joint : Nat → Reference → ℂ) physical reference,
                Qleisli.Semantics.RawAction.events dependencies (a++b++c)
                  (fun row => referenceAction input joint row reference) physical =
                referenceAction output (updatedJoint postInput output postBound.binding postReturned postOp.expected
                  (callerUpdate centerInput literal.outputCode second (selected++spectators)
                    child.bindings (centerBoundary.mapped++spectators)
                    (sparseProduct selectedCodes).dimension (sparseProduct mappedCodes).dimension
                    (Qleisli.RuntimeMultiwayGram.sourceAction frame codes layouts literal table)
                    (updatedJoint input first preBound.binding preReturned preOp.expected joint))) physical reference

/-- Compose the authentic three logical actions at both complete original
source maps and Raw state boundaries. Both intermediate Frames are derived. -/
theorem compose_sites {artifact root execution fuel program block preStep centerStep postStep rootItem rootCount}
    {witness : @RuntimeSelectionSteps.Witness root.dependencies rootItem rootCount}
    (pre : @RuntimeNamedPrimitiveOccurrence.Occurrence root.dependencies program block preStep)
    (center : @RuntimeNamedThreeOccurrence.Middle root.dependencies program block centerStep)
    (post : @RuntimeNamedPrimitiveOccurrence.Occurrence root.dependencies program block postStep)
    (held : RuntimeNamedThreeOccurrence.RetainedData witness center)
    (coverage : RuntimeNamedSelectionOn.Coverage center held)
    (preCall : RuntimeNamedChildRuns.ChildRun artifact root execution
      (RuntimePureBody.runBlockCore artifact root execution (fuel+1)) preStep)
    (centerCall : RuntimeNamedChildRuns.ChildRun artifact root execution
      (RuntimePureBody.runBlockCore artifact root execution (fuel+1)) centerStep)
    (postCall : RuntimeNamedChildRuns.ChildRun artifact root execution
      (RuntimePureBody.runBlockCore artifact root execution (fuel+1)) postStep)
    (a b c : List Semantics.Raw.Event)
    (preOn : RuntimeNamedOccurrenceAction.On pre a)
    (centerOn : RuntimeNamedSelectionOn.On b center held)
    (postOn : RuntimeNamedOccurrenceAction.On post c)
    (firstSource : exitState preStep = entryState centerStep)
    (secondSource : exitState centerStep = entryState postStep)
    (firstRaw : (RuntimeNamedOccurrenceAction.span pre).slice.interval.after =
      (RuntimeNamedSelectionOn.middle center held coverage).slice.interval.before)
    (secondRaw : (RuntimeNamedSelectionOn.middle center held coverage).slice.interval.after =
      (RuntimeNamedOccurrenceAction.span post).slice.interval.before) :
    Composed pre center post held a b c := by
  have preFrame := primitive_after_frame pre preCall a preOn
  have postFrame := primitive_after_frame post postCall c postOn
  have preLaw := RuntimeNamedCallerAction.actual_whole_caller_action pre preCall a preOn
  have centerLaw := actual_occurrence_whole_output center centerCall held coverage b centerOn
  have postLaw := RuntimeNamedCallerAction.actual_whole_caller_action post postCall c postOn
  have returned := actual_occurrence_return_order center centerCall held coverage
  cases pre with
  | @named pStart pCount pInputs pSources pCaller pBefore pChild pRetired pOrdinary pFirst pSize pIn pOut pRole pKind
      pEvent pScope pBody pRead pBoundary pFinal pPrimitive pOriginal pBound =>
    cases center with
    | @named mStart mCount mInputs mSources mCaller mBefore mChild mRetired mOrdinary mEvent mScope mBody
        mRead mBoundary mFinal mNode mSelected =>
      cases post with
      | @named qStart qCount qInputs qSources qCaller qBefore qChild qRetired qOrdinary qFirst qSize qIn qOut qRole qKind
          qEvent qScope qBody qRead qBoundary qFinal qPrimitive qOriginal qBound =>
        dsimp only [Composed,OccurrenceWholeOutput,OccurrenceReturnOrder] at *
        change pScope.interval.after = mScope.interval.before at firstRaw
        change mScope.interval.after = qScope.interval.before at secondRaw
        change some pBoundary.after = some mBefore at firstSource
        change some mBoundary.after = some qBefore at secondSource
        cases stored : held.literal with
        | @selection first size localInputs outputs selector target frame selectorBits targetBits retained restricted
            inputCode outputCode labels expected logical equations codes layouts literal nativeRead =>
          rw [stored] at centerLaw returned
          intro roles checked input same
          obtain ⟨firstFrame⟩ := preFrame checked input same
          let centerInput := frameAt firstRaw firstFrame
          have centerSame : (checkedAt firstRaw pBoundary.afterFrame).bindings = mBefore.bindings :=
            (checkedAt_bindings firstRaw _).trans (pBoundary.sameAfter.trans
              (congrArg RuntimeStructuralAction.SourceState.bindings (Option.some.inj firstSource)))
          obtain ⟨secondFrame⟩ := selection_after_frame mScope mBoundary literal.outputCode returned.1
            _ centerInput centerSame
          let postInput := frameAt secondRaw secondFrame
          have postSame : (checkedAt secondRaw mBoundary.afterFrame).bindings = qBefore.bindings :=
            (checkedAt_bindings secondRaw _).trans (mBoundary.sameAfter.trans
              (congrArg RuntimeStructuralAction.SourceState.bindings (Option.some.inj secondSource)))
          obtain ⟨outputFrame⟩ := postFrame _ postInput postSame
          obtain ⟨preReturned,preMapped,preAction⟩ := preLaw checked input same firstFrame
          obtain ⟨postReturned,postMapped,postAction⟩ := postLaw _ postInput postSame outputFrame
          obtain ⟨_same,selectedCodes,beforeCodes,inputRead,mappedCodes,afterCodes,outputRead,table,chooseAction⟩ :=
            centerLaw _ centerInput centerSame secondFrame
          refine ⟨firstRaw,secondRaw,firstFrame,secondFrame,outputFrame,preReturned,postReturned,
            preMapped,postMapped,selectedCodes,beforeCodes,inputRead,mappedCodes,afterCodes,outputRead,table,?_⟩
          intro Reference joint physical reference
          have firstAction :
              Qleisli.Semantics.RawAction.events root.dependencies a
                (fun row => referenceAction input joint row reference) =
              fun row => referenceAction centerInput
                (updatedJoint input firstFrame pBound.binding preReturned pPrimitive.expected joint) row reference := by
            funext row
            rw [frameAt_action]
            exact preAction joint row reference
          let firstJoint := updatedJoint input firstFrame pBound.binding preReturned pPrimitive.expected joint
          let chosen := mBoundary.input.ordered
          let spectators := RuntimeSelectionPartition.complement (checkedAt firstRaw pBoundary.afterFrame).bindings chosen
          let middleJoint := callerUpdate centerInput literal.outputCode secondFrame (chosen++spectators)
            mChild.bindings (mBoundary.mapped++spectators) (sparseProduct selectedCodes).dimension
            (sparseProduct mappedCodes).dimension
            (Qleisli.RuntimeMultiwayGram.sourceAction frame codes layouts literal table) firstJoint
          have joined :
              Qleisli.Semantics.RawAction.events root.dependencies b
                (fun row => referenceAction centerInput firstJoint row reference) =
              fun row => referenceAction postInput middleJoint row reference := by
            funext row
            rw [frameAt_action]
            exact chooseAction firstJoint row reference
          simp only [Qleisli.Semantics.RawAction.events,List.foldl_append] at firstAction joined ⊢
          rw [firstAction,joined]
          exact postAction middleJoint physical reference

#print axioms compose_sites

def EntryFrame {dependencies program block step roles}
    (pre : @RuntimeNamedPrimitiveOccurrence.Occurrence dependencies program block step)
    (initial : RuntimeOwnerMap.Checked roles block.entry) : Prop :=
  match pre with
  | .named (scope := scope) (before := before) _ _ =>
    ∃ same : block.entry = scope.interval.before, ∃ _frame : Frame (checkedAt same initial),
      (checkedAt same initial).bindings = before.bindings

theorem prefix_zero {dependencies program start count}
    (root : RuntimeInterval.Prepared dependencies program)
    (interval : RuntimeInterval.Checked root.block start count) (zero : start = 0) :
    root.block.entry = interval.before := by
  have valid := (RuntimeNamedFrameAxes.initialized root.inputRead).2.1
  apply RuntimeIntervalStates.prefix_unique root.block start
    (Nat.le_trans (Nat.le_add_right start count) interval.range)
  · simpa only [zero,List.take_zero] using RuntimeIntervalStates.empty_read dependencies 64 root.entry valid
  · exact interval.prefixRead

theorem entry_frame {dependencies program} (root : RuntimeInterval.Prepared dependencies program)
    {step roles} (pre : @RuntimeNamedPrimitiveOccurrence.Occurrence dependencies program root.block step)
    (initial : RuntimeOwnerMap.Checked roles root.block.entry)
    (codes : Nonempty (OwnerCodes initial.bindings))
    (source : RuntimeStructuralAction.SourceState)
    (entry : entryState step = some {source with bindings := initial.bindings})
    (starts : (RuntimeNamedOccurrenceAction.span pre).start = 0) :
    EntryFrame pre initial := by
  cases pre with
  | @named start count inputs sources caller before childHistory childRetired ordinary first size inputToken outputToken role kind
      event scope body read boundary finalOrdinary primitive original bound =>
    change some before = some {source with bindings := initial.bindings} at entry
    change start = 0 at starts
    obtain ⟨frame⟩ := RuntimeForestFrameEvidence.of_ownerCodes initial codes
    have same := prefix_zero root scope.interval starts
    exact ⟨same,frameAt same frame,(checkedAt_bindings same initial).trans
      (congrArg RuntimeStructuralAction.SourceState.bindings (Option.some.inj entry)).symm⟩

/-- The original input storage supplies the first Frame in the actual
source entry order used by the composed three-call action. -/
theorem original_entry_frame {artifact owner name arguments request prepared order runtime}
    (body : @RuntimeBodyOperations.Checked artifact owner name arguments request prepared order runtime)
    (view : RuntimeNamedThreeOccurrence.Three body.checked.result.steps)
    (starts : (RuntimeNamedOccurrenceAction.span view.prePrimitive).start = 0) :
    let source := QleisliKernel.SourceTypes.SourceRuntimeScope.Subject.whole prepared.source.body
    let initial := RuntimeBodyOperations.initialHistory prepared body.checked.native runtime body.checked.inputs
    ∃ checked : RuntimeOwnerMap.Checked source.initialRoles body.checked.native.block.entry,
      RuntimeInterval.Computed
        (RuntimePureBody.reordered source.initialRoles body.checked.native.block.entry initial.bindings) checked ∧
      EntryFrame view.prePrimitive checked := by
  obtain ⟨checked,read,entry,_joins⟩ := RuntimeNamedSourceFlow.original_three body view
  obtain ⟨original⟩ := RuntimeBoundaryOwnerEvidence.inputs_ownerCodes body.checked.inputs
  have subset := RuntimeNamedPrimitiveOutputs.reordered_subset read
  obtain ⟨codes,_⟩ := reindex_exists original checked.bindings subset
  exact ⟨checked,read,entry_frame body.checked.native view.prePrimitive checked ⟨codes⟩ _ entry starts⟩

#print axioms original_entry_frame
/-- The actual traversal fixes all three source steps and both boundary joins.
The same original whole Raw read retains the three slices and final reorder. -/
theorem original_three_composed {artifact owner name arguments request prepared order runtime}
    (body : @RuntimeBodyOperations.Checked artifact owner name arguments request prepared order runtime)
    (view : RuntimeNamedThreeOccurrence.Three body.checked.result.steps)
    (coverage : RuntimeNamedSelectionOn.Coverage view.centerSelection
      (RuntimeNamedThreeOccurrence.actual_body_middle body view)) :
    let held := RuntimeNamedThreeOccurrence.actual_body_middle body view
    let pre := RuntimeNamedOccurrenceAction.span view.prePrimitive
    let center := RuntimeNamedSelectionOn.middle view.centerSelection held coverage
    let post := RuntimeNamedOccurrenceAction.span view.postPrimitive
    let source := QleisliKernel.SourceTypes.SourceRuntimeScope.Subject.whole prepared.source.body
    let initial := RuntimeBodyOperations.initialHistory prepared body.checked.native runtime body.checked.inputs
    pre.start = 0 → center.start = pre.start+pre.count → post.start = center.start+center.count →
    pre.count+center.count+post.count = body.root.program.operations.length →
    ∃ a b c, RuntimeNamedThreeRoot.Whole body.checked.native pre center post a b c ∧
      Composed view.prePrimitive view.centerSelection view.postPrimitive held a b c ∧
      ∃ checked : RuntimeOwnerMap.Checked source.initialRoles body.checked.native.block.entry,
        RuntimeInterval.Computed
          (RuntimePureBody.reordered source.initialRoles body.checked.native.block.entry initial.bindings) checked ∧
        EntryFrame view.prePrimitive checked := by
  intro held pre center post source initial starts next last covers
  obtain ⟨a,b,c,whole,preOn,centerOn,postOn⟩ :=
    RuntimeNamedThreeRoot.original_body body view coverage starts next last covers
  have calls := RuntimeNamedSourceFlow.original_child_runs body view
  obtain ⟨_initial,_read,_entry,firstSource,secondSource,_last,_exit,_returned⟩ :=
    RuntimeNamedSourceFlow.original_three body view
  exact ⟨a,b,c,whole,compose_sites view.prePrimitive view.centerSelection view.postPrimitive held coverage
    calls.1 calls.2.1 calls.2.2 a b c preOn centerOn postOn firstSource secondSource
    whole.toCenter whole.toPost,original_entry_frame body view starts⟩

#print axioms original_three_composed
end Qleisli.RuntimeNamedThreeFrameChain
