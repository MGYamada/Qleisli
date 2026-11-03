import QleisliKernel.Qirf.RuntimeNamedSelectionLocal

/-! One original named selection with its real surrounding primitive events.
The same primitive handler used by the common body loop checks every earlier
and later action. All intervals are contiguous slices of the same native root;
the local named scope and complete typed caller return remain separate checks.
No shortened source body, detached root, callback meaning or public dispatcher
is introduced. General source forms and semantic composition remain separate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeNamedSelectionSurroundings
open QleisliKernel Finite SourceTypes
open QleisliKernel.SourceTypes.SourceRuntimeValues (valueOwners ordinary)
abbrev Position := SourceSequence.Position
abbrev SourceState := RuntimeStructuralAction.SourceState
abbrev Map := RuntimeOwnerMap.Map

structure State {dependencies program} (block : RuntimeInterval.Block dependencies program) where
  history : SourceState
  reverseNodes : List (RuntimePureBody.Node dependencies program block) := []
  cursor : Nat := 0

/-- Each original event keeps its exact source offset and literal native
interval. Reverse accumulation avoids repeated copies of checked node lists. -/
def step {sources owner dependencies program block} (state : @State dependencies program block)
    (pair : SourceRuntimeContext.Event sources owner × Position) : WorkM (State block) := do
  let (event,position) := pair
  exactWork (Exact.charge 16)
  guard (position.offset == SourceRuntimeContext.Event.offset event && position.start == state.cursor) .request
  let interval ← RuntimeInterval.check block position.start position.count
  let frame ← RuntimeOwnerMap.checkBindings (state.history.bindings.map (·.owner)) interval.before state.history.bindings
  let (after,node) ← RuntimePureBody.primitiveAt interval state.history frame.val event
  return ⟨after,node :: state.reverseNodes,position.start+position.count⟩

def walk {sources owner dependencies program block}
    (pairs : List (SourceRuntimeContext.Event sources owner × Position)) (initial : @State dependencies program block) :
    WorkM (State block) := pairs.foldlM step initial

structure AtRoot {artifact owner name arguments source request}
    (occurrence : @RuntimeNamedSelectionOccurrence.Prepared artifact owner name arguments source request)
    (root : Validity.Root) (runtime : RuntimeFamily.Request) where
  pureSource : source.body.checked.summary.inferredEffect = .unitary ∧
    source.body.checked.summary.allocated = [] ∧ source.body.checked.summary.consumed = [] ∧
    source.body.checked.summary.nextOrdinal = source.body.checked.summary.nextOwner
  quantumOnly : (source.body.checked.summary.parameterValues.flatMap ordinary).isEmpty = true ∧
    (ordinary source.body.checked.summary.value).isEmpty = true ∧ runtime.inputRows = [[]] ∧
    RuntimeFamily.inputValues runtime = [] ∧ RuntimeFamily.outputValues runtime = []
  native : RuntimeInterval.Prepared root.dependencies root.program
  nativeRead : RuntimeInterval.Computed (RuntimeInterval.prepare root.dependencies root.program) native
  inputs : RuntimeSourceBoundary.Inputs source.body native runtime.inputStorage
  inputsRead : RuntimeInterval.Computed (RuntimeSourceBoundary.readInputs source.body native runtime.inputStorage) inputs
  initial : SourceState
  initialRead : initial = ⟨inputs.owners.bindings,
    source.body.checked.summary.parameterValues.flatMap valueOwners,source.body.checked.summary.nextOwner⟩
  before : State native.block
  beforeRead : RuntimeInterval.Computed (walk occurrence.parts.before ⟨initial,[],0⟩) before
  reachesCall : before.cursor = occurrence.parts.position.start
  call : RuntimeNamedSelectionLocal.Checked occurrence root native.block before.history
  callRead : RuntimeInterval.Computed (RuntimeNamedSelectionLocal.read occurrence root native.block before.history) call
  after : State native.block
  afterRead : RuntimeInterval.Computed (walk occurrence.parts.after
    ⟨call.boundary.after,[],occurrence.parts.position.start+occurrence.parts.position.count⟩) after
  exhausts : after.cursor = root.program.operations.length
  history : after.history.issued = initial.issued ++ source.body.checked.summary.allocated ∧
    occurrence.parts.event.consumed = source.body.checked.summary.consumed ∧
    after.history.nextOrdinal = source.body.checked.summary.nextOrdinal
  finalInterval : RuntimeInterval.Checked native.block root.program.operations.length 0
  finalIntervalRead : RuntimeInterval.Computed
    (RuntimeInterval.check native.block root.program.operations.length 0) finalInterval
  finalBindings : Map
  finalOrder : RuntimeInterval.Computed
    (RuntimeOwnerMap.order (valueOwners source.body.checked.summary.value) after.history.bindings) finalBindings
  finalFrame : RuntimeOwnerMap.Checked (valueOwners source.body.checked.summary.value) finalInterval.after
  sameFinal : finalFrame.bindings = finalBindings
  returned : RuntimeStructuredRoot.Boundary source.body root native runtime
  returnedRead : RuntimeInterval.Computed (RuntimeStructuredRoot.readBoundary source.body root native finalBindings runtime) returned

/-- The body is read unchanged. Its actual source partition drives one
ordered native walk, including both sides of the genuine call. Every owner,
including a zero-width spectator, reaches the final typed storage check. -/
def readAt {artifact owner name arguments source request}
    (occurrence : @RuntimeNamedSelectionOccurrence.Prepared artifact owner name arguments source request)
    (root : Validity.Root) (runtime : RuntimeFamily.Request) : WorkM (AtRoot occurrence root runtime) := do
  let summary := source.body.checked.summary
  exactWork (Exact.charge (32*((summary.parameterValues.map SourceRuntimeValues.valueFields).sum+
    SourceRuntimeValues.valueFields summary.value+Raw.OwnerFlow.fields (summary.allocated ++ summary.consumed)+
    summary.nextOwner+summary.nextOrdinal+1)))
  if pureSource : summary.inferredEffect = .unitary ∧ summary.allocated = [] ∧ summary.consumed = [] ∧
      summary.nextOrdinal = summary.nextOwner then
    if quantumOnly : (summary.parameterValues.flatMap ordinary).isEmpty = true ∧
        (ordinary summary.value).isEmpty = true ∧ runtime.inputRows = [[]] ∧
        RuntimeFamily.inputValues runtime = [] ∧ RuntimeFamily.outputValues runtime = [] then
      let native ← NaturalAffine.witness (RuntimeInterval.prepare root.dependencies root.program)
      let inputs ← NaturalAffine.witness (RuntimeSourceBoundary.readInputs source.body native.val runtime.inputStorage)
      let initial : SourceState := ⟨inputs.val.owners.bindings,summary.parameterValues.flatMap valueOwners,summary.nextOwner⟩
      let before ← NaturalAffine.witness (walk occurrence.parts.before (⟨initial,[],0⟩ : State native.val.block))
      if reachesCall : before.val.cursor = occurrence.parts.position.start then
        let call ← NaturalAffine.witness (RuntimeNamedSelectionLocal.read occurrence root native.val.block before.val.history)
        let after ← NaturalAffine.witness (walk occurrence.parts.after (⟨call.val.boundary.after,[],
          occurrence.parts.position.start+occurrence.parts.position.count⟩ : State native.val.block))
        if exhausts : after.val.cursor = root.program.operations.length then
          if history : after.val.history.issued = initial.issued ++ summary.allocated ∧
              occurrence.parts.event.consumed = summary.consumed ∧ after.val.history.nextOrdinal = summary.nextOrdinal then
            let finalInterval ← NaturalAffine.witness (RuntimeInterval.check native.val.block root.program.operations.length 0)
            let finalBindings ← NaturalAffine.witness (RuntimeOwnerMap.order (valueOwners summary.value) after.val.history.bindings)
            let finalFrame ← RuntimeOwnerMap.checkBindings (valueOwners summary.value) finalInterval.val.after finalBindings.val
            let returned ← NaturalAffine.witness
              (RuntimeStructuredRoot.readBoundary source.body root native.val finalBindings.val runtime)
            return ⟨pureSource,quantumOnly,native.val,by with_reducible exact native.property,
              inputs.val,by with_reducible exact inputs.property,initial,rfl,before.val,
              by with_reducible exact before.property,reachesCall,call.val,by with_reducible exact call.property,
              after.val,by with_reducible exact after.property,exhausts,history,
              finalInterval.val,by with_reducible exact finalInterval.property,
              finalBindings.val,by with_reducible exact finalBindings.property,finalFrame.val,finalFrame.property,
              returned.val,by with_reducible exact returned.property⟩
          else throw .request
        else throw .request
      else throw .request
    else throw .request
  else throw .request

def AtRoot.nodes {artifact owner name arguments source request occurrence root runtime}
    (checked : @AtRoot artifact owner name arguments source request occurrence root runtime) :
    List (RuntimePureBody.Node root.dependencies root.program checked.native.block) :=
  checked.before.reverseNodes.reverse ++ [checked.call.node] ++ checked.after.reverseNodes.reverse

structure Checked {artifact owner name arguments source request}
    (occurrence : @RuntimeNamedSelectionOccurrence.Prepared artifact owner name arguments source request)
    (order : Array Nat) (runtime : RuntimeFamily.Request) where
  root : Validity.Root
  fresh : RuntimeInterval.Computed
    (Validity.checkRootFromRoots artifact order occurrence.rows occurrence.roots .qmatch) root
  checked : AtRoot occurrence root runtime
  consumed : RuntimeInterval.Computed (readAt occurrence root runtime) checked

def read {artifact owner name arguments source request}
    (occurrence : @RuntimeNamedSelectionOccurrence.Prepared artifact owner name arguments source request)
    (order : Array Nat) (runtime : RuntimeFamily.Request) : WorkM (Checked occurrence order runtime) := do
  let root ← NaturalAffine.witness
    (Validity.checkRootFromRoots artifact order occurrence.rows occurrence.roots .qmatch)
  let checked ← NaturalAffine.witness (readAt occurrence root.val runtime)
  return ⟨root.val,by with_reducible exact root.property,checked.val,by with_reducible exact checked.property⟩

end QleisliKernel.Qirf.RuntimeNamedSelectionSurroundings
