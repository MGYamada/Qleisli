import QleisliKernel.Qirf.RuntimeNamedOrdinaryLocal
import QleisliKernel.Qirf.RuntimeNamedSelectionLocal

/-! One ordered native walk for original pure caller events. Ordinary named
children run the existing common body reader in their literal local scopes;
selection children use the same prepared prefix, arms and local selection
reader. Every continuation receives the preceding complete caller history.
The final typed return includes all spectators, including zero-width owners.
This component issues no handle and supplies no global composition theorem.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeNamedCalls
open QleisliKernel Finite SourceTypes
open QleisliKernel.SourceTypes.SourceRuntimeValues (valueOwners ordinary)
abbrev SourceState := RuntimeStructuralAction.SourceState
abbrev Position := SourceSequence.Position
abbrev Map := RuntimeOwnerMap.Map

structure Primitive {sources caller dependencies program}
    (event : SourceRuntimeContext.Event sources caller) (position : Position)
    (block : RuntimeInterval.Block dependencies program) (before : SourceState) where
  interval : RuntimeInterval.Checked block position.start position.count
  intervalRead : RuntimeInterval.Computed (RuntimeInterval.check block position.start position.count) interval
  frame : {checked : RuntimeOwnerMap.Checked (before.bindings.map (·.owner)) interval.before //
    checked.bindings = before.bindings}
  frameRead : RuntimeInterval.Computed
    (RuntimeOwnerMap.checkBindings (before.bindings.map (·.owner)) interval.before before.bindings) frame
  after : SourceState
  node : RuntimePureBody.Node dependencies program block
  actionRead : RuntimeInterval.Computed (RuntimePureBody.primitiveAt interval before frame.val event) (after,node)

def readPrimitive {sources caller dependencies program}
    (event : SourceRuntimeContext.Event sources caller) (position : Position)
    (block : RuntimeInterval.Block dependencies program) (before : SourceState) :
    WorkM (Primitive event position block before) := do
  let interval ← NaturalAffine.witness (RuntimeInterval.check block position.start position.count)
  let frame ← NaturalAffine.witness
    (RuntimeOwnerMap.checkBindings (before.bindings.map (·.owner)) interval.val.before before.bindings)
  let action ← NaturalAffine.witness (RuntimePureBody.primitiveAt interval.val before frame.val.val event)
  return ⟨interval.val,by with_reducible exact interval.property,frame.val,
    by with_reducible exact frame.property,action.val.1,action.val.2,
    by with_reducible exact action.property⟩

/-- Each result retains the reader for its exact source-indexed action. A
matching interface, name or native output set cannot replace this evidence. -/
inductive Performed {artifact owner name arguments}
    (source : RuntimeBodyDiscovery.PreparedSource artifact owner name arguments)
    (root : Validity.Root) {program : Semantics.Observation.Program}
    (block : RuntimeInterval.Block root.dependencies program) (before : SourceState) :
    {pair : SourceRuntimeContext.Event artifact.sources owner × Position} →
    RuntimeNamedCallsSource.Action source pair → Type where
  | primitive {event : SourceRuntimeContext.Event artifact.sources owner} {position : Position}
      {eligible : RuntimeNamedSelectionOccurrence.primitive event = true}
      (checked : Primitive event position block before) :
      Performed source root block before
        (pair := (event,position)) (.primitive (event := event) (position := position) eligible)
  | ordinary {event position} (prepared : RuntimeNamedCallsSource.Ordinary source event position)
      (checked : RuntimeNamedOrdinaryLocal.Checked prepared root block before) :
      Performed source root block before (.ordinary prepared)
  | selection {event position context}
      (prepared : RuntimeNamedSelectionSource.Call source event position context context.references)
      (checked : RuntimeNamedSelectionLocal.CallChecked prepared root block before) :
      Performed source root block before (.selection context prepared)

def Performed.after {artifact owner name arguments source root program block before pair action}
    (checked : @Performed artifact owner name arguments source root program block before pair action) : SourceState :=
  match checked with
  | .primitive checked => checked.after
  | .ordinary _ checked => checked.boundary.after
  | .selection _ checked => checked.boundary.after

def Performed.retired {artifact owner name arguments source root program block before pair action}
    (_checked : @Performed artifact owner name arguments source root program block before pair action) :
    List Semantics.SourceOwners.Owner :=
  match pair.1 with
  | .named event => event.consumed
  | _ => []

def Performed.node {artifact owner name arguments source root program block before pair action}
    (checked : @Performed artifact owner name arguments source root program block before pair action) :
    RuntimePureBody.Node root.dependencies program block :=
  match checked with
  | .primitive checked => checked.node
  | .ordinary _ checked => checked.node
  | .selection _ checked => checked.node

/-- Common ordinary-child provider islands remain attached to the same
root. Selection prefix/arm/reference receipts remain in the selection result;
this projection does not claim to enumerate or discharge those equations. -/
def Performed.ordinaryObligations {artifact owner name arguments source root program block before pair action}
    (checked : @Performed artifact owner name arguments source root program block before pair action) :
    List (RuntimePureBody.Island root.dependencies) :=
  match checked with
  | .primitive _ => []
  | .ordinary _ checked => checked.nested.obligations
  | .selection _ _ => []

def perform {artifact owner name arguments}
    {source : RuntimeBodyDiscovery.PreparedSource artifact owner name arguments}
    (root : Validity.Root) {program : Semantics.Observation.Program}
    (block : RuntimeInterval.Block root.dependencies program) (before : SourceState)
    {pair : SourceRuntimeContext.Event artifact.sources owner × Position}
    (action : RuntimeNamedCallsSource.Action source pair) :
    WorkM (Performed source root block before action) := do
  match action with
  | .primitive (event := event) (position := position) _ =>
    return .primitive (← readPrimitive event position block before)
  | .ordinary prepared => return .ordinary prepared (← RuntimeNamedOrdinaryLocal.read prepared root block before)
  | .selection _ prepared => return .selection prepared (← RuntimeNamedSelectionLocal.readCall prepared root block before)

structure Receipt {artifact owner name arguments}
    (source : RuntimeBodyDiscovery.PreparedSource artifact owner name arguments)
    (request : RuntimeContextRequest.Context) (root : Validity.Root) {program : Semantics.Observation.Program}
    (block : RuntimeInterval.Block root.dependencies program) where
  entry : RuntimeNamedCallsSource.Entry source request
  before : SourceState
  checked : Performed source root block before entry.action

structure State {artifact owner name arguments}
    (source : RuntimeBodyDiscovery.PreparedSource artifact owner name arguments)
    (request : RuntimeContextRequest.Context) (root : Validity.Root)
    {program : Semantics.Observation.Program}
    (block : RuntimeInterval.Block root.dependencies program) where
  history : SourceState
  reverseRetired : List Semantics.SourceOwners.Owner := []
  reverseReceipts : List (@Receipt artifact owner name arguments source request root program block) := []
  cursor : Nat := 0

/-- Source offsets and contiguous literal slices are checked before invoking
any child. The only next state is the result of that exact original action. -/
def step {artifact owner name arguments}
    {source : RuntimeBodyDiscovery.PreparedSource artifact owner name arguments}
    {request : RuntimeContextRequest.Context} {root : Validity.Root}
    {program : Semantics.Observation.Program} {block : RuntimeInterval.Block root.dependencies program}
    (state : State source request root block)
    (entry : RuntimeNamedCallsSource.Entry source request) : WorkM (State source request root block) := do
  let position := entry.pair.2
  exactWork (Exact.charge 16)
  guard (position.offset == SourceRuntimeContext.Event.offset entry.pair.1 && position.start == state.cursor) .request
  let checked ← perform root block state.history entry.action
  let receipt : Receipt source request root block := ⟨entry,state.history,checked⟩
  return ⟨checked.after,checked.retired.reverse ++ state.reverseRetired,
    receipt :: state.reverseReceipts,position.start+position.count⟩

def walk {artifact owner name arguments}
    {source : RuntimeBodyDiscovery.PreparedSource artifact owner name arguments}
    {request : RuntimeContextRequest.Context} {root : Validity.Root}
    {program : Semantics.Observation.Program} {block : RuntimeInterval.Block root.dependencies program}
    (entries : List (RuntimeNamedCallsSource.Entry source request))
    (initial : State source request root block) : WorkM (State source request root block) := do
  -- Entry.pair uses the retained original list index. This reservation covers
  -- the actual repeated zip/index traversal. Retirements accumulate in reverse
  -- so a later call does not recopy the entire preceding retirement history.
  exactWork (Exact.charge (32*(entries.length+source.body.checked.events.length+request.positions.length+1)^2))
  entries.foldlM step initial

def State.retired {artifact owner name arguments source request root program block}
    (state : @State artifact owner name arguments source request root program block) :
    List Semantics.SourceOwners.Owner := state.reverseRetired.reverse

def State.nodes {artifact owner name arguments source request root program block}
    (state : @State artifact owner name arguments source request root program block) :
    List (RuntimePureBody.Node root.dependencies program block) :=
  state.reverseReceipts.reverse.map (fun receipt => receipt.checked.node)

def State.ordinaryObligations {artifact owner name arguments source request root program block}
    (state : @State artifact owner name arguments source request root program block) :
    List (RuntimePureBody.Island root.dependencies) :=
  state.reverseReceipts.reverse.flatMap (fun receipt => receipt.checked.ordinaryObligations)

structure AtRoot {artifact owner name arguments source request}
    (prepared : @RuntimeNamedCallsSource.Prepared artifact owner name arguments source request)
    (root : Validity.Root) (runtime : RuntimeFamily.Request) where
  pureSource : source.body.checked.summary.inferredEffect = .unitary
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
  result : State source request root native.block
  traversed : RuntimeInterval.Computed (walk prepared.collection.entries
    (⟨initial,[],[],0⟩ : State source request root native.block)) result
  every : result.reverseReceipts.reverse.map (fun receipt => receipt.entry.index) =
    prepared.collection.entries.map (·.index)
  exhausts : result.cursor = root.program.operations.length
  history : result.history.issued = initial.issued ++ source.body.checked.summary.allocated ∧
    result.retired = source.body.checked.summary.consumed ∧
    result.history.nextOrdinal = source.body.checked.summary.nextOrdinal
  finalInterval : RuntimeInterval.Checked native.block root.program.operations.length 0
  finalIntervalRead : RuntimeInterval.Computed
    (RuntimeInterval.check native.block root.program.operations.length 0) finalInterval
  finalBindings : Map
  finalOrder : RuntimeInterval.Computed
    (RuntimeOwnerMap.order (valueOwners source.body.checked.summary.value) result.history.bindings) finalBindings
  finalFrame : RuntimeOwnerMap.Checked (valueOwners source.body.checked.summary.value) finalInterval.after
  sameFinal : finalFrame.bindings = finalBindings
  returned : RuntimeStructuredRoot.Boundary source.body root native runtime
  returnedRead : RuntimeInterval.Computed (RuntimeStructuredRoot.readBoundary source.body root native finalBindings runtime) returned

/-- All prepared source entries run once in their original order. The native
root and dependency graph stay fixed across ordinary and selection callees.
Only the complete original returned value determines the final port order. -/
def readAt {artifact owner name arguments source request}
    (prepared : @RuntimeNamedCallsSource.Prepared artifact owner name arguments source request)
    (root : Validity.Root) (runtime : RuntimeFamily.Request) : WorkM (AtRoot prepared root runtime) := do
  let summary := source.body.checked.summary
  exactWork (Exact.charge (32*((summary.parameterValues.map SourceRuntimeValues.valueFields).sum+
    SourceRuntimeValues.valueFields summary.value+Raw.OwnerFlow.fields (summary.allocated ++ summary.consumed)+
    summary.nextOwner+summary.nextOrdinal+prepared.collection.entries.length+1)))
  if pureSource : summary.inferredEffect = .unitary then
    if quantumOnly : (summary.parameterValues.flatMap ordinary).isEmpty = true ∧
        (ordinary summary.value).isEmpty = true ∧ runtime.inputRows = [[]] ∧
        RuntimeFamily.inputValues runtime = [] ∧ RuntimeFamily.outputValues runtime = [] then
      let native ← NaturalAffine.witness (RuntimeInterval.prepare root.dependencies root.program)
      let inputs ← NaturalAffine.witness (RuntimeSourceBoundary.readInputs source.body native.val runtime.inputStorage)
      let initial : SourceState := ⟨inputs.val.owners.bindings,summary.parameterValues.flatMap valueOwners,summary.nextOwner⟩
      let result ← NaturalAffine.witness (walk prepared.collection.entries
        (⟨initial,[],[],0⟩ : State source request root native.val.block))
      if every : result.val.reverseReceipts.reverse.map (fun receipt => receipt.entry.index) =
          prepared.collection.entries.map (·.index) then
        if exhausts : result.val.cursor = root.program.operations.length then
          if history : result.val.history.issued = initial.issued ++ summary.allocated ∧
              result.val.retired = summary.consumed ∧ result.val.history.nextOrdinal = summary.nextOrdinal then
            let finalInterval ← NaturalAffine.witness (RuntimeInterval.check native.val.block root.program.operations.length 0)
            let finalBindings ← NaturalAffine.witness (RuntimeOwnerMap.order (valueOwners summary.value) result.val.history.bindings)
            let finalFrame ← RuntimeOwnerMap.checkBindings (valueOwners summary.value) finalInterval.val.after finalBindings.val
            let returned ← NaturalAffine.witness
              (RuntimeStructuredRoot.readBoundary source.body root native.val finalBindings.val runtime)
            return ⟨pureSource,quantumOnly,native.val,by with_reducible exact native.property,
              inputs.val,by with_reducible exact inputs.property,initial,rfl,result.val,
              by with_reducible exact result.property,every,exhausts,history,
              finalInterval.val,by with_reducible exact finalInterval.property,
              finalBindings.val,by with_reducible exact finalBindings.property,finalFrame.val,finalFrame.property,
              returned.val,by with_reducible exact returned.property⟩
          else throw .request
        else throw .request
      else throw .request
    else throw .request
  else throw .request

structure Checked {artifact owner name arguments source request}
    (prepared : @RuntimeNamedCallsSource.Prepared artifact owner name arguments source request)
    (order : Array Nat) (runtime : RuntimeFamily.Request) where
  root : Validity.Root
  fresh : RuntimeInterval.Computed
    (Validity.checkRootFromRoots artifact order prepared.rows prepared.roots .qmatch) root
  checked : AtRoot prepared root runtime
  consumed : RuntimeInterval.Computed (readAt prepared root runtime) checked

def read {artifact owner name arguments source request}
    (prepared : @RuntimeNamedCallsSource.Prepared artifact owner name arguments source request)
    (order : Array Nat) (runtime : RuntimeFamily.Request) : WorkM (Checked prepared order runtime) := do
  let root ← NaturalAffine.witness
    (Validity.checkRootFromRoots artifact order prepared.rows prepared.roots .qmatch)
  let checked ← NaturalAffine.witness (readAt prepared root.val runtime)
  return ⟨root.val,by with_reducible exact root.property,checked.val,by with_reducible exact checked.property⟩

end QleisliKernel.Qirf.RuntimeNamedCalls
