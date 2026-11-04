import QleisliKernel.Qirf.RuntimeBodyPlan

/-! Fixed source queries for the common native runtime traversal.
Fresh readers retain live context queues. Planned readers consume exact original
Body/Event indices, never search by a descriptor or recover missing evidence.
These queries supply no native action or acceptance; the common native handlers
must still check every interval, owner, effect, SSA map and hidden history.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeBodyQueries
open QleisliKernel Finite SourceTypes
open RuntimeBodyPlan (Queues Context Position)

inductive Mode (artifact : Artifact) where
  | fresh
  | planned (preparation : RuntimeGraphOperation.Preparation artifact)

def Mode.Cursor {artifact} : Mode artifact → Type
  | .fresh => Queues
  | .planned _ => Unit

def Mode.BodyData {artifact owner name} (mode : Mode artifact)
    (source : SourceRuntimeScope.Subject artifact.sources owner name) (request : Context) : Type :=
  match mode with
  | .fresh => Unit
  | .planned preparation => RuntimeBodyPlan.Body preparation source request

def Mode.EventData {artifact owner name} (mode : Mode artifact)
    (source : SourceRuntimeScope.Subject artifact.sources owner name)
    (event : SourceRuntimeContext.Event artifact.sources owner) (position : Position) : Type :=
  match mode with
  | .fresh => Unit
  | .planned preparation => Sigma fun before : Queues =>
      Sigma fun after : Queues => RuntimeBodyPlan.Event preparation source event position before after

def Mode.EventsData {artifact owner name} (mode : Mode artifact)
    (source : SourceRuntimeScope.Subject artifact.sources owner name)
    (pairs : List (SourceRuntimeContext.Event artifact.sources owner × Position)) : Type :=
  match mode with
  | .fresh => Unit
  | .planned preparation => Sigma fun before : Queues =>
      Sigma fun after : Queues => RuntimeBodyPlan.Events preparation source pairs before after

def Mode.ArmsData {artifact owner name offset selector target} (mode : Mode artifact)
    (table : QuantumArms.Table artifact.sources owner name offset selector target) : Type :=
  match mode with
  | .fresh => Unit
  | .planned preparation => Sigma fun before : Queues =>
      Sigma fun after : Queues => RuntimeBodyPlan.Arms preparation table (List.finRange table.arms.length) before after

def Mode.GraphData {artifact context description} (mode : Mode artifact)
    (graph : StaticOperation.CheckedGraph artifact.sources context description) (demand : StaticOperation.Paths)
    (origin : RuntimeGraphOperation.Origin graph := .unlocated) : Type :=
  match mode with
  | .fresh => Unit
  | .planned preparation => Sigma fun implementations : List RuntimeProviderHeader.Request =>
      Sigma fun references : List (List RuntimeProviderHeader.Request) =>
        RuntimeBodyPlan.Graph preparation graph demand implementations references origin

def Mode.PrefixData {artifact owner name} (mode : Mode artifact)
    (signature : SourceRuntimeContext.Signature artifact.sources owner name)
    (actuals : List (Sigma (StaticOperation.Actual artifact.sources signature.context))) : Type :=
  match mode with
  | .fresh => Unit
  | .planned preparation => Sigma fun before : Queues => Sigma fun after : Queues =>
      RuntimeBodyPlan.Prefixes preparation signature actuals before after

structure Opening {artifact : Artifact} (mode : Mode artifact) {owner name}
    (source : SourceRuntimeScope.Subject artifact.sources owner name) (request : Context) where
  actuals : List (Sigma (StaticOperation.Actual artifact.sources source.signature.context))
  prefixes : mode.PrefixData source.signature actuals
  events : mode.EventsData source (source.events.zip request.positions)
  cursor : mode.Cursor

def openBody {artifact : Artifact} (mode : Mode artifact) {owner name}
    (source : SourceRuntimeScope.Subject artifact.sources owner name) (request : Context)
    (data : mode.BodyData source request) : WorkM (Opening mode source request) := do
  match mode with
  | .fresh =>
    let actuals ← if source.prefixRequired then
      RuntimeProviderHeaders.originalActuals source.signature.operations else pure []
    return ⟨actuals,(),(),Queues.ofContext request⟩
  | .planned _ =>
    match data with
    | .mk _ _ _ actuals _ _ prefixes _ events _ => return ⟨actuals,⟨_,_,prefixes⟩,⟨_,_,events⟩,()⟩

/-- The full original formal list, including unused and zero-power actuals,
drives prefix consumption. Prepared evidence is never found by graph search. -/
def foldPrefixes {artifact : Artifact} (mode : Mode artifact) {owner name}
    (signature : SourceRuntimeContext.Signature artifact.sources owner name) {State : Type}
    (step : (actual : Sigma (StaticOperation.Actual artifact.sources signature.context)) →
      mode.GraphData actual.2.graph (RuntimeGraphOperation.required signature actual.1.1) → State → WorkM State)
    (actuals : List (Sigma (StaticOperation.Actual artifact.sources signature.context)))
    (data : mode.PrefixData signature actuals) (initial : State) : WorkM State :=
  match mode with
  | .fresh => actuals.foldlM (fun state actual => step actual () state) initial
  | .planned preparation =>
    let visit : Nat → (remaining : List (Sigma (StaticOperation.Actual artifact.sources signature.context))) →
        {before after : Queues} → RuntimeBodyPlan.Prefixes preparation signature remaining before after →
        State → WorkM State :=
      Nat.rec (fun remaining {_ _} plans state => match remaining,plans with
        | [],.nil _ => pure state
        | _ :: _,.cons _ _ _ => throw .limit)
        (fun _ next remaining {_ _} plans state => match remaining,plans with
          | [],.nil _ => pure state
          | actual :: rest,.cons cut graph tail => do
            let checked ← step actual ⟨cut.implementations,cut.references,graph⟩ state
            next rest tail checked)
    visit actuals.length actuals data.2.2 initial

/-- Every original arm is consumed at its exact table index in canonical order.
The native sector checks subsequently use that same complete indexed order. -/
def foldArms {artifact : Artifact} (mode : Mode artifact) {owner name offset selector target}
    (table : QuantumArms.Table artifact.sources owner name offset selector target) {State : Type}
    (step : (index : Fin table.arms.length) →
      mode.GraphData (table.arms[index]).operation.graph OperationAccess.controllable
        (.arm (table.arms[index]).operation) → State → WorkM State)
    (data : mode.ArmsData table) (initial : State) : WorkM State :=
  match mode with
  | .fresh => (List.finRange table.arms.length).foldlM (fun state index => step index () state) initial
  | .planned preparation =>
    let visit : Nat → (remaining : List (Fin table.arms.length)) → {before after : Queues} →
        RuntimeBodyPlan.Arms preparation table remaining before after → State → WorkM State :=
      Nat.rec (fun remaining {_ _} plans state => match remaining,plans with
        | [],.nil _ => pure state
        | _ :: _,.cons _ _ _ => throw .limit)
        (fun _ next remaining {_ _} plans state => match remaining,plans with
          | [],.nil _ => pure state
          | index :: rest,.cons cut graph tail => do
            let checked ← step index ⟨cut.implementations,cut.references,graph⟩ state
            next rest tail checked)
    visit (List.finRange table.arms.length).length (List.finRange table.arms.length) data.2.2 initial

structure Named {artifact : Artifact} (mode : Mode artifact) {owner : String}
    (event : SourceRuntimeContext.NamedEvent artifact.sources owner) where
  context : Context
  body : SourceRuntimeTrace.Body event.target.signature
  original : RuntimeInterval.Computed (SourceRuntimeTrace.readNamedBody event) body
  nested : mode.BodyData (.whole body) context
  cursor : mode.Cursor

def readNamed {artifact : Artifact} (mode : Mode artifact) {owner name}
    (source : SourceRuntimeScope.Subject artifact.sources owner name)
    (event : SourceRuntimeContext.NamedEvent artifact.sources owner) (position : Position)
    (cursor : mode.Cursor) (data : mode.EventData source (.named event) position) :
    WorkM (Named mode event) := do
  match mode with
  | .fresh =>
    let (callPosition,child) :: remaining := cursor.calls | throw .request
    guard (callPosition == position && position.offset == event.call.calleeOffset) .request
    let body ← NaturalAffine.witness (SourceRuntimeTrace.readNamedBody event)
    return ⟨child,body.val,by with_reducible exact body.property,(),{cursor with calls := remaining}⟩
  | .planned _ =>
    match data with
    | ⟨_,_,.named _ child _ _ _ _ body original nested⟩ => return ⟨child,body,original,nested,()⟩
    | ⟨_,_,.unsupported _⟩ => throw .request

structure Branch {artifact : Artifact} (mode : Mode artifact) {owner name : String}
    (event : SourceRuntimeContext.BranchEvent artifact.sources owner) where
  callerName : event.callerName = name
  left : Context
  right : Context
  source : RuntimeBranchAction.Source event
  original : RuntimeInterval.Computed (RuntimeBranchAction.readSource event) source
  thenPlan : mode.BodyData (.arm event callerName source.bodies source.original true) left
  elsePlan : mode.BodyData (.arm event callerName source.bodies source.original false) right
  cursor : mode.Cursor

def readBranch {artifact : Artifact} (mode : Mode artifact) {owner name}
    (source : SourceRuntimeScope.Subject artifact.sources owner name)
    (event : SourceRuntimeContext.BranchEvent artifact.sources owner)
    (thenEvents elseEvents : List (SourceRuntimeContext.Event artifact.sources owner)) (position : Position)
    (cursor : mode.Cursor) (data : mode.EventData source (.conditional event thenEvents elseEvents) position) :
    WorkM (Branch mode (name := name) event) := do
  match mode with
  | .fresh =>
    let (branchPosition,left,right) :: remaining := cursor.branches | throw .request
    guard (branchPosition == position && position.offset == event.written.parts.keyword.span.startByte) .request
    if sameName : event.callerName = name then
      let checked ← NaturalAffine.witness (RuntimeBranchAction.readSource event)
      return ⟨sameName,left,right,checked.val,by with_reducible exact checked.property,(),(),
        {cursor with branches := remaining}⟩
    else throw .request
  | .planned _ =>
    match data with
    | ⟨_,_,.conditional _ left right _ _ _ callerName branches original thenPlan elsePlan⟩ =>
      return ⟨callerName,left,right,branches,original,thenPlan,elsePlan,()⟩
    | ⟨_,_,.unsupported _⟩ => throw .request

structure Selection {artifact : Artifact} (mode : Mode artifact) {owner name offset selector target}
    (source : SourceRuntimeScope.Subject artifact.sources owner name)
    (naturals : PhaseApplication.Naturals artifact.sources) (scope : List String) where
  site : RuntimeContextRequest.Site
  table : QuantumArms.Table artifact.sources owner name offset selector target
  original : RuntimeInterval.Computed (QuantumArms.readArmsWithInstantiation source.signature.original
    source.signature.instantiation source.signature.supply offset selector target (some naturals) scope) table
  arms : mode.ArmsData table
  cursor : mode.Cursor

def readSelection {artifact : Artifact} (mode : Mode artifact) {owner name}
    (source : SourceRuntimeScope.Subject artifact.sources owner name)
    {tokens parsed original selector target scope naturals held remaining}
    (position : Position) (cursor : mode.Cursor)
    (data : mode.EventData source (.selection tokens parsed original selector target scope naturals held remaining) position) :
    WorkM (Selection mode (offset := parsed.keyword.span.startByte) (selector := selector.basis)
      (target := target.basis) source naturals scope) := do
  match mode with
  | .fresh =>
    let site :: rest := cursor.sites | throw .request
    guard (site.position == position && position.offset == parsed.keyword.span.startByte) .request
    let table ← NaturalAffine.witness (QuantumArms.readArmsWithInstantiation source.signature.original
      source.signature.instantiation source.signature.supply parsed.keyword.span.startByte selector.basis target.basis
      (some naturals) scope)
    return ⟨site,table.val,by with_reducible exact table.property,(),{cursor with sites := rest}⟩
  | .planned _ =>
    match data with
    | ⟨_,_,.selection site _ _ _ table original _ _ arms⟩ => return ⟨site,table,original,⟨_,_,arms⟩,()⟩
    | ⟨_,_,.unsupported _⟩ => throw .request

/-- A complete operation child has one exact reference group in planned mode.
Fresh mode retains its original complete child queues for the strict reader. -/
def Mode.OperationData {artifact owner} (mode : Mode artifact)
    (event : SourceOperationApplication.Event artifact.sources owner) (child : Context) : Type :=
  match mode with
  | .fresh => Unit
  | .planned preparation => Sigma fun references : List (List RuntimeProviderHeader.Request) =>
      PLift (child.references = [references]) ×
        RuntimeBodyPlan.Graph preparation event.operation.graph OperationAccess.applicable child.bodies references

structure Operation {artifact : Artifact} (mode : Mode artifact) {owner}
    (event : SourceOperationApplication.Event artifact.sources owner) where
  child : Context
  graph : mode.OperationData event child
  cursor : mode.Cursor

def readOperation {artifact : Artifact} (mode : Mode artifact) {owner name}
    (source : SourceRuntimeScope.Subject artifact.sources owner name)
    (event : SourceOperationApplication.Event artifact.sources owner) (position : Position)
    (cursor : mode.Cursor) (data : mode.EventData source (.operation event) position) :
    WorkM (Operation mode event) := do
  match mode with
  | .fresh =>
    let (callPosition,child) :: rest := cursor.calls | throw .request
    guard (callPosition == position && position.offset == event.call.calleeOffset && child.positions.isEmpty &&
      child.sites.isEmpty && child.calls.isEmpty && child.branches.isEmpty) .request
    return ⟨child,(),{cursor with calls := rest}⟩
  | .planned _ =>
    match data with
    | ⟨_,_,.operation _ child _ _ _ _ references groups graph⟩ =>
      return ⟨child,⟨references,⟨⟨groups⟩,graph⟩⟩,()⟩
    | ⟨_,_,.unsupported _⟩ => throw .request

structure Static {artifact : Artifact} (mode : Mode artifact) {owner name}
    (source : SourceRuntimeScope.Subject artifact.sources owner name)
    (event : SourceRuntimeContext.StaticEvent artifact.sources owner) where
  sequence : RuntimeStaticPrimitive.Continuation event
  positions : List Position
  count : positions.length = sequence.selected.result.events.length
  events : mode.EventsData source (sequence.selected.result.events.zip positions)

def readStatic {artifact : Artifact} (mode : Mode artifact) {owner name}
    (source : SourceRuntimeScope.Subject artifact.sources owner name)
    (event : SourceRuntimeContext.StaticEvent artifact.sources owner)
    (children : List (SourceRuntimeContext.Event artifact.sources owner)) (position : Position)
    (pureOnly : Bool) (cursor : mode.Cursor)
    (data : mode.EventData source (.staticConditional event children) position) :
    WorkM (Static mode source event) := do
  match mode with
  | .fresh =>
    let sequence ← match pureOnly with
      | true => do
        let selected ← RuntimeStaticPrimitive.readSequence event
        pure (RuntimeStaticPrimitive.Continuation.unchanged selected)
      | false => RuntimeStaticPrimitive.readContinuation event
    let positions ← sequence.positions position (cursor.calls.map (·.1))
    if count : positions.length = sequence.selected.result.events.length then
      return ⟨sequence,positions,count,()⟩
    else throw .request
  | .planned _ =>
    guard (!pureOnly) .request
    match data with
    | ⟨_,_,.staticConditional selected _ positions _ count events⟩ =>
      return ⟨selected,positions,count,⟨_,_,events⟩⟩
    | ⟨_,_,.unsupported _⟩ => throw .request

/-- The exact indexed event list drives planned queries. Body depth is not
spent per event, and the native step receives the same original event/position.
The Nat traversal bound is the actual full list length, never a guessed fuel. -/
def foldEvents {artifact : Artifact} (mode : Mode artifact) {owner name}
    (source : SourceRuntimeScope.Subject artifact.sources owner name) {State : Type}
    (step : (event : SourceRuntimeContext.Event artifact.sources owner) → (position : Position) →
      mode.EventData source event position → State → WorkM State)
    (pairs : List (SourceRuntimeContext.Event artifact.sources owner × Position))
    (data : mode.EventsData source pairs) (initial : State) : WorkM State :=
  match mode with
  | .fresh => pairs.foldlM (fun state (event,position) => step event position () state) initial
  | .planned preparation =>
    let visit : Nat → (remaining : List (SourceRuntimeContext.Event artifact.sources owner × Position)) →
        {before after : Queues} → RuntimeBodyPlan.Events preparation source remaining before after →
        State → WorkM State :=
      Nat.rec (fun remaining {_ _} plans state => match remaining,plans with
        | [],.nil _ => pure state
        | _ :: _,.cons _ _ => throw .limit)
        (fun _ next remaining {_ _} plans state => match remaining,plans with
          | [],.nil _ => pure state
          | (event,position) :: rest,.cons head tail => do
            let checked ← step event position ⟨_,_,head⟩ state
            next rest tail checked)
    visit pairs.length pairs data.2.2 initial

end QleisliKernel.Qirf.RuntimeBodyQueries
