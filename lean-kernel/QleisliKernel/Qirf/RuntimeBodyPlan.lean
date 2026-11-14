import QleisliKernel.Qirf.RuntimeGraphOperation
import QleisliKernel.Qirf.RuntimeStaticPrimitive
import QleisliKernel.Qirf.RuntimeTransformRequest
import QleisliKernel.Qirf.RuntimeBranchAction
import QleisliKernel.Qirf.RuntimeBasisAction
import QleisliKernel.Qirf.RuntimeCertifiedComputed
import QleisliKernel.Qirf.RuntimeWorkspace
import QleisliKernel.SourceTypes.QuantumArms

/-! Source-indexed staging data for the common runtime traversal.
Every body/event/table/graph is the actual original value with its real reader
witness. Queue indices account for all context slots before the fresh native
root; event indices retain full source order and exact position coverage.
These data grant no native action, source acceptance, handle or duty discharge.
Unsupported native forms remain unsupported, and static eligibility is unchanged.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeBodyPlan
open QleisliKernel Finite SourceTypes
abbrev Context := RuntimeContextRequest.Context
abbrev Position := SourceSequence.Position
abbrev BodyRequest := RuntimeProviderHeader.Request

structure Queues where
  calls : List (Position × Context)
  sites : List RuntimeContextRequest.Site
  branches : List (Position × Context × Context)
  bodies : List BodyRequest
  references : List (List (List BodyRequest))
  staticIntervals : List RuntimeContextRequest.StaticInterval

def Queues.ofContext (request : Context) : Queues :=
  ⟨request.calls,request.sites,request.branches,request.bodies,request.references,request.staticIntervals⟩

def Queues.isEmpty (queues : Queues) : Bool :=
  queues.calls.isEmpty && queues.sites.isEmpty && queues.branches.isEmpty &&
    queues.bodies.isEmpty && queues.references.isEmpty && queues.staticIntervals.isEmpty

/-- A compound interval belongs to its exact parent occurrence. The remaining
queue is still required to be exhausted by the original body traversal. -/
def Queues.takeStatic (queues : Queues) (parent : Position) : Option (List Position) × Queues :=
  match queues.staticIntervals with
  | (position,children) :: rest =>
    if position == parent then (some children,{queues with staticIntervals := rest}) else (none,queues)
  | [] => (none,queues)

/-- One original graph consumes its own exact provider prefix and one reference
group. Graph.providers below separately binds the provider prefix's full count. -/
structure Cut (before : Queues) where
  implementations : List BodyRequest
  references : List (List BodyRequest)
  remainingBodies : List BodyRequest
  remainingReferences : List (List (List BodyRequest))
  bodies : before.bodies = implementations ++ remainingBodies
  groups : before.references = references :: remainingReferences

def Cut.after {before} (cut : Cut before) : Queues :=
  {before with bodies := cut.remainingBodies, references := cut.remainingReferences}

structure Graph {artifact : Artifact} (preparation : RuntimeGraphOperation.Preparation artifact)
    {context description} (graph : StaticOperation.CheckedGraph artifact.sources context description)
    (demand : StaticOperation.Paths) (implementations : List BodyRequest) (references : List (List BodyRequest))
    (origin : RuntimeGraphOperation.Origin graph := .unlocated) where
  occurrences : List Nat
  ordered : RuntimeInterval.Computed (StaticOperation.readOccurrences description) occurrences
  providers : implementations.length = (RuntimeProviderHeaders.providerIndices description occurrences).length
  evidence : preparation.Evidence ⟨context,description,graph,demand,implementations,references,origin⟩
  consumed : RuntimeInterval.Computed
    (preparation.read ⟨context,description,graph,demand,implementations,references,origin⟩) evidence

inductive Prefixes {artifact : Artifact} (preparation : RuntimeGraphOperation.Preparation artifact)
    {owner name} (signature : SourceRuntimeContext.Signature artifact.sources owner name) :
    List (Sigma (StaticOperation.Actual artifact.sources signature.context)) → Queues → Queues → Type where
  | nil (queues : Queues) : Prefixes preparation signature [] queues queues
  | cons {actual : Sigma (StaticOperation.Actual artifact.sources signature.context)}
      {rest : List (Sigma (StaticOperation.Actual artifact.sources signature.context))} {before after : Queues}
      (cut : Cut before)
      (origin : RuntimeGraphOperation.Origin actual.2.graph)
      (graph : Graph preparation actual.2.graph (RuntimeGraphOperation.required signature actual.1.1)
        cut.implementations cut.references origin)
      (tail : Prefixes preparation signature rest cut.after after) :
      Prefixes preparation signature (actual :: rest) before after

inductive Arms {artifact : Artifact} (preparation : RuntimeGraphOperation.Preparation artifact)
    {owner name offset selector target}
    (table : QuantumArms.Table artifact.sources owner name offset selector target) :
    List (Fin table.arms.length) → Queues → Queues → Type where
  | nil (queues : Queues) : Arms preparation table [] queues queues
  | cons {index : Fin table.arms.length} {rest : List (Fin table.arms.length)} {before after : Queues}
      (cut : Cut before)
      (graph : Graph preparation (table.arms[index]).operation.graph OperationAccess.controllable
        cut.implementations cut.references (.arm (table.arms[index]).operation))
      (tail : Arms preparation table rest cut.after after) :
      Arms preparation table (index :: rest) before after

mutual
inductive Body {artifact : Artifact} (preparation : RuntimeGraphOperation.Preparation artifact) :
    {owner name : String} → SourceRuntimeScope.Subject artifact.sources owner name → Context → Type where
  | mk {owner name} {source : SourceRuntimeScope.Subject artifact.sources owner name} {request : Context}
      (positionsCount : request.positions.length = source.events.length)
      (offsets : request.positions.map (·.offset) = source.events.map SourceRuntimeContext.Event.offset)
      (actuals : List {actual : Sigma (StaticOperation.Actual artifact.sources source.signature.context) //
        actual ∈ source.signature.operations.actuals})
      (originalActuals : RuntimeInterval.Computed
        (if source.prefixRequired then RuntimeProviderHeaders.originalActualSlots source.signature.operations else pure []) actuals)
      (afterPrefix : Queues)
      (prefixPlans : Prefixes preparation source.signature (actuals.map Subtype.val) (Queues.ofContext request) afterPrefix)
      (afterEvents : Queues)
      (events : Events preparation source (source.events.zip request.positions) afterPrefix afterEvents)
      (exhausted : afterEvents.isEmpty = true) : Body preparation source request

inductive Event {artifact : Artifact} (preparation : RuntimeGraphOperation.Preparation artifact) :
    {owner name : String} → (source : SourceRuntimeScope.Subject artifact.sources owner name) →
    SourceRuntimeContext.Event artifact.sources owner → Position → Queues → Queues → Type where
  | primitive {owner name} {source : SourceRuntimeScope.Subject artifact.sources owner name} {position : Position} {queues : Queues}
      (event : SourceRuntimeContext.PrimitiveEvent artifact.sources owner) :
      Event preparation source (.primitive event) position queues queues
  | register {owner name} {source : SourceRuntimeScope.Subject artifact.sources owner name}
      {position : Position} {queues : Queues} (event : SourceRuntimeContext.RegisterEvent artifact.sources owner) :
      Event preparation source (.registerPrimitive event) position queues queues
  | phase {owner name} {source : SourceRuntimeScope.Subject artifact.sources owner name} {position : Position} {queues : Queues}
      (event : SourceRuntimeContext.PhaseEvent artifact.sources owner) :
      Event preparation source (.phase event) position queues queues
  | named {owner name} {source : SourceRuntimeScope.Subject artifact.sources owner name}
      {event : SourceRuntimeContext.NamedEvent artifact.sources owner} {position : Position} {before : Queues}
      (callPosition : Position) (child : Context) (remaining : List (Position × Context))
      (call : before.calls = (callPosition,child) :: remaining)
      (located : callPosition = position ∧ position.offset = event.call.calleeOffset)
      (callerName : event.target.callerName = name)
      (body : SourceRuntimeTrace.Body event.target.signature)
      (original : RuntimeInterval.Computed (SourceRuntimeTrace.readNamedBody event) body)
      (nested : Body preparation (.whole body) child) :
      Event preparation source (.named event) position before {before with calls := remaining}
  | operation {owner name} {source : SourceRuntimeScope.Subject artifact.sources owner name}
      {event : SourceOperationApplication.Event artifact.sources owner} {position : Position} {before : Queues}
      (callPosition : Position) (child : Context) (remaining : List (Position × Context))
      (call : before.calls = (callPosition,child) :: remaining)
      (located : callPosition = position ∧ position.offset = event.call.calleeOffset)
      (childEmpty : child.positions.isEmpty = true ∧ child.sites.isEmpty = true ∧
        child.calls.isEmpty = true ∧ child.branches.isEmpty = true)
      (references : List (List BodyRequest)) (groups : child.references = [references])
      (graph : Graph preparation event.operation.graph OperationAccess.applicable child.bodies references (.application event)) :
      Event preparation source (.operation event) position before {before with calls := remaining}
  | transform {owner name} {source : SourceRuntimeScope.Subject artifact.sources owner name}
      {event : SourceRuntimeContext.TransformEvent artifact.sources owner} {position : Position} {before : Queues}
      (child : Context) (remaining : List (Position × Context))
      (call : before.calls = (position,child) :: remaining)
      (request : RuntimeTransformRequest.Checked event position child)
      (original : RuntimeInterval.Computed (RuntimeTransformRequest.read event position child) request)
      (nested : Body preparation (.whole request.source) request.context) :
      Event preparation source (.transform event) position before {before with calls := remaining}
  | selection {owner name} {source : SourceRuntimeScope.Subject artifact.sources owner name}
      {tokens : List LocatedToken} {parsed : QuantumMatch.Parsed}
      {original : QuantumMatch.parse tokens = .ok (parsed,[])}
      {selector target : Semantics.SourceOwners.Owner} {scope : List String}
      {naturals : PhaseApplication.Naturals artifact.sources} {held : List Semantics.SourceOwners.Owner}
      {remaining : SourceRuntimeValues.Environment} {position : Position} {before : Queues}
      (site : RuntimeContextRequest.Site) (rest : List RuntimeContextRequest.Site)
      (selected : before.sites = site :: rest)
      (located : site.position = position ∧ position.offset = parsed.keyword.span.startByte)
      (table : QuantumArms.Table artifact.sources owner name parsed.keyword.span.startByte selector.basis target.basis)
      (originalTable : RuntimeInterval.Computed
        (QuantumArms.readArmsWithInstantiation source.signature.original source.signature.instantiation
          source.signature.supply parsed.keyword.span.startByte selector.basis target.basis (some naturals) scope) table)
      (armCount : site.arms.length = table.arms.length)
      (after : Queues)
      (arms : Arms preparation table (List.finRange table.arms.length) {before with sites := rest} after) :
      Event preparation source (.selection tokens parsed original selector target scope naturals held remaining)
        position before after
  | conditional {owner name} {source : SourceRuntimeScope.Subject artifact.sources owner name}
      {event : SourceRuntimeContext.BranchEvent artifact.sources owner} {thenEvents elseEvents : List (SourceRuntimeContext.Event artifact.sources owner)}
      {position : Position} {before : Queues}
      (branchPosition : Position) (left right : Context) (rest : List (Position × Context × Context))
      (selected : before.branches = (branchPosition,left,right) :: rest)
      (located : branchPosition = position ∧ position.offset = event.written.parts.keyword.span.startByte)
      (callerName : event.callerName = name)
      (branches : RuntimeBranchAction.Source event)
      (original : RuntimeInterval.Computed (RuntimeBranchAction.readSource event) branches)
      (thenPlan : Body preparation (.arm event callerName branches.bodies branches.original true) left)
      (elsePlan : Body preparation (.arm event callerName branches.bodies branches.original false) right) :
      Event preparation source (.conditional event thenEvents elseEvents) position before {before with branches := rest}
  | staticConditional {owner name} {source : SourceRuntimeScope.Subject artifact.sources owner name}
      {event : SourceRuntimeContext.StaticEvent artifact.sources owner} {children : List (SourceRuntimeContext.Event artifact.sources owner)}
      {position : Position} {before after : Queues}
      (selected : RuntimeStaticPrimitive.Continuation event)
      (original : RuntimeInterval.Computed (RuntimeStaticPrimitive.readContinuation event) selected)
      (positions : List Position)
      (originalPositions : RuntimeInterval.Computed
        (selected.positions position (before.calls.map (·.1)) (before.sites.map (·.position))
          (before.takeStatic position).1) positions)
      (positionsCount : positions.length = selected.selected.result.events.length)
      (events : Events preparation source (selected.selected.result.events.zip positions)
        (before.takeStatic position).2 after) :
      Event preparation source (.staticConditional event children) position before after
  | basis {owner name} {source : SourceRuntimeScope.Subject artifact.sources owner name}
      {event : SourceRuntimeContext.BasisEvent artifact.sources owner} {position : Position} {before : Queues}
      (body : RuntimeBasisAction.Source event) :
      Event preparation source (.basis event) position before before
  | computed {owner name} {source : SourceRuntimeScope.Subject artifact.sources owner name}
      {event : SourceRuntimeContext.ComputedEvent artifact.sources owner} {children : List (SourceRuntimeContext.Event artifact.sources owner)}
      {position : Position} {before : Queues}
      (protectedScope : event.written.parts.logical = none) :
      Event preparation source (.computed event children) position before before
  | certifiedComputed {owner name} {source : SourceRuntimeScope.Subject artifact.sources owner name}
      {event : SourceRuntimeContext.ComputedEvent artifact.sources owner} {children : List (SourceRuntimeContext.Event artifact.sources owner)}
      {position : Position} {before : Queues}
      (prepared : RuntimeCertifiedComputed.Prepared event) :
      Event preparation source (.computed event children) position before before
  | workspace {owner name} {source : SourceRuntimeScope.Subject artifact.sources owner name}
      {event : SourceRuntimeContext.WorkspaceEvent artifact.sources owner}
      {children : List (SourceRuntimeContext.Event artifact.sources owner)} {position : Position} {before : Queues}
      (prepared : RuntimeWorkspace.Original event children) :
      Event preparation source (.workspace event children) position before before
  | unsupported {owner name} {source : SourceRuntimeScope.Subject artifact.sources owner name}
      {event : SourceRuntimeContext.Event artifact.sources owner} {position : Position} {before : Queues}
      (unconnected : (match event with
        | .matching .. | .computed .. => true
        | _ => false) = true) : Event preparation source event position before before

inductive Events {artifact : Artifact} (preparation : RuntimeGraphOperation.Preparation artifact) :
    {owner name : String} → (source : SourceRuntimeScope.Subject artifact.sources owner name) →
    List (SourceRuntimeContext.Event artifact.sources owner × Position) → Queues → Queues → Type where
  | nil {owner name} {source : SourceRuntimeScope.Subject artifact.sources owner name} (queues : Queues) :
      Events preparation source [] queues queues
  | cons {owner name} {source : SourceRuntimeScope.Subject artifact.sources owner name}
      {event : SourceRuntimeContext.Event artifact.sources owner} {position : Position}
      {rest : List (SourceRuntimeContext.Event artifact.sources owner × Position)} {before middle after : Queues}
      (head : Event preparation source event position before middle)
      (tail : Events preparation source rest middle after) :
      Events preparation source ((event,position) :: rest) before after
end

end QleisliKernel.Qirf.RuntimeBodyPlan
