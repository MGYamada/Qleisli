import QleisliKernel.Qirf.RuntimeNamedSelectionSource
import QleisliKernel.Qirf.RuntimeNamedSelectionOccurrence
import QleisliKernel.Qirf.RuntimeReferenceContexts

/-! Original ordered call preparation. Every source event keeps its actual
position/index; every named event consumes its own context and genuine callee
read. Selection bodies use the existing complete prefix/arm preparation;
ordinary bodies retain the common discovery result. Neither branch is body
acceptance, and no shape/label alone grants an execution equation.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeNamedCallsSource
open QleisliKernel Finite SourceTypes
abbrev Context := RuntimeContextRequest.Context
abbrev Position := SourceSequence.Position

structure Ordinary {artifact owner name arguments}
    (source : RuntimeBodyDiscovery.PreparedSource artifact owner name arguments)
    (event : SourceRuntimeContext.NamedEvent artifact.sources owner) (position : Position) where
  member : (.named event : SourceRuntimeContext.Event artifact.sources owner) ∈ source.body.checked.events
  callerName : event.target.callerName = name
  offset : position.offset = event.call.calleeOffset
  visibleUnitary : event.effect = .unitary
  context : Context
  referenceFree : context.references.isEmpty = true
  body : SourceRuntimeTrace.Body event.target.signature
  bodyRead : RuntimeInterval.Computed (SourceRuntimeTrace.readNamedBody event) body
  noOperationActuals : body.checked.signature.arguments.operations.isEmpty = true ∧
    body.checked.signature.operations.actuals.isEmpty = true ∧ body.checked.signature.operations.hasMeaningRequirements = false
  discovered : RuntimeBodyDiscovery.Discovery
  discoveryRead : RuntimeInterval.Computed (RuntimeBodyDiscovery.visit artifact 128 body.checked.signature
    body.checked.events body.checked.summary.staticRows context true) discovered

def Ordinary.rows {artifact owner name arguments source event position}
    (ordinary : @Ordinary artifact owner name arguments source event position) : List SourceRows.Row :=
  event.target.sourceRows ++ ordinary.body.checked.signature.sourceRows ++ ordinary.body.checked.summary.staticRows ++
    ordinary.discovered.rows

inductive Action {artifact owner name arguments}
    (source : RuntimeBodyDiscovery.PreparedSource artifact owner name arguments) :
    (SourceRuntimeContext.Event artifact.sources owner × Position) → Type where
  | primitive {event position} (eligible : RuntimeNamedSelectionOccurrence.primitive event = true) :
      Action source (event,position)
  | ordinary {event position} (prepared : Ordinary source event position) : Action source (.named event,position)
  | selection {event position} (context : Context)
      (prepared : RuntimeNamedSelectionSource.Call source event position context context.references) :
      Action source (.named event,position)

def Action.rows {artifact owner name arguments source pair}
    (action : @Action artifact owner name arguments source pair) : List SourceRows.Row :=
  match action with
  | .primitive (event := .primitive event) _ => CallName.sourceRows event.candidate
  | .primitive (event := .phase event) _ => CallName.sourceRows event.application.candidate ++ event.naturals.sourceRows
  | .primitive _ => []
  | .ordinary prepared => prepared.rows
  | .selection _ prepared => prepared.rows

def Action.roots {artifact owner name arguments source pair}
    (action : @Action artifact owner name arguments source pair) : List Nat :=
  match action with
  | .primitive _ => []
  | .ordinary prepared => prepared.discovered.roots
  | .selection _ prepared => prepared.roots

private def prepareAction {artifact owner name arguments}
    (source : RuntimeBodyDiscovery.PreparedSource artifact owner name arguments) (request : Context)
    (pair : SourceRuntimeContext.Event artifact.sources owner × Position)
    (member : pair ∈ source.body.checked.events.zip request.positions)
    (calls : List (Position × Context)) : WorkM (Action source pair × List (Position × Context)) := do
  match pair with
  | (.named event,position) =>
    let (callPosition,child) :: rest := calls | throw .request
    exactWork (Exact.charge (32*(name.utf8ByteSize+event.target.callerName.utf8ByteSize+1)))
    if located : callPosition = position ∧ event.target.callerName = name ∧
        position.offset = event.call.calleeOffset ∧ event.effect = .unitary then
      let body ← NaturalAffine.witness (SourceRuntimeTrace.readNamedBody event)
      match body.val.checked.events with
      | [.selection ..] =>
        let prepared ← RuntimeNamedSelectionSource.prepareCallWithBody source event (List.of_mem_zip member).1
          position child child.references body.val (by with_reducible exact body.property)
        return (.selection child prepared,rest)
      | _ =>
        if noActuals : body.val.checked.signature.arguments.operations.isEmpty = true ∧
            body.val.checked.signature.operations.actuals.isEmpty = true ∧
            body.val.checked.signature.operations.hasMeaningRequirements = false then
          if referenceFree : child.references.isEmpty = true then
            let discovered ← NaturalAffine.witness (RuntimeBodyDiscovery.visit artifact 128 body.val.checked.signature
              body.val.checked.events body.val.checked.summary.staticRows child true)
            let prepared : Ordinary source event position :=
              ⟨(List.of_mem_zip member).1,located.2.1,located.2.2.1,located.2.2.2,child,referenceFree,
                body.val,by with_reducible exact body.property,noActuals,discovered.val,
                by with_reducible exact discovered.property⟩
            return (.ordinary prepared,rest)
          else throw .request
        else throw .request
    else throw .request
  | (event,_position) =>
    if eligible : RuntimeNamedSelectionOccurrence.primitive event = true then return (.primitive eligible,calls)
    else throw .request

structure Entry {artifact owner name arguments}
    (source : RuntimeBodyDiscovery.PreparedSource artifact owner name arguments) (request : Context) where
  index : Fin (source.body.checked.events.zip request.positions).length
  action : Action source ((source.body.checked.events.zip request.positions)[index.val]'index.isLt)

def Entry.pair {artifact owner name arguments source request}
    (entry : @Entry artifact owner name arguments source request) :=
  (source.body.checked.events.zip request.positions)[entry.index.val]'entry.index.isLt

structure Collection {artifact owner name arguments source request} where
  entries : List (@Entry artifact owner name arguments source request)
  remaining : List (Position × Context)

private def collect {artifact owner name arguments}
    (source : RuntimeBodyDiscovery.PreparedSource artifact owner name arguments) (request : Context) :
    WorkM (@Collection artifact owner name arguments source request) := do
  let pairs := source.body.checked.events.zip request.positions
  -- Each checked index below performs a real List lookup. Reserve its full
  -- quadratic construction cost, including standalone uses of this reader.
  exactWork (Exact.charge (64*(pairs.length+request.calls.length+1)^2))
  let (entries,remaining) ← (List.finRange pairs.length).foldlM (fun (entries,calls) index => do
    let pair := pairs[index.val]'index.isLt
    let (action,rest) ← prepareAction source request pair (List.getElem_mem index.isLt) calls
    let entry : Entry source request := ⟨index,action⟩
    return (entry :: entries,rest)) ([],request.calls)
  return ⟨entries.reverse,remaining⟩

structure Prepared {artifact owner name arguments}
    (source : RuntimeBodyDiscovery.PreparedSource artifact owner name arguments) (request : Context) where
  noRootActuals : source.signature.arguments.operations.isEmpty = true ∧
    source.signature.operations.actuals.isEmpty = true ∧ source.signature.operations.hasMeaningRequirements = false
  offsets : request.positions.map (·.offset) = source.body.checked.events.map SourceRuntimeContext.Event.offset
  outerEmpty : request.sites.isEmpty = true ∧ request.branches.isEmpty = true ∧
    request.bodies.isEmpty = true ∧ request.references.isEmpty = true
  referenceContexts : RuntimeInterval.Computed (RuntimeReferenceContexts.ordered request) ()
  collection : @Collection artifact owner name arguments source request
  collected : RuntimeInterval.Computed (collect source request) collection
  every : collection.entries.map (·.index) = List.finRange (source.body.checked.events.zip request.positions).length
  exhausted : collection.remaining = []
  relevance : SourceRows.Retained ([(owner,source.signature.original.source)] ++ source.signature.sourceRows ++
    source.body.checked.summary.staticRows ++ collection.entries.flatMap (fun entry => entry.action.rows))

def Prepared.rows {artifact owner name arguments source request}
    (prepared : @Prepared artifact owner name arguments source request) : List SourceRows.Row := prepared.relevance.rows

def Prepared.roots {artifact owner name arguments source request}
    (prepared : @Prepared artifact owner name arguments source request) : List Nat :=
  (artifact.root :: prepared.collection.entries.flatMap (fun entry => entry.action.roots)).eraseDups

def prepare {artifact owner name arguments}
    (source : RuntimeBodyDiscovery.PreparedSource artifact owner name arguments) (request : Context) :
    WorkM (Prepared source request) := do
  exactWork (Exact.charge (64*(source.body.checked.events.length+request.positions.length+request.calls.length+
    request.sites.length+request.branches.length+request.bodies.length+request.references.length+1)))
  if noRootActuals : source.signature.arguments.operations.isEmpty = true ∧
      source.signature.operations.actuals.isEmpty = true ∧ source.signature.operations.hasMeaningRequirements = false then
    if offsets : request.positions.map (·.offset) = source.body.checked.events.map SourceRuntimeContext.Event.offset then
      if outerEmpty : request.sites.isEmpty = true ∧ request.branches.isEmpty = true ∧
          request.bodies.isEmpty = true ∧ request.references.isEmpty = true then
        let references ← NaturalAffine.witness (RuntimeReferenceContexts.ordered request)
        have unit : references.val = () := by cases references.val; rfl
        let collected ← NaturalAffine.witness (collect source request)
        if every : collected.val.entries.map (·.index) = List.finRange (source.body.checked.events.zip request.positions).length then
          if exhausted : collected.val.remaining = [] then
            let relevance ← SourceRows.read ([(owner,source.signature.original.source)] ++ source.signature.sourceRows ++
              source.body.checked.summary.staticRows ++ collected.val.entries.flatMap (fun entry => entry.action.rows))
            return ⟨noRootActuals,offsets,outerEmpty,
              by with_reducible simpa only [unit] using references.property,
              collected.val,by with_reducible exact collected.property,
              every,exhausted,relevance⟩
          else throw .request
        else throw .request
      else throw .request
    else throw .request
  else throw .request

end QleisliKernel.Qirf.RuntimeNamedCallsSource
