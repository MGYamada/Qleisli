import QleisliKernel.Qirf.ContextSector
import QleisliKernel.Qirf.SourceContextRequest
import QleisliKernel.Qirf.SourceArmBody

/-! Discover original arm bodies and their dependencies before checking a graph.
Each occurrence reuses its exact selected signature. No evidence-index cache
can conflate two original instantiations or skip a statically unused arm.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.SourceBodyHeader
open QleisliKernel QleisliKernel.SourceTypes QleisliKernel.Qirf Finite
open QleisliKernel.Qirf.PureInterval (Witness)
abbrev Context := SourceContextRequest.Context

structure Header {artifact : Artifact} {owner name} (source : SourceTrace.Checked artifact.sources owner name)
    (request : Context) where
  sites : List (SelectionCore.Header artifact source.signature)
  everyEvent : sites.map (·.event) = source.result.events.filterMap ContextSector.selection
  everyRequest : sites.map (·.request) = request.sites

def read {artifact : Artifact} {owner name} (source : SourceTrace.Checked artifact.sources owner name)
    (request : Context) : WorkM (Header source request) := do
  guard (source.result.events.all fun event => match event with | .operation _ => false | _ => true) .request
  guard (request.sites.length ≤ 128) .limit
  let events := source.result.events.filterMap ContextSector.selectionData
  exactWork (Exact.charge (64*(request.sites.length+events.length+1)^2+
    64*(events.map fun event => SourceSequence.eventFields event.1).sum))
  guard (events.length == request.sites.length) .request
  let sites ← (events.zip request.sites).mapM fun (event,request) =>
    SelectionCore.readHeader artifact source.signature (event.1,request) event.2.1 event.2.2
  if everyEvent : sites.map (·.event) = source.result.events.filterMap ContextSector.selection then
    if everyRequest : sites.map (·.request) = request.sites then
      return ⟨sites,everyEvent,everyRequest⟩
    else throw .request
  else throw .request

structure Subject (artifact : Artifact) where
  owner : String
  selector : Semantics.FiniteCarrier.Basis
  target : Semantics.FiniteCarrier.Basis
  bound : SourceArm.Bound artifact owner selector target

def bindings {artifact owner name source request} (header : @Header artifact owner name source request) :
    List (Subject artifact) :=
  header.sites.flatMap fun site => site.bindings.val.map fun bound =>
    ⟨owner,site.ports.selectorIn.basis,site.ports.targetIn.basis,bound⟩

def rows {artifact owner name source request} (header : @Header artifact owner name source request) :
    List (String × String) :=
  source.sourceRows ++ source.result.events.flatMap ContextSector.eventRows ++
    header.sites.flatMap fun site =>
      Carrier.sourceRows site.request.attached site.request.required ++ site.rows.val

def roots {artifact owner name source request} (header : @Header artifact owner name source request) : List Nat :=
  header.sites.flatMap (·.roots.val)

structure Arm (artifact : Artifact) where
  owner : String
  selector : Semantics.FiniteCarrier.Basis
  target : Semantics.FiniteCarrier.Basis
  bound : SourceArm.Bound artifact owner selector target
  request : Context
  source : Witness (SourceTrace.readWithSignature bound.signature)
  header : Header source.val.checked request

def readArm (artifact : Artifact) {owner selector target}
    (bound : SourceArm.Bound artifact owner selector target) (request : Context) : WorkM (Arm artifact) := do
  let source ← NaturalAffine.witness (SourceTrace.readWithSignature bound.signature)
  let header ← read source.val.checked request
  return ⟨owner,selector,target,bound,request,source,header⟩

structure Call (artifact : Artifact) where
  caller : String
  event : SourceCalls.Event artifact.sources caller
  position : SourceSequence.Position
  request : Context
  source : Witness (SourceTrace.readNamedSource event)
  header : Header source.val.checked request

def named {sources owner} : SourceTrace.Event sources owner → Option (SourceCalls.Event sources owner)
  | .named event => some event
  | _ => none

def readCall (artifact : Artifact) {caller} (event : SourceCalls.Event artifact.sources caller)
    (request : SourceSequence.Position × Context) : WorkM (Call artifact) := do
  guard (request.1.offset == event.call.calleeOffset) .request
  let source ← NaturalAffine.witness (SourceTrace.readNamedSource event)
  let header ← read source.val.checked request.2
  return ⟨caller,event,request.1,request.2,source,header⟩

structure Discovery (artifact : Artifact) where
  arms : List (Arm artifact)
  calls : List (Call artifact)

/-- Calls and arms are discovered together, before any dependency snapshot is
accepted. Each child is derived from its parent original occurrence. -/
def discover (artifact : Artifact) : Nat → {owner name : String} →
    {source : SourceTrace.Checked artifact.sources owner name} → {request : Context} →
    Header source request → WorkM (Discovery artifact) :=
  Nat.rec (fun {_ _} {source} {request} header => do
    guard (request.bodies.isEmpty && request.calls.isEmpty && (bindings header).isEmpty &&
      (source.result.events.filterMap named).isEmpty) .limit
    return ⟨[],[]⟩) (fun _ next {_ _} {source} {request} header => do
    let subjects := bindings header
    let events := source.result.events.filterMap named
    exactWork (Exact.charge (16*(subjects.length+events.length+request.bodies.length+request.calls.length+1)))
    guard (subjects.length == request.bodies.length && events.length == request.calls.length) .request
    let arms ← (subjects.zip request.bodies).mapM fun (subject,body) => readArm artifact subject.bound body
    let calls ← (events.zip request.calls).mapM fun (event,body) => readCall artifact event body
    let armDescendants ← arms.mapM fun arm => next arm.header
    let callDescendants ← calls.mapM fun call => next call.header
    return ⟨arms ++ armDescendants.flatMap (·.arms) ++ callDescendants.flatMap (·.arms),
      calls ++ armDescendants.flatMap (·.calls) ++ callDescendants.flatMap (·.calls)⟩)

/-- A request has one child for every immediate arm occurrence in source order.
The recursion consumes the bounded request depth; repeated evidence indices
still take this complete path with their own original signature and actuals. -/
def descendants (artifact : Artifact) : Nat → {owner name : String} →
    {source : SourceTrace.Checked artifact.sources owner name} → {request : Context} →
    Header source request → WorkM (List (Arm artifact)) :=
  Nat.rec (fun {_ _} {_} {request} header => do
    guard request.bodies.isEmpty .limit
    guard (bindings header).isEmpty .limit
    return []) (fun _ next {_ _} {_} {request} header => do
    let subjects := bindings header
    exactWork (Exact.charge (8*(subjects.length+request.bodies.length+1)))
    guard (subjects.length == request.bodies.length) .request
    let children ← (subjects.zip request.bodies).mapM fun (subject,body) => readArm artifact subject.bound body
    let rest ← children.mapM fun child => next child.header
    return children ++ rest.flatten)

end QleisliKernel.Qirf.SourceBodyHeader
