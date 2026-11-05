import QleisliKernel.Qirf.RuntimeDiscoveryData
import QleisliKernel.Qirf.RuntimeBodyPlanReaders

/-! Shared source views and typed optional recordings for discovery.
Legacy callers supply their existing metadata view without claiming a Body.
Staged views retain a genuine Subject. Only a genuine Subject can yield an
indexed body plan. These data do not change existing traversal behavior.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeBodyDiscovery
open QleisliKernel Finite SourceTypes
open RuntimeBodyPlan (Queues)

inductive Scope (artifact : Artifact) (owner name : String) where
  | supplied (signature : SourceRuntimeContext.Signature artifact.sources owner name)
      (events : List (SourceRuntimeContext.Event artifact.sources owner))
      (staticRows : List SourceRows.Row) (prefixRequired : Bool)
  | original (subject : SourceRuntimeScope.Subject artifact.sources owner name)

def Scope.signature {artifact owner name} : Scope artifact owner name → SourceRuntimeContext.Signature artifact.sources owner name
  | .supplied signature _ _ _ => signature
  | .original source => source.signature

def Scope.events {artifact owner name} : Scope artifact owner name → List (SourceRuntimeContext.Event artifact.sources owner)
  | .supplied _ events _ _ => events
  | .original source => source.events

def Scope.staticRows {artifact owner name} : Scope artifact owner name → List SourceRows.Row
  | .supplied _ _ rows _ => rows
  | .original (.whole body) => body.checked.summary.staticRows
  | .original (.arm _ _ bodies _ choice) => if choice then bodies.thenResult.staticRows else bodies.elseResult.staticRows

def Scope.prefixRequired {artifact owner name} : Scope artifact owner name → Bool
  | .supplied _ _ _ required => required
  | .original source => source.prefixRequired

def Scope.named {artifact owner name} (scope : Scope artifact owner name) {caller callee signature}
    (body : @SourceRuntimeTrace.Body artifact.sources caller callee signature) : Scope artifact caller callee :=
  match scope with
  | .supplied .. => .supplied body.checked.signature body.checked.events body.checked.summary.staticRows true
  | .original _ => .original (.whole body)

private def emptyPreparation (artifact : Artifact) : RuntimeGraphOperation.Preparation artifact where
  Evidence _ := Empty
  read _ := throw .request
  rows value := nomatch value
  roots value := nomatch value

def OperationMode.preparation {artifact} : OperationMode artifact → RuntimeGraphOperation.Preparation artifact
  | .strict => emptyPreparation artifact
  | .extended preparation => preparation

def Scope.BodyData {artifact owner name} (scope : Scope artifact owner name)
    (preparation : RuntimeGraphOperation.Preparation artifact) (request : Context) : Type :=
  match scope with
  | .supplied .. => Unit
  | .original source => Option (RuntimeBodyPlan.Body preparation source request)

def Scope.EventData {artifact owner name} (scope : Scope artifact owner name)
    (preparation : RuntimeGraphOperation.Preparation artifact)
    (event : SourceRuntimeContext.Event artifact.sources owner) (position : SourceSequence.Position)
    (before after : Queues) : Type :=
  match scope with
  | .supplied .. => Unit
  | .original source => Option (RuntimeBodyPlan.Event preparation source event position before after)

def Scope.EventsData {artifact owner name} (scope : Scope artifact owner name)
    (preparation : RuntimeGraphOperation.Preparation artifact)
    (pairs : List (SourceRuntimeContext.Event artifact.sources owner × SourceSequence.Position))
    (before after : Queues) : Type :=
  match scope with
  | .supplied .. => Unit
  | .original source => Option (RuntimeBodyPlan.Events preparation source pairs before after)

def Scope.emptyEvents {artifact owner name} (scope : Scope artifact owner name)
    (preparation : RuntimeGraphOperation.Preparation artifact) (queues : Queues) :
    scope.EventsData preparation [] queues queues :=
  match scope with
  | .supplied .. => ()
  | .original _ => some (.nil queues)

def Scope.consEvents {artifact owner name} (scope : Scope artifact owner name)
    (preparation : RuntimeGraphOperation.Preparation artifact) {event position rest before middle after}
    (head : scope.EventData preparation event position before middle)
    (tail : scope.EventsData preparation rest middle after) :
    scope.EventsData preparation ((event,position) :: rest) before after :=
  match scope with
  | .supplied .. => ()
  | .original _ => match head,tail with | some head,some tail => some (.cons head tail) | _,_ => none

structure EventResult {artifact owner name} (mode : OperationMode artifact) (scope : Scope artifact owner name)
    (event : SourceRuntimeContext.Event artifact.sources owner) (position : SourceSequence.Position) (before : Queues) where
  after : Queues
  discovery : Discovery
  receipts : List mode.Receipt
  data : scope.EventData mode.preparation event position before after

structure EventsResult {artifact owner name} (mode : OperationMode artifact) (scope : Scope artifact owner name)
    (pairs : List (SourceRuntimeContext.Event artifact.sources owner × SourceSequence.Position)) (before : Queues) where
  after : Queues
  discovery : Discovery
  receipts : List mode.Receipt
  data : scope.EventsData mode.preparation pairs before after

structure BodyResult {artifact owner name} (mode : OperationMode artifact) (scope : Scope artifact owner name)
    (request : Context) where
  discovery : Discovery
  receipts : List mode.Receipt
  data : scope.BodyData mode.preparation request

structure BranchOriginal {artifact : Artifact} {owner : String}
    (event : SourceRuntimeContext.BranchEvent artifact.sources owner) where
  bodies : SourceRuntimeTrace.BranchBodies event
  original : RuntimeInterval.Computed (SourceRuntimeTrace.readBranchSource event) bodies

structure BranchPlanned {artifact : Artifact} {owner name : String}
    (event : SourceRuntimeContext.BranchEvent artifact.sources owner) where
  callerName : event.callerName = name
  source : RuntimeBranchAction.Source event
  original : RuntimeInterval.Computed (RuntimeBranchAction.readSource event) source

def Scope.BranchData {artifact owner name} (scope : Scope artifact owner name)
    (event : SourceRuntimeContext.BranchEvent artifact.sources owner) : Type :=
  match scope with
  | .supplied .. => BranchOriginal event
  | .original _ => BranchPlanned (name := name) event

def Scope.readBranch {artifact owner name} (scope : Scope artifact owner name)
    (event : SourceRuntimeContext.BranchEvent artifact.sources owner) : WorkM (scope.BranchData event) := do
  match scope with
  | .supplied .. =>
    let bodies ← NaturalAffine.witness (SourceRuntimeTrace.readBranchSource event)
    return ⟨bodies.val,by with_reducible exact bodies.property⟩
  | .original _ =>
    if callerName : event.callerName = name then
      let source ← NaturalAffine.witness (RuntimeBranchAction.readSource event)
      return ⟨callerName,source.val,by with_reducible exact source.property⟩
    else throw .request

def Scope.branchLeft {artifact owner name} (scope : Scope artifact owner name)
    {event : SourceRuntimeContext.BranchEvent artifact.sources owner} (read : scope.BranchData event) : Scope artifact owner name :=
  match scope with
  | .supplied signature _ _ _ => .supplied signature read.bodies.thenResult.events read.bodies.thenResult.staticRows false
  | .original _ => .original (.arm event read.callerName read.source.bodies read.source.original true)

def Scope.branchRight {artifact owner name} (scope : Scope artifact owner name)
    {event : SourceRuntimeContext.BranchEvent artifact.sources owner} (read : scope.BranchData event) : Scope artifact owner name :=
  match scope with
  | .supplied signature _ _ _ => .supplied signature read.bodies.elseResult.events read.bodies.elseResult.staticRows false
  | .original _ => .original (.arm event read.callerName read.source.bodies read.source.original false)

end QleisliKernel.Qirf.RuntimeBodyDiscovery
