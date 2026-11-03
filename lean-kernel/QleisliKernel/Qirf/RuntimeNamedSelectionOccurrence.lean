import QleisliKernel.Qirf.RuntimeNamedSelectionSource

/-! One original selection call in an ordered primitive caller. Source events
are partitioned directly, retaining the actual before/after events and all
request coordinates. The original body/signature is never shortened or copied
into a synthetic function. This preparation checks no native body or root.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeNamedSelectionOccurrence
open QleisliKernel Finite SourceTypes
abbrev Context := RuntimeContextRequest.Context
abbrev Position := SourceSequence.Position

def primitive {sources owner} : SourceRuntimeContext.Event sources owner → Bool
  | .primitive event => event.kind == .h || event.kind == .globalPhaseEighth
  | .phase _ => true
  | _ => false

structure Parts {sources owner} (pairs : List (SourceRuntimeContext.Event sources owner × Position)) where
  before : List (SourceRuntimeContext.Event sources owner × Position)
  event : SourceRuntimeContext.NamedEvent sources owner
  position : Position
  after : List (SourceRuntimeContext.Event sources owner × Position)
  original : pairs = before ++ (.named event,position) :: after
  beforePrimitives : before.all (fun pair => primitive pair.1) = true
  afterPrimitives : after.all (fun pair => primitive pair.1) = true

/-- Fuel is exactly the original pair-list length plus one at the caller;
there is no new source-depth or iteration bound. -/
def readParts {sources owner} : Nat →
    (pairs : List (SourceRuntimeContext.Event sources owner × Position)) → WorkM (Parts pairs) :=
  Nat.rec (fun _ => throw .limit) (fun _ next pairs => do
    match pairs with
    | [] => throw .request
    | (.named event,position) :: after =>
      if valid : after.all (fun pair => primitive pair.1) = true then
        return ⟨[],event,position,after,rfl,rfl,valid⟩
      else throw .request
    | first :: rest =>
      if valid : primitive first.1 = true then
        let found ← next rest
        return ⟨first :: found.before,found.event,found.position,found.after,
          congrArg (List.cons first) found.original,
          by
            change (primitive first.1 && found.before.all (fun pair => primitive pair.1)) = true
            rw [valid,found.beforePrimitives]
            rfl,
          found.afterPrimitives⟩
      else throw .request)

theorem Parts.member {sources owner pairs} (parts : @Parts sources owner pairs) :
    (.named parts.event,parts.position) ∈ pairs := by
  apply Eq.mpr (congrArg (fun items => (.named parts.event,parts.position) ∈ items) parts.original)
  exact List.mem_append_right _ (List.Mem.head _)

private def primitiveRows {sources owner} : SourceRuntimeContext.Event sources owner → List SourceRows.Row
  | .primitive event => CallName.sourceRows event.candidate
  | .phase event => CallName.sourceRows event.application.candidate ++ event.naturals.sourceRows
  | _ => []

structure Prepared {artifact owner name arguments}
    (source : RuntimeBodyDiscovery.PreparedSource artifact owner name arguments) (request : Context) where
  noRootActuals : source.signature.arguments.operations.isEmpty = true ∧
    source.signature.operations.actuals.isEmpty = true ∧ source.signature.operations.hasMeaningRequirements = false
  offsets : request.positions.map (·.offset) = source.body.checked.events.map SourceRuntimeContext.Event.offset
  parts : Parts (source.body.checked.events.zip request.positions)
  partitioned : RuntimeInterval.Computed
    (readParts (source.body.checked.events.length+1) (source.body.checked.events.zip request.positions)) parts
  child : Context
  calls : request.calls = [(parts.position,child)]
  outerEmpty : request.sites.isEmpty = true ∧ request.branches.isEmpty = true ∧
    request.bodies.isEmpty = true ∧ request.references.isEmpty = true
  call : RuntimeNamedSelectionSource.Call source parts.event parts.position child child.references
  callRead : RuntimeInterval.Computed (RuntimeNamedSelectionSource.prepareCall source parts.event
    (List.of_mem_zip parts.member).1 parts.position child child.references) call
  relevance : SourceRows.Retained (call.rows ++
    (parts.before ++ parts.after).flatMap (fun pair => primitiveRows pair.1))

def Prepared.rows {artifact owner name arguments source request}
    (prepared : @Prepared artifact owner name arguments source request) : List SourceRows.Row := prepared.relevance.rows

def Prepared.roots {artifact owner name arguments source request}
    (prepared : @Prepared artifact owner name arguments source request) : List Nat :=
  (artifact.root :: prepared.call.roots).eraseDups

def prepare {artifact owner name arguments}
    (source : RuntimeBodyDiscovery.PreparedSource artifact owner name arguments) (request : Context) :
    WorkM (Prepared source request) := do
  exactWork (Exact.charge (64*(source.body.checked.events.length+request.positions.length+request.calls.length+
    request.sites.length+request.branches.length+request.bodies.length+request.references.length+1)))
  if noRootActuals : source.signature.arguments.operations.isEmpty = true ∧
      source.signature.operations.actuals.isEmpty = true ∧ source.signature.operations.hasMeaningRequirements = false then
    if offsets : request.positions.map (·.offset) = source.body.checked.events.map SourceRuntimeContext.Event.offset then
      let parts ← NaturalAffine.witness
        (readParts (source.body.checked.events.length+1) (source.body.checked.events.zip request.positions))
      match calls : request.calls with
      | [(position,child)] =>
        if valid : position = parts.val.position ∧ request.sites.isEmpty = true ∧ request.branches.isEmpty = true ∧
            request.bodies.isEmpty = true ∧ request.references.isEmpty = true then
          let call ← NaturalAffine.witness (RuntimeNamedSelectionSource.prepareCall source parts.val.event
            (List.of_mem_zip parts.val.member).1 parts.val.position child child.references)
          let relevance ← SourceRows.read (call.val.rows ++
            (parts.val.before ++ parts.val.after).flatMap (fun pair => primitiveRows pair.1))
          return ⟨noRootActuals,offsets,parts.val,by with_reducible exact parts.property,child,
            by simpa only [valid.1] using calls,valid.2,call.val,by with_reducible exact call.property,relevance⟩
        else throw .request
      | _ => throw .request
    else throw .request
  else throw .request

end QleisliKernel.Qirf.RuntimeNamedSelectionOccurrence
