import QleisliKernel.Qirf.RuntimeInheritedActual

/-! Bind a nested original Meaning and every provider child at the actual requested node. The caller and the enclosing written arm have separate credits.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeNestedDuty
open QleisliKernel Finite SourceTypes
open RuntimeInterval (Computed)
open RuntimeNativeSubject (Cursor)

open RuntimeClosedProvider (Tree)
open GenericDutyQueue
open RuntimeClosedSubject (Paired)

private def requestedDetails {artifact catalogue context description graph implementations references prepared root requested}
    {subject : GenericOperationSubstitute.Subject artifact.sources} {closed : GenericOperation.Closed subject.description}
    {checked : @RuntimeOperationTree.Checked artifact catalogue context description graph implementations references prepared root requested}
    {index cursor terminal need ok} (tree : Tree subject closed checked index cursor terminal need ok) :
    Option (Nat × Nat × String × String × Bool) :=
  match tree with
  | .node (cursor := current) (nested := children) _ _ _ source _ _ _ _ _ _ =>
    match source with
    | .requested _ owner name => some (index,current.binding.index.val,owner,name,children)
    | _ => none
  | .formal .. => none

/-- A single actual formal wrapper has exactly one requested node with a
fully bound ordered provider forest. A false descendant cannot be hidden by
an adequate local equation at its parent. -/
private def pendingBelowFormal {artifact catalogue context description graph implementations references prepared root requested}
    {subject : GenericOperationSubstitute.Subject artifact.sources} {closed : GenericOperation.Closed subject.description}
    {checked : @RuntimeOperationTree.Checked artifact catalogue context description graph implementations references prepared root requested}
    {index cursor terminal need ok} (tree : Tree subject closed checked index cursor terminal need ok) :
    Option (Nat × Nat × String × String × Bool) :=
  match tree with
  | .formal _ _ child => requestedDetails child
  | .node .. => none

section
variable {artifact catalogue context description graph implementations references prepared root requested checked}
    (pending : @SourcePendingMeaning.Prepared artifact.sources catalogue)
    {outerRecord outerInvocation} (outer : @GenericDutyQueue.Demand artifact.sources catalogue outerRecord outerInvocation)
    {closed : GenericOperation.Closed outer.transported.subject.description} {outerIndex outerCursor terminal outerPaired}
    (tree : @RuntimeClosedProvider.Checked artifact catalogue context description graph implementations references prepared
      root requested checked outerIndex outerCursor terminal outer.transported.subject closed outerPaired ⟨false,false,false⟩)
    {rootOwner rootName caller callerName scope}
    {innerMarker : SourceOperation.Marker artifact.sources caller scope}
    {cursor : Cursor checked} {parent : RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName caller callerName}
    {id : InstanceId} (inner : Inner innerMarker cursor pending parent id)

structure MissingOnly where
  sourceIndex : Nat
  actualRecord : Nat
  missing : pendingBelowFormal tree.tree = some (sourceIndex,actualRecord,
    innerMarker.selected.resolution.moduleName,innerMarker.selected.resolution.declaration.name,true)
  selectedOriginal : sourceIndex = outer.transported.subject.description.root
  selectedNative : actualRecord = cursor.binding.index.val
  actualTarget : terminal.binding.index.val = cursor.binding.index.val
  supplier : SourceDutySlots.Supplier outer.transported.subject sourceIndex
  tokens : supplier.origin.tokens = innerMarker.tokens
  owner : supplier.origin.state.owner = inner.route.val.invoked.val.demand.source.original.origin.state.owner ∧
    supplier.origin.state.name = inner.route.val.invoked.val.demand.source.original.origin.state.name
  body : supplier.origin.state.prepared.original.envelope.source = inner.route.val.invoked.val.demand.source.original.origin.state.prepared.original.envelope.source ∧
    supplier.origin.state.prepared.original.envelope.declaration = inner.route.val.invoked.val.demand.source.original.origin.state.prepared.original.envelope.declaration ∧
    supplier.origin.state.prepared.original.envelope.occurrence = inner.route.val.invoked.val.demand.source.original.origin.state.prepared.original.envelope.occurrence
  scope : ∀ name,name ∈ supplier.origin.scope ↔ name ∈ scope

def readMissingOnly : WorkM (MissingOnly pending outer tree inner) := do
  let subject := outer.transported.subject
  let original := inner.route.val.invoked.val.demand.source.original.origin
  match missing : pendingBelowFormal tree.tree with
  | some (i,record,owner,name,true) =>
    exactWork (Exact.charge (16*(subject.suppliers.length+owner.utf8ByteSize+name.utf8ByteSize+
      innerMarker.selected.resolution.moduleName.utf8ByteSize+innerMarker.selected.resolution.declaration.name.utf8ByteSize+1)))
    if found : i = subject.description.root ∧ record = cursor.binding.index.val ∧
        terminal.binding.index.val = cursor.binding.index.val ∧ owner = innerMarker.selected.resolution.moduleName ∧
        name = innerMarker.selected.resolution.declaration.name then
      match rows : subject.suppliers.filter (·.1 == i) with
      | [(j,origin)] =>
        let bytes := originalFields origin.state.prepared.original.envelope+
          originalFields original.state.prepared.original.envelope+SourceTrace.Meter.tokenFields origin.tokens+
          SourceTrace.Meter.tokenFields innerMarker.tokens
        let names := (SourceTrace.Meter.nameFields origin.scope + SourceTrace.Meter.nameFields scope+1)*
          (origin.scope.length+scope.length+1)
        exactWork (Exact.charge (32*(bytes+names+1)))
        if jAt : j = i then
          let supplier : SourceDutySlots.Supplier subject i := ⟨origin,by simpa only [jAt] using rows⟩
          if same : origin.tokens = innerMarker.tokens ∧ origin.state.owner = original.state.owner ∧
              origin.state.name = original.state.name ∧ origin.state.prepared.original.envelope.source =
              original.state.prepared.original.envelope.source ∧ origin.state.prepared.original.envelope.declaration =
              original.state.prepared.original.envelope.declaration ∧ origin.state.prepared.original.envelope.occurrence =
              original.state.prepared.original.envelope.occurrence ∧ RuntimeDutyInvocation.sameScope origin.scope scope = true then
            let ⟨tokens,own,callee,source,decl,body,visible⟩ := same
            return ⟨i,record,by simpa only [found.2.2.2.1,found.2.2.2.2] using missing,
              found.1,found.2.1,found.2.2.1,supplier,tokens,⟨own,callee⟩,⟨source,decl,body⟩,
              RuntimeDutyInvocation.sameScope_members visible⟩
          else throw .request
        else throw .request
      | _ => throw .request
    else throw .request
  | _ => throw .request
end

structure Offer {artifact catalogue context description graph implementations references prepared root requested}
    (pending : @SourcePendingMeaning.Prepared artifact.sources catalogue)
    (checked : @RuntimeOperationTree.Checked artifact catalogue context description graph implementations references prepared root requested) where
  caller : String
  scope : List String
  marker : SourceOperation.Marker artifact.sources caller scope
  cursor : Cursor checked
  rootOwner : String
  rootName : String
  callerName : String
  path : RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName caller callerName
  id : InstanceId
  inner : Inner marker cursor pending path id
  call : GenericOperation.ApplicationSource artifact.sources
  formal : StaticHeaders.Formal
  argument : List LocatedToken
  inherited : Inherited catalogue call formal argument inner.route.val.invoked.val.demand.source.original marker.tokens

private def discover {artifact catalogue context description graph implementations references prepared root requested checked
    rootOwner rootName owner name path record invocation original result native index cursor terminal}
    (pending : @SourcePendingMeaning.Prepared artifact.sources catalogue)
    {binding : @RuntimeDutyInvocation.Binding artifact.sources catalogue pending.queue rootOwner rootName owner name path record invocation}
    {transport : GenericDutyQueue.Transport invocation.applications.reverse original result}
    {paired : @Paired artifact catalogue context description graph implementations references prepared root requested
      checked native index cursor terminal} (chain : RuntimeForwardedSupply.Chain binding transport paired) :
    WorkM (Offer pending checked) :=
  match chain with
  | .direct .. => throw .request
  | .formal (caller := caller) (event := event) (parent := parent) (invocation := priorInvocation) (app := call) (prior := prior) hop _ _ => do
    let offered ← readSupplied hop pending prior
    return ⟨caller,event.scope,offered.marker,hop.wrapper.selected.child.cursor,_,_,
      event.target.callerName,parent,priorInvocation.id,offered.inner,
      call.original,hop.supply.source.actual.formal,hop.supply.source.actual.argument.tokens,offered.inherited.val⟩

private def originalFormal (description : GenericOperation.Description) : Bool :=
  description.root == 0 && match description.nodes with | [.formal _] => true | _ => false

/-- Constant-spine preflight on the already indexed queue item. Only the
original call and checked native tree can establish either source credit. -/
def possible {sources catalogue queue} (entry : @SourcePendingMeaning.Entry sources catalogue queue) : Bool :=
  match entry.subject with
  | .demand _ demand => originalFormal demand.source.original.subject && requestedBare demand.transported.subject.description
  | _ => false

section
variable {artifact catalogue owner tokens implementations references operation prepared root requested checked
    rootOwner rootName name path}
    (pending : @SourcePendingMeaning.Prepared artifact.sources catalogue)
    (position : Fin pending.entries.length)
    {source : @RuntimeSourceOperationMarkers.Checked artifact catalogue owner tokens implementations references operation
      prepared root requested checked} {index : Nat}
    {invoked : @RuntimeDutyInvocation.DemandBinding artifact.sources catalogue pending.queue rootOwner rootName owner
      name pending.entries[position] path}
    {closed : GenericOperation.Closed invoked.demand.transported.subject.description}
    (link : RuntimeLinkedSubject.ClosedAt source index invoked closed)

private def ready {sources n} (inner outer : Fin n) (d : GenericOperation.Duty sources) (needed : Bool) : Prop :=
  inner ≠ outer ∧ d.kind = .checkedMeaning ∧ originalFormal d.subject = true ∧ d.bindings.isEmpty = true ∧
    d.runtimeApplication.isNone = true ∧ needed = true

private def readReady {sources n} (inner outer : Fin n) (d : GenericOperation.Duty sources) (needed : Bool) :
    WorkM (PLift (ready inner outer d needed)) :=
  if h : inner ≠ outer ∧ d.kind = .checkedMeaning ∧ originalFormal d.subject = true ∧
      d.bindings.isEmpty = true ∧ d.runtimeApplication.isNone = true ∧ needed = true then pure ⟨h⟩
  else throw Finite.Error.request

structure Pair where
  offer : ResultOf (discover pending link.suppliers)
  matched : ResultOf (readMissingOnly pending invoked.demand link.providers offer.val.inner)
  eligible : ready offer.val.inner.route.val.index.val position invoked.demand.source.original pending.entries[position].unconsumed

-- Keep each dependency at its declared type. The constructor never needs
-- to normalize the source queue or the original native run to compare them.
private def checkOuter (offer : ResultOf (discover pending link.suppliers)) :
    WorkM (PLift (ready offer.val.inner.route.val.index.val position invoked.demand.source.original
      pending.entries[position].unconsumed)) :=
  @readReady artifact.sources pending.entries.length offer.val.inner.route.val.index.val position
    invoked.demand.source.original pending.entries[position].unconsumed

private def attach (offer : ResultOf (discover pending link.suppliers)) :
    WorkM (ResultOf (readMissingOnly pending invoked.demand link.providers offer.val.inner)) :=
  NaturalAffine.witness (readMissingOnly pending invoked.demand link.providers offer.val.inner)

private def finishPair (offer : ResultOf (discover pending link.suppliers)) : WorkM (Pair pending position link) := do
  let matched ← attach pending position link offer
  let ready ← checkOuter pending position link offer
  return {offer := offer,matched := matched,eligible := ready.down}

inductive Role (n : Nat) where
  | supplying (position : Fin n)
  | enclosing

def ForRole : Role pending.entries.length → Type
  | .supplying q => {offer : ResultOf (discover pending link.suppliers) // offer.val.inner.route.val.index.val = q}
  | .enclosing => Pair pending position link

private def optionalRequest {α : Type} (action : WorkM α) : WorkM (Option α) := fun work =>
  match action.run work with
  | (.ok value,left) => (.ok (some value),left)
  | (.error .request,left) => (.ok none,left)
  | (.error error,left) => (.error error,left)

structure Supplement {n : Nat} (evidence : Role n → Type) where
  position : Fin n
  supplying : evidence (.supplying position)
  enclosing : Option (evidence .enclosing)

/-- The caller's credit precedes, and is independent of, the check of the
enclosing request. Each belongs to its own original queue position. -/
def read? : WorkM (Option (Supplement (ForRole pending position link))) := do
  if !originalFormal invoked.demand.source.original.subject then return none
  if (pendingBelowFormal link.providers.tree).isNone then return none
  let some offer ← optionalRequest (NaturalAffine.witness (discover pending link.suppliers)) | return none
  let parent ← optionalRequest (finishPair pending position link offer)
  return some ⟨offer.val.inner.route.val.index.val,⟨offer,rfl⟩,parent⟩
end

end QleisliKernel.Qirf.RuntimeNestedDuty
