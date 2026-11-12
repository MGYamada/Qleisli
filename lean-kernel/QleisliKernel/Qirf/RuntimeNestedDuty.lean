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

private abbrev Missing := Nat × Nat × String × String × Bool

private abbrev PendingAt {artifact catalogue context description graph implementations references prepared root requested}
    (subject : GenericOperationSubstitute.Subject artifact.sources) (closed : GenericOperation.Closed subject.description)
    (checked : @RuntimeOperationTree.Checked artifact catalogue context description graph implementations references prepared root requested) :=
  {index : Nat} → {cursor terminal : Cursor checked} → {need : RuntimeClosedProvider.Need} → {ok : Bool} →
    Tree subject closed checked index cursor terminal need ok → Option (List Missing)

private def pendingChildren {artifact catalogue context description graph implementations references prepared root requested}
    {subject : GenericOperationSubstitute.Subject artifact.sources} {closed : GenericOperation.Closed subject.description}
    {checked : @RuntimeOperationTree.Checked artifact catalogue context description graph implementations references prepared root requested}
    (next : PendingAt subject closed checked) :
    Nat → {cursor : Cursor checked} → {indices : List (Nat × Nat)} →
      {needs : List (Nat × RuntimeClosedProvider.Need)} → {ok : Bool} →
      RuntimeClosedProvider.Forest subject closed checked cursor indices needs ok → Option (List Missing) :=
  Nat.rec (fun {_ _ _ _} items => match items with | .nil => some [] | .cons .. => none)
    (fun _ later {_ _ _ _} items => match items with
      | .nil => some []
      | .cons _ _ tree tail => do
        let first ← next tree
        let rest ← later tail
        return first ++ rest)

/-- Visit the entire original ordered forest, including every formal wrapper.
Only a requested node with fully bound children may leave a hole. An unknown
provider, absent path evidence or further nested hole refuses this summary. -/
private def pendingTree {artifact catalogue context description graph implementations references prepared root requested}
    {subject : GenericOperationSubstitute.Subject artifact.sources} {closed : GenericOperation.Closed subject.description}
    {checked : @RuntimeOperationTree.Checked artifact catalogue context description graph implementations references prepared root requested} :
    Nat → PendingAt subject closed checked :=
  Nat.rec (motive := fun _ => PendingAt subject closed checked)
    (fun {_ _ _ _ _} _ => none)
    (fun _ next {index _ _ _ _} tree => match tree with
      | .formal _ _ child => next child
      | .node (cursor := current) (here := here) payload _ _ source _ _ _ _ _ children => do
        let rest ← pendingChildren next (payload.children.length+1) children
        match source with
        | .requested _ owner name =>
          if rest.isEmpty then return [(index,current.binding.index.val,owner,name,true)] else none
        | _ => if here then return rest else none)

/-- Exactly one unbound original request remains anywhere below the original
formal. Every other local provider and every ordered child is accounted for. -/
private def pendingBelowFormal {artifact catalogue context description graph implementations references prepared root requested}
    {subject : GenericOperationSubstitute.Subject artifact.sources} {closed : GenericOperation.Closed subject.description}
    {checked : @RuntimeOperationTree.Checked artifact catalogue context description graph implementations references prepared root requested}
    {index cursor terminal need ok} (tree : Tree subject closed checked index cursor terminal need ok) :
    Option (Nat × Nat × String × String × Bool) :=
  match tree with
  | .formal _ _ child =>
    match pendingTree (prepared.occurrences.length+1) child with
    | some [missing] => some missing
    | _ => none
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
  selectedNative : actualRecord = cursor.binding.index.val
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
    if found : record = cursor.binding.index.val ∧ owner = innerMarker.selected.resolution.moduleName ∧
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
            return ⟨i,record,by simpa only [found.2.1,found.2.2] using missing,
              found.1,supplier,tokens,⟨own,callee⟩,⟨source,decl,body⟩,
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

private def optionalRequest {α : Type} (action : WorkM α) : WorkM (Option α) := fun work =>
  match action.run work with
  | (.ok value,left) => (.ok (some value),left)
  | (.error .request,left) => (.ok none,left)
  | (.error error,left) => (.error error,left)

private def offerAt {artifact catalogue context description graph implementations references prepared root requested checked
    caller original event app transfer index key choice}
    (pending : @SourcePendingMeaning.Prepared artifact.sources catalogue)
    (supply : @RuntimeFormalActual.SupplyAt artifact.sources caller original event app transfer index key choice)
    (cursor : @Cursor artifact catalogue context description graph implementations references prepared root requested checked)
    {rootOwner rootName parentRecord parentInvocation}
    {parent : RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName caller event.target.callerName}
    (_prior : @RuntimeDutyInvocation.Binding artifact.sources catalogue pending.queue rootOwner rootName caller
      event.target.callerName parent parentRecord parentInvocation) : WorkM (Offer pending checked) := do
  let markers := supply.source.checked.provenance.markers
  exactWork (Exact.charge (16*(markers.length+SourceTrace.Meter.tokenFields supply.source.actual.argument.tokens+1)))
  match markers with
  | [marker] =>
    exactWork (Exact.charge (16*(marker.path.length+SourceTrace.Meter.tokenFields marker.tokens+1)))
    if marker.path = [] ∧ marker.tokens = supply.source.actual.argument.tokens ∧ parentInvocation.depth = 0 then
      let inner ← readInner marker cursor pending parent parentInvocation.id
      let inherited ← readInheritedAt catalogue app supply.source.actual.formal supply.source.actual.argument.tokens
        inner.route.val.invoked.val.demand.source.original marker
      return ⟨caller,event.scope,marker,cursor,rootOwner,rootName,event.target.callerName,parent,
        parentInvocation.id,inner,app,supply.source.actual.formal,supply.source.actual.argument.tokens,inherited⟩
    else throw .request
  | _ => throw .request

/-- Interior entries retain their original ordered constructor paths and
mixed-header slots. A single supplying assertion is selected only after its
own original caller, native child and Meaning equation have been checked. -/
private def discoverInterior {artifact catalogue context description graph implementations references prepared root requested checked
    native index cursor terminal caller original event app transfer paired rootOwner rootName owner name path record invocation result}
    (pending : @SourcePendingMeaning.Prepared artifact.sources catalogue)
    (hop : @RuntimeForwardedSupply.Selected artifact catalogue context description graph implementations references
      prepared root requested checked native index cursor terminal caller original event app transfer paired)
    (prior : @RuntimeDutyInvocation.Binding artifact.sources catalogue pending.queue rootOwner rootName owner name path record invocation)
    (remaining : GenericDutyQueue.Transport invocation.applications.reverse transfer.result.subject result) :
    RuntimeForwardedSupply.AtCaller hop prior remaining → WorkM (Offer pending checked) :=
  match prior,remaining with
  | .root ..,_ => fun impossible => nomatch impossible
  | .named (event := outer) (invocation := previous) (application := supplying) (target := target) outerPrior _,receipt => fun located => do
    let immediate := located.1
    let rows ← immediate.val.entries.mapM fun entry =>
      optionalRequest (offerAt pending entry.leaf.supply entry.leaf.selected.val.child.cursor outerPrior)
    match rows.filterMap id with
    | [offered] => return offered
    | _ => throw .request

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
  | .formal (caller := caller) (event := event) (parent := parent) (invocation := priorInvocation) (app := call) (prior := prior) hop interior _ =>
    match interior.val with
    | .noInterior _ => do
      let offered ← readSupplied hop pending prior
      return ⟨caller,event.scope,offered.marker,hop.wrapper.selected.child.cursor,_,_,
        event.target.callerName,parent,priorInvocation.id,offered.inner,
        call.original,hop.supply.source.actual.formal,hop.supply.source.actual.argument.tokens,offered.inherited.val⟩
    | .located _ located _ => discoverInterior pending hop prior _ located

private def originalFormal (description : GenericOperation.Description) : Bool :=
  description.root == 0 && match description.nodes with | [.formal _] => true | _ => false

/-- Constant-spine preflight on the already indexed queue item. Only the
original call and checked native tree can establish either source credit. -/
def possible {sources catalogue queue} (entry : @SourcePendingMeaning.Entry sources catalogue queue) : Bool :=
  match entry.subject with
  | .demand _ demand => originalFormal demand.source.original.subject
  | _ => false

section
variable {artifact catalogue owner description graph implementations references originals prepared root requested checked
    rootOwner rootName name path}
    (pending : @SourcePendingMeaning.Prepared artifact.sources catalogue)
    (position : Fin pending.entries.length)
    {source : @RuntimeSourceOperationMarkers.Checked artifact catalogue owner description graph implementations references originals
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

structure Supplement {n : Nat} (evidence : Role n → Type) where
  position : Fin n
  supplying : evidence (.supplying position)
  enclosing : Option (evidence .enclosing)

/-- The caller's credit precedes, and is independent of, the check of the
enclosing request. Each belongs to its own original queue position. -/
def read? : WorkM (Option (Supplement (ForRole pending position link))) := do
  if !originalFormal invoked.demand.source.original.subject then return none
  exactWork (Exact.charge (32*(prepared.occurrences.length+1)^2))
  if (pendingBelowFormal link.providers.tree).isNone then return none
  let some offer ← optionalRequest (NaturalAffine.witness (discover pending link.suppliers)) | return none
  let parent ← optionalRequest (finishPair pending position link offer)
  return some ⟨offer.val.inner.route.val.index.val,⟨offer,rfl⟩,parent⟩
end

end QleisliKernel.Qirf.RuntimeNestedDuty
