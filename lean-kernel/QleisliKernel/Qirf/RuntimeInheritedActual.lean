import QleisliKernel.Qirf.RuntimeActualDuty

/-! Recover the one original Op-formal binding introduced by checking a supplied assertion. Retain the checked caller/callee, the full ordered actual and its original slot.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeNestedDuty
open QleisliKernel Finite SourceTypes
open RuntimeInterval (Computed)
open RuntimeNativeSubject (Cursor)

-- A written assertion in a static actual inherits the original supplying call.
-- Compare its full rooted original payload and every lexical supplier row.
-- Restrict this reader to one scalar-free Op formal from an unguarded root.
private structure OriginalKey where
  owner : String
  name : String
  source : String
  declaration : Declaration
  body : BodyOccurrence
  deriving DecidableEq

private def originalKey {sources owner name} (o : OrdinarySignature.Original sources owner name) : OriginalKey :=
  ⟨owner,name,o.source,o.declaration,o.occurrence⟩

/-- Include the actual module/function names and both compared copies of
the declaration. A module's name need not appear in its source text. -/
def originalFields {sources owner name} (o : OrdinarySignature.Original sources owner name) : Nat :=
  let decl := o.declaration
  let body := o.occurrence
  owner.utf8ByteSize+name.utf8ByteSize+o.source.utf8ByteSize+
    2*(decl.name.utf8ByteSize+decl.kind.utf8ByteSize+SourceTrace.Meter.nameFields decl.body+2)+
    SourceTrace.Meter.tokenFields [body.nameToken,body.openBrace,body.closeBrace]+
    SourceTrace.Meter.tokenFields body.header+SourceTrace.Meter.tokenFields body.body+1

private structure OriginKey where
  source : OriginalKey
  scope : List String
  tokens : List LocatedToken
  offset : Nat
  rows : List (String × String)
  unguarded : Bool
  deriving DecidableEq

private def originKey {sources} (o : GenericOperation.Origin sources) : OriginKey :=
  ⟨originalKey o.state.prepared.original.envelope,o.scope,o.tokens,o.offset,o.rows,o.state.environment.guards.isEmpty⟩

private structure ActualKey where
  parameter : Semantics.SymbolicBasis.Parameter
  frame : List NaturalFrames.Binder
  nodes : List GenericOperation.Node
  root : Nat
  frames : List (List NaturalFrames.Binder)
  suppliers : List (Nat × OriginKey)
  deriving DecidableEq

private def actualKey {sources} (a : GenericOperation.ActualOperation sources) : ActualKey :=
  ⟨a.original,a.subject.frame.binders,a.subject.nodes,a.subject.root,a.subject.nodeFrames.map (·.binders),
    a.suppliers.map fun (index,origin) => (index,originKey origin)⟩

private structure CallKey where
  caller : OriginalKey
  scope : List String
  tokens : List LocatedToken
  unguarded : Bool
  callee : OriginalKey
  bases : List (Semantics.SymbolicBasis.Parameter × Semantics.SymbolicBasis.Code)
  naturals : List Semantics.SourceAffine.Form
  operations : List ActualKey
  deriving DecidableEq

private def callKey {sources} (a : GenericOperation.ApplicationSource sources) : CallKey :=
  ⟨originalKey a.state.prepared.original.envelope,a.scope,a.tokens,a.state.environment.guards.isEmpty,
    originalKey a.target.envelope,a.basisActuals,a.naturalActuals,a.operationActuals.map actualKey⟩

-- This first case has no scalar actual at the supplying call and the
-- operation itself has exactly a bare provider and its requested wrapper.
-- Check this constant-spine restriction before comparing symbolic payloads.
def requestedBare (description : GenericOperation.Description) : Bool :=
  description.root == 1 && match description.nodes with
    | [.provider _ _ [] [] [] [],.requested 0 _ _] => true
    | _ => false

private def simpleCall {sources} (call : GenericOperation.ApplicationSource sources) : Bool :=
  match call.basisActuals,call.naturalActuals,call.operationActuals with
  | [],[],[op] => requestedBare op.subject
  | _,_,_ => false

private def applicationCost {sources} (a : GenericOperation.ApplicationSource sources) : Nat :=
  originalFields a.state.prepared.original.envelope + originalFields a.target.envelope +
    SourceTrace.Meter.tokenFields a.tokens + SourceTrace.Meter.nameFields a.scope +
    (a.operationActuals.map fun actual => GenericOperation.Meter.key actual.original+
      GenericOperation.Meter.payload actual.subject+(actual.suppliers.map fun row =>
        originalFields row.2.state.prepared.original.envelope+SourceTrace.Meter.tokenFields row.2.tokens+
        SourceTrace.Meter.nameFields row.2.scope+(row.2.rows.map fun (name,src) => name.utf8ByteSize+src.utf8ByteSize+2).sum+2).sum).sum+1

structure Inherited {sources} (catalogue : GenericCatalogue.Checked sources)
    (app : GenericOperation.ApplicationSource sources) (formal : StaticHeaders.Formal)
    (argument : List LocatedToken) (duty : GenericOperation.Duty sources) (tokens : List LocatedToken) where
  binding : GenericOperation.Binding sources
  only : duty.bindings = [binding]
  application : GenericOperation.ApplicationSource sources
  retained : binding.application = some application
  sharedCall : callKey application = callKey app
  supplying : SourceDutyProviderBare.Applications catalogue [application]
  readOriginal : Computed (SourceDutyProviderBare.readApplications catalogue [application]) supplying
  originalTarget : originalKey binding.original.envelope = originalKey app.target.envelope
  actualOwner : originalKey binding.actual.state.prepared.original.envelope = originalKey app.state.prepared.original.envelope
  mixed : binding.formal = formal
  formalOfCall : app.target.header.formals = [binding.formal]
  appliedTo : binding.actual.tokens = argument ∧ binding.actual.tokens = tokens
  sameScope : binding.actual.scope = app.scope
  noGuard : binding.actual.state.environment.guards.isEmpty = true

section
variable {artifact catalogue context description graph implementations references prepared root requested checked
    native index cursor terminal caller original event app transfer paired}
    (hop : @RuntimeForwardedSupply.Selected artifact catalogue context description graph implementations references
      prepared root requested checked native index cursor terminal caller original event app transfer paired)
    (duty : GenericOperation.Duty artifact.sources)
    (marker : SourceOperation.Marker artifact.sources caller event.scope)

def readInherited : WorkM (Inherited catalogue app hop.supply.source.actual.formal
    hop.supply.source.actual.argument.tokens duty marker.tokens) := do
  match only : duty.bindings with
  | [binding] =>
    match retained : binding.application with
    | none => throw Finite.Error.request
    | some application =>
      guard (simpleCall application && simpleCall app) Finite.Error.request
      exactWork (Exact.charge (32*(applicationCost application+applicationCost app+
        originalFields binding.actual.state.prepared.original.envelope+originalFields binding.original.envelope+
        SourceTrace.Meter.tokenFields binding.actual.tokens+SourceTrace.Meter.tokenFields marker.tokens+
        SourceTrace.Meter.tokenFields hop.supply.source.actual.argument.tokens+
        SourceTrace.Meter.nameFields binding.actual.scope+1)))
      if call : callKey application = callKey app then
        let supplied ← NaturalAffine.witness (SourceDutyProviderBare.readApplications catalogue [application])
        if target : originalKey binding.original.envelope = originalKey app.target.envelope ∧
            originalKey binding.actual.state.prepared.original.envelope = originalKey app.state.prepared.original.envelope ∧
            binding.formal = hop.supply.source.actual.formal ∧ app.target.header.formals = [binding.formal] then
          if site : (binding.actual.tokens = hop.supply.source.actual.argument.tokens ∧ binding.actual.tokens = marker.tokens) ∧
              binding.actual.scope = app.scope ∧ binding.actual.state.environment.guards.isEmpty = true then
            let ⟨original,caller,formal,onlyFormal⟩ := target
            return ⟨binding,only,application,retained,call,supplied.val,by with_reducible exact supplied.property,
              original,caller,formal,onlyFormal,site.1,site.2.1,site.2.2⟩
          else throw Finite.Error.request
        else throw Finite.Error.request
      else throw Finite.Error.request
  | _ => throw Finite.Error.request
end

section
variable {artifact catalogue context description graph implementations references prepared root requested checked
    native index cursor terminal caller original event app transfer paired}
    (hop : @RuntimeForwardedSupply.Selected artifact catalogue context description graph implementations references
      prepared root requested checked native index cursor terminal caller original event app transfer paired)
    {rootOwner rootName} (pending : @SourcePendingMeaning.Prepared artifact.sources catalogue)
    {parent : RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName caller event.target.callerName}
    {parentRecord parentInvocation}
    (prior : @RuntimeDutyInvocation.Binding artifact.sources catalogue pending.queue rootOwner rootName caller
      event.target.callerName parent parentRecord parentInvocation)

structure Supplied where
  parentRead : RuntimeDutyInvocation.Binding pending.queue parent parentInvocation
  marker : SourceOperation.Marker artifact.sources caller event.scope
  onlyMarker : hop.supply.source.checked.provenance.markers = [marker]
  rootMarker : marker.path = []
  wholeArgument : marker.tokens = hop.supply.source.actual.argument.tokens
  parentRoot : parentInvocation.depth = 0
  inner : Inner marker hop.wrapper.selected.child.cursor pending parent parentInvocation.id
  originalRead : Computed (readInner marker hop.wrapper.selected.child.cursor pending parent parentInvocation.id) inner
  inherited : ResultOf (readInherited hop inner.route.val.invoked.val.demand.source.original marker)

def readSupplied : WorkM (Supplied hop pending (parent := parent) (parentInvocation := parentInvocation)) := do
  guard (simpleCall app) .request
  let markers := hop.supply.source.checked.provenance.markers
  exactWork (Exact.charge (16*(markers.length+SourceTrace.Meter.tokenFields hop.supply.source.actual.argument.tokens+1)))
  match selected : markers with
  | [marker] =>
    exactWork (Exact.charge (16*(marker.path.length+SourceTrace.Meter.tokenFields marker.tokens+1)))
    if same : marker.path = [] ∧ marker.tokens = hop.supply.source.actual.argument.tokens ∧ parentInvocation.depth = 0 then
      let inner ← NaturalAffine.witness (readInner marker hop.wrapper.selected.child.cursor pending parent parentInvocation.id)
      let binding ← NaturalAffine.witness (readInherited hop inner.val.route.val.invoked.val.demand.source.original marker)
      return ⟨prior,marker,selected,same.1,same.2.1,same.2.2,inner.val,by with_reducible exact inner.property,binding⟩
    else throw .request
  | _ => throw .request
end

end QleisliKernel.Qirf.RuntimeNestedDuty
