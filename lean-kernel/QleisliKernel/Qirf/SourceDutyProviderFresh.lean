import QleisliKernel.Qirf.SourceDutySlots
import QleisliKernel.Qirf.RuntimeProviderHeader

/-! Fresh original-source provider preparation for one explicit internal case.
The indexed enclosing original is nongeneric, transport has no call edge, no
inherited duty binding or runtime-group application is present, and the closed
provider has no Op children. Ordered original body bytes authenticate the
supplier occurrence before its owning-module context is used. This is not a
general supplier conversion or a language restriction. Unsupported mappings
refuse this preparation; they retain their separate pending continuation.
The resulting graph, ProviderInstance and exact source body are checked source
metadata. Native interval/code/effect/J/C/M equations and full original Meaning
graph transfer remain mandatory; no artifact, final root or handle is read.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.SourceDutyProviderFresh
open QleisliKernel Finite SourceTypes
open GenericOperation GenericOperationSubstitute GenericDutyQueue

private def enclosing {sources catalogue} (record : @RecordIndex sources catalogue) : GenericTypeTrace.BodyRecord sources :=
  catalogue.records[record.val]'record.isLt

private theorem applications_nil {sources catalogue record} (invocation : @Invocation sources catalogue record)
    (root : invocation.depth = 0) : invocation.applications = [] := by
  cases invocation with
  | root _ => rfl
  | call parent application target => simp [Invocation.depth] at root

private theorem identity_subject {sources original result} (transport : @Transport sources [] original result) :
    result = original := by cases transport; rfl

private theorem original_subject {sources catalogue record invocation}
    (demand : @Demand sources catalogue record invocation) (root : invocation.depth = 0) :
    demand.transported.subject = ⟨demand.source.original.subject,demand.source.original.suppliers⟩ := by
  have noApplications := applications_nil invocation root
  have identity : Transport [] ⟨demand.source.original.subject,demand.source.original.suppliers⟩
      demand.transported.subject := by
    simpa only [noApplications,List.reverse_nil] using demand.transported.receipt
  exact identity_subject identity

structure Eligible {sources catalogue record invocation demand view}
    (provider : @SourceDutySlots.Provider sources catalogue record invocation demand view) where
  root : invocation.depth = 0
  identity : demand.transported.subject = ⟨demand.source.original.subject,demand.source.original.suppliers⟩
  noBindings : demand.source.original.bindings.isEmpty = true
  noGroup : demand.source.original.runtimeApplication.isNone = true
  nongeneric : (enclosing record).definition.original.header.formals.isEmpty = true
  supplierOwner : provider.supplier.origin.state.owner = (enclosing record).owner
  supplierName : provider.supplier.origin.state.name = (enclosing record).name
  supplierSource : provider.supplier.origin.state.prepared.original.envelope.source =
    (enclosing record).definition.original.envelope.source
  supplierDeclaration : provider.supplier.origin.state.prepared.original.envelope.declaration =
    (enclosing record).definition.original.envelope.declaration
  supplierBody : provider.supplier.origin.state.prepared.original.envelope.occurrence =
    (enclosing record).definition.original.envelope.occurrence
  dutyOwner : demand.source.original.origin.state.owner = (enclosing record).owner
  dutyName : demand.source.original.origin.state.name = (enclosing record).name
  dutySource : demand.source.original.origin.state.prepared.original.envelope.source =
    (enclosing record).definition.original.envelope.source
  dutyDeclaration : demand.source.original.origin.state.prepared.original.envelope.declaration =
    (enclosing record).definition.original.envelope.declaration
  dutyBody : demand.source.original.origin.state.prepared.original.envelope.occurrence =
    (enclosing record).definition.original.envelope.occurrence
  scope : provider.supplier.origin.scope = demand.source.original.origin.scope
  noOperations : provider.operations = []
  singleton : provider.closed.data.description.nodes =
    [.provider provider.owner provider.name provider.bases provider.naturals []]
  rootNode : provider.closed.data.description.root = 0
  bytes : LocatedFacts.OrderedSlices (enclosing record).definition.original.envelope.source.toUTF8
    (enclosing record).definition.original.envelope.occurrence.openBrace.span.endByte provider.supplier.origin.tokens
  inside : provider.supplier.origin.tokens.all (fun token => token.span.endByte ≤
    (enclosing record).definition.original.envelope.occurrence.closeBrace.span.startByte) = true

private def tokenFields (tokens : List LocatedToken) : Nat :=
  (tokens.map fun token => token.text.utf8ByteSize+4).sum

private def argumentsFields (arguments : StaticTypes.Arguments) : Nat :=
  Raw.OwnerFlow.fields (arguments.bases.zipIdx.map fun (actual,index) => ⟨index,actual.2⟩)+
    (arguments.bases.map fun actual => actual.1.utf8ByteSize+1).sum+
    (arguments.naturals.map fun actual => actual.1.utf8ByteSize+2).sum+
    arguments.operations.length+1

def readEligible {sources catalogue record invocation demand view}
    (provider : @SourceDutySlots.Provider sources catalogue record invocation demand view) : WorkM (Eligible provider) := do
  exactWork (Exact.charge (16*(catalogue.records.length+invocation.depth+1)))
  let caller := enclosing record
  let original := caller.definition.original.envelope
  let supplier := provider.supplier.origin
  let duty := demand.source.original.origin
  exactWork (Exact.charge (32*(original.source.utf8ByteSize+supplier.state.prepared.original.envelope.source.utf8ByteSize+
    duty.state.prepared.original.envelope.source.utf8ByteSize+tokenFields supplier.tokens+
    tokenFields original.occurrence.header+tokenFields original.occurrence.body+
    caller.owner.utf8ByteSize+caller.name.utf8ByteSize+supplier.state.owner.utf8ByteSize+supplier.state.name.utf8ByteSize+
    duty.state.owner.utf8ByteSize+duty.state.name.utf8ByteSize+
    (supplier.scope.map fun name => name.utf8ByteSize+1).sum+
    (duty.scope.map fun name => name.utf8ByteSize+1).sum+argumentsFields provider.signature.staticArguments+
    demand.source.original.bindings.length+caller.definition.original.header.formals.length+1)))
  if root : invocation.depth = 0 then
    if noBindings : demand.source.original.bindings.isEmpty = true then
      if noGroup : demand.source.original.runtimeApplication.isNone = true then
        if nongeneric : caller.definition.original.header.formals.isEmpty = true then
          if site : supplier.state.owner = caller.owner ∧ supplier.state.name = caller.name ∧
              supplier.state.prepared.original.envelope.source = original.source ∧
              supplier.state.prepared.original.envelope.declaration = original.declaration ∧
              supplier.state.prepared.original.envelope.occurrence = original.occurrence ∧
              duty.state.owner = caller.owner ∧ duty.state.name = caller.name ∧
              duty.state.prepared.original.envelope.source = original.source ∧
              duty.state.prepared.original.envelope.declaration = original.declaration ∧
              duty.state.prepared.original.envelope.occurrence = original.occurrence ∧ supplier.scope = duty.scope then
            if leaf : provider.operations = [] ∧ provider.closed.data.description.nodes =
                [.provider provider.owner provider.name provider.bases provider.naturals []] ∧
                provider.closed.data.description.root = 0 then
              if bytes : LocatedFacts.checkOrdered original.source.toUTF8 original.occurrence.openBrace.span.endByte supplier.tokens = true then
                if inside : supplier.tokens.all (fun token => token.span.endByte ≤ original.occurrence.closeBrace.span.startByte) = true then
                  return ⟨root,original_subject demand root,noBindings,noGroup,nongeneric,
                    site.1,site.2.1,site.2.2.1,site.2.2.2.1,site.2.2.2.2.1,
                    site.2.2.2.2.2.1,site.2.2.2.2.2.2.1,site.2.2.2.2.2.2.2.1,
                    site.2.2.2.2.2.2.2.2.1,site.2.2.2.2.2.2.2.2.2.1,site.2.2.2.2.2.2.2.2.2.2,
                    leaf.1,leaf.2.1,leaf.2.2,LocatedFacts.checkOrdered_sound _ _ _ bytes,inside⟩
                else throw .request
              else throw .request
            else throw .request
          else throw .request
        else throw .request
      else throw .request
    else throw .request
  else throw .request

/-- Full data correspondence to the native graph's own provider signature.
Its core and actual receipts, rather than a reconstructed equal-width header,
are the source of the retained runtime Body. -/
structure Identity {sources catalogue record invocation demand view}
    (provider : @SourceDutySlots.Provider sources catalogue record invocation demand view)
    (native : StaticOperation.Provider sources) where
  moduleName : native.moduleName = provider.owner
  declarationName : native.declarationName = provider.name
  source : native.signature.original.source = provider.signature.original.source
  declaration : native.signature.original.declaration = provider.signature.original.declaration
  envelope : native.signature.original.occurrence = provider.signature.original.occurrence
  actuals : native.signature.staticArguments = provider.signature.staticArguments
  inputs : native.signature.inputs = provider.signature.inputs
  outputs : native.signature.outputs = provider.signature.outputs
  shape : native.signature.parts = provider.signature.parts
  publicEffect : native.signature.original.parsedHeader.effect = provider.signature.original.parsedHeader.effect
  expectedEffect : native.expectedEffect = provider.expectedEffect

private def readIdentity {sources catalogue record invocation demand view}
    (provider : @SourceDutySlots.Provider sources catalogue record invocation demand view)
    (native : StaticOperation.Provider sources) : WorkM (Identity provider native) := do
  exactWork (Exact.charge (32*(native.moduleName.utf8ByteSize+native.declarationName.utf8ByteSize+
    provider.owner.utf8ByteSize+provider.name.utf8ByteSize+native.signature.original.source.utf8ByteSize+
    provider.signature.original.source.utf8ByteSize+tokenFields native.signature.original.occurrence.header+
    tokenFields native.signature.original.occurrence.body+tokenFields provider.signature.original.occurrence.header+
    tokenFields provider.signature.original.occurrence.body+argumentsFields native.signature.staticArguments+
    argumentsFields provider.signature.staticArguments+
    Raw.OwnerFlow.fields ((native.signature.inputs ++ native.signature.outputs).zipIdx.map fun (basis,index) => ⟨index,basis⟩)+
    Raw.OwnerFlow.fields ((provider.signature.inputs ++ provider.signature.outputs).zipIdx.map fun (basis,index) => ⟨index,basis⟩)+1)))
  if same : native.moduleName = provider.owner ∧ native.declarationName = provider.name ∧
      native.signature.original.source = provider.signature.original.source ∧
      native.signature.original.declaration = provider.signature.original.declaration ∧
      native.signature.original.occurrence = provider.signature.original.occurrence ∧
      native.signature.staticArguments = provider.signature.staticArguments ∧
      native.signature.inputs = provider.signature.inputs ∧ native.signature.outputs = provider.signature.outputs ∧
      native.signature.parts = provider.signature.parts ∧
      native.signature.original.parsedHeader.effect = provider.signature.original.parsedHeader.effect ∧
      native.expectedEffect = provider.expectedEffect then
    return ⟨same.1,same.2.1,same.2.2.1,same.2.2.2.1,same.2.2.2.2.1,same.2.2.2.2.2.1,
      same.2.2.2.2.2.2.1,same.2.2.2.2.2.2.2.1,same.2.2.2.2.2.2.2.2.1,
      same.2.2.2.2.2.2.2.2.2.1,same.2.2.2.2.2.2.2.2.2.2⟩
  else throw .request

structure Checked {sources catalogue record invocation demand view}
    (provider : @SourceDutySlots.Provider sources catalogue record invocation demand view) where
  eligible : Eligible provider
  graph : StaticOperation.CheckedGraph sources (.source (enclosing record).owner) provider.closed.data.description
  graphRead : SourceDutySlots.Computed (StaticOperation.check sources (.source (enclosing record).owner)
    provider.closed.data.description (some catalogue)) graph
  original : RuntimeProviderHeader.Original graph provider.closed.data.description.root
  originalRead : SourceDutySlots.Computed (RuntimeProviderHeader.readOriginal graph provider.closed.data.description.root) original
  identity : Identity provider original.supplied.provider
  context : original.supplied.context = .source (enclosing record).owner
  noActualChildren : original.supplied.arguments.actuals.isEmpty = true

/-- Source preparation only. This function does not mutate the source slot
plan or consume any pending native body, access, Meaning graph or IR equation. -/
def read {sources catalogue record invocation demand view}
    (provider : @SourceDutySlots.Provider sources catalogue record invocation demand view) : WorkM (Checked provider) := do
  let eligible ← readEligible provider
  let graph ← NaturalAffine.witness (StaticOperation.check sources (.source (enclosing record).owner)
    provider.closed.data.description (some catalogue))
  let original ← NaturalAffine.witness (RuntimeProviderHeader.readOriginal graph.val provider.closed.data.description.root)
  let identity ← readIdentity provider original.val.supplied.provider
  exactWork (Exact.charge (16*((enclosing record).owner.utf8ByteSize+
    (match original.val.supplied.context with | .external => 0 | .source owner => owner.utf8ByteSize)+
    original.val.supplied.arguments.actuals.length+1)))
  if context : original.val.supplied.context = .source (enclosing record).owner then
    if noActualChildren : original.val.supplied.arguments.actuals.isEmpty = true then
      return ⟨eligible,graph.val,by with_reducible exact graph.property,
        original.val,by with_reducible exact original.property,identity,context,noActualChildren⟩
    else throw .request
  else throw .request

end QleisliKernel.Qirf.SourceDutyProviderFresh
