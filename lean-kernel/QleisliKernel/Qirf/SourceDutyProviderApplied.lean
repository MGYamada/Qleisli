import QleisliKernel.Qirf.SourceDutyProviderBare

/-! Authenticated original Basis/Nat provider applications with no Op children.
The checked original supplier activity, simultaneous transport and universal
closed conversion determine the actuals. No selected value for an unrelated
containing formal, equal-width type or equal matrix supplies an instance.
Only the original initial supplying scope and the existing bounded forwarding
edges are prepared here. Host actuals, callee-local open substitutions, groups
and other provenance remain unsupported preparation, not language exclusions.
Native body/access/Meaning equations and final graph checking remain separate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.SourceDutyProviderApplied
open QleisliKernel Finite SourceTypes
open GenericOperation GenericOperationSubstitute GenericDutyQueue

private def tokenFields (tokens : List LocatedToken) : Nat :=
  (tokens.map fun token => token.text.utf8ByteSize+4).sum

private def nameFields (names : List String) : Nat :=
  (names.map fun name => name.utf8ByteSize+1).sum

def basisNat (formal : StaticHeaders.Formal) : Bool :=
  match formal.kind with | .basis | .natural => true | .operation _ => false

private def applicationMatches {sources} (origin : Origin sources) (application : ApplicationSource sources) : Bool :=
  application.tokens == origin.tokens && application.scope == origin.scope &&
    application.state.owner == origin.state.owner && application.state.name == origin.state.name

/-- Build only the exact original mixed-kind Basis/Nat payload. The existing
InState receipt supplies the written Nat forms and their original premises;
the existing universal close reader below decides whether they are constant.
-/
def readDescription {sources} (application : ApplicationSource sources) : WorkM Description := do
  let formals := application.target.header.formals
  let keyFields := application.owner.utf8ByteSize+application.name.utf8ByteSize+4
  exactWork (Exact.charge (16*(formals.length+1)*(application.basisActuals.length+
    application.transfer.forms.length+1)*(keyFields+
    (formals.map fun formal => formal.name.utf8ByteSize+2).sum+1)))
  guard (formals.all basisNat && application.operationActuals.isEmpty) .request
  let bases ← formals.foldlM (fun previous formal => do
    match formal.kind with
    | .basis =>
      let some (_,code) := application.basisActuals.find? (fun actual =>
        actual.1 == ⟨application.owner,application.name,formal.ordinal⟩) | throw .request
      pure (previous ++ [(formal.name,code)])
    | _ => pure previous) []
  let naturals ← formals.foldlM (fun previous formal => do
    match formal.kind with
    | .natural =>
      let some value := application.transfer.forms[formal.ordinal]? | throw .request
      pure (previous ++ [(formal.name,value.form)])
    | _ => pure previous) []
  return GenericOperation.provider (StaticHeaders.frame application.state.prepared.original)
    application.owner application.name bases naturals [] []

structure Checked {sources catalogue record invocation demand view}
    (provider : @SourceDutySlots.Provider sources catalogue record invocation demand view) : Type where
  supplier : SourceDutyProviderBare.Site catalogue provider.supplier.origin.state
    provider.supplier.origin.scope provider.supplier.origin.tokens
  supplyingRoot : supplier.original.entry.index.val = invocation.id.root
  duty : SourceDutyProviderBare.Original catalogue demand.source.original.origin.state
  dutyRecord : duty.entry.index.val = record.val
  transport : Transport invocation.applications.reverse
    ⟨demand.source.original.subject,demand.source.original.suppliers⟩ demand.transported.subject
  sameTransport : transport = demand.transported.receipt
  calls : SourceDutyProviderBare.Applications catalogue invocation.applications
  noGroup : demand.source.original.runtimeApplication.isNone = true
  writtenApplication : (match provider.written with | .application _ => true | .name _ => false) = true
  actualArguments : provider.written.arguments.isEmpty = false
  noOperations : provider.operations = []
  singleton : provider.closed.data.description.nodes =
    [.provider provider.owner provider.name provider.bases provider.naturals []]
  rootNode : provider.closed.data.description.root = 0
  application : ApplicationSource sources
  selected : supplier.original.entry.body.outcome.applications.filter (applicationMatches provider.supplier.origin) = [application]
  sameTokens : application.tokens = provider.supplier.origin.tokens
  sameScope : application.scope = provider.supplier.origin.scope
  sameOwner : application.state.owner = provider.supplier.origin.state.owner
  sameName : application.state.name = provider.supplier.origin.state.name
  sameSource : application.state.prepared.original.envelope.source =
    provider.supplier.origin.state.prepared.original.envelope.source
  sameDeclaration : application.state.prepared.original.envelope.declaration =
    provider.supplier.origin.state.prepared.original.envelope.declaration
  sameBody : application.state.prepared.original.envelope.occurrence =
    provider.supplier.origin.state.prepared.original.envelope.occurrence
  unguarded : application.state.environment.guards.isEmpty = true
  targetOwner : application.owner = provider.owner
  targetName : application.name = provider.name
  targetSource : application.target.envelope.source = provider.signature.original.source
  targetDeclaration : application.target.envelope.declaration = provider.signature.original.declaration
  targetBody : application.target.envelope.occurrence = provider.signature.original.occurrence
  kinds : application.target.header.formals.all basisNat = true
  noActualOperations : application.operationActuals.isEmpty = true
  description : Description
  descriptionRead : SourceDutySlots.Computed (readDescription application) description
  closed : GenericOperation.Closed description
  closedRead : SourceDutySlots.Computed (GenericOperation.close description) (.closed closed)
  sameClosed : closed.data.description = provider.closed.data.description
  relevance : SourceRows.Retained
    (supplier.original.rows ++ duty.rows ++ calls.rows ++ provider.supplier.origin.rows)

def Checked.rawRows {sources catalogue record invocation demand view provider}
    (checked : @Checked sources catalogue record invocation demand view provider) : List SourceRows.Row :=
  checked.supplier.original.rawRows ++ checked.duty.rawRows ++ checked.calls.rawRows ++ provider.supplier.origin.rows

def Checked.rows {sources catalogue record invocation demand view provider}
    (checked : @Checked sources catalogue record invocation demand view provider) : List SourceRows.Row := checked.relevance.rows

theorem Checked.rows_members {sources catalogue record invocation demand view provider}
    (checked : @Checked sources catalogue record invocation demand view provider) (row : SourceRows.Row) :
    row ∈ checked.rows ↔ row ∈ checked.rawRows := by
  change row ∈ checked.relevance.rows ↔ _
  rw [checked.relevance.members]
  simp only [Checked.rawRows,List.mem_append,SourceDutyProviderBare.Original.rows_members,
    SourceDutyProviderBare.Applications.rows_members]

/-- Read an explicit applied branch; the bare reader is neither called nor
retried. The exact original application is selected from its retained checked
body, rather than reconstructed from the provider's convenient closed header.
-/
def read {sources catalogue record invocation demand view}
    (provider : @SourceDutySlots.Provider sources catalogue record invocation demand view) : WorkM (Checked provider) := do
  let supplier ← SourceDutyProviderBare.readSite catalogue provider.supplier.origin.state
    provider.supplier.origin.scope provider.supplier.origin.tokens
  let duty ← SourceDutyProviderBare.readOriginal catalogue demand.source.original.origin.state
  exactWork (Exact.charge (32*(provider.owner.utf8ByteSize+provider.name.utf8ByteSize+
    provider.closed.data.description.nodes.length+provider.operations.length+invocation.depth+
    provider.written.arguments.length+1)))
  if supplyingRoot : supplier.original.entry.index.val = invocation.id.root then
    if dutyRecord : duty.entry.index.val = record.val then
      if noGroup : demand.source.original.runtimeApplication.isNone = true then
        if applied : (match provider.written with | .application _ => true | .name _ => false) = true then
          if actualArguments : provider.written.arguments.isEmpty = false then
            if leaf : provider.operations = [] ∧ provider.closed.data.description.nodes =
                [.provider provider.owner provider.name provider.bases provider.naturals []] ∧
                provider.closed.data.description.root = 0 then
              let applications := supplier.original.entry.body.outcome.applications
              exactWork (Exact.charge (16*(supplier.original.entry.body.outcome.activities.length+
                (applications.map fun application => tokenFields application.tokens+tokenFields provider.supplier.origin.tokens+
                  nameFields application.scope+nameFields provider.supplier.origin.scope+
                  application.state.owner.utf8ByteSize+application.state.name.utf8ByteSize+
                  provider.supplier.origin.state.owner.utf8ByteSize+provider.supplier.origin.state.name.utf8ByteSize+4).sum+1)))
              match selected : applications.filter (applicationMatches provider.supplier.origin) with
              | [application] =>
                let original := provider.supplier.origin.state.prepared.original.envelope
                let target := provider.signature.original
                exactWork (Exact.charge (32*(tokenFields application.tokens+tokenFields provider.supplier.origin.tokens+
                  nameFields application.scope+nameFields provider.supplier.origin.scope+
                  application.state.owner.utf8ByteSize+application.state.name.utf8ByteSize+
                  provider.supplier.origin.state.owner.utf8ByteSize+provider.supplier.origin.state.name.utf8ByteSize+
                  application.state.prepared.original.envelope.source.utf8ByteSize+original.source.utf8ByteSize+
                  tokenFields application.state.prepared.original.envelope.occurrence.header+
                  tokenFields application.state.prepared.original.envelope.occurrence.body+
                  tokenFields original.occurrence.header+tokenFields original.occurrence.body+
                  application.owner.utf8ByteSize+application.name.utf8ByteSize+provider.owner.utf8ByteSize+provider.name.utf8ByteSize+
                  application.target.envelope.source.utf8ByteSize+target.source.utf8ByteSize+
                  tokenFields application.target.envelope.occurrence.header+tokenFields application.target.envelope.occurrence.body+
                  tokenFields target.occurrence.header+tokenFields target.occurrence.body+
                  application.target.header.formals.length+application.operationActuals.length+
                  application.state.environment.guards.length+1)))
                if same : application.tokens = provider.supplier.origin.tokens ∧ application.scope = provider.supplier.origin.scope ∧
                    application.state.owner = provider.supplier.origin.state.owner ∧ application.state.name = provider.supplier.origin.state.name ∧
                    application.state.prepared.original.envelope.source = original.source ∧
                    application.state.prepared.original.envelope.declaration = original.declaration ∧
                    application.state.prepared.original.envelope.occurrence = original.occurrence ∧
                    application.state.environment.guards.isEmpty = true ∧
                    application.owner = provider.owner ∧ application.name = provider.name ∧
                    application.target.envelope.source = target.source ∧ application.target.envelope.declaration = target.declaration ∧
                    application.target.envelope.occurrence = target.occurrence ∧
                    application.target.header.formals.all basisNat = true ∧ application.operationActuals.isEmpty = true then
                  let description ← NaturalAffine.witness (readDescription application)
                  let status ← NaturalAffine.witness (GenericOperation.close description.val)
                  match closedStatus : status.val with
                  | .conditional .. => throw .request
                  | .closed closed =>
                    exactWork (Exact.charge (32*(provider.owner.utf8ByteSize+provider.name.utf8ByteSize+
                      (provider.bases.map fun actual => actual.1.utf8ByteSize+1).sum+
                      Raw.OwnerFlow.fields (provider.bases.zipIdx.map fun (actual,index) => ⟨index,actual.2⟩)+
                      (provider.naturals.map fun actual => actual.1.utf8ByteSize+2).sum+1)))
                    if sameClosed : closed.data.description = provider.closed.data.description then
                      let calls ← SourceDutyProviderBare.readApplications catalogue invocation.applications
                      let relevance ← SourceRows.read
                        (supplier.original.rows ++ duty.rows ++ calls.rows ++ provider.supplier.origin.rows)
                      return ⟨supplier,supplyingRoot,duty,dutyRecord,demand.transported.receipt,rfl,calls,noGroup,
                        applied,actualArguments,leaf.1,leaf.2.1,leaf.2.2,application,selected,
                        same.1,same.2.1,same.2.2.1,same.2.2.2.1,same.2.2.2.2.1,same.2.2.2.2.2.1,
                        same.2.2.2.2.2.2.1,same.2.2.2.2.2.2.2.1,same.2.2.2.2.2.2.2.2.1,
                        same.2.2.2.2.2.2.2.2.2.1,same.2.2.2.2.2.2.2.2.2.2.1,
                        same.2.2.2.2.2.2.2.2.2.2.2.1,same.2.2.2.2.2.2.2.2.2.2.2.2.1,
                        same.2.2.2.2.2.2.2.2.2.2.2.2.2.1,same.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
                        description.val,by with_reducible exact description.property,closed,
                        by with_reducible simpa only [closedStatus] using status.property,sameClosed,relevance⟩
                    else throw .request
                else throw .request
              | _ => throw .request
            else throw .request
          else throw .request
        else throw .request
      else throw .request
    else throw .request
  else throw .request

end QleisliKernel.Qirf.SourceDutyProviderApplied
