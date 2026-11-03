import QleisliKernel.Qirf.SourceDutySlots
import QleisliKernel.SourceTypes.ParameterPatterns
import QleisliKernel.SourceTypes.NaturalRows
import QleisliKernel.SourceTypes.SourceRows

/-! Source provenance for a bare, nongeneric provider forwarded through actual
original calls. The terminal supplier belongs to the indexed root declaration;
its exact original body and captured scope authenticate the written occurrence.
Every intervening call keeps its simultaneous substitution and original query.
This bounded preparation admits no static provider actual, Op child, runtime
group, local alias or guarded scope. Unsupported provenance stays pending; it
is not a restriction on the language or a fallback from another reader.
These receipts establish source provenance only. Provider bodies, demanded
access, Meaning graph transfer and same-final-root equations remain separate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.SourceDutyProviderBare
open QleisliKernel Finite SourceTypes
open GenericOperation GenericOperationSubstitute GenericDutyQueue

private def tokenFields (tokens : List LocatedToken) : Nat :=
  (tokens.map fun token => token.text.utf8ByteSize+4).sum

private def nameFields (names : List String) : Nat :=
  (names.map fun name => name.utf8ByteSize+1).sum

/-- An actual canonical lookup of the complete supplying original. The Entry
retains source/declaration/body identity; equality of display names is not the
authority for selecting a later module's private context. -/
structure Original {sources} (catalogue : GenericCatalogue.Checked sources)
    (state : GenericLexicalNatural.SomeEnvironment sources) : Type where
  entry : GenericCatalogue.Entry catalogue.toRuntimeChecked state.prepared.original.envelope
  computed : SourceDutySlots.Computed
    (GenericCatalogue.lookup catalogue.toRuntimeChecked state.prepared.original.envelope) entry
  owner : entry.body.owner = state.owner
  name : entry.body.name = state.name
  source : entry.body.definition.original.envelope.source = state.prepared.original.envelope.source
  declaration : entry.body.definition.original.envelope.declaration = state.prepared.original.envelope.declaration
  body : entry.body.definition.original.envelope.occurrence = state.prepared.original.envelope.occurrence
  headerRows : List SourceRows.Row
  headerRowsRead : headerRows = entry.body.definition.rows
  helperRows : List SourceRows.Row
  helpersRead : SourceDutySlots.Computed
    (NaturalRows.bindings sources state.owner state.prepared.helpers state.prepared.bindings) helperRows

def Original.rows {sources catalogue state} (original : @Original sources catalogue state) : List SourceRows.Row :=
  [(state.owner,state.prepared.original.envelope.source)] ++ original.headerRows ++ original.helperRows

private def readOriginal {sources} (catalogue : GenericCatalogue.Checked sources)
    (state : GenericLexicalNatural.SomeEnvironment sources) : WorkM (Original catalogue state) := do
  let entry ← NaturalAffine.witness
    (GenericCatalogue.lookup catalogue.toRuntimeChecked state.prepared.original.envelope)
  let canonical := entry.val.body
  let written := state.prepared.original.envelope
  exactWork (Exact.charge (32*(canonical.owner.utf8ByteSize+canonical.name.utf8ByteSize+
    state.owner.utf8ByteSize+state.name.utf8ByteSize+canonical.definition.original.envelope.source.utf8ByteSize+
    written.source.utf8ByteSize+tokenFields canonical.definition.original.envelope.occurrence.header+
    tokenFields canonical.definition.original.envelope.occurrence.body+tokenFields written.occurrence.header+
    tokenFields written.occurrence.body+1)))
  if same : canonical.owner = state.owner ∧ canonical.name = state.name ∧
      canonical.definition.original.envelope.source = written.source ∧
      canonical.definition.original.envelope.declaration = written.declaration ∧
      canonical.definition.original.envelope.occurrence = written.occurrence then
    let helpers ← NaturalAffine.witness
      (NaturalRows.bindings sources state.owner state.prepared.helpers state.prepared.bindings)
    return ⟨entry.val,by with_reducible exact entry.property,
      same.1,same.2.1,same.2.2.1,same.2.2.2.1,same.2.2.2.2,canonical.definition.rows,rfl,
      helpers.val,by with_reducible exact helpers.property⟩
  else throw .request

/-- Only the original initial scope is supported here. No value is selected
for an unused containing formal, and no alias or branch guard is reconstructed
from a convenient closed provider. The pure seed equations retain full types.
-/
structure Site {sources} (catalogue : GenericCatalogue.Checked sources)
    (state : GenericLexicalNatural.SomeEnvironment sources) (scope : List String)
    (tokens : List LocatedToken) : Type where
  original : Original catalogue state
  patterns : List (List String)
  patternsRead : ParameterPatterns.read original.entry.body.definition.original.envelope = .ok patterns
  initial : GenericValues.Environment
  seeded : GenericValues.seed patterns original.entry.body.definition.parameters = .ok initial
  initialScope : scope = original.entry.body.definition.original.header.formals.map (·.name) ++ initial.map (·.name)
  unguarded : state.environment.guards.isEmpty = true
  bytes : LocatedFacts.OrderedSlices state.prepared.original.envelope.source.toUTF8
    state.prepared.original.envelope.occurrence.openBrace.span.endByte tokens
  inside : tokens.all (fun token => token.span.endByte ≤
    state.prepared.original.envelope.occurrence.closeBrace.span.startByte) = true

private def readSite {sources} (catalogue : GenericCatalogue.Checked sources)
    (state : GenericLexicalNatural.SomeEnvironment sources) (scope : List String)
    (tokens : List LocatedToken) : WorkM (Site catalogue state scope tokens) := do
  let original ← readOriginal catalogue state
  exactWork (Exact.charge (8*(catalogue.records.length+1)))
  let definition := original.entry.body.definition
  -- Seeding traverses symbolic value spines, not the nominal source text
  -- stored inside their basis atoms. Pattern/name comparisons include every
  -- parameter and captured name; the header parser has its own quadratic term.
  exactWork (Exact.charge (32*(tokenFields tokens+tokenFields definition.original.envelope.occurrence.header+
    nameFields scope+(definition.parameters.map List.length).sum+
    definition.original.header.formals.length+state.environment.guards.length+1)*
      (scope.length+definition.parameters.length+1)+
    16*(definition.original.envelope.occurrence.header.length+1)^2))
  match patternsRead : ParameterPatterns.read definition.original.envelope with
  | .error _ => throw .request
  | .ok patterns =>
    match seeded : GenericValues.seed patterns definition.parameters with
    | .error _ => throw .request
    | .ok initial =>
      if initialScope : scope = definition.original.header.formals.map (·.name) ++ initial.map (·.name) then
        if unguarded : state.environment.guards.isEmpty = true then
          let written := state.prepared.original.envelope
          if bytes : LocatedFacts.checkOrdered written.source.toUTF8 written.occurrence.openBrace.span.endByte tokens = true then
            if inside : tokens.all (fun token => token.span.endByte ≤ written.occurrence.closeBrace.span.startByte) = true then
              return ⟨original,patterns,patternsRead,initial,seeded,initialScope,unguarded,
                LocatedFacts.checkOrdered_sound _ _ _ bytes,inside⟩
            else throw .request
          else throw .request
        else throw .request
      else throw .request

private def operationOnly (formal : StaticHeaders.Formal) : Bool :=
  match formal.kind with | .operation _ => true | _ => false

/-- Replay one real original application in its own captured caller scope.
The existing ApplicationSource/Transport retains the simultaneous Op insertion;
this value authenticates its source query and relevant headers, not new actuals.
-/
structure Application {sources} (catalogue : GenericCatalogue.Checked sources)
    (application : ApplicationSource sources) : Type where
  caller : Site catalogue application.state application.scope application.tokens
  noBases : application.basisActuals.isEmpty = true
  noNaturals : application.naturalActuals.isEmpty = true
  singleOperation : application.target.header.formals.length ≤ 1
  operationKinds : application.target.header.formals.all operationOnly = true
  candidate : CallName.Checked sources application.state.owner application.scope application.written.callee
  queried : SourceDutySlots.Computed
    (CallName.read sources application.state.owner application.scope application.written.callee) candidate
  resolution : Resolved
  resolved : CallName.candidateResolution candidate = some resolution
  owner : resolution.moduleName = application.owner
  name : resolution.declaration.name = application.name
  source : resolution.source = application.target.envelope.source
  declaration : resolution.declaration = application.target.envelope.declaration
  target : GenericCatalogue.Entry catalogue.toRuntimeChecked application.target.envelope
  targetRead : SourceDutySlots.Computed
    (GenericCatalogue.lookup catalogue.toRuntimeChecked application.target.envelope) target
  targetRows : List SourceRows.Row
  targetRowsRead : targetRows = target.body.definition.rows
  helperRows : List SourceRows.Row
  helpersRead : SourceDutySlots.Computed
    (NaturalRows.bindings sources application.owner application.transfer.callee.helpers
      application.transfer.callee.bindings) helperRows

def Application.rows {sources catalogue application} (checked : @Application sources catalogue application) :
    List SourceRows.Row :=
  checked.caller.original.rows ++ CallName.sourceRows checked.candidate ++
    [(application.owner,application.target.envelope.source)] ++ checked.targetRows ++ checked.helperRows

private def readApplication {sources} (catalogue : GenericCatalogue.Checked sources)
    (application : ApplicationSource sources) : WorkM (Application catalogue application) := do
  let caller ← readSite catalogue application.state application.scope application.tokens
  exactWork (Exact.charge (16*(application.basisActuals.length+application.naturalActuals.length+
    application.target.header.formals.length+1)))
  if noBases : application.basisActuals.isEmpty = true then
    if noNaturals : application.naturalActuals.isEmpty = true then
      if singleOperation : application.target.header.formals.length ≤ 1 then
        if operationKinds : application.target.header.formals.all operationOnly = true then
          let candidate ← NaturalAffine.witness
            (CallName.read sources application.state.owner application.scope application.written.callee)
          match resolved : CallName.candidateResolution candidate.val with
          | none => throw .request
          | some resolution =>
            exactWork (Exact.charge (32*(resolution.moduleName.utf8ByteSize+resolution.declaration.name.utf8ByteSize+
              application.owner.utf8ByteSize+application.name.utf8ByteSize+resolution.source.utf8ByteSize+
              application.target.envelope.source.utf8ByteSize+tokenFields application.target.envelope.occurrence.header+1)))
            if same : resolution.moduleName = application.owner ∧ resolution.declaration.name = application.name ∧
                resolution.source = application.target.envelope.source ∧ resolution.declaration = application.target.envelope.declaration then
              let target ← NaturalAffine.witness
                (GenericCatalogue.lookup catalogue.toRuntimeChecked application.target.envelope)
              let helpers ← NaturalAffine.witness (NaturalRows.bindings sources application.owner
                application.transfer.callee.helpers application.transfer.callee.bindings)
              return ⟨caller,noBases,noNaturals,singleOperation,operationKinds,candidate.val,
                by with_reducible exact candidate.property,resolution,resolved,
                same.1,same.2.1,same.2.2.1,same.2.2.2,target.val,by with_reducible exact target.property,
                target.val.body.definition.rows,rfl,
                helpers.val,by with_reducible exact helpers.property⟩
            else throw .request
        else throw .request
      else throw .request
    else throw .request
  else throw .request

inductive Applications {sources} (catalogue : GenericCatalogue.Checked sources) :
    List (ApplicationSource sources) → Type where
  | nil : Applications catalogue []
  | cons {application rest} (checked : Application catalogue application)
      (tail : Applications catalogue rest) : Applications catalogue (application :: rest)

def Applications.rows {sources catalogue applications} :
    @Applications sources catalogue applications → List SourceRows.Row
  | .nil => []
  | .cons checked tail => checked.rows ++ tail.rows

private def readApplications {sources} (catalogue : GenericCatalogue.Checked sources) :
    (applications : List (ApplicationSource sources)) → WorkM (Applications catalogue applications)
  | [] => pure .nil
  | application :: rest => do
    exactWork (Exact.charge 8)
    let checked ← readApplication catalogue application
    let tail ← readApplications catalogue rest
    return .cons checked tail

structure Checked {sources catalogue record invocation demand view}
    (provider : @SourceDutySlots.Provider sources catalogue record invocation demand view) : Type where
  supplier : Site catalogue provider.supplier.origin.state provider.supplier.origin.scope provider.supplier.origin.tokens
  supplyingRoot : supplier.original.entry.index.val = invocation.id.root
  duty : Original catalogue demand.source.original.origin.state
  dutyRecord : duty.entry.index.val = record.val
  -- This is the exact already executed substitution chain, including every
  -- original insertion of the unchanged caller closure and supplier Origins.
  transport : Transport invocation.applications.reverse
    ⟨demand.source.original.subject,demand.source.original.suppliers⟩ demand.transported.subject
  sameTransport : transport = demand.transported.receipt
  calls : Applications catalogue invocation.applications
  noGroup : demand.source.original.runtimeApplication.isNone = true
  bare : (match provider.written with | .name _ => true | .application _ => false) = true
  noBases : provider.bases = []
  noNaturals : provider.naturals = []
  noOperations : provider.operations = []
  noActuals : provider.signature.staticArguments = {}
  nongeneric : provider.signature.original.parsedHeader.staticTokens.isNone = true
  singleton : provider.closed.data.description.nodes = [.provider provider.owner provider.name [] [] []]
  rootNode : provider.closed.data.description.root = 0

def Checked.rows {sources catalogue record invocation demand view provider}
    (checked : @Checked sources catalogue record invocation demand view provider) : List SourceRows.Row :=
  checked.supplier.original.rows ++ checked.duty.rows ++ checked.calls.rows

/-- Explicit bounded bare-source branch. No failed strict preparation is caught
or retried. In particular f[] is not a bare name, even with no closed actuals.
-/
def read {sources catalogue record invocation demand view}
    (provider : @SourceDutySlots.Provider sources catalogue record invocation demand view) : WorkM (Checked provider) := do
  let supplier ← readSite catalogue provider.supplier.origin.state provider.supplier.origin.scope provider.supplier.origin.tokens
  let duty ← readOriginal catalogue demand.source.original.origin.state
  exactWork (Exact.charge (32*(provider.owner.utf8ByteSize+provider.name.utf8ByteSize+
    invocation.depth+provider.closed.data.description.nodes.length+
    provider.signature.original.occurrence.header.length+provider.signature.staticArguments.bases.length+
    provider.signature.staticArguments.naturals.length+provider.signature.staticArguments.operations.length+1)))
  if supplyingRoot : supplier.original.entry.index.val = invocation.id.root then
    if dutyRecord : duty.entry.index.val = record.val then
      if noGroup : demand.source.original.runtimeApplication.isNone = true then
        if bare : (match provider.written with | .name _ => true | .application _ => false) = true then
          if leaf : provider.bases = [] ∧ provider.naturals = [] ∧ provider.operations = [] ∧
              provider.signature.staticArguments = {} ∧ provider.signature.original.parsedHeader.staticTokens.isNone = true ∧
              provider.closed.data.description.nodes = [.provider provider.owner provider.name [] [] []] ∧
              provider.closed.data.description.root = 0 then
            exactWork (Exact.charge (16*(invocation.depth+1)))
            let calls ← readApplications catalogue invocation.applications
            return ⟨supplier,supplyingRoot,duty,dutyRecord,demand.transported.receipt,rfl,calls,
              noGroup,bare,leaf.1,leaf.2.1,leaf.2.2.1,leaf.2.2.2.1,leaf.2.2.2.2.1,leaf.2.2.2.2.2.1,leaf.2.2.2.2.2.2⟩
          else throw .request
        else throw .request
      else throw .request
    else throw .request
  else throw .request

end QleisliKernel.Qirf.SourceDutyProviderBare
