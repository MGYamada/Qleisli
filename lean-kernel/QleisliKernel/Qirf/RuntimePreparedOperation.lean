import QleisliKernel.Qirf.RuntimeBodyDiscovery
import QleisliKernel.Qirf.SourceMeaningAction

/-! Non-accepting discovery of one actual original operation application.
The complete shared source preparation keeps all canonical pending duties.
Every operation child-edge occurrence retains its real provider header and
each local Meaning request prepares its complete original Meaning graph.
Reference contexts are a separate ordered internal argument, not additional
wire fields or a reinterpretation of the operation implementation contexts.
No root is checked here. Caller lowering, demanded paths, full Meaning/subject
equations and complete catalogue-duty correspondence remain mandatory.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimePreparedOperation
open QleisliKernel Finite SourceTypes
abbrev Context := RuntimeContextRequest.Context
abbrev Request := RuntimeProviderHeader.Request

structure Provider (artifact : Artifact) {context description}
    (graph : StaticOperation.CheckedGraph artifact.sources context description) (index : Nat) where
  request : Request
  header : RuntimeProviderHeader.Header artifact graph index request
  original : RuntimeInterval.Computed (RuntimeProviderHeader.read artifact graph index request) header
  discovery : RuntimeBodyDiscovery.Discovery
  discovered : RuntimeInterval.Computed (RuntimeBodyDiscovery.visit artifact 128
    header.original.body.checked.signature header.original.body.checked.events
    header.original.body.checked.summary.staticRows request.2 true) discovery

def Provider.rows {artifact context description graph index}
    (provider : @Provider artifact context description graph index) : List SourceRows.Row :=
  provider.header.rows ++ provider.discovery.rows

def Provider.roots {artifact context description graph index}
    (provider : @Provider artifact context description graph index) : List Nat :=
  provider.header.roots ++ provider.discovery.roots

private def readProvider (artifact : Artifact) {context description}
    (graph : StaticOperation.CheckedGraph artifact.sources context description) (index : Nat) (request : Request) :
    WorkM (Provider artifact graph index) := do
  let header ← NaturalAffine.witness (RuntimeProviderHeader.read artifact graph index request)
  let body := header.val.original.body.checked
  let discovery ← NaturalAffine.witness (RuntimeBodyDiscovery.visit artifact 128 body.signature body.events
    body.summary.staticRows request.2 true)
  return ⟨request,header.val,by with_reducible exact header.property,
    discovery.val,by with_reducible exact discovery.property⟩

/-- This remains an outstanding subject equation. Preparing every original
reference does not prove the local subject equals the requested Meaning. -/
structure Requirement (artifact : Artifact) (catalogue : GenericCatalogue.Checked artifact.sources)
    (result : StaticOperation.Result artifact.sources) where
  index : Fin result.requirements.length
  subject : Nat
  argument : Option Nat
  request : SourceMeaning.Request artifact.sources
  original : result.requirements[index.val]'index.isLt = ⟨subject,argument,request⟩
  references : List Request
  meaning : SourceMeaningAction.Prepared artifact catalogue request.meaning
  prepared : RuntimeInterval.Computed
    (SourceMeaningAction.prepare artifact catalogue request.meaning references) meaning

private def readRequirements (artifact : Artifact) (catalogue : GenericCatalogue.Checked artifact.sources)
    (result : StaticOperation.Result artifact.sources) (references : List (List Request)) :
    WorkM (List (Requirement artifact catalogue result) × List (List Request)) := do
  exactWork (Exact.charge (16*(result.requirements.length+references.length+1)^2))
  let (rev,remaining) ← (List.finRange result.requirements.length).foldlM (fun (rev,remaining) index => do
    let requests :: remaining := remaining | throw .request
    let original := result.requirements[index.val]'index.isLt
    let request := original.request
    let meaning ← NaturalAffine.witness (SourceMeaningAction.prepare artifact catalogue request.meaning requests)
    let entry : Requirement artifact catalogue result :=
      ⟨index,original.subject,original.argument,request,rfl,requests,meaning.val,
        by with_reducible exact meaning.property⟩
    pure (entry::rev,remaining)) ([],references)
  return (rev.reverse,remaining)

structure Occurrence (artifact : Artifact) (catalogue : GenericCatalogue.Checked artifact.sources)
    {context description} (graph : StaticOperation.CheckedGraph artifact.sources context description)
    (order : List Nat) where
  ordinal : Fin order.length
  index : Nat
  atOrdinal : order[ordinal.val]'ordinal.isLt = index
  result : StaticOperation.Result artifact.sources
  selected : graph.results[index]? = some result
  provider : Option (Provider artifact graph index)
  providerPresent : provider.isSome = result.provider.isSome
  requirements : List (Requirement artifact catalogue result)
  every : requirements.map (·.index) = List.finRange result.requirements.length

def Occurrence.rows {artifact catalogue context description graph order}
    (occurrence : @Occurrence artifact catalogue context description graph order) : List SourceRows.Row :=
  occurrence.provider.toList.flatMap Provider.rows ++ occurrence.requirements.flatMap (·.meaning.rows)

def Occurrence.roots {artifact catalogue context description graph order}
    (occurrence : @Occurrence artifact catalogue context description graph order) : List Nat :=
  occurrence.provider.toList.flatMap Provider.roots ++ occurrence.requirements.flatMap (·.meaning.roots)

private def collect (artifact : Artifact) (catalogue : GenericCatalogue.Checked artifact.sources)
    {context description} (graph : StaticOperation.CheckedGraph artifact.sources context description)
    (order : List Nat) (implementations : List Request) (references : List (List Request)) :
    WorkM (List (Occurrence artifact catalogue graph order)) := do
  -- These actual linked-list node/result lookups are quadratic in the bounded
  -- occurrence list. Source/Meaning/header readers retain their own charges.
  exactWork (Exact.charge (16*(order.length+description.nodes.length+graph.results.length+
    implementations.length+references.length+1)^2))
  let (rev,implementations,references) ← (List.finRange order.length).foldlM
    (fun (rev,implementations,references) ordinal => do
      let index := order[ordinal.val]'ordinal.isLt
      match selected : graph.results[index]? with
      | none => throw .request
      | some result =>
        let providerAction : WorkM (Option (Provider artifact graph index) × List Request) :=
          match result.provider with
          | none => pure (none,implementations)
          | some _ => do
            let request :: remaining := implementations | throw .request
            pure (some (← readProvider artifact graph index request),remaining)
        let (provider,implementations) ← providerAction
        if providerPresent : provider.isSome = result.provider.isSome then
          let (requirements,references) ← readRequirements artifact catalogue result references
          if every : requirements.map (·.index) = List.finRange result.requirements.length then
            let entry : Occurrence artifact catalogue graph order :=
              ⟨ordinal,index,rfl,result,selected,provider,providerPresent,requirements,every⟩
            pure (entry::rev,implementations,references)
          else throw .request
        else throw .request) ([],implementations,references)
  guard (implementations.isEmpty && references.isEmpty) .request
  return rev.reverse

/-- Graph-only preparation is shared by a genuine runtime operation and an
indexed original coherent arm. The graph itself carries its source/supplier
receipts; this value does not invent an enclosing source occurrence. -/
structure GraphPrepared (artifact : Artifact) (catalogue : GenericCatalogue.Checked artifact.sources)
    {context description} (graph : StaticOperation.CheckedGraph artifact.sources context description)
    (implementations : List Request) (references : List (List Request)) where
  order : List Nat
  ordered : RuntimeInterval.Computed (StaticOperation.readOccurrences description) order
  occurrences : List (Occurrence artifact catalogue graph order)
  collected : RuntimeInterval.Computed (collect artifact catalogue graph order implementations references) occurrences
  every : occurrences.map (·.ordinal) = List.finRange order.length

def GraphPrepared.rows {artifact catalogue context description graph implementations references}
    (prepared : @GraphPrepared artifact catalogue context description graph implementations references) : List SourceRows.Row :=
  graph.sourceRows ++ prepared.occurrences.flatMap Occurrence.rows

def GraphPrepared.roots {artifact catalogue context description graph implementations references}
    (prepared : @GraphPrepared artifact catalogue context description graph implementations references) : List Nat :=
  prepared.occurrences.flatMap Occurrence.roots

def prepareGraph (artifact : Artifact) (catalogue : GenericCatalogue.Checked artifact.sources)
    {context description} (graph : StaticOperation.CheckedGraph artifact.sources context description)
    (implementations : List Request) (references : List (List Request)) :
    WorkM (GraphPrepared artifact catalogue graph implementations references) := do
  let order ← NaturalAffine.witness (StaticOperation.readOccurrences description)
  let occurrences ← NaturalAffine.witness (collect artifact catalogue graph order.val implementations references)
  if every : occurrences.val.map (·.ordinal) = List.finRange order.val.length then
    return ⟨order.val,by with_reducible exact order.property,occurrences.val,
      by with_reducible exact occurrences.property,every⟩
  else throw .request

structure Prepared (artifact : Artifact) {owner name arguments}
    (source : RuntimeBodyDiscovery.PreparedSource artifact owner name arguments) (request : Context)
    (references : List (List Request)) where
  event : SourceOperationApplication.Event artifact.sources owner
  original : source.body.checked.events = [.operation event]
  noRootActuals : source.signature.arguments.operations.isEmpty = true ∧
    source.signature.operations.actuals.isEmpty = true ∧ source.signature.operations.hasMeaningRequirements = false
  position : SourceSequence.Position
  positions : request.positions = [position]
  callPosition : SourceSequence.Position
  implementation : Context
  calls : request.calls = [(callPosition,implementation)]
  samePosition : callPosition = position
  offset : position.offset = event.call.calleeOffset
  outerEmpty : request.sites.isEmpty = true ∧ request.branches.isEmpty = true ∧ request.bodies.isEmpty = true
  childEmpty : implementation.positions.isEmpty = true ∧ implementation.sites.isEmpty = true ∧
    implementation.calls.isEmpty = true ∧ implementation.branches.isEmpty = true
  order : List Nat
  ordered : RuntimeInterval.Computed (StaticOperation.readOccurrences event.operation.description) order
  occurrences : List (Occurrence artifact source.catalogue event.operation.graph order)
  collected : RuntimeInterval.Computed
    (collect artifact source.catalogue event.operation.graph order implementation.bodies references) occurrences
  every : occurrences.map (·.ordinal) = List.finRange order.length
  relevance : SourceRows.Retained
    ([(owner,source.body.checked.signature.original.source)] ++ source.signature.sourceRows ++
      source.body.checked.summary.staticRows ++ event.operation.rows ++ event.naturals.sourceRows ++
      event.operation.graph.sourceRows ++ occurrences.flatMap Occurrence.rows)

def Prepared.rows {artifact owner name arguments source request references}
    (prepared : @Prepared artifact owner name arguments source request references) : List SourceRows.Row := prepared.relevance.rows

def Prepared.roots {artifact owner name arguments source request references}
    (prepared : @Prepared artifact owner name arguments source request references) : List Nat :=
  (artifact.root :: prepared.occurrences.flatMap Occurrence.roots).eraseDups

/-- Discover the concrete singleton operation case from the exact shared Body.
The separate reference lists are consumed once per original local requirement
in child-edge postorder. Unused/zero children are retained by readOccurrences.
Other source shapes/root actual prefixes refuse this bounded preparation.
-/
def prepare (artifact : Artifact) {owner name arguments}
    (source : RuntimeBodyDiscovery.PreparedSource artifact owner name arguments) (request : Context)
    (references : List (List Request)) : WorkM (Prepared artifact source request references) := do
  exactWork (Exact.charge (32*(source.body.checked.events.length+request.positions.length+
    request.calls.length+request.sites.length+request.branches.length+request.bodies.length+1)))
  if noRootActuals : source.signature.arguments.operations.isEmpty = true ∧
      source.signature.operations.actuals.isEmpty = true ∧ source.signature.operations.hasMeaningRequirements = false then
    match original : source.body.checked.events with
    | [.operation event] =>
      match positions : request.positions,calls : request.calls with
      | [position],[(callPosition,implementation)] =>
        if same : callPosition = position ∧ position.offset = event.call.calleeOffset then
          if empty : request.sites.isEmpty = true ∧ request.branches.isEmpty = true ∧ request.bodies.isEmpty = true ∧
              implementation.positions.isEmpty = true ∧ implementation.sites.isEmpty = true ∧
              implementation.calls.isEmpty = true ∧ implementation.branches.isEmpty = true then
            let order ← NaturalAffine.witness (StaticOperation.readOccurrences event.operation.description)
            let occurrences ← NaturalAffine.witness
              (collect artifact source.catalogue event.operation.graph order.val implementation.bodies references)
            if every : occurrences.val.map (·.ordinal) = List.finRange order.val.length then
              let relevance ← SourceRows.read
                ([(owner,source.body.checked.signature.original.source)] ++ source.signature.sourceRows ++
                  source.body.checked.summary.staticRows ++ event.operation.rows ++ event.naturals.sourceRows ++
                  event.operation.graph.sourceRows ++ occurrences.val.flatMap Occurrence.rows)
              return ⟨event,original,noRootActuals,position,positions,callPosition,implementation,calls,same.1,same.2,
                ⟨empty.1,empty.2.1,empty.2.2.1⟩,
                ⟨empty.2.2.2.1,empty.2.2.2.2.1,empty.2.2.2.2.2.1,empty.2.2.2.2.2.2⟩,
                order.val,by with_reducible exact order.property,occurrences.val,
                by with_reducible exact occurrences.property,every,relevance⟩
            else throw .request
          else throw .request
        else throw .request
      | _,_ => throw .request
    | _ => throw .request
  else throw .request

/-- Reuse the actual operation preparation without rereading any header,
source body, occurrence or Meaning graph. This projection changes no work. -/
def Prepared.asGraph {artifact owner name arguments source request references}
    (prepared : @Prepared artifact owner name arguments source request references) :
    GraphPrepared artifact source.catalogue prepared.event.operation.graph prepared.implementation.bodies references :=
  ⟨prepared.order,prepared.ordered,prepared.occurrences,prepared.collected,prepared.every⟩

private def directShape (description : OperationDescription.Description) : Bool :=
  description.root == 1 && match description.nodes with
    | [.provider ..,.requested child _ _] => child == 0
    | _ => false

/-- A supported consumption relation selects the actual child of the written
request. Equal names, matrices or widths cannot select a different provider.
The general preparation above remains usable data for other shapes; they do
not acquire this bounded direct-provider continuation by coincidence. -/
structure GraphDirect {artifact catalogue context description graph implementations references}
    (prepared : @GraphPrepared artifact catalogue context description graph implementations references) where
  providerOccurrence : Occurrence artifact catalogue graph prepared.order
  meaningOccurrence : Occurrence artifact catalogue graph prepared.order
  original : prepared.occurrences = [providerOccurrence,meaningOccurrence]
  provider : Provider artifact graph providerOccurrence.index
  present : providerOccurrence.provider = some provider
  requirement : Requirement artifact catalogue meaningOccurrence.result
  required : meaningOccurrence.requirements = [requirement]
  shape : directShape description = true
  providerIndex : providerOccurrence.index = 0
  meaningIndex : meaningOccurrence.index = 1
  subject : requirement.subject = providerOccurrence.index
  noEarlierMeaning : providerOccurrence.requirements.isEmpty = true
  noOtherProvider : meaningOccurrence.provider.isNone = true

def readGraphDirect {artifact catalogue context description graph implementations references}
    (prepared : @GraphPrepared artifact catalogue context description graph implementations references) : WorkM (GraphDirect prepared) := do
  exactWork (Exact.charge (16*(description.nodes.length+prepared.occurrences.length+1)))
  match original : prepared.occurrences with
  | [providerOccurrence,meaningOccurrence] =>
    match present : providerOccurrence.provider,required : meaningOccurrence.requirements with
    | some provider,[requirement] =>
      if supported : directShape description = true ∧ providerOccurrence.index = 0 ∧
          meaningOccurrence.index = 1 ∧ requirement.subject = providerOccurrence.index ∧
          providerOccurrence.requirements.isEmpty = true ∧ meaningOccurrence.provider.isNone = true then
        return ⟨providerOccurrence,meaningOccurrence,original,provider,present,requirement,required,
          supported.1,supported.2.1,supported.2.2.1,supported.2.2.2.1,supported.2.2.2.2.1,supported.2.2.2.2.2⟩
      else throw .request
    | _,_ => throw .request
  | _ => throw .request

abbrev Direct {artifact owner name arguments source request references}
    (prepared : @Prepared artifact owner name arguments source request references) := GraphDirect prepared.asGraph

def readDirect {artifact owner name arguments source request references}
    (prepared : @Prepared artifact owner name arguments source request references) : WorkM (Direct prepared) :=
  readGraphDirect prepared.asGraph

/-- The caller, every forward provider and every original Meaning reference
are discovered before this single actual graph computation. No provider gets
an independent root, and all rows remain derived from this preparation. -/
structure Fresh {artifact owner name arguments source request references}
    (prepared : @Prepared artifact owner name arguments source request references) (order : Array Nat) where
  root : Validity.Root
  checked : RuntimeInterval.Computed
    (Validity.checkRootFromRoots artifact order prepared.rows prepared.roots) root

def prepareRoot {artifact owner name arguments source request references}
    (prepared : @Prepared artifact owner name arguments source request references) (order : Array Nat) :
    WorkM (Fresh prepared order) := do
  let root ← NaturalAffine.witness (Validity.checkRootFromRoots artifact order prepared.rows prepared.roots)
  return ⟨root.val,by with_reducible exact root.property⟩

/-- A same-root direct-provider/M equation receipt. The original canonical
queue is still retained on source.pending; this is not complete catalogue
coverage or a caller IR derivation, and supplies no execution authority. -/
structure GraphChecked {artifact catalogue context description graph implementations references}
    (prepared : @GraphPrepared artifact catalogue context description graph implementations references)
    (root : Validity.Root) (requested : StaticOperation.Paths) where
  direct : GraphDirect prepared
  directRead : RuntimeInterval.Computed (readGraphDirect prepared) direct
  access : OperationAccess.CheckedOccurrences graph requested
  accessRead : RuntimeInterval.Computed
    (OperationAccess.checkOccurrences graph requested) access
  demandedProvider : StaticOperation.Provider artifact.sources
  demand : StaticOperation.Paths
  originalDemand : access.providers = [(direct.providerOccurrence.index,demandedProvider,demand)]
  subject : RuntimeProviderAction.Checked direct.provider.header root demand
  subjectRead : RuntimeInterval.Computed (RuntimeProviderAction.read direct.provider.header root demand) subject
  specification : SourceMeaningAction.Checked direct.requirement.meaning root
  specificationRead : RuntimeInterval.Computed (SourceMeaningAction.read direct.requirement.meaning root) specification
  equation : SourceMeaningAction.ProviderEquation subject specification
  compared : RuntimeInterval.Computed (SourceMeaningAction.compareProvider subject specification) (⟨equation⟩ : PLift _)

def readGraph {artifact catalogue context description graph implementations references}
    (prepared : @GraphPrepared artifact catalogue context description graph implementations references)
    (root : Validity.Root) (requested : StaticOperation.Paths) : WorkM (GraphChecked prepared root requested) := do
  let direct ← NaturalAffine.witness (readGraphDirect prepared)
  let access ← NaturalAffine.witness
    (OperationAccess.checkOccurrences graph requested)
  match demands : access.val.providers with
  | [(index,demandedProvider,demand)] =>
    if same : index = direct.val.providerOccurrence.index then
      let subject ← NaturalAffine.witness (RuntimeProviderAction.read direct.val.provider.header root demand)
      let specification ← NaturalAffine.witness (SourceMeaningAction.read direct.val.requirement.meaning root)
      let equation ← NaturalAffine.witness (SourceMeaningAction.compareProvider subject.val specification.val)
      return ⟨direct.val,by with_reducible exact direct.property,
        access.val,by with_reducible exact access.property,demandedProvider,demand,
        by simpa only [same] using demands,subject.val,by with_reducible exact subject.property,
        specification.val,by with_reducible exact specification.property,equation.val.down,
        by with_reducible exact equation.property⟩
    else throw .request
  | _ => throw .request

private def plainShape (description : OperationDescription.Description) : Bool :=
  description.root == 0 && match description.nodes with | [.provider ..] => true | _ => false

/-- Plain providers use the same actual graph/header/body path without an
invented Meaning assertion. Their absence of local requests is checked. -/
structure GraphPlain {artifact catalogue context description graph implementations references}
    (prepared : @GraphPrepared artifact catalogue context description graph implementations references) where
  occurrence : Occurrence artifact catalogue graph prepared.order
  original : prepared.occurrences = [occurrence]
  provider : Provider artifact graph occurrence.index
  present : occurrence.provider = some provider
  shape : plainShape description = true
  index : occurrence.index = 0
  noRequirements : occurrence.requirements.isEmpty = true
  noMeaning : graph.hasMeaningRequirements = false

def readGraphPlain {artifact catalogue context description graph implementations references}
    (prepared : @GraphPrepared artifact catalogue context description graph implementations references) :
    WorkM (GraphPlain prepared) := do
  exactWork (Exact.charge (16*(description.nodes.length+prepared.occurrences.length+1)))
  match original : prepared.occurrences with
  | [occurrence] =>
    match present : occurrence.provider with
    | some provider =>
      if supported : plainShape description = true ∧ occurrence.index = 0 ∧
          occurrence.requirements.isEmpty = true ∧ graph.hasMeaningRequirements = false then
        return ⟨occurrence,original,provider,present,supported.1,supported.2.1,supported.2.2.1,supported.2.2.2⟩
      else throw .request
    | none => throw .request
  | _ => throw .request

structure PlainChecked {artifact catalogue context description graph implementations references}
    (prepared : @GraphPrepared artifact catalogue context description graph implementations references)
    (root : Validity.Root) (requested : StaticOperation.Paths) where
  direct : GraphPlain prepared
  directRead : RuntimeInterval.Computed (readGraphPlain prepared) direct
  access : OperationAccess.CheckedOccurrences graph requested
  accessRead : RuntimeInterval.Computed (OperationAccess.checkOccurrences graph requested) access
  demandedProvider : StaticOperation.Provider artifact.sources
  demand : StaticOperation.Paths
  originalDemand : access.providers = [(direct.occurrence.index,demandedProvider,demand)]
  subject : RuntimeProviderAction.Checked direct.provider.header root demand
  subjectRead : RuntimeInterval.Computed (RuntimeProviderAction.read direct.provider.header root demand) subject

def readPlain {artifact catalogue context description graph implementations references}
    (prepared : @GraphPrepared artifact catalogue context description graph implementations references)
    (root : Validity.Root) (requested : StaticOperation.Paths) : WorkM (PlainChecked prepared root requested) := do
  let direct ← NaturalAffine.witness (readGraphPlain prepared)
  let access ← NaturalAffine.witness (OperationAccess.checkOccurrences graph requested)
  match demands : access.val.providers with
  | [(index,demandedProvider,demand)] =>
    if same : index = direct.val.occurrence.index then
      let subject ← NaturalAffine.witness (RuntimeProviderAction.read direct.val.provider.header root demand)
      return ⟨direct.val,by with_reducible exact direct.property,access.val,by with_reducible exact access.property,
        demandedProvider,demand,by simpa only [same] using demands,subject.val,by with_reducible exact subject.property⟩
    else throw .request
  | _ => throw .request

abbrev Checked {artifact owner name arguments source request references}
    (prepared : @Prepared artifact owner name arguments source request references) (root : Validity.Root) :=
  GraphChecked prepared.asGraph root OperationAccess.applicable

def read {artifact owner name arguments source request references}
    (prepared : @Prepared artifact owner name arguments source request references) (root : Validity.Root) :
    WorkM (Checked prepared root) := readGraph prepared.asGraph root OperationAccess.applicable

end QleisliKernel.Qirf.RuntimePreparedOperation
