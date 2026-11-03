import QleisliKernel.Qirf.RuntimeDiscoveryScope

/-! Discover every original runtime body before the one fresh graph check.
The traversal follows actual source events and supplied context occurrences;
provider bodies retain their original supplier receipts. A discovery result is
not source/IR acceptance: local action, ordinary history, Meaning and access
continuations must still be checked under the final root.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeBodyDiscovery
open QleisliKernel QleisliKernel.Finite QleisliKernel.SourceTypes
open SourceRuntimeValues

/-- One source traversal owns every original event and context cursor. The
fixed enclosing reader chooses strict graph discovery or a typed continuation;
a failed continuation never retries through another reader. -/
def visitUsing (artifact : Artifact) (operationMode : OperationMode artifact) : Nat → {owner name : String} →
    SourceRuntimeContext.Signature artifact.sources owner name →
    List (SourceRuntimeContext.Event artifact.sources owner) → List (String × String) →
    Context → Bool → WorkM (Discovery × List operationMode.Receipt) :=
  Nat.rec (fun {_ _} _ _ _ _ _ => throw .limit)
    (fun _ next {_ _} signature events staticRows request prefixRequired => do
      guard (request.positions.length ≤ 4096 && request.sites.length ≤ 128 &&
        request.calls.length ≤ 4096 && request.branches.length ≤ 4096 && request.bodies.length ≤ 4096 &&
        request.references.length ≤ 4096) .limit
      exactWork (Exact.charge (32*(events.length+request.positions.length+request.sites.length+
        request.calls.length+request.branches.length+request.bodies.length+request.references.length+1)^2))
      guard (request.positions.map (·.offset) == events.map SourceRuntimeContext.Event.offset) .request
      let readOperation {context description}
          (graph : StaticOperation.CheckedGraph artifact.sources context description)
          (requested : StaticOperation.Paths) (bodies : List BodyRequest)
          (references : List (List (List BodyRequest))) (explicit : Bool) :
          WorkM (Discovery × List BodyRequest × List (List (List BodyRequest)) × List operationMode.Receipt) := do
        let occurrences ← StaticOperation.readOccurrences description
        let indices := RuntimeProviderHeaders.providerIndices description occurrences
        guard (indices.length ≤ bodies.length) .request
        let implementations := bodies.take indices.length
        let (group,references) ← operationMode.takeReferences explicit references
        match operationMode with
        | .extended continuation =>
          let call : RuntimeGraphOperation.Request artifact := ⟨context,description,graph,requested,implementations,group⟩
          let checked ← NaturalAffine.witness (continuation.read call)
          let receipt : RuntimeGraphOperation.PreparedReceipt continuation :=
            ⟨call,checked.val,by with_reducible exact checked.property⟩
          return (⟨continuation.rows checked.val,continuation.roots checked.val⟩,
            bodies.drop indices.length,references,[receipt])
        | .strict =>
          guard (!graph.hasMeaningRequirements) .request
          exactWork (Exact.charge (16*(indices.length+bodies.length+1)))
          let (discovery,remaining) ← indices.foldlM (fun (discovery,bodies) index => do
            let bodyRequest :: rest := bodies | throw .request
            let header ← RuntimeProviderHeader.read artifact graph index bodyRequest
            guard (!header.original.supplied.arguments.hasMeaningRequirements) .request
            let body := header.original.body.checked
            let (nested,_) ← next body.signature body.events body.summary.staticRows bodyRequest.2 true
            return (discovery.append (Discovery.append ⟨header.original.supplied.arguments.sourceRows,header.roots⟩ nested),rest))
            (⟨graph.sourceRows,[]⟩,bodies)
          return (discovery,remaining,references,[])
      let readNamed {caller : String} (event : SourceRuntimeContext.NamedEvent artifact.sources caller)
          (position : SourceSequence.Position) (calls : List (SourceSequence.Position × Context)) :
          WorkM (Discovery × List (SourceSequence.Position × Context) × List operationMode.Receipt) := do
        let (callPosition,child) :: calls := calls | throw .request
        guard (callPosition == position && callPosition.offset == event.call.calleeOffset) .request
        let source ← SourceRuntimeTrace.readNamedBody event
        let (nested,receipts) ← next source.checked.signature source.checked.events
          source.checked.summary.staticRows child true
        return (⟨event.target.sourceRows ++ nested.rows,nested.roots⟩,calls,receipts)
      let initial : Discovery := ⟨signature.sourceRows ++ staticRows,[]⟩
      let (initial,bodies,references,receipts) ← if prefixRequired then do
          operationMode.checkSignature signature
          let actuals ← RuntimeProviderHeaders.originalActuals signature.operations
          actuals.foldlM (fun (discovery,bodies,references,receipts) actual => do
            exactWork (Exact.charge (receipts.length+1))
            let (prepared,rest,references,checked) ← readOperation actual.2.graph
              (RuntimeGraphOperation.required signature actual.1.1) bodies references (!request.references.isEmpty)
            return (discovery.append prepared,rest,references,receipts ++ checked))
            (initial,request.bodies,request.references,([] : List operationMode.Receipt))
        else pure (initial,request.bodies,request.references,([] : List operationMode.Receipt))
      let (discovery,sites,calls,branches,bodies,references,receipts) ←
        (events.zip request.positions).foldlM
          (fun (discovery,sites,calls,branches,bodies,references,receipts) (event,position) => do
          exactWork (Exact.charge (receipts.length+references.length+1))
          match event with
          | .selection _ parsed _ selector target scope naturals .. =>
            let site :: sites := sites | throw .request
            guard (site.position == position && site.position.offset == parsed.keyword.span.startByte) .request
            let table ← QuantumArms.readArmsWithInstantiation signature.original signature.instantiation
              signature.supply parsed.keyword.span.startByte selector.basis target.basis (some naturals) scope
            guard (table.arms.length == site.arms.length) .request
            guard (site.attached.inputs.map (·.basis) == [selector.basis,target.basis] &&
              site.attached.outputs.map (·.basis) == [selector.basis,target.basis] &&
              site.required.inputs.map (·.basis) == [selector.basis,target.basis] &&
              site.required.outputs.map (·.basis) == [selector.basis,target.basis] &&
              site.attached.publicEffect == .unitary && site.required.publicEffect == .unitary) .request
            let discovery := discovery.append ⟨Carrier.sourceRows site.attached site.required ++
              table.arms.flatMap (·.sourceRows),[]⟩
            let (discovery,bodies,references,receipts) ← (table.arms.zip site.arms).foldlM
              (fun (discovery,bodies,references,receipts) (arm,subject) => do
                exactWork (Exact.charge (receipts.length+1))
                let _ ← lift (readOption artifact.programs[subject.implementation]?)
                let _ ← lift (readOption artifact.programs[subject.controlled]?)
                let (prepared,rest,references,checked) ← readOperation arm.operation.graph
                  OperationAccess.controllable bodies references (!request.references.isEmpty)
                return (discovery.append (prepared.append ⟨[],[subject.implementation,subject.controlled]⟩),
                  rest,references,receipts ++ checked)) (discovery,bodies,references,receipts)
            return (discovery,sites,calls,branches,bodies,references,receipts)
          | .named event =>
            let (nested,calls,checked) ← readNamed event position calls
            return (discovery.append nested,sites,calls,branches,bodies,references,receipts ++ checked)
          | .operation event =>
            let (callPosition,child) :: calls := calls | throw .request
            guard (callPosition == position && callPosition.offset == event.call.calleeOffset &&
              child.positions.isEmpty && child.sites.isEmpty && child.calls.isEmpty && child.branches.isEmpty) .request
            let (nested,rest,remaining,checked) ← readOperation event.operation.graph
              OperationAccess.applicable child.bodies child.references (!child.references.isEmpty)
            guard (rest.isEmpty && remaining.isEmpty) .request
            return (discovery.append ⟨event.operation.rows ++ event.naturals.sourceRows ++ nested.rows,nested.roots⟩,
              sites,calls,branches,bodies,references,receipts ++ checked)
          | .conditional event _ _ =>
            let (branchPosition,left,right) :: branches := branches | throw .request
            guard (branchPosition == position && branchPosition.offset == event.written.parts.keyword.span.startByte) .request
            let source ← SourceRuntimeTrace.readBranchSource event
            let (left,leftReceipts) ← next signature source.thenResult.events source.thenResult.staticRows left false
            let (right,rightReceipts) ← next signature source.elseResult.events source.elseResult.staticRows right false
            exactWork (Exact.charge (leftReceipts.length+1))
            return (discovery.append (Discovery.append ⟨event.naturals.sourceRows,[]⟩ (left.append right)),
              sites,calls,branches,bodies,references,receipts ++ leftReceipts ++ rightReceipts)
          | .transform event =>
            let (callPosition,child) :: calls := calls | throw .request
            guard (callPosition == position && callPosition.offset == event.call.calleeOffset &&
              child.positions.isEmpty && child.sites.isEmpty && child.calls.isEmpty && child.branches.isEmpty &&
              child.references.isEmpty) .request
            let [(subject,body)] := child.bodies | throw .request
            let roots ← subjectRoots artifact subject
            let source ← SourceRuntimeTrace.readTransformBody event
            let (nested,checked) ← next source.checked.signature source.checked.events source.checked.summary.staticRows body true
            return (discovery.append ⟨event.target.sourceRows ++ event.counts.flatMap (·.checked.rows) ++ nested.rows,
              roots ++ nested.roots⟩,sites,calls,branches,bodies,references,receipts ++ checked)
          | .basis event =>
            let source ← SourceRuntimeTrace.readBasisSource event
            let rows ← ordinaryRows artifact.sources 128 source.events
            return (discovery.append ⟨event.staticRows ++ source.staticRows ++ rows,[]⟩,
              sites,calls,branches,bodies,references,receipts)
          | .primitive event =>
            return (discovery.append ⟨CallName.sourceRows event.candidate,[]⟩,sites,calls,branches,bodies,references,receipts)
          | .phase event =>
            return (discovery.append ⟨CallName.sourceRows event.application.candidate ++ event.naturals.sourceRows,[]⟩,
              sites,calls,branches,bodies,references,receipts)
          | .staticConditional event _ =>
            let source ← RuntimeStaticPrimitive.readContinuation event
            let positions ← source.positions position (calls.map (·.1))
            guard (positions.length == source.selected.result.events.length) .request
            let initial := discovery.append ⟨source.sourceRows,[]⟩
            exactWork (Exact.charge (16*(source.selected.result.events.length+initial.rows.length+initial.roots.length+1)))
            let (discovery,calls,receipts) ← (source.selected.result.events.zip positions).foldlM
              (fun (discovery,calls,receipts) (event,position) => do
                exactWork (Exact.charge (receipts.length+1))
                match event with
                | .named event =>
                  let (nested,calls,checked) ← readNamed event position calls
                  return (discovery.append nested,calls,receipts ++ checked)
                | .primitive _ | .phase _ => return (discovery,calls,receipts)
                | _ => throw .request) (initial,calls,receipts)
            return (discovery,sites,calls,branches,bodies,references,receipts)
          | .matching .. | .computed .. | .registerPrimitive .. => throw .request)
          (initial,request.sites,request.calls,request.branches,bodies,references,receipts)
      guard (sites.isEmpty && calls.isEmpty && branches.isEmpty && bodies.isEmpty && references.isEmpty) .request
      return (discovery,receipts))

/-- Existing source callers retain the strict continuation and return type. -/
def visit (artifact : Artifact) (fuel : Nat) {owner name : String}
    (signature : SourceRuntimeContext.Signature artifact.sources owner name)
    (events : List (SourceRuntimeContext.Event artifact.sources owner)) (staticRows : List (String × String))
    (request : Context) (prefixRequired : Bool) : WorkM Discovery := do
  let (discovery,_) ← visitUsing artifact .strict fuel signature events staticRows request prefixRequired
  return discovery

/-- One selected original signature and indexed body, under the exact supplied
catalogue. Both source entry points use this executable reader; no alternate
source, signature cache or acceptance result is introduced. -/
structure SelectedSource (artifact : Artifact) (catalogue : GenericCatalogue.Checked artifact.sources)
    (owner name : String) (arguments : StaticTypes.Arguments) where
  signature : SourceRuntimeContext.Signature artifact.sources owner name
  selected : RuntimeInterval.Computed
    (SourceRuntimeContext.readSignature artifact.sources owner name arguments .external (some catalogue)) signature
  body : SourceRuntimeTrace.Body signature
  traversed : RuntimeInterval.Computed (SourceRuntimeTrace.readBodyWithSignature signature) body

def readSelectedSource (artifact : Artifact) (catalogue : GenericCatalogue.Checked artifact.sources)
    (owner name : String) (arguments : StaticTypes.Arguments) :
    WorkM (SelectedSource artifact catalogue owner name arguments) := do
  let signature ← NaturalAffine.witness
    (SourceRuntimeContext.readSignature artifact.sources owner name arguments .external (some catalogue))
  let body ← NaturalAffine.witness (SourceRuntimeTrace.readBodyWithSignature signature.val)
  return ⟨signature.val,by with_reducible exact signature.property,body.val,by with_reducible exact body.property⟩

/-- Source preparation retains complete original pending assessments. It is
not a successful strict Source and cannot replace its withheld proof. Actual
operation/Meaning occurrences remain on this same indexed body for discovery.
-/
structure PreparedSource (artifact : Artifact) (owner name : String) (arguments : StaticTypes.Arguments) where
  catalogue : GenericCatalogue.Checked artifact.sources
  audited : RuntimeInterval.Computed (GenericCatalogue.read artifact.sources) catalogue
  pending : SourcePendingMeaning.Prepared catalogue
  pendingRead : RuntimeInterval.Computed (SourcePendingMeaning.prepare catalogue) pending
  selection : SelectedSource artifact catalogue owner name arguments

def PreparedSource.signature {artifact owner name arguments}
    (source : PreparedSource artifact owner name arguments) := source.selection.signature

def PreparedSource.body {artifact owner name arguments}
    (source : PreparedSource artifact owner name arguments) : SourceRuntimeTrace.Body source.signature := source.selection.body

/-- All-original assessment precedes the selected signature/body. This is
non-accepting preparation: a closed M remains explicit and unconsumed. -/
def prepareSource (artifact : Artifact) (owner name : String) (arguments : StaticTypes.Arguments) :
    WorkM (PreparedSource artifact owner name arguments) := do
  let catalogue ← NaturalAffine.witness (GenericCatalogue.read artifact.sources)
  let pending ← NaturalAffine.witness (SourcePendingMeaning.prepare catalogue.val)
  let selection ← readSelectedSource artifact catalogue.val owner name arguments
  return ⟨catalogue.val,by with_reducible exact catalogue.property,
    pending.val,by with_reducible exact pending.property,selection⟩

structure Source (artifact : Artifact) (owner name : String) (arguments : StaticTypes.Arguments) where
  catalogue : GenericCatalogue.Checked artifact.sources
  audited : RuntimeInterval.Computed (GenericCatalogue.read artifact.sources) catalogue
  pending : SourcePendingMeaning.Checked catalogue
  pendingRead : RuntimeInterval.Computed (SourcePendingMeaning.read catalogue) pending
  signature : SourceRuntimeContext.Signature artifact.sources owner name
  selected : RuntimeInterval.Computed
    (SourceRuntimeContext.readSignature artifact.sources owner name arguments .external (some catalogue)) signature
  body : SourceRuntimeTrace.Body signature
  traversed : RuntimeInterval.Computed (SourceRuntimeTrace.readBodyWithSignature signature) body

def readSource (artifact : Artifact) (owner name : String) (arguments : StaticTypes.Arguments) :
    WorkM (Source artifact owner name arguments) := do
  let catalogue ← NaturalAffine.witness (GenericCatalogue.read artifact.sources)
  let pending ← NaturalAffine.witness (SourcePendingMeaning.read catalogue.val)
  let selection ← readSelectedSource artifact catalogue.val owner name arguments
  return ⟨catalogue.val,by with_reducible exact catalogue.property,
    pending.val,by with_reducible exact pending.property,selection.signature,
    selection.selected,selection.body,selection.traversed⟩

/-- Reuse every actual component of a successful strict read, including the
assessment preparation retained by that read. This claims no new whole-reader
run and never reconstructs a source body or canonical queue. -/
def Source.preparation {artifact owner name arguments} (source : Source artifact owner name arguments) :
    PreparedSource artifact owner name arguments :=
  ⟨source.catalogue,source.audited,source.pending.toPrepared,source.pending.preparedRead,
    ⟨source.signature,source.selected,source.body,source.traversed⟩⟩

structure Headers (artifact : Artifact) (owner name : String) (arguments : StaticTypes.Arguments)
    (request : Context) where
  source : Source artifact owner name arguments
  discovered : Discovery
  original : RuntimeInterval.Computed (visit artifact 128 source.body.checked.signature
    source.body.checked.events source.body.checked.summary.staticRows request true) discovered

def readHeaders (artifact : Artifact) (owner name : String) (arguments : StaticTypes.Arguments)
    (request : Context) : WorkM (Headers artifact owner name arguments request) := do
  let source ← readSource artifact owner name arguments
  let discovered ← NaturalAffine.witness (visit artifact 128 source.body.checked.signature
    source.body.checked.events source.body.checked.summary.staticRows request true)
  return ⟨source,discovered.val,by with_reducible exact discovered.property⟩

def Headers.roots {artifact owner name arguments request}
    (headers : @Headers artifact owner name arguments request) : List Nat :=
  (artifact.root :: headers.discovered.roots).eraseDups

structure Fresh {artifact owner name arguments request} (order : Array Nat)
    (headers : @Headers artifact owner name arguments request) where
  root : Validity.Root
  checked : RuntimeInterval.Computed
    (Validity.checkRootFromRoots artifact order headers.discovered.rows headers.roots) root

/-- This is the sole fresh graph after complete original discovery. No local
body continuation may replace its dependencies or check a different root. -/
def prepare {artifact owner name arguments request} (order : Array Nat)
    (headers : @Headers artifact owner name arguments request) : WorkM (Fresh order headers) := do
  let bytes := (artifact.sources.toList.map fun row => row.1.utf8ByteSize+row.2.utf8ByteSize).sum
  exactWork (Exact.charge (8+(bytes+artifact.sources.size+1)*(headers.discovered.rows.length+1)+
    16*(headers.discovered.roots.length+1)^2))
  let root ← NaturalAffine.witness
    (Validity.checkRootFromRoots artifact order headers.discovered.rows headers.roots)
  return ⟨root.val,by with_reducible exact root.property⟩

end QleisliKernel.Qirf.RuntimeBodyDiscovery
