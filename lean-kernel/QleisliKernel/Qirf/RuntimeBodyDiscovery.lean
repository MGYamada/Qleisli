import QleisliKernel.Qirf.RuntimeProviderHeader
import QleisliKernel.SourceTypes.QuantumArms

/-! Discover every original runtime body before the one fresh graph check.
The traversal follows actual source events and supplied context occurrences;
provider bodies retain their original supplier receipts. A discovery result is
not source/IR acceptance: local action, ordinary history, Meaning and access
continuations must still be checked under the final root.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeBodyDiscovery
open QleisliKernel QleisliKernel.Finite QleisliKernel.SourceTypes
open SourceRuntimeValues
abbrev Context := RuntimeContextRequest.Context
abbrev BodyRequest := RuntimeProviderHeader.Request

structure Discovery where
  rows : List (String × String) := []
  roots : List Nat := []

def Discovery.append (first second : Discovery) : Discovery :=
  ⟨first.rows ++ second.rows,first.roots ++ second.roots⟩

private def subjectRoots (artifact : Artifact) : SourceProviderSubject.Subject → WorkM (List Nat)
  | .pure index => do
    let _ ← lift (readOption artifact.programs[index]?)
    return [index]
  | .function index => do
    let entry ← lift (readOption artifact.entries[index]?)
    let _ ← lift (readOption artifact.programs[entry.implementation]?)
    return [entry.implementation,artifact.programs.size+index]

/-- Coherent ordinary helper bodies contribute original source queries rather
than fabricated runtime call intervals. Their actual finite reference/action
correspondence is checked by the separate basis continuation. -/
private def ordinaryRows (sources : Sources) : Nat → {owner : String} →
    List (SourceRuntimeContext.Event sources owner) → WorkM (List (String × String)) :=
  Nat.rec (fun {_} _ => throw .limit) (fun _ next {_} events => do
    events.foldlM (fun rows event => do
      match event with
      | .named event =>
        guard (event.target.signature.arguments.operations.isEmpty &&
          !event.target.signature.operations.hasMeaningRequirements) .request
        let source ← SourceRuntimeTrace.readNamedBody event
        guard (!source.checked.summary.quantumUse && source.checked.summary.allocated.isEmpty &&
          source.checked.summary.consumed.isEmpty &&
          source.checked.summary.inferredEffect == .unitary) .request
        let children ← next source.checked.events
        return rows ++ event.target.sourceRows ++ source.checked.signature.sourceRows ++
          source.checked.summary.staticRows ++ children
      | _ => throw .request) [] )

/-- The containing prefix is present once for a function body. Branch children
inherit it; operation-application children have their own tree and no invented
function prefix. Every provider occurrence consumes one body slot, even when
its descriptor node or supplied evidence index repeats. -/
def visit (artifact : Artifact) : Nat → {owner name : String} →
    SourceRuntimeContext.Signature artifact.sources owner name →
    List (SourceRuntimeContext.Event artifact.sources owner) → List (String × String) →
    Context → Bool → WorkM Discovery :=
  Nat.rec (fun {_ _} _ _ _ _ _ => throw .limit)
    (fun _ next {_ _} signature events staticRows request prefixRequired => do
      guard (request.positions.length ≤ 4096 && request.sites.length ≤ 128 &&
        request.calls.length ≤ 4096 && request.branches.length ≤ 4096 && request.bodies.length ≤ 4096) .limit
      exactWork (Exact.charge (32*(events.length+request.positions.length+request.sites.length+
        request.calls.length+request.branches.length+request.bodies.length+1)^2))
      guard (request.positions.map (·.offset) == events.map SourceRuntimeContext.Event.offset) .request
      let readOperation {context description}
          (graph : StaticOperation.CheckedGraph artifact.sources context description)
          (bodies : List BodyRequest) : WorkM (Discovery × List BodyRequest) := do
        -- The final Meaning evaluator is not supplied by graph metadata.
        guard (!graph.hasMeaningRequirements) .request
        let occurrences ← StaticOperation.readOccurrences description
        let indices := occurrences.filter fun index => match description.nodes[index]? with
          | some (.provider ..) => true
          | _ => false
        exactWork (Exact.charge (16*(indices.length+bodies.length+1)))
        indices.foldlM (fun (discovery,bodies) index => do
          let bodyRequest :: rest := bodies | throw .request
          let header ← RuntimeProviderHeader.read artifact graph index bodyRequest
          guard (!header.original.supplied.arguments.hasMeaningRequirements) .request
          let body := header.original.body.checked
          let nested ← next body.signature body.events body.summary.staticRows bodyRequest.2 true
          return (discovery.append (Discovery.append ⟨header.original.supplied.arguments.sourceRows,header.roots⟩ nested),rest))
          (⟨graph.sourceRows,[]⟩,bodies)
      let initial : Discovery := ⟨signature.sourceRows ++ staticRows,[]⟩
      let (initial,bodies) ← if prefixRequired then do
          guard (!signature.operations.hasMeaningRequirements) .request
          signature.operations.actuals.foldlM (fun (discovery,bodies) actual => do
            let (prepared,rest) ← readOperation actual.2.graph bodies
            return (discovery.append prepared,rest)) (initial,request.bodies)
        else pure (initial,request.bodies)
      let (discovery,sites,calls,branches,bodies) ←
        (events.zip request.positions).foldlM (fun (discovery,sites,calls,branches,bodies) (event,position) => do
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
            let (discovery,bodies) ← (table.arms.zip site.arms).foldlM
              (fun (discovery,bodies) (arm,subject) => do
                let _ ← lift (readOption artifact.programs[subject.implementation]?)
                let _ ← lift (readOption artifact.programs[subject.controlled]?)
                let (prepared,rest) ← readOperation arm.operation.graph bodies
                return (discovery.append (prepared.append ⟨[],[subject.implementation,subject.controlled]⟩),rest))
              (discovery,bodies)
            return (discovery,sites,calls,branches,bodies)
          | .named event =>
            let (callPosition,child) :: calls := calls | throw .request
            guard (callPosition == position && callPosition.offset == event.call.calleeOffset) .request
            let source ← SourceRuntimeTrace.readNamedBody event
            let nested ← next source.checked.signature source.checked.events
              source.checked.summary.staticRows child true
            return (discovery.append ⟨event.target.sourceRows ++ nested.rows,nested.roots⟩,
              sites,calls,branches,bodies)
          | .operation event =>
            let (callPosition,child) :: calls := calls | throw .request
            guard (callPosition == position && callPosition.offset == event.call.calleeOffset &&
              child.positions.isEmpty && child.sites.isEmpty && child.calls.isEmpty && child.branches.isEmpty) .request
            let (nested,rest) ← readOperation event.operation.graph child.bodies
            guard rest.isEmpty .request
            return (discovery.append ⟨event.operation.rows ++ event.naturals.sourceRows ++ nested.rows,nested.roots⟩,
              sites,calls,branches,bodies)
          | .conditional event _ _ =>
            let (branchPosition,left,right) :: branches := branches | throw .request
            guard (branchPosition == position && branchPosition.offset == event.written.parts.keyword.span.startByte) .request
            let source ← SourceRuntimeTrace.readBranchSource event
            let left ← next signature source.thenResult.events source.thenResult.staticRows left false
            let right ← next signature source.elseResult.events source.elseResult.staticRows right false
            return (discovery.append (Discovery.append ⟨event.naturals.sourceRows,[]⟩ (left.append right)),
              sites,calls,branches,bodies)
          | .transform event =>
            let (callPosition,child) :: calls := calls | throw .request
            guard (callPosition == position && callPosition.offset == event.call.calleeOffset &&
              child.positions.isEmpty && child.sites.isEmpty && child.calls.isEmpty && child.branches.isEmpty) .request
            let [(subject,body)] := child.bodies | throw .request
            let roots ← subjectRoots artifact subject
            let source ← SourceRuntimeTrace.readTransformBody event
            let nested ← next source.checked.signature source.checked.events source.checked.summary.staticRows body true
            return (discovery.append ⟨event.target.sourceRows ++ event.counts.flatMap (·.checked.rows) ++ nested.rows,
              roots ++ nested.roots⟩,sites,calls,branches,bodies)
          | .basis event =>
            let source ← SourceRuntimeTrace.readBasisSource event
            let rows ← ordinaryRows artifact.sources 128 source.events
            return (discovery.append ⟨event.staticRows ++ source.staticRows ++ rows,[]⟩,
              sites,calls,branches,bodies)
          | .primitive event =>
            return (discovery.append ⟨CallName.sourceRows event.candidate,[]⟩,sites,calls,branches,bodies)
          | .phase event =>
            return (discovery.append ⟨CallName.sourceRows event.application.candidate ++ event.naturals.sourceRows,[]⟩,
              sites,calls,branches,bodies)) (initial,request.sites,request.calls,request.branches,bodies)
      guard (sites.isEmpty && calls.isEmpty && branches.isEmpty && bodies.isEmpty) .request
      return discovery)

structure Source (artifact : Artifact) (owner name : String) (arguments : StaticTypes.Arguments) where
  signature : SourceRuntimeContext.Signature artifact.sources owner name
  selected : RuntimeInterval.Computed
    (SourceRuntimeContext.readSignature artifact.sources owner name arguments .external) signature
  body : SourceRuntimeTrace.Body signature
  traversed : RuntimeInterval.Computed (SourceRuntimeTrace.readBodyWithSignature signature) body

def readSource (artifact : Artifact) (owner name : String) (arguments : StaticTypes.Arguments) :
    WorkM (Source artifact owner name arguments) := do
  let signature ← NaturalAffine.witness (SourceRuntimeContext.readSignature artifact.sources owner name arguments .external)
  let body ← NaturalAffine.witness (SourceRuntimeTrace.readBodyWithSignature signature.val)
  return ⟨signature.val,by with_reducible exact signature.property,
    body.val,by with_reducible exact body.property⟩

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
