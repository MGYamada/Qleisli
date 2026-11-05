import QleisliKernel.Qirf.RuntimeCallerInterval
import QleisliKernel.Qirf.RuntimePreparedArm
import QleisliKernel.Qirf.RuntimeSelectionSource

/-! A complete literal qmatch interval with original, controllable arm actions.
Provider bodies and Meaning references contribute their roots before a single
graph read. Each indexed arm subsequently uses that root and the same sector
and owner checks as the ordinary source-body traversal.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeSelectionMeaning
open QleisliKernel Finite SourceTypes
abbrev Request := RuntimeProviderHeader.Request

structure SharedArm {artifact : Artifact} (catalogue : GenericCatalogue.Checked artifact.sources)
    {owner name : String} {signature : SourceRuntimeContext.Signature artifact.sources owner name}
    {body : SourceRuntimeTrace.Body signature} {request : RuntimeContextRequest.Context}
    (site : RuntimeSelectionSource.Site body request) where
  index : Fin site.table.arms.length
  implementations : List Request
  references : List (List Request)
  prepared : RuntimePreparedArm.Prepared artifact catalogue site.table index implementations references
  original : RuntimeInterval.Computed
    (RuntimePreparedArm.prepare artifact catalogue site.table index implementations references) prepared

abbrev Arm {artifact owner name arguments source request}
    (site : @RuntimeSelectionSource.Checked artifact owner name arguments source request) :=
  SharedArm source.catalogue site.toSite

private def collect {artifact : Artifact} (catalogue : GenericCatalogue.Checked artifact.sources)
    {owner name : String} {signature : SourceRuntimeContext.Signature artifact.sources owner name}
    {body : SourceRuntimeTrace.Body signature} {request : RuntimeContextRequest.Context}
    (site : RuntimeSelectionSource.Site body request)
    (references : List (List (List Request))) : WorkM (Array (SharedArm catalogue site)) := do
  guard (references.length == site.table.arms.length) .request
  exactWork (Exact.charge (16*(site.table.arms.length+request.bodies.length+1)^2))
  let (arms,remaining,groups) ← (List.finRange site.table.arms.length).foldlM (fun (arms,bodies,groups) index => do
    let group :: rest := groups | throw .request
    let operation := (site.table.arms[index]).operation
    let occurrences ← StaticOperation.readOccurrences operation.description
    let count := (RuntimeProviderHeaders.providerIndices operation.description occurrences).length
    guard (count ≤ bodies.length) .request
    let implementations := bodies.take count
    let prepared ← NaturalAffine.witness (RuntimePreparedArm.prepare artifact catalogue site.table index implementations group)
    let arm : SharedArm catalogue site := ⟨index,implementations,group,prepared.val,by with_reducible exact prepared.property⟩
    return (arms.push arm,bodies.drop count,rest)) (#[],request.bodies,references)
  guard (remaining.isEmpty && groups.isEmpty) .request
  return arms

/-- Arms prepared once for this exact original body/site. The enclosing root
reader or authenticated named-call reader retains how the site was obtained. -/
structure PreparedSite {artifact : Artifact} (catalogue : GenericCatalogue.Checked artifact.sources)
    {owner name : String} {signature : SourceRuntimeContext.Signature artifact.sources owner name}
    {body : SourceRuntimeTrace.Body signature} {request : RuntimeContextRequest.Context}
    (site : RuntimeSelectionSource.Site body request) (references : List (List (List Request))) where
  arms : Array (SharedArm catalogue site)
  collected : RuntimeInterval.Computed (collect catalogue site references) arms
  order : arms.toList.map (·.index) = List.finRange site.table.arms.length
  relevance : SourceRows.Retained (site.relevance.rows ++ arms.toList.flatMap (·.prepared.rows))

def prepareSite {artifact : Artifact} (catalogue : GenericCatalogue.Checked artifact.sources)
    {owner name : String} {signature : SourceRuntimeContext.Signature artifact.sources owner name}
    {body : SourceRuntimeTrace.Body signature} {request : RuntimeContextRequest.Context}
    (site : RuntimeSelectionSource.Site body request) (references : List (List (List Request))) :
    WorkM (PreparedSite catalogue site references) := do
  let arms ← NaturalAffine.witness (collect catalogue site references)
  if order : arms.val.toList.map (·.index) = List.finRange site.table.arms.length then
    let relevance ← SourceRows.read (site.relevance.rows ++ arms.val.toList.flatMap (·.prepared.rows))
    return ⟨arms.val,by with_reducible exact arms.property,order,relevance⟩
  else throw .request

def PreparedSite.roots {artifact catalogue owner name signature body request site references}
    (prepared : @PreparedSite artifact catalogue owner name signature body request site references) : List Nat :=
  (site.site.arms.flatMap (fun arm => [arm.implementation,arm.controlled]) ++
    prepared.arms.toList.flatMap (·.prepared.roots)).eraseDups

structure Prepared {artifact owner name arguments}
    (source : RuntimeBodyDiscovery.PreparedSource artifact owner name arguments) (request : RuntimeContextRequest.Context)
    (references : List (List (List Request))) where
  site : RuntimeSelectionSource.Checked source request
  original : RuntimeInterval.Computed (RuntimeSelectionSource.read source request) site
  arms : Array (Arm site)
  collected : RuntimeInterval.Computed (collect source.catalogue site.toSite references) arms
  order : arms.toList.map (·.index) = List.finRange site.table.arms.length
  relevance : SourceRows.Retained (site.relevance.rows ++ arms.toList.flatMap (·.prepared.rows))

def prepare {artifact owner name arguments}
    (source : RuntimeBodyDiscovery.PreparedSource artifact owner name arguments) (request : RuntimeContextRequest.Context)
    (references : List (List (List Request))) : WorkM (Prepared source request references) := do
  let site ← NaturalAffine.witness (RuntimeSelectionSource.read source request)
  let shared ← prepareSite source.catalogue site.val.toSite references
  return ⟨site.val,by with_reducible exact site.property,shared.arms,shared.collected,shared.order,shared.relevance⟩

def Prepared.asSite {artifact owner name arguments source request references}
    (prepared : @Prepared artifact owner name arguments source request references) :
    PreparedSite source.catalogue prepared.site.toSite references :=
  ⟨prepared.arms,prepared.collected,prepared.order,prepared.relevance⟩

def Prepared.roots {artifact owner name arguments source request references}
    (prepared : @Prepared artifact owner name arguments source request references) : List Nat :=
  (artifact.root :: (prepared.site.site.arms.flatMap (fun arm => [arm.implementation,arm.controlled]) ++
    prepared.arms.toList.flatMap (·.prepared.roots))).eraseDups

structure SharedRealized {artifact catalogue owner name signature body request site}
    (arm : @SharedArm artifact catalogue owner name signature body request site) (root : Validity.Root) where
  checked : RuntimePreparedArm.Checked arm.prepared root
  original : RuntimeInterval.Computed (RuntimePreparedArm.read arm.prepared root) checked

abbrev Realized {artifact owner name arguments source request site}
    (arm : @Arm artifact owner name arguments source request site) (root : Validity.Root) :=
  SharedRealized arm root

private def realizeAt {artifact catalogue owner name signature body request site references}
    (prepared : @PreparedSite artifact catalogue owner name signature body request site references) (root : Validity.Root)
    (index : Fin site.table.arms.length)
    (_ : QuantumArms.BoundArm artifact.sources owner site.selector.basis site.target.basis)
    (done : List (Σ arm : SharedArm catalogue site, SharedRealized arm root)) :
    WorkM (Semantics.Exact.Matrix × List (Σ arm : SharedArm catalogue site, SharedRealized arm root)) := do
  let arm ← lift (readOption prepared.arms[index.val]?)
  if arm.index = index then
    let checked ← NaturalAffine.witness (RuntimePreparedArm.read arm.prepared root)
    return (checked.val.action,⟨arm,checked.val,by with_reducible exact checked.property⟩ :: done)
  else throw .request

private def realize {artifact owner name arguments source request references}
    (prepared : @Prepared artifact owner name arguments source request references) (root : Validity.Root)
    (index : Fin prepared.site.table.arms.length)
    (arm : QuantumArms.BoundArm artifact.sources owner prepared.site.selector.basis prepared.site.target.basis)
    (done : List (Σ arm : Arm prepared.site, Realized arm root)) :
    WorkM (Semantics.Exact.Matrix × List (Σ arm : Arm prepared.site, Realized arm root)) :=
  realizeAt prepared.asSite root index arm done

structure Checked {artifact owner name arguments source request references}
    (prepared : @Prepared artifact owner name arguments source request references)
    (order : Array Nat) (runtime : RuntimeFamily.Request) where
  root : Validity.Root
  fresh : RuntimeInterval.Computed (Validity.checkRootFromRoots artifact order prepared.relevance.rows prepared.roots) root
  covers : prepared.site.site.position.start = 0 ∧ prepared.site.site.position.count = root.program.operations.length
  ports : RuntimeCallerInterval.Ports source.body root prepared.site.site.position runtime
  node : RuntimePureBody.Node root.dependencies root.program ports.block.block
  reverseArms : List (Σ arm : Arm prepared.site, Realized arm root)
  equation : RuntimeInterval.Computed
    (RuntimePureBody.selectionNode artifact ports.interval ports.initial ports.moved prepared.site.selector
      prepared.site.target prepared.site.table prepared.site.site [] (realize prepared root)) (node,reverseArms)
  returned : RuntimeCallerInterval.Return ports

def read {artifact owner name arguments source request references}
    (prepared : @Prepared artifact owner name arguments source request references)
    (order : Array Nat) (runtime : RuntimeFamily.Request) : WorkM (Checked prepared order runtime) := do
  let root ← NaturalAffine.witness (Validity.checkRootFromRoots artifact order prepared.relevance.rows prepared.roots)
  let site := prepared.site
  let pos := site.site.position
  if covers : pos.start = 0 ∧ pos.count = root.val.program.operations.length then
    let ports ← RuntimeCallerInterval.read source.body root.val pos runtime
    let result ← NaturalAffine.witness (RuntimePureBody.selectionNode artifact ports.interval ports.initial ports.moved
      site.selector site.target site.table site.site [] (realize prepared root.val))
    let returned ← RuntimeCallerInterval.finish ports
    return ⟨root.val,by with_reducible exact root.property,covers,ports,result.val.1,result.val.2,
      by with_reducible exact result.property,returned⟩
  else throw .request

/-- A complete pure selection in a genuine local call program. This record
retains its exact Body and final dependency root; the enclosing named boundary
must establish the local program and canonical input mapping and transfer its
source-ordered result back to the caller. It is not a new root decision. -/
structure LocalChecked {artifact catalogue owner name signature body request site references}
    (prepared : @PreparedSite artifact catalogue owner name signature body request site references)
    (root : Validity.Root) {program : Semantics.Observation.Program}
    (native : RuntimeInterval.Prepared root.dependencies program) (initial : RuntimeOwnerMap.Map) where
  covers : site.site.position.start = 0 ∧ site.site.position.count = program.operations.length
  quantumOnly : (body.checked.summary.parameterValues.flatMap SourceRuntimeValues.ordinary).isEmpty = true ∧
    (SourceRuntimeValues.ordinary body.checked.summary.value).isEmpty = true
  pureSource : body.checked.summary.inferredEffect = .unitary
  sourceHistory : body.checked.summary.allocated = [] ∧ body.checked.summary.consumed = [] ∧
    body.checked.summary.nextOrdinal = body.checked.summary.nextOwner
  issued : (body.checked.summary.parameterValues.flatMap SourceRuntimeValues.valueOwners).map (·.ordinal) =
    List.range body.checked.summary.nextOwner
  interval : RuntimeInterval.Checked native.block site.site.position.start site.site.position.count
  intervalRead : RuntimeInterval.Computed
    (RuntimeInterval.check native.block site.site.position.start site.site.position.count) interval
  initialFrame : RuntimeOwnerMap.Checked
    (body.checked.summary.parameterValues.flatMap SourceRuntimeValues.valueOwners) interval.before
  sameInitial : initialFrame.bindings = initial
  moved : RuntimeOwnerTransition.Checked interval initialFrame.bindings
  node : RuntimePureBody.Node root.dependencies program native.block
  reverseArms : List (Σ arm : SharedArm catalogue site, SharedRealized arm root)
  equation : RuntimeInterval.Computed
    (RuntimePureBody.selectionNode artifact interval initialFrame moved site.selector site.target site.table site.site
      [] (realizeAt prepared root)) (node,reverseArms)
  finalBindings : RuntimeOwnerMap.Map
  finalOrder : RuntimeInterval.Computed (RuntimeOwnerMap.order
    (SourceRuntimeValues.valueOwners body.checked.summary.value) moved.after.bindings) finalBindings
  finalFrame : RuntimeOwnerMap.Checked (SourceRuntimeValues.valueOwners body.checked.summary.value) interval.after
  sameFinal : finalFrame.bindings = finalBindings
  returned : List Semantics.Raw.Port
  returnedRead : RuntimeInterval.Computed
    (RuntimePureBody.rolePorts (SourceRuntimeValues.valueOwners body.checked.summary.value) finalBindings) returned
  localOutputs : (returned.map (·.token)).Perm program.outputs

def LocalChecked.history {artifact catalogue owner name signature body request site references prepared root program native initial}
    (checked : @LocalChecked artifact catalogue owner name signature body request site references prepared root program native initial) :
    RuntimeStructuralAction.SourceState :=
  ⟨checked.finalBindings,body.checked.summary.parameterValues.flatMap SourceRuntimeValues.valueOwners,
    body.checked.summary.nextOrdinal⟩

def LocalChecked.retired {artifact catalogue owner name signature body request site references prepared root program native initial}
    (_checked : @LocalChecked artifact catalogue owner name signature body request site references prepared root program native initial) :
    List Semantics.SourceOwners.Owner := []

def LocalChecked.value {artifact catalogue owner name signature body request site references prepared root program native initial}
    (_checked : @LocalChecked artifact catalogue owner name signature body request site references prepared root program native initial) :
    SourceRuntimeValues.Value := body.checked.summary.value

/-- Consume all original arm/provider/Meaning obligations against this same
root, then the entire literal selection interval and complete source frame.
Local native output order is only a set: the enclosing named boundary consumes
finalBindings in the original source result order and closes the caller order. -/
def readAt {artifact catalogue owner name signature body request site references}
    (prepared : @PreparedSite artifact catalogue owner name signature body request site references)
    (root : Validity.Root) {program : Semantics.Observation.Program}
    (native : RuntimeInterval.Prepared root.dependencies program) (initial : RuntimeOwnerMap.Map) :
    WorkM (LocalChecked prepared root native initial) := do
  let summary := body.checked.summary
  let inputRoles := summary.parameterValues.flatMap SourceRuntimeValues.valueOwners
  let outputRoles := SourceRuntimeValues.valueOwners summary.value
  exactWork (Exact.charge (32*((summary.parameterValues.map SourceRuntimeValues.valueFields).sum+
    SourceRuntimeValues.valueFields summary.value+Raw.OwnerFlow.fields (inputRoles ++ summary.allocated ++ summary.consumed)+
    summary.nextOwner+summary.nextOrdinal+1)))
  if quantumOnly : (summary.parameterValues.flatMap SourceRuntimeValues.ordinary).isEmpty = true ∧
      (SourceRuntimeValues.ordinary summary.value).isEmpty = true then
    if pureSource : summary.inferredEffect = .unitary then
      if sourceHistory : summary.allocated = [] ∧ summary.consumed = [] ∧ summary.nextOrdinal = summary.nextOwner then
        if issued : inputRoles.map (·.ordinal) = List.range summary.nextOwner then
          let pos := site.site.position
          if covers : pos.start = 0 ∧ pos.count = program.operations.length then
            let interval ← NaturalAffine.witness (RuntimeInterval.check native.block pos.start pos.count)
            let initialFrame ← RuntimeOwnerMap.checkBindings inputRoles interval.val.before initial
            let moved ← RuntimeOwnerTransition.read interval.val initialFrame.val.bindings
            let checked ← NaturalAffine.witness (RuntimePureBody.selectionNode artifact interval.val initialFrame.val moved
              site.selector site.target site.table site.site [] (realizeAt prepared root))
            let finalBindings ← NaturalAffine.witness (RuntimeOwnerMap.order outputRoles moved.after.bindings)
            let finalFrame ← RuntimeOwnerMap.checkBindings outputRoles interval.val.after finalBindings.val
            let returned ← NaturalAffine.witness (RuntimePureBody.rolePorts outputRoles finalBindings.val)
            if localOutputs : (returned.val.map (·.token)).Perm program.outputs then
              return ⟨covers,quantumOnly,pureSource,sourceHistory,issued,interval.val,
                by with_reducible exact interval.property,initialFrame.val,initialFrame.property,moved,
                checked.val.1,checked.val.2,by with_reducible exact checked.property,finalBindings.val,
                by with_reducible exact finalBindings.property,finalFrame.val,finalFrame.property,
                returned.val,by with_reducible exact returned.property,localOutputs⟩
            else throw .request
          else throw .request
        else throw .request
      else throw .request
    else throw .request
  else throw .request

end QleisliKernel.Qirf.RuntimeSelectionMeaning
