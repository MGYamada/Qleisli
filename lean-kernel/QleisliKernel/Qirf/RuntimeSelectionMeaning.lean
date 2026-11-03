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

structure Arm {artifact owner name arguments source request}
    (site : @RuntimeSelectionSource.Checked artifact owner name arguments source request) where
  index : Fin site.table.arms.length
  implementations : List Request
  references : List (List Request)
  prepared : RuntimePreparedArm.Prepared artifact source.catalogue site.table index implementations references
  original : RuntimeInterval.Computed
    (RuntimePreparedArm.prepare artifact source.catalogue site.table index implementations references) prepared

private def collect {artifact owner name arguments source request}
    (site : @RuntimeSelectionSource.Checked artifact owner name arguments source request)
    (references : List (List (List Request))) : WorkM (Array (Arm site)) := do
  guard (references.length == site.table.arms.length) .request
  exactWork (Exact.charge (16*(site.table.arms.length+request.bodies.length+1)^2))
  let (arms,remaining,groups) ← (List.finRange site.table.arms.length).foldlM (fun (arms,bodies,groups) index => do
    let group :: rest := groups | throw .request
    let operation := (site.table.arms[index]).operation
    let occurrences ← StaticOperation.readOccurrences operation.description
    let count := (RuntimeProviderHeaders.providerIndices operation.description occurrences).length
    guard (count ≤ bodies.length) .request
    let implementations := bodies.take count
    let prepared ← NaturalAffine.witness (RuntimePreparedArm.prepare artifact source.catalogue site.table index implementations group)
    let arm : Arm site := ⟨index,implementations,group,prepared.val,by with_reducible exact prepared.property⟩
    return (arms.push arm,bodies.drop count,rest)) (#[],request.bodies,references)
  guard (remaining.isEmpty && groups.isEmpty) .request
  return arms

structure Prepared {artifact owner name arguments}
    (source : RuntimeBodyDiscovery.PreparedSource artifact owner name arguments) (request : RuntimeContextRequest.Context)
    (references : List (List (List Request))) where
  site : RuntimeSelectionSource.Checked source request
  original : RuntimeInterval.Computed (RuntimeSelectionSource.read source request) site
  arms : Array (Arm site)
  collected : RuntimeInterval.Computed (collect site references) arms
  order : arms.toList.map (·.index) = List.finRange site.table.arms.length
  relevance : SourceRows.Retained (site.relevance.rows ++ arms.toList.flatMap (·.prepared.rows))

def prepare {artifact owner name arguments}
    (source : RuntimeBodyDiscovery.PreparedSource artifact owner name arguments) (request : RuntimeContextRequest.Context)
    (references : List (List (List Request))) : WorkM (Prepared source request references) := do
  let site ← NaturalAffine.witness (RuntimeSelectionSource.read source request)
  let arms ← NaturalAffine.witness (collect site.val references)
  if order : arms.val.toList.map (·.index) = List.finRange site.val.table.arms.length then
    let relevance ← SourceRows.read (site.val.relevance.rows ++ arms.val.toList.flatMap (·.prepared.rows))
    return ⟨site.val,by with_reducible exact site.property,arms.val,by with_reducible exact arms.property,order,relevance⟩
  else throw .request

def Prepared.roots {artifact owner name arguments source request references}
    (prepared : @Prepared artifact owner name arguments source request references) : List Nat :=
  (artifact.root :: (prepared.site.site.arms.flatMap (fun arm => [arm.implementation,arm.controlled]) ++
    prepared.arms.toList.flatMap (·.prepared.roots))).eraseDups

structure Realized {artifact owner name arguments source request site}
    (arm : @Arm artifact owner name arguments source request site) (root : Validity.Root) where
  checked : RuntimePreparedArm.Checked arm.prepared root
  original : RuntimeInterval.Computed (RuntimePreparedArm.read arm.prepared root) checked

private def realize {artifact owner name arguments source request references}
    (prepared : @Prepared artifact owner name arguments source request references) (root : Validity.Root)
    (index : Fin prepared.site.table.arms.length)
    (_ : QuantumArms.BoundArm artifact.sources owner prepared.site.selector.basis prepared.site.target.basis)
    (done : List (Σ arm : Arm prepared.site, Realized arm root)) :
    WorkM (Semantics.Exact.Matrix × List (Σ arm : Arm prepared.site, Realized arm root)) := do
  let arm ← lift (readOption prepared.arms[index.val]?)
  if arm.index = index then
    let checked ← NaturalAffine.witness (RuntimePreparedArm.read arm.prepared root)
    return (checked.val.action,⟨arm,checked.val,by with_reducible exact checked.property⟩ :: done)
  else throw .request

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

end QleisliKernel.Qirf.RuntimeSelectionMeaning
