import QleisliKernel.Qirf.RuntimeAccessPartition
import QleisliKernel.Qirf.RuntimePureBody

/-! Resolve a written access call and check the original callee body over the
call's actual pure Raw fragment. The common body walk checks every nested
action and the exact ordered return, including distinct zero-width owners.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeAccessCallee
open QleisliKernel Finite SourceTypes SourceRuntimeValues

abbrev Context := RuntimeContextRequest.Context

def roles (places : List AccessSyntax.Place) : List Semantics.FiniteCarrier.Basis :=
  (RuntimeAccessInterval.roles places).map (·.basis)

structure Target {artifact : Artifact} {owner name dependencies program signature root tokens}
    (source : @RuntimeAccessSource.Checked artifact.sources owner name dependencies program signature root)
    (call : AccessSyntax.CheckedCall tokens) where
  caller : SourceRuntimeContext.Signature artifact.sources owner name
  callerBody : caller.original.occurrence.body = signature.original.occurrence.body
  scope : List String
  scopeRead : scope = caller.staticNames ++ source.entry.map (·.original.binder.text)
  resolved : SourceRuntimeContext.Target artifact.sources owner scope call.parsed.call.callee
  resolvedRead : RuntimeInterval.Computed (do
    let written ← lift ((StaticApplication.readSyntax call.parsed.call.callee).mapError fun _ => .request)
    let candidate ← CallName.read artifact.sources owner scope written.callee
    SourceRuntimeContext.readTarget caller (← caller.naturals) written candidate) resolved

private def readTarget {artifact : Artifact} {owner name dependencies program signature root tokens}
    (source : @RuntimeAccessSource.Checked artifact.sources owner name dependencies program signature root)
    (call : AccessSyntax.CheckedCall tokens) : WorkM (Target source call) := do
  let supply ← StaticOperation.checkArgumentsWithInstantiation signature.instantiation .external
  let bound ← SourceRuntimeContext.fromQuantumCore signature .external supply
  let caller := bound.signature
  let scope := caller.staticNames ++ source.entry.map (·.original.binder.text)
  let resolved ← NaturalAffine.witness (do
    let written ← lift ((StaticApplication.readSyntax call.parsed.call.callee).mapError fun _ => .request)
    let candidate ← CallName.read artifact.sources owner scope written.callee
    SourceRuntimeContext.readTarget caller (← caller.naturals) written candidate)
  return ⟨caller,bound.body,scope,rfl,resolved.val,by with_reducible exact resolved.property⟩

def outputShape (places : List AccessSyntax.Place) : List Semantics.RuntimeType.Atom :=
  let fields := (roles places).map Semantics.RuntimeType.owner
  match fields with
  | [only] => only
  | _ => Semantics.RuntimeType.tuple fields.length fields

structure Checked {artifact : Artifact} {root : Validity.Root} {owner name signature tokens}
    {block : RuntimeInterval.Prepared root.dependencies root.program} {callee start count inputs outputs}
    (source : @RuntimeAccessSource.Checked artifact.sources owner name root.dependencies root.program signature block)
    (call : @RuntimeAccessInterval.Checked tokens root.dependencies root.program callee source.lookup source.naturals (fun _ _ => none)
      block.block start count inputs outputs) (request : Context) where
  occurrence : tokens = source.calls.first.leading ∨ tokens = source.calls.second.leading
  target : Target source callee
  targetRead : RuntimeInterval.Computed (readTarget source callee) target
  body : SourceRuntimeTrace.Body target.resolved.signature
  bodyRead : RuntimeInterval.Computed (SourceRuntimeTrace.readBodyWithSignature target.resolved.signature) body
  inputTypes : target.resolved.signature.parameters.map (·.tree) = (roles call.places).map Semantics.RuntimeType.owner
  outputType : target.resolved.signature.result.tree = outputShape call.places
  unitary : SourceEffect.visible owner target.resolved.resolution.moduleName
    target.resolved.signature.original.declaration.isPublic target.resolved.signature.original.parsedHeader.effect
    body.checked.summary.generic.inferredEffect = .unitary
  entry : RuntimeOwnerMap.Map
  entryRead : RuntimeInterval.Computed (RuntimeSourceBoundary.bindings
    (body.checked.summary.parameterValues.flatMap valueOwners)
    ((call.frame.selected.zip (roles call.places)).map fun (port,basis) =>
      (⟨port,basis⟩ : Semantics.CarrierInterface.Owner))) entry
  execution : RuntimePureBody.Checked artifact root body call.fragment request entry

/-- Use the same dependency snapshot and body walk as ordinary named calls.
Context positions are checked by that walk against every source occurrence. -/
def read {artifact : Artifact} {owner name signature tokens} (root : Validity.Root)
    {block : RuntimeInterval.Prepared root.dependencies root.program} {callee start count inputs outputs}
    (source : @RuntimeAccessSource.Checked artifact.sources owner name root.dependencies root.program signature block)
    (call : @RuntimeAccessInterval.Checked tokens root.dependencies root.program callee source.lookup source.naturals (fun _ _ => none)
      block.block start count inputs outputs) (request : Context) : WorkM (Checked source call request) := do
  exactWork (Exact.charge (32*(tokens.length+source.calls.first.leading.length+source.calls.second.leading.length+1)))
  let occurrence : PLift (tokens = source.calls.first.leading ∨ tokens = source.calls.second.leading) ←
    if matched : tokens = source.calls.first.leading ∨ tokens = source.calls.second.leading then
      pure (⟨matched⟩ : PLift (tokens = source.calls.first.leading ∨ tokens = source.calls.second.leading))
    else throw .request
  let target ← NaturalAffine.witness (readTarget source callee)
  let signature := target.val.resolved.signature
  let body ← NaturalAffine.witness (SourceRuntimeTrace.readBodyWithSignature signature)
  let bases := roles call.places
  exactWork (Exact.charge (64*(Raw.OwnerFlow.fields (RuntimeAccessInterval.roles call.places)+1)))
  if inputTypes : signature.parameters.map (·.tree) = bases.map Semantics.RuntimeType.owner then
    if outputType : signature.result.tree = outputShape call.places then
      if unitary : SourceEffect.visible owner target.val.resolved.resolution.moduleName
          signature.original.declaration.isPublic signature.original.parsedHeader.effect
          body.val.checked.summary.generic.inferredEffect = .unitary then
        let entry ← NaturalAffine.witness (RuntimeSourceBoundary.bindings
          (body.val.checked.summary.parameterValues.flatMap valueOwners)
          ((call.frame.selected.zip bases).map fun (port,basis) => ⟨port,basis⟩))
        let execution ← RuntimePureBody.check artifact root body.val call.fragment request entry.val
        return ⟨occurrence.down,target.val,by with_reducible exact target.property,body.val,
          by with_reducible exact body.property,inputTypes,outputType,unitary,entry.val,
          by with_reducible exact entry.property,execution⟩
      else throw .request
    else throw .request
  else throw .request

private def finalEnvironment (entry : List RuntimeAccessSource.Parameter) : Semantics.SourceOwners.Environment :=
  entry.zipIdx.map fun (parameter,index) =>
    ⟨parameter.original.binder.text,[.owner ⟨index,parameter.original.basis.map RuntimeAccessInterval.carrier⟩]⟩

private def finish (tokens : List LocatedToken) (entry : List RuntimeAccessSource.Parameter)
    (restored : List Semantics.Raw.Port) (parts : QuantumSignatureCore.ResultParts)
    (bases : List Semantics.FiniteCarrier.Basis) : Option (List Nat) := do
  let (value,remaining) ← (QuantumMoves.eval (tokens.map (·.text)) (finalEnvironment entry)).toOption
  let owners := Semantics.SourceOwners.valueOwners value
  if !remaining.isEmpty || !QuantumBody.resultShape parts value || owners.map (·.basis) != bases then none else
    owners.mapM fun owner => do
      let port ← restored[owner.ordinal]?
      return port.token

structure Pair {artifact : Artifact} {root : Validity.Root} {owner name signature}
    {block : RuntimeInterval.Prepared root.dependencies root.program}
    {source : @RuntimeAccessSource.Checked artifact.sources owner name root.dependencies root.program signature block}
    {firstStart firstCount firstInputs firstOutputs start count inputs outputs}
    {first : RuntimeAccessPartition.Checked source firstStart firstCount firstInputs firstOutputs}
    (second : RuntimeAccessPartition.Second first start count inputs outputs) (firstRequest secondRequest : Context) where
  firstBody : Checked source first.call.interval firstRequest
  secondBody : Checked source second.call secondRequest
  firstSectors : RuntimeAccessInterval.Sectors first.call.interval
  secondSectors : RuntimeAccessInterval.Sectors second.call
  finalOffset : start+count+RuntimeAccessPartition.routingCount second.call.places = root.program.operations.length
  finalReturn : finish source.calls.second.suffix source.entry second.owners.restored
    signature.parts signature.outputs = some root.program.outputs

/-- This proof component covers exactly two original adjacent calls followed by
a structural return. Both common-body checks use the same checked root and
their actual fragments. Each control mask is derived from the written places. -/
def readPair {artifact : Artifact} {owner name signature} (root : Validity.Root)
    {block : RuntimeInterval.Prepared root.dependencies root.program}
    {source : @RuntimeAccessSource.Checked artifact.sources owner name root.dependencies root.program signature block}
    {firstStart firstCount firstInputs firstOutputs start count inputs outputs}
    {first : RuntimeAccessPartition.Checked source firstStart firstCount firstInputs firstOutputs}
    (second : RuntimeAccessPartition.Second first start count inputs outputs) (firstRequest secondRequest : Context) :
    WorkM (Pair second firstRequest secondRequest) := do
  exactWork (Exact.charge (32*(source.calls.second.suffix.length+source.entry.length+1)^2))
  if finalOffset : start+count+RuntimeAccessPartition.routingCount second.call.places = root.program.operations.length then
    if finalReturn : finish source.calls.second.suffix source.entry second.owners.restored
        signature.parts signature.outputs = some root.program.outputs then
      let firstBody ← read root source first.call.interval firstRequest
      let secondBody ← read root source second.call secondRequest
      let firstSectors ← RuntimeAccessInterval.checkSectors first.call.interval
      let secondSectors ← RuntimeAccessInterval.checkSectors second.call
      return ⟨firstBody,secondBody,firstSectors,secondSectors,finalOffset,finalReturn⟩
    else throw .request
  else throw .request

end QleisliKernel.Qirf.RuntimeAccessCallee
