import QleisliKernel.Qirf.RuntimeTransformOwners
import QleisliKernel.Qirf.RuntimeTransformRequest
import QleisliKernel.Qirf.OperationIRMeaning
import QleisliKernel.Qirf.Carrier
import QleisliKernel.CodeSpace

/-! Exact native action for the independently read original transform. The
caller must check the selected forward body against its actual original
source with the common traversal before using this interval equation.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeTransformAction
open Finite SourceTypes Semantics.Exact
open SourceRuntimeValues (valueOwners)
open RuntimeInterval (Computed)

inductive Binding (artifact : Artifact)
    {caller : String} (event : SourceRuntimeContext.TransformEvent artifact.sources caller) :
    SourceProviderSubject.Subject → Nat → Type where
  | pure (index : Nat) : Binding artifact event (.pure index) index
  | function (index : Nat) (entry : Entry)
      (found : artifact.entries[index]? = some entry)
      (identity : Semantics.Function.Identity)
      (original : Computed (Qirf.identity artifact entry) identity)
      (named : identity.implementation =
        event.target.resolution.moduleName ++ "::" ++ event.target.resolution.declaration.name)
      (source : (event.target.resolution.moduleName,event.target.signature.original.source) ∈ identity.sources) :
      Binding artifact event (.function index) entry.implementation

private def readBinding (artifact : Artifact) {caller}
    (event : SourceRuntimeContext.TransformEvent artifact.sources caller)
    (subject : SourceProviderSubject.Subject) : WorkM (Σ index, Binding artifact event subject index) := do
  match subject with
  | .pure index => return ⟨index,.pure index⟩
  | .function index =>
    match found : artifact.entries[index]? with
    | none => throw .request
    | some entry =>
      let source := event.target.signature.original.source
      let name := event.target.resolution.moduleName ++ "::" ++ event.target.resolution.declaration.name
      let identity ← NaturalAffine.witness (Qirf.identity artifact entry)
      let size := (identity.val.sources.map fun row => row.1.utf8ByteSize+row.2.utf8ByteSize+1).sum
      exactWork (Exact.charge (16*(size+name.utf8ByteSize+identity.val.implementation.utf8ByteSize+
        (source.utf8ByteSize+event.target.resolution.moduleName.utf8ByteSize+1)*(identity.val.sources.length+1))))
      if named : identity.val.implementation = name then
        if bound : (event.target.resolution.moduleName,source) ∈ identity.val.sources then
          return ⟨entry.implementation,.function index entry found identity.val
            (by with_reducible exact identity.property) named bound⟩
        else throw .request
      else throw .request

def owners (bindings : RuntimeOwnerMap.Map) : List Semantics.CarrierInterface.Owner :=
  bindings.map fun binding => ⟨binding.port,binding.owner.basis⟩

def forwardBindings (roles : List Semantics.SourceOwners.Owner) (ports : List Semantics.Raw.Port) :
    RuntimeOwnerMap.Map :=
  (roles.zip ports).map fun (owner,port) => ⟨owner,port⟩

structure Forward (artifact : Artifact) (dependencies : List Semantics.Finite.Dependency)
    {caller position child} {event : SourceRuntimeContext.TransformEvent artifact.sources caller}
    (request : RuntimeTransformRequest.Checked event position child) where
  index : Nat
  binding : Binding artifact event request.subject index
  program : Semantics.Observation.Program
  original : artifact.programs[index]? = some program
  effect : program.effect = .unitary
  roles : List Semantics.SourceOwners.Owner
  sourceRoles : roles = request.source.checked.summary.parameterValues.flatMap valueOwners
  widths : RuntimeStructuralAction.widths program.inputs roles = true
  initial : RuntimeOwnerMap.Map
  bound : initial = forwardBindings roles program.inputs
  prepared : RuntimeInterval.Prepared dependencies program
  preparedRead : Computed (RuntimeInterval.prepare dependencies program) prepared

def readForward (artifact : Artifact) (dependencies : List Semantics.Finite.Dependency)
    {caller position child} {event : SourceRuntimeContext.TransformEvent artifact.sources caller}
    (request : RuntimeTransformRequest.Checked event position child) : WorkM (Forward artifact dependencies request) := do
  let ⟨index,binding⟩ ← readBinding artifact event request.subject
  match original : artifact.programs[index]? with
  | none => throw .request
  | some program =>
    let roles := request.source.checked.summary.parameterValues.flatMap valueOwners
    exactWork (Exact.charge (16*(Raw.OwnerFlow.fields roles+program.inputs.length+1)))
    if effect : program.effect = .unitary then
      if widths : RuntimeStructuralAction.widths program.inputs roles = true then
        let prepared ← NaturalAffine.witness (RuntimeInterval.prepare dependencies program)
        return ⟨index,binding,program,original,effect,roles,rfl,widths,forwardBindings roles program.inputs,rfl,
          prepared.val,by with_reducible exact prepared.property⟩
      else throw .request
    else throw .request

structure ForwardMap {artifact dependencies caller position child event request}
    (forward : @Forward artifact dependencies caller position child event request)
    (returned : RuntimeOwnerMap.Map) where
  order : returned.map (·.owner) = valueOwners request.source.checked.summary.value
  ports : returned.map (·.port.token) = forward.program.outputs
  inputCode : Matrix
  outputCode : Matrix
  inputRead : Computed (Carrier.ownerCode (owners forward.initial)) inputCode
  outputRead : Computed (Carrier.ownerCode (owners returned)) outputCode
  physical : Matrix
  physicalRead : Computed (Raw.BranchFunction.reconstruct dependencies forward.program) physical
  physicalUnitary : Computed (wholeSpace physical) ()
  code : CodeSpace.Map inputCode outputCode physical
  logicalUnitary : Computed (wholeSpace code.logical) ()

def readForwardMap {artifact dependencies caller position child event request}
    (forward : @Forward artifact dependencies caller position child event request)
    (returned : RuntimeOwnerMap.Map) : WorkM (ForwardMap forward returned) := do
  let roles := valueOwners request.source.checked.summary.value
  exactWork (Exact.charge (16*(Raw.OwnerFlow.fields (roles ++ returned.map (·.owner))+
    returned.length+forward.program.outputs.length+1)))
  if boundary : returned.map (·.owner) = roles ∧ returned.map (·.port.token) = forward.program.outputs then
    let input ← NaturalAffine.witness (Carrier.ownerCode (owners forward.initial))
    let output ← NaturalAffine.witness (Carrier.ownerCode (owners returned))
    let physical ← NaturalAffine.witness (Raw.BranchFunction.reconstruct dependencies forward.program)
    let physicalUnitary ← NaturalAffine.witness (wholeSpace physical.val)
    let code ← CodeSpace.readMap input.val output.val physical.val
    let logicalUnitary ← NaturalAffine.witness (wholeSpace code.logical)
    have physicalDone : physicalUnitary.val = () := by cases physicalUnitary.val; rfl
    have logicalDone : logicalUnitary.val = () := by cases logicalUnitary.val; rfl
    return ⟨boundary.1,boundary.2,input.val,output.val,
      by with_reducible exact input.property,by with_reducible exact output.property,
      physical.val,by with_reducible exact physical.property,
      by with_reducible simpa only [physicalDone] using physicalUnitary.property,code,
      by with_reducible simpa only [logicalDone] using logicalUnitary.property⟩
  else throw .request

def expected {sources caller} (event : SourceRuntimeContext.TransformEvent sources caller) (forward : Matrix) :
    WorkM Matrix := do
  guard (event.copies ≤ 4096) .limit
  let repeated ← if event.copies == 1 then pure forward else OperationIRMeaning.power forward event.copies
  match event.written.access with
  | .forward => pure repeated
  | .adjoint => exactWork (Exact.Matrix.adjointWork repeated)
  | .controlled => OperationIRMeaning.controlled repeated

structure Checked {dependencies program block start count sources caller}
    {interval : @RuntimeInterval.Checked dependencies program block start count}
    {event : SourceRuntimeContext.TransformEvent sources caller} {before : RuntimeStructuralAction.SourceState}
    (held : RuntimeTransformOwners.Checked interval event before) (forward : Matrix) where
  inputCode : Matrix
  outputCode : Matrix
  inputRead : Computed (Carrier.ownerCode (owners held.selected)) inputCode
  outputRead : Computed (Carrier.ownerCode (owners (RuntimeTransformOwners.assigned event held.returned))) outputCode
  actual : Matrix
  actualRead : Computed (Raw.ProtectedEvaluation.reconstruct dependencies
    (RuntimePureInterval.fragment held.literal.selected held.literal.operations (held.returned.map (·.port.token)))) actual
  original : Matrix
  originalRead : Computed (expected event forward) original
  code : CodeSpace.Map inputCode outputCode actual
  equation : code.logical = original

def read {dependencies program block start count sources caller}
    {interval : @RuntimeInterval.Checked dependencies program block start count}
    {event : SourceRuntimeContext.TransformEvent sources caller} {before : RuntimeStructuralAction.SourceState}
    (held : RuntimeTransformOwners.Checked interval event before) (forward : Matrix) :
    WorkM (Checked held forward) := do
  let input ← NaturalAffine.witness (Carrier.ownerCode (owners held.selected))
  let output ← NaturalAffine.witness (Carrier.ownerCode (owners (RuntimeTransformOwners.assigned event held.returned)))
  let actual ← NaturalAffine.witness (Raw.ProtectedEvaluation.reconstruct dependencies
    (RuntimePureInterval.fragment held.literal.selected held.literal.operations (held.returned.map (·.port.token))))
  let original ← NaturalAffine.witness (expected event forward)
  let code ← CodeSpace.readMap input.val output.val actual.val
  exactWork (Exact.charge (code.logical.entries.length+original.val.entries.length+1))
  if equal : code.logical = original.val then
    return ⟨input.val,output.val,by with_reducible exact input.property,by with_reducible exact output.property,
      actual.val,by with_reducible exact actual.property,original.val,by with_reducible exact original.property,code,equal⟩
  else throw .equation

end QleisliKernel.Qirf.RuntimeTransformAction
