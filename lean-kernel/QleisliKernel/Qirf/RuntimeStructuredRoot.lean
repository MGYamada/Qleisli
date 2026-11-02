import QleisliKernel.Qirf.RuntimeSourceBoundary
import QleisliKernel.Qirf.RuntimeFamily

/-! The complete retained runtime boundary of a structural source derivation.
This stage reuses the same original signature, Raw root and source-owner maps.
It allocates no joined code matrix. Local source/IR action, code, ordinary SSA,
history and branch proofs must still be composed before any accepted handle is
issued; a successful boundary check is not that semantic derivation.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeStructuredRoot
open QleisliKernel QleisliKernel.Finite SourceTypes

private def basisFields (basis : Semantics.FiniteCarrier.Basis) : Nat :=
  QleisliKernel.RuntimeStorage.footprint [] [.quantum ⟨⟨0,[],0⟩,basis⟩]

private def namedFields (values : List (String × Nat)) : Nat :=
  (values.map fun value => value.1.utf8ByteSize+2).sum

private def nodeFields : OperationDescription.Node → Nat
  | .primitive _ target => basisFields target+2
  | .provider owner name bases naturals operations | .formal owner name bases naturals operations _ =>
    owner.utf8ByteSize+name.utf8ByteSize+
      (bases.map fun (name,basis) => name.utf8ByteSize+basisFields basis+1).sum+
      namedFields naturals+namedFields operations+8
  | .requested _ owner name => owner.utf8ByteSize+name.utf8ByteSize+4
  | _ => 4

private def argumentFields (arguments : StaticTypes.Arguments) : Nat :=
  (arguments.bases.map fun (name,basis) => name.utf8ByteSize+basisFields basis+1).sum+
    namedFields arguments.naturals+
    (arguments.operations.map fun (name,description) =>
      name.utf8ByteSize+(description.nodes.map nodeFields).sum+2).sum

def rawEffect (root : Validity.Root) : Semantics.Raw.Effect :=
  if root.checked.state.observe then .observe else root.program.effect

structure Boundary {sources owner name signature}
    (body : @SourceRuntimeTrace.Body sources owner name signature)
    (root : Validity.Root)
    (prepared : RuntimeInterval.Prepared root.dependencies root.program)
    (request : RuntimeFamily.Request) where
  moduleName : request.moduleName = owner
  declarationName : request.declarationName = name
  externalActuals : signature.context = .external
  arguments : request.staticArguments = signature.arguments
  selection : OrdinarySignature.selectionAllowed request.selection signature.original = true
  parameterTypes : request.parameters = signature.parameters.map (·.tree)
  resultType : request.result = signature.result.tree
  inputs : RuntimeSourceBoundary.Inputs body prepared request.inputStorage
  owners : RuntimeOwnerMap.Checked
    (SourceRuntimeValues.valueOwners (RuntimeSourceBoundary.summary body).value) root.checked.state
  outputs : RuntimeSourceBoundary.Outputs (RuntimeSourceBoundary.summary body).value
    root.checked.state owners request.storage root.program.outputs
  ordinaryInputs : RuntimeInterval.Computed
    (OrdinaryFamily.storageIds ((RuntimeFamily.inputValues request).map (·.2))) root.program.classicalInputs
  ordinaryOutputs : RuntimeInterval.Computed
    (OrdinaryFamily.storageIds ((RuntimeFamily.outputValues request).map (·.2))) root.program.classicalOutputs
  annotation : RuntimeFamily.annotationAllowed signature.original.parsedHeader.effect
    signature.original.declaration.isPublic (RuntimeSourceBoundary.summary body).quantumUse request.publicEffect = true
  originalEffect : SourceEffect.rank (RuntimeSourceBoundary.summary body).generic.inferredEffect ≤
    SourceEffect.rank request.publicEffect
  actualEffect : SourceEffect.rank (rawEffect root) ≤ SourceEffect.rank request.publicEffect
  domain : OrdinaryDomain.Checked ((RuntimeFamily.inputValues request).map (·.1))
  inputRows : request.inputRows = OrdinaryDomain.assignments domain

/-- Recheck the complete final frame against this exact root. The map is
computed by the enclosing native source derivation, never a supplied wire map.
Neither equal widths nor a matching projection identifies the original result.
All existing runtime metadata and ordinary-domain capacities remain in force. -/
def readBoundary {sources owner name signature}
    (body : @SourceRuntimeTrace.Body sources owner name signature)
    (root : Validity.Root)
    (prepared : RuntimeInterval.Prepared root.dependencies root.program)
    (finalBindings : RuntimeOwnerMap.Map) (request : RuntimeFamily.Request) :
    WorkM (Boundary body root prepared request) := do
  guard (request.parameters.length ≤ 64 && request.inputStorage.length ≤ 64 &&
    (request.parameters.map List.length).sum ≤ 384 && request.result.length ≤ 384 &&
    (request.inputStorage.map List.length).sum ≤ 384 && request.storage.length ≤ 384) .limit
  let metadata := request.parameters.foldl (fun count tree =>
      count+QleisliKernel.RuntimeStorage.footprint tree [])
      (QleisliKernel.RuntimeStorage.footprint request.result request.storage)+
    request.inputStorage.foldl (fun count stored => count+QleisliKernel.RuntimeStorage.footprint [] stored) 0
  exactWork (Exact.charge (16*(metadata+argumentFields request.staticArguments+
    argumentFields signature.arguments+request.moduleName.utf8ByteSize+request.declarationName.utf8ByteSize+1)))
  if moduleName : request.moduleName = owner then
    if declarationName : request.declarationName = name then
      if externalActuals : signature.context = .external then
        if arguments : request.staticArguments = signature.arguments then
          if selection : OrdinarySignature.selectionAllowed request.selection signature.original = true then
            if parameterTypes : request.parameters = signature.parameters.map (·.tree) then
              if resultType : request.result = signature.result.tree then
                let inputs ← RuntimeSourceBoundary.readInputs body prepared request.inputStorage
                let owners ← RuntimeOwnerMap.check
                  (SourceRuntimeValues.valueOwners (RuntimeSourceBoundary.summary body).value)
                  root.checked.state finalBindings
                let outputs ← RuntimeSourceBoundary.checkOutputs body root.checked.state owners
                  request.storage root.program.outputs
                let ordinaryInputs ← NaturalAffine.witness
                  (OrdinaryFamily.storageIds ((RuntimeFamily.inputValues request).map (·.2)))
                let ordinaryOutputs ← NaturalAffine.witness
                  (OrdinaryFamily.storageIds ((RuntimeFamily.outputValues request).map (·.2)))
                if inputIds : ordinaryInputs.val = root.program.classicalInputs then
                  if outputIds : ordinaryOutputs.val = root.program.classicalOutputs then
                    if annotation : RuntimeFamily.annotationAllowed signature.original.parsedHeader.effect
                        signature.original.declaration.isPublic (RuntimeSourceBoundary.summary body).quantumUse
                        request.publicEffect = true then
                      if originalEffect : SourceEffect.rank (RuntimeSourceBoundary.summary body).generic.inferredEffect ≤
                          SourceEffect.rank request.publicEffect then
                        if actualEffect : SourceEffect.rank (rawEffect root) ≤ SourceEffect.rank request.publicEffect then
                          let domain ← OrdinaryDomain.read ((RuntimeFamily.inputValues request).map (·.1))
                          if inputRows : request.inputRows = OrdinaryDomain.assignments domain then
                            return ⟨moduleName,declarationName,externalActuals,arguments,selection,
                              parameterTypes,resultType,inputs,owners,outputs,
                              by simpa only [inputIds] using ordinaryInputs.property,
                              by simpa only [outputIds] using ordinaryOutputs.property,
                              annotation,originalEffect,actualEffect,domain,inputRows⟩
                          else throw .request
                        else throw .request
                      else throw .request
                    else throw .request
                  else throw .request
                else throw .request
              else throw .request
            else throw .request
          else throw .request
        else throw .request
      else throw .request
    else throw .request
  else throw .request

theorem Boundary.fullResultType {sources owner name signature body root prepared request}
    (boundary : @Boundary sources owner name signature body root prepared request) :
    Semantics.RuntimeStorage.typeOf request.storage = request.result := by
  rw [boundary.outputs.originalType,(RuntimeSourceBoundary.summary body).typed]
  exact boundary.resultType.symm

end QleisliKernel.Qirf.RuntimeStructuredRoot
