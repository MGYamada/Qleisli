import QleisliKernel.Qirf.RuntimeProviderHeader
import QleisliKernel.Qirf.RuntimeMaterialization
import QleisliKernel.SourceTypes.OperationAccess

/-! Discharge demanded local implementation paths for an original provider.
The actual forward, inverse and control programs use one final dependency root.
Original whole-body inference is checked independently of Gram/equality facts.
Complete source/IR traversal and nested access obligations remain mandatory;
this component alone issues no operation capability or execution authority.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeProviderPaths
open QleisliKernel QleisliKernel.Finite QleisliKernel.SourceTypes

inductive Realization {artifact context description graph index request}
    (header : @RuntimeProviderHeader.Header artifact context description graph index request)
    (root : Validity.Root) (ir : RuntimeProviderHeader.IR header root) (demand : StaticOperation.Paths) where
  | forwardOnly (noInverse : demand.adjointable = false) (noControl : demand.controllable = false) :
      Realization header root ir demand
  | transformed
      (originalUnitary : header.original.body.checked.summary.generic.inferredEffect = .unitary)
      (closedUnitary : header.original.body.checked.summary.inferredEffect = .unitary)
      (visibleUnitary : header.original.supplied.provider.expectedEffect = .unitary)
      (controlPorts : demand.controllable = true →
        header.original.supplied.provider.signature.inputs = header.original.supplied.provider.signature.outputs)
      (forward : RuntimeMaterialization.Forward root.dependencies ir.original.program)
      (inverse : Option (RuntimeMaterialization.Inverse forward ir.original.prepared.inputCode
        ir.original.prepared.outputCode ir.original.prepared.equations.action))
      (inverseDemand : inverse.isSome = demand.adjointable)
      (controlled : Option (RuntimeMaterialization.Controlled forward ir.original.prepared.inputCode
        ir.original.prepared.outputCode ir.original.prepared.equations.action))
      (controlDemand : controlled.isSome = demand.controllable) : Realization header root ir demand

structure Checked {artifact context description graph index request}
    (header : @RuntimeProviderHeader.Header artifact context description graph index request)
    (root : Validity.Root) (demand : StaticOperation.Paths) where
  originalEffect : SourceEffect.permits (some header.original.supplied.provider.expectedEffect)
    header.original.body.checked.summary.generic.inferredEffect = true
  closedEffect : SourceEffect.permits (some header.original.supplied.provider.expectedEffect)
    header.original.body.checked.summary.inferredEffect = true
  ir : RuntimeProviderHeader.IR header root
  paths : Realization header root ir demand

def read {artifact context description graph index request}
    (header : @RuntimeProviderHeader.Header artifact context description graph index request)
    (root : Validity.Root) (demand : StaticOperation.Paths) : WorkM (Checked header root demand) := do
  let provider := header.original.supplied.provider
  let source := header.original.body.checked
  if effects : SourceEffect.permits (some provider.expectedEffect) source.summary.generic.inferredEffect = true ∧
      SourceEffect.permits (some provider.expectedEffect) source.summary.inferredEffect = true then
    let ir ← RuntimeProviderHeader.readIR header root
    if plain : demand.adjointable = false ∧ demand.controllable = false then
      return ⟨effects.1,effects.2,ir,.forwardOnly plain.1 plain.2⟩
    else
      if unitary : source.summary.generic.inferredEffect = .unitary ∧
          source.summary.inferredEffect = .unitary ∧ provider.expectedEffect = .unitary then
        if controlPorts : demand.controllable = true → provider.signature.inputs = provider.signature.outputs then
          let prepared := ir.original.prepared
          let forward ← RuntimeMaterialization.readForwardWithOriginal
            ⟨prepared.verified,prepared.verification⟩ ⟨prepared.physical,prepared.physicalRead⟩
          let inverseAction : WorkM (Option (RuntimeMaterialization.Inverse forward ir.original.prepared.inputCode
              ir.original.prepared.outputCode ir.original.prepared.equations.action)) :=
            if demand.adjointable then do
              let value ← RuntimeMaterialization.readInverse forward ir.original.prepared.inputCode
                ir.original.prepared.outputCode ir.original.prepared.equations.action
              pure (some value)
            else pure none
          let inverse ← inverseAction
          let controlledAction : WorkM (Option (RuntimeMaterialization.Controlled forward ir.original.prepared.inputCode
              ir.original.prepared.outputCode ir.original.prepared.equations.action)) :=
            if demand.controllable then do
              let value ← RuntimeMaterialization.readControlled forward prepared.inputCode
                prepared.outputCode prepared.equations.action
                (some ⟨prepared.equations.wholeSpace unitary.2.2⟩)
              pure (some value)
            else pure none
          let controlled ← controlledAction
          if inverseDemand : inverse.isSome = demand.adjointable then
            if controlDemand : controlled.isSome = demand.controllable then
              return ⟨effects.1,effects.2,ir,.transformed unitary.1 unitary.2.1 unitary.2.2
                controlPorts forward inverse inverseDemand controlled controlDemand⟩
            else throw .request
          else throw .request
        else throw .request
      else throw .request
  else throw .request

end QleisliKernel.Qirf.RuntimeProviderPaths
