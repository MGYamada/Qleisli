import QleisliKernel.Qirf.Carrier
import QleisliKernel.Qirf.PureInterval
import QleisliKernel.SourceTypes.StaticOperation

/-! Typed rectangular provider IR under one already checked final graph.
The actual original domain and codomain remain distinct. Codes, Gram and
no-leak equations are checked without a replacement root or supplied matrix.
Original source-body preservation and required inverse/control realization
remain additional enclosing obligations; this component issues no handle.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.PureProviderSubject
open QleisliKernel QleisliKernel.Qirf QleisliKernel.SourceTypes Finite
open Semantics.Exact Semantics.CarrierInterface

def logical (physical inputCode outputCode : Matrix) : WorkM Matrix := do
  let restricted ← exactWork (Exact.Matrix.composeWork physical inputCode)
  let outputAdjoint ← exactWork (Exact.Matrix.adjointWork outputCode)
  exactWork (Exact.Matrix.composeWork outputAdjoint restricted)

structure Checked {artifact order rows roots}
    (root : QleisliKernel.Qirf.PureInterval.Witness (Validity.checkRootFromRoots artifact order rows roots))
    (provider : StaticOperation.Provider artifact.sources) (index : Nat) where
  program : Semantics.Observation.Program
  original : artifact.programs[index]? = some program
  verified : QleisliKernel.Qirf.PureInterval.Witness (Raw.Observation.verify root.val.dependencies program)
  domain : Semantics.FiniteCarrier.Basis
  codomain : Semantics.FiniteCarrier.Basis
  sourceInputs : provider.signature.inputs = [domain]
  sourceOutputs : provider.signature.outputs = [codomain]
  input : Semantics.Raw.Port
  output : Semantics.Raw.Port
  inputPort : program.inputs = [input]
  outputPort : program.outputs = [output.token]
  live : verified.val.state.quantum.live = [output]
  noClassical : program.classicalInputs = [] ∧ program.classicalOutputs = []
  noObservation : verified.val.state.observe = false
  publicBoundary : provider.internalInference = true ∨
    program.effect = .unitary ∨ program.effect = .iso
  pureExpected : provider.expectedEffect ≠ .observe
  inputCode : QleisliKernel.Qirf.PureInterval.Witness (Carrier.ownerCode [⟨input,domain⟩])
  outputCode : QleisliKernel.Qirf.PureInterval.Witness (Carrier.ownerCode [⟨output,codomain⟩])
  physical : QleisliKernel.Qirf.PureInterval.Witness (Raw.BranchFunction.reconstruct root.val.dependencies program)
  physicalShape : physical.val.cols = inputCode.val.rows ∧ physical.val.rows = outputCode.val.rows
  action : QleisliKernel.Qirf.PureInterval.Witness (logical physical.val inputCode.val outputCode.val)
  isometry : QleisliKernel.Qirf.PureInterval.Witness (exactWork (Exact.Matrix.isometryWork action.val))
  gram : isometry.val = true
  unitaryShape : provider.expectedEffect = .unitary → action.val.rows = action.val.cols
  actual : QleisliKernel.Qirf.PureInterval.Witness (exactWork (Exact.Matrix.composeWork physical.val inputCode.val))
  specified : QleisliKernel.Qirf.PureInterval.Witness (exactWork (Exact.Matrix.composeWork outputCode.val action.val))
  noLeak : actual.val = specified.val

/-- The enclosing graph must list this actual program as a subject. Repeating
the Raw decision under the final dependencies is not a new graph/root decision,
and a historical matrix/cache cannot provide any field of this result. -/
def check {artifact order rows roots}
    (root : QleisliKernel.Qirf.PureInterval.Witness (Validity.checkRootFromRoots artifact order rows roots))
    (provider : StaticOperation.Provider artifact.sources) (index : Nat) :
    WorkM (Checked root provider index) := do
  match original : artifact.programs[index]? with
  | none => throw .request
  | some program =>
    let verified ← NaturalAffine.witness (Raw.Observation.verify root.val.dependencies program)
    match sourceInputs : provider.signature.inputs, sourceOutputs : provider.signature.outputs,
        inputPort : program.inputs, outputTokens : program.outputs with
    | [domain],[codomain],[input],[outputToken] =>
      match live : verified.val.state.quantum.live with
      | [output] =>
        if outputPort : program.outputs = [output.token] then
          if noClassical : program.classicalInputs = [] ∧ program.classicalOutputs = [] then
            if noObservation : verified.val.state.observe = false then
              if publicBoundary : provider.internalInference = true ∨
                  program.effect = .unitary ∨ program.effect = .iso then
                if pureExpected : provider.expectedEffect ≠ .observe then
                  let inputCode ← NaturalAffine.witness (Carrier.ownerCode [⟨input,domain⟩])
                  let outputCode ← NaturalAffine.witness (Carrier.ownerCode [⟨output,codomain⟩])
                  let physical ← NaturalAffine.witness (Raw.BranchFunction.reconstruct root.val.dependencies program)
                  if physicalShape : physical.val.cols = inputCode.val.rows ∧ physical.val.rows = outputCode.val.rows then
                    let action ← NaturalAffine.witness (logical physical.val inputCode.val outputCode.val)
                    let isometry ← NaturalAffine.witness (exactWork (Exact.Matrix.isometryWork action.val))
                    if gram : isometry.val = true then
                      if unitaryShape : provider.expectedEffect = .unitary → action.val.rows = action.val.cols then
                        let actual ← NaturalAffine.witness (exactWork (Exact.Matrix.composeWork physical.val inputCode.val))
                        let specified ← NaturalAffine.witness (exactWork (Exact.Matrix.composeWork outputCode.val action.val))
                        exactWork (Exact.charge (actual.val.entries.length+specified.val.entries.length+1))
                        if noLeak : actual.val = specified.val then
                          return ⟨program,original,verified,domain,codomain,sourceInputs,sourceOutputs,input,output,
                            inputPort,outputPort,live,noClassical,noObservation,publicBoundary,pureExpected,
                            inputCode,outputCode,physical,physicalShape,action,isometry,gram,unitaryShape,actual,specified,noLeak⟩
                        else throw .equation
                      else throw .request
                    else throw .equation
                  else throw .request
                else throw .request
              else throw .request
            else throw .request
          else throw .request
        else throw .request
      | _ => throw .request
    | _,_,_,_ => throw .request

theorem Checked.originalProgram {artifact order rows roots provider index}
    {root : QleisliKernel.Qirf.PureInterval.Witness (Validity.checkRootFromRoots artifact order rows roots)}
    (checked : Checked root provider index) : artifact.programs[index]? = some checked.program := checked.original

theorem Checked.noHiddenObservation {artifact order rows roots provider index}
    {root : QleisliKernel.Qirf.PureInterval.Witness (Validity.checkRootFromRoots artifact order rows roots)}
    (checked : Checked root provider index) : checked.verified.val.state.observe = false := checked.noObservation

end QleisliKernel.Qirf.PureProviderSubject
