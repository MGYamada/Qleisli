import QleisliKernel.Qirf.Carrier
import QleisliKernel.Qirf.PureInterval
import QleisliKernel.SourceTypes.StaticOperation

/-! Typed rectangular provider IR under the enclosing final graph.
Actual original domain/codomain stay distinct. Code/Gram/no-leak checks issue no
handle, source-body theorem or inverse/control access. The enclosing caller
retains its fresh root witness; this continuation never checks another root.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.PureProviderSubject
open QleisliKernel QleisliKernel.Qirf QleisliKernel.SourceTypes Finite
open Semantics.Exact Semantics.CarrierInterface

abbrev Computed {α : Type} (action : WorkM α) := QleisliKernel.Qirf.PureInterval.Witness action

def logical (physical inputCode outputCode : Matrix) : WorkM Matrix := do
  let restricted ← exactWork (Exact.Matrix.composeWork physical inputCode)
  let outputAdjoint ← exactWork (Exact.Matrix.adjointWork outputCode)
  exactWork (Exact.Matrix.composeWork outputAdjoint restricted)

structure Ports {sources} (provider : StaticOperation.Provider sources)
    (program : Semantics.Observation.Program) (verified : Raw.Observation.Checked) where
  domain : Semantics.FiniteCarrier.Basis
  codomain : Semantics.FiniteCarrier.Basis
  sourceInputs : provider.signature.inputs = [domain]
  sourceOutputs : provider.signature.outputs = [codomain]
  input : Semantics.Raw.Port
  output : Semantics.Raw.Port
  inputPort : program.inputs = [input]
  outputPort : program.outputs = [output.token]
  live : verified.state.quantum.live = [output]
  noClassical : program.classicalInputs = [] ∧ program.classicalOutputs = []
  noObservation : verified.state.observe = false
  publicBoundary : provider.internalInference = true ∨ program.effect = .unitary ∨ program.effect = .iso
  pureExpected : provider.expectedEffect ≠ .observe

structure Codes {sources provider program verified} (ports : @Ports sources provider program verified) where
  inputCode : Computed (Carrier.ownerCode [⟨ports.input,ports.domain⟩])
  outputCode : Computed (Carrier.ownerCode [⟨ports.output,ports.codomain⟩])

structure Equations {sources provider program verified ports}
    (codes : @Codes sources provider program verified ports) (physical : Matrix) where
  physicalShape : physical.cols = codes.inputCode.val.rows ∧ physical.rows = codes.outputCode.val.rows
  action : Computed (logical physical codes.inputCode.val codes.outputCode.val)
  isometry : Computed (exactWork (Exact.Matrix.isometryWork action.val))
  gram : isometry.val = true
  unitaryShape : provider.expectedEffect = .unitary → action.val.rows = action.val.cols
  actual : Computed (exactWork (Exact.Matrix.composeWork physical codes.inputCode.val))
  specified : Computed (exactWork (Exact.Matrix.composeWork codes.outputCode.val action.val))
  noLeak : actual.val = specified.val

structure Prepared {sources} (provider : StaticOperation.Provider sources)
    (dependencies : List Semantics.Finite.Dependency) (program : Semantics.Observation.Program) where
  verified : Computed (Raw.Observation.verify dependencies program)
  ports : Ports provider program verified.val
  codes : Codes ports
  physical : Computed (Raw.BranchFunction.reconstruct dependencies program)
  equations : Equations codes physical.val

structure Checked (artifact : Artifact) (root : Validity.Root)
    (provider : StaticOperation.Provider artifact.sources) (index : Nat) where
  program : Semantics.Observation.Program
  original : artifact.programs[index]? = some program
  prepared : Prepared provider root.dependencies program

/-- Independent executable equations over an already prepared exact subject.
Separate records avoid reducing the complete graph computation in every field. -/
def equations {sources provider program verified ports}
    (codes : @Codes sources provider program verified ports) (physical : Matrix) : WorkM (Equations codes physical) := do
  if physicalShape : physical.cols = codes.inputCode.val.rows ∧ physical.rows = codes.outputCode.val.rows then
    let action ← NaturalAffine.witness (logical physical codes.inputCode.val codes.outputCode.val)
    let isometry ← NaturalAffine.witness (exactWork (Exact.Matrix.isometryWork action.val))
    if gram : isometry.val = true then
      if unitaryShape : provider.expectedEffect = .unitary → action.val.rows = action.val.cols then
        let actual ← NaturalAffine.witness (exactWork (Exact.Matrix.composeWork physical codes.inputCode.val))
        let specified ← NaturalAffine.witness (exactWork (Exact.Matrix.composeWork codes.outputCode.val action.val))
        exactWork (Exact.charge (actual.val.entries.length+specified.val.entries.length+1))
        if noLeak : actual.val = specified.val then
          return ⟨physicalShape,action,isometry,gram,unitaryShape,actual,specified,noLeak⟩
        else throw .equation
      else throw .request
    else throw .equation
  else throw .request

def prepare {sources} (provider : StaticOperation.Provider sources)
    (dependencies : List Semantics.Finite.Dependency) (program : Semantics.Observation.Program) :
    WorkM (Prepared provider dependencies program) := do
  let verified ← NaturalAffine.witness (Raw.Observation.verify dependencies program)
  match sourceInputs : provider.signature.inputs, sourceOutputs : provider.signature.outputs, inputPort : program.inputs with
  | [domain],[codomain],[input] =>
    match live : verified.val.state.quantum.live with
    | [output] =>
      if outputPort : program.outputs = [output.token] then
        if noClassical : program.classicalInputs = [] ∧ program.classicalOutputs = [] then
          if noObservation : verified.val.state.observe = false then
            if publicBoundary : provider.internalInference = true ∨ program.effect = .unitary ∨ program.effect = .iso then
              if pureExpected : provider.expectedEffect ≠ .observe then
                let ports : Ports provider program verified.val :=
                  ⟨domain,codomain,sourceInputs,sourceOutputs,input,output,inputPort,outputPort,live,
                    noClassical,noObservation,publicBoundary,pureExpected⟩
                let inputCode ← NaturalAffine.witness (Carrier.ownerCode [⟨input,domain⟩])
                let outputCode ← NaturalAffine.witness (Carrier.ownerCode [⟨output,codomain⟩])
                let codes : Codes ports := ⟨inputCode,outputCode⟩
                let physical ← NaturalAffine.witness (Raw.BranchFunction.reconstruct dependencies program)
                let equations ← equations codes physical.val
                return ⟨verified,ports,codes,physical,equations⟩
              else throw .request
            else throw .request
          else throw .request
        else throw .request
      else throw .request
    | _ => throw .request
  | _,_,_ => throw .request

/-- Only the exact retained root dependencies are consumed. The enclosing
native result retains the successful root computation and source-body proof. -/
def check (artifact : Artifact) (root : Validity.Root)
    (provider : StaticOperation.Provider artifact.sources) (index : Nat) :
    WorkM (Checked artifact root provider index) := do
  match original : artifact.programs[index]? with
  | none => throw .request
  | some program => return ⟨program,original,← prepare provider root.dependencies program⟩

theorem Checked.originalProgram {artifact root provider index} (checked : Checked artifact root provider index) :
    artifact.programs[index]? = some checked.program := checked.original

theorem Checked.noHiddenObservation {artifact root provider index} (checked : Checked artifact root provider index) :
    checked.prepared.verified.val.state.observe = false := checked.prepared.ports.noObservation

end QleisliKernel.Qirf.PureProviderSubject
