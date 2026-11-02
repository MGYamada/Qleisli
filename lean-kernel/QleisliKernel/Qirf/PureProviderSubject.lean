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

abbrev Computed {α : Type} (action : WorkM α) (value : α) : Prop :=
  ∃ work left, action.run work = (.ok value,left)

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

structure Equations (effect : Semantics.Raw.Effect) (inputCode outputCode physical : Matrix) where
  physicalShape : physical.cols = inputCode.rows ∧ physical.rows = outputCode.rows
  action : Matrix
  actionRead : Computed (logical physical inputCode outputCode) action
  isometryRead : Computed (exactWork (Exact.Matrix.isometryWork action)) true
  unitaryShape : effect = .unitary → action.rows = action.cols
  actual : Matrix
  actualRead : Computed (exactWork (Exact.Matrix.composeWork physical inputCode)) actual
  specified : Matrix
  specifiedRead : Computed (exactWork (Exact.Matrix.composeWork outputCode action)) specified
  noLeak : actual = specified

/-- Retain concrete values and their actual run equations separately. No
projection must infer a monadic result type by unfolding the whole checker. -/
structure Prepared {sources} (provider : StaticOperation.Provider sources)
    (dependencies : List Semantics.Finite.Dependency) (program : Semantics.Observation.Program) where
  verified : Raw.Observation.Checked
  verification : Computed (Raw.Observation.verify dependencies program) verified
  ports : Ports provider program verified
  inputCode : Matrix
  outputCode : Matrix
  inputCodeRead : Computed (Carrier.ownerCode [⟨ports.input,ports.domain⟩]) inputCode
  outputCodeRead : Computed (Carrier.ownerCode [⟨ports.output,ports.codomain⟩]) outputCode
  physical : Matrix
  physicalRead : Computed (Raw.BranchFunction.reconstruct dependencies program) physical
  equations : Equations provider.expectedEffect inputCode outputCode physical

structure Checked (artifact : Artifact) (root : Validity.Root)
    (provider : StaticOperation.Provider artifact.sources) (index : Nat) where
  program : Semantics.Observation.Program
  original : artifact.programs[index]? = some program
  prepared : Prepared provider root.dependencies program

def equations (effect : Semantics.Raw.Effect) (inputCode outputCode physical : Matrix) :
    WorkM (Equations effect inputCode outputCode physical) := do
  if physicalShape : physical.cols = inputCode.rows ∧ physical.rows = outputCode.rows then
    let action ← NaturalAffine.witness (logical physical inputCode outputCode)
    let isometry ← NaturalAffine.witness (exactWork (Exact.Matrix.isometryWork action.val))
    if gram : isometry.val = true then
      if unitaryShape : effect = .unitary → action.val.rows = action.val.cols then
        let actual ← NaturalAffine.witness (exactWork (Exact.Matrix.composeWork physical inputCode))
        let specified ← NaturalAffine.witness (exactWork (Exact.Matrix.composeWork outputCode action.val))
        exactWork (Exact.charge (actual.val.entries.length+specified.val.entries.length+1))
        if noLeak : actual.val = specified.val then
          return ⟨physicalShape,action.val,by with_reducible exact action.property,
            by simpa only [gram] using isometry.property,unitaryShape,
            actual.val,by with_reducible exact actual.property,
            specified.val,by with_reducible exact specified.property,noLeak⟩
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
                let physical ← NaturalAffine.witness (Raw.BranchFunction.reconstruct dependencies program)
                let equations ← equations provider.expectedEffect inputCode.val outputCode.val physical.val
                return ⟨verified.val,by with_reducible exact verified.property,ports,inputCode.val,outputCode.val,
                  by with_reducible exact inputCode.property,by with_reducible exact outputCode.property,
                  physical.val,by with_reducible exact physical.property,equations⟩
              else throw .request
            else throw .request
          else throw .request
        else throw .request
      else throw .request
    | _ => throw .request
  | _,_,_ => throw .request

def check (artifact : Artifact) (root : Validity.Root)
    (provider : StaticOperation.Provider artifact.sources) (index : Nat) :
    WorkM (Checked artifact root provider index) := do
  match original : artifact.programs[index]? with
  | none => throw .request
  | some program => return ⟨program,original,← prepare provider root.dependencies program⟩

theorem Checked.originalProgram {artifact root provider index} (checked : Checked artifact root provider index) :
    artifact.programs[index]? = some checked.program := checked.original

theorem Checked.noHiddenObservation {artifact root provider index} (checked : Checked artifact root provider index) :
    checked.prepared.verified.state.observe = false := checked.prepared.ports.noObservation

end QleisliKernel.Qirf.PureProviderSubject
