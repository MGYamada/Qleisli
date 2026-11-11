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

def logical (restricted outputCode : Matrix) : WorkM Matrix := do
  let outputAdjoint ← exactWork (Exact.Matrix.adjointWork outputCode)
  FiniteCarrier.codeProduct .left outputAdjoint restricted

private def readCodeProduct (side : FiniteCarrier.CodeSide) (left right : Matrix) :
    WorkM {value : Matrix // Computed (exactWork (Exact.Matrix.composeWork left right)) value} := do
  let checked ← NaturalAffine.witness (FiniteCarrier.codeProduct side left right)
  return ⟨checked.val,by
    obtain ⟨work,remaining,ran⟩ := checked.property
    obtain ⟨before,after,dense⟩ := FiniteCarrier.codeProduct_dense side left right checked.val work remaining ran
    refine ⟨before,after,?_⟩
    change (let (result,remaining) := Exact.Matrix.compose left right before
      (Finite.arithmetic result,remaining)) = _
    rw [dense]
    rfl⟩

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
  actual : Matrix
  actualRead : Computed (exactWork (Exact.Matrix.composeWork physical inputCode)) actual
  action : Matrix
  actionRead : Computed (logical actual outputCode) action
  isometryRead : Computed (exactWork (Exact.Matrix.isometryWork action)) true
  unitaryShape : effect = .unitary → action.rows = action.cols
  specified : Matrix
  specifiedRead : Computed (exactWork (Exact.Matrix.composeWork outputCode action)) specified
  noLeak : actual = specified

theorem Equations.wholeSpace {effect inputCode outputCode physical}
    (receipt : Equations effect inputCode outputCode physical) (unitary : effect = .unitary) :
    Computed (Finite.wholeSpace receipt.action) () := by
  obtain ⟨work,left,ran⟩ := receipt.isometryRead
  have square : (receipt.action.rows == receipt.action.cols) = true :=
    beq_iff_eq.mpr (receipt.unitaryShape unitary)
  refine ⟨work,left,?_⟩
  unfold Finite.wholeSpace
  rw [Finite.bind_run]
  simp only [square]
  change ((exactWork (Exact.Matrix.isometryWork receipt.action)) >>= fun iso =>
    Finite.guard iso .notIsometric).run work = _
  rw [Finite.bind_run,ran]
  rfl

/-- Literal provider ownership and purity before any code or matrix reads. -/
structure VerifiedPorts {sources} (provider : StaticOperation.Provider sources)
    (dependencies : List Semantics.Finite.Dependency) (program : Semantics.Observation.Program) where
  verified : Raw.Observation.Checked
  verification : Computed (Raw.Observation.verify dependencies program) verified
  ports : Ports provider program verified

/-- Retain concrete values and their actual run equations separately. No
projection must infer a monadic result type by unfolding the whole checker. -/
structure Prepared {sources} (provider : StaticOperation.Provider sources)
    (dependencies : List Semantics.Finite.Dependency) (program : Semantics.Observation.Program)
    extends VerifiedPorts provider dependencies program where
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

private def readIsometry (action : Matrix) :
    WorkM (PLift (Computed (exactWork (Exact.Matrix.isometryWork action)) true)) := do
  if action.rows == action.cols then
    let checked ← try
      NaturalAffine.witness (FiniteRestriction.adaptiveWholeSpace action)
    catch error =>
      match error with
      | .notIsometric => throw .equation
      | other => throw other
    return ⟨by
      obtain ⟨work,left,ran⟩ := checked.property
      have unit : checked.val = () := by cases checked.val; rfl
      obtain ⟨before,after,original⟩ :=
        FiniteRestriction.adaptiveWholeSpace_bound action work left (by simpa only [unit] using ran)
      obtain ⟨before,after,dense⟩ := (Finite.wholeSpace_conditions _ before after original).2
      refine ⟨before,after,?_⟩
      change (let (result,remaining) := Exact.Matrix.isometry action before
        (Finite.arithmetic result,remaining)) = _
      rw [dense]
      rfl⟩
  else
    let checked ← NaturalAffine.witness (exactWork (Exact.Matrix.isometryWork action))
    if accepted : checked.val = true then
      return ⟨by simpa only [accepted] using checked.property⟩
    else throw .equation

def equations (effect : Semantics.Raw.Effect) (inputCode outputCode physical : Matrix) :
    WorkM (Equations effect inputCode outputCode physical) := do
  if physicalShape : physical.cols = inputCode.rows ∧ physical.rows = outputCode.rows then
    -- The logical projection and no-leak equation use the same restriction.
    let actual ← readCodeProduct .right physical inputCode
    let action ← NaturalAffine.witness (logical actual.val outputCode)
    let isometry ← readIsometry action.val
    if unitaryShape : effect = .unitary → action.val.rows = action.val.cols then
      let specified ← readCodeProduct .left outputCode action.val
      exactWork (Exact.charge (actual.val.entries.length+specified.val.entries.length+1))
      if noLeak : actual.val = specified.val then
        return ⟨physicalShape,actual.val,actual.property,action.val,
          by with_reducible exact action.property,isometry.down,
          unitaryShape,specified.val,specified.property,noLeak⟩
      else throw .equation
    else throw .request
  else throw .request

private def withPorts {sources} (provider : StaticOperation.Provider sources)
    (dependencies : List Semantics.Finite.Dependency) (program : Semantics.Observation.Program)
    {α : Type} (consume : VerifiedPorts provider dependencies program → WorkM α) : WorkM α := do
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
                consume ⟨verified.val,by with_reducible exact verified.property,ports⟩
              else throw .request
            else throw .request
          else throw .request
        else throw .request
      else throw .request
    | _ => throw .request
  | _,_,_ => throw .request

def readPorts {sources} (provider : StaticOperation.Provider sources)
    (dependencies : List Semantics.Finite.Dependency) (program : Semantics.Observation.Program) :
    WorkM (VerifiedPorts provider dependencies program) :=
  withPorts provider dependencies program pure

def prepare {sources} (provider : StaticOperation.Provider sources)
    (dependencies : List Semantics.Finite.Dependency) (program : Semantics.Observation.Program) :
    WorkM (Prepared provider dependencies program) :=
  withPorts provider dependencies program fun checked => do
    let ports := checked.ports
    let inputCode ← NaturalAffine.witness (Carrier.ownerCode [⟨ports.input,ports.domain⟩])
    let outputCode ← NaturalAffine.witness (Carrier.ownerCode [⟨ports.output,ports.codomain⟩])
    let physical ← NaturalAffine.witness (Raw.BranchFunction.reconstruct dependencies program)
    let equations ← equations provider.expectedEffect inputCode.val outputCode.val physical.val
    return ⟨checked,inputCode.val,outputCode.val,by with_reducible exact inputCode.property,
      by with_reducible exact outputCode.property,physical.val,by with_reducible exact physical.property,equations⟩

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
