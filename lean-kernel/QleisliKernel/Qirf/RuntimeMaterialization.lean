import QleisliKernel.Qirf.RuntimeInterval
import QleisliKernel.Qirf.NominalSector
import QleisliKernel.CodeSpace

/-! Concrete local inverse/control programs checked under the final dependencies.
This stage checks the actual materialized Raw fragments and exact code/action
relations. It supplies no source access: the enclosing original body derivation
must establish Unitary inference and discharge every demanded nested path,
including unused and zero-power children. No final cancellation can do so.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeMaterialization
open QleisliKernel QleisliKernel.Finite Semantics.Exact Semantics.Finite
open RuntimeInterval (Computed)

private def inverseStep (step : Step) : WorkM Step := do
  match step.action with
  | .hadamard _ => return step
  | .contract axes index adjoint => return ⟨step.controls,.contract axes index (!adjoint)⟩
  | .monomial axes permutation phases =>
    guard (permutation.length == phases.length && permutation.length ≤ 64 &&
      decide (permutation.Perm (List.range permutation.length))) .request
    exactWork (Exact.charge (8*(permutation.length+1)^2))
    let inverse := (List.range permutation.length).map permutation.idxOf
    let phases := inverse.map fun original => (8-(phases[original]?.getD 0)%8)%8
    return ⟨step.controls,.monomial axes inverse phases⟩

private def controlledStep (step : Step) : Step :=
  let action := match step.action with
    | .hadamard target => .hadamard (target+1)
    | .contract axes index adjoint => .contract (axes.map (·+1)) index adjoint
    | .monomial axes permutation phases => .monomial (axes.map (·+1)) permutation phases
  ⟨⟨0,true⟩ :: step.controls.map (fun control => ⟨control.index+1,control.whenOne⟩),action⟩

def program (bits : Nat) (steps : List Step) : Semantics.Raw.Program :=
  let inputs := [⟨0,List.range bits,bits⟩]
  if steps.isEmpty then ⟨inputs,[],[0],.unitary⟩
  else ⟨inputs,[.applyUnitary 0 1 steps],[1],.unitary⟩

/-- Two separate owners are retained, including the zero-wire target. The
canonical join/apply/split is checked as actual Raw rather than a width alias. -/
def controlledProgram (bits : Nat) (steps : List Step) : Semantics.Raw.Program :=
  ⟨[⟨0,[0],1⟩,⟨1,(List.range bits).map (·+1),bits⟩],
    [.join 0 1 2,.applyUnitary 2 3 (steps.map controlledStep),.split 3 4 5 1],
    [4,5],.unitary⟩

structure Forward (dependencies : List Dependency) (original : Semantics.Observation.Program) where
  verified : Raw.Observation.Checked
  verifiedRead : Computed (Raw.Observation.verify dependencies original) verified
  noObservation : verified.state.observe = false
  noOrdinary : original.classicalInputs = [] ∧ original.classicalOutputs = []
  input : Semantics.Raw.Port
  inputPort : original.inputs = [input]
  bits : Nat
  width : input.bits = bits ∧ verified.state.quantum.frame.length = bits
  selected : List Semantics.Raw.Event
  selectedRead : Computed (do
    let (_,events) ← Raw.BranchFunction.selected 65 verified.prepared.events []
    return events) selected
  steps : List Step
  extracted : selected.mapM Semantics.Function.extracted = some (selected.map fun event =>
    (Semantics.Function.extracted event).getD [])
  flattened : steps = (selected.map fun event => (Semantics.Function.extracted event).getD []).flatten
  prepared : Raw.Prepared
  preparation : Computed (Raw.Pure.verify dependencies (program bits steps)) prepared
  physical : Matrix
  physicalRead : Computed (Raw.BranchFunction.reconstruct dependencies original) physical
  materialized : Matrix
  materializedRead : Computed (Raw.ProtectedEvaluation.reconstruct dependencies (program bits steps)) materialized
  sameOperator : materialized = physical

/-- Closed classical branches are selected only after the original Raw reader
checks both arms. Erasure, workspace insertion, mismatched physical ports and
unsupported extraction refuse here; they never acquire an inverse fallback. -/
def readForward (dependencies : List Dependency) (original : Semantics.Observation.Program) :
    WorkM (Forward dependencies original) := do
  let verified ← SourceTypes.NaturalAffine.witness (Raw.Observation.verify dependencies original)
  if noObservation : verified.val.state.observe = false then
    if noOrdinary : original.classicalInputs = [] ∧ original.classicalOutputs = [] then
      match inputPort : original.inputs with
      | [input] =>
        let bits := input.bits
        guard (bits ≤ 6) .limit
        if width : input.bits = bits ∧ verified.val.state.quantum.frame.length = bits then
          let selected ← SourceTypes.NaturalAffine.witness (do
            let (_,events) ← Raw.BranchFunction.selected 65 verified.val.prepared.events []
            return events)
          exactWork (Exact.charge (16*(selected.val.length+1)))
          if extracted : selected.val.mapM Semantics.Function.extracted = some (selected.val.map fun event =>
              (Semantics.Function.extracted event).getD []) then
            let steps := (selected.val.map fun event => (Semantics.Function.extracted event).getD []).flatten
            guard (steps.length ≤ 1024) .limit
            let prepared ← SourceTypes.NaturalAffine.witness (Raw.Pure.verify dependencies (program bits steps))
            let physical ← SourceTypes.NaturalAffine.witness (Raw.BranchFunction.reconstruct dependencies original)
            let materialized ← SourceTypes.NaturalAffine.witness
              (Raw.ProtectedEvaluation.reconstruct dependencies (program bits steps))
            exactWork (Exact.charge (physical.val.entries.length+materialized.val.entries.length+1))
            if sameOperator : materialized.val = physical.val then
              return ⟨verified.val,by with_reducible exact verified.property,noObservation,noOrdinary,
                input,inputPort,bits,width,selected.val,by with_reducible exact selected.property,steps,
                extracted,rfl,prepared.val,by with_reducible exact prepared.property,
                physical.val,by with_reducible exact physical.property,
                materialized.val,by with_reducible exact materialized.property,sameOperator⟩
            else throw .equation
          else throw .request
        else throw .request
      | _ => throw .request
    else throw .request
  else throw .request

structure Inverse {dependencies original} (forward : Forward dependencies original)
    (inputCode outputCode logical : Matrix) where
  steps : List Step
  transformed : Computed (forward.steps.reverse.mapM inverseStep) steps
  prepared : Raw.Prepared
  preparedRead : Computed (Raw.Pure.verify dependencies (program forward.bits steps)) prepared
  physical : Matrix
  physicalRead : Computed (Raw.ProtectedEvaluation.reconstruct dependencies (program forward.bits steps)) physical
  expectedPhysical : Matrix
  physicalAdjoint : Computed (exactWork (Exact.Matrix.adjointWork forward.physical)) expectedPhysical
  exactPhysical : physical = expectedPhysical
  expectedLogical : Matrix
  logicalAdjoint : Computed (exactWork (Exact.Matrix.adjointWork logical)) expectedLogical
  code : CodeSpace.Map outputCode inputCode physical
  exactLogical : code.logical = expectedLogical

def readInverse {dependencies original} (forward : Forward dependencies original)
    (inputCode outputCode logical : Matrix) : WorkM (Inverse forward inputCode outputCode logical) := do
  exactWork (Exact.charge (16*(forward.steps.length+1)))
  let steps ← SourceTypes.NaturalAffine.witness (forward.steps.reverse.mapM inverseStep)
  let prepared ← SourceTypes.NaturalAffine.witness (Raw.Pure.verify dependencies (program forward.bits steps.val))
  let physical ← SourceTypes.NaturalAffine.witness
    (Raw.ProtectedEvaluation.reconstruct dependencies (program forward.bits steps.val))
  let expectedPhysical ← SourceTypes.NaturalAffine.witness (exactWork (Exact.Matrix.adjointWork forward.physical))
  exactWork (Exact.charge (physical.val.entries.length+expectedPhysical.val.entries.length+1))
  if exactPhysical : physical.val = expectedPhysical.val then
    let expectedLogical ← SourceTypes.NaturalAffine.witness (exactWork (Exact.Matrix.adjointWork logical))
    let code ← CodeSpace.readMap outputCode inputCode physical.val
    exactWork (Exact.charge (code.logical.entries.length+expectedLogical.val.entries.length+1))
    if exactLogical : code.logical = expectedLogical.val then
      return ⟨steps.val,by with_reducible exact steps.property,prepared.val,
        by with_reducible exact prepared.property,physical.val,by with_reducible exact physical.property,
        expectedPhysical.val,by with_reducible exact expectedPhysical.property,exactPhysical,
        expectedLogical.val,by with_reducible exact expectedLogical.property,code,exactLogical⟩
    else throw .equation
  else throw .equation

structure Controlled {dependencies original} (forward : Forward dependencies original)
    (inputCode outputCode logical : Matrix) where
  prepared : Raw.Prepared
  preparedRead : Computed (Raw.Pure.verify dependencies (controlledProgram forward.bits forward.steps)) prepared
  sectors : Raw.Sector.Retained
  sectorRead : Computed (Raw.Sector.read dependencies [.bit] [.bits forward.bits]
    (controlledProgram forward.bits forward.steps)) sectors
  identity : Matrix
  identityRead : Exact.Matrix.identity logical.rows = .ok identity
  logicals : List Matrix
  equations : Computed (NominalSector.checkLogicals inputCode outputCode sectors.sectors [0,1]
    [identity,logical]) logicals

/-- The extra control uses the existing structural restriction checker. A
six-bit leaf therefore needs two local sectors, never a dense 128-square map.
Both the inactive identity and active exact-phase code equations are checked. -/
def readControlled {dependencies original} (forward : Forward dependencies original)
    (inputCode outputCode logical : Matrix) : WorkM (Controlled forward inputCode outputCode logical) := do
  let prepared ← SourceTypes.NaturalAffine.witness
    (Raw.Pure.verify dependencies (controlledProgram forward.bits forward.steps))
  let sectors ← SourceTypes.NaturalAffine.witness (Raw.Sector.read dependencies [.bit] [.bits forward.bits]
    (controlledProgram forward.bits forward.steps))
  exactWork (Exact.charge (logical.rows*logical.rows+1))
  match identityRead : Exact.Matrix.identity logical.rows with
  | .error _ => throw .limit
  | .ok identity =>
    let logicals ← SourceTypes.NaturalAffine.witness
      (NominalSector.checkLogicals inputCode outputCode sectors.val.sectors [0,1] [identity,logical])
    return ⟨prepared.val,by with_reducible exact prepared.property,
      sectors.val,by with_reducible exact sectors.property,identity,identityRead,
      logicals.val,by with_reducible exact logicals.property⟩

theorem Inverse.fullCodeEquation {dependencies original forward inputCode outputCode logical}
    (inverse : @Inverse dependencies original forward inputCode outputCode logical) :
    CodeSpace.CompositionEquation outputCode inputCode inverse.physical inverse.expectedLogical := by
  rw [← inverse.exactLogical]
  exact inverse.code.equation

end QleisliKernel.Qirf.RuntimeMaterialization
