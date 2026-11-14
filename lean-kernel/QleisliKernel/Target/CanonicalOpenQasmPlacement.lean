import QleisliKernel.Target.CanonicalOpenQasmWorkspace

/-! Derive a physical placement by replaying matched prefixes of the original
closed Raw root and the decoded terminal gate word. A declared routing step
must occupy an actual SWAP instruction. Ordinary Raw SWAPs match as gates and
leave the placement alone. Source workspace operators are checked separately.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Target.CanonicalOpenQasmPlacement
open Finite Qirf
open Semantics.RawTrace (Interface)
open CanonicalOpenQasmResources (Circuit Instruction)

inductive Match where
  | original | route
  deriving BEq, DecidableEq, Repr

structure State where
  raw : Interface := {}
  locations : List Nat := []
  rawIndex : Nat := 0
  gateIndex : Nat := 0
  deriving BEq, DecidableEq, Repr

private def gateWord (circuit : Circuit) (atGate : Nat) (locations : List Nat)
    (steps : List Semantics.Finite.Step) : Option Nat := do
  let inFrame := fun (axis : Nat) => axis < locations.length
  if !steps.all (fun step => step.controls.all (inFrame ∘ (·.index)) &&
      (Finite.targets step.action).all inFrame) then none else
  let word := (circuit.gates.drop atGate).take steps.length
  if word.map Instruction.step == steps.map (Semantics.RawTrace.localize locations) then
    some (atGate+steps.length)
  else none

private def fresh (capacity : Nat) (locations : List Nat) : Option (List Nat) :=
  ((List.range capacity).find? fun axis => !locations.contains axis).map (fun wire => locations ++ [wire])

private def followRaw (circuit : Circuit) (state : State) (operation : Semantics.Raw.Op) : Option State := do
  let (next,events) ← Semantics.RawTrace.step state.raw operation
  let (locations,gateIndex) ← match events with
    | [] => some (state.locations,state.gateIndex)
    | [.init0 _] => (fresh circuit.qubits state.locations).map (·,state.gateIndex)
    | [.liftBasis before after [] [axis] [0]] =>
      if after == before+1 && axis == before then
        (fresh circuit.qubits state.locations).map (·,state.gateIndex)
      else none
    | [.circuit _ steps] =>
      (gateWord circuit state.gateIndex state.locations steps).map (state.locations,·)
    | _ => none
  if next.frame.length == locations.length then
    some ⟨next,locations,state.rawIndex+1,gateIndex⟩
  else none

private def followSwap (circuit : Circuit) (connected : Nat → Nat → Bool) (state : State) : Option State := do
  let some ⟨.swap,[first,second]⟩ := circuit.gates[state.gateIndex]? | none
  if first != second && first < circuit.qubits && second < circuit.qubits && connected first second then
    let move : Routing.Swap := ⟨first,second⟩
    some {state with locations := state.locations.map move.axis, gateIndex := state.gateIndex+1}
  else none

def replay (original : Array Semantics.Observation.Op) (circuit : Circuit) (connected : Nat → Nat → Bool)
    (alignment : List Match) : Option State :=
  alignment.foldlM (fun state action => match action with
    | .route => followSwap circuit connected state
    | .original => do
      let some (.pure operation) := original[state.rawIndex]? | none
      followRaw circuit state operation) {}

structure Checked {bytes capacity} (target : CanonicalOpenQasmResources.Checked bytes capacity)
    (program : Semantics.Observation.Program) (connected : Nat → Nat → Bool)
    (alignment : List Match) where
  closed : program.inputs.isEmpty = true ∧ program.classicalInputs.isEmpty = true
  state : State
  actual : replay program.operations.toArray target.circuit connected alignment = some state

def check {bytes capacity} (target : CanonicalOpenQasmResources.Checked bytes capacity)
    (program : Semantics.Observation.Program) (connected : Nat → Nat → Bool) (alignment : List Match) :
    WorkM (Checked target program connected alignment) := do
  guard (program.operations.length ≤ 65536 && alignment.length ≤ 65536) .limit
  exactWork (Exact.charge (32*(1+program.operations.length) +
    32*(1+alignment.length)*(1+alignment.length+target.circuit.gates.length)))
  if closed : program.inputs.isEmpty = true ∧ program.classicalInputs.isEmpty = true then
    match original : replay program.operations.toArray target.circuit connected alignment with
    | some state => return ⟨closed,state,original⟩
    | none => throw .request
  else throw .request

/-- Retain the exact original prefix coordinates used to derive placement. -/
structure WorkspaceBinding {sources caller dependencies program block sourceStart sourceCount event events original
    sourceInterval sourceBefore}
    {literal : @RuntimeWorkspace.Literal sources caller dependencies program block
      sourceStart sourceCount event events original sourceInterval sourceBefore}
    (map : RuntimeWorkspace.CallerMap literal) {bytes capacity}
    {target : CanonicalOpenQasmResources.Checked bytes capacity} {connected alignment}
    (prefixCheck : Checked target program connected alignment) (count : Nat) where
  operations : ObservationBinding.lists (ObservationBinding.operation 65) block.operations program.operations = true
  offset : prefixCheck.state.rawIndex = sourceStart
  sameFrame : prefixCheck.state.raw = sourceInterval.before.quantum.reference
  placed : CanonicalOpenQasmWorkspace.Placed map target prefixCheck.state.locations prefixCheck.state.gateIndex count

theorem WorkspaceBinding.originalOperations {sources caller dependencies program block sourceStart sourceCount event
    events original sourceInterval sourceBefore}
    {literal : @RuntimeWorkspace.Literal sources caller dependencies program block
      sourceStart sourceCount event events original sourceInterval sourceBefore}
    {map : RuntimeWorkspace.CallerMap literal} {bytes capacity}
    {target : CanonicalOpenQasmResources.Checked bytes capacity} {connected alignment}
    {prefixCheck : Checked target program connected alignment} {count}
    (binding : WorkspaceBinding map prefixCheck count) : block.operations = program.operations :=
  ObservationBinding.lists_sound (ObservationBinding.operation 65) (ObservationBinding.operation_sound 65)
    _ _ binding.operations

/-- A root interval can take its placement only from the checked, literal
prefix ending at that exact Raw operation and target gate. The checked
original frame includes every port, including zero-width owners. -/
def workspace {sources caller dependencies program block sourceStart sourceCount event events original
    sourceInterval sourceBefore}
    {literal : @RuntimeWorkspace.Literal sources caller dependencies program block
      sourceStart sourceCount event events original sourceInterval sourceBefore}
    (map : RuntimeWorkspace.CallerMap literal) {bytes capacity}
    {target : CanonicalOpenQasmResources.Checked bytes capacity} {connected alignment}
    (prefixCheck : Checked target program connected alignment)
    (count : Nat) (scratch : Option Nat) :
    WorkM (WorkspaceBinding map prefixCheck count) := do
  exactWork (Exact.charge (16*(program.operations.length+block.operations.length+1)))
  if bound : ObservationBinding.lists (ObservationBinding.operation 65) block.operations program.operations = true ∧
      prefixCheck.state.rawIndex = sourceStart ∧
      prefixCheck.state.raw = sourceInterval.before.quantum.reference then
    let placed ← CanonicalOpenQasmWorkspace.checkPlacement map target prefixCheck.state.locations
      prefixCheck.state.gateIndex count scratch
    return ⟨bound.1,bound.2.1,bound.2.2,placed⟩
  else throw .request

end QleisliKernel.Target.CanonicalOpenQasmPlacement
