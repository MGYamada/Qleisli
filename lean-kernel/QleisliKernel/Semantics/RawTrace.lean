import QleisliKernel.Semantics.Raw

/-! Independent original-operation trace semantics. This reader records ordered
interfaces and literal action data, with no acceptance predicates, freshness
policy, budgets, cached meanings or producer receipts. Missing operands have no
trace. Full complex interpretation and clean-release validity are separate.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Semantics.RawTrace
open Raw Finite

structure Interface where
  live : List Port := []
  frame : List Nat := []
  deriving BEq, DecidableEq, Repr

deriving instance ReflBEq, LawfulBEq for Interface

def take (state : Interface) (token : Nat) : Option (Port × Interface) := do
  let port ← state.live.find? (fun port => port.token == token)
  return (port,{state with live := state.live.filter (fun port => port.token != token)})

def insert (state : Interface) (token : Nat) (wires : List Nat) : Interface :=
  {state with live := state.live ++ [⟨token,wires,wires.length⟩]}

def axes (state : Interface) (wires : List Nat) : List Nat := wires.map state.frame.idxOf

/-- Literal gate action data, independent of a checker's gate conversion. -/
def gate (value : Gate) (axis : Nat) : Step :=
  ⟨[],match value with
    | .h => .hadamard axis
    | .x => .monomial [axis] [1,0] [0,0]
    | .z => .monomial [axis] [0,1] [0,4]
    | .t => .monomial [axis] [0,1] [0,1]⟩

def unitary : UnitaryStep → Step
  | .gate value axis => gate value axis
  | .cnot control target => {gate .x target with controls := [⟨control,true⟩]}
  | .toffoli a b target => {gate .x target with controls := [⟨a,true⟩,⟨b,true⟩]}
  | .phase value => ⟨[],.monomial [] [0] [match value with | .minusOne => 4 | .eighthTurn => 1]⟩

def localize (indices : List Nat) (step : Step) : Step :=
  let axis := fun index => indices[index]?.getD 0
  ⟨step.controls.map (fun control => ⟨axis control.index,control.whenOne⟩),match step.action with
    | .hadamard target => .hadamard (axis target)
    | .monomial targets permutation phases => .monomial (targets.map axis) permutation phases
    | .contract targets dependency adjoint => .contract (targets.map axis) dependency adjoint⟩

/-- Read the meaning-bearing fields of every original pure constructor. This
neither decides admissibility nor constructs an evidence matrix. In particular,
computed events retain the actual body and requested logical data together. -/
def step (state : Interface) (op : Op) : Option (Interface × List Event) := do
  let bits := state.frame.length
  match op with
  | .init0 output wire =>
    return ({insert state output [wire] with frame := state.frame ++ [wire]},[.init0 bits])
  | .gate value input output =>
    let (port,next) ← take state input
    return (insert next output port.wires,
      [.circuit bits [gate value (state.frame.idxOf (port.wires[0]?.getD 0))]])
  | .cnot control target controlOut targetOut =>
    let (c,next) ← take state control
    let (t,next) ← take next target
    let action := {gate .x (state.frame.idxOf (t.wires[0]?.getD 0)) with
      controls := [⟨state.frame.idxOf (c.wires[0]?.getD 0),true⟩]}
    return (insert (insert next controlOut c.wires) targetOut t.wires,[.circuit bits [action]])
  | .toffoli a b target aOut bOut targetOut =>
    let (a,next) ← take state a
    let (b,next) ← take next b
    let (t,next) ← take next target
    let action := {gate .x (state.frame.idxOf (t.wires[0]?.getD 0)) with
      controls := [⟨state.frame.idxOf (a.wires[0]?.getD 0),true⟩,⟨state.frame.idxOf (b.wires[0]?.getD 0),true⟩]}
    return (insert (insert (insert next aOut a.wires) bOut b.wires) targetOut t.wires,[.circuit bits [action]])
  | .quantumIf control target controlOut targetOut zero one =>
    let (c,next) ← take state control
    let (t,next) ← take next target
    let arm (polarity : Bool) (steps : List UnitaryStep) : List Step := steps.map fun original =>
      let action := localize (axes state t.wires) (unitary original)
      {action with controls := action.controls ++ [⟨state.frame.idxOf (c.wires[0]?.getD 0),polarity⟩]}
    return (insert (insert next controlOut c.wires) targetOut t.wires,
      [.circuit bits (arm false zero ++ arm true one)])
  | .split input left right leftBits =>
    let (port,next) ← take state input
    return (insert (insert next left (port.wires.take leftBits)) right (port.wires.drop leftBits),[])
  | .join left right output =>
    let (l,next) ← take state left
    let (r,next) ← take next right
    return (insert next output (l.wires ++ r.wires),[])
  | .liftBasis input output wires table =>
    let (port,next) ← take state input
    let frame := state.frame ++ wires.drop port.bits
    return ({insert next output wires with frame},
      [.liftBasis bits frame.length (axes state port.wires) (wires.map frame.idxOf) table])
  | .applyUnitary input output steps =>
    let (port,next) ← take state input
    return (insert next output port.wires,[.circuit bits (steps.map (localize (axes state port.wires)))])
  | .certifiedCompute input output ancilla function useSteps logicalSteps =>
    let (port,next) ← take state input
    return (insert next output port.wires,
      [.computed bits (axes state port.wires) port.bits ancilla.length function useSteps logicalSteps])
  | .computeUseUncompute input output targets ancilla function uses =>
    let (source,next) ← take state input
    let (ports,next) ← targets.foldlM (fun (ports,next) target => do
      let (port,next) ← take next target.input
      pure (ports ++ [port],next)) ([],next)
    let next := insert next output source.wires
    let next := (targets.zip ports).foldl (fun next (target,port) => insert next target.output port.wires) next
    return (next,[.protectedComputed bits (axes state (source.wires ++ ports.flatMap (·.wires)))
      source.bits ancilla.length function uses])

structure Prepared where
  state : Interface
  events : List Event := []
  inputBits : Nat
  deriving BEq, DecidableEq, Repr

deriving instance ReflBEq, LawfulBEq for Prepared

def advance (prepared : Prepared) (op : Op) : Option Prepared := do
  let (next,events) ← step prepared.state op
  return {prepared with state := next,events := prepared.events ++ events}

def initial (ports : List Port) : Interface :=
  ⟨ports,ports.flatMap (·.wires)⟩

def finish (program : Program) (prepared : Prepared) : Prepared :=
  let wires := program.outputs.flatMap fun token =>
    ((prepared.state.live.find? (fun port => port.token == token)).map (·.wires)).getD []
  {prepared with events := prepared.events ++ [.reorder prepared.state.frame.length (axes prepared.state wires)]}

/-- Whole original program, including all original inputs, operations and final
output order. Admissibility must be established by the independent checker. -/
def run (program : Program) : Option Prepared := do
  let state := initial program.inputs
  let result ← program.operations.foldlM advance ⟨state,[],state.frame.length⟩
  return finish program result

end QleisliKernel.Semantics.RawTrace
