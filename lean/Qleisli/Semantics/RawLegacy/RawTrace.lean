import Qleisli.Semantics.RawLegacy.Raw
import QleisliKernel.Semantics.RawTrace

/-! Pre-Unit-opcode semantic fragment for checked representation transport.
Extracted from `lean-kernel/QleisliKernel/Semantics/RawTrace.lean` at `bb28608599e5df86b485ad5ff369e22d97a51ae6`
(SHA-256 `56c9dafe6f581b17449f3040303b88f036696f6591c024584be7bd2b2bed3eab`). Only imports, namespaces and
references to shared unchanged definitions differ. There is no checker here.
Stable payloads/states/rules are shared; their historical identity must still be checked.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.Semantics.RawLegacy.RawTrace
open QleisliKernel.Semantics.Raw QleisliKernel.Semantics.Finite QleisliKernel.Semantics.RawTrace
open Raw

/-- Read the meaning-bearing fields of every original pure constructor. This
neither decides admissibility nor constructs an evidence matrix. In particular,
computed events retain the actual body and requested logical data together. -/
def step (state : Interface) (op : Raw.Op) : Option (Interface × List Event) := do
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

def advance (prepared : Prepared) (op : Raw.Op) : Option Prepared := do
  let (next,events) ← step prepared.state op
  return {prepared with state := next,events := prepared.events ++ events}

def finish (program : Raw.Program) (prepared : Prepared) : Prepared :=
  let wires := program.outputs.flatMap fun token =>
    ((prepared.state.live.find? (fun port => port.token == token)).map (·.wires)).getD []
  {prepared with events := prepared.events ++ [.reorder prepared.state.frame.length (axes prepared.state wires)]}

/-- Whole original program, including all original inputs, operations and final
output order. Admissibility must be established by the independent checker. -/
def run (program : Raw.Program) : Option Prepared := do
  let state := initial program.inputs
  let result ← program.operations.foldlM advance ⟨state,[],state.frame.length⟩
  return finish program result


end Qleisli.Semantics.RawLegacy.RawTrace
