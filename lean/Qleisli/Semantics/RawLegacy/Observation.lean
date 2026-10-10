import Qleisli.Semantics.RawLegacy.RawTrace
import QleisliKernel.Semantics.Observation

/-! Pre-Unit-opcode semantic fragment for checked representation transport.
Extracted from `lean-kernel/QleisliKernel/Semantics/Observation.lean` at `bb28608599e5df86b485ad5ff369e22d97a51ae6`
(SHA-256 `5faf3991f8441f23b3053e87d16a2131aafecbd3dc8c75f906695878e534743e`). Only imports, namespaces and
references to shared unchanged definitions differ. There is no checker here.
Stable payloads/states/rules are shared; their historical identity must still be checked.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.Semantics.RawLegacy.Observation
open QleisliKernel.Semantics.Raw QleisliKernel.Semantics.Finite QleisliKernel.Semantics.Observation

inductive Op where
  | pure (operation : Raw.Op)
  | measure (input output : Nat)
  | reset (input output wire : Nat)
  | discard (input : Nat)
  | constant (value : Bool) (output : Nat)
  | not (input output : Nat)
  | xor (left right output : Nat)
  | and (left right output : Nat)
  | branch (condition : Nat) (thenOps elseOps : List Op)
      (quantum : List QuantumPhi) (classical : List ClassicalPhi)

structure Program where
  inputs : List Port
  classicalInputs : List Nat
  operations : List Op
  outputs : List Nat
  classicalOutputs : List Nat
  effect : Effect

/-- A total, depth-bounded literal reader. Freshness, widths, effects and scope
are checked independently; the bound matches the original 64 nested branches. -/
def readOps (fuel : Nat) : QleisliKernel.Semantics.RawTrace.Interface → List Op → Option (QleisliKernel.Semantics.RawTrace.Interface × List QleisliKernel.Semantics.Observation.Event) :=
  Nat.rec (fun _ _ => none) (fun _ recurse initial operations =>
    operations.foldlM (fun (state,events) op => do
      let (next,added) ← match op with
      | .pure operation => do
        let (next,added) ← RawTrace.step state operation
        pure (next,added.map QleisliKernel.Semantics.Observation.Event.pure)
      | .measure input output => do
        let (port,next) ← QleisliKernel.Semantics.RawTrace.take state input
        pure ({next with frame := remaining state port.wires},
          [.erase state.frame.length (QleisliKernel.Semantics.RawTrace.axes state port.wires) (some output)])
      | .discard input => do
        let (port,next) ← QleisliKernel.Semantics.RawTrace.take state input
        pure ({next with frame := remaining state port.wires},
          [.erase state.frame.length (QleisliKernel.Semantics.RawTrace.axes state port.wires) none])
      | .reset input output wire => do
        let (port,next) ← QleisliKernel.Semantics.RawTrace.take state input
        let frame := remaining state port.wires
        pure ({QleisliKernel.Semantics.RawTrace.insert next output [wire] with frame := frame ++ [wire]},
          [.erase state.frame.length (QleisliKernel.Semantics.RawTrace.axes state port.wires) none,.pure (.init0 frame.length)])
      | .constant value output => pure (state,[.classical (.constant value) output])
      | .not input output => pure (state,[.classical (.not input) output])
      | .xor left right output => pure (state,[.classical (.xor left right) output])
      | .and left right output => pure (state,[.classical (.and left right) output])
      | .branch condition thenOps elseOps quantum classical => do
        let (left,leftEvents) ← recurse state thenOps
        let (right,rightEvents) ← recurse state elseOps
        let finish := fun (arm : QleisliKernel.Semantics.RawTrace.Interface) (choice : Bool) =>
          QleisliKernel.Semantics.Observation.Event.pure (.reorder arm.frame.length (QleisliKernel.Semantics.RawTrace.axes arm (phiWires arm quantum choice)))
        pure (phiInterface quantum,
          [.branch condition (leftEvents ++ [finish left true]) (rightEvents ++ [finish right false]) classical])
      pure (next,events ++ added)) (initial,[])) fuel

def read (program : Program) : Option Prepared := do
  let initial := QleisliKernel.Semantics.RawTrace.initial program.inputs
  let (state,events) ← readOps 65 initial program.operations
  let wires := program.outputs.flatMap fun token =>
    ((state.live.find? (fun port => port.token == token)).map (·.wires)).getD []
  return ⟨state,events ++ [.pure (.reorder state.frame.length (QleisliKernel.Semantics.RawTrace.axes state wires))],initial.frame.length⟩


end Qleisli.Semantics.RawLegacy.Observation
