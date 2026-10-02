import QleisliKernel.Semantics.RawTrace

/-! Original observing raw data and independent literal instrument reader.
No acceptance predicates, receipts, budgets or proposed matrices are imported.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Semantics.Observation
open Raw Finite

structure QuantumPhi where
  thenToken : Nat
  elseToken : Nat
  output : Nat
  wires : List Nat
  deriving BEq, DecidableEq, Repr

structure ClassicalPhi where
  thenId : Nat
  elseId : Nat
  output : Nat
  deriving BEq, DecidableEq, Repr

deriving instance ReflBEq, LawfulBEq for QuantumPhi, ClassicalPhi

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

inductive Expr where
  | constant (value : Bool)
  | not (input : Nat)
  | xor (left right : Nat)
  | and (left right : Nat)
  deriving BEq, DecidableEq, Repr

/-- Erasure retains every hidden basis outcome. Measurement additionally binds
its public SSA bit. Both branch arms include their complete phi permutation. -/
inductive Event where
  | pure (operation : Raw.Event)
  | erase (bits : Nat) (axes : List Nat) (output : Option Nat)
  | classical (expression : Expr) (output : Nat)
  | branch (condition : Nat) (thenEvents elseEvents : List Event)
      (classical : List ClassicalPhi)

def remaining (state : RawTrace.Interface) (wires : List Nat) : List Nat :=
  state.frame.filter (fun wire => !wires.contains wire)

def phiWires (state : RawTrace.Interface) (phis : List QuantumPhi) (choice : Bool) : List Nat :=
  phis.flatMap fun phi =>
    ((state.live.find? (fun (port : Port) => port.token == (if choice then phi.thenToken else phi.elseToken))).map
      (·.wires)).getD []

def phiInterface (phis : List QuantumPhi) : RawTrace.Interface :=
  ⟨phis.map (fun phi => ⟨phi.output,phi.wires,phi.wires.length⟩),phis.flatMap (·.wires)⟩

/-- A total, depth-bounded literal reader. Freshness, widths, effects and scope
are checked independently; the bound matches the original 64 nested branches. -/
def readOps (fuel : Nat) : RawTrace.Interface → List Op → Option (RawTrace.Interface × List Event) :=
  Nat.rec (fun _ _ => none) (fun _ recurse initial operations =>
    operations.foldlM (fun (state,events) op => do
      let (next,added) ← match op with
      | .pure operation => do
        let (next,added) ← RawTrace.step state operation
        pure (next,added.map Event.pure)
      | .measure input output => do
        let (port,next) ← RawTrace.take state input
        pure ({next with frame := remaining state port.wires},
          [.erase state.frame.length (RawTrace.axes state port.wires) (some output)])
      | .discard input => do
        let (port,next) ← RawTrace.take state input
        pure ({next with frame := remaining state port.wires},
          [.erase state.frame.length (RawTrace.axes state port.wires) none])
      | .reset input output wire => do
        let (port,next) ← RawTrace.take state input
        let frame := remaining state port.wires
        pure ({RawTrace.insert next output [wire] with frame := frame ++ [wire]},
          [.erase state.frame.length (RawTrace.axes state port.wires) none,.pure (.init0 frame.length)])
      | .constant value output => pure (state,[.classical (.constant value) output])
      | .not input output => pure (state,[.classical (.not input) output])
      | .xor left right output => pure (state,[.classical (.xor left right) output])
      | .and left right output => pure (state,[.classical (.and left right) output])
      | .branch condition thenOps elseOps quantum classical => do
        let (left,leftEvents) ← recurse state thenOps
        let (right,rightEvents) ← recurse state elseOps
        let finish := fun (arm : RawTrace.Interface) (choice : Bool) =>
          Event.pure (.reorder arm.frame.length (RawTrace.axes arm (phiWires arm quantum choice)))
        pure (phiInterface quantum,
          [.branch condition (leftEvents ++ [finish left true]) (rightEvents ++ [finish right false]) classical])
      pure (next,events ++ added)) (initial,[])) fuel

structure Prepared where
  state : RawTrace.Interface
  events : List Event
  inputBits : Nat

def read (program : Program) : Option Prepared := do
  let initial := RawTrace.initial program.inputs
  let (state,events) ← readOps 65 initial program.operations
  let wires := program.outputs.flatMap fun token =>
    ((state.live.find? (fun port => port.token == token)).map (·.wires)).getD []
  return ⟨state,events ++ [.pure (.reorder state.frame.length (RawTrace.axes state wires))],initial.frame.length⟩

end QleisliKernel.Semantics.Observation
