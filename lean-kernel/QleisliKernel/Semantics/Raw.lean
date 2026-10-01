import QleisliKernel.Semantics.Finite

/-! Original straight-line pure RawProgram data. This module contains no checker,
producer receipt, capacity policy or transport. Classical control and observing
constructors are deliberately a separate VM-26 packet.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Semantics.Raw
open Finite

inductive Effect where
  | unitary | iso | observe
  deriving BEq, DecidableEq, Repr

inductive Gate where
  | h | x | z | t
  deriving BEq, DecidableEq, Repr

inductive Phase where
  | minusOne | eighthTurn
  deriving BEq, DecidableEq, Repr

structure Port where
  token : Nat
  wires : List Nat
  bits : Nat
  deriving BEq, DecidableEq, Repr

inductive UnitaryStep where
  | gate (gate : Gate) (target : Nat)
  | cnot (control target : Nat)
  | toffoli (a b target : Nat)
  | phase (phase : Phase)
  deriving BEq, DecidableEq, Repr

inductive Region where
  | source | ancilla
  deriving BEq, DecidableEq, Repr

structure ProtectedBit where
  region : Region
  index : Nat
  deriving BEq, DecidableEq, Repr

structure ProtectedControl where
  bit : ProtectedBit
  whenOne : Bool
  deriving BEq, DecidableEq, Repr

inductive Use where
  | protectedGate (bit : ProtectedBit) (gate : Gate)
  | targetGate (controls : List ProtectedControl) (target : Nat) (gate : Gate)
  | phase (controls : List ProtectedControl) (phase : Phase)
  deriving BEq, DecidableEq, Repr

structure Target where
  input : Nat
  output : Nat
  deriving BEq, DecidableEq, Repr

inductive Op where
  | init0 (output wire : Nat)
  | gate (gate : Gate) (input output : Nat)
  | cnot (control target controlOut targetOut : Nat)
  | toffoli (a b target aOut bOut targetOut : Nat)
  | quantumIf (control target controlOut targetOut : Nat) (zero one : List UnitaryStep)
  | split (input left right leftBits : Nat)
  | join (left right output : Nat)
  | liftBasis (input output : Nat) (wires table : List Nat)
  | applyUnitary (input output : Nat) (steps : List Step)
  | certifiedCompute (input output : Nat) (ancilla function : List Nat)
      (useSteps logicalSteps : List Step)
  | computeUseUncompute (input output : Nat) (targets : List Target)
      (ancilla function : List Nat) (uses : List Use)
  deriving BEq, DecidableEq, Repr

structure Program where
  inputs : List Port
  operations : List Op
  outputs : List Nat
  effect : Effect
  deriving BEq, DecidableEq, Repr

/-- Raw bodies, including original signatures, are reconstructed before calls.
No computed circuit, matrix, private identity or accepted flag is supplied. -/
structure Evidence where
  signature : Basis
  implementation : Program
  specification : Program
  deriving BEq, DecidableEq, Repr

/-- Straight-line action data for a literal extracted trace. These are outputs
of raw reconstruction, not accepted matrices or producer validity claims. -/
inductive Event where
  | circuit (bits : Nat) (steps : List Step)
  | init0 (bits : Nat)
  | liftBasis (inputBits outputBits : Nat) (inputAxes outputAxes table : List Nat)
  | reorder (bits : Nat) (axes : List Nat)
  | computed (bits : Nat) (axes : List Nat) (sourceBits ancillaBits : Nat)
      (function : List Nat) (useSteps logicalSteps : List Step)
  | protectedComputed (bits : Nat) (axes : List Nat) (sourceBits ancillaBits : Nat)
      (function : List Nat) (uses : List Use)
  deriving BEq, DecidableEq, Repr

def registerBasis (bits : Nat) : Basis :=
  Nat.rec [.unit] (fun n previous => if n == 0 then [.bit] else .pair :: .bit :: previous) bits

/-- The original compute action XORs the function into high auxiliary axes.
Data (source followed by targets) occupy the low axes. It is self-inverse. -/
def computeStep (sourceBits dataBits ancillaBits : Nat) (function : List Nat) : Step :=
  let bits := dataBits+ancillaBits
  ⟨[],.monomial (List.range bits) ((List.range (2^bits)).map fun label =>
    label ^^^ ((function[label % 2^sourceBits]?.getD 0) * 2^dataBits)) (List.replicate (2^bits) 0)⟩

deriving instance ReflBEq, LawfulBEq for Effect, Gate, Phase, Port, UnitaryStep,
  Region, ProtectedBit, ProtectedControl, Use, Target, Op, Program, Evidence, Event

end QleisliKernel.Semantics.Raw
