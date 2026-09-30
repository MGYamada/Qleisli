import Std

/-! Reference cyclic-phase semantics, independent of acceptance and normalization.
Changes to this mathematical specification require explicit semantic review.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/

namespace QleisliKernel

/-- A phase of `ticks` means exp(2π i ticks / 256) on basis state one. -/
inductive Gate where
  | x
  | phase (ticks : Nat)
  deriving BEq, DecidableEq, Repr

abbrev Word := List Gate

/-- The phase belongs to the original input basis value, before the flip. -/
structure Summary where
  flip : Bool
  phase0 : Nat
  phase1 : Nat
  deriving BEq, DecidableEq, Repr

/-- Cyclic phases are represented canonically modulo 256 during execution. -/
structure State where
  bit : Bool
  phase : Nat
  deriving BEq, DecidableEq, Repr

def modulus : Nat := 256

/-- Direct operational semantics, independent of the summary accumulator. -/
def step : Gate → State → State
  | .x, state => { state with bit := !state.bit }
  | .phase ticks, state =>
      { state with phase := (state.phase + if state.bit then ticks else 0) % modulus }

def execute (word : Word) (state : State) : State :=
  word.foldl (fun current gate => step gate current) state

/-- Initial phases are cyclic residues; this accepts every natural representative. -/
def run (word : Word) (bit : Bool) (initialPhase : Nat) : State :=
  execute word ⟨bit, initialPhase % modulus⟩

def Summary.action (summary : Summary) (bit : Bool) (initialPhase : Nat) : State :=
  ⟨Bool.xor bit summary.flip,
    (initialPhase + if bit then summary.phase1 else summary.phase0) % modulus⟩


end QleisliKernel
