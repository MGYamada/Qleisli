import Std

/-!
An executable, phase-sensitive checker for one-bit words over X and exact
256th-root phases. This is a bounded kernel experiment, not the full Qleisli
IR verifier. Its theorem concerns cyclic-phase action, not complex matrices,
source translation, ownership, measurement, or the native compilation chain.

Copyright 2026 Masahiko G. Yamada. Licensed under Apache-2.0.
-/

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

def maxGates : Nat := 4096

def gateValid : Gate → Bool
  | .x => true
  | .phase ticks => ticks < modulus

def wordValid (word : Word) : Bool :=
  word.length ≤ maxGates && word.all gateValid

def summaryValid (summary : Summary) : Bool :=
  summary.phase0 < modulus && summary.phase1 < modulus

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

def identitySummary : Summary := ⟨false, 0, 0⟩

/-- The executable normalizer uses a constant-size accumulator. -/
def accumulate (summary : Summary) : Gate → Summary
  | .x => { summary with flip := !summary.flip }
  | .phase ticks =>
      { summary with
        phase0 := (summary.phase0 + if summary.flip then ticks else 0) % modulus
        phase1 := (summary.phase1 + if !summary.flip then ticks else 0) % modulus }

def normalize (word : Word) : Summary := word.foldl accumulate identitySummary

/-- Both summaries are explicit: a submitted claim never chooses the requirement. -/
def verify (word : Word) (claimed expected : Summary) : Bool :=
  wordValid word && summaryValid claimed && summaryValid expected &&
    decide (normalize word = claimed) && decide (claimed = expected)

/-- Public checks include all gates and both full canonical summaries. -/
theorem verify_conditions (word : Word) (claimed expected : Summary) :
    verify word claimed expected = true ↔
      wordValid word = true ∧ summaryValid claimed = true ∧
      summaryValid expected = true ∧ normalize word = claimed ∧ claimed = expected := by
  simp [verify, and_assoc]

/-- Acceptance does not silently ignore invalid phase gates. -/
theorem wordValid_iff (word : Word) :
    wordValid word = true ↔
      word.length ≤ maxGates ∧ ∀ gate ∈ word, gateValid gate = true := by
  simp [wordValid]

private theorem accumulate_valid (summary : Summary) (gate : Gate)
    (valid : summaryValid summary = true) :
    summaryValid (accumulate summary gate) = true := by
  cases gate with
  | x => simpa [accumulate, summaryValid] using valid
  | phase ticks => simp [accumulate, summaryValid, modulus, Nat.mod_lt]

private theorem fold_valid (word : Word) (summary : Summary)
    (valid : summaryValid summary = true) :
    summaryValid (word.foldl accumulate summary) = true := by
  induction word generalizing summary with
  | nil => exact valid
  | cons gate rest ih =>
      exact ih (accumulate summary gate) (accumulate_valid summary gate valid)

/-- Every normalizer output is a canonical cyclic-phase summary. -/
theorem normalize_valid (word : Word) : summaryValid (normalize word) = true := by
  exact fold_valid word identitySummary (by decide)

private theorem action_accumulate (summary : Summary) (gate : Gate)
    (bit : Bool) (initialPhase : Nat) :
    (accumulate summary gate).action bit initialPhase =
      step gate (summary.action bit initialPhase) := by
  cases gate with
  | x =>
    cases bit <;> cases h : summary.flip <;>
      simp [accumulate, Summary.action, step, h]
  | phase ticks =>
    cases bit <;> cases h : summary.flip <;>
      simp [accumulate, Summary.action, step, h, Nat.add_assoc]

private theorem action_fold (word : Word) (summary : Summary)
    (bit : Bool) (initialPhase : Nat) :
    (word.foldl accumulate summary).action bit initialPhase =
      execute word (summary.action bit initialPhase) := by
  induction word generalizing summary with
  | nil => rfl
  | cons gate rest ih =>
      change (rest.foldl accumulate (accumulate summary gate)).action bit initialPhase =
        execute rest (step gate (summary.action bit initialPhase))
      rw [ih, action_accumulate]

/-- The actual normalizer agrees with direct gate execution on all input phases. -/
theorem normalize_correct (word : Word) (bit : Bool) (initialPhase : Nat) :
    (normalize word).action bit initialPhase = run word bit initialPhase := by
  rw [normalize, action_fold]
  simp [identitySummary, Summary.action, run]

/-- Acceptance binds the computed action to the independently supplied requirement. -/
theorem verify_sound (word : Word) (claimed expected : Summary)
    (accepted : verify word claimed expected = true)
    (bit : Bool) (initialPhase : Nat) :
    run word bit initialPhase = expected.action bit initialPhase := by
  simp only [verify, Bool.and_eq_true, decide_eq_true_eq] at accepted
  have normalized : normalize word = expected := accepted.1.2.trans accepted.2
  rw [← normalize_correct, normalized]

end QleisliKernel
