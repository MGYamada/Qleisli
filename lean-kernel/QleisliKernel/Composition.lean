import QleisliKernel.PhaseWord

/-! Phase-sensitive composition over the actual executable summaries.
Copyright 2026 Masahiko G. Yamada. Apache-2.0. -/

namespace QleisliKernel

abbrev Action := Bool → Nat → State

def thenAction (first second : Action) : Action := fun bit phase =>
  let middle := first bit phase
  second middle.bit middle.phase

def compose (first second : Summary) : Summary :=
  ⟨Bool.xor first.flip second.flip,
   (first.phase0 + if first.flip then second.phase1 else second.phase0) % modulus,
   (first.phase1 + if first.flip then second.phase0 else second.phase1) % modulus⟩

/-- Repetition composes cached constant-size summaries, never the body IR. -/
def repeatSummary (count : Nat) (body : Summary) : Summary :=
  Nat.rec identitySummary (fun _ previous => compose previous body) count

/-- Independent operational repetition of the already interpreted action. -/
def repeatAction (count : Nat) (body : Action) : Action :=
  Nat.rec identitySummary.action (fun _ previous => thenAction previous body) count

theorem compose_action (first second : Summary) :
    (compose first second).action = thenAction first.action second.action := by
  funext bit phase
  cases bit <;> cases h₁ : first.flip <;> cases h₂ : second.flip <;>
    simp [compose, Summary.action, thenAction, h₁, h₂, Nat.add_assoc]

theorem repeat_action (count : Nat) (body : Summary) :
    (repeatSummary count body).action = repeatAction count body.action := by
  induction count with
  | zero => rfl
  | succ n ih =>
    change (compose (repeatSummary n body) body).action =
      thenAction (repeatAction n body.action) body.action
    rw [compose_action, ih]

end QleisliKernel

namespace QleisliKernel

/-- A one-bit monomial squares to a diagonal action; this closed power avoids
iteration even over the cached summary. Every arithmetic operand is bounded
by the enclosing checker before native evaluation. -/
def powerSummary (count : Nat) (body : Summary) : Summary :=
  if body.flip then
    let phase := (count / 2) * (body.phase0 + body.phase1)
    if count % 2 == 0 then ⟨false, phase % modulus, phase % modulus⟩
    else ⟨true, (phase + body.phase0) % modulus, (phase + body.phase1) % modulus⟩
  else ⟨false, (count * body.phase0) % modulus, (count * body.phase1) % modulus⟩

theorem powerSummary_zero (body : Summary) : powerSummary 0 body = identitySummary := by
  simp [powerSummary, identitySummary]

theorem powerSummary_succ (count : Nat) (body : Summary) :
    powerSummary (count + 1) body = compose (powerSummary count body) body := by
  cases body with
  | mk flip p₀ p₁ =>
    cases flip with
    | false => simp [powerSummary, compose, Nat.add_mul, Nat.add_mod]
    | true =>
      have parity : count % 2 = 0 ∨ count % 2 = 1 := by omega
      rcases parity with even | odd
      · have divNext : (count + 1) / 2 = count / 2 := by omega
        have modNext : (count + 1) % 2 = 1 := by omega
        simp [powerSummary, compose, even, divNext, modNext, Nat.add_mod]
      · have divNext : (count + 1) / 2 = count / 2 + 1 := by omega
        have modNext : (count + 1) % 2 = 0 := by omega
        simp [powerSummary, compose, odd, divNext, modNext, Nat.add_mul,
          Nat.add_assoc, Nat.add_left_comm]
        congr 1
        omega

theorem powerSummary_eq_repeat (count : Nat) (body : Summary) :
    powerSummary count body = repeatSummary count body := by
  induction count with
  | zero => exact powerSummary_zero body
  | succ n ih =>
    rw [powerSummary_succ, ih]
    rfl

theorem powerSummary_action (count : Nat) (body : Summary) :
    (powerSummary count body).action = repeatAction count body.action := by
  rw [powerSummary_eq_repeat, repeat_action]

end QleisliKernel
