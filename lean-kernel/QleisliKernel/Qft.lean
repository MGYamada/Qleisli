import QleisliKernel.PathSum

/-! Fixed-profile QFT template and its symbolic path certificate.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/

namespace QleisliKernel.Qft
open Interference PhasePolynomial PathSum

/-- Descending stages, H first, then controlled positive dyadic phases. -/
def stage (j : Nat) : List Interference.Gate :=
  .hadamard j :: (List.range j).reverse.map (fun k =>
    .diagonal [⟨[k, j], 2 ^ (7 - j + k)⟩])

def template (width : Nat) : List Interference.Gate :=
  (List.range width).reverse.flatMap stage

def finalAxes (width : Nat) : List Nat := (List.range width).reverse

/-- Independent bilinear Fourier phase, not a traversal of the gate template. -/
def fourierTerms (width : Nat) : Polynomial :=
  (List.range width).flatMap (fun k => (List.range (width - k)).map (fun l =>
    ⟨[k, width + l], 2 ^ (8 - width + k + l)⟩))

def expected (width : Nat) : Symbolic :=
  ⟨(List.range width).map (fun j => width + (width - 1 - j)),
    PhasePolynomial.normalize (fourierTerms width), width⟩

/-- Internal structural matcher. No external schema registry is enabled here. -/
def matchCircuit (width : Nat) (gates : List Interference.Gate) (axes : List Nat) : Bool :=
  1 ≤ width && width ≤ 8 && gates.length ≤ 36 && axes.length = width &&
    decide (gates = template width) && decide (axes = finalAxes width)

theorem matchCircuit_conditions (width : Nat) (gates : List Interference.Gate) (axes : List Nat)
    (accepted : matchCircuit width gates axes = true) :
    1 ≤ width ∧ width ≤ 8 ∧ gates = template width ∧ axes = finalAxes width := by
  simp only [matchCircuit, Bool.and_eq_true, decide_eq_true_eq] at accepted
  exact ⟨accepted.1.1.1.1.1, accepted.1.1.1.1.2, accepted.1.2, accepted.2⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
set_option cbv.maxSteps 2000000 in
/-- Kernel reduction covers eight bounded templates, never basis assignments. -/
theorem compile_template (width : Nat) (positive : 1 ≤ width) (bounded : width ≤ 8) :
    PathSum.compile width (template width) = some (expected width) := by
  have cases : width = 1 ∨ width = 2 ∨ width = 3 ∨ width = 4 ∨
      width = 5 ∨ width = 6 ∨ width = 7 ∨ width = 8 := by omega
  rcases cases with h | h | h | h | h | h | h | h <;> subst width <;> cbv

theorem matched_paths (width : Nat) (gates : List Interference.Gate) (axes : List Nat)
    (accepted : matchCircuit width gates axes = true) (input choices : Bits) :
    runFrom gates choices (realize width (initial width) input choices) =
      realize width (expected width) input choices := by
  obtain ⟨positive, bounded, same, _⟩ := matchCircuit_conditions width gates axes accepted
  subst gates
  exact (compile_sound width (template width) (expected width)
    (compile_template width positive bounded) input choices).symm

/-- Final reversal makes each output bit exactly its corresponding path choice. -/
theorem output_choice (width axis : Nat) (inside : axis < width) (input choices : Bits) :
    (realize width (expected width) input choices).bits (width - 1 - axis) = choices axis := by
  have reverseInside : width - 1 - axis < width := by omega
  have reverseTwice : width - 1 - (width - 1 - axis) = axis := by omega
  simp [realize, expected, LayoutDag.lookup, reverseInside, reverseTwice]

theorem matched_output (width axis : Nat) (inside : axis < width)
    (gates : List Interference.Gate) (axes : List Nat)
    (accepted : matchCircuit width gates axes = true) (input choices : Bits) :
    (runFrom gates choices (realize width (initial width) input choices)).bits
      (width - 1 - axis) = choices axis := by
  rw [matched_paths width gates axes accepted input choices]
  exact output_choice width axis inside input choices

end QleisliKernel.Qft
