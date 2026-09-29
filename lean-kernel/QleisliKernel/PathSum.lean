import QleisliKernel.Interference

/-! Symbolic path compilation for H and dyadic diagonal gates.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/

namespace QleisliKernel.PathSum
open Interference PhasePolynomial

structure Symbolic where
  wires : List Nat
  phases : Polynomial
  hadamards : Nat
  deriving BEq, DecidableEq, Repr

structure PathState where
  bits : Bits
  phase : Nat
  hadamards : Nat

/-- Inputs and path choices are basis indices, never copied quantum owners. -/
def assignment (width : Nat) (input choices : Bits) (index : Nat) : Bool :=
  if index < width then input index else choices (index - width)

@[simp] theorem assignment_fresh (width count : Nat) (input choices : Bits) :
    assignment width input choices (width + count) = choices count := by
  simp [assignment, show ¬ width + count < width by omega]

def realize (width : Nat) (symbolic : Symbolic) (input choices : Bits) : PathState :=
  let values := assignment width input choices
  ⟨values ∘ LayoutDag.lookup symbolic.wires, evaluate symbolic.phases values, symbolic.hadamards⟩

/-- Direct interpretation of the literal gate at a fixed sequence of H choices. -/
def step (choices : Bits) (state : PathState) : Interference.Gate → PathState
  | .hadamard axis =>
    let output := choices state.hadamards
    ⟨setBit state.bits axis output,
      (state.phase + if state.bits axis && output then 128 else 0) % modulus,
      state.hadamards + 1⟩
  | .diagonal terms =>
    ⟨state.bits, (state.phase + evaluate terms state.bits) % modulus, state.hadamards⟩

def compileStep (width : Nat) (symbolic : Symbolic) : Interference.Gate → Option Symbolic
  | .hadamard axis =>
    if axis < symbolic.wires.length then
      let fresh := width + symbolic.hadamards
      let term : Term := ⟨[LayoutDag.lookup symbolic.wires axis, fresh], 128⟩
      some ⟨symbolic.wires.set axis fresh,
        PhasePolynomial.normalize (symbolic.phases ++ [term]), symbolic.hadamards + 1⟩
    else none
  | .diagonal terms =>
    if valid symbolic.wires.length terms then
      some ⟨symbolic.wires, PhasePolynomial.normalize
        (symbolic.phases ++ remap (LayoutDag.lookup symbolic.wires) terms), symbolic.hadamards⟩
    else none

theorem lookup_set (wires : List Nat) (axis fresh : Nat) (values : Bits)
    (inside : axis < wires.length) :
    values ∘ LayoutDag.lookup (wires.set axis fresh) =
      setBit (values ∘ LayoutDag.lookup wires) axis (values fresh) := by
  funext i
  by_cases same : i = axis
  · subst i
    simp [LayoutDag.lookup, setBit, List.getElem?_set_self inside]
  · simp [LayoutDag.lookup, setBit, same, List.getElem?_set_ne (Ne.symm same)]

theorem compileStep_sound (width : Nat) (symbolic result : Symbolic) (gate : Interference.Gate)
    (compiled : compileStep width symbolic gate = some result) (input choices : Bits) :
    realize width result input choices = step choices (realize width symbolic input choices) gate := by
  cases gate with
  | hadamard axis =>
    simp only [compileStep] at compiled
    split at compiled
    next inside =>
      cases Option.some.inj compiled
      simp only [realize, step, PhasePolynomial.normalize_sound, evaluate_append]
      rw [lookup_set symbolic.wires axis (width + symbolic.hadamards) _ inside]
      simp [evaluate, Term.value, Function.comp_def]
    next outside => contradiction
  | diagonal terms =>
    simp only [compileStep] at compiled
    split at compiled
    next wellFormed =>
      cases Option.some.inj compiled
      simp [realize, step, PhasePolynomial.normalize_sound, evaluate_append, remap_sound]
    next invalid => contradiction

def compileFrom (width : Nat) (gates : List Interference.Gate) (initial : Symbolic) :
    Option Symbolic := gates.foldlM (compileStep width) initial

def runFrom (gates : List Interference.Gate) (choices : Bits) (initial : PathState) : PathState :=
  gates.foldl (step choices) initial

theorem compileFrom_sound (width : Nat) (gates : List Interference.Gate)
    (initial result : Symbolic) (compiled : compileFrom width gates initial = some result)
    (input choices : Bits) :
    realize width result input choices =
      runFrom gates choices (realize width initial input choices) := by
  induction gates generalizing initial with
  | nil =>
    have same : initial = result := by simpa [compileFrom] using compiled
    subst result
    rfl
  | cons gate rest ih =>
    cases hs : compileStep width initial gate with
    | none => simp [compileFrom, hs] at compiled
    | some next =>
      have tail : compileFrom width rest next = some result := by simpa [compileFrom, hs] using compiled
      rw [ih next tail, compileStep_sound width initial next gate hs input choices]
      rfl

def initial (width : Nat) : Symbolic := ⟨List.range width, [], 0⟩

theorem initial_inside (width axis : Nat) (input choices : Bits) (inside : axis < width) :
    (realize width (initial width) input choices).bits axis = input axis := by
  simp [realize, initial, LayoutDag.lookup, assignment, inside]

def compile (width : Nat) (gates : List Interference.Gate) : Option Symbolic :=
  compileFrom width gates (initial width)

theorem compile_sound (width : Nat) (gates : List Interference.Gate) (result : Symbolic)
    (compiled : compile width gates = some result) (input choices : Bits) :
    realize width result input choices =
      runFrom gates choices (realize width (initial width) input choices) :=
  compileFrom_sound width gates (initial width) result compiled input choices

end QleisliKernel.PathSum
