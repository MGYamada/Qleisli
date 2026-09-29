import QleisliKernel.Interference

/-! Actual controlled-iterate schedules and their phase-sensitive action law.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/

namespace QleisliKernel.ControlledPowers
open Interference

structure Stage where
  control : Nat
  targetDefinition : Nat
  count : Nat
  whenOne : Bool
  deriving BEq, DecidableEq, Repr

def template (width target : Nat) : List Stage :=
  (List.range width).map (fun k => ⟨k, target, 2 ^ k, true⟩)

/-- An internal structural check; the external provider still needs checked
type, whole-space unitarity and controlled-access evidence. -/
def check (width target : Nat) (stages : List Stage) : Bool :=
  1 ≤ width && width ≤ 8 && stages.length = width && decide (stages = template width target)

theorem check_conditions (width target : Nat) (stages : List Stage)
    (accepted : check width target stages = true) :
    1 ≤ width ∧ width ≤ 8 ∧ stages = template width target := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at accepted
  exact ⟨accepted.1.1.1, accepted.1.1.2, accepted.2⟩

/-- Semantic execution, never called by the schedule checker. -/
def iterate {A : Type} (operation : A → A) (count : Nat) (state : A) : A :=
  Nat.rec state (fun _ previous => operation previous) count

theorem iterate_add {A : Type} (operation : A → A) (first second : Nat) (state : A) :
    iterate operation (first + second) state = iterate operation second (iterate operation first state) := by
  induction second with
  | zero => rfl
  | succ n ih =>
    change operation (iterate operation (first + n) state) =
      operation (iterate operation n (iterate operation first state))
    exact congrArg operation ih

def selected (bits : Bits) (stage : Stage) : Nat :=
  if bits stage.control = stage.whenOne then stage.count else 0

def applyStage {A : Type} (operations : Nat → A → A) (bits : Bits) (state : A) (stage : Stage) : A :=
  if bits stage.control = stage.whenOne then iterate (operations stage.targetDefinition) stage.count state
  else state

/-- One controlled-power schema operand. Its local control is coordinate zero;
embedding into a larger interface requires the enclosing checked port map.
The exponent limit follows the profile's maximum repeat count, 4096. -/
def checkSingle (exponent target : Nat) (stage : Stage) : Bool :=
  exponent ≤ 12 && decide (stage = ⟨0, target, 2^exponent, true⟩)

theorem checkSingle_action {A : Type} (operations : Nat → A → A)
    (exponent target : Nat) (stage : Stage) (accepted : checkSingle exponent target stage = true)
    (bits : Bits) (state : A) :
    applyStage operations bits state stage =
      if bits 0 then iterate (operations target) (2^exponent) state else state := by
  have shape : stage = ⟨0, target, 2^exponent, true⟩ := by
    simp only [checkSingle, Bool.and_eq_true, decide_eq_true_eq] at accepted
    exact accepted.2
  rw [shape]
  rfl

def run {A : Type} (operations : Nat → A → A) (bits : Bits) (stages : List Stage) (state : A) : A :=
  stages.foldl (applyStage operations bits) state

/-- Coherent sector lifting: control coordinates are retained, not measured.
`A` may contain target amplitudes with an arbitrary reference. Mathematical
linearity/unitarity comes from the interpreted provider, not this type alone. -/
def coherentStage {B A : Type} (operations : Nat → A → A) (controls : B → Bits)
    (state : B → A) (stage : Stage) : B → A :=
  fun basis => applyStage operations (controls basis) (state basis) stage

def coherentRun {B A : Type} (operations : Nat → A → A) (controls : B → Bits)
    (stages : List Stage) (state : B → A) : B → A :=
  stages.foldl (coherentStage operations controls) state

theorem coherentRun_apply {B A : Type} (operations : Nat → A → A) (controls : B → Bits)
    (stages : List Stage) (state : B → A) (basis : B) :
    coherentRun operations controls stages state basis =
      run operations (controls basis) stages (state basis) := by
  induction stages generalizing state with
  | nil => rfl
  | cons stage rest ih =>
    change coherentRun operations controls rest (coherentStage operations controls state stage) basis = _
    rw [ih]
    rfl

def selectedUses (stages : List Stage) (bits : Bits) : Nat := (stages.map (selected bits)).sum

def maximumUses (stages : List Stage) : Nat := (stages.map Stage.count).sum

def value (width : Nat) (bits : Bits) : Nat :=
  ((List.range width).map (fun k => if bits k then 2 ^ k else 0)).sum

theorem applyStage_same {A : Type} (operations : Nat → A → A) (target : Nat)
    (bits : Bits) (state : A) (stage : Stage) (same : stage.targetDefinition = target) :
    applyStage operations bits state stage = iterate (operations target) (selected bits stage) state := by
  simp only [applyStage, selected, same]
  split <;> rfl

theorem run_same {A : Type} (operations : Nat → A → A) (target : Nat) (bits : Bits)
    (stages : List Stage) (same : ∀ stage ∈ stages, stage.targetDefinition = target) (state : A) :
    run operations bits stages state = iterate (operations target) (selectedUses stages bits) state := by
  induction stages generalizing state with
  | nil => rfl
  | cons stage rest ih =>
    have first := same stage (by simp)
    have remaining : ∀ s ∈ rest, s.targetDefinition = target := fun s h => same s (by simp [h])
    change run operations bits rest (applyStage operations bits state stage) = _
    rw [ih remaining, applyStage_same operations target bits state stage first]
    exact (iterate_add (operations target) (selected bits stage) (selectedUses rest bits) state).symm

theorem selected_template (width target : Nat) (bits : Bits) :
    selectedUses (template width target) bits = value width bits := by
  simp [selectedUses, template, selected, value, List.map_map, Function.comp_def]

theorem check_action {A : Type} (operations : Nat → A → A) (width target : Nat)
    (stages : List Stage) (accepted : check width target stages = true) (bits : Bits) (state : A) :
    run operations bits stages state = iterate (operations target) (value width bits) state := by
  obtain ⟨_, _, same⟩ := check_conditions width target stages accepted
  subst stages
  rw [run_same operations target bits (template width target) (by simp [template]) state,
    selected_template]

/-- Counts reflect literal U applications, not the number of descriptors. -/
theorem maximumUses_template (width target : Nat) :
    maximumUses (template width target) + 1 = 2 ^ width := by
  induction width with
  | zero => rfl
  | succ width ih =>
    have next : maximumUses (template (width + 1) target) =
        maximumUses (template width target) + 2 ^ width := by
      simp [maximumUses, template, List.range_succ, List.sum_append]
    rw [next, Nat.pow_succ]
    omega

end QleisliKernel.ControlledPowers
