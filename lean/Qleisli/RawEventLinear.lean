import Qleisli.RawActionLinear
import Qleisli.Semantics.ObservingAction

/-! Finite weighted linearity of every literal pure and erasure event.
The weights are fixed for one reference column. Computed and protected
events retain their original physical execution.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.Semantics.RawAction
open QleisliKernel.Semantics.Finite (Dependency Step gather scatter)
open QleisliKernel.Semantics.Raw (Event Gate Use computeStep)

noncomputable def combination {Index : Type} (indices : List Index)
    (weight values : Index → ℂ) : ℂ :=
  (indices.map (fun index => values index * weight index)).sum

private theorem combination_if {Index : Type} (indices : List Index) (weight values : Index → ℂ)
    (condition : Prop) [Decidable condition] :
    (if condition then combination indices weight values else 0) =
      combination indices weight (fun index => if condition then values index else 0) := by
  by_cases held : condition <;> simp [held,combination]

private theorem combination_mul {Index : Type} (indices : List Index) (weight values : Index → ℂ)
    (factor : ℂ) : combination indices weight values * factor =
      combination indices weight (fun index => values index * factor) := by
  unfold combination
  rw [← List.sum_map_mul_right]
  apply Qleisli.Exact.sum_map_congr
  intro index _
  exact mul_right_comm _ _ _

private theorem sum_combination {Index Row : Type} (indices : List Index) (rows : List Row)
    (weight : Index → ℂ) (values : Row → Index → ℂ) :
    (rows.map (fun row => combination indices weight (values row))).sum =
      combination indices weight (fun index => (rows.map (fun row => values row index)).sum) := by
  unfold combination
  rw [Qleisli.Exact.sum_swap]
  apply Qleisli.Exact.sum_map_congr
  intro index _
  rw [List.sum_map_mul_right]

private theorem circuit_combination {Index : Type} (dependencies : List Dependency) (steps : List Step)
    (indices : List Index) (weight : Index → ℂ) (values : Index → Nat → ℂ) (row : Nat) :
    circuit dependencies steps (fun input => combination indices weight (fun index => values index input)) row =
      combination indices weight (fun index => circuit dependencies steps (values index) row) := by
  unfold combination
  rw [circuit_sum]
  apply Qleisli.Exact.sum_map_congr
  intro index _
  exact circuit_scale dependencies steps (values index) (weight index) row

private theorem protected_gate_combination {Index : Type} (indices : List Index) (weight : Index → ℂ)
    (gate : Gate) (axis : Nat) (values : Index → Nat → ℂ) (row : Nat) :
    Protected.gate gate axis (fun input => combination indices weight (fun index => values index input)) row =
      combination indices weight (fun index => Protected.gate gate axis (values index) row) := by
  cases gate with
  | x => rfl
  | z => exact combination_mul _ _ _ _
  | t => exact combination_mul _ _ _ _
  | h =>
    let operation : Step := ⟨[],.hadamard axis⟩
    change step [] operation (fun input => combination indices weight (fun index => values index input)) row =
      combination indices weight (fun index => step [] operation (values index) row)
    unfold combination
    rw [step_sum]
    apply Qleisli.Exact.sum_map_congr
    intro index _
    exact step_scale [] operation (values index) (weight index) row

private theorem protected_use_combination {Index Ref : Type} (indices : List Index) (weight : Index → ℂ)
    (use : Use) (values : Index → Protected.Physical Ref) :
    Protected.physicalUse use
      (fun source ancilla target ref => combination indices weight (fun index => values index source ancilla target ref)) =
    (fun source ancilla target ref =>
      combination indices weight (fun index => Protected.physicalUse use (values index) source ancilla target ref)) := by
  funext source ancilla target ref
  cases use with
  | protectedGate location operation =>
    cases location with
    | mk region axis =>
      cases region with
      | source =>
        simpa only [Protected.physicalUse] using
          protected_gate_combination indices weight operation axis (fun index label => values index label ancilla target ref) source
      | ancilla =>
        simpa only [Protected.physicalUse] using
          protected_gate_combination indices weight operation axis (fun index label => values index source label target ref) ancilla
  | targetGate controls axis operation =>
    by_cases enabled : QleisliKernel.Semantics.Protected.enabled source ancilla controls = true
    · simpa only [Protected.physicalUse,enabled,if_true] using
        protected_gate_combination indices weight operation axis (fun index label => values index source ancilla label ref) target
    · simp only [Protected.physicalUse,enabled,Bool.false_eq_true,if_false]
  | phase controls phase =>
    exact combination_mul _ _ _ _

private theorem protected_run_combination {Index Ref : Type} (indices : List Index) (weight : Index → ℂ)
    (uses : List Use) (values : Index → Protected.Physical Ref) :
    Protected.run uses
      (fun source ancilla target ref => combination indices weight (fun index => values index source ancilla target ref)) =
    (fun source ancilla target ref =>
      combination indices weight (fun index => Protected.run uses (values index) source ancilla target ref)) := by
  induction uses generalizing values with
  | nil => rfl
  | cons use uses ih =>
    change Protected.run uses (Protected.physicalUse use
        (fun source ancilla target ref => combination indices weight (fun index => values index source ancilla target ref))) =
      (fun source ancilla target ref => combination indices weight
        (fun index => Protected.run uses (Protected.physicalUse use (values index)) source ancilla target ref))
    rw [protected_use_combination]
    exact ih _

/-- Within a checked diagonal protected block, the same finite weighted
linearity holds at each source and auxiliary coordinate. -/
theorem protected_blocks_combination {Index Ref : Type} (indices : List Index) (weight : Index → ℂ)
    (uses : List Use) (valid : ∀ use ∈ uses, Protected.DiagonalProtected use)
    (source ancilla : Nat) (values : Index → Nat → Ref → ℂ) :
    Protected.blocks source ancilla uses
      (fun target ref => combination indices weight (fun index => values index target ref)) =
    (fun target ref => combination indices weight (fun index =>
      Protected.blocks source ancilla uses (values index) target ref)) := by
  have same := congrArg (fun run : Protected.Physical Ref => run source ancilla)
    (protected_run_combination indices weight uses (fun index _ _ => values index))
  simpa only [Protected.run_blocks uses valid] using same

/-- Each original pure event commutes with finite weighted sums in a
reference column, including the full computed-scope action. -/
theorem event_combination {Index : Type} (dependencies : List Dependency) (operation : Event)
    (indices : List Index) (weight : Index → ℂ) (values : Index → Nat → ℂ) (row : Nat) :
    event dependencies operation (fun input => combination indices weight (fun index => values index input)) row =
      combination indices weight (fun index => event dependencies operation (values index) row) := by
  cases operation with
  | circuit _ steps => exact circuit_combination _ steps _ _ _ _
  | init0 bits => exact combination_if _ _ _ (row < 2^bits)
  | liftBasis before _ inputAxes outputAxes table =>
    simp only [event]
    simp_rw [combination_if]
    exact sum_combination _ _ _ _
  | reorder bits axes =>
    simp only [event]
    simp_rw [combination_if]
    exact sum_combination _ _ _ _
  | computed _ axes sourceBits ancillaBits function uses _ =>
    simp only [event,embed]
    simp_rw [combination_if]
    exact circuit_combination _ _ _ _ _ _
  | protectedComputed _ axes sourceBits _ function uses =>
    let localRow := gather row axes
    let source := localRow % 2^sourceBits
    let ancilla := 0 ^^^ function[source]?.getD 0
    let target := localRow / 2^sourceBits
    let inputs : Index → Protected.Physical Unit := fun index source ancilla target _ =>
      if (ancilla ^^^ function[source]?.getD 0) = 0 then
        values index (scatter row axes (source+target*2^sourceBits)) else 0
    change Protected.run uses (fun source ancilla target _ =>
      if (ancilla ^^^ function[source]?.getD 0) = 0 then
        combination indices weight (fun index => values index (scatter row axes (source+target*2^sourceBits))) else 0)
        source ancilla target () =
      combination indices weight (fun index => Protected.run uses (inputs index) source ancilla target ())
    simp_rw [combination_if]
    exact congrArg (fun action : Protected.Physical Unit => action source ancilla target ())
      (protected_run_combination indices weight uses inputs)

  | structuralComputed _ axes forward inverse uses =>
    simp only [event,embed]
    simp_rw [combination_if]
    exact circuit_combination _ _ _ _ _ _

theorem erase_combination {Index : Type} (bits : Nat) (axes : List Nat) (outcome : Nat)
    (indices : List Index) (weight : Index → ℂ) (values : Index → Nat → ℂ) (row : Nat) :
    ObservingAction.erase bits axes outcome (fun input => combination indices weight (fun index => values index input)) row =
      combination indices weight (fun index => ObservingAction.erase bits axes outcome (values index) row) := by
  simp only [ObservingAction.erase]
  simp_rw [combination_if]
  exact sum_combination _ _ _ _

#print axioms event_combination
#print axioms erase_combination
end Qleisli.Semantics.RawAction
