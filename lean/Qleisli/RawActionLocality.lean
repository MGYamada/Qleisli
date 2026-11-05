import Qleisli.Semantics.RawAction
import QleisliKernel.Qirf.RuntimeLocalEvents

/-! Direct locality of the independent total complex Raw action.
The proof keeps the actual ordered selected axes, controls, local input sums,
dependency indices and adjoints. The concrete interval result applies only to
the retained circuit-event shape. It proves neither bounded availability/work
equivalence nor a Raw protected-program, full forest-code or Gram theorem.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.Semantics.RawAction.Locality
open QleisliKernel.Semantics.Exact QleisliKernel.Semantics.Finite
open QleisliKernel.Qirf

/-- A slice of one complete joint amplitude function, not a tensor factor. -/
def pull (base : Nat) (selected : List Nat) (values : Nat → ℂ) : Nat → ℂ :=
  fun input => values (scatter base selected input)

theorem hadamard_selected (base value : Nat) (selected : List Nat) (unique : selected.Nodup)
    (index : Nat) (bound : index < selected.length) (values : Nat → ℂ) :
    Protected.gate .h ((selected[index]?).getD 0) values (scatter base selected value) =
      Protected.gate .h index (pull base selected values) value := by
  have low := RuntimeScatterTransport.scatter_write base value selected unique index bound 0 (by decide)
  have high := RuntimeScatterTransport.scatter_write base value selected unique index bound 1 (by decide)
  simp only [RuntimeScatterTransport.write, Nat.zero_mul, Nat.add_zero, Nat.one_mul] at low high
  rw [RuntimeScatterTransport.scatter_at base value selected unique index bound] at low high
  rw [low] at high
  simp only [Protected.gate, List.getElem?_eq_getElem bound, Option.getD_some,
    RuntimeScatterTransport.scatter_at base value selected unique index bound]
  rw [low, high]
  rfl

/-- The literal localized step acts on the same scatter slice. No arithmetic
law or coefficient-success premise is needed: each complex expression has the
same operands and the same ordered local summation indices. -/
theorem step_selected (dependencies : List Dependency) (base value : Nat)
    (selected : List Nat) (unique : selected.Nodup) (operation : Step)
    (controls : ∀ control ∈ operation.controls, control.index < selected.length)
    (targets : ∀ axis ∈ QleisliKernel.Finite.targets operation.action, axis < selected.length)
    (values : Nat → ℂ) :
    step dependencies (QleisliKernel.Semantics.RawTrace.localize selected operation)
        values (scatter base selected value) =
      step dependencies operation (pull base selected values) value := by
  rcases operation with ⟨controlList, action⟩
  cases action with
  | hadamard axis =>
    have bound := targets axis (List.mem_singleton_self axis)
    simp only [step, QleisliKernel.Semantics.RawTrace.localize,
      RuntimeScatterTransport.enabled_selected base value selected unique controlList controls,
      hadamard_selected base value selected unique axis bound values, pull]
  | monomial axes permutation phases =>
    have gathered : gather (scatter base selected value)
        (axes.map fun index => (selected[index]?).getD 0) = gather value axes :=
      RuntimeScatterTransport.gather_mapped base value selected unique axes targets
    have scattered (input : Nat) : scatter (scatter base selected value)
        (axes.map fun index => (selected[index]?).getD 0) input =
          scatter base selected (scatter value axes input) :=
      RuntimeScatterTransport.scatter_mapped base value input selected unique axes targets
    simp only [step, QleisliKernel.Semantics.RawTrace.localize,
      RuntimeScatterTransport.enabled_selected base value selected unique controlList controls,
      gathered, scattered, pull]
  | contract axes dependency adjoint =>
    have gathered : gather (scatter base selected value)
        (axes.map fun index => (selected[index]?).getD 0) = gather value axes :=
      RuntimeScatterTransport.gather_mapped base value selected unique axes targets
    have scattered (input : Nat) : scatter (scatter base selected value)
        (axes.map fun index => (selected[index]?).getD 0) input =
          scatter base selected (scatter value axes input) :=
      RuntimeScatterTransport.scatter_mapped base value input selected unique axes targets
    simp only [step, QleisliKernel.Semantics.RawTrace.localize,
      RuntimeScatterTransport.enabled_selected base value selected unique controlList controls,
      gathered, scattered, pull]

theorem circuit_selected (dependencies : List Dependency) (base : Nat)
    (selected : List Nat) (unique : selected.Nodup) (operations : List Step)
    (controls : ∀ operation ∈ operations, ∀ control ∈ operation.controls, control.index < selected.length)
    (targets : ∀ operation ∈ operations, ∀ axis ∈ QleisliKernel.Finite.targets operation.action,
      axis < selected.length) (values : Nat → ℂ) :
    pull base selected (circuit dependencies
      (operations.map (QleisliKernel.Semantics.RawTrace.localize selected)) values) =
        circuit dependencies operations (pull base selected values) := by
  induction operations generalizing values with
  | nil => rfl
  | cons first rest ih =>
    have restControls : ∀ operation ∈ rest, ∀ control ∈ operation.controls, control.index < selected.length :=
      fun operation member => controls operation (List.mem_cons_of_mem _ member)
    have restTargets : ∀ operation ∈ rest, ∀ axis ∈ QleisliKernel.Finite.targets operation.action,
        axis < selected.length := fun operation member => targets operation (List.mem_cons_of_mem _ member)
    change pull base selected (circuit dependencies
        (rest.map (QleisliKernel.Semantics.RawTrace.localize selected))
        (step dependencies (QleisliKernel.Semantics.RawTrace.localize selected first) values)) =
      circuit dependencies rest (step dependencies first (pull base selected values))
    have tail : pull base selected (circuit dependencies
        (rest.map (QleisliKernel.Semantics.RawTrace.localize selected))
        (step dependencies (QleisliKernel.Semantics.RawTrace.localize selected first) values)) =
      circuit dependencies rest
        (pull base selected (step dependencies (QleisliKernel.Semantics.RawTrace.localize selected first) values)) := by
      apply ih <;> assumption
    rw [tail]
    have head : pull base selected
        (step dependencies (QleisliKernel.Semantics.RawTrace.localize selected first) values) =
          step dependencies first (pull base selected values) := by
      funext value
      exact step_selected dependencies base value selected unique first
        (controls first (List.mem_cons_self)) (targets first (List.mem_cons_self)) values
    rw [head]

theorem circuit_output (dependencies : List Dependency) (output : Nat)
    (selected : List Nat) (unique : selected.Nodup) (operations : List Step)
    (controls : ∀ operation ∈ operations, ∀ control ∈ operation.controls, control.index < selected.length)
    (targets : ∀ operation ∈ operations, ∀ axis ∈ QleisliKernel.Finite.targets operation.action,
      axis < selected.length) (values : Nat → ℂ) :
    circuit dependencies (operations.map (QleisliKernel.Semantics.RawTrace.localize selected)) values output =
      circuit dependencies operations (pull output selected values) (gather output selected) := by
  have point := congrFun (circuit_selected dependencies output selected unique operations controls targets values)
    (gather output selected)
  simpa only [pull, RuntimeScatterTransport.scatter_gather output selected unique] using point

/-- This flattening concerns only total complex circuit events. It does not
drop the distinct event charges from any bounded coefficient computation. -/
theorem circuit_events (dependencies : List Dependency) (bits : Nat) (selected : List Nat)
    (chunks : List (List Step)) (values : Nat → ℂ) :
    events dependencies (RuntimeLocalEvents.circuitEvents bits selected chunks) values =
      circuit dependencies (chunks.flatten.map (QleisliKernel.Semantics.RawTrace.localize selected)) values := by
  induction chunks generalizing values with
  | nil => rfl
  | cons first rest ih =>
    change events dependencies (RuntimeLocalEvents.circuitEvents bits selected rest)
        (circuit dependencies (first.map (QleisliKernel.Semantics.RawTrace.localize selected)) values) =
      circuit dependencies ((first :: rest).flatten.map (QleisliKernel.Semantics.RawTrace.localize selected)) values
    rw [ih]
    simp only [List.flatten_cons, List.map_append, circuit, List.foldl_append]

theorem events_output (dependencies : List Dependency) (bits : Nat) (selected : List Nat)
    (unique : selected.Nodup) (chunks : List (List Step))
    (controls : ∀ chunk ∈ chunks, ∀ operation ∈ chunk,
      ∀ control ∈ operation.controls, control.index < selected.length)
    (targets : ∀ chunk ∈ chunks, ∀ operation ∈ chunk,
      ∀ axis ∈ QleisliKernel.Finite.targets operation.action, axis < selected.length)
    (values : Nat → ℂ) (output : Nat) :
    events dependencies (RuntimeLocalEvents.circuitEvents bits selected chunks) values output =
      circuit dependencies chunks.flatten (pull output selected values) (gather output selected) := by
  rw [circuit_events]
  have allControls : ∀ operation ∈ chunks.flatten, ∀ control ∈ operation.controls,
      control.index < selected.length := by
    intro operation present control held
    obtain ⟨chunk, member, inside⟩ := List.mem_flatten.mp present
    exact controls chunk member operation inside control held
  have allTargets : ∀ operation ∈ chunks.flatten, ∀ axis ∈ QleisliKernel.Finite.targets operation.action,
      axis < selected.length := by
    intro operation present axis held
    obtain ⟨chunk, member, inside⟩ := List.mem_flatten.mp present
    exact targets chunk member operation inside axis held
  exact circuit_output dependencies output selected unique chunks.flatten allControls allTargets values

/-- Actual original interval, complete before-frame selected-owner lookup,
ordered physical wires, retained chunks and the exact local tape remain in
the subject. Every joint-reference slice is arbitrary. The circuit-only event
shape comes from `checked.literal`; no protected/computed event is reclassified
as a circuit and the enclosing final Raw output permutation is not removed. -/
theorem literal_references {Reference : Type}
    {dependencies program block start count inputs outputs roles frame selectorBits targetBits retained restricted
      beforeRoles afterRoles before after}
    (checked : @RuntimeLocalEvents.Literal dependencies program block start count inputs outputs roles frame
      selectorBits targetBits retained restricted beforeRoles afterRoles before after)
    (values : Reference → Nat → ℂ) :
    (fun reference output => events dependencies checked.traceResult.events (values reference) output) =
      (fun reference output => circuit dependencies retained.steps
        (fun input => values reference (scatter output
          (RuntimeForestCode.forestAxes frame.interval.before.quantum.frame checked.selection.selected) input))
        (gather output (RuntimeForestCode.forestAxes frame.interval.before.quantum.frame checked.selection.selected))) := by
  rw [checked.literal]
  funext reference output
  have localized := events_output dependencies frame.interval.before.quantum.frame.length
    (RuntimeForestCode.forestAxes frame.interval.before.quantum.frame checked.selection.selected)
    checked.selection.distinct checked.chunks (RuntimeLocalEvents.bounds_controls checked.bounded)
    (RuntimeLocalEvents.bounds_targets checked.bounded) (values reference) output
  simpa only [checked.localSteps, pull] using localized

#print axioms step_selected
#print axioms circuit_output
#print axioms literal_references

end Qleisli.Semantics.RawAction.Locality
