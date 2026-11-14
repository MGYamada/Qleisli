import Qleisli.RuntimeComputedProtectedAction
import QleisliKernel.Qirf.StructuralComputedRaw

/-! Exact clean return for the structurally checked source predicate and use.
Keep the entire data/reference amplitude family through the existing
non-dense protected model, without constructing a truth table or matrix.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.StructuralComputedRestoration
open QleisliKernel Qirf
open Qleisli.Semantics.Protected
open Qleisli.Semantics.Exact (scalar)

def selected {sources caller} {event : SourceTypes.SourceRuntimeContext.ComputedEvent sources caller}
    (original : StructuralXorPredicate.Original event) (source : Nat) : Nat :=
  (Semantics.SourceOrdinary.evaluate (StructuralXorPredicate.valuation original.fields source)
    original.expression).getD 0

theorem selected_bit {sources caller} {event : SourceTypes.SourceRuntimeContext.ComputedEvent sources caller}
    (original : StructuralXorPredicate.Original event) (source : Nat) :
    selected original source = 0 ∨ selected original source = 1 := by
  unfold selected
  rw [original.compiled.evaluates, Option.getD_some]
  cases StructuralXor.predicate original.compiled.clauses source <;> decide

private theorem bit_of_packed_source (width source aux : Nat)
    (controls : List Semantics.Finite.Control)
    (inside : ∀ control ∈ controls, control.index < width) :
    Semantics.Finite.enabled controls (FiniteRestriction.pack width source aux) =
      Semantics.Finite.enabled controls source := by
  induction controls with
  | nil => rfl
  | cons control rest ih =>
    have head := FiniteRestriction.bit_selector width source aux control.index
      (inside control List.mem_cons_self)
    have tail := ih (fun item present => inside item (List.mem_cons_of_mem _ present))
    simp only [Semantics.Finite.enabled, List.all_cons] at tail ⊢
    rw [head, tail]

private theorem selected_packed {sources caller} {event : SourceTypes.SourceRuntimeContext.ComputedEvent sources caller}
    {original : StructuralXorPredicate.Original event} {steps : List Semantics.Finite.Step}
    (checked : StructuralXor.Checked original.width original.compiled.clauses steps)
    (source aux : Nat) :
    StructuralXor.predicate original.compiled.clauses (FiniteRestriction.pack original.width source aux) =
      StructuralXor.predicate original.compiled.clauses source := by
  have fold (clauses : List (List Semantics.Finite.Control)) (initial : Bool)
      (inside : ∀ controls ∈ clauses, ∀ control ∈ controls, control.index < original.width) :
      clauses.foldl (fun parity controls => Bool.xor parity
        (Semantics.Finite.enabled controls (FiniteRestriction.pack original.width source aux))) initial =
      clauses.foldl (fun parity controls => Bool.xor parity
        (Semantics.Finite.enabled controls source)) initial := by
    induction clauses generalizing initial with
    | nil => rfl
    | cons controls rest ih =>
      simp only [List.foldl_cons]
      rw [bit_of_packed_source _ _ _ _ (inside controls List.mem_cons_self)]
      exact ih _ (fun clause member => inside clause (List.mem_cons_of_mem _ member))
  exact fold _ false checked.disjoint

private theorem aux_write (width source aux : Nat) (bound : source < 2^width)
    (small : aux < 2) (choice : Bool) :
    StructuralXor.targetUpdate width (FiniteRestriction.pack width source aux) choice =
      FiniteRestriction.pack width source (aux ^^^ choice.toNat) := by
  cases choice with
  | false => simp [StructuralXor.targetUpdate]
  | true =>
    have auxBit : Semantics.Finite.bit aux 0 = aux := by
      simp [Semantics.Finite.bit, Nat.mod_eq_of_lt small]
    change RuntimeScatterTransport.write (FiniteRestriction.pack width source aux) width
      (1 - Semantics.Finite.bit (FiniteRestriction.pack width source aux) width) =
      FiniteRestriction.pack width source (aux ^^^ 1)
    have atAxis := FiniteRestriction.bit_target width source aux 0 bound
    rw [Nat.add_zero, auxBit] at atAxis
    have replacement : Semantics.Finite.bit (1-aux) 0 = 1-aux := by
      have smallReplacement : 1-aux < 2 := by omega
      simp [Semantics.Finite.bit, Nat.mod_eq_of_lt smallReplacement]
    have written := FiniteRestriction.update_pack width source aux 0 (1-aux) 0 bound
    simp only [Nat.add_zero, Nat.pow_zero, Nat.mul_one, auxBit, atAxis, replacement, Nat.sub_self,
      Nat.zero_add] at written
    simp only [RuntimeScatterTransport.write, atAxis]
    rw [written]
    have flip : 1-aux = aux ^^^ 1 := by
      have cases : aux = 0 ∨ aux = 1 := by omega
      rcases cases with rfl | rfl <;> rfl
    rw [flip]

/-- On the packed data-and-scratch coordinates, a checked literal circuit
performs the same reversible XOR used by the protected restoration theorem. -/
theorem literal_xor {sources caller} {event : SourceTypes.SourceRuntimeContext.ComputedEvent sources caller}
    {original : StructuralXorPredicate.Original event} {steps : List Semantics.Finite.Step}
    (checked : StructuralXor.Checked original.width original.compiled.clauses steps)
    (source aux : Nat) (bound : source < 2^original.width) (small : aux < 2)
    (value : Semantics.Exact.Scalar) (valid : QleisliKernel.Exact.Scalar.valid value = true)
    (nonzero : value ≠ Semantics.Exact.Scalar.zero) :
    steps.foldlM (fun row step => do
      let [(output, coefficient)] ← Finite.contributions [] step row.1 row.2 | throw Finite.Error.equation
      return (output, coefficient)) (FiniteRestriction.pack original.width source aux, value) =
    .ok (FiniteRestriction.pack original.width source (aux ^^^ selected original source), value) := by
  have literal := checked.action (FiniteRestriction.pack original.width source aux) value valid nonzero
  have output : StructuralXor.targetUpdate original.width (FiniteRestriction.pack original.width source aux)
      (StructuralXor.predicate original.compiled.clauses (FiniteRestriction.pack original.width source aux)) =
      FiniteRestriction.pack original.width source (aux ^^^ selected original source) := by
    rw [selected_packed checked source aux, aux_write _ _ _ bound small]
    simp only [selected, original.compiled.evaluates, Option.getD_some]
  rw [output] at literal
  exact literal

/-- The clean scratch factors out with its original zero value even when the
data and reference are entangled. The retained live action includes the exact
common phase from the independently reconstructed original two-entry diagonal. -/
theorem clean_return {sources caller computeSteps inverseSteps uses}
    {event : SourceTypes.SourceRuntimeContext.ComputedEvent sources caller}
    {original : StructuralXorPredicate.Original event}
    (checked : StructuralComputedUse.Checked original computeSteps inverseSteps uses)
    {R : Type} (ψ : Logical R) :
    compute (selected original) (run uses (compute (selected original) (zero ψ))) =
      zero (fun source target reference =>
        ψ source target reference * scalar (checked.action.matrix.entry
          (selected original source) (selected original source))) := by
  have diagonal : ∀ use ∈ uses, DiagonalProtected use := by
    intro use present
    cases use with
    | protectedGate location gate => exact checked.emitted.diagonalGate location gate present
    | targetGate _ _ _ => trivial
    | phase _ _ => trivial
  rw [clean_factorization _ uses diagonal]
  congr 1
  funext source target reference
  unfold logical
  rw [← checked.equation]
  have parts := RuntimeComputedProtectedAction.auxiliary_fibres checked.emitted source (ψ source) target reference
  rcases selected_bit original source with off | on
  · simpa [off, RuntimeComputedUse.RawAction.matrix, Semantics.Exact.Matrix.entry] using parts.1
  · simpa [on, RuntimeComputedUse.RawAction.matrix, Semantics.Exact.Matrix.entry] using parts.2

/-- The literal forward and inverse both have the protected model's XOR action
on any valid joint data/auxiliary label, with the original coefficient. -/
theorem literal_pair {sources caller computeSteps inverseSteps uses}
    {event : SourceTypes.SourceRuntimeContext.ComputedEvent sources caller}
    {original : StructuralXorPredicate.Original event}
    (checked : StructuralComputedUse.Checked original computeSteps inverseSteps uses)
    (source aux : Nat) (bound : source < 2^original.width) (small : aux < 2)
    (value : Semantics.Exact.Scalar) (valid : QleisliKernel.Exact.Scalar.valid value = true)
    (nonzero : value ≠ Semantics.Exact.Scalar.zero) :
    ∀ steps ∈ [computeSteps, inverseSteps],
      steps.foldlM (fun row step => do
        let [(output, coefficient)] ← Finite.contributions [] step row.1 row.2 | throw Finite.Error.equation
        return (output, coefficient)) (FiniteRestriction.pack original.width source aux, value) =
      .ok (FiniteRestriction.pack original.width source (aux ^^^ selected original source), value) := by
  intro steps present
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl
  · exact literal_xor checked.forward source aux bound small value valid nonzero
  · exact literal_xor checked.reverse source aux bound small value valid nonzero

/-- The source-bound Raw transition retains the frame and keeps its newly
issued scratch private. The same checked packet supplies the all-reference
zero-return equation for the original phase action. -/
theorem checked_packet {sources caller}
    {event : SourceTypes.SourceRuntimeContext.ComputedEvent sources caller}
    {original : StructuralXorPredicate.Original event} {packet before entry}
    (checked : StructuralComputedRaw.SourceChecked original packet before entry)
    {R : Type} (ψ : Logical R) :
    packet.scratch ∉ entry.quantum.seenWires ∧
    packet.scratch ∈ checked.raw.after.seenWires ∧
    packet.scratch ∉ checked.raw.after.frame ∧
    checked.raw.after.frame = entry.quantum.frame ∧
    compute (selected original) (run packet.uses (compute (selected original) (zero ψ))) =
      zero (fun source target reference =>
        ψ source target reference * scalar (checked.matched.action.matrix.entry
          (selected original source) (selected original source))) :=
  ⟨checked.raw.scratchIssued.1,checked.raw.scratchIssued.2,checked.raw.scratchPrivate,
    checked.raw.sameFrame,clean_return checked.matched ψ⟩

#print axioms clean_return
#print axioms literal_xor
#print axioms literal_pair
#print axioms checked_packet

end Qleisli.StructuralComputedRestoration
