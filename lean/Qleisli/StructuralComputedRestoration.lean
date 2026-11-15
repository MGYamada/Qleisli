import Qleisli.RuntimeComputedProtectedAction
import Qleisli.RuntimeForestProduct
import Qleisli.Semantics.RawAction
import QleisliKernel.Qirf.RuntimeLocalEvents
import QleisliKernel.Qirf.RuntimeScatterTransport
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
    change FiniteRestriction.BitUpdate.write (FiniteRestriction.pack width source aux) width
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
    simp only [FiniteRestriction.BitUpdate.write, atAxis]
    rw [written]
    have flip : 1-aux = aux ^^^ 1 := by
      have cases : aux = 0 ∨ aux = 1 := by omega
      rcases cases with rfl | rfl <;> rfl
    rw [flip]

private theorem raw_toggle (axis : Nat) (controls : List Semantics.Finite.Control)
    (ψ : Nat → ℂ) (label : Nat) :
    Qleisli.Semantics.RawAction.step [] (StructuralXor.toggle axis controls) ψ label =
      ψ (StructuralXor.targetUpdate axis label (Semantics.Finite.enabled controls label)) := by
  unfold Qleisli.Semantics.RawAction.step
  change (if !Semantics.Finite.enabled controls label then ψ label else _) = _
  cases enabled : Semantics.Finite.enabled controls label with
  | false => simp [StructuralXor.targetUpdate]
  | true =>
    have bounds := FiniteRestriction.BitUpdate.bit_lt label axis
    have gather : Semantics.Finite.gather label [axis] = Semantics.Finite.bit label axis := by
      simp [Semantics.Finite.gather, List.zipIdx_cons, List.zipIdx_nil]
    have scatter (value : Nat) (small : value < 2) :
        Semantics.Finite.scatter label [axis] value =
          FiniteRestriction.BitUpdate.write label axis value := by
      simp [Semantics.Finite.scatter, FiniteRestriction.BitUpdate.write,
        List.zipIdx_cons, List.zipIdx_nil, Semantics.Finite.bit, Nat.mod_eq_of_lt small]
    have bitCases : Semantics.Finite.bit label axis = 0 ∨ Semantics.Finite.bit label axis = 1 := by
      omega
    have indices : List.range 2 = [0,1] := by decide
    rcases bitCases with off | on
    · simpa [StructuralXor.toggle, Semantics.RawTrace.gate, StructuralXor.targetUpdate,
        gather, off, indices, Qleisli.Semantics.Finite.phase] using congrArg ψ (scatter 1 (by decide))
    · simpa [StructuralXor.toggle, Semantics.RawTrace.gate, StructuralXor.targetUpdate,
        gather, on, indices, Qleisli.Semantics.Finite.phase] using congrArg ψ (scatter 0 (by decide))

private theorem predicate_cons (control : List Semantics.Finite.Control)
    (clauses : List (List Semantics.Finite.Control)) (label : Nat) :
    StructuralXor.predicate (control :: clauses) label =
      Bool.xor (StructuralXor.predicate clauses label) (Semantics.Finite.enabled control label) := by
  have fold (a b : Bool) :
      clauses.foldl (fun parity row => Bool.xor parity (Semantics.Finite.enabled row label)) (Bool.xor a b) =
        Bool.xor
          (clauses.foldl (fun parity row => Bool.xor parity (Semantics.Finite.enabled row label)) a) b := by
    induction clauses generalizing a with
    | nil => rfl
    | cons row rest ih =>
      simp only [List.foldl_cons]
      rw [show ((a ^^ b) ^^ Semantics.Finite.enabled row label) =
          ((a ^^ Semantics.Finite.enabled row label) ^^ b) by
        cases a <;> cases b <;> cases Semantics.Finite.enabled row label <;> decide]
      exact ih _
  exact fold false (Semantics.Finite.enabled control label)

private theorem raw_circuit (axis : Nat) (clauses : List (List Semantics.Finite.Control))
    (inside : ∀ clause ∈ clauses, ∀ control ∈ clause, control.index < axis)
    (ψ : Nat → ℂ) (label : Nat) :
    Qleisli.Semantics.RawAction.circuit [] (clauses.map (StructuralXor.toggle axis)) ψ label =
      ψ (StructuralXor.targetUpdate axis label (StructuralXor.predicate clauses label)) := by
  induction clauses generalizing ψ with
  | nil => rfl
  | cons clause rest ih =>
    unfold Qleisli.Semantics.RawAction.circuit
    simp only [List.map_cons, List.foldl_cons]
    change Qleisli.Semantics.RawAction.circuit [] (rest.map (StructuralXor.toggle axis))
      (Qleisli.Semantics.RawAction.step [] (StructuralXor.toggle axis clause) ψ) label = _
    rw [ih (fun clause member => inside clause (List.mem_cons_of_mem _ member)), raw_toggle,
      StructuralXor.enabled_update _ _ _ _
        (fun control member => Nat.ne_of_lt (inside clause List.mem_cons_self control member)),
      StructuralXor.targetUpdate_xor, predicate_cons]

/-- The complex-amplitude interpreter reads the same reversible XOR action
from the literal forward or inverse circuit, with no support or product-state
assumption on the input function. -/
theorem literal_circuit_xor {sources caller}
    {event : SourceTypes.SourceRuntimeContext.ComputedEvent sources caller}
    {original : StructuralXorPredicate.Original event} {steps : List Semantics.Finite.Step}
    (checked : StructuralXor.Checked original.width original.compiled.clauses steps)
    (ψ : Nat → ℂ) (source aux : Nat) (bound : source < 2^original.width) (small : aux < 2) :
    Qleisli.Semantics.RawAction.circuit [] steps ψ (FiniteRestriction.pack original.width source aux) =
      ψ (FiniteRestriction.pack original.width source (aux ^^^ selected original source)) := by
  rw [checked.literal, raw_circuit _ _ checked.disjoint, selected_packed checked source aux,
    aux_write _ _ _ bound small]
  simp only [selected, original.compiled.evaluates, Option.getD_some]

private theorem packed_aux_bit (width source aux : Nat) (bound : source < 2^width) :
    Semantics.Finite.bit (FiniteRestriction.pack width source aux) width =
      Semantics.Finite.bit aux 0 := by
  simpa only [Nat.add_zero] using FiniteRestriction.bit_target width source aux 0 bound

private theorem physical_controls (width source aux : Nat) (bound : source < 2^width)
    (controls : List Semantics.Raw.ProtectedControl)
    (valid : Raw.protectedControlsValid 0 1 controls = true) :
    Semantics.Finite.enabled (controls.map fun control =>
      ⟨Semantics.Protected.axis width control.bit,control.whenOne⟩)
      (FiniteRestriction.pack width source aux) =
      Semantics.Protected.enabled source aux controls := by
  have all := (Bool.and_eq_true_iff.mp valid).1
  clear valid
  induction controls with
  | nil => rfl
  | cons first rest ih =>
    obtain ⟨⟨region,index⟩,polarity⟩ := first
    simp only [List.all_cons, Bool.and_eq_true] at all
    cases region
    case source =>
      simp [Raw.protectedValid] at all
    case ancilla =>
      have zero : index = 0 := by
        simpa [Raw.protectedValid, Nat.lt_one_iff] using all.1
      subst index
      simp only [Semantics.Finite.enabled, List.map_cons, List.all_cons,
        Semantics.Protected.enabled, Semantics.Protected.axis, Nat.add_zero,
        packed_aux_bit _ _ _ bound, Semantics.Protected.value]
      congr 1
      exact ih all.2

private theorem raw_diagonal (axis exponent label : Nat) (ψ : Nat → ℂ) :
    Qleisli.Semantics.RawAction.step [] ⟨[],.monomial [axis] [0,1] [0,exponent]⟩ ψ label =
      ψ label * (if Semantics.Finite.bit label axis == 1 then Qleisli.Semantics.Finite.phase exponent else 1) := by
  have bounds := FiniteRestriction.BitUpdate.bit_lt label axis
  have gather : Semantics.Finite.gather label [axis] = Semantics.Finite.bit label axis := by
    simp [Semantics.Finite.gather, List.zipIdx_cons, List.zipIdx_nil]
  have keep : Semantics.Finite.scatter label [axis] (Semantics.Finite.bit label axis) = label := by
    rw [← gather]
    exact RuntimeScatterTransport.scatter_gather label [axis] (by simp)
  have indices : List.range 2 = [0,1] := by decide
  have zeroPhase : Qleisli.Semantics.Finite.phase 0 = 1 := rfl
  have bitCases : Semantics.Finite.bit label axis = 0 ∨ Semantics.Finite.bit label axis = 1 := by
    omega
  rcases bitCases with off | on
  · rw [off] at keep
    simp [Qleisli.Semantics.RawAction.step, Semantics.Finite.enabled, indices, gather, off, keep, zeroPhase]
  · rw [on] at keep
    simp [Qleisli.Semantics.RawAction.step, Semantics.Finite.enabled, indices, gather, on, keep]

private theorem physical_step (width source aux : Nat) (bound : source < 2^width)
    (operation : Semantics.Raw.Use) (valid : Raw.usesValid 0 1 0 [operation] = true)
    (ψ : Nat → ℂ) :
    Qleisli.Semantics.RawAction.step [] (Semantics.Protected.physical 0 width operation) ψ
      (FiniteRestriction.pack width source aux) =
    blockUse source aux operation (fun _ (_ : Unit) => ψ (FiniteRestriction.pack width source aux)) 0 () := by
  simp only [Raw.usesValid, List.all_cons, List.all_nil, Bool.and_true] at valid
  cases operation with
  | protectedGate location gate =>
    obtain ⟨region,index⟩ := location
    have checks := Bool.and_eq_true_iff.mp valid
    cases region
    case source =>
      simp [Raw.protectedValid] at checks
    case ancilla =>
      have zero : index = 0 := by
        simpa [Raw.protectedValid, Nat.lt_one_iff] using checks.1
      subst index
      have diagonal : gate = .z ∨ gate = .t := by
        simpa only [Bool.or_eq_true, beq_iff_eq] using checks.2
      rcases diagonal with rfl | rfl <;>
        simpa [Semantics.Protected.physical, Semantics.Protected.axis, Semantics.RawTrace.gate,
          blockUse, Semantics.Protected.value, packed_aux_bit _ _ _ bound] using
          raw_diagonal width _ (FiniteRestriction.pack width source aux) ψ
  | targetGate controls target gate =>
    simp at valid
  | phase controls operation =>
    have enabled := physical_controls width source aux bound controls valid
    have indices : List.range 1 = [0] := by decide
    simp [Semantics.Protected.physical, Qleisli.Semantics.RawAction.step, enabled, blockUse,
      indices, Semantics.Finite.scatter, Semantics.Finite.gather, List.zipIdx_nil]
    cases Semantics.Protected.enabled source aux controls <;> simp

private theorem physical_uses (width source aux : Nat) (bound : source < 2^width)
    (uses : List Semantics.Raw.Use) (valid : Raw.usesValid 0 1 0 uses = true) (ψ : Nat → ℂ) :
    Qleisli.Semantics.RawAction.circuit [] (uses.map (Semantics.Protected.physical 0 width)) ψ
      (FiniteRestriction.pack width source aux) =
    blocks source aux uses (fun _ (_ : Unit) => ψ (FiniteRestriction.pack width source aux)) 0 () := by
  induction uses generalizing ψ with
  | nil => rfl
  | cons operation rest ih =>
    have checks : Raw.usesValid 0 1 0 [operation] = true ∧ Raw.usesValid 0 1 0 rest = true := by
      simpa only [Raw.usesValid, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] using valid
    change Qleisli.Semantics.RawAction.circuit [] (rest.map (Semantics.Protected.physical 0 width))
        (Qleisli.Semantics.RawAction.step [] (Semantics.Protected.physical 0 width operation) ψ)
        (FiniteRestriction.pack width source aux) =
      blocks source aux rest
        (blockUse source aux operation (fun _ (_ : Unit) => ψ (FiniteRestriction.pack width source aux))) 0 ()
    rw [ih checks.2]
    congr 1
    funext target reference
    cases reference
    have action := physical_step width source aux bound operation checks.1 ψ
    rw [action]
    cases operation with
    | protectedGate => rfl
    | phase => rfl
    | targetGate => simp [Raw.usesValid] at checks

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

/-- The actual emitted forward, use, and inverse circuit implements the
original phase and returns the private auxiliary to zero. Each reference
slice may be an arbitrary amplitude function of the live data. -/
theorem literal_clean_return {sources caller computeSteps inverseSteps uses}
    {event : SourceTypes.SourceRuntimeContext.ComputedEvent sources caller}
    {original : StructuralXorPredicate.Original event}
    (checked : StructuralComputedUse.Checked original computeSteps inverseSteps uses)
    (valid : Raw.usesValid 0 1 0 uses = true) (ψ : Nat → ℂ)
    (source aux : Nat) (bound : source < 2^original.width) (small : aux < 2) :
    Qleisli.Semantics.RawAction.circuit []
      (computeSteps ++ uses.map (Semantics.Protected.physical 0 original.width) ++ inverseSteps)
      (fun label => if label < 2^original.width then ψ label else 0)
      (FiniteRestriction.pack original.width source aux) =
      if aux = 0 then ψ source * scalar (checked.action.matrix.entry
        (selected original source) (selected original source)) else 0 := by
  have chosen : selected original source < 2 := by
    rcases selected_bit original source with off | on <;> omega
  have xorSmall {left right : Nat} (leftBit : left < 2) (rightBit : right < 2) : left ^^^ right < 2 := by
    have leftCases : left = 0 ∨ left = 1 := by omega
    have rightCases : right = 0 ∨ right = 1 := by omega
    rcases leftCases with rfl | rfl <;> rcases rightCases with rfl | rfl <;> decide
  have append (before after : List Semantics.Finite.Step) (values : Nat → ℂ) :
      Qleisli.Semantics.RawAction.circuit [] (before ++ after) values =
        Qleisli.Semantics.RawAction.circuit [] after
          (Qleisli.Semantics.RawAction.circuit [] before values) := by
    simp only [Qleisli.Semantics.RawAction.circuit, List.foldl_append]
  rw [append, append, literal_circuit_xor checked.reverse _ source aux bound small,
    physical_uses _ source _ bound uses valid]
  have beforeUse := literal_circuit_xor checked.forward
    (fun label => if label < 2^original.width then ψ label else 0) source _
    bound (xorSmall small chosen)
  rw [beforeUse, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  have initial :
      (if FiniteRestriction.pack original.width source aux < 2^original.width
        then ψ (FiniteRestriction.pack original.width source aux) else 0) =
      if aux = 0 then ψ source else 0 := by
    by_cases zero : aux = 0
    · simpa [zero, FiniteRestriction.pack] using
        (if_pos bound : (if source < 2^original.width then ψ source else 0) = ψ source)
    · have tooLarge : ¬ FiniteRestriction.pack original.width source aux < 2^original.width := by
        unfold FiniteRestriction.pack
        have atLeast := Nat.mul_le_mul_left (2^original.width) (Nat.one_le_iff_ne_zero.mpr zero)
        simp only [Nat.mul_one] at atLeast
        omega
      simp [zero, tooLarge]
  simp only [initial]
  by_cases zero : aux = 0
  · subst aux
    simp only [Nat.zero_xor, ← checked.equation]
    have parts := RuntimeComputedProtectedAction.auxiliary_fibres checked.emitted source
      (fun _ (_ : Unit) => ψ source) 0 ()
    rcases selected_bit original source with off | on
    · simpa [off, RuntimeComputedUse.RawAction.matrix, Semantics.Exact.Matrix.entry] using parts.1
    · simpa [on, RuntimeComputedUse.RawAction.matrix, Semantics.Exact.Matrix.entry] using parts.2
  · simp only [if_neg zero, blocks_zero]

/-- The same phase acts on the literal selected axes of the caller frame.
An arbitrary caller amplitude function retains all spectator correlations. -/
theorem literal_event {sources caller computeSteps inverseSteps uses}
    {event : SourceTypes.SourceRuntimeContext.ComputedEvent sources caller}
    {original : StructuralXorPredicate.Original event}
    (checked : StructuralComputedUse.Checked original computeSteps inverseSteps uses)
    (valid : Raw.usesValid 0 1 0 uses = true) (dependencies : List Semantics.Finite.Dependency)
    (bits : Nat) (axes : List Nat) (width : axes.length = original.width) (unique : axes.Nodup)
    (ψ : Nat → ℂ) (row : Nat) :
    Qleisli.Semantics.RawAction.event dependencies
      (.structuralComputed bits axes computeSteps inverseSteps uses) ψ row =
    ψ row * scalar (checked.action.matrix.entry
      (selected original (Semantics.Finite.gather row axes))
      (selected original (Semantics.Finite.gather row axes))) := by
  have bounded := Qleisli.RuntimeForestProduct.gather_bound row axes
  rw [width] at bounded
  have action := literal_clean_return checked valid (fun input => ψ (Semantics.Finite.scatter row axes input))
    (Semantics.Finite.gather row axes) 0 bounded (by decide)
  simpa only [Qleisli.Semantics.RawAction.event, Qleisli.Semantics.RawAction.embed, width,
    FiniteRestriction.pack, Nat.mul_zero, Nat.add_zero, if_pos rfl,
    RuntimeScatterTransport.scatter_gather row axes unique] using action

/-- Extract the very event checked in the source interval, with the caller's
ordered axes and unchanged frame. -/
theorem interval_trace {sources caller dependencies program block start count}
    {event : SourceTypes.SourceRuntimeContext.ComputedEvent sources caller}
    {interval : @RuntimeInterval.Checked dependencies program block start count} {before}
    (checked : StructuralComputedRaw.IntervalChecked event interval before) :
    let prior := interval.before.quantum
    let after := interval.after.quantum
    let raw := checked.checked.raw
    after.frame = prior.frame ∧
    RuntimeLocalEvents.trace prior.reference [checked.packet.operation] = some
      ⟨after.reference,[.structuralComputed prior.frame.length
        (raw.input.wires.map prior.frame.idxOf) checked.packet.forward
        checked.packet.inverse checked.packet.uses],prior.frame.length⟩ := by
  intro prior after raw
  have taken : Semantics.RawTrace.take prior.reference checked.packet.input =
      some (raw.input,raw.taken.reference) := Raw.take_reference _ _ _ _ raw.takeRead
  have reserved := Raw.reserve_reference _ _ _ raw.reserveRead
  have matching : raw.after = after := checked.afterQuantum
  have inserted : Semantics.RawTrace.insert raw.taken.reference checked.packet.output raw.input.wires =
      after.reference := by
    rw [← reserved, ← Raw.insert_reference _ _ _ _ raw.insertRead, matching]
  refine ⟨matching ▸ raw.sameFrame,?_⟩
  simp only [RuntimeLocalEvents.trace, List.foldlM_cons, List.foldlM_nil, Semantics.RawTrace.advance,
    StructuralComputedRaw.Packet.operation, Semantics.RawTrace.step, taken, bind, Option.bind, pure, inserted]
  rfl

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
#print axioms literal_circuit_xor
#print axioms literal_clean_return
#print axioms literal_event
#print axioms interval_trace
#print axioms literal_xor
#print axioms literal_pair
#print axioms checked_packet

end Qleisli.StructuralComputedRestoration
