import Qleisli.Exact
import QleisliKernel.Raw.InstrumentEquality
import Qleisli.RawInstrumentDenotation
import ReferenceEquality

/-! Refinement of the actual streamed native coefficient computation to the
independent complex meaning. This experiment is not a public acceptance gate
or a source-preservation/constitutional discharge.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.Experiments.InstrumentCoefficient
open QleisliKernel.Semantics.Exact QleisliKernel.Finite
open QleisliKernel.Raw.InstrumentEquality
open Qleisli.Semantics.Exact

private theorem lookup_list_reference (outputs : List Nat)
    (values : QleisliKernel.Raw.Instrument.Values) (actual : List Bool) (work left : Nat)
    (ok : (outputs.mapM (QleisliKernel.Raw.Instrument.lookup values)).run work = (.ok actual,left)) :
    outputs.mapM (Qleisli.Semantics.RawInstrument.value values) = some actual := by
  induction outputs generalizing actual work left with
  | nil =>
    have same := (pure_success _ _ _ _ ok).1
    subst actual
    rfl
  | cons output rest ih =>
    simp only [List.mapM_cons] at ok ⊢
    obtain ⟨value,middle,hv,h⟩ := bind_success _ _ _ _ _ ok
    obtain ⟨tail,after,ht,h⟩ := bind_success _ _ _ _ _ h
    have same := (pure_success _ _ _ _ h).1
    subst actual
    simp [Qleisli.Raw.Instrument.Denotation.lookup_reference _ _ _ _ _ hv, ih _ _ _ ht]

/-- Preparation preserves each reconstructed matrix and projects its original
classical values in the selected public order, without sorting or relabeling. -/
theorem prepare_reference (outputs : List Nat)
    (original : List QleisliKernel.Raw.Instrument.History) (prepared : List History)
    (work left : Nat) (ok : (prepare outputs original).run work = (.ok prepared,left)) :
    List.Forall₂ (fun source target => source.operator = target.operator ∧
      outputs.mapM (Qleisli.Semantics.RawInstrument.value source.values) = some target.outcome)
      original prepared := by
  induction original generalizing prepared work left with
  | nil =>
    have same := (pure_success _ _ _ _ ok).1
    subst prepared
    exact .nil
  | cons history rest ih =>
    unfold prepare at ok
    simp only [List.mapM_cons] at ok
    obtain ⟨value,middle,hv,h⟩ := bind_success _ _ _ _ _ ok
    obtain ⟨tail,after,ht,h⟩ := bind_success _ _ _ _ _ h
    have same := (pure_success _ _ _ _ h).1
    subst prepared
    obtain ⟨_,last,_,hv⟩ := bind_success _ _ _ _ _ hv
    obtain ⟨outcome,final,ho,hv⟩ := bind_success _ _ _ _ _ hv
    have selected := (pure_success _ _ _ _ hv).1
    subst value
    exact .cons ⟨rfl,lookup_list_reference _ _ _ _ _ ho⟩ (ih _ _ _ ht)

noncomputable def contribution (outcome : List Bool) (row col otherRow otherCol : Nat)
    (history : History) : ℂ :=
  if history.outcome = outcome then
    entry history.operator row col * star (entry history.operator otherRow otherCol)
  else 0

/-- Complete unnormalized coefficient: every hidden history with the chosen
public label contributes once, including repeated/equivalent Kraus terms. -/
noncomputable def meaning (histories : List History) (outcome : List Bool)
    (row col otherRow otherCol : Nat) : ℂ :=
  (histories.map (contribution outcome row col otherRow otherCol)).sum

private theorem fold_meaning {A : Type} (step : Scalar → A → WorkM Scalar)
    (term : A → ℂ)
    (sound : ∀ initial a result work left,
      (step initial a).run work = (.ok result,left) →
      scalar result = scalar initial + term a)
    (xs : List A) (initial result : Scalar) (work left : Nat)
    (ok : (xs.foldlM step initial).run work = (.ok result,left)) :
    scalar result = scalar initial + (xs.map term).sum := by
  induction xs generalizing initial work left with
  | nil =>
    have same := (pure_success _ _ _ _ ok).1
    simp only [same, List.map_nil, List.sum_nil, add_zero]
  | cons a xs ih =>
    simp only [List.foldlM_cons] at ok
    obtain ⟨next,middle,hn,hr⟩ := bind_success _ _ _ _ _ ok
    rw [ih next middle left hr, sound _ _ _ _ _ hn]
    simp only [List.map_cons, List.sum_cons, add_assoc]

/-- A successful native calculation equals the full complex CP coefficient.
Budget/capacity failures make no claim; no probability-only quotient is used. -/
theorem coefficient_meaning (histories : List History) (outcome : List Bool)
    (row col otherRow otherCol : Nat) (result : Scalar) (work left : Nat)
    (ok : (coefficient histories outcome row col otherRow otherCol).run work =
      (.ok result,left)) :
    scalar result = meaning histories outcome row col otherRow otherCol := by
  unfold coefficient at ok
  have folded := fold_meaning _ (contribution outcome row col otherRow otherCol)
    ?_ histories Scalar.zero result work left ok
  · simpa [meaning, scalar, Scalar.zero, rational, Coefficient.integer] using folded
  · intro initial history result work left accepted
    obtain ⟨_,middle,_,h⟩ := bind_success _ _ _ _ _ accepted
    split at h
    · have same := (pure_success _ _ _ _ h).1
      simp_all [contribution]
    · rename_i equalLabel
      simp only [pure_bind] at h
      obtain ⟨_,after,_,h⟩ := bind_success _ _ _ _ _ h
      obtain ⟨conjugate,last,hc,h⟩ := bind_success _ _ _ _ _ h
      obtain ⟨product,final,hp,ha⟩ := bind_success _ _ _ _ _ h
      have conjugated := Qleisli.Exact.scalar_conjugate_preserves _ _
        (arithmetic_success _ _ (lift_success _ _ _ _ hc).1)
      have multiplied := Qleisli.Exact.scalar_mul_preserves _ _ _
        (arithmetic_success _ _ (lift_success _ _ _ _ hp).1)
      have added := Qleisli.Exact.scalar_add_preserves _ _ _
        (arithmetic_success _ _ (lift_success _ _ _ _ ha).1)
      simp_all [contribution, entry]

private theorem forM_member {A : Type} (xs : List A) (step : A → WorkM Unit)
    (work left : Nat) (ok : (xs.forM step).run work = (.ok (),left))
    (a : A) (member : a ∈ xs) :
    ∃ before after, (step a).run before = (.ok (),after) := by
  induction xs generalizing work left with
  | nil => simp at member
  | cons head tail ih =>
    change (step head >>= fun _ => tail.forM step).run work = (.ok (),left) at ok
    obtain ⟨_,middle,hh,ht⟩ := bind_success _ _ _ _ _ ok
    rcases List.mem_cons.mp member with same | rest
    · subst a
      exact ⟨work,middle,hh⟩
    · exact ih middle left ht rest

private theorem meaning_zero_of_absent (histories : List History) (outcome : List Bool)
    (row col otherRow otherCol : Nat)
    (absent : outcome ∉ histories.map (·.outcome)) :
    meaning histories outcome row col otherRow otherCol = 0 := by
  induction histories with
  | nil => simp [meaning]
  | cons history rest ih =>
    have distinct : history.outcome ≠ outcome := by
      intro same
      exact absent (by simp [same])
    have remaining : outcome ∉ rest.map (·.outcome) := by
      intro member
      exact absent (by simp [member])
    simpa [meaning, contribution, distinct] using ih remaining

/-- Successful comparison covers every physical coordinate and every public
label. Unlisted/impossible labels denote zero on both sides. -/
theorem compare_meaning (rows cols results : Nat) (actual expected : List History)
    (work left : Nat)
    (ok : (QleisliKernel.Raw.InstrumentEquality.compare rows cols results actual expected).run work = (.ok (),left))
    (outcome : List Bool) (row col otherRow otherCol : Nat)
    (hr : row < rows) (hc : col < cols) (hor : otherRow < rows) (hoc : otherCol < cols) :
    meaning actual outcome row col otherRow otherCol =
      meaning expected outcome row col otherRow otherCol := by
  by_cases present : outcome ∈ (actual ++ expected).map (·.outcome)
  · unfold QleisliKernel.Raw.InstrumentEquality.compare at ok
    obtain ⟨_,w₁,_,h⟩ := bind_success _ _ _ _ _ ok
    obtain ⟨_,w₂,_,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨_,w₃,_,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨_,w₄,_,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨w₅,w₆,h⟩ := forM_member _ _ _ _ h outcome (by simpa using present)
    obtain ⟨_,w₇,_,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨w₈,w₉,h⟩ := forM_member _ _ _ _ h row (by simpa using hr)
    obtain ⟨w₁₀,w₁₁,h⟩ := forM_member _ _ _ _ h col (by simpa using hc)
    obtain ⟨w₁₂,w₁₃,h⟩ := forM_member _ _ _ _ h otherRow (by simpa using hor)
    obtain ⟨w₁₄,w₁₅,h⟩ := forM_member _ _ _ _ h otherCol (by simpa using hoc)
    obtain ⟨a,w₁₆,ha,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨b,w₁₇,hb,he⟩ := bind_success _ _ _ _ _ h
    have equal := Qleisli.Exact.equality_preserves a b (guard_success _ _ _ _ he).1
    rw [coefficient_meaning _ _ _ _ _ _ _ _ _ ha,
        coefficient_meaning _ _ _ _ _ _ _ _ _ hb] at equal
    exact equal
  · have absentActual : outcome ∉ actual.map (·.outcome) := by
      intro member
      exact present (by simp [List.map_append, member])
    have absentExpected : outcome ∉ expected.map (·.outcome) := by
      intro member
      exact present (by simp [List.map_append, member])
    rw [meaning_zero_of_absent _ _ _ _ _ _ absentActual,
        meaning_zero_of_absent _ _ _ _ _ _ absentExpected]

/-- The independent complex matrix family uses a zero Kraus operator for
histories belonging to another public outcome. Hidden indices are private. -/
noncomputable def operators (histories : List History) (outcome : List Bool)
    (rows cols : Nat) : Fin histories.length → Matrix (Fin rows) (Fin cols) ℂ :=
  fun index row col => if (histories.get index).outcome = outcome then
    entry (histories.get index).operator row.val col.val else 0

theorem choi_meaning (histories : List History) (outcome : List Bool) (rows cols : Nat)
    (row otherRow : Fin rows) (col otherCol : Fin cols) :
    Qleisli.Experiments.InstrumentEquality.choi (operators histories outcome rows cols)
        (row,col) (otherRow,otherCol) =
      meaning histories outcome row.val col.val otherRow.val otherCol.val := by
  unfold Qleisli.Experiments.InstrumentEquality.choi meaning
  rw [← List.ofFn_getElem_eq_map, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro index _
  simp only [operators, contribution, List.get_eq_getElem]
  split <;> simp_all

/-- Actual native comparison implies equality of the complete unnormalized
instrument on any joint input matrix with an arbitrary finite reference. -/
theorem compare_instrument {R : Type} [Fintype R] [DecidableEq R]
    (rows cols results : Nat) (actual expected : List History) (work left : Nat)
    (ok : (QleisliKernel.Raw.InstrumentEquality.compare rows cols results actual expected).run work =
      (.ok (),left)) (rho : Matrix (Fin cols × R) (Fin cols × R) ℂ) :
    (fun outcome => Qleisli.Experiments.InstrumentEquality.channel
      (operators actual outcome rows cols) rho) =
    (fun outcome => Qleisli.Experiments.InstrumentEquality.channel
      (operators expected outcome rows cols) rho) := by
  apply Qleisli.Experiments.InstrumentEquality.instrument_eq_of_choi_eq
  intro outcome
  ext ⟨row,col⟩ ⟨otherRow,otherCol⟩
  rw [choi_meaning, choi_meaning]
  exact compare_meaning _ _ _ _ _ _ _ ok _ _ _ _ _ row.isLt col.isLt otherRow.isLt otherCol.isLt

end Qleisli.Experiments.InstrumentCoefficient
