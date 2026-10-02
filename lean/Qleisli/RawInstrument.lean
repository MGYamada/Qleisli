import QleisliKernel.Raw.Instrument
import Qleisli.RawPure
import Qleisli.Semantics.InstrumentComplete
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! Actual observing acceptance, exact Kraus completeness and joint density
semantics. No Rust verification premise or producer-provided Gram is used.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.Raw.Instrument
open QleisliKernel.Semantics.Exact QleisliKernel.Semantics.Finite
open QleisliKernel.Semantics.Observation QleisliKernel.Raw.Instrument QleisliKernel.Finite
open Qleisli.Semantics.Exact
open scoped BigOperators Matrix
open scoped ComplexOrder

private theorem map_meaning {α : Type} (step : α → WorkM Scalar) (meaning : α → ℂ)
    (sound : ∀ a value work left, (step a).run work = (.ok value,left) → scalar value = meaning a)
    (xs : List α) (values : List Scalar) (work left : Nat)
    (ok : (xs.mapM step).run work = (.ok values,left)) :
    values.map scalar = xs.map meaning := by
  induction xs generalizing work values left with
  | nil =>
    have same := (pure_success _ _ _ _ ok).1
    subst values
    rfl
  | cons a xs ih =>
    simp only [List.mapM_cons] at ok
    obtain ⟨value,middle,hv,h⟩ := bind_success _ _ _ _ _ ok
    obtain ⟨rest,after,hr,h⟩ := bind_success _ _ _ _ _ h
    have same := (pure_success _ _ _ _ h).1
    subst values
    simp only [List.map_cons,sound a value work middle hv,ih rest middle after hr]

theorem add_meaning (x y z : Matrix) (work left : Nat)
    (ok : (add x y).run work = (.ok z,left)) :
    z.rows = x.rows ∧ z.cols = x.cols ∧ ∀ row col, row < x.rows → col < x.cols →
      entry z row col = entry x row col + entry y row col := by
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨values,before,hv,h⟩ := bind_success _ _ _ _ _ h
  have make := arithmetic_success _ _ (lift_success _ _ _ _ h).1
  have record := (Exact.matrix_make_result _ _ _ _ make).1
  have meaning : values.map scalar = (List.range (x.rows*x.cols)).map (fun index =>
      entry x (index / x.cols) (index % x.cols) + entry y (index / x.cols) (index % x.cols)) := by
    apply map_meaning _ _ _ _ _ _ _ hv
    intro index value work left checked
    exact Exact.scalar_add_preserves _ _ _ (arithmetic_success _ _ (lift_success _ _ _ _ checked).1)
  subst z
  refine ⟨rfl,rfl,?_⟩
  intro row col hr hc
  have result := Exact.matrix_entry_of_meanings _ _ _ _ row col hr hc meaning
  have positive : 0 < x.cols := by omega
  have divide : (row*x.cols+col) / x.cols = row := by
    rw [Nat.add_comm,Nat.add_mul_div_right col row positive,Nat.div_eq_of_lt hc,Nat.zero_add]
  simpa only [divide,Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt hc] using result

noncomputable def historyGram (history : History) (row col : Nat) : ℂ :=
  ((List.range history.operator.rows).map fun k =>
    star (entry history.operator k row) * entry history.operator k col).sum

theorem addGram_meaning (sum result : Matrix) (history : History) (work left : Nat)
    (ok : (addGram sum history).run work = (.ok result,left)) :
    result.rows = sum.rows ∧ result.cols = sum.cols ∧ sum.rows = history.operator.cols ∧
    sum.cols = history.operator.cols ∧ ∀ row col, row < sum.rows → col < sum.cols →
      entry result row col = entry sum row col + historyGram history row col := by
  obtain ⟨adjoint,middle,ha,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨gram,after,hg,h⟩ := bind_success _ _ _ _ _ h
  have adj := Exact.adjoint_meaning _ _ _ _ (exactWork_success _ _ _ _ ha)
  have product := Exact.compose_meaning _ _ _ _ _ (exactWork_success _ _ _ _ hg)
  have addition := add_meaning _ _ _ _ _ h
  have sizes : sum.rows = gram.rows ∧ sum.cols = gram.cols := by
    obtain ⟨_,_,guard,_⟩ := bind_success _ _ _ _ _ h
    simpa only [Bool.and_eq_true,beq_iff_eq] using (guard_success _ _ _ _ guard).1
  have r : sum.rows = history.operator.cols := sizes.1.trans (product.2.1.trans adj.1)
  have c : sum.cols = history.operator.cols := sizes.2.trans product.2.2.1
  refine ⟨addition.1,addition.2.1,r,c,?_⟩
  intro row col hr hc
  rw [addition.2.2 row col hr hc,product.2.2.2 row col (by omega) (by omega)]
  rw [adj.2.1]
  congr 1
  apply Exact.sum_map_congr
  intro k hk
  rw [adj.2.2 row k (by omega) (List.mem_range.mp hk)]

theorem fold_gram_meaning (histories : List History) (initial actual : Matrix) (work left : Nat)
    (ok : (histories.foldlM addGram initial).run work = (.ok actual,left)) :
    actual.rows = initial.rows ∧ actual.cols = initial.cols ∧
    ∀ row col, row < initial.rows → col < initial.cols →
      entry actual row col = entry initial row col + (histories.map (fun h => historyGram h row col)).sum := by
  induction histories generalizing initial work with
  | nil =>
    have same := (pure_success _ _ _ _ ok).1
    subst actual
    simp
  | cons history histories ih =>
    simp only [List.foldlM_cons] at ok
    obtain ⟨next,middle,hn,rest⟩ := bind_success _ _ _ _ _ ok
    have first := addGram_meaning _ _ _ _ _ hn
    have last := ih next middle rest
    refine ⟨last.1.trans first.1,last.2.1.trans first.2.1,?_⟩
    intro row col hr hc
    rw [last.2.2 row col (by omega) (by omega),first.2.2.2.2 row col hr hc]
    simp only [List.map_cons,List.sum_cons]
    ring

/-- Exact acceptance checks the complete sum, including reset/discard outcomes
which are not public classical results and zero-probability branches. -/
theorem gram_meaning (bits : Nat) (histories : List History) (actual : Matrix) (work left : Nat)
    (ok : (gram bits histories).run work = (.ok actual,left)) :
    actual.rows = 2^bits ∧ actual.cols = 2^bits ∧ ∀ row col, row < 2^bits → col < 2^bits →
      entry actual row col = (histories.map (fun h => historyGram h row col)).sum := by
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨zero,middle,hz,h⟩ := bind_success _ _ _ _ _ h
  have same := (Exact.matrix_make_result _ _ _ _ (arithmetic_success _ _ (lift_success _ _ _ _ hz).1)).1
  have folded := fold_gram_meaning _ _ _ _ _ h
  subst zero
  refine ⟨folded.1,folded.2.1,?_⟩
  intro row col hr hc
  rw [folded.2.2 row col hr hc]
  have zeros : entry ⟨2^bits,2^bits,List.replicate (2^bits*2^bits) Scalar.zero⟩ row col = 0 := by
    apply (Exact.matrix_entry_of_meanings _ _ _ (fun _ => (0 : ℂ)) row col hr hc _).trans
    · rfl
    · simp [Exact.scalar_zero_meaning]
  rw [zeros,zero_add]

theorem inspect_complete (inputs : List QleisliKernel.Semantics.Function.Input)
    (bindings : List QleisliKernel.Semantics.Function.Binding) (program : Program)
    (classical : List Bool) (checked : Checked) (work left : Nat)
    (ok : (inspect inputs bindings program classical).run work = (.ok checked,left)) :
    checked.structureCheck.program = program ∧
    QleisliKernel.Semantics.Observation.read program = some checked.structureCheck.prepared ∧
    ∀ row col, row < 2^checked.structureCheck.prepared.inputBits → col < 2^checked.structureCheck.prepared.inputBits →
      (checked.histories.map (fun h => historyGram h row col)).sum = if row = col then 1 else 0 := by
  rcases inspect_conditions _ _ _ _ _ _ _ ok with ⟨receipts,a,b,c,d,e,f,total,identity,_,hs,hg,hi,equal⟩
  have original := QleisliKernel.Raw.Observation.verify_conditions _ _ _ _ _ hs
  have complete := gram_meaning _ _ _ _ _ hg
  have identityEntries := (Exact.identity_meaning _ _ hi).2.2.2
  refine ⟨original.1,original.2.2,?_⟩
  intro row col hr hc
  rw [← complete.2.2 row col hr hc,equal]
  exact identityEntries row col hr hc

private theorem range_sum (n : Nat) (f : Nat → ℂ) :
    ((List.range n).map f).sum = ∑ k : Fin n, f k := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.range_succ,List.map_append,List.sum_append,List.map_singleton,List.sum_singleton]
    rw [Fin.sum_univ_castSucc]
    simpa only [Fin.val_castSucc,Fin.val_last] using congrArg (fun z => z + f n) ih

noncomputable def family (checked : Checked) (index : Fin checked.histories.length) :
    _root_.Matrix (Fin (2^checked.structureCheck.state.quantum.frame.length))
      (Fin (2^checked.structureCheck.prepared.inputBits)) ℂ :=
  fun row col => entry checked.histories[index].operator row col

/-- The complete family is proved from the actual executable Gram sum and
actual final interface checking, not supplied as an isometry premise. -/
theorem accepted_kraus_complete (inputs : List QleisliKernel.Semantics.Function.Input)
    (bindings : List QleisliKernel.Semantics.Function.Binding) (program : Program)
    (classical : List Bool) (checked : Checked) (work left : Nat)
    (ok : (inspect inputs bindings program classical).run work = (.ok checked,left)) :
    ∑ i, (family checked i)ᴴ * family checked i = 1 := by
  have complete := (inspect_complete _ _ _ _ _ _ _ ok).2.2
  rcases QleisliKernel.Raw.Instrument.inspect_execution _ _ _ _ _ _ _ ok with
    ⟨_,_,_,_,_,_,_,_,_,_,_,_,shape⟩
  have rows : ∀ h ∈ checked.histories,
      h.operator.rows = 2^checked.structureCheck.state.quantum.frame.length := by
    simp only [List.all_eq_true,Bool.and_eq_true,beq_iff_eq] at shape
    exact fun h member => (shape h member).1
  ext row col
  simp only [Matrix.sum_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.one_apply]
  have lists : (checked.histories.map (fun h => historyGram h row col)).sum =
      ∑ i, ∑ k, star (family checked i k row) * family checked i k col := by
    rw [← List.ofFn_getElem_eq_map checked.histories (fun h => historyGram h row col),List.sum_ofFn]
    apply Finset.sum_congr rfl
    intro i _
    rw [historyGram,rows _ (List.getElem_mem _)]
    exact range_sum _ _
  rw [← lists]
  have result := complete row col row.isLt col.isLt
  simpa only [Fin.ext_iff] using result

/-- Every public outcome is a sum of unnormalized hidden histories. Extending
by identity on an arbitrary reference proves complete positivity, including
partial Bell measurement, discard, reset and adaptive classical feedback. -/
theorem outcome_positive {Reference : Type} [Fintype Reference] [DecidableEq Reference]
    (checked : Checked) (selected : Fin checked.histories.length → Bool)
    (rho : _root_.Matrix (Fin (2^checked.structureCheck.prepared.inputBits) × Reference)
      (Fin (2^checked.structureCheck.prepared.inputBits) × Reference) ℂ)
    (positive : rho.PosSemidef) :
    (∑ i, if selected i then Qleisli.Semantics.Instrument.density (family checked i) rho else 0).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro i _
  split
  · exact positive.mul_mul_conjTranspose_same _
  · exact Matrix.PosSemidef.zero

theorem accepted_trace_preserving {Reference : Type} [Fintype Reference] [DecidableEq Reference]
    (inputs : List QleisliKernel.Semantics.Function.Input) (bindings : List QleisliKernel.Semantics.Function.Binding)
    (program : Program) (classical : List Bool) (checked : Checked) (work left : Nat)
    (ok : (inspect inputs bindings program classical).run work = (.ok checked,left))
    (rho : _root_.Matrix (Fin (2^checked.structureCheck.prepared.inputBits) × Reference)
      (Fin (2^checked.structureCheck.prepared.inputBits) × Reference) ℂ) :
    ∑ i, Matrix.trace (Qleisli.Semantics.Instrument.density (family checked i) rho) = Matrix.trace rho := by
  exact Qleisli.Semantics.Instrument.complete_trace _ (accepted_kraus_complete _ _ _ _ _ _ _ ok) rho

/-- A selected public outcome cannot increase trace on any positive joint
input. Its complement retains all other hidden histories; there is no
postselection or renormalization inside the accepted instrument. -/
theorem accepted_outcome_trace_nonincreasing {Reference : Type} [Fintype Reference] [DecidableEq Reference]
    (inputs : List QleisliKernel.Semantics.Function.Input) (bindings : List QleisliKernel.Semantics.Function.Binding)
    (program : Program) (classical : List Bool) (checked : Checked) (work left : Nat)
    (ok : (inspect inputs bindings program classical).run work = (.ok checked,left))
    (selected : Fin checked.histories.length → Bool)
    (rho : _root_.Matrix (Fin (2^checked.structureCheck.prepared.inputBits) × Reference)
      (Fin (2^checked.structureCheck.prepared.inputBits) × Reference) ℂ) (positive : rho.PosSemidef) :
    (∑ i, if selected i then Matrix.trace (Qleisli.Semantics.Instrument.density (family checked i) rho) else 0).re ≤
      (Matrix.trace rho).re := by
  have total := accepted_trace_preserving _ _ _ _ _ _ _ ok rho
  rw [← total,Complex.re_sum,Complex.re_sum]
  apply Finset.sum_le_sum
  intro i _
  split
  · rfl
  · simpa using Complex.re_le_re (positive.mul_mul_conjTranspose_same
      (Qleisli.Semantics.Instrument.withReference (family checked i))).trace_nonneg

end Qleisli.Raw.Instrument
