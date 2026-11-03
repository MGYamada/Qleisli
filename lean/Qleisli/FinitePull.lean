import Qleisli.Finite
import Qleisli.Semantics.RawAction
import QleisliKernel.Qirf.RuntimeScatterTransport
import QleisliKernel.Raw.Ownership
import Mathlib.Data.Nat.Bitwise

/-! Successful finite-vector steps denote the independent backward action.
The original contribution/accumulation order is unchanged. Only the resulting
complex sums are rearranged; no bounded arithmetic operation, error or work
state is identified with a reassociated computation. This is a mathematical
one-step bridge, not an isometry proof or a new acceptance gate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.Finite
open QleisliKernel.Semantics.Exact QleisliKernel.Semantics.Finite QleisliKernel.Finite
open Qleisli.Semantics.Exact

namespace Pull

namespace Scatter
export QleisliKernel.Qirf.RuntimeScatterTransport
  (bit_lt scatter_outside scatter_at gather_at scatter_gather)
end Scatter

private theorem bit_ext (left right : Nat)
    (same : ∀ axis, bit left axis = bit right axis) : left = right := by
  apply Nat.eq_of_testBit_eq
  intro axis
  have equal := same axis
  simp only [bit] at equal
  rw [← Nat.toNat_testBit left axis, ← Nat.toNat_testBit right axis] at equal
  cases leftBit : left.testBit axis <;> cases rightBit : right.testBit axis <;> simp_all

private theorem bit_zero (label bits axis : Nat) (bound : label < 2^bits)
    (outside : bits ≤ axis) : bit label axis = 0 := by
  have power : 2^bits ≤ 2^axis := by gcongr <;> norm_num
  simp [bit, Nat.div_eq_of_lt (Nat.lt_of_lt_of_le bound power)]

private theorem bound_of_bits (label bits : Nat)
    (outside : ∀ axis, bits ≤ axis → bit label axis = 0) : label < 2^bits := by
  have cleared (axis : Nat) (after : bits ≤ axis) : label.testBit axis = false := by
    have zero := outside axis after
    simp only [bit] at zero
    rw [← Nat.toNat_testBit label axis] at zero
    cases value : label.testBit axis <;> simp_all
  apply Nat.lt_of_testBit bits (cleared bits (Nat.le_refl _)) (by simp)
  intro axis after
  rw [cleared axis (Nat.le_of_lt after)]
  simp [Nat.testBit_two_pow_of_ne (Nat.ne_of_lt after)]

private theorem gather_cons (label first : Nat) (rest : List Nat) :
    gather label (first :: rest) = bit label first + 2*gather label rest := by
  have weights (pairs : List (Nat × Nat)) :
      (pairs.map (fun pair => bit label pair.1 * 2^(pair.2+1))).sum =
        2*(pairs.map (fun pair => bit label pair.1 * 2^pair.2)).sum := by
    induction pairs with
    | nil => rfl
    | cons first rest ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      simp only [Nat.pow_succ, Nat.mul_add]
      ac_rfl
  unfold gather
  simp only [List.zipIdx_cons, List.map_cons, List.sum_cons, Nat.pow_zero, Nat.mul_one]
  rw [List.zipIdx_succ]
  simp only [List.map_map, Function.comp_def]
  rw [weights]

private theorem gather_bound (label : Nat) (axes : List Nat) : gather label axes < 2^axes.length := by
  induction axes with
  | nil => simp [gather]
  | cons axis axes ih =>
    rw [gather_cons, List.length_cons, Nat.pow_succ]
    have small := Scatter.bit_lt label axis
    omega

private theorem scatter_bound (label bits value : Nat) (axes : List Nat)
    (bound : label < 2^bits) (axesBound : ∀ axis ∈ axes, axis < bits) :
    scatter label axes value < 2^bits := by
  apply bound_of_bits
  intro axis after
  have absent : axis ∉ axes := by
    intro present
    have before := axesBound axis present
    omega
  rw [Scatter.scatter_outside label value axis axes absent, bit_zero label bits axis bound after]

private theorem gather_scatter (label value : Nat) (axes : List Nat)
    (unique : axes.Nodup) (bound : value < 2^axes.length) :
    gather (scatter label axes value) axes = value := by
  apply bit_ext
  intro axis
  by_cases before : axis < axes.length
  · rw [Scatter.gather_at _ axes axis before, Scatter.scatter_at _ _ axes unique axis before]
  · rw [bit_zero _ axes.length axis (gather_bound _ axes) (by omega),
      bit_zero value axes.length axis bound (by omega)]

private theorem scatter_overwrite (label first second : Nat) (axes : List Nat)
    (unique : axes.Nodup) :
    scatter (scatter label axes first) axes second = scatter label axes second := by
  apply bit_ext
  intro axis
  by_cases present : axis ∈ axes
  · obtain ⟨index, bound, same⟩ := List.getElem_of_mem present
    subst axis
    rw [Scatter.scatter_at _ _ axes unique index bound, Scatter.scatter_at _ _ axes unique index bound]
  · rw [Scatter.scatter_outside _ _ axis axes present,
      Scatter.scatter_outside _ _ axis axes present, Scatter.scatter_outside _ _ axis axes present]

private theorem scatter_equal (label row output : Nat) (axes : List Nat)
    (unique : axes.Nodup) (bound : output < 2^axes.length) :
    row = scatter label axes output ↔
      gather row axes = output ∧ label = scatter row axes (gather label axes) := by
  constructor
  · intro same
    subst row
    exact ⟨gather_scatter label output axes unique bound, by
      rw [scatter_overwrite label output (gather label axes) axes unique,
        Scatter.scatter_gather label axes unique]⟩
  · rintro ⟨coordinate, original⟩
    conv_rhs => rw [original]
    rw [scatter_overwrite row (gather label axes) output axes unique,
      ← coordinate, Scatter.scatter_gather row axes unique]

private theorem enabled_scatter (controls : List Control) (label value : Nat) (axes : List Nat)
    (outside : ∀ control ∈ controls, control.index ∉ axes) :
    enabled controls (scatter label axes value) = enabled controls label := by
  induction controls with
  | nil => rfl
  | cons control controls ih =>
    change (((bit (scatter label axes value) control.index == 1) == control.whenOne) &&
      enabled controls (scatter label axes value)) =
        (((bit label control.index == 1) == control.whenOne) && enabled controls label)
    rw [Scatter.scatter_outside label value control.index axes (outside control (by simp)),
      ih (fun c present => outside c (by simp [present]))]

private theorem geometry (dependencies : List Dependency) (bits : Nat) (step : Step)
    (valid : stepValid dependencies bits step = true) :
    (targets step.action).Nodup ∧
      (∀ axis ∈ targets step.action, axis < bits) ∧
      (∀ control ∈ step.controls, control.index ∉ targets step.action) := by
  have checked : axesValid bits (step.controls.map (·.index) ++ targets step.action) = true := by
    simp only [stepValid, Bool.and_eq_true] at valid
    tauto
  have bounded : ∀ axis ∈ step.controls.map (·.index) ++ targets step.action, axis < bits := by
    simp only [axesValid, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at checked
    tauto
  have distinct : ((step.controls.map (·.index) ++ targets step.action).eraseDups.length ==
      (step.controls.map (·.index) ++ targets step.action).length) = true := by
    simp only [axesValid, Bool.and_eq_true] at checked
    tauto
  have unique := QleisliKernel.Raw.Ownership.unique_nodup _ distinct
  refine ⟨(List.nodup_append.mp unique).2.1,
    fun axis present => bounded axis (List.mem_append_right _ present), ?_⟩
  intro control present collision
  exact (List.nodup_append.mp unique).2.2 control.index
    (List.mem_map.mpr ⟨control, present, rfl⟩) control.index collision rfl

/-- Mathematical local coefficients. These use the independent complex meaning,
not the bounded scalar implementation or an acceptance summary. -/
private noncomputable def kernel (dependencies : List Dependency) (action : Action)
    (output input : Nat) : ℂ :=
  match action with
  | .hadamard _ => if output = 1 ∧ input = 1 then -Qleisli.Semantics.Finite.halfRoot
      else Qleisli.Semantics.Finite.halfRoot
  | .monomial _ permutation phases =>
    if permutation[input]? = some output then Qleisli.Semantics.Finite.phase (phases[input]?.getD 0) else 0
  | .contract _ index adjoint =>
    match dependencies[index]? with
    | none => 0
    | some dependency => if adjoint then star (entry dependency.meaning input output)
        else entry dependency.meaning output input

private theorem rawStar_meaning (value : Scalar) :
    scalar (Qleisli.Semantics.Finite.rawStar value) = star (scalar value) := by
  simp [Qleisli.Semantics.Finite.rawStar, scalar, rational]
  ring

private theorem option_fold_pure {α β : Type} (items : List α) (initial : β) (step : β → α → β) :
    items.foldlM (fun acc item => some (step acc item)) initial = some (items.foldl step initial) := by
  induction items generalizing initial with
  | nil => rfl
  | cons item items ih => simp only [List.foldlM_cons, List.foldl_cons]; exact ih _

private theorem append_fold {α β : Type} (items : List α) (initial : List β) (f : α → List β) :
    items.foldl (fun acc item => acc ++ f item) initial = initial ++ items.flatMap f := by
  induction items generalizing initial with
  | nil => simp
  | cons item items ih => simp [ih, List.append_assoc]

private theorem sum_flatMap {α : Type} (items : List α) (f : α → List ℂ) :
    (items.flatMap f).sum = (items.map (fun item => (f item).sum)).sum := by
  induction items with
  | nil => rfl
  | cons item items ih => simp [ih]

private theorem factor_ite (p q : Prop) [Decidable p] [Decidable q] (a b : ℂ) :
    (if p ∧ q then a*b else 0) = if q then a*(if p then b else 0) else 0 := by
  by_cases first : p <;> by_cases second : q <;> simp [first, second]

private theorem active_contributions (dependencies : List Dependency) (bits : Nat) (step : Step)
    (valid : stepValid dependencies bits step = true) (label row : Nat) (value : Scalar)
    (nonzero : value ≠ Scalar.zero) (active : enabled step.controls label = true) :
    ∃ terms, Qleisli.Semantics.Finite.contributions dependencies step label value = some terms ∧
      (terms.map (fun term => if row = term.1 then term.2 else 0)).sum =
        if scatter label (targets step.action) (gather row (targets step.action)) = row then
          scalar value * kernel dependencies step.action
            (gather row (targets step.action)) (gather label (targets step.action)) else 0 := by
  have unique := (geometry dependencies bits step valid).1
  rcases step with ⟨controls, action⟩
  cases action with
  | hadamard axis =>
    let low := label - bit label axis * 2^axis
    let high := low + 2^axis
    let amplitude := scalar value * Qleisli.Semantics.Finite.halfRoot
    have lowScatter : scatter label [axis] 0 = low := by simp [scatter, low, bit]
    have highScatter : scatter label [axis] 1 = high := by simp [scatter, high, low, bit]
    have lowRow := scatter_equal label row 0 [axis] unique (by simp)
    have highRow := scatter_equal label row 1 [axis] unique (by simp)
    have sign : label = high ↔ bit label axis = 1 := by
      have weight := QleisliKernel.FiniteRestriction.bit_weight_le label axis
      have small := Scatter.bit_lt label axis
      have positive : 0 < 2^axis := Nat.two_pow_pos _
      have bitCases : bit label axis = 0 ∨ bit label axis = 1 := by omega
      rcases bitCases with coordinate | coordinate
      · simp only [high, low, coordinate, Nat.zero_mul, Nat.sub_zero]
        omega
      · have contained : 2^axis ≤ label := by simpa only [coordinate, Nat.one_mul] using weight
        simp [high, low, coordinate, Nat.sub_add_cancel contained]
    refine ⟨[(low, amplitude), (high, if label = high then -amplitude else amplitude)], ?_, ?_⟩
    · simp [Qleisli.Semantics.Finite.contributions, nonzero, active, low, high, amplitude]
    · have inputSmall := Scatter.bit_lt label axis
      have outputSmall := Scatter.bit_lt row axis
      have gathered (n : Nat) : gather n [axis] = bit n axis := by simp [gather]
      have mask : scatter label [axis] (gather row [axis]) = row ↔
          label = scatter row [axis] (gather label [axis]) := by
        constructor
        · intro same
          exact ((scatter_equal label row _ [axis] unique (gather_bound row [axis])).mp same.symm).2
        · intro same
          exact ((scatter_equal label row _ [axis] unique (gather_bound row [axis])).mpr ⟨rfl, same⟩).symm
      rw [lowScatter] at lowRow
      rw [highScatter] at highRow
      by_cases spectator : label = scatter row [axis] (gather label [axis])
      · have lowIff : row = low ↔ bit row axis = 0 := by
          constructor
          · intro same
            simpa only [gathered] using (lowRow.mp same).1
          · intro coordinate
            exact lowRow.mpr ⟨by simpa only [gathered] using coordinate, spectator⟩
        have highIff : row = high ↔ bit row axis = 1 := by
          constructor
          · intro same
            simpa only [gathered] using (highRow.mp same).1
          · intro coordinate
            exact highRow.mpr ⟨by simpa only [gathered] using coordinate, spectator⟩
        have selected := mask.mpr spectator
        have inputCases : bit label axis = 0 ∨ bit label axis = 1 := by omega
        have outputCases : bit row axis = 0 ∨ bit row axis = 1 := by omega
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, targets]
        rw [if_pos selected]
        simp only [lowIff, highIff, sign, kernel, gathered]
        rcases inputCases with inputCoordinate | inputCoordinate <;>
          rcases outputCases with outputCoordinate | outputCoordinate <;>
          simp [inputCoordinate, outputCoordinate] <;> dsimp [amplitude] <;> ring
      · have lowNot : row ≠ low := by
          intro same
          exact spectator ((lowRow.mp same).2)
        have highNot : row ≠ high := by
          intro same
          exact spectator ((highRow.mp same).2)
        simp [targets, lowNot, highNot, mask, spectator]
  | monomial axes permutation phases =>
    have readValid := valid
    simp only [stepValid, targets, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
      decide_eq_true_eq] at readValid
    have size : permutation.length = 2^axes.length := by tauto
    have phaseSize : phases.length = permutation.length := by tauto
    have outputs : ∀ output ∈ permutation, output < 2^axes.length := by tauto
    have inputBound : gather label axes < permutation.length := by rw [size]; exact gather_bound label axes
    have phaseBound : gather label axes < phases.length := by omega
    let output := permutation[gather label axes]'inputBound
    let exponent := phases[gather label axes]'phaseBound
    have outputBound : output < 2^axes.length := outputs output (List.getElem_mem inputBound)
    have coordinates := scatter_equal label row output axes unique outputBound
    refine ⟨[(scatter label axes output, scalar value * Qleisli.Semantics.Finite.phase exponent)], ?_, ?_⟩
    · simp [Qleisli.Semantics.Finite.contributions, nonzero, active, output, exponent,
        List.getElem?_eq_getElem inputBound, List.getElem?_eq_getElem phaseBound]
    · have mask : scatter label axes (gather row axes) = row ↔
          label = scatter row axes (gather label axes) := by
        constructor
        · intro same
          exact ((scatter_equal label row _ axes unique (gather_bound row axes)).mp same.symm).2
        · intro same
          exact ((scatter_equal label row _ axes unique (gather_bound row axes)).mpr ⟨rfl, same⟩).symm
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
        targets, kernel, List.getElem?_eq_getElem inputBound, List.getElem?_eq_getElem phaseBound,
        Option.getD_some]
      change (if row = scatter label axes output then scalar value * Qleisli.Semantics.Finite.phase exponent else 0) =
        if scatter label axes (gather row axes) = row then
          scalar value * (if output = gather row axes then Qleisli.Semantics.Finite.phase exponent else 0) else 0
      have reverse : output = gather row axes ↔ gather row axes = output := eq_comm
      simp only [coordinates, mask, reverse]
      exact factor_ite _ _ _ _
  | contract axes index adjoint =>
    have found : ∃ dependency, dependencies[index]? = some dependency ∧
        dependency.meaning.rows = 2^axes.length ∧ dependency.meaning.cols = 2^axes.length := by
      cases lookup : dependencies[index]? with
      | none => simp [stepValid, lookup] at valid
      | some dependency =>
        refine ⟨dependency, rfl, ?_⟩
        simp only [stepValid, lookup, bind, Option.bind, pure, Option.getD_some,
          Bool.and_eq_true, beq_iff_eq] at valid
        tauto
    obtain ⟨dependency, lookup, rows, _cols⟩ := found
    let raw := fun output => if adjoint then Qleisli.Semantics.Finite.rawStar
      (dependency.meaning.entry (gather label axes) output)
      else dependency.meaning.entry output (gather label axes)
    let coefficient := fun output => if adjoint then star (entry dependency.meaning (gather label axes) output)
      else entry dependency.meaning output (gather label axes)
    let pieces := fun output => if raw output = Scalar.zero then []
      else [(scatter label axes output, scalar value * coefficient output)]
    have rawMeaning (output : Nat) : scalar (raw output) = coefficient output := by
      cases adjoint <;> simp [raw, coefficient, entry, rawStar_meaning]
    refine ⟨(List.range dependency.meaning.rows).flatMap pieces, ?_, ?_⟩
    · simp only [Qleisli.Semantics.Finite.contributions, beq_iff_eq, nonzero, if_false,
        active, Bool.not_true, Bool.false_eq_true, lookup, bind, Option.bind, pure]
      rw [option_fold_pure]
      have localStep : (fun (acc : List (Nat × ℂ)) (output : Nat) =>
          if raw output = Scalar.zero then acc
          else acc ++ [(scatter label axes output, scalar value * coefficient output)]) =
          (fun acc output => acc ++ pieces output) := by
        funext acc output
        split <;> simp [pieces, *]
      change some ((List.range dependency.meaning.rows).foldl
        (fun acc output => if raw output = Scalar.zero then acc
          else acc ++ [(scatter label axes output, scalar value * coefficient output)]) []) = _
      rw [localStep, append_fold]
      rfl
    · rw [List.map_flatMap, sum_flatMap]
      have point (output : Nat) (present : output ∈ List.range dependency.meaning.rows) :
          ((pieces output).map (fun term => if row = term.1 then term.2 else 0)).sum =
            if gather row axes = output ∧ label = scatter row axes (gather label axes)
            then scalar value * coefficient output else 0 := by
        have outputBound : output < 2^axes.length := by rw [← rows]; exact List.mem_range.mp present
        have coordinate := scatter_equal label row output axes unique outputBound
        by_cases zero : raw output = Scalar.zero
        · have vanished : coefficient output = 0 := by rw [← rawMeaning, zero, Exact.scalar_zero_meaning]
          simp [pieces, zero, vanished]
        · simp [pieces, zero, coordinate]
      rw [Exact.sum_map_congr _ _ _ point]
      have mask : scatter label axes (gather row axes) = row ↔
          label = scatter row axes (gather label axes) := by
        constructor
        · intro same
          exact ((scatter_equal label row _ axes unique (gather_bound row axes)).mp same.symm).2
        · intro same
          exact ((scatter_equal label row _ axes unique (gather_bound row axes)).mpr ⟨rfl, same⟩).symm
      by_cases spectator : label = scatter row axes (gather label axes)
      · have collapse (output : Nat) :
            (gather row axes = output ∧ label = scatter row axes (gather label axes)) ↔
              gather row axes = output := ⟨And.left, fun coordinate => ⟨coordinate, spectator⟩⟩
        simp only [collapse]
        rw [Exact.range_delta_sum _ _ _ (by rw [rows]; exact gather_bound row axes)]
        simp only [targets, if_pos (mask.mpr spectator), kernel, lookup, coefficient]
      · simp [spectator, mask, targets]

private theorem contributions_entry (dependencies : List Dependency) (bits : Nat) (step : Step)
    (valid : stepValid dependencies bits step = true) (label row : Nat) (value : Scalar) :
    ∃ terms, Qleisli.Semantics.Finite.contributions dependencies step label value = some terms ∧
      (terms.map (fun term => if row = term.1 then term.2 else 0)).sum =
        if !enabled step.controls row then (if row = label then scalar value else 0)
        else if scatter label (targets step.action) (gather row (targets step.action)) = row then
          scalar value * kernel dependencies step.action
            (gather row (targets step.action)) (gather label (targets step.action)) else 0 := by
  by_cases zero : value = Scalar.zero
  · subst value
    refine ⟨[], by simp [Qleisli.Semantics.Finite.contributions], ?_⟩
    simp [Exact.scalar_zero_meaning]
  · have controls := (geometry dependencies bits step valid).2.2
    have onMask (mask : scatter label (targets step.action) (gather row (targets step.action)) = row) :
        enabled step.controls row = enabled step.controls label := by
      rw [← mask]
      exact enabled_scatter step.controls label _ (targets step.action) controls
    cases active : enabled step.controls label with
    | false =>
      refine ⟨[(label, scalar value)], ?_, ?_⟩
      · simp [Qleisli.Semantics.Finite.contributions, zero, active]
      · by_cases same : row = label
        · subst row; simp [active]
        · by_cases mask : scatter label (targets step.action) (gather row (targets step.action)) = row
          · simp [onMask mask, active, same]
          · simp [same, mask]
    | true =>
      obtain ⟨terms, read, coefficient⟩ := active_contributions dependencies bits step valid label row value zero active
      refine ⟨terms, read, ?_⟩
      rw [coefficient]
      by_cases mask : scatter label (targets step.action) (gather row (targets step.action)) = row
      · simp [onMask mask, active, mask]
      · have different : row ≠ label := by
          intro same
          subst row
          exact mask (Scatter.scatter_gather label _ (geometry dependencies bits step valid).1)
        simp [mask, different]

private theorem terms_length (terms : List (Nat × ℂ)) (values : List ℂ) :
    (terms.foldl Qleisli.Semantics.Finite.addAt values).length = values.length := by
  induction terms generalizing values with
  | nil => rfl
  | cons term terms ih =>
    rw [List.foldl_cons, ih (Qleisli.Semantics.Finite.addAt values term)]
    simp only [Qleisli.Semantics.Finite.addAt, List.length_set]

private theorem terms_entry (terms : List (Nat × ℂ)) (values : List ℂ) (row : Nat)
    (bound : row < values.length) :
    (terms.foldl Qleisli.Semantics.Finite.addAt values)[row]?.getD 0 =
      values[row]?.getD 0 + (terms.map (fun term => if row = term.1 then term.2 else 0)).sum := by
  induction terms generalizing values with
  | nil => simp
  | cons term terms ih =>
    rw [List.foldl_cons, ih _ (by simpa [Qleisli.Semantics.Finite.addAt] using bound)]
    by_cases same : row = term.1
    · subst row
      simp [Qleisli.Semantics.Finite.addAt, bound, add_assoc]
    · simp [Qleisli.Semantics.Finite.addAt, same, Ne.symm same]

private theorem fold_entry (dependencies : List Dependency) (bits : Nat) (step : Step)
    (valid : stepValid dependencies bits step = true) (items : List (Scalar × Nat))
    (initial : List ℂ) (row : Nat) (bound : row < initial.length) :
    ∃ result, items.foldlM (fun next (value, label) => do
        let terms ← Qleisli.Semantics.Finite.contributions dependencies step label value
        pure (terms.foldl Qleisli.Semantics.Finite.addAt next)) initial = some result ∧
      result.length = initial.length ∧ result[row]?.getD 0 = initial[row]?.getD 0 +
        (items.map (fun item =>
          if !enabled step.controls row then (if row = item.2 then scalar item.1 else 0)
          else if scatter item.2 (targets step.action) (gather row (targets step.action)) = row then
            scalar item.1 * kernel dependencies step.action
              (gather row (targets step.action)) (gather item.2 (targets step.action)) else 0)).sum := by
  induction items generalizing initial with
  | nil => exact ⟨initial, rfl, rfl, by simp⟩
  | cons item items ih =>
    obtain ⟨terms, read, coefficient⟩ := contributions_entry dependencies bits step valid item.2 row item.1
    have size := terms_length terms initial
    obtain ⟨result, rest, resultSize, entry⟩ := ih (terms.foldl Qleisli.Semantics.Finite.addAt initial)
      (by rw [size]; exact bound)
    refine ⟨result, ?_, resultSize.trans size, ?_⟩
    · simpa only [List.foldlM_cons, read, bind, Option.bind, pure] using rest
    · rw [entry, terms_entry terms initial row bound, coefficient]
      simp [add_assoc]

private theorem sum_fiber (bits row : Nat) (axes : List Nat) (unique : axes.Nodup)
    (axesBound : ∀ axis ∈ axes, axis < bits) (rowBound : row < 2^bits)
    (f : Nat → Nat → ℂ) :
    ((List.range (2^bits)).map (fun label =>
      if scatter label axes (gather row axes) = row then f label (gather label axes) else 0)).sum =
        ((List.range (2^axes.length)).map (fun input => f (scatter row axes input) input)).sum := by
  have expand (label : Nat) :
      (if scatter label axes (gather row axes) = row then f label (gather label axes) else 0) =
        ((List.range (2^axes.length)).map (fun input =>
          if gather label axes = input ∧ scatter label axes (gather row axes) = row
          then f label input else 0)).sum := by
    by_cases mask : scatter label axes (gather row axes) = row
    · simp only [mask, and_true, if_true]
      exact (Exact.range_delta_sum _ _ _ (gather_bound label axes)).symm
    · simp [mask]
  rw [Exact.sum_map_congr _ _ _ (fun label _ => expand label), Exact.sum_swap]
  apply Exact.sum_map_congr
  intro input member
  have inputBound := List.mem_range.mp member
  have physicalBound := scatter_bound row bits input axes rowBound axesBound
  have condition (label : Nat) :
      (gather label axes = input ∧ scatter label axes (gather row axes) = row) ↔
        label = scatter row axes input := by
    constructor
    · rintro ⟨coordinate, mask⟩
      have original := ((scatter_equal label row _ axes unique (gather_bound row axes)).mp mask.symm).2
      simpa only [coordinate] using original
    · intro original
      subst label
      exact ⟨gather_scatter row input axes unique inputBound, by
        rw [scatter_overwrite row input (gather row axes) axes unique,
          Scatter.scatter_gather row axes unique]⟩
  simp_rw [condition, eq_comm (b := scatter row axes input)]
  exact Exact.range_delta_sum _ _ _ physicalBound

private theorem kernel_action (dependencies : List Dependency) (bits : Nat) (step : Step)
    (valid : stepValid dependencies bits step = true) (ψ : Nat → ℂ) (row : Nat) :
    (if !enabled step.controls row then ψ row else
      ((List.range (2^(targets step.action).length)).map (fun input =>
        ψ (scatter row (targets step.action) input) * kernel dependencies step.action
          (gather row (targets step.action)) input)).sum) =
      Qleisli.Semantics.RawAction.step dependencies step ψ row := by
  rcases step with ⟨controls, action⟩
  cases action with
  | hadamard axis =>
    have small := Scatter.bit_lt row axis
    have bitCases : bit row axis = 0 ∨ bit row axis = 1 := by omega
    have gathered : gather row [axis] = bit row axis := by simp [gather]
    have low : scatter row [axis] 0 = row - bit row axis * 2^axis := by simp [scatter, bit]
    have high : scatter row [axis] 1 = row - bit row axis * 2^axis + 2^axis := by simp [scatter, bit]
    by_cases disabled : (!enabled controls row) = true
    · simp [Qleisli.Semantics.RawAction.step, disabled]
    · rcases bitCases with coordinate | coordinate <;>
        simp [Qleisli.Semantics.RawAction.step, Qleisli.Semantics.Protected.gate, disabled,
          kernel, targets, gathered, low, high, List.range_succ, coordinate] <;> ring
  | monomial axes permutation phases =>
    have size : permutation.length = 2^axes.length := by
      simp only [stepValid, Bool.and_eq_true, beq_iff_eq] at valid
      tauto
    simp only [Qleisli.Semantics.RawAction.step, targets, kernel, size, beq_iff_eq]
    split
    · rfl
    · apply Exact.sum_map_congr
      intro input _
      split <;> simp_all
  | contract axes index adjoint =>
    cases lookup : dependencies[index]? with
    | none => simp [stepValid, lookup] at valid
    | some dependency =>
      have cols : dependency.meaning.cols = 2^axes.length := by
        simp only [stepValid, lookup, bind, Option.bind, pure, Option.getD_some,
          Bool.and_eq_true, beq_iff_eq] at valid
        tauto
      simp [Qleisli.Semantics.RawAction.step, targets, kernel, lookup, cols]

private theorem zipIdx_map_range {α : Type} (f : Nat → α) (n : Nat) :
    ((List.range n).map f).zipIdx = (List.range n).map (fun i => (f i, i)) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.range_succ, List.zipIdx_append, ih]

end Pull

/-- Every coefficient of a successful original finite step has the independent
literal backward-action meaning. Validity supplies bounded, distinct ordered
targets, disjoint controls, complete permutation/phase tables, and the exact
square dependency lookup. It supplies no dependency isometry. The theorem does
not assert that any other bounded evaluation succeeds or spends the same work. -/
theorem applyStep_pull (dependencies : List Dependency) (bits : Nat) (step : Step)
    (values result : List Scalar) (row : Nat)
    (valid : stepValid dependencies bits step = true) (size : values.length = 2^bits)
    (accepted : applyStep dependencies step values = .ok result) (bound : row < 2^bits) :
    scalar (result[row]?.getD Scalar.zero) = Qleisli.Semantics.RawAction.step dependencies step
      (fun input => scalar (values[input]?.getD Scalar.zero)) row := by
  have original := applyStep_meaning dependencies step values result accepted
  have expanded : values = (List.range values.length).map
      (fun input => values[input]?.getD Scalar.zero) := by
    apply List.ext_getElem
    · simp
    · intro index before _after
      simp [List.getElem?_eq_getElem before]
  have indexed : values.zipIdx = (List.range values.length).map
      (fun input => (values[input]?.getD Scalar.zero, input)) := by
    calc
      values.zipIdx = ((List.range values.length).map
          (fun input => values[input]?.getD Scalar.zero)).zipIdx :=
        congrArg (fun xs : List Scalar => xs.zipIdx) expanded
      _ = _ := Pull.zipIdx_map_range _ _
  have unfolded := original
  unfold Qleisli.Semantics.Finite.applyStep at unfolded
  simp only [indexed, size] at unfolded
  obtain ⟨actual, read, length, coefficient⟩ := Pull.fold_entry dependencies bits step valid
    ((List.range (2^bits)).map (fun input => (values[input]?.getD Scalar.zero, input)))
    (List.replicate (2^bits) 0) row (by simpa using bound)
  have same : actual = result.map scalar := Option.some.inj (read.symm.trans unfolded)
  have resultBound : row < result.length := by
    have lengths := congrArg List.length same
    simp only [List.length_map, length, List.length_replicate] at lengths
    omega
  have interpreted : scalar (result[row]?.getD Scalar.zero) = actual[row]?.getD 0 := by
    rw [same]
    simp [List.getElem?_map, List.getElem?_eq_getElem resultBound]
  rw [interpreted, coefficient]
  simp only [List.getElem?_replicate, bound, if_true, Option.getD_some, zero_add,
    List.map_map, Function.comp_def]
  rw [← Pull.kernel_action dependencies bits step valid _ row]
  by_cases active : enabled step.controls row = true
  · simp only [active, Bool.not_true, Bool.false_eq_true, if_false]
    exact Pull.sum_fiber bits row _ (Pull.geometry dependencies bits step valid).1
      (Pull.geometry dependencies bits step valid).2.1 bound
      (fun label input => scalar (values[label]?.getD Scalar.zero) *
        Pull.kernel dependencies step.action (gather row (targets step.action)) input)
  · have inactive : enabled step.controls row = false := Bool.eq_false_iff.mpr active
    simp only [inactive, Bool.not_false, if_true]
    exact Exact.range_delta_sum _ _ _ bound

#print axioms applyStep_pull

end Qleisli.Finite
