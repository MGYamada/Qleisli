import Qleisli.Exact
import QleisliKernel.ExactMatrix
import Mathlib.Algebra.BigOperators.Ring.List

/-! General matrix denotation of the actual bounded exact implementation.
Successful execution preserves complete complex amplitudes, with arbitrary
untouched reference indices. Copyright 2026 Masahiko G. Yamada.
SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.Exact
open QleisliKernel.Semantics.Exact QleisliKernel.Exact
open Qleisli.Semantics.Exact

theorem scalar_zero_meaning : scalar Scalar.zero = 0 := by
  simp [scalar, Scalar.zero, rational, Coefficient.integer]

theorem scalar_one_meaning : scalar Scalar.one = 1 := by
  simp [scalar, Scalar.one, rational, Coefficient.integer]

theorem work_map_meaning {α : Type} (step : α → WorkM Scalar) (meaning : α → ℂ)
    (sound : ∀ a value work left, (step a).run work = (.ok value, left) →
      scalar value = meaning a)
    (xs : List α) (values : List Scalar) (work left : Nat)
    (ok : (xs.mapM step).run work = (.ok values, left)) :
    values.map scalar = xs.map meaning := by
  induction xs generalizing work values with
  | nil =>
    have h : (Except.ok [], work) = (Except.ok values, left) := ok
    cases h
    rfl
  | cons a xs ih =>
    simp only [List.mapM_cons] at ok
    obtain ⟨value, middle, hv, h⟩ := work_bind_success _ _ _ _ _ ok
    obtain ⟨rest, after, hr, h⟩ := work_bind_success _ _ _ _ _ h
    have hp : (Except.ok (value :: rest), after) = (Except.ok values, left) := h
    cases hp
    simp only [List.map_cons, sound a value work middle hv, ih rest middle hr]

theorem work_fold_sum {α : Type} (step : Scalar → α → WorkM Scalar)
    (contribution : α → ℂ)
    (sound : ∀ acc a value work left, (step acc a).run work = (.ok value, left) →
      scalar value = scalar acc + contribution a)
    (xs : List α) (initial result : Scalar) (work left : Nat)
    (ok : (xs.foldlM step initial).run work = (.ok result, left)) :
    scalar result = scalar initial + (xs.map contribution).sum := by
  induction xs generalizing initial work with
  | nil =>
    have h : (Except.ok initial, work) = (Except.ok result, left) := ok
    cases h
    simp
  | cons a xs ih =>
    simp only [List.foldlM_cons] at ok
    obtain ⟨next, middle, hn, h⟩ := work_bind_success _ _ _ _ _ ok
    rw [ih next middle h, sound initial a next work middle hn]
    simp only [List.map_cons, List.sum_cons]
    ring

theorem matrix_make_result (rows cols : Nat) (values : List Scalar) (z : Matrix)
    (ok : Matrix.make rows cols values = .ok z) :
    z = ⟨rows, cols, values⟩ ∧ 0 < rows ∧ 0 < cols ∧ values.length = rows * cols := by
  unfold Matrix.make at ok
  split at ok
  · cases ok
  · rename_i valid
    split at ok
    · cases ok
    · rename_i size
      simp only [Except.ok.injEq] at ok
      have positive : 0 < rows ∧ 0 < cols := by
        have hvalid : matrixValid rows cols = true := by simpa using valid
        simp only [matrixValid, Bool.and_eq_true, decide_eq_true_eq] at hvalid
        omega
      exact ⟨ok.symm, positive.1, positive.2, by omega⟩

theorem matrix_entry_of_meanings (rows cols : Nat) (values : List Scalar)
    (meaning : Nat → ℂ) (row col : Nat) (hr : row < rows) (hc : col < cols)
    (same : values.map scalar = (List.range (rows * cols)).map meaning) :
    entry ⟨rows, cols, values⟩ row col = meaning (row * cols + col) := by
  have hi : row * cols + col < rows * cols := by
    calc
      row * cols + col < row * cols + cols := Nat.add_lt_add_left hc _
      _ = (row + 1) * cols := by simp [Nat.add_mul]
      _ ≤ rows * cols := Nat.mul_le_mul_right _ (by omega)
  have hs : values.length = rows * cols := by
    have h := congrArg List.length same
    simpa using h
  have hv : row * cols + col < values.length := by omega
  have h := congrArg (fun xs : List ℂ => xs[row * cols + col]?) same
  simp only [List.getElem?_map, List.getElem?_range, hi, Option.map_some] at h
  rw [List.getElem?_eq_getElem hv] at h
  have value : scalar values[row * cols + col] = meaning (row * cols + col) := by
    simpa using h
  simpa [entry, Matrix.entry, List.getElem?_eq_getElem hv] using value

theorem compose_meaning (x y z : Matrix) (work left : Nat)
    (ok : Matrix.compose x y work = (.ok z, left)) :
    x.cols = y.rows ∧ z.rows = x.rows ∧ z.cols = y.cols ∧
      ∀ row col, row < x.rows → col < y.cols →
        entry z row col = ((List.range x.cols).map
          (fun k => entry x row k * entry y k col)).sum := by
  unfold Matrix.compose Matrix.composeWork at ok
  split at ok
  · cases ok
  · rename_i shape
    obtain ⟨_, w₁, _, h⟩ := work_bind_success _ _ _ _ _ ok
    obtain ⟨_, w₂, _, h⟩ := work_bind_success _ _ _ _ _ h
    obtain ⟨values, w₃, hv, h⟩ := work_bind_success _ _ _ _ _ h
    have made := (work_lift_success _ _ _ _ h).1
    obtain ⟨hz, _, cols_positive, _⟩ := matrix_make_result _ _ _ _ made
    subst z
    refine ⟨by omega, rfl, rfl, ?_⟩
    have meaning := work_map_meaning _
      (fun i => ((List.range x.cols).map (fun k =>
        entry x (i / y.cols) k * entry y k (i % y.cols))).sum) ?_
      _ _ _ _ hv
    · intro row col hr hc
      have actual := matrix_entry_of_meanings _ _ values _ row col hr hc meaning
      have div : (row * y.cols + col) / y.cols = row := by
        rw [Nat.add_comm, Nat.add_mul_div_right col row cols_positive,
          Nat.div_eq_of_lt hc, Nat.zero_add]
      simpa only [div, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hc] using actual
    · intro i value before after success
      obtain ⟨sum, _, hs, h⟩ := work_bind_success _ _ _ _ _ success
      have he : sum = value := Except.ok.inj (congrArg Prod.fst h)
      subst value
      have folded := work_fold_sum _
        (fun k => entry x (i / y.cols) k * entry y k (i % y.cols)) ?_ _ _ _ _ _ hs
      · simpa only [scalar_zero_meaning, zero_add] using folded
      · intro acc k result w₀ w₁ step_ok
        obtain ⟨product, middle, hm, ha⟩ := work_bind_success _ _ _ _ _ step_ok
        have hm := (work_lift_success _ _ _ _ hm).1
        have ha := (work_lift_success _ _ _ _ ha).1
        rw [scalar_add_preserves _ _ _ ha, scalar_mul_preserves _ _ _ hm]
        rfl

theorem tensor_meaning (x y z : Matrix) (work left : Nat)
    (ok : Matrix.tensor x y work = (.ok z, left)) :
    z.rows = x.rows * y.rows ∧ z.cols = x.cols * y.cols ∧
      ∀ row col, row < z.rows → col < z.cols →
        entry z row col = entry x (row % x.rows) (col % x.cols) *
          entry y (row / x.rows) (col / x.cols) := by
  unfold Matrix.tensor Matrix.tensorWork at ok
  dsimp only at ok
  split at ok
  · cases ok
  · obtain ⟨_, w₁, _, h⟩ := work_bind_success _ _ _ _ _ ok
    obtain ⟨_, w₂, _, h⟩ := work_bind_success _ _ _ _ _ h
    obtain ⟨values, w₃, hv, h⟩ := work_bind_success _ _ _ _ _ h
    have made := (work_lift_success _ _ _ _ h).1
    obtain ⟨hz, _, cols_positive, _⟩ := matrix_make_result _ _ _ _ made
    subst z
    refine ⟨rfl, rfl, ?_⟩
    have meaning := work_map_meaning _
      (fun i => entry x ((i / (x.cols * y.cols)) % x.rows)
        ((i % (x.cols * y.cols)) % x.cols) *
        entry y ((i / (x.cols * y.cols)) / x.rows)
        ((i % (x.cols * y.cols)) / x.cols))
      (fun _ _ _ _ success => scalar_mul_preserves _ _ _
        (work_lift_success _ _ _ _ success).1) _ _ _ _ hv
    intro row col hr hc
    have actual := matrix_entry_of_meanings _ _ values _ row col hr hc meaning
    have div : (row * (x.cols * y.cols) + col) / (x.cols * y.cols) = row := by
      rw [Nat.add_comm, Nat.add_mul_div_right col row cols_positive,
        Nat.div_eq_of_lt hc, Nat.zero_add]
    simpa only [div, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hc] using actual

theorem adjoint_meaning (x z : Matrix) (work left : Nat)
    (ok : Matrix.adjoint x work = (.ok z, left)) :
    z.rows = x.cols ∧ z.cols = x.rows ∧
      ∀ row col, row < x.cols → col < x.rows →
        entry z row col = star (entry x col row) := by
  unfold Matrix.adjoint Matrix.adjointWork at ok
  obtain ⟨_, w₁, _, h⟩ := work_bind_success _ _ _ _ _ ok
  obtain ⟨values, w₂, hv, h⟩ := work_bind_success _ _ _ _ _ h
  have made := (work_lift_success _ _ _ _ h).1
  obtain ⟨hz, _, rows_positive, _⟩ := matrix_make_result _ _ _ _ made
  subst z
  refine ⟨rfl, rfl, ?_⟩
  have meaning := work_map_meaning _
    (fun i => star (entry x (i % x.rows) (i / x.rows)))
    (fun _ _ _ _ success => scalar_conjugate_preserves _ _
      (work_lift_success _ _ _ _ success).1) _ _ _ _ hv
  intro row col hr hc
  have values_meaning : values.map scalar =
      (List.range (x.cols * x.rows)).map (fun i =>
        star (entry x (i % x.rows) (i / x.rows))) := by
    simpa only [Nat.mul_comm x.rows x.cols] using meaning
  have actual := matrix_entry_of_meanings _ _ values _ row col hr hc values_meaning
  have div : (row * x.rows + col) / x.rows = row := by
    rw [Nat.add_comm, Nat.add_mul_div_right col row rows_positive,
      Nat.div_eq_of_lt hc, Nat.zero_add]
  simpa only [div, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hc] using actual

theorem sum_map_congr {α : Type} (xs : List α) (f g : α → ℂ)
    (same : ∀ a ∈ xs, f a = g a) : (xs.map f).sum = (xs.map g).sum := by
  congr 1
  exact List.map_congr_left same

theorem sum_swap {α β : Type} (xs : List α) (ys : List β) (f : α → β → ℂ) :
    (xs.map (fun a => (ys.map (f a)).sum)).sum =
      (ys.map (fun b => (xs.map (fun a => f a b)).sum)).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih, List.sum_map_add]

theorem compose_action {R : Type} (x y z : Matrix) (work left : Nat)
    (ok : Matrix.compose x y work = (.ok z, left))
    (joint : Nat → R → ℂ) (row : Nat) (reference : R) (hr : row < x.rows) :
    action z joint row reference =
      action x (fun k r => action y joint k r) row reference := by
  obtain ⟨shape, _, cols, meaning⟩ := compose_meaning x y z work left ok
  unfold action
  rw [cols]
  calc
    _ = ((List.range y.cols).map (fun col => ((List.range x.cols).map
        (fun k => entry x row k * entry y k col * joint col reference)).sum)).sum := by
      apply sum_map_congr
      intro col hc
      rw [meaning row col hr (List.mem_range.mp hc), ← List.sum_map_mul_right]
    _ = ((List.range x.cols).map (fun k => ((List.range y.cols).map
        (fun col => entry x row k * entry y k col * joint col reference)).sum)).sum :=
      sum_swap _ _ _
    _ = _ := by
      apply sum_map_congr
      intro k _
      simpa only [mul_assoc] using List.sum_map_mul_left (List.range y.cols)
        (fun col => entry y k col * joint col reference) (entry x row k)

theorem tensor_action {R : Type} (x y z : Matrix) (work left : Nat)
    (ok : Matrix.tensor x y work = (.ok z, left))
    (joint : Nat → R → ℂ) (row : Nat) (reference : R) (hr : row < z.rows) :
    action z joint row reference = ((List.range (x.cols * y.cols)).map
      (fun col => entry x (row % x.rows) (col % x.cols) *
        entry y (row / x.rows) (col / x.cols) * joint col reference)).sum := by
  obtain ⟨_, cols, meaning⟩ := tensor_meaning x y z work left ok
  unfold action
  rw [cols]
  apply sum_map_congr
  intro col hc
  rw [meaning row col hr (by rw [cols]; exact List.mem_range.mp hc)]

/-- The first operand occupies the low coordinate, including Unit dimensions.
No permutation, transpose or phase quotient is implicit in tensor formation. -/
theorem tensor_low_coordinate (x y z : Matrix) (work left : Nat)
    (ok : Matrix.tensor x y work = (.ok z, left)) (rx ry cx cy : Nat)
    (hrx : rx < x.rows) (hry : ry < y.rows) (hcx : cx < x.cols) (hcy : cy < y.cols) :
    entry z (rx + x.rows * ry) (cx + x.cols * cy) =
      entry x rx cx * entry y ry cy := by
  obtain ⟨rows, cols, meaning⟩ := tensor_meaning x y z work left ok
  have coordinate_bound (low high lowDim highDim : Nat)
      (hl : low < lowDim) (hh : high < highDim) : low + lowDim * high < lowDim * highDim := by
    calc
      low + lowDim * high < lowDim + lowDim * high := Nat.add_lt_add_right hl _
      _ = lowDim * (high + 1) := by ring
      _ ≤ lowDim * highDim := Nat.mul_le_mul_left _ (by omega)
  have hr : rx + x.rows * ry < z.rows := by
    rw [rows]
    exact coordinate_bound rx ry x.rows y.rows hrx hry
  have hc : cx + x.cols * cy < z.cols := by
    rw [cols]
    exact coordinate_bound cx cy x.cols y.cols hcx hcy
  rw [meaning _ _ hr hc]
  have pr : 0 < x.rows := by omega
  have pc : 0 < x.cols := by omega
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrx, Nat.mod_eq_of_lt hcx,
    Nat.add_mul_div_left rx ry pr, Nat.add_mul_div_left cx cy pc,
    Nat.div_eq_of_lt hrx, Nat.div_eq_of_lt hcx, Nat.zero_add]

theorem identity_meaning (dim : Nat) (z : Matrix) (ok : Matrix.identity dim = .ok z) :
    0 < dim ∧ z.rows = dim ∧ z.cols = dim ∧
      ∀ row col, row < dim → col < dim → entry z row col = if row = col then 1 else 0 := by
  unfold Matrix.identity at ok
  split at ok
  · cases ok
  · obtain ⟨hz, positive, _, _⟩ := matrix_make_result _ _ _ _ ok
    subst z
    refine ⟨positive, rfl, rfl, ?_⟩
    have meaning :
        ((List.range (dim * dim)).map (fun i =>
          if i / dim = i % dim then Scalar.one else Scalar.zero)).map scalar =
        (List.range (dim * dim)).map (fun i => if i / dim = i % dim then 1 else 0) := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro i _
      by_cases h : i / dim = i % dim
      · simp [h, scalar_one_meaning]
      · simp [h, scalar_zero_meaning]
    intro row col hr hc
    have actual := matrix_entry_of_meanings _ _ _ _ row col hr hc meaning
    have div : (row * dim + col) / dim = row := by
      rw [Nat.add_comm, Nat.add_mul_div_right col row positive,
        Nat.div_eq_of_lt hc, Nat.zero_add]
    simpa only [div, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hc] using actual

theorem isometry_gram (x : Matrix) (work left : Nat)
    (ok : Matrix.isometry x work = (.ok true, left)) :
    0 < x.cols ∧ ∀ row col, row < x.cols → col < x.cols →
      ((List.range x.rows).map (fun k => star (entry x k row) * entry x k col)).sum =
        if row = col then 1 else 0 := by
  unfold Matrix.isometry Matrix.isometryWork at ok
  split at ok
  · have impossible : false = true := Except.ok.inj (congrArg Prod.fst ok)
    cases impossible
  · obtain ⟨_, w₁, _, h⟩ := work_bind_success _ _ _ _ _ ok
    obtain ⟨adjoint, w₂, ha, h⟩ := work_bind_success _ _ _ _ _ h
    obtain ⟨product, w₃, hp, h⟩ := work_bind_success _ _ _ _ _ h
    obtain ⟨identity, w₄, hi, h⟩ := work_bind_success _ _ _ _ _ h
    have same : (product == identity) = true := Except.ok.inj (congrArg Prod.fst h)
    have same : product = identity := beq_iff_eq.mp same
    subst product
    obtain ⟨positive, _, _, identity_entries⟩ := identity_meaning x.cols identity
      (work_lift_success _ _ _ _ hi).1
    obtain ⟨adj_rows, adj_cols, adj_entries⟩ := adjoint_meaning x adjoint w₁ w₂ ha
    obtain ⟨_, _, _, product_entries⟩ := compose_meaning adjoint x identity w₂ w₃ hp
    refine ⟨positive, ?_⟩
    intro row col hr hc
    rw [← identity_entries row col hr hc, product_entries row col (by rw [adj_rows]; exact hr) hc]
    rw [adj_cols]
    apply sum_map_congr
    intro k hk
    rw [adj_entries row k hr (List.mem_range.mp hk)]

theorem star_list_sum (xs : List ℂ) : star xs.sum = (xs.map star).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [ih]

theorem range_delta_sum (dim index : Nat) (f : Nat → ℂ) (hi : index < dim) :
    ((List.range dim).map (fun j => if index = j then f j else 0)).sum = f index := by
  induction dim with
  | zero => omega
  | succ dim ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    by_cases same : index = dim
    · subst index
      have zeros : ((List.range dim).map (fun j => if dim = j then f j else 0)).sum = 0 := by
        have values : (List.range dim).map (fun j => if dim = j then f j else 0) =
            (List.range dim).map (fun _ => (0 : ℂ)) := by
          apply List.map_congr_left
          intro j hj
          have hn : dim ≠ j := by have h := List.mem_range.mp hj; omega
          simp [hn]
        simp [values]
      simp [zeros]
    · rw [ih (by omega)]
      simp [same]

theorem isometry_inner_product {R S : Type} (x : Matrix) (work left : Nat)
    (ok : Matrix.isometry x work = (.ok true, left))
    (joint : Nat → R → ℂ) (other : Nat → S → ℂ) (reference : R) (otherReference : S) :
    ((List.range x.rows).map (fun row => star (action x joint row reference) *
      action x other row otherReference)).sum =
    ((List.range x.cols).map (fun col => star (joint col reference) *
      other col otherReference)).sum := by
  obtain ⟨_, gram⟩ := isometry_gram x work left ok
  let term := fun i j k => star (joint j reference) *
    (star (entry x i j) * entry x i k) * other k otherReference
  have expanded (i : Nat) : star (action x joint i reference) *
      action x other i otherReference = ((List.range x.cols).map (fun j =>
        ((List.range x.cols).map (fun k => term i j k)).sum)).sum := by
    unfold action
    rw [star_list_sum, List.map_map, ← List.sum_map_mul_right]
    apply sum_map_congr
    intro j _
    rw [← List.sum_map_mul_left]
    apply sum_map_congr
    intro k _
    simp only [Function.comp_apply, term, star_mul]
    ring
  calc
    _ = ((List.range x.rows).map (fun i => ((List.range x.cols).map (fun j =>
        ((List.range x.cols).map (fun k => term i j k)).sum)).sum)).sum := by
      apply sum_map_congr
      intro i _
      exact expanded i
    _ = ((List.range x.cols).map (fun j => ((List.range x.rows).map (fun i =>
        ((List.range x.cols).map (fun k => term i j k)).sum)).sum)).sum := sum_swap _ _ _
    _ = ((List.range x.cols).map (fun j => ((List.range x.cols).map (fun k =>
        ((List.range x.rows).map (fun i => term i j k)).sum)).sum)).sum := by
      apply sum_map_congr
      intro j _
      exact sum_swap _ _ _
    _ = ((List.range x.cols).map (fun j => ((List.range x.cols).map (fun k =>
        if j = k then star (joint j reference) * other k otherReference else 0)).sum)).sum := by
      apply sum_map_congr
      intro j hj
      apply sum_map_congr
      intro k hk
      change ((List.range x.rows).map (fun i => star (joint j reference) *
        (star (entry x i j) * entry x i k) * other k otherReference)).sum = _
      rw [List.sum_map_mul_right, List.sum_map_mul_left,
        gram j k (List.mem_range.mp hj) (List.mem_range.mp hk)]
      split <;> simp
    _ = _ := by
      apply sum_map_congr
      intro j hj
      exact range_delta_sum x.cols j
        (fun k => star (joint j reference) * other k otherReference) (List.mem_range.mp hj)

theorem isometry_norm {R : Type} (x : Matrix) (work left : Nat)
    (ok : Matrix.isometry x work = (.ok true, left))
    (joint : Nat → R → ℂ) (reference : R) :
    ((List.range x.rows).map (fun row => Complex.normSq (action x joint row reference))).sum =
      ((List.range x.cols).map (fun col => Complex.normSq (joint col reference))).sum := by
  have h := isometry_inner_product x work left ok joint joint reference reference
  have re_sum (xs : List ℂ) : xs.sum.re = (xs.map Complex.re).sum := by
    induction xs with
    | nil => simp
    | cons a xs ih => simp [ih]
  have norm_product (value : ℂ) : (star value * value).re = Complex.normSq value := by
    change ((starRingEnd ℂ) value * value).re = Complex.normSq value
    rw [← Complex.normSq_eq_conj_mul_self]
    rfl
  have real_parts := congrArg Complex.re h
  rw [re_sum, re_sum] at real_parts
  simpa only [List.map_map, Function.comp_def, norm_product] using real_parts

/-- Summing over any finite reference domain preserves the joint norm, so the
claim includes entangled inputs rather than requiring separable states. -/
theorem isometry_joint_norm {R : Type} (x : Matrix) (work left : Nat)
    (ok : Matrix.isometry x work = (.ok true, left))
    (joint : Nat → R → ℂ) (references : List R) :
    (references.map (fun r => ((List.range x.rows).map
      (fun row => Complex.normSq (action x joint row r))).sum)).sum =
    (references.map (fun r => ((List.range x.cols).map
      (fun col => Complex.normSq (joint col r))).sum)).sum := by
  congr 1
  apply List.map_congr_left
  intro r _
  exact isometry_norm x work left ok joint r

/-- A zero-qubit (one-dimensional) operation retains its complete scalar,
including global phase and its action on an arbitrary reference. -/
theorem unit_phase_action {R : Type} (k : Int) (joint : Nat → R → ℂ) (reference : R) :
    action ⟨1, 1, [Scalar.phase k]⟩ joint 0 reference =
      scalar (Scalar.phase k) * joint 0 reference := by
  simp [action, entry, Matrix.entry, List.range_succ]

theorem unit_phase_four_action {R : Type} (joint : Nat → R → ℂ) (reference : R) :
    action ⟨1, 1, [Scalar.phase 4]⟩ joint 0 reference = -joint 0 reference := by
  rw [unit_phase_action, unit_scalar_phase_retained]
  ring

end Qleisli.Exact
