import QleisliKernel.Exact

/-! Admission and exact work accounting for the actual bounded matrix operations.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/

namespace QleisliKernel.Exact
open Semantics.Exact

def ListRel {α β : Type} (p : α → β → Prop) (xs : List α) (ys : List β) : Prop :=
  List.rec (motive := fun _ => List β → Prop)
    (fun ys => match ys with | [] => True | _ :: _ => False)
    (fun a _ next ys => match ys with
      | [] => False
      | b :: rest => p a b ∧ next rest) xs ys

theorem work_bind_run {α β : Type} (first : WorkM α) (next : α → WorkM β) (work : Nat) :
    (first >>= next).run work =
      match first.run work with
      | (.error error, left) => (.error error, left)
      | (.ok value, left) => (next value).run left := by
  simp only [ExceptT.run, bind, ExceptT.bind, ExceptT.mk, StateT.bind]
  cases first work with
  | mk result middle => cases result <;> rfl

theorem work_bind_success {α β : Type} (first : WorkM α) (next : α → WorkM β)
    (work left : Nat) (z : β) (ok : (first >>= next).run work = (.ok z, left)) :
    ∃ value middle, first.run work = (.ok value, middle) ∧
      (next value).run middle = (.ok z, left) := by
  rw [work_bind_run] at ok
  cases h : first.run work with
  | mk result middle =>
    rw [h] at ok
    cases result with
    | error error => cases ok
    | ok value => exact ⟨value, middle, rfl, ok⟩

theorem work_bind_error {α β : Type} (first : WorkM α) (next : α → WorkM β)
    (work left : Nat) (error : Error)
    (failed : (first >>= next).run work = (.error error, left)) :
    first.run work = (.error error, left) ∨
      ∃ value middle, first.run work = (.ok value, middle) ∧
        (next value).run middle = (.error error, left) := by
  rw [work_bind_run] at failed
  cases h : first.run work with
  | mk result middle =>
    rw [h] at failed
    cases result with
    | error original =>
      cases failed
      exact Or.inl rfl
    | ok value => exact Or.inr ⟨value, middle, rfl, failed⟩

theorem work_lift_success {α : Type} (result : Except Error α) (work left : Nat)
    (z : α) (ok : (liftExact result).run work = (.ok z, left)) :
    result = .ok z ∧ left = work := by
  cases result with
  | error error => cases ok
  | ok value =>
    have h : (Except.ok value, work) = (Except.ok z, left) := ok
    cases h
    exact ⟨rfl, rfl⟩

theorem work_lift_error {α : Type} (result : Except Error α) (work left : Nat)
    (error : Error) (failed : (liftExact result).run work = (.error error, left)) :
    result = .error error ∧ left = work := by
  cases result with
  | ok value => cases failed
  | error original =>
    have h : (Except.error original, work) = (Except.error error, left) := failed
    cases h
    exact ⟨rfl, rfl⟩

theorem work_pure_success {α : Type} (value z : α) (work left : Nat)
    (ok : (pure value : WorkM α).run work = (.ok z, left)) :
    z = value ∧ left = work := by
  have h : (Except.ok value, work) = (Except.ok z, left) := ok
  cases h
  exact ⟨rfl, rfl⟩

theorem work_map_relation {α β : Type} (step : α → WorkM β) (p : α → β → Prop)
    (preserve : ∀ a b work left, (step a).run work = (.ok b, left) → p a b)
    (xs : List α) (ys : List β) (work left : Nat)
    (ok : (xs.mapM step).run work = (.ok ys, left)) : ListRel p xs ys := by
  induction xs generalizing ys work left with
  | nil =>
    simp only [List.mapM_nil] at ok
    obtain ⟨hy, _⟩ := work_pure_success [] ys work left ok
    subst ys
    trivial
  | cons a xs ih =>
    simp only [List.mapM_cons] at ok
    obtain ⟨b, middle, hb, h⟩ := work_bind_success _ _ _ _ _ ok
    obtain ⟨rest, tailWork, ht, h⟩ := work_bind_success _ _ _ _ _ h
    obtain ⟨hy, _⟩ := work_pure_success (b :: rest) ys tailWork left h
    subst ys
    exact ⟨preserve a b work middle hb, ih rest middle tailWork ht⟩

theorem listRel_length {α β : Type} (p : α → β → Prop) (xs : List α) (ys : List β)
    (h : ListRel p xs ys) : ys.length = xs.length := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [ListRel]
  | cons a xs ih =>
    cases ys with
    | nil => exact False.elim h
    | cons b ys => exact congrArg Nat.succ (ih ys h.2)

theorem listRel_getElem {α β : Type} (p : α → β → Prop) (xs : List α) (ys : List β)
    (h : ListRel p xs ys) (i : Nat) (hi : i < xs.length) :
    p (xs[i]'hi) (ys[i]'(by rw [listRel_length p xs ys h]; exact hi)) := by
  induction xs generalizing ys i with
  | nil => cases hi
  | cons a xs ih =>
    cases ys with
    | nil => exact False.elim h
    | cons b ys =>
      cases i with
      | zero => exact h.1
      | succ i => exact ih ys h.2 i (by simpa using hi)

theorem work_fold_invariant {α β : Type} (step : β → α → WorkM β) (p : β → Prop)
    (preserve : ∀ b a z work left, p b → (step b a).run work = (.ok z, left) → p z)
    (xs : List α) (initial z : β) (work left : Nat) (vi : p initial)
    (ok : (xs.foldlM step initial).run work = (.ok z, left)) : p z := by
  induction xs generalizing initial work with
  | nil =>
    simp only [List.foldlM_nil] at ok
    obtain ⟨hz, _⟩ := work_pure_success initial z work left ok
    simpa [hz] using vi
  | cons a xs ih =>
    simp only [List.foldlM_cons] at ok
    obtain ⟨next, middle, hn, h⟩ := work_bind_success _ _ _ _ _ ok
    exact ih next middle (preserve initial a next work middle vi hn) h

theorem work_fold_reference {α β γ : Type} (step : β → α → WorkM β)
    (reference : β → γ) (referenceStep : γ → α → γ)
    (preserve : ∀ b a z work left, (step b a).run work = (.ok z, left) →
      reference z = referenceStep (reference b) a)
    (xs : List α) (initial z : β) (work left : Nat)
    (ok : (xs.foldlM step initial).run work = (.ok z, left)) :
    reference z = xs.foldl referenceStep (reference initial) := by
  induction xs generalizing initial work with
  | nil =>
    simp only [List.foldlM_nil] at ok
    obtain ⟨hz, _⟩ := work_pure_success initial z work left ok
    simp [hz]
  | cons a xs ih =>
    simp only [List.foldlM_cons] at ok
    obtain ⟨next, middle, hn, h⟩ := work_bind_success _ _ _ _ _ ok
    rw [List.foldl_cons, ← preserve initial a next work middle hn]
    exact ih next middle h

/-- The arithmetic-only portion retains the state on every outcome. -/
def KeepsWork {α : Type} (f : WorkM α) : Prop := ∀ work, (f.run work).2 = work

theorem keeps_pure {α : Type} (value : α) : KeepsWork (pure value) := by intro work; rfl
theorem keeps_lift {α : Type} (result : Except Error α) : KeepsWork (liftExact result) := by
  cases result <;> intro work <;> rfl
theorem keeps_throw {α : Type} (error : Error) : KeepsWork (throw error : WorkM α) := by
  intro work; rfl

theorem keeps_bind {α β : Type} (first : WorkM α) (next : α → WorkM β)
    (hf : KeepsWork first) (hn : ∀ value, KeepsWork (next value)) :
    KeepsWork (first >>= next) := by
  intro work
  rw [work_bind_run]
  cases h : first.run work with
  | mk result middle =>
    have hm : middle = work := by simpa [h] using hf work
    cases result with
    | error error => exact hm
    | ok value => exact (hn value middle).trans hm

theorem keeps_fold {α β : Type} (step : β → α → WorkM β)
    (hs : ∀ b a, KeepsWork (step b a)) (xs : List α) (initial : β) :
    KeepsWork (xs.foldlM step initial) := by
  induction xs generalizing initial with
  | nil => exact keeps_pure initial
  | cons a xs ih =>
    simp only [List.foldlM_cons]
    exact keeps_bind _ _ (hs initial a) (fun next => ih next)

theorem keeps_map {α β : Type} (step : α → WorkM β)
    (hs : ∀ a, KeepsWork (step a)) (xs : List α) : KeepsWork (xs.mapM step) := by
  induction xs with
  | nil => exact keeps_pure []
  | cons a xs ih =>
    simp only [List.mapM_cons]
    exact keeps_bind _ _ (hs a) (fun value => keeps_bind _ _ ih (fun rest => keeps_pure (value :: rest)))

theorem charged_exact_remaining {α : Type} (amount work : Nat) (next : Unit → WorkM α)
    (enough : amount ≤ work) (hn : ∀ value, KeepsWork (next value)) :
    ((charge amount >>= next).run work).2 = work - amount := by
  rw [charged_run amount work next enough]
  exact hn () (work - amount)

/-- Dimensions, exact row-major storage and canonical coefficients are separate
admission premises; constructing the raw data structure proves none of them. -/
def Matrix.Admitted (x : Matrix) : Prop :=
  matrixValid x.rows x.cols = true ∧ x.entries.length = x.rows * x.cols ∧
    ∀ value ∈ x.entries, Scalar.valid value = true

theorem matrix_make_value (rows cols : Nat) (entries : List Scalar) (z : Matrix)
    (ok : Matrix.make rows cols entries = .ok z) :
    z = ⟨rows, cols, entries⟩ ∧ matrixValid rows cols = true ∧ entries.length = rows * cols := by
  unfold Matrix.make at ok
  split at ok
  · cases ok
  · split at ok
    · cases ok
    · simp_all

theorem matrix_make_admitted (rows cols : Nat) (entries : List Scalar) (z : Matrix)
    (valid : ∀ value ∈ entries, Scalar.valid value = true)
    (ok : Matrix.make rows cols entries = .ok z) : Matrix.Admitted z := by
  obtain ⟨hz, dimensions, length⟩ := matrix_make_value rows cols entries z ok
  subst z
  exact ⟨dimensions, length, valid⟩

theorem matrix_entry_valid (x : Matrix) (hx : Matrix.Admitted x) (row col : Nat) :
    Scalar.valid (x.entry row col) = true := by
  unfold Matrix.entry
  cases h : x.entries[row * x.cols + col]? with
  | none => decide
  | some value => exact hx.2.2 value (List.mem_of_getElem? h)

theorem matrix_identity_admitted (dim : Nat) (z : Matrix)
    (ok : Matrix.identity dim = .ok z) : Matrix.Admitted z := by
  unfold Matrix.identity at ok
  split at ok
  · cases ok
  · apply matrix_make_admitted dim dim _ z _ ok
    intro value member
    obtain ⟨i, _, hi⟩ := List.mem_map.mp member
    subst value
    split <;> decide

theorem listRel_all_right {α β : Type} (p : α → β → Prop) (q : β → Prop)
    (xs : List α) (ys : List β) (h : ListRel p xs ys)
    (implies : ∀ a b, p a b → q b) : ∀ value ∈ ys, q value := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [ListRel]
  | cons a xs ih =>
    cases ys with
    | nil => simp
    | cons b ys =>
      intro value member
      rcases List.mem_cons.mp member with hb | ht
      · subst value; exact implies a b h.1
      · exact ih ys h.2 value ht

theorem compose_admitted (x y z : Matrix) (work left : Nat)
    (ok : (Matrix.composeWork x y).run work = (.ok z, left)) : Matrix.Admitted z := by
  unfold Matrix.composeWork at ok
  split at ok
  · change (Except.error Error.shapeMismatch, work) = (.ok z, left) at ok
    cases ok
  obtain ⟨_, firstWork, _, ok⟩ := work_bind_success _ _ _ _ _ ok
  obtain ⟨_, chargedWork, _, ok⟩ := work_bind_success _ _ _ _ _ ok
  obtain ⟨entries, finalWork, mapped, ok⟩ := work_bind_success _ _ _ _ _ ok
  obtain ⟨made, _⟩ := work_lift_success _ _ _ _ ok
  apply matrix_make_admitted x.rows y.cols entries z _ made
  have relation := work_map_relation _ (fun _ value => Scalar.valid value = true)
    (fun i value before after h => by
      obtain ⟨sum, middle, folded, hp⟩ := work_bind_success _ _ _ _ _ h
      obtain ⟨hv, _⟩ := work_pure_success sum value middle after hp
      subst value
      apply work_fold_invariant _ (fun s => Scalar.valid s = true) _ _ _ _ _ _ (by decide) folded
      intro accumulator k result before after va h
      obtain ⟨product, middle, multiplied, added⟩ := work_bind_success _ _ _ _ _ h
      obtain ⟨hm, _⟩ := work_lift_success _ _ _ _ multiplied
      obtain ⟨ha, _⟩ := work_lift_success _ _ _ _ added
      exact scalar_add_valid _ _ _ va (scalar_mul_valid _ _ _ hm) ha)
    _ entries chargedWork finalWork mapped
  exact listRel_all_right _ _ _ _ relation (fun _ _ h => h)

theorem tensor_admitted (x y z : Matrix) (work left : Nat)
    (ok : (Matrix.tensorWork x y).run work = (.ok z, left)) : Matrix.Admitted z := by
  unfold Matrix.tensorWork at ok
  dsimp only at ok
  split at ok
  · change (Except.error Error.dimension, work) = (.ok z, left) at ok
    cases ok
  obtain ⟨_, firstWork, _, ok⟩ := work_bind_success _ _ _ _ _ ok
  obtain ⟨_, chargedWork, _, ok⟩ := work_bind_success _ _ _ _ _ ok
  obtain ⟨entries, finalWork, mapped, ok⟩ := work_bind_success _ _ _ _ _ ok
  obtain ⟨made, _⟩ := work_lift_success _ _ _ _ ok
  apply matrix_make_admitted (x.rows * y.rows) (x.cols * y.cols) entries z _ made
  have relation := work_map_relation _ (fun _ value => Scalar.valid value = true)
    (fun _ value before after h =>
      scalar_mul_valid _ _ _ (work_lift_success _ before after value h).1)
    _ entries chargedWork finalWork mapped
  exact listRel_all_right _ _ _ _ relation (fun _ _ h => h)

theorem adjoint_admitted (x z : Matrix) (hx : Matrix.Admitted x) (work left : Nat)
    (ok : (Matrix.adjointWork x).run work = (.ok z, left)) : Matrix.Admitted z := by
  unfold Matrix.adjointWork at ok
  obtain ⟨_, chargedWork, _, ok⟩ := work_bind_success _ _ _ _ _ ok
  obtain ⟨entries, finalWork, mapped, ok⟩ := work_bind_success _ _ _ _ _ ok
  obtain ⟨made, _⟩ := work_lift_success _ _ _ _ ok
  apply matrix_make_admitted x.cols x.rows entries z _ made
  have relation := work_map_relation _ (fun _ value => Scalar.valid value = true)
    (fun _ value before after h =>
      scalar_conjugate_valid _ _ (matrix_entry_valid x hx _ _)
        (work_lift_success _ before after value h).1)
    _ entries chargedWork finalWork mapped
  exact listRel_all_right _ _ _ _ relation (fun _ _ h => h)

theorem compose_shape_error (x y : Matrix) (work : Nat) (shape : x.cols ≠ y.rows) :
    (Matrix.composeWork x y).run work = (.error .shapeMismatch, work) := by
  unfold Matrix.composeWork
  rw [if_pos shape]
  rfl

theorem tensor_dimension_error (x y : Matrix) (work : Nat)
    (dimensions : matrixValid (x.rows * y.rows) (x.cols * y.cols) = false) :
    (Matrix.tensorWork x y).run work = (.error .dimension, work) := by
  unfold Matrix.tensorWork
  simp only [dimensions, Bool.not_false, ↓reduceIte]
  rfl

theorem compose_remaining (x y : Matrix) (work : Nat) (shape : x.cols = y.rows)
    (enough : 2 * x.rows * x.cols * y.cols ≤ work) :
    ((Matrix.composeWork x y).run work).2 = work - 2 * x.rows * x.cols * y.cols := by
  unfold Matrix.composeWork
  rw [if_neg (fun h => h shape)]
  change ((charge (2 * x.rows * x.cols * y.cols) >>= _).run work).2 = _
  apply charged_exact_remaining _ _ _ enough
  intro _
  apply keeps_bind _ _
    (keeps_map _ (fun i => keeps_bind _ _
      (keeps_fold _ (fun sum k => keeps_bind _ _ (keeps_lift _) (fun product => keeps_lift _)) _ _)
      (fun sum => keeps_pure sum)) _)
  intro entries
  exact keeps_lift _

theorem tensor_remaining (x y : Matrix) (work : Nat)
    (dimensions : matrixValid (x.rows * y.rows) (x.cols * y.cols) = true)
    (enough : x.rows * y.rows * (x.cols * y.cols) ≤ work) :
    ((Matrix.tensorWork x y).run work).2 = work - x.rows * y.rows * (x.cols * y.cols) := by
  unfold Matrix.tensorWork
  simp only [dimensions, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  change ((charge (x.rows * y.rows * (x.cols * y.cols)) >>= _).run work).2 = _
  apply charged_exact_remaining _ _ _ enough
  intro _
  exact keeps_bind _ _ (keeps_map _ (fun i => keeps_lift _) _) (fun entries => keeps_lift _)

theorem adjoint_remaining (x : Matrix) (work : Nat) (enough : x.rows * x.cols ≤ work) :
    ((Matrix.adjointWork x).run work).2 = work - x.rows * x.cols := by
  unfold Matrix.adjointWork
  apply charged_exact_remaining _ _ _ enough
  intro _
  exact keeps_bind _ _ (keeps_map _ (fun i => keeps_lift _) _) (fun entries => keeps_lift _)

theorem compose_work_limit (x y : Matrix) (work : Nat) (shape : x.cols = y.rows)
    (short : work < 2 * x.rows * x.cols * y.cols) :
    (Matrix.composeWork x y).run work = (.error .workLimit, work) := by
  unfold Matrix.composeWork
  rw [if_neg (fun h => h shape)]
  change ((charge (2 * x.rows * x.cols * y.cols) >>= _).run work) = _
  exact charged_failure _ _ _ short

theorem tensor_work_limit (x y : Matrix) (work : Nat)
    (dimensions : matrixValid (x.rows * y.rows) (x.cols * y.cols) = true)
    (short : work < x.rows * y.rows * (x.cols * y.cols)) :
    (Matrix.tensorWork x y).run work = (.error .workLimit, work) := by
  unfold Matrix.tensorWork
  simp only [dimensions, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  change ((charge (x.rows * y.rows * (x.cols * y.cols)) >>= _).run work) = _
  exact charged_failure _ _ _ short

theorem adjoint_work_limit (x : Matrix) (work : Nat) (short : work < x.rows * x.cols) :
    (Matrix.adjointWork x).run work = (.error .workLimit, work) := by
  unfold Matrix.adjointWork
  exact charged_failure _ _ _ short

theorem compose_success_cost (x y z : Matrix) (work left : Nat)
    (ok : (Matrix.composeWork x y).run work = (.ok z, left)) :
    x.cols = y.rows ∧ 2 * x.rows * x.cols * y.cols ≤ work ∧
      left = work - 2 * x.rows * x.cols * y.cols := by
  have shape : x.cols = y.rows := by
    by_cases h : x.cols = y.rows
    · exact h
    rw [compose_shape_error x y work h] at ok
    cases ok
  have enough : 2 * x.rows * x.cols * y.cols ≤ work := by
    by_cases h : 2 * x.rows * x.cols * y.cols ≤ work
    · exact h
    rw [compose_work_limit x y work shape (by omega)] at ok
    cases ok
  exact ⟨shape, enough, by simpa [ok] using compose_remaining x y work shape enough⟩

theorem tensor_success_cost (x y z : Matrix) (work left : Nat)
    (ok : (Matrix.tensorWork x y).run work = (.ok z, left)) :
    matrixValid (x.rows * y.rows) (x.cols * y.cols) = true ∧
      x.rows * y.rows * (x.cols * y.cols) ≤ work ∧
      left = work - x.rows * y.rows * (x.cols * y.cols) := by
  have dimensions : matrixValid (x.rows * y.rows) (x.cols * y.cols) = true := by
    cases h : matrixValid (x.rows * y.rows) (x.cols * y.cols) with
    | true => rfl
    | false => rw [tensor_dimension_error x y work h] at ok; cases ok
  have enough : x.rows * y.rows * (x.cols * y.cols) ≤ work := by
    by_cases h : x.rows * y.rows * (x.cols * y.cols) ≤ work
    · exact h
    rw [tensor_work_limit x y work dimensions (by omega)] at ok
    cases ok
  exact ⟨dimensions, enough, by simpa [ok] using tensor_remaining x y work dimensions enough⟩

theorem adjoint_success_cost (x z : Matrix) (work left : Nat)
    (ok : (Matrix.adjointWork x).run work = (.ok z, left)) :
    x.rows * x.cols ≤ work ∧ left = work - x.rows * x.cols := by
  have enough : x.rows * x.cols ≤ work := by
    by_cases h : x.rows * x.cols ≤ work
    · exact h
    rw [adjoint_work_limit x work (by omega)] at ok
    cases ok
  exact ⟨enough, by simpa [ok] using adjoint_remaining x work enough⟩

theorem compose_arithmetic_failure_cost (x y : Matrix) (work left : Nat)
    (error : (Matrix.composeWork x y).run work = (.error .arithmeticCapacity, left)) :
    x.cols = y.rows ∧ 2 * x.rows * x.cols * y.cols ≤ work ∧
      left = work - 2 * x.rows * x.cols * y.cols := by
  have shape : x.cols = y.rows := by
    by_cases h : x.cols = y.rows
    · exact h
    rw [compose_shape_error x y work h] at error
    cases error
  have enough : 2 * x.rows * x.cols * y.cols ≤ work := by
    by_cases h : 2 * x.rows * x.cols * y.cols ≤ work
    · exact h
    rw [compose_work_limit x y work shape (by omega)] at error
    cases error
  exact ⟨shape, enough, by simpa [error] using compose_remaining x y work shape enough⟩

theorem tensor_arithmetic_failure_cost (x y : Matrix) (work left : Nat)
    (error : (Matrix.tensorWork x y).run work = (.error .arithmeticCapacity, left)) :
    matrixValid (x.rows * y.rows) (x.cols * y.cols) = true ∧
      x.rows * y.rows * (x.cols * y.cols) ≤ work ∧
      left = work - x.rows * y.rows * (x.cols * y.cols) := by
  have dimensions : matrixValid (x.rows * y.rows) (x.cols * y.cols) = true := by
    cases h : matrixValid (x.rows * y.rows) (x.cols * y.cols) with
    | true => rfl
    | false => rw [tensor_dimension_error x y work h] at error; cases error
  have enough : x.rows * y.rows * (x.cols * y.cols) ≤ work := by
    by_cases h : x.rows * y.rows * (x.cols * y.cols) ≤ work
    · exact h
    rw [tensor_work_limit x y work dimensions (by omega)] at error
    cases error
  exact ⟨dimensions, enough, by simpa [error] using tensor_remaining x y work dimensions enough⟩

theorem adjoint_arithmetic_failure_cost (x : Matrix) (work left : Nat)
    (error : (Matrix.adjointWork x).run work = (.error .arithmeticCapacity, left)) :
    x.rows * x.cols ≤ work ∧ left = work - x.rows * x.cols := by
  have enough : x.rows * x.cols ≤ work := by
    by_cases h : x.rows * x.cols ≤ work
    · exact h
    rw [adjoint_work_limit x work (by omega)] at error
    cases error
  exact ⟨enough, by simpa [error] using adjoint_remaining x work enough⟩

theorem adjoint_shape (x z : Matrix) (work left : Nat)
    (ok : (Matrix.adjointWork x).run work = (.ok z, left)) :
    z.rows = x.cols ∧ z.cols = x.rows := by
  unfold Matrix.adjointWork at ok
  obtain ⟨_, _, _, ok⟩ := work_bind_success _ _ _ _ _ ok
  obtain ⟨entries, _, _, ok⟩ := work_bind_success _ _ _ _ _ ok
  obtain ⟨made, _⟩ := work_lift_success _ _ _ _ ok
  obtain ⟨hz, _, _⟩ := matrix_make_value x.cols x.rows entries z made
  subst z
  exact ⟨rfl, rfl⟩

theorem compose_shape (x y z : Matrix) (work left : Nat)
    (ok : (Matrix.composeWork x y).run work = (.ok z, left)) :
    z.rows = x.rows ∧ z.cols = y.cols := by
  have shape := (compose_success_cost x y z work left ok).1
  unfold Matrix.composeWork at ok
  rw [if_neg (fun h => h shape)] at ok
  obtain ⟨_, _, _, ok⟩ := work_bind_success _ _ _ _ _ ok
  obtain ⟨_, _, _, ok⟩ := work_bind_success _ _ _ _ _ ok
  obtain ⟨entries, _, _, ok⟩ := work_bind_success _ _ _ _ _ ok
  obtain ⟨made, _⟩ := work_lift_success _ _ _ _ ok
  obtain ⟨hz, _, _⟩ := matrix_make_value x.rows y.cols entries z made
  subst z
  exact ⟨rfl, rfl⟩

theorem tensor_shape (x y z : Matrix) (work left : Nat)
    (ok : (Matrix.tensorWork x y).run work = (.ok z, left)) :
    z.rows = x.rows * y.rows ∧ z.cols = x.cols * y.cols := by
  have dimensions := (tensor_success_cost x y z work left ok).1
  unfold Matrix.tensorWork at ok
  simp only [dimensions, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at ok
  obtain ⟨_, _, _, ok⟩ := work_bind_success _ _ _ _ _ ok
  obtain ⟨_, _, _, ok⟩ := work_bind_success _ _ _ _ _ ok
  obtain ⟨entries, _, _, ok⟩ := work_bind_success _ _ _ _ _ ok
  obtain ⟨made, _⟩ := work_lift_success _ _ _ _ ok
  obtain ⟨hz, _, _⟩ := matrix_make_value (x.rows * y.rows) (x.cols * y.cols) entries z made
  subst z
  exact ⟨rfl, rfl⟩

theorem isometry_wide (x : Matrix) (work : Nat) (wide : x.rows < x.cols) :
    (Matrix.isometryWork x).run work = (.ok false, work) := by
  unfold Matrix.isometryWork
  rw [if_pos wide]
  rfl

theorem isometry_success_cost (x : Matrix) (answer : Bool) (work left : Nat)
    (ok : (Matrix.isometryWork x).run work = (.ok answer, left)) :
    if x.rows < x.cols then answer = false ∧ left = work
    else x.rows * x.cols + 2 * x.cols * x.rows * x.cols ≤ work ∧
      left = work - (x.rows * x.cols + 2 * x.cols * x.rows * x.cols) := by
  by_cases wide : x.rows < x.cols
  · rw [if_pos wide]
    rw [isometry_wide x work wide] at ok
    cases ok
    exact ⟨rfl, rfl⟩
  · rw [if_neg wide]
    unfold Matrix.isometryWork at ok
    rw [if_neg wide] at ok
    obtain ⟨_, firstWork, pureOk, ok⟩ := work_bind_success _ _ _ _ _ ok
    obtain ⟨_, firstEq⟩ := work_pure_success _ _ _ _ pureOk
    subst firstWork
    obtain ⟨adjoint, adjointWork, hadjoint, ok⟩ := work_bind_success _ _ _ _ _ ok
    obtain ⟨product, productWork, hproduct, ok⟩ := work_bind_success _ _ _ _ _ ok
    obtain ⟨_, finalWork, hidentity, ok⟩ := work_bind_success _ _ _ _ _ ok
    have hfinal := (work_lift_success _ _ _ _ hidentity).2
    have hleft := (work_pure_success _ _ _ _ ok).2
    obtain ⟨hrows, hcols⟩ := adjoint_shape x adjoint work adjointWork hadjoint
    obtain ⟨cost1, remaining1⟩ := adjoint_success_cost x adjoint work adjointWork hadjoint
    obtain ⟨_, cost2, remaining2⟩ := compose_success_cost adjoint x product adjointWork productWork hproduct
    rw [hrows, hcols] at cost2 remaining2
    constructor <;> omega

/-- A successful computation has paid precisely this amount, independently of
the identity of its result. This does not postulate success or total arithmetic. -/
def SuccessfulCost {α : Type} (f : WorkM α) (cost : Nat) : Prop :=
  ∀ work value left, f.run work = (.ok value, left) →
    cost ≤ work ∧ left = work - cost

theorem sequential_success_cost {α β : Type} (first : WorkM α) (next : α → WorkM β)
    (firstCost : Nat) (nextCost : α → Nat) (hf : SuccessfulCost first firstCost)
    (hn : ∀ value, SuccessfulCost (next value) (nextCost value))
    (work left : Nat) (z : β) (ok : (first >>= next).run work = (.ok z, left)) :
    ∃ value middle, first.run work = (.ok value, middle) ∧
      (next value).run middle = (.ok z, left) ∧
      firstCost + nextCost value ≤ work ∧ left = work - (firstCost + nextCost value) := by
  obtain ⟨value, middle, hfirst, hnext⟩ := work_bind_success first next work left z ok
  obtain ⟨enough1, remaining1⟩ := hf work value middle hfirst
  obtain ⟨enough2, remaining2⟩ := hn value middle z left hnext
  exact ⟨value, middle, hfirst, hnext, by omega, by omega⟩

/-- Once the first stage succeeds, every continuation outcome retains its cost;
the continuation receives the actual reduced state, including on failure. -/
theorem sequential_no_refund {α β : Type} (first : WorkM α) (next : α → WorkM β)
    (firstCost work : Nat) (value : α) (middle : Nat)
    (hf : SuccessfulCost first firstCost) (hfirst : first.run work = (.ok value, middle))
    (hn : Spends (next value)) : ((first >>= next).run work).2 ≤ work - firstCost := by
  rw [work_bind_run, hfirst]
  obtain ⟨_, remaining⟩ := hf work value middle hfirst
  simpa [remaining] using hn middle

theorem sequential_failed_charge {α β : Type} (first : WorkM α) (next : α → Unit → WorkM β)
    (firstCost work : Nat) (value : α) (middle amount : Nat)
    (hf : SuccessfulCost first firstCost) (hfirst : first.run work = (.ok value, middle))
    (short : middle < amount) :
    (first >>= fun value => charge amount >>= next value).run work =
      (.error .workLimit, work - firstCost) := by
  rw [work_bind_run, hfirst]
  change (charge amount >>= next value).run middle = _
  rw [charged_failure amount middle (next value) short]
  rw [(hf work value middle hfirst).2]

theorem adjoint_remaining_cases (x : Matrix) (work : Nat) :
    ((Matrix.adjointWork x).run work).2 = work ∨
      ((Matrix.adjointWork x).run work).2 = work - x.rows * x.cols := by
  by_cases enough : x.rows * x.cols ≤ work
  · exact Or.inr (adjoint_remaining x work enough)
  · exact Or.inl (by rw [adjoint_work_limit x work (by omega)])

theorem compose_remaining_cases (x y : Matrix) (work : Nat) (shape : x.cols = y.rows) :
    ((Matrix.composeWork x y).run work).2 = work ∨
      ((Matrix.composeWork x y).run work).2 = work - 2 * x.rows * x.cols * y.cols := by
  by_cases enough : 2 * x.rows * x.cols * y.cols ≤ work
  · exact Or.inr (compose_remaining x y work shape enough)
  · exact Or.inl (by rw [compose_work_limit x y work shape (by omega)])

/-- All isometry failures retain exactly the charges of the stages entered:
no charge, the adjoint charge, or both adjoint and Gram-composition charges. -/
theorem isometry_failure_stages (x : Matrix) (work left : Nat) (error : Error)
    (failed : (Matrix.isometryWork x).run work = (.error error, left)) :
    left = work ∨ left = work - x.rows * x.cols ∨
      left = work - (x.rows * x.cols + 2 * x.cols * x.rows * x.cols) := by
  by_cases wide : x.rows < x.cols
  · rw [isometry_wide x work wide] at failed
    cases failed
  · unfold Matrix.isometryWork at failed
    rw [if_neg wide] at failed
    rcases work_bind_error _ _ _ _ _ failed with impossible | ⟨_, firstWork, hp, failed⟩
    · change (Except.ok PUnit.unit, work) = (.error error, left) at impossible
      cases impossible
    obtain ⟨_, hw⟩ := work_pure_success _ _ _ _ hp
    subst firstWork
    rcases work_bind_error _ _ _ _ _ failed with adjFailed | ⟨adjoint, adjointWork, adjOk, failed⟩
    · have stages := adjoint_remaining_cases x work
      rw [adjFailed] at stages
      rcases stages with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    obtain ⟨hrows, hcols⟩ := adjoint_shape x adjoint work adjointWork adjOk
    obtain ⟨_, adjRemaining⟩ := adjoint_success_cost x adjoint work adjointWork adjOk
    rcases work_bind_error _ _ _ _ _ failed with productFailed | ⟨product, productWork, productOk, failed⟩
    · have stages := compose_remaining_cases adjoint x adjointWork (by rw [hcols])
      rw [productFailed, hrows, hcols, adjRemaining] at stages
      rcases stages with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (by simpa [Nat.sub_sub] using h))
    obtain ⟨_, _, productRemaining⟩ := compose_success_cost adjoint x product adjointWork productWork productOk
    rw [hrows, hcols, adjRemaining] at productRemaining
    have lastKeeps : KeepsWork (do
        let identity ← liftExact (Matrix.identity x.cols)
        pure (product == identity)) :=
      keeps_bind _ _ (keeps_lift _) (fun identity => keeps_pure _)
    have lastRemaining := lastKeeps productWork
    rw [failed, productRemaining] at lastRemaining
    exact Or.inr (Or.inr (by simpa [Nat.sub_sub] using lastRemaining))

theorem identity_not_arithmetic_failure (dim : Nat) :
    Matrix.identity dim ≠ .error .arithmeticCapacity := by
  intro failed
  unfold Matrix.identity at failed
  split at failed
  · cases failed
  · unfold Matrix.make at failed
    split at failed
    · cases failed
    · split at failed <;> cases failed

/-- An arithmetic error cannot undo any successful precharge, including when
the Gram computation follows an already charged adjoint. -/
theorem isometry_arithmetic_failure_stages (x : Matrix) (work left : Nat)
    (failed : (Matrix.isometryWork x).run work = (.error .arithmeticCapacity, left)) :
    left = work - x.rows * x.cols ∨
      left = work - (x.rows * x.cols + 2 * x.cols * x.rows * x.cols) := by
  by_cases wide : x.rows < x.cols
  · rw [isometry_wide x work wide] at failed
    cases failed
  · unfold Matrix.isometryWork at failed
    rw [if_neg wide] at failed
    rcases work_bind_error _ _ _ _ _ failed with impossible | ⟨_, firstWork, hp, failed⟩
    · change (Except.ok PUnit.unit, work) = (Except.error Error.arithmeticCapacity, left) at impossible
      cases impossible
    obtain ⟨_, hw⟩ := work_pure_success _ _ _ _ hp
    subst firstWork
    rcases work_bind_error _ _ _ _ _ failed with adjFailed | ⟨adjoint, adjointWork, adjOk, failed⟩
    · exact Or.inl (adjoint_arithmetic_failure_cost x work left adjFailed).2
    obtain ⟨hrows, hcols⟩ := adjoint_shape x adjoint work adjointWork adjOk
    obtain ⟨_, adjRemaining⟩ := adjoint_success_cost x adjoint work adjointWork adjOk
    rcases work_bind_error _ _ _ _ _ failed with productFailed | ⟨product, productWork, _, failed⟩
    · obtain ⟨_, _, productRemaining⟩ := compose_arithmetic_failure_cost adjoint x adjointWork left productFailed
      rw [hrows, hcols, adjRemaining] at productRemaining
      exact Or.inr (by simpa [Nat.sub_sub] using productRemaining)
    rcases work_bind_error _ _ _ _ _ failed with identityFailed | ⟨identity, finalWork, _, impossible⟩
    · exact False.elim (identity_not_arithmetic_failure x.cols
        (work_lift_error _ _ _ _ identityFailed).1)
    · change (Except.ok (product == identity), finalWork) = (Except.error Error.arithmeticCapacity, left) at impossible
      cases impossible

end QleisliKernel.Exact
