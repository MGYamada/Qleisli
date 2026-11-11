import QleisliKernel.ExactMatrix

/-! Compact row or column supports preserve the exact ordered composition,
including arithmetic failures. An omitted term has a literal zero factor,
bounded coefficients on the opposite side and a canonical running sum.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Exact
open Semantics.Exact

private theorem scalar_exponent_bound (x : Scalar) (valid : Scalar.valid x = true) (i : Nat) :
    (x.get i).exponent ≤ maxInputExponent := by
  have bound (c : Coefficient) (h : Coefficient.valid c = true) : c.exponent ≤ maxInputExponent := by
    simp only [Coefficient.valid,Bool.and_eq_true,decide_eq_true_eq] at h
    exact Nat.le_trans h.1.2 (by decide)
  simp only [Scalar.valid,Bool.and_eq_true] at valid
  unfold Scalar.get
  split
  · exact bound _ valid.1.1.1
  · exact bound _ valid.1.1.2
  · exact bound _ valid.1.2
  · exact bound _ valid.2

private theorem coefficient_add_zero (x : Coefficient) (valid : Coefficient.valid x = true) :
    Coefficient.add x (.integer 0) = .ok x := by
  by_cases zero : x.numerator = 0
  · have exponent : x.exponent = 0 := by
      simp only [Coefficient.valid, Bool.and_eq_true, zero, ↓reduceIte, decide_eq_true_eq] at valid
      exact valid.2
    have canonical : x = .integer 0 := by cases x; simp_all [Semantics.Exact.Coefficient.integer]
    subst x
    rfl
  · simp [Coefficient.add,zero,Semantics.Exact.Coefficient.integer,bind,Except.bind,pure,Except.pure]

private theorem scalar_add_zero (x : Scalar) (valid : Scalar.valid x = true) :
    Scalar.add x Scalar.zero = .ok x := by
  obtain ⟨⟨⟨a,b⟩,c⟩,d⟩ := by simpa only [Scalar.valid,Bool.and_eq_true] using valid
  cases x with
  | mk xa xb xc xd =>
    change (do
      let ra ← Coefficient.add xa (.integer 0)
      let rb ← Coefficient.add xb (.integer 0)
      let rc ← Coefficient.add xc (.integer 0)
      let rd ← Coefficient.add xd (.integer 0)
      pure (⟨ra,rb,rc,rd⟩ : Scalar)) = .ok ⟨xa,xb,xc,xd⟩
    rw [coefficient_add_zero xa a,coefficient_add_zero xb b,coefficient_add_zero xc c,coefficient_add_zero xd d]
    rfl

private def dotStep (total : Scalar) (term : Scalar × Scalar) : Except Error Scalar := do
  let product ← mulZeroFast term.1 term.2
  Scalar.add total product

private theorem dotStep_valid (total : Scalar) (term : Scalar × Scalar) (next : Scalar)
    (valid : Scalar.valid total = true) (step : dotStep total term = .ok next) :
    Scalar.valid next = true := by
  simp only [dotStep,mulZeroFast_equiv] at step
  cases product : Scalar.mul term.1 term.2 with
  | error error => simp [product,bind,Except.bind] at step
  | ok result =>
    exact scalar_add_valid total result next valid (scalar_mul_valid _ _ _ product)
      (by simpa only [product,bind,Except.bind] using step)

-- Filtering either operand keeps the original index order, including the
-- first arithmetic failure. Each omitted product must be exact zero.
private theorem sparse_dot (indices : List Nat) (term : Nat → Scalar × Scalar)
    (keep : Nat → Bool) (total : Scalar) (valid : Scalar.valid total = true)
    (drops : ∀ k ∈ indices, keep k = false → Scalar.mul (term k).1 (term k).2 = .ok Scalar.zero) :
    (indices.filter keep).foldlM (fun sum k => dotStep sum (term k)) total =
      indices.foldlM (fun sum k => dotStep sum (term k)) total := by
  induction indices generalizing total with
  | nil => rfl
  | cons index rest ih =>
    have tailDrops : ∀ k ∈ rest, keep k = false → Scalar.mul (term k).1 (term k).2 = .ok Scalar.zero :=
      fun k inside => drops k (List.mem_cons_of_mem _ inside)
    cases kept : keep index with
    | false =>
      have unchanged : dotStep total (term index) = .ok total := by
        unfold dotStep
        rw [mulZeroFast_equiv,drops index List.mem_cons_self kept]
        exact scalar_add_zero total valid
      simp only [List.filter_cons,kept,Bool.false_eq_true,if_false,List.foldlM_cons,unchanged,bind,Except.bind]
      exact ih total valid tailDrops
    | true =>
      simp only [List.filter_cons,kept,if_true,List.foldlM_cons,bind,Except.bind]
      cases stepped : dotStep total (term index) with
      | error error => rfl
      | ok next => exact ih next (dotStep_valid total (term index) next valid stepped) tailDrops

private theorem mapM_equal_on {α β ε : Type} (xs : List α)
    (first second : α → Except ε β) (equal : ∀ a ∈ xs, first a = second a) :
    xs.mapM first = xs.mapM second := by
  induction xs with
  | nil => rfl
  | cons head tail ih =>
    have sameHead := equal head List.mem_cons_self
    have sameTail := ih (fun a member => equal a (List.mem_cons_of_mem _ member))
    simp only [List.mapM_cons,sameHead,sameTail]

private def denseEntries (x y : Matrix) : Except Error (List Scalar) :=
  (List.range (x.rows*y.cols)).mapM fun i =>
    (List.range x.cols).foldlM (fun sum k => dotStep sum (x.entry (i/y.cols) k,y.entry k (i%y.cols))) Scalar.zero

private def arrayEntry (entries : Array Scalar) (cols row col : Nat) : Scalar :=
  entries[row * cols + col]?.getD Scalar.zero

private theorem arrayEntry_eq (x : Matrix) (row col : Nat) :
    arrayEntry x.entries.toArray x.cols row col = x.entry row col := by
  simp only [arrayEntry,List.getElem?_toArray,Matrix.entry]

private def compactRows (rows cols : Nat) (entries : Array Scalar) : Array (List Nat) :=
  ((List.range rows).map fun row =>
    (List.range cols).filter fun k => !(arrayEntry entries cols row k == Scalar.zero)).toArray

private def compactColumns (rows cols : Nat) (entries : Array Scalar) : Array (List Nat) :=
  ((List.range cols).map fun column =>
    (List.range rows).filter fun k => !(arrayEntry entries cols k column == Scalar.zero)).toArray

private def sparseEntries (x y : Matrix) (left right : Array Scalar)
    (support : Nat → Nat → List Nat) : Except Error (List Scalar) :=
  (List.range (x.rows*y.cols)).mapM fun i =>
    let row := i / y.cols
    let column := i % y.cols
    (support row column).foldlM
      (fun sum k => dotStep sum
        (arrayEntry left x.cols row k,arrayEntry right y.cols k column)) Scalar.zero

private def rowSupport (rows : Array (List Nat)) (row _column : Nat) : List Nat :=
  rows[row]?.getD []

private def columnSupport (columns : Array (List Nat)) (_row column : Nat) : List Nat :=
  columns[column]?.getD []

private theorem sparse_rows_equiv (x y : Matrix) (right : Matrix.Admitted y) :
    sparseEntries x y x.entries.toArray y.entries.toArray
      (rowSupport (compactRows x.rows x.cols x.entries.toArray)) = denseEntries x y := by
  unfold sparseEntries denseEntries
  apply mapM_equal_on
  intro index member
  have positive : 0 < y.cols := by
    have shape := right.1
    simp only [matrixValid,Bool.and_eq_true,decide_eq_true_eq] at shape
    exact shape.1.2
  have row : index/y.cols < x.rows :=
    (Nat.div_lt_iff_lt_mul positive).mpr (List.mem_range.mp member)
  simp only [rowSupport,compactRows,List.getElem?_toArray,List.getElem?_map,List.getElem?_range,row,
    Option.map_some,Option.getD_some,arrayEntry_eq]
  apply sparse_dot _ _ _ _ (by decide)
  intro k _ omitted
  have zero : x.entry (index / y.cols) k = Scalar.zero := by simpa using omitted
  simp only [zero]
  exact scalar_zero_mul _ (scalar_exponent_bound _ (matrix_entry_valid _ right _ _))

private theorem sparse_columns_equiv (x y : Matrix) (left : Matrix.Admitted x)
    (shape : x.cols = y.rows) :
    sparseEntries x y x.entries.toArray y.entries.toArray
      (columnSupport (compactColumns y.rows y.cols y.entries.toArray)) = denseEntries x y := by
  unfold sparseEntries denseEntries
  apply mapM_equal_on
  intro index member
  have positive : 0 < y.cols := by
    by_cases zero : y.cols = 0
    · simp [zero] at member
    · omega
  have column := Nat.mod_lt index positive
  simp only [columnSupport,compactColumns,List.getElem?_toArray,List.getElem?_map,List.getElem?_range,column,
    Option.map_some,Option.getD_some,arrayEntry_eq,← shape]
  apply sparse_dot _ _ _ _ (by decide)
  intro k _ omitted
  have zero : y.entry k (index % y.cols) = Scalar.zero := by simpa using omitted
  simp only [zero]
  exact scalar_mul_zero _ (scalar_exponent_bound _ (matrix_entry_valid _ left _ _))

private theorem lift_exact_bind {α β : Type}
    (original : Except Error α) (next : α → Except Error β) :
    (liftExact original >>= (fun value => liftExact (next value))) = liftExact (original >>= next) := by
  cases original <;> rfl

private theorem lift_exact_fold {α β : Type} (xs : List α) (step : β → α → Except Error β) (initial : β) :
    xs.foldlM (fun state item => liftExact (step state item)) initial =
      liftExact (xs.foldlM step initial) := by
  induction xs generalizing initial with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.foldlM_cons,ih,lift_exact_bind]

private theorem lift_exact_map {α β : Type} (xs : List α) (step : α → Except Error β) :
    xs.mapM (fun item => liftExact (step item)) = liftExact (xs.mapM step) := by
  induction xs with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.mapM_cons,ih]
    cases step head <;> cases tail.mapM step <;> rfl

private def finishComposition (x y : Matrix) (left right : Array Scalar)
    (support : Nat → Nat → List Nat) : Except Error Matrix := do
  let entries ← sparseEntries x y left right support
  Matrix.make x.rows y.cols entries

private def denseComposition (x y : Matrix) : Except Error Matrix := do
  let entries ← denseEntries x y
  Matrix.make x.rows y.cols entries

/-- Reserve the conversions, support scan and output visits before doing them.
The second charge covers both exact operations for every retained dot term. -/
def Matrix.composeSparseLeftWork (x y : Matrix) : WorkM Matrix := do
  if x.cols ≠ y.rows then throw .shapeMismatch
  charge (x.entries.length + y.entries.length + x.rows * (2 * x.cols + 1) + 3 * x.rows * y.cols)
  let left := x.entries.toArray
  let right := y.entries.toArray
  let rows := compactRows x.rows x.cols left
  let terms := rows.foldl (fun total row => total + row.length) 0
  charge (2 * terms * y.cols)
  liftExact (finishComposition x y left right (rowSupport rows))

/-- The symmetric cost strategy builds support from the right operand's
columns. The multiplication and accumulation order is unchanged. -/
def Matrix.composeSparseRightWork (x y : Matrix) : WorkM Matrix := do
  if x.cols ≠ y.rows then throw .shapeMismatch
  charge (x.entries.length + y.entries.length + y.cols * (2 * y.rows + 1) + 3 * x.rows * y.cols)
  let left := x.entries.toArray
  let right := y.entries.toArray
  let columns := compactColumns y.rows y.cols right
  let terms := columns.foldl (fun total column => total + column.length) 0
  charge (2 * terms * x.rows)
  liftExact (finishComposition x y left right (columnSupport columns))

private theorem compose_from_dense_entries (x y : Matrix) :
    Matrix.composeWork x y = (do
      if x.cols ≠ y.rows then throw .shapeMismatch
      charge (2*x.rows*x.cols*y.cols)
      liftExact (denseComposition x y)) := by
  simp only [Matrix.composeWork_list,denseComposition,denseEntries,dotStep,mulZeroFast_equiv,
    bind_pure,← lift_exact_bind,← lift_exact_fold,← lift_exact_map]

private theorem compose_at_cost (x y result : Matrix) (same : x.cols = y.rows)
    (value : denseComposition x y = .ok result) :
    (Matrix.composeWork x y).run (2*x.rows*x.cols*y.cols) = (.ok result,0) := by
  simp only [compose_from_dense_entries,if_neg (not_not_intro same),pure_bind]
  rw [charged_run _ _ _ (Nat.le_refl _),Nat.sub_self,value]
  rfl

theorem Matrix.composeSparseLeft_success (x y result : Matrix) (right : Matrix.Admitted y)
    (work left : Nat) (ok : (Matrix.composeSparseLeftWork x y).run work = (.ok result,left)) :
    (Matrix.composeWork x y).run (2*x.rows*x.cols*y.cols) = (.ok result,0) := by
  by_cases same : x.cols = y.rows
  · unfold Matrix.composeSparseLeftWork at ok
    simp only [if_neg (not_not_intro same),pure_bind] at ok
    obtain ⟨_,_,_,ok⟩ := work_bind_success _ _ _ _ _ ok
    obtain ⟨_,_,_,ok⟩ := work_bind_success _ _ _ _ _ ok
    apply compose_at_cost _ _ _ same
    simpa only [finishComposition,denseComposition,sparse_rows_equiv _ _ right]
      using (work_lift_success _ _ _ _ ok).1
  · simp [Matrix.composeSparseLeftWork,same] at ok
    cases ok

theorem Matrix.composeSparseRight_success (x y result : Matrix) (admitted : Matrix.Admitted x)
    (work left : Nat) (ok : (Matrix.composeSparseRightWork x y).run work = (.ok result,left)) :
    (Matrix.composeWork x y).run (2*x.rows*x.cols*y.cols) = (.ok result,0) := by
  by_cases same : x.cols = y.rows
  · unfold Matrix.composeSparseRightWork at ok
    simp only [if_neg (not_not_intro same),pure_bind] at ok
    obtain ⟨_,_,_,ok⟩ := work_bind_success _ _ _ _ _ ok
    obtain ⟨_,_,_,ok⟩ := work_bind_success _ _ _ _ _ ok
    apply compose_at_cost _ _ _ same
    simpa only [finishComposition,denseComposition,sparse_columns_equiv _ _ admitted same]
      using (work_lift_success _ _ _ _ ok).1
  · simp [Matrix.composeSparseRightWork,same] at ok
    cases ok

-- Index the transposed input from an array. The adjoint still visits and
-- conjugates every original coefficient in exactly the ordinary order.
private def adjointArrayWork (x : Matrix) : WorkM Matrix := do
  charge (x.rows * x.cols)
  let input := x.entries.toArray
  let entries ← (List.range (x.rows * x.cols)).mapM fun i =>
    liftExact (Scalar.conjugate (arrayEntry input x.cols (i % x.rows) (i / x.rows)))
  liftExact (Matrix.make x.cols x.rows entries)

private theorem adjointArray_eq (x : Matrix) : adjointArrayWork x = Matrix.adjointWork x := by
  simp only [adjointArrayWork,Matrix.adjointWork,arrayEntry_eq]

/-- The same exact Gram matrix as `isometryWork`, with compact ordered rows.
The caller independently checks that the right operand is admitted. -/
def Matrix.sparseIsometryWork (x : Matrix) : WorkM Bool := do
  if x.rows < x.cols then return false
  charge x.entries.length
  let adjoint ← adjointArrayWork x
  let product ← Matrix.composeSparseLeftWork adjoint x
  let identity ← liftExact (Matrix.identity x.cols)
  return product == identity

/-- Changing the budget changes neither the order nor the result of the Gram
equation. Success of the compact executable entails the original check. -/
theorem Matrix.sparseIsometry_success (x : Matrix) (admitted : Matrix.Admitted x)
    (work left : Nat) (ok : (Matrix.sparseIsometryWork x).run work = (.ok true,left)) :
    ∃ before after, Matrix.isometry x before = (.ok true,after) := by
  by_cases wide : x.rows < x.cols
  · simp [Matrix.sparseIsometryWork,wide] at ok
    cases ok
  unfold Matrix.sparseIsometryWork at ok
  simp only [if_neg wide,pure_bind,adjointArray_eq] at ok
  obtain ⟨_,afterArray,_,ok⟩ := work_bind_success _ _ _ _ _ ok
  obtain ⟨adjoint,middle,adjointOk,ok⟩ := work_bind_success _ _ _ _ _ ok
  obtain ⟨product,_,productOk,ok⟩ := work_bind_success _ _ _ _ _ ok
  obtain ⟨identity,_,identityOk,ok⟩ := work_bind_success _ _ _ _ _ ok
  have dense := Matrix.composeSparseLeft_success adjoint x product admitted _ _ productOk
  have identityEq := (work_lift_success _ _ _ _ identityOk).1
  have resultEq := (work_pure_success _ _ _ _ ok).1
  let cost := 2*adjoint.rows*adjoint.cols*x.cols
  obtain ⟨enough,remaining⟩ := adjoint_success_cost x adjoint afterArray middle adjointOk
  have adjointAtCost : (Matrix.adjointWork x).run (x.rows*x.cols + cost) = (.ok adjoint,cost) := by
    let finish := do
      let entries ← (List.range (x.rows * x.cols)).mapM fun i =>
        Scalar.conjugate (x.entry (i % x.rows) (i / x.rows))
      Matrix.make x.cols x.rows entries
    have splitWork : Matrix.adjointWork x = (do charge (x.rows*x.cols); liftExact finish) := by
      simp only [Matrix.adjointWork,finish,lift_exact_bind,lift_exact_map]
    rw [splitWork,charged_run _ _ _ enough] at adjointOk
    have adjointEq := (work_lift_success _ _ _ _ adjointOk).1
    rw [splitWork,charged_run _ _ _ (by omega),adjointEq]
    change (Except.ok adjoint,x.rows*x.cols + cost - x.rows*x.cols) = _
    congr 1
    omega
  refine ⟨x.rows*x.cols + cost,0,?_⟩
  simp only [Matrix.isometry,Matrix.isometryWork,if_neg wide,pure_bind,work_bind_run,adjointAtCost]
  have productAtCost : (Matrix.composeWork adjoint x).run cost = (.ok product,0) := dense
  rw [productAtCost,identityEq]
  change (Except.ok (product == identity),0) = _
  rw [resultEq]

#print axioms Matrix.composeSparseLeft_success
#print axioms Matrix.composeSparseRight_success
#print axioms Matrix.sparseIsometry_success
end QleisliKernel.Exact
