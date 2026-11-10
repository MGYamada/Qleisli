import QleisliKernel.ExactMatrix

/-! Compact rows preserve the exact ordered composition, including arithmetic
failures. Literal zero terms are omitted only with canonical coefficients on
the right and a canonical running sum.
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

/-- A compact row or column retains the original order of the nonzero
terms and the first arithmetic failure. The dropped terms must have a
literal zero operand and bounded exponents. -/
private theorem sparse_dot (terms : List (Scalar × Scalar)) (keep : Scalar × Scalar → Bool)
    (total : Scalar) (valid : Scalar.valid total = true)
    (bounds : ∀ term ∈ terms, Scalar.valid term.2 = true)
    (drops : ∀ term ∈ terms, keep term = false → term.1 = Scalar.zero) :
    (terms.filter keep).foldlM dotStep total = terms.foldlM dotStep total := by
  induction terms generalizing total with
  | nil => rfl
  | cons term rest ih =>
    have tailBound : ∀ other ∈ rest, Scalar.valid other.2 = true :=
      fun other inside => bounds other (List.mem_cons_of_mem _ inside)
    have tailDrops : ∀ other ∈ rest, keep other = false → other.1 = Scalar.zero :=
      fun other inside => drops other (List.mem_cons_of_mem _ inside)
    cases kept : keep term with
    | false =>
      have safe := bounds term List.mem_cons_self
      have zeroProduct : Scalar.mul term.1 term.2 = .ok Scalar.zero := by
        rw [drops term List.mem_cons_self kept]
        exact scalar_zero_mul term.2 (fun k => scalar_exponent_bound term.2 safe k)
      have unchanged : dotStep total term = .ok total := by
        unfold dotStep
        rw [mulZeroFast_equiv,zeroProduct]
        exact scalar_add_zero total valid
      simp only [List.filter_cons,kept,Bool.false_eq_true,if_false,List.foldlM_cons,unchanged,bind,Except.bind]
      exact ih total valid tailBound tailDrops
    | true =>
      simp only [List.filter_cons,kept,if_true,List.foldlM_cons,bind,Except.bind]
      cases stepped : dotStep total term with
      | error error => rfl
      | ok next => exact ih next (dotStep_valid total term next valid stepped) tailBound tailDrops

private theorem sparse_indexed_dot (indices : List Nat) (left right : Nat → Scalar) (total : Scalar)
    (valid : Scalar.valid total = true)
    (bounds : ∀ index ∈ indices, Scalar.valid (right index) = true) :
    let product := fun k => (left k,right k)
    let step := fun sum k => dotStep sum (product k)
    ((indices.filter (fun k => !(left k == Scalar.zero))).foldlM step total) =
      indices.foldlM step total := by
  intro product step
  have safe : ∀ term ∈ indices.map product, Scalar.valid term.2 = true := by
    intro term member
    obtain ⟨index, inside, rfl⟩ := List.mem_map.mp member
    exact bounds index inside
  let keep := fun term : Scalar × Scalar => !(term.1 == Scalar.zero)
  have drops : ∀ term ∈ indices.map product, keep term = false → term.1 = Scalar.zero := by
    intro term _ omitted
    simpa [keep] using omitted
  simpa only [List.filter_map,List.foldlM_map,Function.comp_def,keep,step,product] using
    sparse_dot (indices.map product) keep total valid safe drops

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

private def sparseEntries (x y : Matrix) (left right : Array Scalar)
    (rows : Array (List Nat)) : Except Error (List Scalar) :=
  (List.range (x.rows*y.cols)).mapM fun i =>
    (rows[i/y.cols]?.getD []).foldlM
      (fun sum k => dotStep sum
        (arrayEntry left x.cols (i/y.cols) k,arrayEntry right y.cols k (i%y.cols))) Scalar.zero

private theorem sparse_entries_equiv (x y : Matrix) (right : Matrix.Admitted y) :
    sparseEntries x y x.entries.toArray y.entries.toArray
      (compactRows x.rows x.cols x.entries.toArray) = denseEntries x y := by
  unfold sparseEntries denseEntries
  apply mapM_equal_on
  intro index member
  have positive : 0 < y.cols := by
    have shape := right.1
    simp only [matrixValid,Bool.and_eq_true,decide_eq_true_eq] at shape
    exact shape.1.2
  have row : index/y.cols < x.rows :=
    (Nat.div_lt_iff_lt_mul positive).mpr (List.mem_range.mp member)
  have actual : ((compactRows x.rows x.cols x.entries.toArray)[index/y.cols]?).getD [] =
      (List.range x.cols).filter (fun k => !(x.entry (index/y.cols) k == Scalar.zero)) := by
    simp only [compactRows,List.getElem?_toArray,List.getElem?_map,List.getElem?_range,row,
      Option.map_some,Option.getD_some,arrayEntry_eq]
  simp only [actual,arrayEntry_eq]
  exact sparse_indexed_dot (List.range x.cols) (x.entry (index/y.cols))
    (fun k => y.entry k (index%y.cols)) Scalar.zero (by decide)
    (fun k _ => matrix_entry_valid _ right _ _)

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
    (rows : Array (List Nat)) : Except Error Matrix := do
  let entries ← sparseEntries x y left right rows
  Matrix.make x.rows y.cols entries

/-- Reserve the conversions, support scan and output visits before doing them.
The second charge covers both exact operations for every retained dot term. -/
private def sparseComposeWork (x y : Matrix) : WorkM Matrix := do
  if x.cols ≠ y.rows then throw .shapeMismatch
  charge (x.entries.length + y.entries.length + x.rows * (2 * x.cols + 1) + 3 * x.rows * y.cols)
  let left := x.entries.toArray
  let right := y.entries.toArray
  let rows := compactRows x.rows x.cols left
  let terms := rows.foldl (fun total row => total + row.length) 0
  charge (2 * terms * y.cols)
  liftExact (finishComposition x y left right rows)

private theorem compose_from_sparse_entries (x y : Matrix) (right : Matrix.Admitted y) :
    Matrix.composeWork x y = (do
      if x.cols ≠ y.rows then throw .shapeMismatch
      charge (2*x.rows*x.cols*y.cols)
      liftExact (finishComposition x y x.entries.toArray y.entries.toArray
        (compactRows x.rows x.cols x.entries.toArray))) := by
  simp only [Matrix.composeWork_list,finishComposition,sparse_entries_equiv x y right,
    denseEntries,dotStep,mulZeroFast_equiv,bind_pure,← lift_exact_bind,← lift_exact_fold,← lift_exact_map]

private theorem sparseCompose_success (x y result : Matrix) (right : Matrix.Admitted y)
    (work left : Nat) (ok : (sparseComposeWork x y).run work = (.ok result,left)) :
    (Matrix.composeWork x y).run (2*x.rows*x.cols*y.cols) = (.ok result,0) := by
  by_cases same : x.cols = y.rows
  · unfold sparseComposeWork at ok
    simp only [if_neg (not_not_intro same),pure_bind] at ok
    obtain ⟨_,middle,_,ok⟩ := work_bind_success _ _ _ _ _ ok
    obtain ⟨_,_,_,ok⟩ := work_bind_success _ _ _ _ _ ok
    have resultEq := (work_lift_success _ _ _ _ ok).1
    simp only [compose_from_sparse_entries x y right,if_neg (not_not_intro same),pure_bind]
    rw [charged_run _ _ _ (Nat.le_refl _),Nat.sub_self,resultEq]
    rfl
  · simp [sparseComposeWork,same] at ok
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
  let product ← sparseComposeWork adjoint x
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
  have dense := sparseCompose_success adjoint x product admitted _ _ productOk
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

#print axioms Matrix.sparseIsometry_success
end QleisliKernel.Exact
