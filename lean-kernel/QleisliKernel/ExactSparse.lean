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

private theorem filter_single (indices : List Nat) (pick : Nat)
    (unique : indices.Nodup) (present : pick ∈ indices) :
    indices.filter (· == pick) = [pick] := by
  induction indices with
  | nil => cases present
  | cons first rest ih =>
    obtain ⟨missing,distinct⟩ := List.nodup_cons.mp unique
    by_cases same : first = pick
    · subst first
      have empty : rest.filter (· == pick) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro k member
        simp only [beq_iff_eq]
        rintro rfl
        exact missing member
      simp [empty]
    · have tail : pick ∈ rest := (List.mem_cons.mp present).resolve_left (Ne.symm same)
      simp [same,ih distinct tail]

private theorem dot_select (width pick : Nat) (bound : pick < width)
    (term : Nat → Scalar × Scalar) (value : Scalar)
    (product : ∀ k < width, Scalar.mul (term k).1 (term k).2 =
      .ok (if k = pick then value else Scalar.zero)) :
    (List.range width).foldlM (fun sum k => dotStep sum (term k)) Scalar.zero = .ok value := by
  have sparse := sparse_dot (List.range width) term (· == pick) Scalar.zero (by decide)
    (fun k member dropped => by
      have different : k ≠ pick := by simpa using dropped
      simpa only [if_neg different] using product k (List.mem_range.mp member))
  rw [filter_single _ _ List.nodup_range (List.mem_range.mpr bound)] at sparse
  rw [← sparse]
  simp only [List.foldlM_cons,dotStep,mulZeroFast_equiv,product pick bound,if_true,bind,Except.bind,
    scalar_zero_add,List.foldlM_nil,pure,Except.pure]

private def diagonalCode (dim : Nat) : Matrix :=
  ⟨dim,dim,(List.range (dim*dim)).map fun i =>
    if i / dim = i % dim then Scalar.one else Scalar.zero⟩

private theorem diagonal_entry (dim row col : Nat) (rowBound : row < dim) (colBound : col < dim) :
    (diagonalCode dim).entry row col = if row = col then Scalar.one else Scalar.zero := by
  have positive : 0 < dim := Nat.zero_lt_of_lt colBound
  have indexBound : row*dim+col < dim*dim := by
    calc
      row*dim+col < row*dim+dim := Nat.add_lt_add_left colBound _
      _ = (row+1)*dim := (Nat.succ_mul _ _).symm
      _ ≤ dim*dim := Nat.mul_le_mul_right _ rowBound
  have remainder : (row*dim+col) % dim = col := by
    simp [Nat.add_mod,Nat.mod_eq_of_lt colBound]
  have quotient : (row*dim+col) / dim = row := by
    rw [Nat.mul_comm row dim,Nat.mul_add_div positive,Nat.div_eq_of_lt colBound,Nat.add_zero]
  simp only [diagonalCode,Matrix.entry,List.getElem?_map,List.getElem?_range indexBound,
    Option.map_some,Option.getD_some,remainder,quotient]

private theorem identity_is_diagonal (dim : Nat) (code : Matrix)
    (identity : Matrix.identity dim = .ok code) : code = diagonalCode dim := by
  unfold Matrix.identity Matrix.make at identity
  split at identity
  · cases identity
  · split at identity
    · cases identity
    · exact (Except.ok.inj identity).symm

private theorem reindex_entries (x : Matrix) (length : x.entries.length = x.rows*x.cols) :
    (List.range (x.rows*x.cols)).map (fun i => x.entry (i / x.cols) (i % x.cols)) =
      x.entries := by
  apply List.ext_getElem?
  intro i
  by_cases inside : i < x.rows*x.cols
  · have bound : i < x.entries.length := length ▸ inside
    have linear : i / x.cols * x.cols + i % x.cols = i := by
      calc
        i / x.cols * x.cols + i % x.cols = i % x.cols + x.cols * (i / x.cols) := by
          rw [Nat.mul_comm (i / x.cols),Nat.add_comm]
        _ = i := Nat.mod_add_div i x.cols
    simp only [List.getElem?_map,List.getElem?_range inside,Option.map_some,Matrix.entry,linear,
      List.getElem?_eq_getElem bound,Option.getD_some]
  · have absent : x.entries.length ≤ i := length ▸ Nat.le_of_not_gt inside
    simp only [List.getElem?_map,List.getElem?_eq_none (l := List.range _) (by simpa using Nat.le_of_not_gt inside),
      Option.map_none,List.getElem?_eq_none absent]

private theorem map_exact {α β : Type} (items : List α) (step : α → Except Error β)
    (output : α → β) (exactAt : ∀ item ∈ items, step item = .ok (output item)) :
    items.mapM step = .ok (items.map output) := by
  induction items with
  | nil => rfl
  | cons first rest ih =>
    have tail := ih (fun item member => exactAt item (List.mem_cons_of_mem _ member))
    simp only [List.mapM_cons,List.map_cons,exactAt first List.mem_cons_self,tail,bind,
      Except.bind,pure,Except.pure]

/-- Every line has either one literal unit coefficient or only zeros.
The array is indexed in the original row or column order. -/
structure SingleEntrySupport (outer inner : Nat) (entry : Nat → Nat → Scalar) where
  indices : Array (Option Nat)
  bounded : ∀ line < outer, ∀ index, indices[line]?.getD none = some index → index < inner
  literal : ∀ line < outer, ∀ index < inner,
    entry line index = if indices[line]?.getD none = some index then Scalar.one else Scalar.zero

private def inspectSingleEntries (outer inner : Nat) (entry : Nat → Nat → Scalar) :
    Option (SingleEntrySupport outer inner entry) := do
  let positions := List.range inner
  let picks := ((List.range outer).map fun line =>
    positions.find? (fun index => entry line index == Scalar.one)).toArray
  if verified : (List.range outer).all (fun line => positions.all fun index =>
      entry line index == (if picks[line]?.getD none == some index then Scalar.one else Scalar.zero)) then
    return ⟨picks,by
      intro line lineBound index found
      simp only [picks,List.getElem?_toArray,List.getElem?_map,List.getElem?_range lineBound,
        Option.map_some,Option.getD_some] at found
      exact List.mem_range.mp (List.mem_of_find?_eq_some found),by
      intro line lineBound index indexBound
      have row := List.all_eq_true.mp verified line (List.mem_range.mpr lineBound)
      have cell := beq_iff_eq.mp (List.all_eq_true.mp row index (List.mem_range.mpr indexBound))
      simpa only [beq_iff_eq] using cell⟩
  else none

structure Matrix.SingleEntrySupports (matrix : Matrix) where
  rows : SingleEntrySupport matrix.rows matrix.cols matrix.entry
  columns : SingleEntrySupport matrix.cols matrix.rows (fun col row => matrix.entry row col)

/-- Precharge both scans before reading the literal coefficients. The decision
contains only arrays and proof-erased bounds. -/
def Matrix.readSingleEntrySupports (matrix : Matrix) : WorkM (Option (Matrix.SingleEntrySupports matrix)) := do
  if !matrixValid matrix.rows matrix.cols then return none
  charge (10*matrix.rows*matrix.cols + 4*(matrix.rows+matrix.cols) + 1)
  let entries := (matrix.entries.take (matrix.rows*matrix.cols)).toArray
  let entry := arrayEntry entries matrix.cols
  have original (row col : Nat) (rowBound : row < matrix.rows) (colBound : col < matrix.cols) :
      entry row col = matrix.entry row col := by
    have cell : row*matrix.cols+col < matrix.rows*matrix.cols := by
      calc
        row*matrix.cols+col < row*matrix.cols+matrix.cols := Nat.add_lt_add_left colBound _
        _ = (row+1)*matrix.cols := (Nat.succ_mul _ _).symm
        _ ≤ matrix.rows*matrix.cols := Nat.mul_le_mul_right _ rowBound
    simp only [entry,entries,arrayEntry,Matrix.entry,List.getElem?_toArray,List.getElem?_take_of_lt cell]
  let supports : Option (Matrix.SingleEntrySupports matrix) := do
    let rows ← inspectSingleEntries matrix.rows matrix.cols entry
    let columns ← inspectSingleEntries matrix.cols matrix.rows (fun col row => entry row col)
    pure ⟨⟨rows.indices,rows.bounded,by
      intro row rowBound col colBound
      exact (original row col rowBound colBound).symm.trans (rows.literal row rowBound col colBound)⟩,
      ⟨columns.indices,columns.bounded,by
        intro col colBound row rowBound
        exact (original row col rowBound colBound).symm.trans (columns.literal col colBound row rowBound)⟩⟩
  return supports

private def selectedValue (pick : Option Nat) (value : Nat → Scalar) : Scalar :=
  match pick with | none => Scalar.zero | some index => value index

private theorem dot_select_optional (width : Nat) (pick : Option Nat)
    (bounded : ∀ i, pick = some i → i < width) (term : Nat → Scalar × Scalar) (value : Nat → Scalar)
    (product : ∀ k < width, Scalar.mul (term k).1 (term k).2 =
      .ok (if pick = some k then value k else Scalar.zero)) :
    (List.range width).foldlM (fun sum k => dotStep sum (term k)) Scalar.zero =
      .ok (selectedValue pick value) := by
  cases pick with
  | none =>
    have sparse := sparse_dot (List.range width) term (fun _ => false) Scalar.zero (by decide)
      (fun k member _ => by simpa using product k (List.mem_range.mp member))
    have empty : (List.range width).filter (fun _ => false) = [] := by
      apply List.filter_eq_nil_iff.mpr
      simp
    rw [empty] at sparse
    exact sparse.symm
  | some index =>
    apply dot_select width index (bounded index rfl)
    intro k inside
    by_cases same : k = index
    · subst k
      simpa using product index inside
    · simpa [same,Ne.symm same] using product k inside

private def gatherLeft (code y : Matrix) (rows : Array (Option Nat)) : List Scalar :=
  let entries := y.entries.toArray
  (List.range (code.rows*y.cols)).map fun index =>
    match rows[index/y.cols]?.getD none with
    | none => Scalar.zero
    | some selected => arrayEntry entries y.cols selected (index%y.cols)

private def gatherRight (x code : Matrix) (columns : Array (Option Nat)) : List Scalar :=
  let entries := x.entries.toArray
  (List.range (x.rows*code.cols)).map fun index =>
    match columns[index%code.cols]?.getD none with
    | none => Scalar.zero
    | some selected => arrayEntry entries x.cols (index/code.cols) selected

/-- With certified single-entry support, copy each required coefficient
or write the padding zero. -/
def Matrix.composeSingleLeftWork (code y : Matrix)
    (rows : SingleEntrySupport code.rows code.cols code.entry) : WorkM Matrix := do
  if code.cols ≠ y.rows then throw .shapeMismatch
  charge (y.entries.length + 3*code.rows*y.cols)
  liftExact (Matrix.make code.rows y.cols (gatherLeft code y rows.indices))

def Matrix.composeSingleRightWork (x code : Matrix)
    (columns : SingleEntrySupport code.cols code.rows (fun col row => code.entry row col)) : WorkM Matrix := do
  if x.cols ≠ code.rows then throw .shapeMismatch
  charge (x.entries.length + 3*x.rows*code.cols)
  liftExact (Matrix.make x.rows code.cols (gatherRight x code columns.indices))

private theorem gather_left_entries (code y : Matrix) (admitted : Matrix.Admitted y)
    (rows : SingleEntrySupport code.rows code.cols code.entry) :
    denseEntries code y = .ok (gatherLeft code y rows.indices) := by
  unfold denseEntries gatherLeft
  apply map_exact
  intro index member
  have dimensions := admitted.1
  simp only [matrixValid,Bool.and_eq_true,decide_eq_true_eq] at dimensions
  have rowBound := (Nat.div_lt_iff_lt_mul dimensions.1.2).mpr (List.mem_range.mp member)
  simp only [arrayEntry_eq]
  apply dot_select_optional code.cols (rows.indices[index/y.cols]?.getD none)
    (rows.bounded _ rowBound) (fun k => (code.entry (index/y.cols) k,y.entry k (index%y.cols)))
    (fun k => y.entry k (index%y.cols))
  intro k inside
  change Scalar.mul (code.entry (index/y.cols) k) (y.entry k (index%y.cols)) = _
  rw [rows.literal _ rowBound _ inside]
  have valid := matrix_entry_valid y admitted k (index%y.cols)
  split
  · exact scalar_one_mul _ valid
  · exact scalar_zero_mul _ (scalar_exponent_bound _ valid)

private theorem gather_right_entries (x code : Matrix) (admitted : Matrix.Admitted x)
    (columns : SingleEntrySupport code.cols code.rows (fun col row => code.entry row col))
    (shape : x.cols = code.rows) : denseEntries x code = .ok (gatherRight x code columns.indices) := by
  unfold denseEntries gatherRight
  apply map_exact
  intro index member
  have positive : 0 < code.cols := by
    by_cases zero : code.cols = 0
    · simp [zero] at member
    · omega
  have colBound := Nat.mod_lt index positive
  simp only [arrayEntry_eq]
  apply dot_select_optional x.cols (columns.indices[index%code.cols]?.getD none)
    (fun k found => shape.symm ▸ columns.bounded _ colBound k found)
    (fun k => (x.entry (index/code.cols) k,code.entry k (index%code.cols)))
    (fun k => x.entry (index/code.cols) k)
  intro k inside
  change Scalar.mul (x.entry (index/code.cols) k) (code.entry k (index%code.cols)) = _
  rw [columns.literal _ colBound _ (shape ▸ inside)]
  have valid := matrix_entry_valid x admitted (index/code.cols) k
  split
  · exact scalar_mul_one _ valid
  · exact scalar_mul_zero _ (scalar_exponent_bound _ valid)

theorem Matrix.composeSingleLeft_success (code y result : Matrix) (admitted : Matrix.Admitted y)
    (rows : SingleEntrySupport code.rows code.cols code.entry)
    (work left : Nat) (ok : (Matrix.composeSingleLeftWork code y rows).run work = (.ok result,left)) :
    (Matrix.composeWork code y).run (2*code.rows*code.cols*y.cols) = (.ok result,0) := by
  by_cases shape : code.cols = y.rows
  · simp only [Matrix.composeSingleLeftWork,if_neg (not_not_intro shape),pure_bind] at ok
    obtain ⟨_,_,_,made⟩ := work_bind_success _ _ _ _ _ ok
    apply compose_at_cost _ _ _ shape
    simpa only [denseComposition,gather_left_entries _ _ admitted rows,bind,Except.bind]
      using (work_lift_success _ _ _ _ made).1
  · simp [Matrix.composeSingleLeftWork,shape] at ok
    cases ok

theorem Matrix.composeSingleRight_success (x code result : Matrix) (admitted : Matrix.Admitted x)
    (columns : SingleEntrySupport code.cols code.rows (fun col row => code.entry row col))
    (work left : Nat) (ok : (Matrix.composeSingleRightWork x code columns).run work = (.ok result,left)) :
    (Matrix.composeWork x code).run (2*x.rows*x.cols*code.cols) = (.ok result,0) := by
  by_cases shape : x.cols = code.rows
  · simp only [Matrix.composeSingleRightWork,if_neg (not_not_intro shape),pure_bind] at ok
    obtain ⟨_,_,_,made⟩ := work_bind_success _ _ _ _ _ ok
    apply compose_at_cost _ _ _ shape
    simpa only [denseComposition,gather_right_entries _ _ admitted columns shape,bind,Except.bind]
      using (work_lift_success _ _ _ _ made).1
  · simp [Matrix.composeSingleRightWork,shape] at ok
    cases ok

private theorem dense_entries_selected (x y output : Matrix)
    (rows : output.rows = x.rows) (cols : output.cols = y.cols) (admitted : Matrix.Admitted output)
    (cells : ∀ i ∈ List.range (x.rows*y.cols),
      (List.range x.cols).foldlM (fun sum k => dotStep sum (x.entry (i/y.cols) k,y.entry k (i%y.cols)))
        Scalar.zero = .ok (output.entry (i/y.cols) (i%y.cols))) :
    denseComposition x y = .ok output := by
  unfold denseComposition denseEntries
  rw [map_exact _ _ _ cells,← rows,← cols,reindex_entries _ admitted.2.1]
  rcases output with ⟨rows,cols,entries⟩
  simp [bind,Except.bind,Matrix.make,admitted.1,admitted.2.1]

/-- Left multiplication by a literal identity preserves every admitted coefficient. -/
theorem Matrix.compose_identity_left (code y : Matrix) (admitted : Matrix.Admitted y)
    (identity : Matrix.identity y.rows = .ok code) :
    (Matrix.composeWork code y).run (2*code.rows*code.cols*y.cols) = (.ok y,0) := by
  have same := identity_is_diagonal _ _ identity
  subst code
  apply compose_at_cost _ _ _ rfl
  apply dense_entries_selected (diagonalCode y.rows) y y rfl rfl admitted
  intro i member
  have dims := admitted.1
  simp only [matrixValid,Bool.and_eq_true,decide_eq_true_eq] at dims
  have row : i / y.cols < y.rows := (Nat.div_lt_iff_lt_mul dims.1.2).mpr (List.mem_range.mp member)
  apply dot_select y.rows (i / y.cols) row
  intro k inner
  change Scalar.mul ((diagonalCode y.rows).entry (i/y.cols) k) (y.entry k (i%y.cols)) = _
  rw [diagonal_entry y.rows _ _ row inner]
  by_cases selected : k = i/y.cols
  · subst k
    simp only [if_true]
    exact scalar_one_mul _ (matrix_entry_valid _ admitted _ _)
  · simp only [if_neg selected,if_neg (Ne.symm selected)]
    exact scalar_zero_mul _ (scalar_exponent_bound _ (matrix_entry_valid _ admitted _ _))

/-- Right multiplication by a literal identity preserves every admitted coefficient. -/
theorem Matrix.compose_identity_right (x code : Matrix) (admitted : Matrix.Admitted x)
    (identity : Matrix.identity x.cols = .ok code) :
    (Matrix.composeWork x code).run (2*x.rows*x.cols*code.cols) = (.ok x,0) := by
  have same := identity_is_diagonal _ _ identity
  subst code
  apply compose_at_cost _ _ _ rfl
  apply dense_entries_selected x (diagonalCode x.cols) x rfl rfl admitted
  intro i _
  have dims := admitted.1
  simp only [matrixValid,Bool.and_eq_true,decide_eq_true_eq] at dims
  have col : i % x.cols < x.cols := Nat.mod_lt _ dims.1.2
  apply dot_select x.cols (i % x.cols) col
  intro k inner
  change Scalar.mul (x.entry (i/x.cols) k) ((diagonalCode x.cols).entry k (i%x.cols)) = _
  rw [diagonal_entry x.cols _ _ inner col]
  by_cases selected : k = i%x.cols
  · subst k
    simp only [if_true]
    exact scalar_mul_one _ (matrix_entry_valid _ admitted _ _)
  · simp only [if_neg selected]
    exact scalar_mul_zero _ (scalar_exponent_bound _ (matrix_entry_valid _ admitted _ _))

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
