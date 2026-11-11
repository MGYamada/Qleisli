import QleisliKernel.Semantics.Exact

/-! Actual bounded arithmetic for the existing finite R8 coefficient domain.
No float equality, new coefficient domain or production evidence seal.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace QleisliKernel.Exact
open Semantics.Exact

inductive Error where
  | arithmeticCapacity | workLimit | dimension | entryCount | shapeMismatch
  deriving BEq, DecidableEq, Repr

def minNumerator : Int := -(2 ^ 127)
def maxNumerator : Int := 2 ^ 127 - 1
def maxExponent : Nat := 126
def maxInputExponent : Nat := 2 ^ 32 - 1
def maxDimension : Nat := 64

def numeratorValid (n : Int) : Bool := minNumerator ≤ n && n ≤ maxNumerator
def Coefficient.valid (x : Coefficient) : Bool :=
  numeratorValid x.numerator && x.exponent ≤ maxExponent &&
    (if x.numerator = 0 then x.exponent = 0 else x.exponent = 0 || x.numerator % 2 ≠ 0)

def Scalar.valid (x : Scalar) : Bool :=
  Coefficient.valid x.a && Coefficient.valid x.b && Coefficient.valid x.c && Coefficient.valid x.d

/-- At most 128 halvings; the loop is an explicit total structural recursor. -/
def normalize (fuel : Nat) : Coefficient → Coefficient :=
  Nat.rec (motive := fun _ => Coefficient → Coefficient) id
    (fun _ next x =>
      if x.numerator = 0 then .integer 0
      else if x.exponent = 0 || x.numerator % 2 ≠ 0 then x
      else next ⟨x.numerator / 2, x.exponent - 1⟩) fuel

def checkedInt (n : Int) : Except Error Int :=
  if numeratorValid n then .ok n else .error .arithmeticCapacity

def Coefficient.make (n : Int) (e : Nat) : Except Error Coefficient :=
  match checkedInt n with
  | .error error => .error error
  | .ok n =>
    if e > maxInputExponent then .error .arithmeticCapacity else
    let x := normalize 128 ⟨n, e⟩
    if Coefficient.valid x then .ok x else .error .arithmeticCapacity

def Coefficient.add (x y : Coefficient) : Except Error Coefficient := do
  if x.numerator = 0 then return y
  if y.numerator = 0 then return x
  let e := max x.exponent y.exponent
  let px ← checkedInt ((2 : Int) ^ (e - x.exponent))
  let py ← checkedInt ((2 : Int) ^ (e - y.exponent))
  let nx ← checkedInt (x.numerator * px)
  let ny ← checkedInt (y.numerator * py)
  let n ← checkedInt (nx + ny)
  Coefficient.make n e

def Coefficient.mul (x y : Coefficient) : Except Error Coefficient := do
  let n ← checkedInt (x.numerator * y.numerator)
  Coefficient.make n (x.exponent + y.exponent)

def Coefficient.neg (x : Coefficient) : Except Error Coefficient := do
  let n ← checkedInt (-x.numerator)
  return ⟨n, x.exponent⟩

def Scalar.make (a b c d : Int) (e : Nat) : Except Error Scalar := do
  return ⟨← Coefficient.make a e, ← Coefficient.make b e, ← Coefficient.make c e, ← Coefficient.make d e⟩

def Scalar.add (x y : Scalar) : Except Error Scalar := do
  return ⟨← Coefficient.add x.a y.a, ← Coefficient.add x.b y.b, ← Coefficient.add x.c y.c, ← Coefficient.add x.d y.d⟩

def Scalar.neg (x : Scalar) : Except Error Scalar := do
  return ⟨← Coefficient.neg x.a, ← Coefficient.neg x.b, ← Coefficient.neg x.c, ← Coefficient.neg x.d⟩

def Scalar.conjugate (x : Scalar) : Except Error Scalar := do
  return ⟨x.a, x.b, ← Coefficient.neg x.c, ← Coefficient.neg x.d⟩

def multiplyTerm (x y : Scalar) (acc : Scalar) (indices : Nat × Nat) :
    Except Error Scalar := do
  let (i, j) := indices
  let product ← Coefficient.mul (x.get i) (y.get j)
  let product ← if i % 2 = 1 && j % 2 = 1 then Coefficient.mul product (.integer 2) else pure product
  let product ← if i / 2 = 1 && j / 2 = 1 then Coefficient.neg product else pure product
  let k := Nat.xor i j
  let value ← Coefficient.add (acc.get k) product
  return acc.set k value

def coefficientPairs : List (Nat × Nat) :=
  (List.range 4).flatMap (fun i => (List.range 4).map (fun j => (i, j)))

def Scalar.mul (x y : Scalar) : Except Error Scalar :=
  coefficientPairs.foldlM (multiplyTerm x y) Scalar.zero

def Scalar.phase (k : Int) : Scalar :=
  let zero := Coefficient.integer 0
  let one := Coefficient.integer 1
  let negOne := Coefficient.integer (-1)
  let half : Coefficient := ⟨1, 1⟩
  let negHalf : Coefficient := ⟨-1, 1⟩
  match k % 8 with
  | 0 => ⟨one, zero, zero, zero⟩ | 1 => ⟨zero, half, zero, half⟩
  | 2 => ⟨zero, zero, one, zero⟩ | 3 => ⟨zero, negHalf, zero, half⟩
  | 4 => ⟨negOne, zero, zero, zero⟩ | 5 => ⟨zero, negHalf, zero, negHalf⟩
  | 6 => ⟨zero, zero, negOne, zero⟩ | _ => ⟨zero, half, zero, negHalf⟩

def matrixValid (rows cols : Nat) : Bool :=
  1 ≤ rows && rows ≤ maxDimension && 1 ≤ cols && cols ≤ maxDimension

def Matrix.make (rows cols : Nat) (entries : List Scalar) : Except Error Matrix :=
  if !matrixValid rows cols then .error .dimension
  else if entries.length ≠ rows * cols then .error .entryCount
  else .ok ⟨rows, cols, entries⟩

def Matrix.identity (dim : Nat) : Except Error Matrix :=
  if !matrixValid dim dim then .error .dimension else
  Matrix.make dim dim ((List.range (dim * dim)).map (fun i =>
    if i / dim = i % dim then Scalar.one else Scalar.zero))

/-- State is retained on arithmetic failure. Failed precharge changes no work. -/
abbrev WorkM := ExceptT Error (StateM Nat)

/-- Initial exact-work allowance shared by ordinary and source-qmatch decisions. -/
def _root_.QleisliKernel.exactWorkLimit : Nat := 20000000

def charge (amount : Nat) : WorkM Unit := fun remaining =>
  if amount > remaining then (.error .workLimit, remaining)
  else (.ok (), remaining - amount)

def liftExact {α : Type} (result : Except Error α) : WorkM α :=
  match result with | .ok x => pure x | .error e => throw e

private theorem coefficient_make_zero (e : Nat) (bounded : e ≤ maxInputExponent) :
    Coefficient.make 0 e = .ok (.integer 0) := by
  unfold Coefficient.make
  simp only [show checkedInt 0 = .ok 0 from rfl, if_neg (Nat.not_lt.mpr bounded)]
  rfl

private theorem coefficient_zero_mul (v : Coefficient) (bounded : v.exponent ≤ maxInputExponent) :
    Coefficient.mul (.integer 0) v = .ok (.integer 0) := by
  simpa only [Coefficient.mul,Semantics.Exact.Coefficient.integer,Int.zero_mul,Nat.zero_add,
    show checkedInt 0 = .ok 0 from rfl,bind,Except.bind] using coefficient_make_zero v.exponent bounded

private theorem coefficient_mul_zero (v : Coefficient) (bounded : v.exponent ≤ maxInputExponent) :
    Coefficient.mul v (.integer 0) = .ok (.integer 0) := by
  simpa only [Coefficient.mul,Semantics.Exact.Coefficient.integer,Int.mul_zero,Nat.add_zero,
    show checkedInt 0 = .ok 0 from rfl,bind,Except.bind] using coefficient_make_zero v.exponent bounded

private theorem coefficient_valid_parts (c : Coefficient) (valid : Coefficient.valid c = true) :
    (numeratorValid c.numerator = true ∧ c.exponent ≤ maxExponent) ∧
      (if c.numerator = 0 then decide (c.exponent = 0)
        else (decide (c.exponent = 0) || decide (c.numerator % 2 ≠ 0))) = true := by
  simpa only [Coefficient.valid,Bool.and_eq_true,decide_eq_true_eq] using valid

private theorem coefficient_canonical_zero (c : Coefficient) (valid : Coefficient.valid c = true)
    (zero : c.numerator = 0) : c = .integer 0 := by
  have exp : c.exponent = 0 := by
    simpa only [zero,if_true,decide_eq_true_eq] using (coefficient_valid_parts c valid).2
  cases c
  simp_all [Coefficient.integer]

private theorem coefficient_valid_exponent (c : Coefficient) (valid : Coefficient.valid c = true) :
    c.exponent ≤ maxInputExponent := by
  exact Nat.le_trans (coefficient_valid_parts c valid).1.2 (by decide)

private theorem normalize_canonical (c : Coefficient) (valid : Coefficient.valid c = true) :
    normalize 128 c = c := by
  by_cases zero : c.numerator = 0
  · rw [coefficient_canonical_zero c valid zero]
    rfl
  · have terminal : (decide (c.exponent = 0) || decide (c.numerator % 2 ≠ 0)) = true := by
      simpa only [zero,if_false] using (coefficient_valid_parts c valid).2
    change (if c.numerator = 0 then Coefficient.integer 0
      else if (decide (c.exponent = 0) || decide (c.numerator % 2 ≠ 0)) then c
      else normalize 127 ⟨c.numerator / 2,c.exponent - 1⟩) = c
    simp only [zero,if_false,terminal,if_true]

private theorem coefficient_make_canonical (c : Coefficient) (valid : Coefficient.valid c = true) :
    Coefficient.make c.numerator c.exponent = .ok c := by
  have n : numeratorValid c.numerator = true := (coefficient_valid_parts c valid).1.1
  have repr : (⟨c.numerator,c.exponent⟩ : Coefficient) = c := by cases c; rfl
  simp only [Coefficient.make,checkedInt,n,if_true,Nat.not_lt.mpr (coefficient_valid_exponent c valid),if_false,
    repr,normalize_canonical c valid,valid]

private theorem coefficient_one_mul (c : Coefficient) (valid : Coefficient.valid c = true) :
    Coefficient.mul (.integer 1) c = .ok c := by
  have n : numeratorValid c.numerator = true := (coefficient_valid_parts c valid).1.1
  simpa only [Coefficient.mul,Coefficient.integer,Int.one_mul,Nat.zero_add,
    checkedInt,n,if_true,bind,Except.bind] using coefficient_make_canonical c valid

private theorem coefficient_mul_one (c : Coefficient) (valid : Coefficient.valid c = true) :
    Coefficient.mul c (.integer 1) = .ok c := by
  have n : numeratorValid c.numerator = true := (coefficient_valid_parts c valid).1.1
  simpa only [Coefficient.mul,Coefficient.integer,Int.mul_one,Nat.add_zero,
    checkedInt,n,if_true,bind,Except.bind] using coefficient_make_canonical c valid

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

theorem scalar_add_zero (x : Scalar) (valid : Scalar.valid x = true) :
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

private theorem coefficient_zero_add (c : Coefficient) :
    Coefficient.add (.integer 0) c = .ok c := rfl

theorem scalar_mul_one (x : Scalar) (valid : Scalar.valid x = true) :
    Scalar.mul x Scalar.one = .ok x := by
  obtain ⟨⟨⟨a,b⟩,c⟩,d⟩ := by simpa only [Scalar.valid,Bool.and_eq_true] using valid
  cases x
  simp [Scalar.mul,coefficientPairs,show List.range 4 = [0,1,2,3] by decide,multiplyTerm,
    Scalar.one,Scalar.zero,Scalar.get,Scalar.set,bind,Except.bind,pure,Except.pure,
    coefficient_mul_zero _ (coefficient_valid_exponent _ a),coefficient_mul_zero _ (coefficient_valid_exponent _ b),coefficient_mul_zero _ (coefficient_valid_exponent _ c),coefficient_mul_zero _ (coefficient_valid_exponent _ d),
    coefficient_mul_one _ a,coefficient_mul_one _ b,coefficient_mul_one _ c,coefficient_mul_one _ d,
    coefficient_zero_add,coefficient_add_zero _ a,coefficient_add_zero _ b,coefficient_add_zero _ c,
    show Coefficient.mul (.integer 0) (.integer 2) = .ok (.integer 0) from rfl,
    show Coefficient.neg (.integer 0) = .ok (.integer 0) from rfl]

theorem scalar_one_mul (x : Scalar) (valid : Scalar.valid x = true) :
    Scalar.mul Scalar.one x = .ok x := by
  obtain ⟨⟨⟨a,b⟩,c⟩,d⟩ := by simpa only [Scalar.valid,Bool.and_eq_true] using valid
  cases x
  simp [Scalar.mul,coefficientPairs,show List.range 4 = [0,1,2,3] by decide,multiplyTerm,
    Scalar.one,Scalar.zero,Scalar.get,Scalar.set,bind,Except.bind,pure,Except.pure,
    coefficient_zero_mul _ (coefficient_valid_exponent _ a),coefficient_zero_mul _ (coefficient_valid_exponent _ b),coefficient_zero_mul _ (coefficient_valid_exponent _ c),coefficient_zero_mul _ (coefficient_valid_exponent _ d),
    coefficient_one_mul _ a,coefficient_one_mul _ b,coefficient_one_mul _ c,coefficient_one_mul _ d,
    coefficient_zero_add,coefficient_add_zero _ a,coefficient_add_zero _ b,coefficient_add_zero _ c,coefficient_add_zero _ d,
    show Coefficient.mul (.integer 0) (.integer 2) = .ok (.integer 0) from rfl,
    show Coefficient.neg (.integer 0) = .ok (.integer 0) from rfl]

theorem scalar_zero_add (value : Scalar) : Scalar.add Scalar.zero value = .ok value := by
  cases value
  rfl

private theorem get_zero (i : Nat) : Scalar.zero.get i = .integer 0 := by
  unfold Scalar.get
  split <;> rfl

private theorem set_zero (i : Nat) : Scalar.zero.set i (.integer 0) = Scalar.zero := by
  unfold Scalar.set
  split <;> rfl

private theorem zero_term {x y : Scalar} (i j : Nat)
    (product : Coefficient.mul (x.get i) (y.get j) = .ok (.integer 0)) :
    multiplyTerm x y Scalar.zero (i,j) = .ok Scalar.zero := by
  by_cases scale : (decide (i % 2 = 1) && decide (j % 2 = 1)) = true
  all_goals
    by_cases sign : (decide (i / 2 = 1) && decide (j / 2 = 1)) = true
    all_goals
      simp [multiplyTerm,product,scale,sign,bind,Except.bind,pure,Except.pure,
        show Coefficient.mul (.integer 0) (.integer 2) = .ok (.integer 0) from rfl,
        show Coefficient.neg (.integer 0) = .ok (.integer 0) from rfl,
        get_zero,show Coefficient.add (.integer 0) (.integer 0) = .ok (.integer 0) from rfl,set_zero]

private theorem fold_zero (x y : Scalar) (steps : List (Nat × Nat))
    (term : ∀ i j, multiplyTerm x y Scalar.zero (i,j) = .ok Scalar.zero) :
    steps.foldlM (multiplyTerm x y) Scalar.zero = .ok Scalar.zero := by
  induction steps with
  | nil => rfl
  | cons step rest ih =>
    rcases step with ⟨i,j⟩
    simp only [List.foldlM_cons,term,bind,Except.bind,ih]

theorem scalar_zero_mul (v : Scalar) (bounded : ∀ i, (v.get i).exponent ≤ maxInputExponent) :
    Scalar.mul Scalar.zero v = .ok Scalar.zero := by
  apply fold_zero
  intro i j
  apply zero_term
  rw [get_zero]
  exact coefficient_zero_mul (v.get j) (bounded j)

theorem scalar_mul_zero (v : Scalar) (bounded : ∀ i, (v.get i).exponent ≤ maxInputExponent) :
    Scalar.mul v Scalar.zero = .ok Scalar.zero := by
  apply fold_zero
  intro i j
  apply zero_term
  rw [get_zero]
  exact coefficient_mul_zero (v.get i) (bounded i)

private def smallExponents (v : Scalar) : Bool :=
  v.a.exponent ≤ maxInputExponent && v.b.exponent ≤ maxInputExponent &&
    v.c.exponent ≤ maxInputExponent && v.d.exponent ≤ maxInputExponent

private theorem smallExponents_bound (v : Scalar) (safe : smallExponents v = true) :
    ∀ i, (v.get i).exponent ≤ maxInputExponent := by
  simp only [smallExponents,Bool.and_eq_true,decide_eq_true_eq] at safe
  intro i
  unfold Scalar.get
  split
  · exact safe.1.1.1
  · exact safe.1.1.2
  · exact safe.1.2
  · exact safe.2

/-- Matrix coefficients are often zero. Check the other coefficient's
exponents before omitting the zero products, since raw scalars can be malformed. -/
def mulZeroFast (a b : Scalar) : Except Error Scalar :=
  if a == Scalar.zero && smallExponents b then .ok Scalar.zero
  else if b == Scalar.zero && smallExponents a then .ok Scalar.zero
  else Scalar.mul a b

theorem mulZeroFast_equiv (a b : Scalar) : mulZeroFast a b = Scalar.mul a b := by
  unfold mulZeroFast
  split
  · rename_i h
    obtain ⟨zero,safe⟩ := Bool.and_eq_true_iff.mp h
    rw [beq_iff_eq.mp zero]
    exact (scalar_zero_mul b (smallExponents_bound b safe)).symm
  · split
    · rename_i h
      obtain ⟨zero,safe⟩ := Bool.and_eq_true_iff.mp h
      rw [beq_iff_eq.mp zero]
      exact (scalar_mul_zero a (smallExponents_bound a safe)).symm
    · rfl

def Matrix.composeWork (x y : Matrix) : WorkM Matrix := do
  if x.cols ≠ y.rows then throw .shapeMismatch
  charge (2 * x.rows * x.cols * y.cols)
  let left := x.entries.toArray
  let right := y.entries.toArray
  let entries ← (List.range (x.rows * y.cols)).mapM fun i => do
    let row := i / y.cols
    let col := i % y.cols
    let sum ← (List.range x.cols).foldlM (fun sum k => do
      let a := left[row * x.cols + k]?.getD Scalar.zero
      let b := right[k * y.cols + col]?.getD Scalar.zero
      let product ← liftExact (mulZeroFast a b)
      liftExact (Scalar.add sum product)) Scalar.zero
    pure sum
  liftExact (Matrix.make x.rows y.cols entries)

/-- The executable table lookup preserves the same coefficients, term order,
arithmetic failures and remaining work as the original list traversal. -/
theorem Matrix.composeWork_list (x y : Matrix) :
    composeWork x y = (do
      if x.cols ≠ y.rows then throw .shapeMismatch
      charge (2 * x.rows * x.cols * y.cols)
      let entries ← (List.range (x.rows * y.cols)).mapM fun i => do
        let sum ← (List.range x.cols).foldlM (fun sum k => do
          let product ← liftExact (Scalar.mul (x.entry (i / y.cols) k) (y.entry k (i % y.cols)))
          liftExact (Scalar.add sum product)) Scalar.zero
        pure sum
      liftExact (Matrix.make x.rows y.cols entries)) := by
  simp only [composeWork,mulZeroFast_equiv,List.getElem?_toArray,Semantics.Exact.Matrix.entry]

def Matrix.compose (x y : Matrix) (work : Nat) : Except Error Matrix × Nat :=
  (Matrix.composeWork x y).run work

def Matrix.tensorWork (x y : Matrix) : WorkM Matrix := do
  let rows := x.rows * y.rows
  let cols := x.cols * y.cols
  if !matrixValid rows cols then throw .dimension
  charge (rows * cols)
  let entries ← (List.range (rows * cols)).mapM fun i =>
    let row := i / cols
    let col := i % cols
    liftExact (Scalar.mul (x.entry (row % x.rows) (col % x.cols))
      (y.entry (row / x.rows) (col / x.cols)))
  liftExact (Matrix.make rows cols entries)

def Matrix.tensor (x y : Matrix) (work : Nat) : Except Error Matrix × Nat :=
  (Matrix.tensorWork x y).run work

def Matrix.adjointWork (x : Matrix) : WorkM Matrix := do
  charge (x.rows * x.cols)
  let entries ← (List.range (x.rows * x.cols)).mapM fun i =>
    liftExact (Scalar.conjugate (x.entry (i % x.rows) (i / x.rows)))
  liftExact (Matrix.make x.cols x.rows entries)

def Matrix.adjoint (x : Matrix) (work : Nat) : Except Error Matrix × Nat :=
  (Matrix.adjointWork x).run work

def Matrix.isometryWork (x : Matrix) : WorkM Bool := do
  if x.rows < x.cols then return false
  let adjoint ← (Matrix.adjointWork x)
  let product ← Matrix.composeWork adjoint x
  let identity ← liftExact (Matrix.identity x.cols)
  return product == identity

def Matrix.isometry (x : Matrix) (work : Nat) : Except Error Bool × Nat :=
  (Matrix.isometryWork x).run work

theorem checkedInt_value (n value : Int) (ok : checkedInt n = .ok value) : value = n := by
  unfold checkedInt at ok
  split at ok <;> simp_all

theorem make_valid (n : Int) (e : Nat) (x : Coefficient) (ok : Coefficient.make n e = .ok x) :
    Coefficient.valid x = true := by
  unfold Coefficient.make at ok
  split at ok
  · cases ok
  · split at ok
    · cases ok
    · dsimp only at ok
      split at ok <;> simp_all

theorem charge_success (amount remaining : Nat) (enough : amount ≤ remaining) :
    (charge amount).run remaining = (.ok (), remaining - amount) := by
  change (if remaining < amount then (Except.error Error.workLimit, remaining)
    else (Except.ok (), remaining - amount) : Except Error Unit × Nat) = _
  rw [if_neg (Nat.not_lt.mpr enough)]

theorem charge_failure (amount remaining : Nat) (short : remaining < amount) :
    (charge amount).run remaining = (.error .workLimit, remaining) := by
  change (if remaining < amount then (Except.error Error.workLimit, remaining)
    else (Except.ok (), remaining - amount) : Except Error Unit × Nat) = _
  rw [if_pos short]

/-- Successful binding exposes the actual intermediate value. -/
theorem bind_success {α β : Type} (first : Except Error α) (next : α → Except Error β)
    (z : β) (ok : (first >>= next) = .ok z) :
    ∃ value, first = .ok value ∧ next value = .ok z := by
  cases first with
  | error e => simp [bind, Except.bind] at ok
  | ok value => exact ⟨value, rfl, ok⟩

theorem checkedInt_valid (n value : Int) (ok : checkedInt n = .ok value) :
    numeratorValid value = true := by
  unfold checkedInt at ok
  split at ok <;> simp_all

theorem coefficient_mul_valid (x y z : Coefficient)
    (ok : Coefficient.mul x y = .ok z) : Coefficient.valid z = true := by
  obtain ⟨n, _, result⟩ := bind_success _ _ z ok
  exact make_valid n (x.exponent + y.exponent) z result

theorem coefficient_add_valid (x y z : Coefficient)
    (vx : Coefficient.valid x = true) (vy : Coefficient.valid y = true)
    (ok : Coefficient.add x y = .ok z) : Coefficient.valid z = true := by
  by_cases hx : x.numerator = 0
  · simp [Coefficient.add, hx, pure, Except.pure] at ok
    simpa [← ok] using vy
  · by_cases hy : y.numerator = 0
    · simp [Coefficient.add, hx, hy, pure, Except.pure, bind, Except.bind] at ok
      simpa [← ok] using vx
    · simp [Coefficient.add, hx, hy] at ok
      obtain ⟨_, _, h⟩ := bind_success _ _ z ok
      obtain ⟨_, _, h⟩ := bind_success _ _ z h
      obtain ⟨_, _, h⟩ := bind_success _ _ z h
      obtain ⟨_, _, h⟩ := bind_success _ _ z h
      obtain ⟨n, _, h⟩ := bind_success _ _ z h
      exact make_valid n (max x.exponent y.exponent) z h

theorem coefficient_neg_valid (x z : Coefficient) (vx : Coefficient.valid x = true)
    (ok : Coefficient.neg x = .ok z) : Coefficient.valid z = true := by
  obtain ⟨n, checked, result⟩ := bind_success _ _ z ok
  have hn := checkedInt_value (-x.numerator) n checked
  have range := checkedInt_valid _ _ checked
  simp only [pure, Except.pure, Except.ok.injEq] at result
  subst z
  simp only [Coefficient.valid, Bool.and_eq_true, decide_eq_true_eq] at vx ⊢
  refine ⟨⟨range, vx.1.2⟩, ?_⟩
  by_cases hzero : x.numerator = 0
  · simpa [hn, hzero] using vx.2
  · have nz : n ≠ 0 := by omega
    simp only [hzero, nz, ↓reduceIte, Bool.or_eq_true, decide_eq_true_eq] at vx ⊢
    rcases vx.2 with he | ho
    · exact Or.inl he
    · right; omega

theorem scalar_get_valid (x : Scalar) (vx : Scalar.valid x = true) (i : Nat) :
    Coefficient.valid (x.get i) = true := by
  simp only [Scalar.valid, Bool.and_eq_true] at vx
  rcases i with _ | i
  · exact vx.1.1.1
  rcases i with _ | i
  · exact vx.1.1.2
  rcases i with _ | i
  · exact vx.1.2
  · exact vx.2

theorem scalar_set_valid (x : Scalar) (vx : Scalar.valid x = true) (i : Nat)
    (value : Coefficient) (vv : Coefficient.valid value = true) :
    Scalar.valid (x.set i value) = true := by
  simp only [Scalar.valid, Bool.and_eq_true] at vx
  rcases i with _ | i
  · simp [Scalar.set, Scalar.valid, vv, vx]
  rcases i with _ | i
  · simp [Scalar.set, Scalar.valid, vv, vx]
  rcases i with _ | i
  · simp [Scalar.set, Scalar.valid, vv, vx]
  · simp [Scalar.set, Scalar.valid, vv, vx]

theorem scalar_add_valid (x y z : Scalar) (vx : Scalar.valid x = true)
    (vy : Scalar.valid y = true) (ok : Scalar.add x y = .ok z) : Scalar.valid z = true := by
  obtain ⟨a, ha, h⟩ := bind_success _ _ z ok
  obtain ⟨b, hb, h⟩ := bind_success _ _ z h
  obtain ⟨c, hc, h⟩ := bind_success _ _ z h
  obtain ⟨d, hd, h⟩ := bind_success _ _ z h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst z
  simp only [Scalar.valid, Bool.and_eq_true] at vx vy ⊢
  exact ⟨⟨⟨coefficient_add_valid _ _ _ vx.1.1.1 vy.1.1.1 ha,
    coefficient_add_valid _ _ _ vx.1.1.2 vy.1.1.2 hb⟩,
    coefficient_add_valid _ _ _ vx.1.2 vy.1.2 hc⟩,
    coefficient_add_valid _ _ _ vx.2 vy.2 hd⟩

theorem scalar_neg_valid (x z : Scalar) (vx : Scalar.valid x = true)
    (ok : Scalar.neg x = .ok z) : Scalar.valid z = true := by
  obtain ⟨a, ha, h⟩ := bind_success _ _ z ok
  obtain ⟨b, hb, h⟩ := bind_success _ _ z h
  obtain ⟨c, hc, h⟩ := bind_success _ _ z h
  obtain ⟨d, hd, h⟩ := bind_success _ _ z h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst z
  simp only [Scalar.valid, Bool.and_eq_true] at vx ⊢
  exact ⟨⟨⟨coefficient_neg_valid _ _ vx.1.1.1 ha, coefficient_neg_valid _ _ vx.1.1.2 hb⟩,
    coefficient_neg_valid _ _ vx.1.2 hc⟩, coefficient_neg_valid _ _ vx.2 hd⟩

theorem scalar_conjugate_valid (x z : Scalar) (vx : Scalar.valid x = true)
    (ok : Scalar.conjugate x = .ok z) : Scalar.valid z = true := by
  obtain ⟨c, hc, h⟩ := bind_success _ _ z ok
  obtain ⟨d, hd, h⟩ := bind_success _ _ z h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst z
  simp only [Scalar.valid, Bool.and_eq_true] at vx ⊢
  exact ⟨⟨vx.1.1, coefficient_neg_valid _ _ vx.1.2 hc⟩,
    coefficient_neg_valid _ _ vx.2 hd⟩

theorem multiplyTerm_valid (x y acc z : Scalar) (va : Scalar.valid acc = true)
    (indices : Nat × Nat) (ok : multiplyTerm x y acc indices = .ok z) : Scalar.valid z = true := by
  simp only [multiplyTerm, bind, Except.bind, pure, Except.pure] at ok
  split at ok
  · cases ok
  · rename_i product hp
    have vp := coefficient_mul_valid _ _ _ hp
    have finish (signed : Coefficient) (vs : Coefficient.valid signed = true)
        (h : (do let value ← Coefficient.add (acc.get (indices.fst.xor indices.snd)) signed
                 pure (acc.set (indices.fst.xor indices.snd) value)) = .ok z) :
        Scalar.valid z = true := by
      obtain ⟨value, hv, h⟩ := bind_success _ _ z h
      have vv := coefficient_add_valid _ _ _ (scalar_get_valid acc va _) vs hv
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst z
      exact scalar_set_valid acc va _ value vv
    have sign (scaled : Coefficient) (vs : Coefficient.valid scaled = true)
        (h : (if indices.fst / 2 = 1 && indices.snd / 2 = 1 then
                (do let signed ← Coefficient.neg scaled
                    let value ← Coefficient.add (acc.get (indices.fst.xor indices.snd)) signed
                    pure (acc.set (indices.fst.xor indices.snd) value))
              else (do let value ← Coefficient.add (acc.get (indices.fst.xor indices.snd)) scaled
                       pure (acc.set (indices.fst.xor indices.snd) value))) = .ok z) :
        Scalar.valid z = true := by
      split at h
      · obtain ⟨signed, hn, h⟩ := bind_success _ _ z h
        exact finish signed (coefficient_neg_valid _ _ vs hn) h
      · exact finish scaled vs h
    split at ok
    · obtain ⟨scaled, hs, h⟩ := bind_success _ _ z ok
      exact sign scaled (coefficient_mul_valid _ _ _ hs) h
    · exact sign product vp ok

theorem fold_valid {α β : Type} (step : β → α → Except Error β) (p : β → Prop)
    (preserve : ∀ b a z, p b → step b a = .ok z → p z)
    (xs : List α) (initial z : β) (vi : p initial)
    (ok : xs.foldlM step initial = .ok z) : p z := by
  induction xs generalizing initial with
  | nil =>
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at ok
    simpa [← ok] using vi
  | cons a xs ih =>
    simp only [List.foldlM_cons] at ok
    obtain ⟨next, hn, h⟩ := bind_success _ _ z ok
    exact ih next (preserve initial a next vi hn) h

theorem scalar_mul_valid (x y z : Scalar) (ok : Scalar.mul x y = .ok z) :
    Scalar.valid z = true := by
  exact fold_valid (multiplyTerm x y) (fun s => Scalar.valid s = true)
    (fun acc indices z va h => multiplyTerm_valid x y acc z va indices h)
    coefficientPairs Scalar.zero z (by decide) ok

/-- Every outcome, including an error, leaves no more work than it received. -/
def Spends {α : Type} (f : WorkM α) : Prop := ∀ work, (f.run work).2 ≤ work

theorem spends_pure {α : Type} (value : α) : Spends (pure value) := by
  intro work
  exact Nat.le_refl work

theorem spends_lift {α : Type} (result : Except Error α) : Spends (liftExact result) := by
  cases result <;> intro work <;> exact Nat.le_refl work

theorem spends_throw {α : Type} (error : Error) : Spends (throw error : WorkM α) := by
  intro work
  exact Nat.le_refl work

theorem spends_charge (amount : Nat) : Spends (charge amount) := by
  intro work
  change (if work < amount then (Except.error Error.workLimit, work)
    else (Except.ok (), work - amount) : Except Error Unit × Nat).2 ≤ work
  split
  · exact Nat.le_refl work
  · exact Nat.sub_le work amount

theorem spends_bind {α β : Type} (first : WorkM α) (next : α → WorkM β)
    (hf : Spends first) (hn : ∀ value, Spends (next value)) : Spends (first >>= next) := by
  intro work
  have h := hf work
  change (first work).2 ≤ work at h
  simp only [ExceptT.run, bind, ExceptT.bind, ExceptT.mk, StateT.bind]
  cases he : first work with
  | mk result left =>
    simp only [he] at h ⊢
    cases result with
    | error e => simpa [ExceptT.bindCont, pure, StateT.pure] using h
    | ok value => simpa [ExceptT.bindCont] using Nat.le_trans (hn value left) h

theorem spends_fold {α β : Type} (step : β → α → WorkM β)
    (hs : ∀ b a, Spends (step b a)) (xs : List α) (initial : β) :
    Spends (xs.foldlM step initial) := by
  induction xs generalizing initial with
  | nil => exact spends_pure initial
  | cons a xs ih =>
    simp only [List.foldlM_cons]
    exact spends_bind _ _ (hs initial a) (fun next => ih next)

theorem spends_map {α β : Type} (step : α → WorkM β)
    (hs : ∀ a, Spends (step a)) (xs : List α) : Spends (xs.mapM step) := by
  induction xs with
  | nil => exact spends_pure []
  | cons a xs ih =>
    simp only [List.mapM_cons]
    exact spends_bind _ _ (hs a) (fun value => spends_bind _ _ ih (fun rest => spends_pure (value :: rest)))

theorem compose_spends (x y : Matrix) : Spends (Matrix.composeWork x y) := by
  unfold Matrix.composeWork
  split
  · exact spends_throw _
  · apply spends_bind _ _ (spends_pure ())
    intro _
    apply spends_bind _ _ (spends_charge _)
    intro _
    apply spends_bind _ _
      (spends_map _ (fun i => spends_bind _ _
        (spends_fold _ (fun sum k => spends_bind _ _ (spends_lift _) (fun product => spends_lift _)) _ _)
        (fun sum => spends_pure sum)) _)
    intro entries
    exact spends_lift _

theorem tensor_spends (x y : Matrix) : Spends (Matrix.tensorWork x y) := by
  unfold Matrix.tensorWork
  dsimp only
  split
  · exact spends_throw _
  · apply spends_bind _ _ (spends_pure ())
    intro _
    apply spends_bind _ _ (spends_charge _)
    intro _
    exact spends_bind _ _ (spends_map _ (fun i => spends_lift _) _) (fun entries => spends_lift _)

theorem adjoint_spends (x : Matrix) : Spends (Matrix.adjointWork x) := by
  unfold Matrix.adjointWork
  exact spends_bind _ _ (spends_charge _)
    (fun _ => spends_bind _ _ (spends_map _ (fun i => spends_lift _) _) (fun entries => spends_lift _))

theorem isometry_spends (x : Matrix) : Spends (Matrix.isometryWork x) := by
  unfold Matrix.isometryWork
  split
  · exact spends_pure false
  · apply spends_bind _ _ (spends_pure ())
    intro _
    exact spends_bind _ _ (adjoint_spends x) (fun adjoint =>
      spends_bind _ _ (compose_spends adjoint x) (fun product =>
      spends_bind _ _ (spends_lift _) (fun identity => spends_pure (product == identity))))

theorem scalar_make_valid (a b c d : Int) (e : Nat) (z : Scalar)
    (ok : Scalar.make a b c d e = .ok z) : Scalar.valid z = true := by
  obtain ⟨va, ha, h⟩ := bind_success _ _ z ok
  obtain ⟨vb, hb, h⟩ := bind_success _ _ z h
  obtain ⟨vc, hc, h⟩ := bind_success _ _ z h
  obtain ⟨vd, hd, h⟩ := bind_success _ _ z h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst z
  simp only [Scalar.valid, Bool.and_eq_true]
  exact ⟨⟨⟨make_valid _ _ _ ha, make_valid _ _ _ hb⟩, make_valid _ _ _ hc⟩,
    make_valid _ _ _ hd⟩

theorem scalar_phase_valid (k : Int) : Scalar.valid (Scalar.phase k) = true := by
  unfold Scalar.phase
  split <;> decide

/-- Successful precharge fixes the exact starting work for all later outcomes. -/
theorem charged_run {α : Type} (amount work : Nat) (next : Unit → WorkM α)
    (enough : amount ≤ work) :
    (charge amount >>= next).run work = (next ()).run (work - amount) := by
  simp only [ExceptT.run, bind, ExceptT.bind, ExceptT.mk, StateT.bind]
  rw [show charge amount work = (.ok (), work - amount) from charge_success amount work enough]
  rfl

theorem charged_failure {α : Type} (amount work : Nat) (next : Unit → WorkM α)
    (short : work < amount) :
    (charge amount >>= next).run work = (.error .workLimit, work) := by
  simp only [ExceptT.run, bind, ExceptT.bind, ExceptT.mk, StateT.bind]
  rw [show charge amount work = (.error .workLimit, work) from charge_failure amount work short]
  rfl

theorem charged_remaining {α : Type} (amount work : Nat) (next : Unit → WorkM α)
    (enough : amount ≤ work) (hn : ∀ value, Spends (next value)) :
    ((charge amount >>= next).run work).2 ≤ work - amount := by
  rw [charged_run amount work next enough]
  exact hn () (work - amount)

end QleisliKernel.Exact
