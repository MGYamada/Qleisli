import QleisliKernel.Semantics.Exact

/-! Actual bounded arithmetic for the existing finite R8 coefficient domain.
No float equality, new coefficient domain or production evidence seal.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/

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

def charge (amount : Nat) : WorkM Unit := fun remaining =>
  if amount > remaining then (.error .workLimit, remaining)
  else (.ok (), remaining - amount)

def liftExact {α : Type} (result : Except Error α) : WorkM α :=
  match result with | .ok x => pure x | .error e => throw e

def Matrix.composeWork (x y : Matrix) : WorkM Matrix := do
  if x.cols ≠ y.rows then throw .shapeMismatch
  charge (2 * x.rows * x.cols * y.cols)
  let entries ← (List.range (x.rows * y.cols)).mapM fun i => do
    let sum ← (List.range x.cols).foldlM (fun sum k => do
      let product ← liftExact (Scalar.mul (x.entry (i / y.cols) k) (y.entry k (i % y.cols)))
      liftExact (Scalar.add sum product)) Scalar.zero
    pure sum
  liftExact (Matrix.make x.rows y.cols entries)

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
