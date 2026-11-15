import QleisliKernel.FiniteRestriction.BitUpdate
import QleisliKernel.Semantics.RawTrace

/-! Phase-free controlled XOR on one actual ordered target wire.
The check visits literal circuit steps and their controls without enumerating
input labels. Source predicate and owner correspondence are separate premises.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.StructuralXor
open QleisliKernel Semantics.Finite Semantics.Exact
open _root_.QleisliKernel.FiniteRestriction.BitUpdate (bit_lt bit_write write)

def toggle (target : Nat) (controls : List Control) : Step :=
  {Semantics.RawTrace.gate .x target with controls}

def targetUpdate (target label : Nat) (flip : Bool) : Nat :=
  if flip then write label target (1 - bit label target) else label

private theorem gather_single (label target : Nat) : gather label [target] = bit label target := by
  simp [gather, List.zipIdx_cons, List.zipIdx_nil]

private theorem scatter_single (label target value : Nat) (small : value < 2) :
    scatter label [target] value = write label target value := by
  simp [scatter, write, List.zipIdx_cons, List.zipIdx_nil, bit, Nat.mod_eq_of_lt small]

theorem toggle_contribution (target : Nat) (controls : List Control) (label : Nat)
    (value : Scalar) (valid : Exact.Scalar.valid value = true) (nonzero : value ≠ Scalar.zero) :
    Finite.contributions [] (toggle target controls) label value =
      .ok [(targetUpdate target label (enabled controls label),value)] := by
  have bitSmall := bit_lt label target
  have newSmall : 1 - bit label target < 2 := by omega
  have zeroCheck : (value == Scalar.zero) = false := by simpa using nonzero
  have mulOne := Exact.scalar_mul_one value valid
  have phaseZero (phase : Nat) (zero : phase = 0) : Exact.Scalar.phase (phase : Int) = Scalar.one := by
    subst phase
    decide
  have bits : bit label target = 0 ∨ bit label target = 1 := by omega
  have permutation : [1,0][bit label target]? = some (1 - bit label target) := by
    rcases bits with zero | one
    · rw [zero]
      rfl
    · rw [one]
      rfl
  have phases : [0,0][bit label target]? = some 0 := by
    rcases bits with zero | one
    · rw [zero]
      rfl
    · rw [one]
      rfl
  cases control : enabled controls label <;>
    simp only [Finite.contributions, zeroCheck, toggle, Semantics.RawTrace.gate, control,
      Bool.not_true, Bool.not_false, Bool.false_eq_true, if_false, if_true, targetUpdate,
      gather_single, permutation, phases, Finite.readOption, phaseZero 0 rfl, mulOne, Finite.arithmetic,
      bind, Except.bind, Except.mapError, pure, Except.pure, scatter_single _ _ _ newSmall]

theorem enabled_update (controls : List Control) (target label : Nat) (flip : Bool)
    (distinct : ∀ control ∈ controls, control.index ≠ target) :
    enabled controls (targetUpdate target label flip) = enabled controls label := by
  cases flip with
  | false => rfl
  | true =>
    induction controls with
    | nil => rfl
    | cons control rest ih =>
      have different := distinct control List.mem_cons_self
      have untouched := ih (fun other member => distinct other (List.mem_cons_of_mem _ member))
      have replacement : 1 - bit label target < 2 := by omega
      have same : bit (targetUpdate target label true) control.index = bit label control.index := by
        simp [targetUpdate, bit_write _ _ _ _ replacement, different]
      simp only [enabled, List.all_cons] at untouched ⊢
      rw [same, untouched]

private theorem targetUpdate_bit (target label query : Nat) (flip : Bool) :
    bit (targetUpdate target label flip) query =
      if flip && decide (query = target) then 1 - bit label query else bit label query := by
  cases flip with
  | false => rfl
  | true =>
    have replacement : 1 - bit label target < 2 := by omega
    by_cases same : query = target
    · subst query
      simp [targetUpdate, bit_write _ _ _ _ replacement]
    · simp [targetUpdate, bit_write _ _ _ _ replacement, same]

theorem targetUpdate_preserves (target label query : Nat) (flip : Bool) (other : query ≠ target) :
    bit (targetUpdate target label flip) query = bit label query := by
  simp [targetUpdate_bit, other]

theorem targetUpdate_flips (target label : Nat) (flip : Bool) :
    bit (targetUpdate target label flip) target = (Bool.xor (bit label target == 1) flip).toNat := by
  have small := bit_lt label target
  have cases : bit label target = 0 ∨ bit label target = 1 := by omega
  rw [targetUpdate_bit]
  rcases cases with zero | one
  · cases flip <;> simp [zero]
  · cases flip <;> simp [one]

/-- Two input-preserving updates compose by XOR on the actual target bit. -/
theorem targetUpdate_xor (target label : Nat) (first second : Bool) :
    targetUpdate target (targetUpdate target label first) second =
      targetUpdate target label (Bool.xor first second) := by
  apply Nat.eq_of_testBit_eq
  intro axis
  have small := bit_lt label axis
  have same : bit (targetUpdate target (targetUpdate target label first) second) axis =
      bit (targetUpdate target label (Bool.xor first second)) axis := by
    simp only [targetUpdate_bit]
    by_cases same : axis = target
    · subst axis
      cases first <;> cases second <;> simp <;> omega
    · simp [same]
  simp only [bit, ← Nat.toNat_testBit] at same
  cases left : (targetUpdate target (targetUpdate target label first) second).testBit axis <;>
    cases right : (targetUpdate target label (Bool.xor first second)).testBit axis <;>
      simp_all

/-- Each clause contributes a controlled flip. Their parity is the logical
Boolean result. A clause may test either polarity of an input bit. -/
def predicate (clauses : List (List Control)) (label : Nat) : Bool :=
  clauses.foldl (fun parity controls => Bool.xor parity (enabled controls label)) false

private def run (target : Nat) (clauses : List (List Control)) (label : Nat) : Nat :=
  clauses.foldl (fun row controls => targetUpdate target row (enabled controls row)) label

private theorem run_from (target label : Nat) (clauses : List (List Control)) (parity : Bool)
    (distinct : ∀ controls ∈ clauses, ∀ control ∈ controls, control.index ≠ target) :
    run target clauses (targetUpdate target label parity) = targetUpdate target label
      (clauses.foldl (fun total controls => Bool.xor total (enabled controls label)) parity) := by
  induction clauses generalizing parity with
  | nil => rfl
  | cons controls rest ih =>
    simp only [run, List.foldl_cons]
    rw [enabled_update _ _ _ _ (distinct controls List.mem_cons_self), targetUpdate_xor]
    exact ih _ (fun other member => distinct other (List.mem_cons_of_mem _ member))

theorem run_predicate (target label : Nat) (clauses : List (List Control))
    (distinct : ∀ controls ∈ clauses, ∀ control ∈ controls, control.index ≠ target) :
    run target clauses label = targetUpdate target label (predicate clauses label) :=
  run_from target label clauses false distinct

private theorem predicate_update (target label : Nat) (clauses : List (List Control)) (flip : Bool)
    (distinct : ∀ controls ∈ clauses, ∀ control ∈ controls, control.index ≠ target) :
    predicate clauses (targetUpdate target label flip) = predicate clauses label := by
  have fold (parity : Bool) :
      clauses.foldl (fun total controls => Bool.xor total (enabled controls (targetUpdate target label flip))) parity =
        clauses.foldl (fun total controls => Bool.xor total (enabled controls label)) parity := by
    induction clauses generalizing parity with
    | nil => rfl
    | cons controls rest ih =>
      simp only [List.foldl_cons]
      rw [enabled_update _ _ _ _ (distinct controls List.mem_cons_self)]
      exact ih (fun other member => distinct other (List.mem_cons_of_mem _ member)) _
  exact fold false

structure Checked (target : Nat) (clauses : List (List Control)) (steps : List Step) : Type where
  literal : steps = clauses.map (toggle target)
  disjoint : ∀ controls ∈ clauses, ∀ control ∈ controls, control.index < target

private theorem Checked.distinct {target clauses steps} (checked : Checked target clauses steps) :
    ∀ controls ∈ clauses, ∀ control ∈ controls, control.index ≠ target :=
  fun controls member control present => Nat.ne_of_lt (checked.disjoint controls member control present)

/-- Applying the same checked embedding twice restores the complete input. -/
theorem Checked.involution {target clauses steps} (checked : Checked target clauses steps) (label : Nat) :
    let update := fun row => targetUpdate target row (predicate clauses row)
    update (update label) = label := by
  dsimp only
  rw [predicate_update _ _ _ _ checked.distinct, targetUpdate_xor]
  cases predicate clauses label <;> rfl

/-- Charge the fields of the clauses and actual circuit, independent of the
cardinality of the data carrier. Count invalidly shaped proposed steps too. -/
def comparisonCharge (clauses : List (List Control)) (steps : List Step) : Nat :=
  let clauseFields := (clauses.map fun controls => controls.length + 1).sum
  let stepFields := (steps.map fun step => step.controls.length + 1 + match step.action with
    | .monomial axes permutation phases => axes.length + permutation.length + phases.length
    | .hadamard _ => 1
    | .contract axes _ _ => axes.length + 2).sum
  8 * (clauseFields + stepFields + 1)

/-- Bind a nominated Boolean representation to literal circuit actions. The
caller separately establishes where the clauses came from and which owner
actually occupies each coordinate. The result carries no handle. -/
def check (target : Nat) (clauses : List (List Control)) (steps : List Step) :
    Finite.WorkM (Checked target clauses steps) := do
  Finite.exactWork (Exact.charge (comparisonCharge clauses steps))
  if literal : steps = clauses.map (toggle target) then
    if inside : (clauses.all fun controls => controls.all (·.index < target)) = true then
      return ⟨literal, fun controls member control present =>
        of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp inside controls member) control present)⟩
    else throw .request
  else throw .equation

/-- A short budget fails at the field precharge, retaining the work count. -/
theorem check_work_limit (target : Nat) (clauses : List (List Control)) (steps : List Step)
    (work : Nat) (short : work < comparisonCharge clauses steps) :
    (check target clauses steps).run work = (.error (.arithmetic .workLimit),work) := by
  unfold check
  rw [Finite.bind_run]
  have unpaid :
      (Finite.exactWork (Exact.charge (comparisonCharge clauses steps))).run work =
        (.error (.arithmetic .workLimit),work) := by
    let result := (Exact.charge (comparisonCharge clauses steps)).run work
    change (Finite.arithmetic result.1,result.2) = _
    dsimp only [result]
    rw [Exact.charge_failure _ _ short]
    rfl
  rw [unpaid]

/-- The actual successful checker consumes exactly a linear charge in literal
flips and their controls. No carrier cardinality enters the equation. -/
theorem check_circuit_work {target clauses steps} {checked : Checked target clauses steps}
    {work left : Nat} (ok : (check target clauses steps).run work = (.ok checked,left)) :
    work = left + 8 * ((clauses.map fun controls => 2 * controls.length + 7).sum + 1) := by
  have compared := ok
  unfold check at compared
  obtain ⟨_,middle,charged,comparison⟩ := Finite.bind_success _ _ _ _ _ compared
  have paid := Finite.exactWork_success _ _ _ _ charged
  have enough : comparisonCharge clauses steps ≤ work := by
    by_cases short : work < comparisonCharge clauses steps
    · rw [check_work_limit target clauses steps work short] at ok
      cases ok
    · exact Nat.le_of_not_gt short
  rw [Exact.charge_success _ _ enough] at paid
  have remaining : middle = work - comparisonCharge clauses steps := (congrArg Prod.snd paid).symm
  have unchanged : left = middle := by
    split at comparison
    next =>
      split at comparison
      next => exact (Finite.pure_success _ _ _ _ comparison).2
      next => cases comparison
    next => cases comparison
  have fields : comparisonCharge clauses steps =
      8 * ((clauses.map fun controls => 2 * controls.length + 7).sum + 1) := by
    rw [checked.literal, comparisonCharge]
    congr 1
    have sumFields (clauses : List (List Control)) :
        (clauses.map fun controls => controls.length + 1).sum +
          ((clauses.map (toggle target)).map fun step => step.controls.length + 1 + match step.action with
            | .monomial axes permutation phases => axes.length + permutation.length + phases.length
            | .hadamard _ => 1
            | .contract axes _ _ => axes.length + 2).sum =
          (clauses.map fun controls => 2 * controls.length + 7).sum := by
      induction clauses with
      | nil => rfl
      | cons controls rest ih =>
        simp only [List.map_cons, List.sum_cons, toggle, Semantics.RawTrace.gate, List.length_cons,
          List.length_nil, Nat.reduceAdd]
        omega
    rw [sumFields]
  omega

/-- Every accepted literal step retains its coefficient and the composition
preserves the input coordinates. The only updated bit is the nominated target. -/
theorem Checked.action {target clauses steps} (checked : Checked target clauses steps)
    (label : Nat) (value : Scalar) (valid : Exact.Scalar.valid value = true)
    (nonzero : value ≠ Scalar.zero) :
    steps.foldlM (fun row step => do
      let [(output, coefficient)] ← Finite.contributions [] step row.1 row.2 | throw Finite.Error.equation
      return (output, coefficient)) (label, value) =
      .ok (targetUpdate target label (predicate clauses label), value) := by
  have evaluate (clauses : List (List Control)) (label : Nat) :
      (clauses.map (toggle target)).foldlM (fun row step => do
        let [(output, coefficient)] ← Finite.contributions [] step row.1 row.2 | throw Finite.Error.equation
        return (output, coefficient)) (label, value) = .ok (run target clauses label, value) := by
    induction clauses generalizing label with
    | nil => rfl
    | cons controls rest ih =>
      simp only [List.map_cons, List.foldlM_cons, toggle_contribution _ _ _ _ valid nonzero,
        bind, Except.bind, run, List.foldl_cons]
      exact ih _
  rw [checked.literal, evaluate, run_predicate _ _ _ checked.distinct]

#print axioms check_circuit_work
#print axioms Checked.action

end QleisliKernel.Qirf.StructuralXor
