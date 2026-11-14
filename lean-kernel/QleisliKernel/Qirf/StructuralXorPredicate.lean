import QleisliKernel.Qirf.StructuralXor
import QleisliKernel.SourceTypes.SourceRuntimeTrace

/-! Compile the checked original predicate's ordinary expression to bounded
parity clauses on its declared input coordinates. No input labels are listed.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.StructuralXorPredicate
open QleisliKernel Semantics.Finite Semantics.SourceOrdinary SourceTypes
open StructuralXor (predicate)

private def boolValue (value : Bool) : Option Nat := some value.toNat

private def parity (clauses : List (List Control)) (label : Nat) : Bool :=
  clauses.foldr (fun controls result => Bool.xor (enabled controls label) result) false

private theorem fold_parity (clauses : List (List Control)) (label : Nat) (initial : Bool) :
    clauses.foldl (fun result controls => Bool.xor result (enabled controls label)) initial =
      Bool.xor initial (parity clauses label) := by
  induction clauses generalizing initial with
  | nil => exact (Bool.xor_false initial).symm
  | cons controls rest ih =>
    simp only [List.foldl_cons, parity, List.foldr_cons]
    rw [ih]
    exact Bool.xor_assoc _ _ _

private theorem predicate_parity (clauses : List (List Control)) (label : Nat) :
    predicate clauses label = parity clauses label := by
  rw [predicate, fold_parity, Bool.false_xor]

private theorem parity_append (left right : List (List Control)) (label : Nat) :
    parity (left ++ right) label = Bool.xor (parity left label) (parity right label) := by
  induction left with
  | nil => exact (Bool.false_xor _).symm
  | cons controls rest ih =>
    simp only [List.cons_append, parity, List.foldr_cons] at ih ⊢
    rw [ih, Bool.xor_assoc]

/-- The exact input leaf represented by one original parameter ordinal. -/
inductive Field where
  | unit
  | bit (axis : Nat)
  | bits (axis width : Nat)

def Field.read (label : Nat) : Field → Nat
  | .unit => 0
  | .bit axis => Semantics.Finite.bit label axis
  | .bits axis width => (label / 2^axis) % 2^width

def valuation (fields : List Field) (label : Nat) : Valuation :=
  ⟨fun index => fields[index]?.map (Field.read label), fun _ => none, fun _ _ _ => none⟩

structure Compiled (fields : List Field) (expression : Expression) where
  clauses : List (List Control)
  meaning : ∀ label, evaluate (valuation fields label) expression = some (parity clauses label).toNat

private def constant (value : Bool) : List (List Control) := if value then [[]] else []

private theorem parity_constant (value : Bool) (label : Nat) :
    parity (constant value) label = value := by cases value <;> rfl

private theorem bit_as_bool (label axis : Nat) : (bit label axis == 1).toNat = bit label axis := by
  have small := RuntimeScatterTransport.bit_lt label axis
  have either : bit label axis = 0 ∨ bit label axis = 1 := by omega
  rcases either with zero | one
  · simp [zero]
  · simp [one]

private theorem parity_single (label axis : Nat) :
    (parity [[⟨axis,true⟩]] label).toNat = bit label axis := by
  simpa [parity, enabled] using bit_as_bool label axis

private theorem bit_slice (label axis offset width : Nat) (inside : offset < width) :
    bit ((label / 2^axis) % 2^width) offset = bit label (axis + offset) := by
  simp only [bit, ← Nat.toNat_testBit, Nat.testBit_mod_two_pow, decide_eq_true inside,
    Bool.true_and, Nat.testBit_div_two_pow, Nat.add_comm]

private theorem digit_ext {left right width : Nat} (leftBound : left < 2^width)
    (rightBound : right < 2^width) :
    (∀ i, i < width → bit left i = bit right i) ↔ left = right := by
  constructor
  · intro digits
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases inside : i < width
    · have same := digits i inside
      simp only [bit, ← Nat.toNat_testBit] at same
      cases leftBit : left.testBit i <;> cases rightBit : right.testBit i <;> simp_all
    · have power : 2^width ≤ 2^i := Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt inside)
      rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le leftBound power),
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le rightBound power)]
  · intro same _ _
    rw [same]

private def wordControls (axis width expected : Nat) : List Control :=
  (List.range width).map fun offset => ⟨axis+offset,bit expected offset == 1⟩

private theorem wordControls_eq (label axis width expected : Nat) (bound : expected < 2^width) :
    enabled (wordControls axis width expected) label =
      (((label / 2^axis) % 2^width) == expected) := by
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, ← digit_ext (Nat.mod_lt _ (Nat.two_pow_pos _)) bound]
  simp only [enabled, wordControls, List.all_map, List.all_eq_true, List.mem_range,
    Function.comp_apply, beq_iff_eq]
  apply forall_congr'
  intro offset
  apply forall_congr'
  intro inside
  rw [bit_slice _ _ _ _ inside]
  have leftSmall := RuntimeScatterTransport.bit_lt label (axis+offset)
  have rightSmall := RuntimeScatterTransport.bit_lt expected offset
  have left : bit label (axis+offset) = 0 ∨ bit label (axis+offset) = 1 := by omega
  have right : bit expected offset = 0 ∨ bit expected offset = 1 := by omega
  rcases left with zero | one <;> rcases right with zero' | one' <;> simp_all

private theorem parity_word (label axis width expected : Nat) (bound : expected < 2^width) :
    parity [wordControls axis width expected] label = (((label / 2^axis) % 2^width) == expected) := by
  simpa only [parity, List.foldr_cons, List.foldr_nil, Bool.xor_false] using
    wordControls_eq label axis width expected bound

private theorem parity_prefix (label : Nat) (initial : List Control) (clauses : List (List Control)) :
    parity (clauses.map (initial ++ ·)) label = (enabled initial label && parity clauses label) := by
  induction clauses with
  | nil => simp [parity]
  | cons controls rest ih =>
    have head : enabled (initial ++ controls) label = (enabled initial label && enabled controls label) := by
      simp [enabled]
    simp only [parity, List.map_cons, List.foldr_cons] at ih ⊢
    rw [head, ih, Bool.and_xor_distrib_left]

private theorem enabled_dedup (label : Nat) (controls : List Control) :
    enabled controls.eraseDups label = enabled controls label := by
  unfold enabled
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true, List.mem_eraseDups]

private theorem parity_product (label : Nat) (left right : List (List Control)) :
    parity (left.flatMap fun controls => right.map (controls ++ ·)) label =
      (parity left label && parity right label) := by
  induction left with
  | nil => rfl
  | cons controls rest ih =>
    rw [List.flatMap_cons, parity_append, parity_prefix, ih]
    change Bool.xor (enabled controls label && parity right label) (parity rest label && parity right label) = _
    rw [← Bool.and_xor_distrib_right]
    rfl

private theorem parity_dedup (label : Nat) (clauses : List (List Control)) :
    parity (clauses.map List.eraseDups) label = parity clauses label := by
  induction clauses with
  | nil => rfl
  | cons controls rest ih =>
    simp only [parity, List.map_cons, List.foldr_cons] at ih ⊢
    rw [enabled_dedup, ih]

private def clauseFields (clauses : List (List Control)) : Nat :=
  (clauses.map (·.length + 1)).sum

private def charged (amount : Nat) : Finite.WorkM Unit :=
  Finite.exactWork (Exact.charge (8 * (amount + 1)))

private def join {fields a b} (left : Compiled fields a) (right : Compiled fields b) :
    Finite.WorkM (Compiled fields (.and a b)) := do
  let leftFields := clauseFields left.clauses + 1
  let rightFields := clauseFields right.clauses + 1
  charged (leftFields * rightFields * (leftFields + rightFields))
  return ⟨(left.clauses.flatMap (fun controls => right.clauses.map (controls ++ ·))).map List.eraseDups, by
    intro label
    rw [evaluate_unfold, parity_dedup, parity_product]
    simp only [evaluateStep, left.meaning, right.meaning]
    cases parity left.clauses label <;> cases parity right.clauses label <;> rfl⟩

private def compileStep (fields : List Field) : (expression : Expression) →
    ((child : Expression) → sizeOf child < sizeOf expression → Finite.WorkM (Compiled fields child)) →
    Finite.WorkM (Compiled fields expression)
  | .bit value, _ => do
    charged 1
    return ⟨constant value, fun label => by rw [evaluate_unfold, parity_constant]; cases value <;> rfl⟩
  | .input index, _ => do
    charged (fields.length + 1)
    match input : fields[index]? with
    | some (.bit axis) =>
      return ⟨[[⟨axis,true⟩]], fun label => by
        rw [evaluate_unfold]
        simp only [evaluateStep, valuation, input, Option.map_some, Field.read, parity_single]⟩
    | _ => throw .request
  | .not child, recur => do
    let compiled ← recur child (by decreasing_tactic)
    charged 1
    return ⟨[] :: compiled.clauses, by
      intro label
      rw [evaluate_unfold]
      simp only [evaluateStep, compiled.meaning]
      change _ = boolValue (Bool.xor true (parity compiled.clauses label))
      cases parity compiled.clauses label <;> rfl⟩
  | .xor first second, recur => do
    let left ← recur first (by decreasing_tactic)
    let right ← recur second (by decreasing_tactic)
    charged (clauseFields left.clauses + clauseFields right.clauses)
    return ⟨left.clauses ++ right.clauses, by
      intro label
      rw [evaluate_unfold, parity_append]
      simp only [evaluateStep, left.meaning, right.meaning]
      cases parity left.clauses label <;> cases parity right.clauses label <;> rfl⟩
  | .and first second, recur => do
    let left ← recur first (by decreasing_tactic)
    let right ← recur second (by decreasing_tactic)
    join left right
  | .equalsOrdinal expected (.input index), _ => do
    charged (fields.length + 1)
    match input : fields[index]? with
    | some (.bits axis width) =>
      charged width
      if bound : expected < 2^width then
        return ⟨[wordControls axis width expected], by
          intro label
          rw [evaluate_unfold, parity_word _ _ _ _ bound]
          simp only [evaluateStep]
          rw [evaluate_unfold]
          simp only [evaluateStep, valuation, input, Option.map_some, Field.read,
            bind, Option.bind]
          cases (((label / 2^axis) % 2^width) == expected) <;> rfl⟩
      else throw .request
    | _ => throw .request
  | _, _ => throw .request

def compile (fields : List Field) : (expression : Expression) → Finite.WorkM (Compiled fields expression) :=
  Expression.descend (compileStep fields)

theorem Compiled.evaluates {fields expression} (compiled : Compiled fields expression) (label : Nat) :
    evaluate (valuation fields label) expression = some (predicate compiled.clauses label).toNat := by
  rw [predicate_parity]
  exact compiled.meaning label

private def inputFields (parameter : Value) : Finite.WorkM (List Field × Nat) := do
  charged (SourceRuntimeValues.valueFields parameter)
  let (fields, width) ← parameter.foldlM (fun (fields,width) atom => do
    match atom with
    | .tuple _ => return (fields,width)
    | .ordinary basis (.input ordinal) =>
      Finite.guard (ordinal == fields.size) .request
      match basis with
      | [.unit] => return (fields.push .unit,width)
      | [.bit] => return (fields.push (.bit width),width+1)
      | [.bits size] => return (fields.push (.bits width size),width+size)
      | _ => throw .request
    | _ => throw .request) ((#[] : Array Field),0)
  return (fields.toList,width)

structure Original {sources caller} (event : SourceRuntimeContext.ComputedEvent sources caller) where
  body : SourceRuntimeTrace.Body event.predicate.target.signature
  original : RuntimeInterval.Computed (SourceRuntimeTrace.readComputedPredicateBody event) body
  fields : List Field
  width : Nat
  parameterMap : ∃ parameter, body.checked.summary.parameterValues = [parameter] ∧
    RuntimeInterval.Computed (inputFields parameter) (fields,width)
  expression : Expression
  result : body.checked.summary.value = [.ordinary [.bit] expression]
  compiled : Compiled fields expression

/-- The predicate and input coordinate map are derived from the same original
typed body, including its already resolved ordinary callees. -/
def read {sources caller} (event : SourceRuntimeContext.ComputedEvent sources caller) :
    Finite.WorkM (Original event) := do
  let body ← NaturalAffine.witness (SourceRuntimeTrace.readComputedPredicateBody event)
  match parameters : body.val.checked.summary.parameterValues with
  | [parameter] =>
    Finite.guard (SourceRuntimeValues.typeOf parameter == Semantics.RuntimeType.ordinary event.input.basis) .request
    let fields ← NaturalAffine.witness (inputFields parameter)
    match result : body.val.checked.summary.value with
    | [.ordinary [.bit] expression] =>
      let compiled ← compile fields.val.1 expression
      return ⟨body.val, by with_reducible exact body.property, fields.val.1, fields.val.2,
        ⟨parameter,parameters,by with_reducible exact fields.property⟩, expression, result, compiled⟩
    | _ => throw .request
  | _ => throw .request

/-- Verify the original source's compiled predicate against the supplied
literal steps. The target follows the original data in local wire order. -/
def check {sources caller} {event : SourceRuntimeContext.ComputedEvent sources caller}
    (original : Original event) (steps : List Step) :
    Finite.WorkM (StructuralXor.Checked original.width original.compiled.clauses steps) :=
  StructuralXor.check original.width original.compiled.clauses steps

/-- The literal steps XOR the one-bit result of the original predicate with
the auxiliary, preserving every exact input coordinate and coefficient. -/
theorem Original.action {sources caller} {event : SourceRuntimeContext.ComputedEvent sources caller}
    (original : Original event) {steps : List Step}
    (checked : StructuralXor.Checked original.width original.compiled.clauses steps)
    (label : Nat) (value : Semantics.Exact.Scalar)
    (valid : Exact.Scalar.valid value = true) (nonzero : value ≠ Semantics.Exact.Scalar.zero) :
    let toggle := (evaluate (valuation original.fields label) original.expression).getD 0 == 1
    steps.foldlM (fun row step => do
      let [(output, coefficient)] ← Finite.contributions [] step row.1 row.2 | throw Finite.Error.equation
      return (output, coefficient)) (label, value) =
      .ok (StructuralXor.targetUpdate original.width label toggle, value) := by
  dsimp only
  rw [original.compiled.evaluates, Option.getD_some]
  cases originalValue : predicate original.compiled.clauses label <;>
    simpa only [originalValue] using checked.action label value valid nonzero

#print axioms Compiled.evaluates
#print axioms read
#print axioms Original.action

end QleisliKernel.Qirf.StructuralXorPredicate
