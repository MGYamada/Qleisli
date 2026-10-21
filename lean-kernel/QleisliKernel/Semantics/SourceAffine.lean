import Std

/-! Integer affine meanings, independent of normalization and implication checks.
Coefficient positions belong to the enclosing original formal-parameter frame;
this mathematical representation does not identify binders by spelling.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Semantics.SourceAffine

abbrev Valuation := Nat → Int

def dot (coefficients : List Int) (values : Valuation) : Int :=
  coefficients.foldr (fun coefficient remaining => fun values =>
    coefficient * values 0 + remaining (fun i => values (i+1))) (fun _ => 0) values

@[simp] theorem dot_nil (values : Valuation) : dot [] values = 0 := rfl
@[simp] theorem dot_cons (first : Int) (rest : List Int) (values : Valuation) :
    dot (first::rest) values = first*values 0 + dot rest (fun i => values (i+1)) := rfl

structure Form where
  constant : Int
  coefficients : List Int
  deriving BEq, DecidableEq, Repr

def Form.evaluate (form : Form) (values : Valuation) : Int :=
  form.constant + dot form.coefficients values

def Form.add (a b : Form) : Form :=
  ⟨a.constant+b.constant,List.zipWith (·+·) a.coefficients b.coefficients⟩

def Form.scale (factor : Int) (a : Form) : Form :=
  ⟨factor*a.constant,a.coefficients.map (factor*·)⟩

theorem dot_add (a b : List Int) (same : a.length = b.length) (values : Valuation) :
    dot (List.zipWith (·+·) a b) values = dot a values + dot b values := by
  induction a generalizing b values with
  | nil => cases b <;> simp_all [dot]
  | cons first rest ih =>
    cases b with
    | nil => simp at same
    | cons other tail =>
      simp only [List.length_cons,Nat.add_right_cancel_iff] at same
      simp only [List.zipWith_cons_cons,dot_cons,Int.add_mul,ih tail same]
      omega

theorem dot_scale (factor : Int) (a : List Int) (values : Valuation) :
    dot (a.map (factor*·)) values = factor*dot a values := by
  induction a generalizing values with
  | nil => simp
  | cons first rest ih =>
    simp only [List.map_cons,dot_cons,ih,Int.mul_add,Int.mul_assoc]

theorem Form.evaluate_add (a b : Form) (same : a.coefficients.length = b.coefficients.length)
    (values : Valuation) : (a.add b).evaluate values = a.evaluate values+b.evaluate values := by
  simp only [Form.evaluate,Form.add,dot_add _ _ same]
  omega

theorem Form.evaluate_scale (factor : Int) (a : Form) (values : Valuation) :
    (a.scale factor).evaluate values = factor*a.evaluate values := by
  simp only [Form.evaluate,Form.scale,dot_scale,Int.mul_add]

theorem dot_zero (coefficients : List Int) (zero : coefficients.all (· == 0) = true)
    (values : Valuation) : dot coefficients values = 0 := by
  induction coefficients generalizing values with
  | nil => rfl
  | cons first rest ih =>
    simp only [List.all_cons,Bool.and_eq_true,beq_iff_eq] at zero
    rcases zero with ⟨head,tail⟩
    simp only [dot_cons,head,Int.zero_mul,Int.zero_add]
    exact ih tail _

def coordinate (variables position : Nat) : Form :=
  ⟨0,List.replicate position 0 ++ 1 :: List.replicate (variables-position-1) 0⟩

private theorem dot_zero_prefix (count : Nat) (tail : List Int) (values : Valuation) :
    dot (List.replicate count 0 ++ tail) values = dot tail (fun i => values (i+count)) := by
  induction count generalizing values with
  | zero => simp
  | succ count ih =>
    simp only [List.replicate_succ,List.cons_append,dot_cons,Int.zero_mul,Int.zero_add,ih]
    simp only [Nat.add_assoc]

theorem coordinate_evaluate (variables position : Nat) (values : Valuation) :
    (coordinate variables position).evaluate values = values position := by
  have zero : (List.replicate (variables-position-1) (0 : Int)).all (· == 0) = true := by simp
  simp only [coordinate,Form.evaluate,dot_zero_prefix,dot_cons,dot_zero _ zero,
    Int.zero_add,Int.one_mul,Int.add_zero,Nat.zero_add]

theorem coordinate_length (variables position : Nat) (bound : position < variables) :
    (coordinate variables position).coefficients.length = variables := by
  simp only [coordinate,List.length_append,List.length_replicate,List.length_cons]
  omega

/-- Every row represents an exact integer inequality `row(values) <= 0`. -/
def Holds (rows : List Form) (values : Valuation) : Prop :=
  ∀ row ∈ rows, row.evaluate values ≤ 0

/-- A context is a disjunction of conjunctions, including the empty cases. -/
def Satisfies (alternatives : List (List Form)) (values : Valuation) : Prop :=
  ∃ rows ∈ alternatives, Holds rows values

theorem holds_singleton (a : Form) (values : Valuation) :
    Holds [a] values ↔ a.evaluate values ≤ 0 := by simp [Holds]

theorem holds_pair (a b : Form) (values : Valuation) :
    Holds [a,b] values ↔ a.evaluate values ≤ 0 ∧ b.evaluate values ≤ 0 := by simp [Holds]

theorem satisfies_singleton (a : List Form) (values : Valuation) :
    Satisfies [a] values ↔ Holds a values := by simp [Satisfies]

theorem satisfies_pair (a b : List Form) (values : Valuation) :
    Satisfies [a,b] values ↔ Holds a values ∨ Holds b values := by simp [Satisfies]

theorem holds_append (a b : List Form) (values : Valuation) :
    Holds (a ++ b) values ↔ Holds a values ∧ Holds b values := by
  simp only [Holds,List.mem_append,or_imp,forall_and]

theorem satisfies_product (a b : List (List Form)) (values : Valuation) :
    Satisfies (a.flatMap (fun first => b.map (first ++ ·))) values ↔
      Satisfies a values ∧ Satisfies b values := by
  constructor
  · rintro ⟨rows,member,held⟩
    obtain ⟨first,ha,mapped⟩ := List.mem_flatMap.mp member
    obtain ⟨second,hb,same⟩ := List.mem_map.mp mapped
    subst rows
    obtain ⟨hfirst,hsecond⟩ := (holds_append first second values).mp held
    exact ⟨⟨first,ha,hfirst⟩,⟨second,hb,hsecond⟩⟩
  · rintro ⟨⟨first,ha,hfirst⟩,⟨second,hb,hsecond⟩⟩
    exact ⟨first ++ second,List.mem_flatMap.mpr
      ⟨first,ha,List.mem_map.mpr ⟨second,hb,rfl⟩⟩,
      (holds_append first second values).mpr ⟨hfirst,hsecond⟩⟩

inductive Comparison where
  | eq | ne | le | lt | ge | gt
  deriving BEq, DecidableEq, Repr

def Comparison.Relation : Comparison → Int → Int → Prop
  | .eq,a,b => a = b
  | .ne,a,b => a ≠ b
  | .le,a,b => a ≤ b
  | .lt,a,b => a < b
  | .ge,a,b => b ≤ a
  | .gt,a,b => b < a

def Comparison.negate : Comparison → Comparison
  | .eq => .ne | .ne => .eq | .le => .gt
  | .lt => .ge | .ge => .lt | .gt => .le

def Comparison.test : Comparison → Int → Int → Bool
  | .eq,a,b => a == b | .ne,a,b => a != b
  | .le,a,b => a ≤ b | .lt,a,b => a < b
  | .ge,a,b => b ≤ a | .gt,a,b => b < a

theorem Comparison.test_relation (op : Comparison) (a b : Int) :
    op.test a b = true ↔ op.Relation a b := by
  cases op <;> simp [test,Relation]

theorem Comparison.negate_relation (op : Comparison) (a b : Int) :
    op.negate.Relation a b ↔ ¬op.Relation a b := by
  cases op <;> simp [negate,Relation] <;> omega

end QleisliKernel.Semantics.SourceAffine
