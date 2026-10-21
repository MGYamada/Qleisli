import QleisliKernel.SourceTypes.NaturalConstraints

/-! Exact comparisons and bounded implication over original affine frames.
The successful result carries a proof about the original operands/context;
neither a failed search nor rational feasibility grants an integer witness.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.NaturalPredicates
open Semantics.SourceAffine NaturalAffine

structure Context (meaning : Valuation → Prop) where
  alternatives : List (List Form)
  correct : ∀ values, Satisfies alternatives values ↔ meaning values

structure Established (proposition : Prop) : Type where
  proof : proposition

private structure Known (meaning : Valuation → Int) where
  form : Form
  correct : ∀ values, form.evaluate values = meaning values

private def difference (a b : Form) : WorkM (Known (fun values => a.evaluate values-b.evaluate values)) := do
  let result ← witness (sub a b)
  return ⟨result.val,by
    obtain ⟨work,left,ok⟩ := result.property
    exact sub_meaning a b result.val work left ok⟩

private def negative (a : Form) : WorkM (Known (fun values => -a.evaluate values)) := do
  let result ← witness (scale (-1) a)
  return ⟨result.val,by
    obtain ⟨work,left,ok⟩ := result.property
    intro values
    simpa only [Int.neg_one_mul] using scale_meaning (-1) a result.val work left ok values⟩

private def increment (a one : Form) (oneMeaning : ∀ values,one.evaluate values = 1) :
    WorkM (Known (fun values => a.evaluate values+1)) := do
  let result ← witness (add a one)
  return ⟨result.val,by
    obtain ⟨work,left,ok⟩ := result.property
    intro values
    rw [add_meaning _ _ _ _ _ ok,oneMeaning]⟩

/-- Preserve the common checked difference/negation/one construction order,
including a capacity failure in an intermediate unused by the chosen operator. -/
def comparison (a : Form) (op : Comparison) (b : Form) :
    WorkM (Context (fun values => op.Relation (a.evaluate values) (b.evaluate values))) := do
  let diff ← difference a b
  let neg ← negative diff.form
  let one ← witness (constant a.coefficients.length 1)
  have oneMeaning : ∀ values,one.val.evaluate values = 1 := by
    obtain ⟨work,left,ok⟩ := one.property
    exact constant_meaning _ _ _ _ _ ok
  match op with
  | .eq => return ⟨[[diff.form,neg.form]],by
      intro values
      simp only [satisfies_singleton,holds_pair,neg.correct,diff.correct,Comparison.Relation]
      omega⟩
  | .ne =>
    let first ← increment diff.form one.val oneMeaning
    let second ← increment neg.form one.val oneMeaning
    return ⟨[[first.form],[second.form]],by
      intro values
      simp only [satisfies_pair,holds_singleton,first.correct,second.correct,neg.correct,
        diff.correct,Comparison.Relation]
      omega⟩
  | .le => return ⟨[[diff.form]],by
      intro values
      simp only [satisfies_singleton,holds_singleton,diff.correct,Comparison.Relation]
      omega⟩
  | .lt =>
    let first ← increment diff.form one.val oneMeaning
    return ⟨[[first.form]],by
      intro values
      simp only [satisfies_singleton,holds_singleton,first.correct,
        diff.correct,Comparison.Relation]
      omega⟩
  | .ge => return ⟨[[neg.form]],by
      intro values
      simp only [satisfies_singleton,holds_singleton,neg.correct,
        diff.correct,Comparison.Relation]
      omega⟩
  | .gt =>
    let first ← increment neg.form one.val oneMeaning
    return ⟨[[first.form]],by
      intro values
      simp only [satisfies_singleton,holds_singleton,first.correct,
        neg.correct,diff.correct,Comparison.Relation]
      omega⟩

def conjunction {a b : Valuation → Prop} (first : Context a) (second : Context b) :
    WorkM (Context (fun values => a values ∧ b values)) := do
  Finite.guard (first.alternatives.length*second.alternatives.length ≤ 64) .limit
  Finite.exactWork (Exact.charge (first.alternatives.length*second.alternatives.length+1))
  -- Validate and charge each complete copied row before constructing products.
  let _ ← first.alternatives.mapM fun a => second.alternatives.mapM fun b => do
    Finite.guard (a.length+b.length ≤ 4096) .limit
    let cells := a.foldl (fun n row => n+row.coefficients.length+2) 0 +
      b.foldl (fun n row => n+row.coefficients.length+2) 0
    Finite.exactWork (Exact.charge (cells+1))
    let _ ← a.mapM valid
    let _ ← b.mapM valid
    pure ()
  let alternatives := first.alternatives.flatMap (fun rows => second.alternatives.map (rows ++ ·))
  return ⟨alternatives,by
    intro values
    rw [satisfies_product,first.correct,second.correct]⟩

private def refuteLoop : Nat → (alternatives : List (List Form)) →
    WorkM (Established (∀ values,¬Satisfies alternatives values)) :=
  Nat.rec (fun alternatives => if empty : alternatives = [] then
      pure ⟨by simp [empty,Satisfies]⟩ else throw .limit)
    (fun _ recurse alternatives => match alternatives with
      | [] => pure ⟨by simp [Satisfies]⟩
      | rows :: rest => do
        let some proof ← NaturalConstraints.check rows | throw .request
        let remaining ← recurse rest
        return ⟨by
          intro values possible
          rcases possible with ⟨branch,member,held⟩
          rcases List.mem_cons.mp member with head | tail
          · subst branch
            exact proof.witness values held
          · exact remaining.proof values ⟨branch,tail,held⟩⟩)

def implies {meaning : Valuation → Prop} (context : Context meaning)
    (a : Form) (op : Comparison) (b : Form) :
    WorkM (Established (∀ values,meaning values → op.Relation (a.evaluate values) (b.evaluate values))) := do
  let opposite ← comparison a op.negate b
  let counterexamples ← conjunction context opposite
  let noValues ← refuteLoop counterexamples.alternatives.length counterexamples.alternatives
  return ⟨by
    intro values original
    by_cases wanted : op.Relation (a.evaluate values) (b.evaluate values)
    · exact wanted
    · exact False.elim (noValues.proof values (counterexamples.correct values |>.mpr
        ⟨original,Comparison.negate_relation _ _ _ |>.mpr wanted⟩))⟩

/-- The subtraction guard uses the common direct `b-a+1` counterexample
construction, without introducing comparison's extra checked negation. -/
def provesLe {meaning : Valuation → Prop} (context : Context meaning) (a b : Form) :
    WorkM (Established (∀ values,meaning values → a.evaluate values ≤ b.evaluate values)) := do
  let diff ← difference b a
  let one ← witness (constant b.coefficients.length 1)
  have oneMeaning : ∀ values,one.val.evaluate values = 1 := by
    obtain ⟨work,left,ok⟩ := one.property
    exact constant_meaning _ _ _ _ _ ok
  let counterexample ← increment diff.form one.val oneMeaning
  let opposite : Context (fun values => b.evaluate values-a.evaluate values+1 ≤ 0) :=
    ⟨[[counterexample.form]],by
      intro values
      simp only [satisfies_singleton,holds_singleton,counterexample.correct,diff.correct]⟩
  let counterexamples ← conjunction context opposite
  let noValues ← refuteLoop counterexamples.alternatives.length counterexamples.alternatives
  return ⟨by
    intro values original
    by_cases wanted : a.evaluate values ≤ b.evaluate values
    · exact wanted
    · exact False.elim (noValues.proof values ((counterexamples.correct values).mpr
        ⟨original,by omega⟩))⟩

/-- This is the common feasibility filter, not an integer-existence proof. -/
def feasible {meaning : Valuation → Prop} (context : Context meaning) : WorkM Bool :=
  context.alternatives.foldlM (fun found rows => do
    if found then return true
    let result ← NaturalConstraints.check rows
    return result.isNone) false

end QleisliKernel.SourceTypes.NaturalPredicates
