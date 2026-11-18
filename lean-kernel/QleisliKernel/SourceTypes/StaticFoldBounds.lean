import QleisliKernel.SourceTypes.NaturalPredicates

/-! Lexical affine coordinates for original half-open static folds. Widening
retains every outer inequality's meaning, including for an empty range.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.StaticFoldBounds
open Semantics.SourceAffine
open NaturalAffine
open NaturalPredicates (Context)

def widen (form : Form) : Form :=
  ⟨form.constant,form.coefficients ++ [0]⟩

private theorem dot_widen (coefficients : List Int) (values : Valuation) :
    dot (coefficients ++ [0]) values = dot coefficients values := by
  induction coefficients generalizing values with
  | nil => simp
  | cons first rest ih => simp only [List.cons_append,dot_cons,ih]

theorem widen_evaluate (form : Form) (values : Valuation) :
    (widen form).evaluate values = form.evaluate values := by
  simp only [widen,Form.evaluate,dot_widen]

private theorem holds_widen (rows : List Form) (values : Valuation) :
    Holds (rows.map widen) values ↔ Holds rows values := by
  simp [Holds,List.mem_map,widen_evaluate]

private theorem satisfies_widen (alternatives : List (List Form)) (values : Valuation) :
    Satisfies (alternatives.map (List.map widen)) values ↔ Satisfies alternatives values := by
  constructor
  · rintro ⟨rows,member,held⟩
    obtain ⟨original,found,rfl⟩ := List.mem_map.mp member
    exact ⟨original,found,(holds_widen original values).mp held⟩
  · rintro ⟨rows,member,held⟩
    exact ⟨rows.map widen,List.mem_map.mpr ⟨rows,member,rfl⟩,(holds_widen rows values).mpr held⟩

/-- Widen the existing affine frame by a fresh position. Every old inequality
keeps its meaning for the very same valuation. -/
def widenContext {meaning : Valuation → Prop} (context : Context meaning) (variables : Nat) :
    WorkM (Context meaning) := do
  Finite.guard (variables + 1 ≤ 32) .limit
  Finite.exactWork (Exact.charge (context.alternatives.length + 1))
  let rows ← context.alternatives.mapM fun conjunction => do
    Finite.exactWork (Exact.charge (conjunction.length + 1))
    conjunction.mapM fun row => do
      Finite.guard (row.coefficients.length == variables) .request
      let widened := widen row
      valid widened
      return widened
  if same : rows = context.alternatives.map (List.map widen) then
    return ⟨rows,by intro values; rw [same,satisfies_widen,context.correct]⟩
  else throw .request

/-- The extra coordinate is a Nat in the actual half-open loop bounds. An empty
range leaves an inconsistent iteration context and the original body remains
available to the source reader. -/
def iteration {meaning : Valuation → Prop} (context : Context meaning) (variables : Nat)
    (start stop : Form) : WorkM (Context (fun values =>
      meaning values ∧ 0 ≤ values variables ∧ start.evaluate values ≤ values variables ∧
        values variables < stop.evaluate values)) := do
  Finite.guard (start.coefficients.length == variables && stop.coefficients.length == variables) .request
  let outer ← widenContext context variables
  let index ← witness (parameter (variables+1) variables)
  let zero ← witness (constant (variables+1) 0)
  have indexMeaning (values : Valuation) : index.val.evaluate values = values variables := by
    obtain ⟨work,left,ok⟩ := index.property
    exact parameter_meaning _ _ _ work left ok values
  have zeroMeaning (values : Valuation) : zero.val.evaluate values = 0 := by
    obtain ⟨work,left,ok⟩ := zero.property
    exact constant_meaning _ _ _ work left ok values
  let nonnegative ← NaturalPredicates.comparison zero.val .le index.val
  let lower ← NaturalPredicates.comparison (widen start) .le index.val
  let upper ← NaturalPredicates.comparison index.val .lt (widen stop)
  let bracket ← NaturalPredicates.conjunction lower upper
  let bounds ← NaturalPredicates.conjunction nonnegative bracket
  let result ← NaturalPredicates.conjunction outer bounds
  return ⟨result.alternatives,by
    intro values
    simpa only [Comparison.Relation,indexMeaning,zeroMeaning,widen_evaluate] using result.correct values⟩

end QleisliKernel.SourceTypes.StaticFoldBounds
