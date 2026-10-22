import QleisliKernel.SourceTypes.NaturalAffine

/-! Simultaneous affine substitution in original canonical coefficient order.
Replacement forms are never traversed as callee variables. Each checked scale
and addition retains exact meaning and its signed-i128 intermediate failures.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.NaturalSubstitute
open Semantics.SourceAffine NaturalAffine

def replacementValues (replacements : List Form) (values : Valuation) : Valuation :=
  fun position => (replacements[position]?.map (fun form => form.evaluate values)).getD 0

private theorem replacement_head (head : Form) (tail : List Form) (values : Valuation) :
    replacementValues (head::tail) values 0 = head.evaluate values := rfl

private theorem replacement_tail (head : Form) (tail : List Form) (values : Valuation) :
    (fun i => replacementValues (head::tail) values (i+1)) = replacementValues tail values := rfl

structure Result (template : Form) (replacements : List Form) where
  form : Form
  correct : ∀ values,form.evaluate values = template.evaluate (replacementValues replacements values)

private structure Accumulated (coefficients : List Int) (replacements : List Form) (prior : Form) where
  form : Form
  correct : ∀ values,form.evaluate values = prior.evaluate values +
    dot coefficients (replacementValues replacements values)

private def loop : Nat → (coefficients : List Int) → (replacements : List Form) → (prior : Form) →
    WorkM (Accumulated coefficients replacements prior) :=
  Nat.rec (fun _ _ _ => throw .limit) (fun _ recurse coefficients replacements prior => do
    Finite.exactWork (Exact.charge 1)
    match coefficients,replacements with
    | [],[] => return ⟨prior,by intro values; simp only [dot_nil,Int.add_zero]⟩
    | coefficient :: rest,head :: tail =>
      if zero : coefficient = 0 then
        let result ← recurse rest tail prior
        return ⟨result.form,by
          intro values
          rw [result.correct,dot_cons,zero,Int.zero_mul,Int.zero_add,replacement_tail]⟩
      else
        let scaled ← witness (scale coefficient head)
        let next ← witness (add prior scaled.val)
        let result ← recurse rest tail next.val
        return ⟨result.form,by
          intro values
          obtain ⟨scaleWork,scaleLeft,scaleOk⟩ := scaled.property
          obtain ⟨addWork,addLeft,addOk⟩ := next.property
          rw [result.correct,add_meaning _ _ _ _ _ addOk,
            scale_meaning _ _ _ _ _ scaleOk,dot_cons,replacement_head,replacement_tail]
          omega⟩
    | _,_ => throw .request)

def substitute (variables : Nat) (template : Form) (replacements : List Form) :
    WorkM (Result template replacements) := do
  valid template
  Finite.guard (variables ≤ 32 && template.coefficients.length == replacements.length) .request
  Finite.exactWork (Exact.charge (replacements.length+1))
  let _ ← replacements.mapM fun replacement => do
    valid replacement
    Finite.guard (replacement.coefficients.length == variables) .request
  let start ← witness (constant variables template.constant)
  let result ← loop (template.coefficients.length+1) template.coefficients replacements start.val
  return ⟨result.form,by
    intro values
    obtain ⟨work,left,ok⟩ := start.property
    rw [result.correct,constant_meaning _ _ _ _ _ ok]
    rfl⟩

end QleisliKernel.SourceTypes.NaturalSubstitute
