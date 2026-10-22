import QleisliKernel.SourceTypes.NaturalFrames
import QleisliKernel.SourceTypes.NaturalSubstitute

/-! Original helper premises are checked in declaration order, then the generic
body. Context truth refers to the independent original-expression evaluator;
normalization results do not define the intended predicate.
Original dependency-call readers still require their separate binding proofs.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.NaturalPrepare
open Semantics.SourceNatural Semantics.SourceAffine NaturalAffine NaturalPredicates

structure Numeric where
  left : Form
  comparison : Comparison
  right : Form

def Numeric.Truth (numeric : Numeric) (values : Valuation) : Prop :=
  numeric.comparison.Relation (numeric.left.evaluate values) (numeric.right.evaluate values)

def NumericsTruth (numeric : List Numeric) (values : Valuation) : Prop :=
  ∀ fact ∈ numeric,fact.Truth values

def Meaning (frame : NaturalFrames.Frame) (calls : Calls) (premises : List Predicate)
    (values : Valuation) : Prop :=
  NaturalFrames.Natural frame values ∧ PredicatesTruth 128 (NaturalFrames.names frame values) calls premises

structure Scope (frame : NaturalFrames.Frame) (calls : Calls) (premises : List Predicate) where
  context : Context (Meaning frame calls premises)
  numeric : List Numeric
  correct : ∀ values,NaturalFrames.Natural frame values →
    (NumericsTruth numeric values ↔ PredicatesTruth 128 (NaturalFrames.names frame values) calls premises)

structure CallsReader (frame : NaturalFrames.Frame) (calls : Calls) where
  read : ∀ {meaning : Valuation → Prop}, Context meaning →
    (∀ values,meaning values → NaturalFrames.Natural frame values) →
    ∀ fuel path arguments,
      NaturalNormalize.Arguments (NaturalFrames.names frame) calls meaning fuel arguments →
      WorkM (NaturalNormalize.Result (NaturalFrames.names frame) calls meaning (fuel+1) (.call path arguments))

private def readers {frame calls premises} (scope : Scope frame calls premises)
    (callReader : CallsReader frame calls) :
    NaturalNormalize.Readers (NaturalFrames.names frame) calls (Meaning frame calls premises) :=
  ⟨NaturalFrames.readName frame calls (fun _ held => held.1),
    callReader.read scope.context (fun _ held => held.1)⟩

private theorem normalized_predicate {frame calls meaning} (predicate : Predicate)
    (a : NaturalNormalize.Result (NaturalFrames.names frame) calls meaning 128 predicate.left)
    (b : NaturalNormalize.Result (NaturalFrames.names frame) calls meaning 128 predicate.right)
    (values : Valuation) (held : meaning values) :
    predicate.comparison.Relation (a.form.evaluate values) (b.form.evaluate values) ↔
      predicate.Truth 128 (NaturalFrames.names frame values) calls := by
  obtain ⟨x,hx,px⟩ := a.correct values held
  obtain ⟨y,hy,py⟩ := b.correct values held
  constructor
  · intro valid
    exact ⟨x,y,hx,hy,by rwa [← px,← py]⟩
  · rintro ⟨otherX,otherY,otherLeft,otherRight,valid⟩
    have sameX : otherX = x := Option.some.inj (otherLeft.symm.trans hx)
    have sameY : otherY = y := Option.some.inj (otherRight.symm.trans hy)
    subst otherX
    subst otherY
    rwa [px,py]

private def extend {frame calls premises} (scope : Scope frame calls premises)
    (callReader : CallsReader frame calls) (predicate : Predicate) :
    WorkM (Scope frame calls (premises ++ [predicate])) := do
  let a ← NaturalNormalize.normalize frame.binders.length scope.context (readers scope callReader) 128 predicate.left
  let b ← NaturalNormalize.normalize frame.binders.length scope.context (readers scope callReader) 128 predicate.right
  let numeric : Numeric := ⟨a.form,predicate.comparison,b.form⟩
  let condition ← comparison a.form predicate.comparison b.form
  let context ← conjunction scope.context condition
  return ⟨⟨context.alternatives,by
    intro values
    rw [context.correct]
    change (Meaning frame calls premises values ∧ numeric.Truth values) ↔ _
    constructor
    · rintro ⟨held,valid⟩
      exact ⟨held.1,(predicates_append _ _ _ _ _).mpr
        ⟨held.2,(predicates_singleton _ _ _ _).mpr
          ((normalized_predicate predicate a b values held).mp valid)⟩⟩
    · rintro ⟨natural,all⟩
      obtain ⟨prior,current⟩ := (predicates_append _ _ _ _ _).mp all
      have held : Meaning frame calls premises values := ⟨natural,prior⟩
      exact ⟨held,(normalized_predicate predicate a b values held).mpr
        ((predicates_singleton _ _ _ _).mp current)⟩⟩,
    scope.numeric ++ [numeric],by
      intro values natural
      have prior := scope.correct values natural
      simp only [NumericsTruth,List.mem_append,List.mem_singleton,or_imp,forall_and,forall_eq]
      rw [← NumericsTruth,prior,predicates_append,predicates_singleton]
      constructor
      · rintro ⟨old,new⟩
        exact ⟨old,(normalized_predicate predicate a b values ⟨natural,old⟩).mp new⟩
      · rintro ⟨old,new⟩
        exact ⟨old,(normalized_predicate predicate a b values ⟨natural,old⟩).mpr new⟩⟩

private def requirements {frame calls} (callReader : CallsReader frame calls) :
    Nat → (premises remaining : List Predicate) → Scope frame calls premises →
      WorkM (Scope frame calls (premises ++ remaining)) :=
  Nat.rec (fun _ _ _ => throw .limit)
    (fun _ recurse premises remaining scope => do
      Finite.exactWork (Exact.charge 1)
      match remaining with
      | [] => return (by simpa only [List.append_nil] using scope)
      | predicate :: rest =>
        let next ← extend scope callReader predicate
        let result ← recurse (premises ++ [predicate]) rest next
        return (by simpa only [List.append_assoc,List.singleton_append] using result))

structure Prepared (original : NaturalCatalog.Original) (calls : Calls) where
  scope : Scope (NaturalFrames.original original) calls original.helper.premises
  body : NaturalNormalize.Result (NaturalFrames.names (NaturalFrames.original original)) calls
    (Meaning (NaturalFrames.original original) calls original.helper.premises) 128 original.helper.body

/-- Check an original definition generically before any closed instantiation.
Calls require source-bound readers; no external template is accepted here. -/
def check (original : NaturalCatalog.Original) (calls : Calls)
    (callReader : CallsReader (NaturalFrames.original original) calls) :
    WorkM (Prepared original calls) := do
  let frame := NaturalFrames.original original
  let initial ← NaturalFrames.initial frame
  let scope : Scope frame calls [] := ⟨⟨initial.alternatives,by
      intro values
      rw [initial.correct]
      constructor
      · intro held
        exact ⟨held,by intro _ member; cases member⟩
      · intro held
        exact held.1⟩,
    [],by simp [NumericsTruth,PredicatesTruth]⟩
  let scope ← requirements callReader (original.helper.premises.length+1) [] original.helper.premises scope
  Finite.guard (← feasible scope.context) .request
  let body ← NaturalNormalize.normalize frame.binders.length scope.context (readers scope callReader) 128 original.helper.body
  return ⟨scope,body⟩

end QleisliKernel.SourceTypes.NaturalPrepare
