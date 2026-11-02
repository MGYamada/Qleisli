import QleisliKernel.SourceTypes.StaticNatural

/-! Symbolic Nat aliases under the original generic header's ordered premises.
Each alias retains its initializer's helper interpretation and earlier lexical
meaning. Closing to a convenient caller value cannot repair nonlinear or
unguarded original arithmetic, and later shadowing cannot rebind an initializer.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.GenericLexicalNatural
open Finite Semantics.SourceNatural Semantics.SourceAffine

abbrev Meaning {sources owner name tokens} (prepared : StaticNatural.Prepared sources owner name tokens) :=
  NaturalPrepare.Meaning (StaticHeaders.frame prepared.original)
    (NaturalHelpers.interpretation prepared.helpers prepared.bindings) prepared.original.header.premises

structure Environment {sources owner name tokens}
    (prepared : StaticNatural.Prepared sources owner name tokens) where
  meaning : Valuation → Prop
  context : NaturalPredicates.Context meaning
  original : ∀ values,meaning values → Meaning prepared values
  names : Valuation → Names
  reader : ∀ bindings fuel path,
    WorkM (NaturalNormalize.Result names (NaturalHelpers.interpretation prepared.helpers bindings)
      meaning (fuel+1) (.name path))

def initial {sources owner name tokens} (prepared : StaticNatural.Prepared sources owner name tokens) :
    Environment prepared :=
  ⟨Meaning prepared,prepared.scope.context,fun _ held => held,
    NaturalFrames.names (StaticHeaders.frame prepared.original),fun bindings =>
    NaturalFrames.readName (StaticHeaders.frame prepared.original)
      (NaturalHelpers.interpretation prepared.helpers bindings) (fun _ held => held.1)⟩

structure Checked {sources owner name tokens}
    (prepared : StaticNatural.Prepared sources owner name tokens) (environment : Environment prepared)
    (scope : List String) (expression : Expr) where
  bindings : List (Path × NaturalCatalog.Key)
  resolved : ∃ before after,
    (NaturalCatalog.scopedExpressionBindings sources (prepared.helpers.map (·.original)) owner scope [expression]).run before =
      (.ok bindings,after)
  normalized : NaturalNormalize.Result environment.names (NaturalHelpers.interpretation prepared.helpers bindings)
    environment.meaning 128 expression

private def normalize {sources owner name tokens}
    (prepared : StaticNatural.Prepared sources owner name tokens) (environment : Environment prepared)
    (bindings : List (Path × NaturalCatalog.Key)) (expression : Expr) :
    WorkM (NaturalNormalize.Result environment.names (NaturalHelpers.interpretation prepared.helpers bindings)
      environment.meaning 128 expression) :=
  NaturalNormalize.normalize (StaticHeaders.frame prepared.original).binders.length
    environment.context
    ⟨environment.reader bindings,
      fun fuel path arguments args => NaturalHelpers.readCall
        (StaticHeaders.frame prepared.original).binders.length environment.names
        prepared.helpers bindings environment.context fuel path arguments args⟩ 128 expression

def read {sources owner name tokens}
    (prepared : StaticNatural.Prepared sources owner name tokens) (environment : Environment prepared)
    (scope : List String) (expression : Expr) : WorkM (Checked prepared environment scope expression) := do
  let bindings ← NaturalAffine.witness
    (NaturalCatalog.scopedExpressionBindings sources (prepared.helpers.map (·.original)) owner scope [expression])
  let normalized ← normalize prepared environment bindings.val expression
  return ⟨bindings.val,by with_reducible exact bindings.property,normalized⟩

def extend {sources owner name tokens prepared environment scope expression}
    (checked : @Checked sources owner name tokens prepared environment scope expression)
    (aliasName : String) : Environment prepared :=
  ⟨environment.meaning,environment.context,environment.original,
    (fun values path => if path = [aliasName] then
      evaluate 128 (environment.names values) (NaturalHelpers.interpretation prepared.helpers checked.bindings) expression
    else environment.names values path),
    fun laterBindings _fuel path => do
      exactWork (Exact.charge (aliasName.utf8ByteSize+(path.map String.utf8ByteSize).sum+1))
      if same : path = [aliasName] then
        return ⟨checked.normalized.form,by
          intro values held
          obtain ⟨value,computed,meaning⟩ := checked.normalized.correct values held
          refine ⟨value,?_,meaning⟩
          change (if path = [aliasName] then _ else _) = some value
          rw [if_pos same]
          exact computed⟩
      else
        let result ← environment.reader laterBindings _fuel path
        return ⟨result.form,by
          intro values held
          obtain ⟨value,computed,meaning⟩ := result.correct values held
          refine ⟨value,?_,meaning⟩
          change (if path = [aliasName] then _ else _) = some value
          rw [if_neg same]
          exact computed⟩⟩

structure PredicateChecked {sources owner name tokens}
    (prepared : StaticNatural.Prepared sources owner name tokens) (environment : Environment prepared)
    (scope : List String) (predicate : Predicate) where
  bindings : List (Path × NaturalCatalog.Key)
  resolved : ∃ before after,
    (NaturalCatalog.scopedExpressionBindings sources (prepared.helpers.map (·.original)) owner scope
      [predicate.left,predicate.right]).run before = (.ok bindings,after)
  left : NaturalNormalize.Result environment.names (NaturalHelpers.interpretation prepared.helpers bindings)
    environment.meaning 128 predicate.left
  right : NaturalNormalize.Result environment.names (NaturalHelpers.interpretation prepared.helpers bindings)
    environment.meaning 128 predicate.right

def readPredicate {sources owner name tokens}
    (prepared : StaticNatural.Prepared sources owner name tokens) (environment : Environment prepared)
    (scope : List String) (predicate : Predicate) : WorkM (PredicateChecked prepared environment scope predicate) := do
  let bindings ← NaturalAffine.witness
    (NaturalCatalog.scopedExpressionBindings sources (prepared.helpers.map (·.original)) owner scope
      [predicate.left,predicate.right])
  let left ← normalize prepared environment bindings.val predicate.left
  let right ← normalize prepared environment bindings.val predicate.right
  pure ⟨bindings.val,by with_reducible exact bindings.property,left,right⟩

theorem PredicateChecked.branchMeaning {sources owner name tokens prepared environment scope predicate}
    (checked : @PredicateChecked sources owner name tokens prepared environment scope predicate)
    (branch : Bool) (values : Valuation) (held : environment.meaning values) :
    (predicate.forBranch branch).Truth 128 (environment.names values)
      (NaturalHelpers.interpretation prepared.helpers checked.bindings) ↔
      (predicate.forBranch branch).comparison.Relation
        (checked.left.form.evaluate values) (checked.right.form.evaluate values) := by
  obtain ⟨a,left,sameLeft⟩ := checked.left.correct values held
  obtain ⟨b,right,sameRight⟩ := checked.right.correct values held
  rw [sameLeft,sameRight]
  exact Predicate.truth_iff_of_values _ _ _ _ _ _ left right

/-- Strengthen the exact lexical interpretation by an original branch guard.
Both operands have already been normalized in the preceding context; a guard
cannot justify a subtraction in its own condition. No feasibility test removes
an original branch or grants evidence about opaque Basis parameters. -/
def underPredicate {sources owner name tokens prepared environment scope predicate}
    (checked : @PredicateChecked sources owner name tokens prepared environment scope predicate)
    (branch : Bool) : WorkM (Environment prepared) := do
  let compared ← NaturalPredicates.comparison checked.left.form
    (predicate.forBranch branch).comparison checked.right.form
  let joined ← NaturalPredicates.conjunction environment.context compared
  let guardedMeaning := fun values => environment.meaning values ∧
    (predicate.forBranch branch).Truth 128 (environment.names values)
      (NaturalHelpers.interpretation prepared.helpers checked.bindings)
  let context : NaturalPredicates.Context guardedMeaning := ⟨joined.alternatives,by
    intro values
    rw [joined.correct]
    constructor
    · rintro ⟨held,related⟩
      exact ⟨held,(checked.branchMeaning branch values held).mpr related⟩
    · rintro ⟨held,truth⟩
      exact ⟨held,(checked.branchMeaning branch values held).mp truth⟩⟩
  pure ⟨guardedMeaning,context,fun values held => environment.original values held.1,
    environment.names,fun bindings fuel path => do
      let previous ← environment.reader bindings fuel path
      pure ⟨previous.form,fun values held => previous.correct values held.1⟩⟩

structure SomeEnvironment (sources : Sources) where
  owner : String
  name : String
  prepared : StaticNatural.Prepared sources owner name ["0"]
  environment : Environment prepared

def validate {sources : Sources} (state : SomeEnvironment sources) (caller : String) (scope : List String) (expression : Expr) :
    WorkM Unit := do
  guard (state.owner == caller) .request
  let _ ← read state.prepared state.environment scope expression
  pure ()

def bind {sources : Sources} (state : SomeEnvironment sources) (caller : String) (scope : List String)
    (name : String) (expression : Expr) : WorkM (SomeEnvironment sources) := do
  guard (state.owner == caller && !scope.contains name) .request
  let checked ← read state.prepared state.environment scope expression
  pure ⟨state.owner,state.name,state.prepared,extend checked name⟩

def assume {sources : Sources} (state : SomeEnvironment sources) (caller : String) (scope : List String)
    (predicate : Predicate) (branch : Bool) : WorkM (SomeEnvironment sources) := do
  guard (state.owner == caller) .request
  let checked ← readPredicate state.prepared state.environment scope predicate
  let environment ← underPredicate checked branch
  pure ⟨state.owner,state.name,state.prepared,environment⟩

end QleisliKernel.SourceTypes.GenericLexicalNatural
