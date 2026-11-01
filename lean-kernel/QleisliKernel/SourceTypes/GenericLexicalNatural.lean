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
  names : Valuation → Names
  reader : ∀ bindings fuel path,
    WorkM (NaturalNormalize.Result names (NaturalHelpers.interpretation prepared.helpers bindings)
      (Meaning prepared) (fuel+1) (.name path))

def initial {sources owner name tokens} (prepared : StaticNatural.Prepared sources owner name tokens) :
    Environment prepared :=
  ⟨NaturalFrames.names (StaticHeaders.frame prepared.original),fun bindings =>
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
    (Meaning prepared) 128 expression

def read {sources owner name tokens}
    (prepared : StaticNatural.Prepared sources owner name tokens) (environment : Environment prepared)
    (scope : List String) (expression : Expr) : WorkM (Checked prepared environment scope expression) := do
  let bindings ← NaturalAffine.witness
    (NaturalCatalog.scopedExpressionBindings sources (prepared.helpers.map (·.original)) owner scope [expression])
  let normalized ← NaturalNormalize.normalize (StaticHeaders.frame prepared.original).binders.length
    prepared.scope.context
    ⟨environment.reader bindings.val,
      fun fuel path arguments args => NaturalHelpers.readCall
        (StaticHeaders.frame prepared.original).binders.length environment.names
        prepared.helpers bindings.val prepared.scope.context fuel path arguments args⟩ 128 expression
  return ⟨bindings.val,by with_reducible exact bindings.property,normalized⟩

def extend {sources owner name tokens prepared environment scope expression}
    (checked : @Checked sources owner name tokens prepared environment scope expression)
    (aliasName : String) : Environment prepared :=
  ⟨(fun values path => if path = [aliasName] then
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

end QleisliKernel.SourceTypes.GenericLexicalNatural
