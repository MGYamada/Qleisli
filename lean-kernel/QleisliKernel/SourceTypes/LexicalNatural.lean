import QleisliKernel.SourceTypes.NaturalClosed

/-! Per-expression helper lookup with immutable earlier lexical aliases.
Each initializer is checked once in its original call resolution and lexical
environment. Its retained exact value/proof supplies later constant lookups,
even when the consuming expression has a different helper table.
The caller must still authenticate the original tokens, scope and actuals.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.LexicalNatural
open QleisliKernel QleisliKernel.SourceTypes QleisliKernel.Finite
open QleisliKernel.Semantics.SourceNatural QleisliKernel.Semantics.SourceAffine

structure Environment (entries : List NaturalHelpers.Entry) where
  names : Names
  reader : ∀ bindings, NaturalClosed.NameReader names (NaturalHelpers.interpretation entries bindings)

def empty (entries : List NaturalHelpers.Entry) : Environment entries :=
  ⟨NaturalClosed.empty,fun bindings => NaturalClosed.emptyReader (NaturalHelpers.interpretation entries bindings)⟩

/-- `originalBindings` is captured at the original initializer, never replaced
by the call table of a later use. Only name lookup is polymorphic in that table. -/
def extend (entries : List NaturalHelpers.Entry) (previous : Environment entries)
    (originalBindings : List (Path × NaturalCatalog.Key)) (name : String) (initializer : Expr)
    (checked : NaturalClosed.Checked previous.names
      (NaturalHelpers.interpretation entries originalBindings) initializer) :
    Environment entries :=
  ⟨NaturalClosed.extend previous.names (NaturalHelpers.interpretation entries originalBindings) name initializer,
    fun laterBindings fuel path => do
      exactWork (Exact.charge (name.utf8ByteSize+(path.map String.utf8ByteSize).sum+1))
      if same : path = [name] then
        return ⟨⟨(checked.value : Int),[]⟩,by
          intro _ _
          refine ⟨checked.value,?_,?_⟩
          · change NaturalClosed.extend previous.names
              (NaturalHelpers.interpretation entries originalBindings) name initializer path = some checked.value
            simp only [NaturalClosed.extend,if_pos same]
            exact checked.computed
          · simp only [Form.evaluate,dot_nil,Int.add_zero]⟩
      else
        let result ← previous.reader laterBindings fuel path
        return ⟨result.form,by
          intro values held
          obtain ⟨n,computed,meaning⟩ := result.correct values held
          refine ⟨n,?_,meaning⟩
          change NaturalClosed.extend previous.names
            (NaturalHelpers.interpretation entries originalBindings) name initializer path = some n
          simp only [NaturalClosed.extend,if_neg same]
          exact computed⟩⟩

abbrev Witness {α : Type} (action : WorkM α) :=
  {value : α // ∃ work left,action.run work = (.ok value,left)}

def originalBindings (sources : Sources) (caller : String) (entries : List NaturalHelpers.Entry)
    (scope : List String) (expression : Expr) : WorkM (List (Path × NaturalCatalog.Key)) :=
  NaturalCatalog.scopedExpressionBindings sources (entries.map (·.original)) caller scope [expression]

structure Checked (sources : Sources) (caller : String) (entries : List NaturalHelpers.Entry)
    (environment : Environment entries) (scope : List String) (expression : Expr) where
  bindings : Witness (originalBindings sources caller entries scope expression)
  result : NaturalClosed.Checked environment.names
    (NaturalHelpers.interpretation entries bindings.val) expression

def read (sources : Sources) (caller : String) (entries : List NaturalHelpers.Entry)
    (environment : Environment entries) (scope : List String) (expression : Expr) :
    WorkM (Checked sources caller entries environment scope expression) := do
  let bindings : Witness (originalBindings sources caller entries scope expression) ←
    NaturalAffine.witness (originalBindings sources caller entries scope expression)
  let result ← NaturalClosed.read environment.names entries bindings.val
    (environment.reader bindings.val) expression
  return @Checked.mk sources caller entries environment scope expression bindings result

structure Bound (sources : Sources) (caller : String) (entries : List NaturalHelpers.Entry)
    (environment : Environment entries) (scope : List String) (name : String) (expression : Expr) where
  unbound : name ∉ scope
  checked : Checked sources caller entries environment scope expression

def bind (sources : Sources) (caller : String) (entries : List NaturalHelpers.Entry)
    (environment : Environment entries) (scope : List String) (name : String) (expression : Expr) :
    WorkM (Bound sources caller entries environment scope name expression) := do
  exactWork (Exact.charge (name.utf8ByteSize+(scope.map String.utf8ByteSize).sum+1))
  if unbound : name ∉ scope then
    let checked ← read sources caller entries environment scope expression
    return ⟨unbound,checked⟩
  else throw .request

def Bound.environment {sources caller entries environment scope name expression}
    (bound : Bound sources caller entries environment scope name expression) : Environment entries :=
  extend entries environment bound.checked.bindings.val name expression bound.checked.result

end QleisliKernel.SourceTypes.LexicalNatural
