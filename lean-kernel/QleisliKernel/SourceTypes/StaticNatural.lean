import QleisliKernel.SourceTypes.StaticHeaders

/-! Generic Nat expressions under the selected original runtime header.
Ordered premises and expressions are normalized before closed arguments enter.
Existing original-helper interpretation and simultaneous substitution supply
the exact value proof. Callers must bind expression tokens to their actual
source type occurrence; this component grants no execution or operation access.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.StaticNatural
open Finite Semantics.SourceNatural Semantics.SourceAffine

structure Prepared (sources : Sources) (owner name : String) (tokens : List String) where
  original : StaticHeaders.Original sources owner name
  helpers : List NaturalHelpers.Entry
  helpersPrepared : ∃ work left,
    (NaturalHelpers.prepare sources).run work = (.ok helpers,left)
  expression : Expr
  parsed : NaturalSyntax.read tokens = .ok expression
  bindings : List (Path × NaturalCatalog.Key)
  resolved : ∃ work left,
    (NaturalCatalog.scopedExpressionBindings sources (helpers.map (·.original)) owner
      (original.header.formals.map (·.name))
      (expression :: original.header.premises.flatMap (fun p => [p.left,p.right]))).run work =
      (.ok bindings,left)
  scope : NaturalPrepare.Scope (StaticHeaders.frame original)
    (NaturalHelpers.interpretation helpers bindings) original.header.premises
  normalized : NaturalNormalize.Result (NaturalFrames.names (StaticHeaders.frame original))
    (NaturalHelpers.interpretation helpers bindings)
    (NaturalPrepare.Meaning (StaticHeaders.frame original)
      (NaturalHelpers.interpretation helpers bindings) original.header.premises) 128 expression

def prepare (sources : Sources) (owner name : String) (tokens : List String) :
    WorkM (Prepared sources owner name tokens) := do
  let original ← StaticHeaders.read sources owner name
  let helpers ← NaturalAffine.witness (NaturalHelpers.prepare sources)
  exactWork (Exact.charge ((tokens.map String.utf8ByteSize).sum+tokens.length+1))
  match parsed : NaturalSyntax.read tokens with
  | .error _ => throw .request
  | .ok expression =>
    let bindings ← NaturalAffine.witness
      (NaturalCatalog.scopedExpressionBindings sources (helpers.val.map (·.original)) owner
        (original.header.formals.map (·.name))
        (expression :: original.header.premises.flatMap (fun p => [p.left,p.right])))
    let frame := StaticHeaders.frame original
    let calls := NaturalHelpers.interpretation helpers.val bindings.val
    let callReader := NaturalHelpers.reader frame helpers.val bindings.val
    let scope ← NaturalPrepare.checkPremises frame calls callReader original.header.premises
    let normalized ← NaturalNormalize.normalize frame.binders.length scope.context
      ⟨NaturalFrames.readName frame calls (fun _ held => held.1),
        callReader.read scope.context (fun _ held => held.1)⟩ 128 expression
    return ⟨original,helpers.val,by with_reducible exact helpers.property,
      expression,parsed,bindings.val,by with_reducible exact bindings.property,scope,normalized⟩

abbrev Bindings := List (String × Nat)

/-- The original mixed-kind ordinals are preserved. Non-Nat entries never
become Nat binders, so their placeholder cannot supply an arithmetic name. -/
def arguments {sources owner name} (original : StaticHeaders.Original sources owner name)
    (bindings : Bindings) : List Nat :=
  original.header.formals.map fun formal =>
    if formal.kind == .natural then
      (bindings.find? (fun binding => binding.1 == formal.name)).map (·.2) |>.getD 0
    else 0

def bindingsMatch {sources owner name} (original : StaticHeaders.Original sources owner name)
    (bindings : Bindings) : Bool :=
  let expected := original.header.formals.filter (·.kind == .natural)
  bindings.length == expected.length &&
    expected.all (fun formal => (bindings.filter (fun binding => binding.1 == formal.name)).length == 1) &&
    bindings.all (fun binding => binding.2 ≤ 4294967295)

private def constants (numbers : List Nat) : List Form :=
  numbers.map (fun (n : Nat) => ⟨(n : Int),[]⟩)

private theorem constants_related (numbers : List Nat) (values : Valuation) :
    Related (fun (form : Form) (n : Nat) => form.evaluate values = (n : Int))
      (constants numbers) numbers := by
  induction numbers with
  | nil => exact .nil
  | cons n rest ih =>
    exact .cons (by simp [Form.evaluate,dot_nil]) ih

private def satisfies (numeric : List NaturalPrepare.Numeric) (values : Valuation) : Bool :=
  numeric.all fun fact => fact.comparison.test (fact.left.evaluate values) (fact.right.evaluate values)

private theorem satisfies_truth (numeric : List NaturalPrepare.Numeric) (values : Valuation)
    (ok : satisfies numeric values = true) : NaturalPrepare.NumericsTruth numeric values := by
  intro fact member
  exact (Comparison.test_relation _ _ _).mp ((List.all_eq_true.mp ok) fact member)

structure Closed {sources owner name tokens} (prepared : Prepared sources owner name tokens)
    (bindings : Bindings) where
  value : Nat
  bounded : value ≤ 4294967295
  matched : bindingsMatch prepared.original bindings = true
  premises : PredicatesTruth 128
    (NaturalFrames.names (StaticHeaders.frame prepared.original)
      (NaturalFrames.argumentValues (StaticHeaders.frame prepared.original)
        (arguments prepared.original bindings)))
    (NaturalHelpers.interpretation prepared.helpers prepared.bindings) prepared.original.header.premises
  meaning : Value
    (NaturalFrames.names (StaticHeaders.frame prepared.original)
      (NaturalFrames.argumentValues (StaticHeaders.frame prepared.original)
        (arguments prepared.original bindings)))
    (NaturalHelpers.interpretation prepared.helpers prepared.bindings) prepared.expression value

/-- Closing cannot repair an invalid generic expression or late premise: a
Prepared value comes only from the prior generic check at the external gate. -/
def close {sources owner name tokens} (prepared : Prepared sources owner name tokens)
    (bindings : Bindings) : WorkM (Closed prepared bindings) := do
  guard (bindings.length ≤ 32) .limit
  exactWork (Exact.charge ((bindings.map (fun b => b.1.utf8ByteSize+1)).sum*
    (prepared.original.header.formals.length+1)+1))
  if matched : bindingsMatch prepared.original bindings = true then
    let frame := StaticHeaders.frame prepared.original
    let numbers := arguments prepared.original bindings
    let values := NaturalFrames.argumentValues frame numbers
    exactWork (Exact.charge ((prepared.scope.numeric.length+1)*(frame.binders.length+1)*4))
    if satisfied : satisfies prepared.scope.numeric values = true then
      have natural := NaturalFrames.argumentValues_natural frame numbers
      have premises := (prepared.scope.correct values natural).mp
        (satisfies_truth _ _ satisfied)
      let replacements := NaturalFrames.replacements frame (constants numbers)
      let closed ← NaturalSubstitute.substitute 0 prepared.normalized.form replacements
      if shape : closed.form.coefficients = [] then
        if bounds : 0 ≤ closed.form.constant ∧ closed.form.constant ≤ 4294967295 then
          let value := closed.form.constant.toNat
          return ⟨value,by omega,matched,premises,by
            obtain ⟨n,computed,same⟩ := prepared.normalized.correct values ⟨natural,premises⟩
            have substitution := NaturalFrames.replacements_meaning frame
              (constants numbers) numbers (fun _ => 0) (constants_related numbers (fun _ => 0))
            have integer := closed.correct (fun _ => 0)
            rw [substitution] at integer
            have numeric : closed.form.constant = (n : Int) := by
              simpa only [Form.evaluate,shape,dot_nil,Int.add_zero] using integer.trans same
            have equal : value = n := by omega
            rw [equal]
            exact evaluate_value _ _ _ _ _ computed⟩
        else throw .limit
      else throw .request
    else throw .request
  else throw .request

end QleisliKernel.SourceTypes.StaticNatural
