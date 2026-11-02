import QleisliKernel.SourceTypes.StaticInstantiation
import QleisliKernel.SourceTypes.GenericLexicalNatural
import QleisliKernel.SourceTypes.StaticBindings
import QleisliKernel.SourceTypes.CallSyntax

/-! Caller-to-callee implication for original ordinary static applications.
Original actual expressions are normalized in the caller's symbolic lexical
environment, then simultaneously substituted in the callee's original frame.
The result proves its original predicates for every caller valuation satisfying
the original premises. Selected closed actuals supply no proof of implication.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.StaticCallPremises
open Finite Semantics.SourceNatural Semantics.SourceAffine

private def adapt {α : Type} (value : Except String α) : WorkM α :=
  lift (value.mapError fun _ => .request)

def callerState {sources owner name original}
    (instantiation : @StaticInstantiation.Checked sources owner name original)
    (provided : Option (GenericLexicalNatural.SomeEnvironment sources)) :
    WorkM (GenericLexicalNatural.SomeEnvironment sources) := do
  match instantiation with
  | .closed _ =>
    guard provided.isNone .request
    match parsed : StaticHeaders.parse original.parsedHeader with
    | .error _ => throw .request
    | .ok header =>
      let header : StaticHeaders.Original sources owner name := ⟨original,header,parsed⟩
      let prepared ← StaticNatural.prepareOriginal header ["0"]
      pure ⟨owner,name,prepared.prepared,GenericLexicalNatural.initial prepared.prepared⟩
  | .static _ environment _ =>
    let state := provided.getD ⟨owner,name,environment.numeric,GenericLexicalNatural.initial environment.numeric⟩
    guard (state.owner == owner && state.name == name &&
      state.prepared.original.envelope.source == original.source &&
      state.prepared.original.envelope.declaration == original.declaration) .request
    pure state

/-- Shared original symbolic validation used by Nat and Basis actuals. Closed
callers may use their separately checked lexical constants; generic callers
must also preserve the exact original symbolic initializer interpretation. -/
def validateNatural {sources owner name original}
    (instantiation : @StaticInstantiation.Checked sources owner name original)
    (provided : Option (GenericLexicalNatural.SomeEnvironment sources)) (scope : List String)
    (expression : Expr) : WorkM Unit := do
  match instantiation with
  | .closed _ => guard provided.isNone .request
  | .static .. =>
    let state ← callerState instantiation provided
    GenericLexicalNatural.validate state owner scope expression

abbrev Meaning {sources} (state : GenericLexicalNatural.SomeEnvironment sources) :=
  state.environment.meaning

structure Known {sources} (state : GenericLexicalNatural.SomeEnvironment sources) where
  form : Form
  nonnegative : ∀ values,Meaning state values → 0 ≤ form.evaluate values

def readForm {sources} (state : GenericLexicalNatural.SomeEnvironment sources) (scope : List String)
    (formal : StaticHeaders.Formal) (argument : CallSyntax.Argument) : WorkM (Known state) := do
  match formal.kind with
  | .natural =>
    let expression ← adapt (StaticBindings.natural argument.tokens)
    let checked ← GenericLexicalNatural.read state.prepared state.environment scope expression.expression
    pure ⟨checked.normalized.form,by
      intro values held
      obtain ⟨n,_computed,same⟩ := checked.normalized.correct values held
      rw [same]
      omega⟩
  | _ =>
    let zero ← NaturalAffine.witness (NaturalAffine.constant (StaticHeaders.frame state.prepared.original).binders.length 0)
    pure ⟨zero.val,by
      intro values _held
      obtain ⟨before,after,ran⟩ := zero.property
      rw [NaturalAffine.constant_meaning _ _ _ _ _ ran]
      omega⟩

def readForms {sources} (state : GenericLexicalNatural.SomeEnvironment sources) (scope : List String)
    (formals : List StaticHeaders.Formal) (arguments : List CallSyntax.Argument) : WorkM (List (Known state)) := do
  guard (formals.length == arguments.length) .request
  (formals.zip arguments).mapM fun (formal,argument) => readForm state scope formal argument

def numbers {sources : Sources} {state : GenericLexicalNatural.SomeEnvironment sources}
    (forms : List (Known state)) (values : Valuation) : List Nat :=
  forms.map (fun form => (form.form.evaluate values).toNat)

private theorem related {sources : Sources} {state : GenericLexicalNatural.SomeEnvironment sources}
    (forms : List (Known state))
    (values : Valuation) (held : Meaning state values) :
    Related (fun (form : Form) (n : Nat) => form.evaluate values = (n : Int))
      (forms.map (·.form)) (numbers forms values) := by
  induction forms with
  | nil => exact .nil
  | cons form rest ih =>
    exact .cons (Int.toNat_of_nonneg (form.nonnegative values held)).symm ih

structure Transfer {sources owner name original targetOwner targetName}
    (instantiation : @StaticInstantiation.Checked sources owner name original)
    (provided : Option (GenericLexicalNatural.SomeEnvironment sources)) (scope : List String)
    (target : StaticHeaders.Original sources targetOwner targetName) (arguments : List CallSyntax.Argument) where
  state : GenericLexicalNatural.SomeEnvironment sources
  stateRead : ∃ before after,(callerState instantiation provided).run before = (.ok state,after)
  callee : StaticNatural.Prepared sources targetOwner targetName ["0"]
  originalHeader : callee.original = target
  forms : List (Known state)
  formsRead : ∃ before after,(readForms state scope target.header.formals arguments).run before = (.ok forms,after)
  count : forms.length = target.header.formals.length
  originalPredicates : ∀ values,Meaning state values →
    PredicatesTruth 128
      (NaturalFrames.names (StaticHeaders.frame target)
        (NaturalFrames.argumentValues (StaticHeaders.frame target) (numbers forms values)))
      (NaturalHelpers.interpretation callee.helpers callee.bindings) target.header.premises

/-- A whole-body symbolic traversal already authenticates its lexical state
from the original header and every original initializer. This variant never
closes that state or replaces it by the selected static argument values. -/
structure InState {sources : Sources} (state : GenericLexicalNatural.SomeEnvironment sources)
    (scope : List String) {targetOwner targetName}
    (target : StaticHeaders.Original sources targetOwner targetName) (arguments : List CallSyntax.Argument) where
  callee : StaticNatural.Prepared sources targetOwner targetName ["0"]
  originalHeader : callee.original = target
  forms : List (Known state)
  formsRead : ∃ before after,(readForms state scope target.header.formals arguments).run before = (.ok forms,after)
  count : forms.length = target.header.formals.length
  originalPredicates : ∀ values,Meaning state values →
    PredicatesTruth 128
      (NaturalFrames.names (StaticHeaders.frame target)
        (NaturalFrames.argumentValues (StaticHeaders.frame target) (numbers forms values)))
      (NaturalHelpers.interpretation callee.helpers callee.bindings) target.header.premises

def readInState {sources : Sources} (state : GenericLexicalNatural.SomeEnvironment sources)
    (scope : List String) {targetOwner targetName}
    (target : StaticHeaders.Original sources targetOwner targetName) (arguments : List CallSyntax.Argument) :
    WorkM (InState state scope target arguments) := do
  let helpers : NaturalHelpers.Checked sources := ⟨state.prepared.helpers,state.prepared.helpersPrepared⟩
  let callee ← StaticNatural.prepareOriginalWithHelpers target ["0"] helpers
  let forms ← NaturalAffine.witness (readForms state scope target.header.formals arguments)
  if count : forms.val.length = target.header.formals.length then
    let replacements := NaturalFrames.replacements (StaticHeaders.frame callee.prepared.original) (forms.val.map (·.form))
    let premises ← NaturalHelpers.implyPremises state.environment.context
      (StaticHeaders.frame state.prepared.original).binders.length replacements callee.prepared.scope.numeric
    pure ⟨callee.prepared,callee.originalHeader,forms.val,by with_reducible exact forms.property,count,by
      intro values held
      have substitution := NaturalFrames.replacements_meaning (StaticHeaders.frame callee.prepared.original)
        (forms.val.map (·.form)) (numbers forms.val values) values (related forms.val values held)
      have numeric := premises.proof values held
      change NaturalPrepare.NumericsTruth callee.prepared.scope.numeric
        (NaturalSubstitute.replacementValues replacements values) at numeric
      rw [substitution] at numeric
      have natural := NaturalFrames.argumentValues_natural (StaticHeaders.frame callee.prepared.original) (numbers forms.val values)
      have predicates := (callee.prepared.scope.correct _ natural).mp numeric
      have frameSame := congrArg
        (fun (header : StaticHeaders.Original sources targetOwner targetName) => StaticHeaders.frame header) callee.originalHeader
      have premisesSame := congrArg
        (fun (header : StaticHeaders.Original sources targetOwner targetName) => header.header.premises) callee.originalHeader
      simpa only [frameSame,premisesSame] using predicates⟩
  else throw .request

inductive Checked {sources owner name original targetOwner targetName}
    (instantiation : @StaticInstantiation.Checked sources owner name original)
    (provided : Option (GenericLexicalNatural.SomeEnvironment sources)) (scope : List String)
    (target : StaticHeaders.Original sources targetOwner targetName) (arguments : List CallSyntax.Argument) where
  | empty (noPremises : target.header.premises = [])
  | transferred (transfer : Transfer instantiation provided scope target arguments)

def read {sources owner name original targetOwner targetName}
    (instantiation : @StaticInstantiation.Checked sources owner name original)
    (provided : Option (GenericLexicalNatural.SomeEnvironment sources)) (scope : List String)
    (target : StaticHeaders.Original sources targetOwner targetName) (arguments : List CallSyntax.Argument) :
    WorkM (Checked instantiation provided scope target arguments) := do
  match noPremises : target.header.premises with
  | [] => pure (.empty noPremises)
  | _ :: _ =>
    let state ← NaturalAffine.witness (callerState instantiation provided)
    let given ← readInState state.val scope target arguments
    pure (.transferred ⟨state.val,by with_reducible exact state.property,given.callee,given.originalHeader,
      given.forms,given.formsRead,given.count,given.originalPredicates⟩)

end QleisliKernel.SourceTypes.StaticCallPremises
