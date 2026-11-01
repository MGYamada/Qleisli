import QleisliKernel.SourceTypes.NaturalPrepare

/-! Bind acyclic original helper definitions to generic normalization and exact
simultaneous calls. Reference calls execute original predicates/body; checked
templates only propose affine results, with proofs of that source interpretation.
No producer template or success receipt enters this path.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.NaturalHelpers
open Semantics.SourceNatural Semantics.SourceAffine NaturalAffine NaturalPredicates NaturalPrepare

structure Entry where
  original : NaturalCatalog.Original
  calls : Calls
  prepared : Prepared original calls

def Entry.frame (entry : Entry) := NaturalFrames.original entry.original

def Entry.reference (entry : Entry) : Definition :=
  ⟨entry.original.helper.parameters.length,
    fun arguments => NaturalFrames.names entry.frame (NaturalFrames.argumentValues entry.frame arguments),
    entry.original.helper.premises,entry.original.helper.body⟩

def Entry.invoke (entry : Entry) (arguments : List Nat) : Option Nat :=
  entry.reference.execute entry.calls arguments

/-- Only canonical keys resolved from original source are present in bindings. -/
def interpretation (entries : List Entry) (bindings : List (Path × NaturalCatalog.Key)) : Calls :=
  fun path arguments => do
    let (_,key) ← bindings.find? (fun binding => binding.1 == path)
    let entry ← entries.find? (fun entry => entry.original.key == key)
    entry.invoke arguments

private def premiseLoop {meaning : Valuation → Prop} (context : Context meaning)
    (variables : Nat) (replacements : List Form) :
    Nat → (pending : List Numeric) →
      WorkM (Established (∀ values,meaning values → NumericsTruth pending
        (NaturalSubstitute.replacementValues replacements values))) :=
  Nat.rec (fun _ => throw .limit) (fun _ recurse pending => do
    Finite.exactWork (Exact.charge 1)
    match pending with
    | [] => return ⟨by intro _ _ _ member; cases member⟩
    | fact :: rest =>
      let a ← NaturalSubstitute.substitute variables fact.left replacements
      let b ← NaturalSubstitute.substitute variables fact.right replacements
      let proved ← implies context a.form fact.comparison b.form
      let remaining ← recurse rest
      return ⟨by
        intro values held other member
        rcases List.mem_cons.mp member with same | tail
        · subst other
          change fact.comparison.Relation _ _
          rw [← a.correct values,← b.correct values]
          exact proved.proof values held
        · exact remaining.proof values held other tail⟩)

/-- The original helper-call checker is independent of how the caller's
Nat names are interpreted. Checked aliases may provide their own original-name
meaning; every actual expression still carries its computation proof. -/
def readCall (variables : Nat) (names : Valuation → Names) (entries : List Entry)
    (bindings : List (Path × NaturalCatalog.Key)) {meaning : Valuation → Prop}
    (context : Context meaning) (fuel : Nat) (path : Path) (arguments : List Expr)
    (args : NaturalNormalize.Arguments names (interpretation entries bindings) meaning fuel arguments) :
    WorkM (NaturalNormalize.Result names (interpretation entries bindings) meaning
      (fuel+1) (.call path arguments)) := do
  Finite.exactWork (Exact.charge ((bindings.map (fun binding =>
    (binding.1.map String.utf8ByteSize).sum+binding.2.moduleName.utf8ByteSize+
    binding.2.declarationName.utf8ByteSize+1)).sum+entries.length+1))
  match bound : bindings.find? (fun binding => binding.1 == path) with
  | none => throw .request
  | some binding =>
    match selected : entries.find? (fun entry => entry.original.key == binding.2) with
    | none => throw .request
    | some entry =>
      if arity : args.forms.length = entry.original.helper.parameters.length then
        Finite.exactWork (Exact.charge (entry.frame.binders.length*(args.forms.length+1)+1))
        let replacements := NaturalFrames.replacements entry.frame args.forms
        let premises ← premiseLoop context variables replacements
          (entry.prepared.scope.numeric.length+1) entry.prepared.scope.numeric
        let result ← NaturalSubstitute.substitute variables entry.prepared.body.form replacements
        return ⟨result.form,by
          intro values held
          obtain ⟨numbers,argumentExpressions,argumentForms⟩ := args.correct values held
          let actual := NaturalFrames.argumentValues entry.frame numbers
          have substitution := NaturalFrames.replacements_meaning entry.frame args.forms numbers values argumentForms
          have numeric := premises.proof values held
          change NumericsTruth entry.prepared.scope.numeric
            (NaturalSubstitute.replacementValues (NaturalFrames.replacements entry.frame args.forms) values) at numeric
          rw [substitution] at numeric
          have natural := NaturalFrames.argumentValues_natural entry.frame numbers
          have originalPremises := (entry.prepared.scope.correct actual natural).mp numeric
          obtain ⟨n,body,same⟩ := entry.prepared.body.correct actual ⟨natural,originalPremises⟩
          have count : numbers.length = entry.reference.arity := by
            have related := argumentForms.length_eq
            exact related.symm.trans arity
          have invoked : entry.invoke numbers = some n :=
            Definition.execute_of_body entry.reference entry.calls numbers n count originalPremises body
          have call : interpretation entries bindings path numbers = some n := by
            simp only [interpretation,bound]
            change (do
              let chosen ← entries.find? (fun item => item.original.key == binding.2)
              chosen.invoke numbers) = some n
            rw [selected]
            exact invoked
          refine ⟨n,evaluate_call _ _ _ _ _ _ _ argumentExpressions call,?_⟩
          rw [result.correct values,substitution]
          exact same⟩
      else throw .request

/-- Existing original-formal callers use exactly the same helper computation. -/
def reader (frame : NaturalFrames.Frame) (entries : List Entry)
    (bindings : List (Path × NaturalCatalog.Key)) : CallsReader frame (interpretation entries bindings) :=
  ⟨fun context _natural fuel path arguments args =>
    readCall frame.binders.length (NaturalFrames.names frame) entries bindings context fuel path arguments args⟩

/-- Validate every original helper, including disconnected/private definitions,
in original dependency order before exposing any call interpretation. -/
def prepare (sources : Sources) : WorkM (List Entry) := do
  let ordered ← NaturalCatalog.prepare sources
  ordered.foldlM (fun entries original => do
    Finite.exactWork (Exact.charge (entries.length+original.helper.parameters.length+1))
    let calls := interpretation entries original.calls
    let checked ← NaturalPrepare.check original calls (reader (NaturalFrames.original original) entries original.calls)
    return (⟨original,calls,checked⟩ : Entry) :: entries) []

end QleisliKernel.SourceTypes.NaturalHelpers
