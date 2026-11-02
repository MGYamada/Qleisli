import QleisliKernel.SourceTypes.GenericTypeTrace

/-! Closing one ORIGINAL conditional basis obligation at its exact selected
instance. Active ports retain independent symbolic evaluations; an inactive
receipt proves the original accumulated static guard false. Neither case is an
injectivity proof. The corresponding full-domain original BasisEvent and native
body/code equation must still discharge every active obligation.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.GenericBasisInstance
open Finite Semantics.SourceAffine Semantics.SymbolicBasis

def contextValue (alternatives : List (List Form)) (values : Valuation) : Bool :=
  alternatives.any fun rows => rows.all fun row => decide (row.evaluate values ≤ 0)

theorem contextValue_truth (alternatives : List (List Form)) (values : Valuation) :
    contextValue alternatives values = true ↔ Satisfies alternatives values := by
  simp only [contextValue,List.any_eq_true,List.all_eq_true,decide_eq_true_eq,Satisfies,Holds]

def values {sources owner name original}
    (instantiation : @StaticInstantiation.Checked sources owner name original)
    (obligation : GenericTypeTrace.BasisObligation sources) : Valuation :=
  NaturalFrames.argumentValues (StaticHeaders.frame obligation.state.prepared.original)
    (StaticNatural.arguments obligation.state.prepared.original instantiation.arguments.naturals)

def parameters {sources owner name original}
    (instantiation : @StaticInstantiation.Checked sources owner name original)
    (obligation : GenericTypeTrace.BasisObligation sources) : Parameters := fun key => do
  if key.moduleName != owner || key.declarationName != name then none else do
    let formal ← obligation.state.prepared.original.header.formals[key.ordinal]?
    if formal.ordinal != key.ordinal || formal.kind != .basis then none else do
      let (_,basis) ← instantiation.arguments.bases.find? (·.1 == formal.name)
      pure basis

def Aligned {sources owner name original}
    (_instantiation : @StaticInstantiation.Checked sources owner name original)
    (obligation : GenericTypeTrace.BasisObligation sources) : Prop :=
  obligation.owner = owner ∧ obligation.name = name ∧
  obligation.state.owner = owner ∧ obligation.state.name = name ∧
  obligation.state.prepared.original.envelope.source = original.source ∧
  obligation.state.prepared.original.envelope.declaration = original.declaration ∧
  obligation.state.prepared.original.envelope.occurrence.header = original.occurrence.header ∧
  obligation.state.prepared.original.envelope.occurrence.body = original.occurrence.body ∧
  obligation.state.prepared.original.envelope.occurrence.openBrace = original.occurrence.openBrace ∧
  obligation.state.prepared.original.envelope.occurrence.closeBrace = original.occurrence.closeBrace

structure Active {sources owner name original}
    (instantiation : @StaticInstantiation.Checked sources owner name original)
    (obligation : GenericTypeTrace.BasisObligation sources) where
  input : Semantics.FiniteCarrier.Basis
  output : Semantics.FiniteCarrier.Basis
  held : obligation.state.environment.meaning (values instantiation obligation)
  inputRead : evaluate (parameters instantiation obligation) (values instantiation obligation) obligation.input = some input
  outputRead : evaluate (parameters instantiation obligation) (values instantiation obligation) obligation.output = some output

inductive Status {sources owner name original}
    (instantiation : @StaticInstantiation.Checked sources owner name original)
    (obligation : GenericTypeTrace.BasisObligation sources) where
  | inactive (guardFalse : ¬obligation.state.environment.meaning (values instantiation obligation)) :
      Status instantiation obligation
  | active (ports : Active instantiation obligation) : Status instantiation obligation

structure Binding {sources owner name original}
    (instantiation : @StaticInstantiation.Checked sources owner name original)
    (obligation : GenericTypeTrace.BasisObligation sources) where
  aligned : Aligned instantiation obligation
  status : Status instantiation obligation

def closeBasis {sources owner name original}
    (instantiation : @StaticInstantiation.Checked sources owner name original)
    (obligation : GenericTypeTrace.BasisObligation sources) : WorkM (Binding instantiation obligation) := do
  exactWork (Exact.charge (32*(original.source.utf8ByteSize+
    obligation.state.prepared.original.envelope.source.utf8ByteSize+
    GenericValues.codeFields obligation.input+GenericValues.codeFields obligation.output+
    (obligation.state.environment.context.alternatives.map fun rows =>
      (rows.map fun row => row.coefficients.length+2).sum).sum+1)))
  if aligned : Aligned instantiation obligation then
    let actual := values instantiation obligation
    let context := obligation.state.environment.context
    if held : contextValue context.alternatives actual = true then
      have meaning := (context.correct actual).mp ((contextValue_truth _ _).mp held)
      match inputRead : evaluate (parameters instantiation obligation) actual obligation.input with
      | none => throw .request
      | some input =>
        match outputRead : evaluate (parameters instantiation obligation) actual obligation.output with
        | none => throw .request
        | some output => pure ⟨aligned,.active ⟨input,output,meaning,inputRead,outputRead⟩⟩
    else
      pure ⟨aligned,.inactive (by
        intro meaning
        exact held ((contextValue_truth _ _).mpr ((context.correct actual).mpr meaning)))⟩
  else throw .request

end QleisliKernel.SourceTypes.GenericBasisInstance
