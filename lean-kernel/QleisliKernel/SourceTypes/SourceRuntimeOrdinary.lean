import QleisliKernel.SourceTypes.SourceRuntimeValues

/-! Actual symbolic result extraction against the independent ordinary
valuation. Source body generation, actual SSA/measurement/phi correspondence and
complete native instrument equations remain separate checked obligations.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.SourceRuntimeOrdinary
open QleisliKernel
open Semantics.SourceOrdinary

def readAtom (values : Valuation) : Atom → Except String ResultAtom
  | .owner owner => pure (.owner owner)
  | .tuple arity => pure (.tuple arity)
  | .ordinary basis expression => do
    let some ordinal := evaluate values expression | throw "undefined original ordinary value"
    let some dimension := Semantics.FiniteCarrier.dimension basis | throw "invalid original ordinary type"
    if ordinal < dimension then pure (.ordinary basis ordinal)
    else throw "ordinary result outside its exact logical carrier"

def extract (values : Valuation) (value : Value) : Except String Result :=
  value.mapM (readAtom values)

/-- A callee valuation induced by actual caller expressions and owner roles.
Measurement identities keep their original site and the complete caller path;
no SSA number or produced history table defines this valuation. -/
def calledValuation (values : Valuation) (site : Site)
    (owners : List Semantics.SourceOwners.Owner)
    (inputs : List (Semantics.FiniteCarrier.Basis × Expression)) : Valuation :=
  { inputs := fun ordinal => do
      let (_,expression) ← inputs[ordinal]?
      evaluate values expression
    basisInputs := values.basisInputs
    measured := fun origin calls owner =>
      match SourceRuntimeValues.mappedOwner owners owner with
      | .error _ => none
      | .ok actual => values.measured origin (site :: calls) actual }

/-- Actual executable source expression transport agrees with independent
valuation substitution. This is a call-value lemma, not source AST lowering or
agreement with native SSA, code-space maps or complete instruments. -/
theorem expressionTransport_reference (values : Valuation) (site : Site)
    (owners : List Semantics.SourceOwners.Owner)
    (inputs : List (Semantics.FiniteCarrier.Basis × Expression)) (expression result : Expression)
    (transported : SourceRuntimeValues.expressionTransport site owners inputs expression = .ok result) :
    evaluate values result = evaluate (calledValuation values site owners inputs) expression := by
  induction expression generalizing result with
  | input ordinal =>
    cases selected : inputs[ordinal]? with
    | none => simp [SourceRuntimeValues.expressionTransport,selected] at transported
    | some input =>
      obtain ⟨basis,actual⟩ := input
      simp only [SourceRuntimeValues.expressionTransport,selected] at transported
      cases transported
      simp only [evaluate,calledValuation,selected,bind,Option.bind]
  | basisInput ordinal =>
    cases transported
    rfl
  | unit => cases transported; rfl
  | bit bit => cases transported; rfl
  | ordinal ordinal => cases transported; rfl
  | measured origin calls owner =>
    cases found : SourceRuntimeValues.mappedOwner owners owner with
    | error error =>
      simp only [SourceRuntimeValues.expressionTransport,found] at transported
      change (Except.error error : Except String Expression) = .ok result at transported
      cases transported
    | ok actual =>
      simp only [SourceRuntimeValues.expressionTransport,found] at transported
      cases transported
      simp only [evaluate,calledValuation,found]
  | project value ordinal _ih =>
    cases read : SourceRuntimeValues.expressionTransport site owners inputs value with
    | error error =>
      simp only [SourceRuntimeValues.expressionTransport,read] at transported
      change (Except.error error : Except String Expression) = .ok result at transported
      cases transported
    | ok actual =>
      simp only [SourceRuntimeValues.expressionTransport,read] at transported
      cases transported
      rfl
  | field stride dimension value ih =>
    cases read : SourceRuntimeValues.expressionTransport site owners inputs value with
    | error error =>
      simp only [SourceRuntimeValues.expressionTransport,read] at transported
      change (Except.error error : Except String Expression) = .ok result at transported
      cases transported
    | ok actual =>
      simp only [SourceRuntimeValues.expressionTransport,read] at transported
      cases transported
      simp only [evaluate,ih actual read]
  | equalsOrdinal ordinal value ih =>
    cases read : SourceRuntimeValues.expressionTransport site owners inputs value with
    | error error =>
      simp only [SourceRuntimeValues.expressionTransport,read] at transported
      change (Except.error error : Except String Expression) = .ok result at transported
      cases transported
    | ok actual =>
      simp only [SourceRuntimeValues.expressionTransport,read] at transported
      cases transported
      simp only [evaluate,ih actual read]
  | not value ih =>
    cases read : SourceRuntimeValues.expressionTransport site owners inputs value with
    | error error =>
      simp only [SourceRuntimeValues.expressionTransport,read] at transported
      change (Except.error error : Except String Expression) = .ok result at transported
      cases transported
    | ok actual =>
      simp only [SourceRuntimeValues.expressionTransport,read] at transported
      cases transported
      simp only [evaluate,ih actual read]
  | combine stride first second firstIH secondIH =>
    cases firstRead : SourceRuntimeValues.expressionTransport site owners inputs first with
    | error error => simp [SourceRuntimeValues.expressionTransport,firstRead,bind,Except.bind] at transported
    | ok a =>
      cases secondRead : SourceRuntimeValues.expressionTransport site owners inputs second with
      | error error => simp [SourceRuntimeValues.expressionTransport,firstRead,secondRead,bind,Except.bind] at transported
      | ok b =>
        simp only [SourceRuntimeValues.expressionTransport,firstRead,secondRead] at transported
        cases transported
        simp only [evaluate,firstIH a firstRead,secondIH b secondRead]
  | xor first second firstIH secondIH =>
    cases firstRead : SourceRuntimeValues.expressionTransport site owners inputs first with
    | error error => simp [SourceRuntimeValues.expressionTransport,firstRead,bind,Except.bind] at transported
    | ok a =>
      cases secondRead : SourceRuntimeValues.expressionTransport site owners inputs second with
      | error error => simp [SourceRuntimeValues.expressionTransport,firstRead,secondRead,bind,Except.bind] at transported
      | ok b =>
        simp only [SourceRuntimeValues.expressionTransport,firstRead,secondRead] at transported
        cases transported
        simp only [evaluate,firstIH a firstRead,secondIH b secondRead]
  | and first second firstIH secondIH =>
    cases firstRead : SourceRuntimeValues.expressionTransport site owners inputs first with
    | error error => simp [SourceRuntimeValues.expressionTransport,firstRead,bind,Except.bind] at transported
    | ok a =>
      cases secondRead : SourceRuntimeValues.expressionTransport site owners inputs second with
      | error error => simp [SourceRuntimeValues.expressionTransport,firstRead,secondRead,bind,Except.bind] at transported
      | ok b =>
        simp only [SourceRuntimeValues.expressionTransport,firstRead,secondRead] at transported
        cases transported
        simp only [evaluate,firstIH a firstRead,secondIH b secondRead]
  | choose condition thenValue elseValue conditionIH thenIH elseIH =>
    cases conditionRead : SourceRuntimeValues.expressionTransport site owners inputs condition with
    | error error => simp [SourceRuntimeValues.expressionTransport,conditionRead,bind,Except.bind] at transported
    | ok selected =>
      cases thenRead : SourceRuntimeValues.expressionTransport site owners inputs thenValue with
      | error error => simp [SourceRuntimeValues.expressionTransport,conditionRead,thenRead,bind,Except.bind] at transported
      | ok a =>
        cases elseRead : SourceRuntimeValues.expressionTransport site owners inputs elseValue with
        | error error => simp [SourceRuntimeValues.expressionTransport,conditionRead,thenRead,elseRead,bind,Except.bind] at transported
        | ok b =>
          simp only [SourceRuntimeValues.expressionTransport,conditionRead,thenRead,elseRead] at transported
          cases transported
          simp only [evaluate,conditionIH selected conditionRead,thenIH a thenRead,elseIH b elseRead]

theorem readAtom_sound (values : Valuation) (atom : Atom) (result : ResultAtom)
    (read : readAtom values atom = .ok result) : AtomEvaluates values atom result := by
  cases atom with
  | owner owner => cases read; exact .owner owner
  | tuple arity => cases read; exact .tuple arity
  | ordinary basis expression =>
    cases computed : evaluate values expression with
    | none => simp [readAtom,computed] at read
    | some ordinal =>
      cases finite : Semantics.FiniteCarrier.dimension basis with
      | none => simp [readAtom,computed,finite] at read
      | some dimension =>
        by_cases inside : ordinal < dimension
        · simp only [readAtom,computed,finite,if_pos inside] at read
          cases read
          exact .ordinary basis expression ordinal dimension computed finite inside
        · simp [readAtom,computed,finite,inside] at read

theorem extract_sound (values : Valuation) (value : Value) (result : Result)
    (read : extract values value = .ok result) : Evaluates values value result := by
  change value.mapM (readAtom values) = .ok result at read
  induction value generalizing result with
  | nil =>
    simp only [List.mapM_nil] at read
    cases read
    exact .nil
  | cons atom rest ih =>
    simp only [List.mapM_cons] at read
    cases headRead : readAtom values atom with
    | error error => simp [headRead,bind,Except.bind] at read
    | ok head =>
      cases tailRead : rest.mapM (readAtom values) with
      | error error => simp [headRead,tailRead,bind,Except.bind] at read
      | ok tail =>
        simp only [headRead,tailRead,bind,Except.bind] at read
        have same : head :: tail = result := by
          exact Except.ok.inj read
        subst result
        exact .cons (readAtom_sound values atom head headRead) (ih tail tailRead)

end QleisliKernel.SourceTypes.SourceRuntimeOrdinary
