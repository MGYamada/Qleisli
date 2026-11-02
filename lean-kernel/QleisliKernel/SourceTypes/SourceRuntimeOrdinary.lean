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
        · simp only [readAtom,computed,finite,if_pos inside,bind,Except.bind] at read
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
