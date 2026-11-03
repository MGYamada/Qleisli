import QleisliKernel.SourceTypes.SourceRuntimeBranches

/-! Complete ordinary enum-match result merges. A fresh phi retains every
original arm's actual owner; no width-only owner permutation or selected arm
can determine the result metadata.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.SourceRuntimeMatching
open QleisliKernel QleisliKernel.SourceTypes SourceRuntimeValues

structure Phi where
  output : Semantics.SourceOwners.Owner
  inputs : List Semantics.SourceOwners.Owner
  sameType : ∀ input ∈ inputs,input.basis = output.basis
  deriving DecidableEq, Repr

instance : BEq Phi where
  beq first second := decide (first = second)

private def choose (condition : Expression) (values : List (Nat × Expression)) : Expression :=
  match values.foldr (fun (ordinal,value) rest =>
    some (match rest with
      | none => value
      | some tail => .choose (.equalsOrdinal ordinal condition) value tail)) (none : Option Expression) with
  | none => .unit
  | some expression => expression

def merge (condition : Expression) (ordinals : List Nat) (arms : List Value) (nextOrdinal : Nat) :
    Except String (Value × List Phi) := do
  let some first := arms.head? | throw "match has no original arm"
  if ordinals.length != arms.length || !(arms.all fun arm => arm.length == first.length) then
    throw "match complete result forest shape"
  (List.range first.length).foldlM (fun (value,phis) index => do
    let some head := first[index]? | throw "match result field"
    let column ← arms.mapM fun arm => do
      let some atom := arm[index]? | throw "match result field"
      pure atom
    match head with
    | .owner first =>
      let inputs ← column.mapM fun atom => match atom with
        | .owner owner => pure owner
        | _ => throw "match owner result shape"
      if sameType : inputs.all (fun owner => decide (owner.basis = first.basis)) = true then
        let output : Semantics.SourceOwners.Owner := ⟨nextOrdinal+phis.length,first.basis⟩
        have typed : ∀ input ∈ inputs,input.basis = output.basis := by
          intro input member
          exact of_decide_eq_true ((List.all_eq_true.mp sameType) input member)
        return (value ++ [.owner output],phis ++ [⟨output,inputs,typed⟩])
      else throw "match owner original nominal types"
    | .ordinary basis _ =>
      let values ← column.mapM fun atom => match atom with
        | .ordinary actual expression => do
          if actual != basis then throw "match ordinary nominal types"
          pure expression
        | _ => throw "match ordinary result shape"
      return (value ++ [.ordinary basis (choose condition (ordinals.zip values))],phis)
    | .tuple arity =>
      if column.all (fun atom => match atom with | .tuple actual => actual == arity | _ => false) then
        return (value ++ [.tuple arity],phis)
      else throw "match result tuple arity") ([],[])

end QleisliKernel.SourceTypes.SourceRuntimeMatching
