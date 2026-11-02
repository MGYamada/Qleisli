import QleisliKernel.Semantics.SourceOwners

/-! Independent logical ordinary-value expressions and their valuation.
Inputs and measurement histories are abstract source identities, never Raw SSA
numbers or producer tables. This reference imports no parser or checker and
does not itself give a source/native preservation theorem.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Semantics.SourceOrdinary
open SourceOwners

structure Site where
  moduleName : String
  functionName : String
  offset : Nat
  deriving BEq, DecidableEq, Repr

inductive Expression where
  | input (ordinal : Nat)
  | basisInput (ordinal : Nat)
  | unit
  | bit (value : Bool)
  | ordinal (value : Nat)
  | measured (origin : Site) (calls : List Site) (owner : Owner)
  | project (value : Expression) (ordinal : Nat)
  | combine (stride : Nat) (first second : Expression)
  | field (stride dimension : Nat) (receiver : Expression)
  | not (value : Expression)
  | xor (first second : Expression)
  | and (first second : Expression)
  | choose (condition thenValue elseValue : Expression)
  deriving BEq, DecidableEq, Repr

structure Valuation where
  inputs : Nat → Option Nat
  basisInputs : Nat → Option Nat
  measured : Site → List Site → Owner → Option Nat

/-- Logical first-component-fast ordinals. Both Boolean operands are strict;
only the selected branch of choose is evaluated. The obsolete untyped project
placeholder has no value; actual nominal fields use their exact stride and
cardinality. Code-space and effect judgments remain separate. -/
def evaluate (values : Valuation) : Expression → Option Nat
  | .input ordinal => values.inputs ordinal
  | .basisInput ordinal => values.basisInputs ordinal
  | .unit => some 0
  | .bit value => some (if value then 1 else 0)
  | .ordinal value => some value
  | .measured origin calls owner => values.measured origin calls owner
  | .project .. => none
  | .combine stride first second => do
    if stride == 0 then none else do
      let first ← evaluate values first
      let second ← evaluate values second
      if first ≥ stride then none else some (first+stride*second)
  | .field stride dimension receiver => do
    if stride == 0 || dimension == 0 then none else do
      let receiver ← evaluate values receiver
      some ((receiver/stride)%dimension)
  | .not value => do
    let value ← evaluate values value
    if value ≥ 2 then none else some (1-value)
  | .xor first second => do
    let first ← evaluate values first
    let second ← evaluate values second
    if first ≥ 2 || second ≥ 2 then none else some (if first == second then 0 else 1)
  | .and first second => do
    let first ← evaluate values first
    let second ← evaluate values second
    if first ≥ 2 || second ≥ 2 then none else some (if first == 1 && second == 1 then 1 else 0)
  | .choose condition thenValue elseValue => do
    let condition ← evaluate values condition
    if condition ≥ 2 then none else if condition == 1 then evaluate values thenValue else evaluate values elseValue

inductive ResultAtom where
  | owner (value : Owner)
  | ordinary (basis : FiniteCarrier.Basis) (ordinal : Nat)
  | tuple (arity : Nat)
  deriving BEq, DecidableEq, Repr

abbrev Result := List ResultAtom

inductive Atom where
  | owner (value : Owner)
  | ordinary (basis : FiniteCarrier.Basis) (expression : Expression)
  | tuple (arity : Nat)
  deriving BEq, DecidableEq, Repr

abbrev Value := List Atom

inductive AtomEvaluates (values : Valuation) : Atom → ResultAtom → Prop where
  | owner (value : Owner) : AtomEvaluates values (.owner value) (.owner value)
  | tuple (arity : Nat) : AtomEvaluates values (.tuple arity) (.tuple arity)
  | ordinary (basis : FiniteCarrier.Basis) (expression : Expression) (ordinal dimension : Nat)
      (computed : evaluate values expression = some ordinal)
      (finite : FiniteCarrier.dimension basis = some dimension) (inside : ordinal < dimension) :
      AtomEvaluates values (.ordinary basis expression) (.ordinary basis ordinal)

inductive Evaluates (values : Valuation) : Value → Result → Prop where
  | nil : Evaluates values [] []
  | cons {atom result rest results} (head : AtomEvaluates values atom result)
      (tail : Evaluates values rest results) : Evaluates values (atom :: rest) (result :: results)

end QleisliKernel.Semantics.SourceOrdinary
