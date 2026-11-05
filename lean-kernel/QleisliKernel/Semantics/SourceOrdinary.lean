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
  | equalsOrdinal (ordinal : Nat) (value : Expression)
  | not (value : Expression)
  | xor (first second : Expression)
  | and (first second : Expression)
  | choose (condition thenValue elseValue : Expression)

/-- Executable descent on proper subexpressions. The structural size occurs
only in the termination proof, so no traversal computes a separate size or
imposes a depth limit. Each caller controls which children it evaluates. -/
def Expression.descend {motive : Expression → Type}
    (step : (e : Expression) → ((child : Expression) → sizeOf child < sizeOf e → motive child) → motive e)
    (e : Expression) : motive e :=
  WellFounded.fix (measure (fun x : Expression => sizeOf x)).wf step e

theorem Expression.descend_eq {motive : Expression → Type}
    (step : (e : Expression) → ((child : Expression) → sizeOf child < sizeOf e → motive child) → motive e)
    (e : Expression) : Expression.descend step e = step e (fun child _ => Expression.descend step child) :=
  WellFounded.fix_eq _ _ _

private def decideFields {p q : Prop} (first : Decidable p) (rest : Unit → Decidable q) : Decidable (p ∧ q) :=
  match first with
  | .isFalse no => .isFalse fun pair => no pair.1
  | .isTrue hp =>
    match rest () with
    | .isFalse no => .isFalse fun pair => no pair.2
    | .isTrue hq => .isTrue ⟨hp,hq⟩

instance : DecidableEq Expression :=
  Expression.descend (motive := fun left => (right : Expression) → Decidable (left = right)) (fun left => by
    cases left <;> intro smaller right <;> cases right <;> first
      | (apply isFalse; intro equal; cases equal; done)
      | (apply isTrue; rfl)
      | (simp
         repeat' (refine decideFields ?_ (fun _ => ?_))
         all_goals first | exact smaller _ (by decreasing_tactic) _ | infer_instance))

instance : BEq Expression := ⟨fun a b => decide (a = b)⟩

private def constructorFormat (name : String) (fields : List Std.Format) (prec : Nat) : Std.Format :=
  let head := Std.Format.text ("QleisliKernel.Semantics.SourceOrdinary.Expression." ++ name)
  let body := fields.foldl (fun text field => text ++ Std.Format.line ++ field) head
  Repr.addAppParen (Std.Format.nest (if prec ≥ max_prec then 1 else 2) body).group prec

instance : Repr Expression where
  reprPrec := Expression.descend (motive := fun _ => Nat → Std.Format) (fun e => match e with
    | .input i => fun _ => constructorFormat "input" [reprArg i]
    | .basisInput i => fun _ => constructorFormat "basisInput" [reprArg i]
    | .unit => fun _ => constructorFormat "unit" []
    | .bit b => fun _ => constructorFormat "bit" [reprArg b]
    | .ordinal i => fun _ => constructorFormat "ordinal" [reprArg i]
    | .measured origin calls owner => fun _ => constructorFormat "measured" [reprArg origin,reprArg calls,reprArg owner]
    | .project value i => fun child => constructorFormat "project" [child value (by decreasing_tactic) max_prec,reprArg i]
    | .combine stride a b => fun child => constructorFormat "combine"
        [reprArg stride,child a (by decreasing_tactic) max_prec,child b (by decreasing_tactic) max_prec]
    | .field stride dim value => fun child => constructorFormat "field"
        [reprArg stride,reprArg dim,child value (by decreasing_tactic) max_prec]
    | .equalsOrdinal i value => fun child => constructorFormat "equalsOrdinal" [reprArg i,child value (by decreasing_tactic) max_prec]
    | .not value => fun child => constructorFormat "not" [child value (by decreasing_tactic) max_prec]
    | .xor a b => fun child => constructorFormat "xor" [child a (by decreasing_tactic) max_prec,child b (by decreasing_tactic) max_prec]
    | .and a b => fun child => constructorFormat "and" [child a (by decreasing_tactic) max_prec,child b (by decreasing_tactic) max_prec]
    | .choose c t f => fun child => constructorFormat "choose"
        [child c (by decreasing_tactic) max_prec,child t (by decreasing_tactic) max_prec,child f (by decreasing_tactic) max_prec])

structure Valuation where
  inputs : Nat → Option Nat
  basisInputs : Nat → Option Nat
  measured : Site → List Site → Owner → Option Nat

/-- Logical first-component-fast ordinals. Both Boolean operands are strict;
only the selected branch of choose is evaluated. The obsolete untyped project
placeholder has no value; actual nominal fields use their exact stride and
cardinality. Code-space and effect judgments remain separate. -/
def evaluateStep (values : Valuation) : (e : Expression) →
    ((child : Expression) → sizeOf child < sizeOf e → Option Nat) → Option Nat
  | .input ordinal, _ => values.inputs ordinal
  | .basisInput ordinal, _ => values.basisInputs ordinal
  | .unit, _ => some 0
  | .bit value, _ => some (if value then 1 else 0)
  | .ordinal value, _ => some value
  | .measured origin calls owner, _ => values.measured origin calls owner
  | .project .., _ => none
  | .combine stride first second, child => do
    if stride == 0 then none else do
      let first ← child first (by decreasing_tactic)
      let second ← child second (by decreasing_tactic)
      if first ≥ stride then none else some (first+stride*second)
  | .field stride dimension receiver, child => do
    if stride == 0 || dimension == 0 then none else do
      let receiver ← child receiver (by decreasing_tactic)
      some ((receiver/stride)%dimension)
  | .equalsOrdinal ordinal value, child => do
    let value ← child value (by decreasing_tactic)
    some (if value == ordinal then 1 else 0)
  | .not value, child => do
    let value ← child value (by decreasing_tactic)
    if value ≥ 2 then none else some (1-value)
  | .xor first second, child => do
    let first ← child first (by decreasing_tactic)
    let second ← child second (by decreasing_tactic)
    if first ≥ 2 || second ≥ 2 then none else some (if first == second then 0 else 1)
  | .and first second, child => do
    let first ← child first (by decreasing_tactic)
    let second ← child second (by decreasing_tactic)
    if first ≥ 2 || second ≥ 2 then none else some (if first == 1 && second == 1 then 1 else 0)
  | .choose condition thenValue elseValue, child => do
    let condition ← child condition (by decreasing_tactic)
    if condition ≥ 2 then none else if condition == 1 then child thenValue (by decreasing_tactic) else child elseValue (by decreasing_tactic)

def evaluate (values : Valuation) : Expression → Option Nat :=
  Expression.descend (evaluateStep values)

theorem evaluate_unfold (values : Valuation) (e : Expression) :
    evaluate values e = evaluateStep values e (fun child _ => evaluate values child) :=
  Expression.descend_eq _ e

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
