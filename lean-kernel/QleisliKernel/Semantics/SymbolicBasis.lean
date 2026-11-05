import QleisliKernel.Semantics.FiniteCarrier
import QleisliKernel.Semantics.SourceAffine

/-! Original opaque basis parameters and affine-width type meanings.
This reference imports no source reader or acceptance code. Parameters retain
original declaration identity and mixed formal ordinal; selected values do not
identify an opaque parameter with a concrete type or a tuple decomposition.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Semantics.SymbolicBasis

structure Parameter where
  moduleName : String
  declarationName : String
  ordinal : Nat
  deriving BEq, DecidableEq, Repr

inductive Atom where
  | fixed (atom : FiniteCarrier.Atom)
  | parameter (binderKey : Parameter)
  | bits (width : SourceAffine.Form)
  deriving BEq, DecidableEq, Repr

abbrev Code := List Atom
abbrev Parameters := Parameter → Option FiniteCarrier.Basis

def Atom.evaluate (parameters : Parameters) (values : SourceAffine.Valuation) : Atom → Option FiniteCarrier.Basis
  | .fixed atom => some [atom]
  | .parameter binderKey => parameters binderKey
  | .bits width =>
    let value := width.evaluate values
    if 0 ≤ value then some [.bits value.toNat] else none

def evaluate (parameters : Parameters) (values : SourceAffine.Valuation) (code : Code) : Option FiniteCarrier.Basis := do
  let parts ← code.mapM (Atom.evaluate parameters values)
  return parts.flatten

@[simp] theorem evaluate_nil (parameters : Parameters) (values : SourceAffine.Valuation) :
    evaluate parameters values [] = some [] := rfl

@[simp] theorem evaluate_cons (parameters : Parameters) (values : SourceAffine.Valuation) (atom : Atom) (rest : Code) :
    evaluate parameters values (atom :: rest) = (do
      let head ← atom.evaluate parameters values
      let tail ← evaluate parameters values rest
      pure (head ++ tail)) := by
  simp only [evaluate,List.mapM_cons]
  cases atom.evaluate parameters values <;> cases rest.mapM (Atom.evaluate parameters values) <;> rfl

theorem evaluate_append (parameters : Parameters) (values : SourceAffine.Valuation) (left right : Code) :
    evaluate parameters values (left ++ right) = (do
      let first ← evaluate parameters values left
      let second ← evaluate parameters values right
      pure (first ++ second)) := by
  induction left with
  | nil => simp [evaluate]
  | cons atom rest ih =>
    simp only [List.cons_append,evaluate_cons,ih]
    cases atom.evaluate parameters values <;> cases evaluate parameters values rest <;>
      cases evaluate parameters values right <;> simp [List.append_assoc]

end QleisliKernel.Semantics.SymbolicBasis
