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
  | parameter (parameter : Parameter)
  | bits (width : SourceAffine.Form)
  deriving BEq, DecidableEq, Repr

abbrev Code := List Atom
abbrev Parameters := Parameter → Option FiniteCarrier.Basis

def Atom.evaluate (parameters : Parameters) (values : SourceAffine.Valuation) : Atom → Option FiniteCarrier.Basis
  | .fixed atom => some [atom]
  | .parameter parameter => parameters parameter
  | .bits width =>
    let value := width.evaluate values
    if 0 ≤ value then some [.bits value.toNat] else none

def evaluate (parameters : Parameters) (values : SourceAffine.Valuation) : Code → Option FiniteCarrier.Basis
  | [] => some []
  | atom :: rest => do
    let head ← atom.evaluate parameters values
    let tail ← evaluate parameters values rest
    pure (head ++ tail)

theorem evaluate_append (parameters : Parameters) (values : SourceAffine.Valuation) (left right : Code) :
    evaluate parameters values (left ++ right) = (do
      let first ← evaluate parameters values left
      let second ← evaluate parameters values right
      pure (first ++ second)) := by
  induction left with
  | nil => simp [evaluate]
  | cons atom rest ih =>
    simp only [List.cons_append,evaluate,ih]
    cases atom.evaluate parameters values <;> cases evaluate parameters values rest <;>
      cases evaluate parameters values right <;> simp [List.append_assoc]

end QleisliKernel.Semantics.SymbolicBasis
