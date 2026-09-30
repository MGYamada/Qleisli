import Std

/-! Independent finite R8 data and interpretation interfaces.
No normalization, acceptance, capacities or proposed summaries occur here.
Complex denotation is defined separately in Qleisli.Semantics.Exact.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/

namespace QleisliKernel.Semantics.Exact

structure Coefficient where
  numerator : Int
  exponent : Nat
  deriving BEq, DecidableEq, Repr

structure Scalar where
  a : Coefficient
  b : Coefficient
  c : Coefficient
  d : Coefficient
  deriving BEq, DecidableEq, Repr

def Coefficient.integer (n : Int) : Coefficient := ⟨n, 0⟩
def Scalar.zero : Scalar := ⟨.integer 0, .integer 0, .integer 0, .integer 0⟩
def Scalar.one : Scalar := ⟨.integer 1, .integer 0, .integer 0, .integer 0⟩

def Scalar.get (x : Scalar) : Nat → Coefficient
  | 0 => x.a | 1 => x.b | 2 => x.c | _ => x.d

def Scalar.set (x : Scalar) (i : Nat) (v : Coefficient) : Scalar :=
  match i with
  | 0 => { x with a := v } | 1 => { x with b := v }
  | 2 => { x with c := v } | _ => { x with d := v }

structure Matrix where
  rows : Nat
  cols : Nat
  entries : List Scalar
  deriving BEq, DecidableEq, Repr

def Matrix.entry (x : Matrix) (row col : Nat) : Scalar :=
  x.entries[row * x.cols + col]?.getD Scalar.zero

deriving instance ReflBEq, LawfulBEq for Coefficient, Scalar, Matrix

end QleisliKernel.Semantics.Exact
