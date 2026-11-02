import QleisliKernel.Semantics.FiniteCarrier

/-! Independent exact primitive operators on finite logical labels.
H uses the Bit basis; phase(k) fixes zero and multiplies one by exp(iπk/4).
The global eighth turn multiplies every logical label, including the sole
label of Unit, by exp(iπ/4). No Raw program, checker or producer table defines
these coefficients. Complex interpretation/specification review is separate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Semantics.PrimitiveOperator
open Exact FiniteCarrier

inductive Kind where
  | h | globalPhaseEighth | phase (exponent : Nat)

def halfRoot : Scalar := ⟨.integer 0,⟨1,1⟩,.integer 0,.integer 0⟩
def negativeHalfRoot : Scalar := ⟨.integer 0,⟨-1,1⟩,.integer 0,.integer 0⟩

def phase (exponent : Nat) : Scalar :=
  let zero := Coefficient.integer 0
  let one := Coefficient.integer 1
  let minus := Coefficient.integer (-1)
  let half : Coefficient := ⟨1,1⟩
  let negativeHalf : Coefficient := ⟨-1,1⟩
  match exponent % 8 with
  | 0 => ⟨one,zero,zero,zero⟩
  | 1 => ⟨zero,half,zero,half⟩
  | 2 => ⟨zero,zero,one,zero⟩
  | 3 => ⟨zero,negativeHalf,zero,half⟩
  | 4 => ⟨minus,zero,zero,zero⟩
  | 5 => ⟨zero,negativeHalf,zero,negativeHalf⟩
  | 6 => ⟨zero,zero,minus,zero⟩
  | _ => ⟨zero,half,zero,negativeHalf⟩

def meaning (kind : Kind) (basis : Basis) : Option Matrix :=
  match kind with
  | .h =>
    if basis == [.bit] then some ⟨2,2,[halfRoot,halfRoot,halfRoot,negativeHalfRoot]⟩ else none
  | .phase exponent =>
    if basis == [.bit] then some ⟨2,2,[Scalar.one,Scalar.zero,Scalar.zero,phase exponent]⟩ else none
  | .globalPhaseEighth => do
    let shape ← layout basis
    let dimension := shape.labels.length
    return ⟨dimension,dimension,(List.range (dimension*dimension)).map fun index =>
      if index / dimension == index % dimension then phase 1 else Scalar.zero⟩

end QleisliKernel.Semantics.PrimitiveOperator
