import QleisliKernel.Semantics.SourceNatural

/-! Independent u32 obligations for every original ordinary Nat expression node.
Static helper bodies retain their separate checked signed-affine rules.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Semantics.SourceNatural.Bounds

def children : Expr → List Expr
  | .number _ | .name _ => []
  | .add a b | .sub a b | .mul a b => [a,b]
  | .call _ arguments => arguments

/-- Includes every caller operand, even an ignored helper argument or a term
multiplied by zero. A bounded final value cannot hide an invalid intermediate. -/
inductive AllU32 (names : Names) (calls : Calls) : Expr → Prop where
  | node (expression : Expr) (value : Nat)
      (meaning : Value names calls expression value) (bounded : value ≤ 4294967295)
      (operands : ∀ child ∈ children expression,AllU32 names calls child) :
      AllU32 names calls expression

end QleisliKernel.Semantics.SourceNatural.Bounds
