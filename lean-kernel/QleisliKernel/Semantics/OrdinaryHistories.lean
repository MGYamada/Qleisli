import QleisliKernel.Semantics.OrdinaryValue

/-! Complete ordered ordinary output families over classical valuations.
No checker, source parser or Raw reconstruction defines this relation.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Semantics.OrdinaryValue
open FiniteCarrier

inductive RepresentsAll (basis : Basis) (storage : Storage) : List Valuation → List Value → Prop
  | nil : RepresentsAll basis storage [] []
  | cons {values : Valuation} {value : Value} {histories : List Valuation} {outputs : List Value}
      (head : Represents values basis value storage)
      (tail : RepresentsAll basis storage histories outputs) :
      RepresentsAll basis storage (values :: histories) (value :: outputs)

theorem RepresentsAll.lengths {basis storage histories outputs}
    (represented : RepresentsAll basis storage histories outputs) : histories.length = outputs.length := by
  induction represented with
  | nil => rfl
  | cons head tail ih => simpa using congrArg Nat.succ ih

end QleisliKernel.Semantics.OrdinaryValue
