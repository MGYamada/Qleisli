import QleisliKernel.Semantics.RuntimeType
import QleisliKernel.Semantics.OrdinaryValue
import QleisliKernel.Semantics.CarrierInterface

/-! Complete runtime storage, with ordinary values and quantum owners distinct.
The prefix retains outer product shape. Ordinary leaves may contain complete
ordinary records/products; Q leaves retain their full logical basis and actual
Raw port. These reference projections import no acceptance checker.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Semantics.RuntimeStorage

inductive Atom where
  | ordinary (basis : FiniteCarrier.Basis) (stored : OrdinaryValue.Storage)
  | quantum (owner : CarrierInterface.Owner)
  | tuple (arity : Nat)

abbrev Value := List Atom

def nodeType : Atom → RuntimeType.Tree
  | .ordinary basis _ => RuntimeType.ordinary basis
  | .quantum owner => RuntimeType.owner owner.basis
  | .tuple arity => [.finite (if arity == 2 then .pair else .tuple arity)]

def typeOf (value : Value) : RuntimeType.Tree := value.flatMap nodeType

def ordinary (value : Value) : List (FiniteCarrier.Basis × OrdinaryValue.Storage) :=
  value.filterMap fun atom => match atom with
    | .ordinary basis stored => some (basis,stored)
    | _ => none

def quantum (value : Value) : List CarrierInterface.Owner :=
  value.filterMap fun atom => match atom with | .quantum owner => some owner | _ => none

def bases (value : Value) : List FiniteCarrier.Basis :=
  value.filterMap fun atom => match atom with
    | .ordinary basis _ => some basis
    | .quantum owner => some owner.basis
    | .tuple _ => none

/-- Shape of the storage itself is independent of the expanded finite basis
prefix. An incomplete leaf cannot consume a neighboring storage node. -/
def shapeStep (pending : Option Nat) (atom : Atom) : Option Nat := do
  let count ← pending
  match atom with
  | .tuple arity =>
    if arity < 2 || arity > count then none else some (count-arity+1)
  | _ => some (count+1)

def shaped (value : Value) : Prop := value.foldr (fun atom rest => shapeStep rest atom) (some 0) = some 1

def Matches (expected : RuntimeType.Tree) (stored : Value) : Prop :=
  shaped stored ∧ typeOf stored = expected

end QleisliKernel.Semantics.RuntimeStorage
