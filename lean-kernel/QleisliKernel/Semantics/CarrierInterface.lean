import QleisliKernel.Semantics.FiniteCarrier
import QleisliKernel.Semantics.Raw

/-! Typed owner forests retain nominal trees and zero-width owners separately
from their product encoding. This is data, not source elaboration or acceptance.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Semantics.CarrierInterface
open FiniteCarrier

structure Owner where
  port : Raw.Port
  basis : Basis
  deriving BEq, DecidableEq, Repr

structure Interface where
  inputs : List Owner
  outputs : List Owner
  publicEffect : Raw.Effect
  deriving BEq, DecidableEq, Repr

/-- Only the matrix coordinates use a product. The enclosing ordered owner
list remains part of the interface, even for singleton or empty carriers. -/
def forest (owners : List Owner) : Basis :=
  match owners with
  | [] => [.unit]
  | [owner] => owner.basis
  | [first,second] => .pair :: first.basis ++ second.basis
  | _ => .tuple owners.length :: owners.flatMap (·.basis)

deriving instance ReflBEq, LawfulBEq for Owner, Interface
end QleisliKernel.Semantics.CarrierInterface
