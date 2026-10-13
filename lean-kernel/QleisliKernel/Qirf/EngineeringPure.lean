import QleisliKernel.Qirf.PureLeaf
import QleisliKernel.Engineering.Pure

/-! Engineering comparison of two original rectangular pure artifacts.
Both existing exact PureLeaf gates run before any inequality check. This
component is used by a separate engineering protocol, never an exact accepted
handle. It provides no exact equality between the two meanings, capability, cleanup,
realization or resource certificate. A zero budget retains that claim kind.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.EngineeringPure
open Semantics.Exact Semantics.Finite Finite

/-- Each independent matrix request binds its own original root, dependency
order and exact ordered ports. A matrix or receipt cannot replace the body. -/
structure LeafRequest where
  artifact : Artifact
  order : Array Nat
  input : Semantics.Raw.Port
  output : Semantics.Raw.Port
  required : Matrix

/-- Common complete type trees are checked on both original root interfaces;
equal physical widths alone do not satisfy this requirement. -/
structure Request where
  domain : Basis
  codomain : Basis
  actual : LeafRequest
  ideal : LeafRequest
  epsilon : Coefficient

/-- Internal component data, never a production accepted-program handle or a
serialized success receipt. Each exact root has its own independent request. -/
structure Checked where
  actual : PureLeaf.Checked
  ideal : PureLeaf.Checked
  comparison : Engineering.Pure.Checked

def check (request : Request) : WorkM Checked := do
  let actual ← PureLeaf.check request.actual.artifact request.actual.order
    request.domain request.codomain request.actual.input request.actual.output
    request.actual.required
  let ideal ← PureLeaf.check request.ideal.artifact request.ideal.order
    request.domain request.codomain request.ideal.input request.ideal.output
    request.ideal.required
  let comparison ← Engineering.Pure.checkMatrices actual.actual ideal.actual request.epsilon
  return ⟨actual,ideal,comparison⟩

/-- The three successful calls belong to this one execution and share its
remaining work. The existing PureLeaf postconditions separately expose original
root validation, body reconstruction, effects, ports, exact Gram and equations. -/
structure Postcondition (request : Request) (checked : Checked) (work left : Nat) : Prop where
  execution : ∃ afterActual afterIdeal,
    (PureLeaf.check request.actual.artifact request.actual.order
      request.domain request.codomain request.actual.input request.actual.output
      request.actual.required).run work = (.ok checked.actual,afterActual) ∧
    (PureLeaf.check request.ideal.artifact request.ideal.order
      request.domain request.codomain request.ideal.input request.ideal.output
      request.ideal.required).run afterActual = (.ok checked.ideal,afterIdeal) ∧
    (Engineering.Pure.checkMatrices checked.actual.actual checked.ideal.actual
      request.epsilon).run afterIdeal = (.ok checked.comparison,left)

theorem check_postcondition (request : Request) (checked : Checked) (work left : Nat)
    (ok : (check request).run work = (.ok checked,left)) :
    Postcondition request checked work left := by
  obtain ⟨actual,a,ha,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨ideal,b,hi,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨comparison,c,hc,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  have remaining := (pure_success _ _ _ _ h).2
  subst checked
  subst left
  exact ⟨⟨a,b,ha,hi,hc⟩⟩

end QleisliKernel.Qirf.EngineeringPure
